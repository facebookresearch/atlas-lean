/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DCDispatchEncoding
public import MathlibExt.Analysis.Convex.RationalLPCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Exact rational optimality certificates for DC economic dispatch

## i. Overview

The DC economic dispatch problem of `PhyslibExt.Circuits.DCDispatchEncoding`
minimizes the linear cost `cost ⬝ᵥ pg` subject to the lossless DC balance
`L_b * θ = Cgen * pg - d`, the reference angle `θ ref = 0`, generator
limits `pmin ≤ pg ≤ pmax` and branch flow limits `fmin ≤ f ≤ fmax`. This
file certifies optimality of a dispatch exactly, with rational data and
a computable checker.

The data `b, d, pmin, pmax, fmin, fmax, cost` are rational, and the real
problem is the canonical one applied to their entrywise casts
(`castVec`). A certificate consists of a rational primal dispatch
`(pg, θ)` and a rational dual witness: nodal prices `lam` (free; the
multipliers of the balance, read as locational marginal prices), a
reference multiplier `ρ` (free) and generator and flow bound multipliers
`μhi, μlo, ηhi, ηlo` (required nonnegative). The certified lower bound is
`dualLowerBound = d ⬝ lam + pmin ⬝ μlo - pmax ⬝ μhi + fmin ⬝ ηlo - fmax ⬝ ηhi`.

The checker `checksDispatchCertificate` runs the exact rational LP gap
checker `MathlibExt.Analysis.Convex.RationalLPCertificate.checksLPGap` on
a rational copy of the canonical inequality-form LP of the encoding
module. The primal witness enters through the positive/negative-part
split, the free dual variables through the same split over the two rows
of each equality, and the bound multipliers unchanged, so a negative
bound multiplier fails the checker's sign test. The canonical LP is real
and noncomputable, which is why the rational copy exists; the
encoding-equivalence lemmas show it casts entrywise to the canonical LP.

The checker accepts exactly the certificates that are primal feasible,
dual feasible (`IsDualFeasible`: nonnegative bound multipliers, generator
stationarity `lam (gbus g) = cost g + μhi g - μlo g` and angle
stationarity) and whose gap `cost ⬝ pg - dualLowerBound` lies in
`[0, ε]`. Acceptance transfers through the encoding to the real problem:
the dispatch is feasible, `dualLowerBound` bounds the cost of every
feasible real dispatch, and the dispatch cost is within `ε` of the
optimum. Acceptance at `ε = 0` proves global optimality. All inputs are
rational, so no floating-point solver output is itself a certificate;
dimensions are fixed by the `Fin` types, so a dimensionally malformed
certificate cannot be stated. No positivity of `b` or ordering of the
bounds is assumed, and a negative budget makes the checker reject every
certificate.

## ii. Key results

- `dispatch_certificate_correct`: an accepted certificate gives a feasible
  dispatch, a valid lower bound on every feasible cost, a gap in `[0, ε]`
  and `ε`-optimality.
- `dispatch_optimal_of_checks_zero`: acceptance at zero gap gives global
  optimality, with the dispatch cost equal to the certified bound.
- `checksDispatchCertificate_eq_true_iff`: the checker accepts exactly the
  primal feasible, dual feasible certificates within the gap budget;
  `checks_eq_false_of_not_dispatchFeasible`,
  `checks_eq_false_of_not_dualFeasible` and `checks_eq_false_of_lt_gap`
  are the three rejections.
- `ratLpMatrix_map`, `castVec_ratLpRhs`, `castVec_ratLpObjective`,
  `castVec_ratEncode`: the rational LP casts to the canonical LP.

## iii. Table of contents

- A. Rational data and the rational LP
- B. Dual witnesses
- C. The certificate checker
- D. Encoding equivalence
- E. Acceptance and rejection
- F. Soundness through the encoding
- G. Headline

## iv. References

- A. J. Wood, B. F. Wollenberg, and G. B. Sheblé, *Power Generation,
  Operation, and Control*, 3rd ed., Wiley, 2014: economic dispatch and
  the DC optimal power flow as a linear program.
- F. C. Schweppe, M. C. Caramanis, R. D. Tabors, and R. E. Bohn, *Spot
  Pricing of Electricity*, Kluwer Academic Publishers, 1988: nodal prices
  as the multipliers of the network balance constraints.
- D. Bertsimas and J. N. Tsitsiklis, *Introduction to Linear
  Optimization*, Athena Scientific, 1997, Chapter 4: weak duality and
  primal-dual optimality certificates.

## A. Rational data and the rational LP
-/

@[expose] public section

namespace PhyslibExt.Circuits.DCDispatchCertificate

open Matrix
open PhyslibExt.Circuits.DCDispatchEncoding
open MathlibExt.Analysis.Convex.RationalLPCertificate

/-- Real reading of a rational vector: the entrywise cast. -/
def castVec {ι : Type*} (v : ι → ℚ) : ι → ℝ :=
  fun i => (v i : ℝ)

/-- Rational tail-positive incidence: `1` at the tail of a branch, `-1`
at its head. -/
def ratIncidence (nN nE : ℕ) (tail head : Fin nE → Fin nN) : Matrix (Fin nN) (Fin nE) ℚ :=
  fun v e => (if tail e = v then 1 else 0) - (if head e = v then 1 else 0)

/-- Rational weighted Laplacian `B * diag(b) * Bᵀ`. -/
def ratLaplacian (nN nE : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℚ) :
    Matrix (Fin nN) (Fin nN) ℚ :=
  ratIncidence nN nE tail head * Matrix.diagonal b * Matrix.transpose (ratIncidence nN nE tail head)

/-- Rational branch-flow coefficient matrix `diag(b) * Bᵀ`. -/
def ratBranchFlowMatrix (nN nE : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℚ) :
    Matrix (Fin nE) (Fin nN) ℚ :=
  Matrix.diagonal b * Matrix.transpose (ratIncidence nN nE tail head)

/-- Rational generator-to-bus incidence. -/
def ratGeneratorIncidence (nN nG : ℕ) (gbus : Fin nG → Fin nN) : Matrix (Fin nN) (Fin nG) ℚ :=
  fun v g => if gbus g = v then 1 else 0

/-- Rational reference row selecting the angle of bus `ref`. -/
def ratReferenceRow (nN : ℕ) (ref : Fin nN) : Matrix (Fin 1) (Fin nN) ℚ :=
  fun _ v => if v = ref then 1 else 0

/-- One rational block of constraint rows on the free variables `(pg, θ)`. -/
def ratFreeRows {r : ℕ} (nN nG : ℕ) (P : Matrix (Fin r) (Fin nG) ℚ)
    (T : Matrix (Fin r) (Fin nN) ℚ) : Fin r → Fin (nG + nN) → ℚ :=
  fun i => Fin.append (P i) (T i)

/-- Rational constraint matrix on the free variables, in the row order of
the canonical `freeConstraintMatrix`. -/
def ratFreeConstraintMatrix (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (ref : Fin nN) :
    Matrix (Fin (numRows nN nE nG)) (Fin (nG + nN)) ℚ :=
  Matrix.of <|
    Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append
      (ratFreeRows nN nG (-ratGeneratorIncidence nN nG gbus) (ratLaplacian nN nE tail head b))
      (ratFreeRows nN nG (ratGeneratorIncidence nN nG gbus) (-ratLaplacian nN nE tail head b)))
      (ratFreeRows nN nG (0 : Matrix (Fin 1) (Fin nG) ℚ) (ratReferenceRow nN ref)))
      (ratFreeRows nN nG (0 : Matrix (Fin 1) (Fin nG) ℚ) (-ratReferenceRow nN ref)))
      (ratFreeRows nN nG (1 : Matrix (Fin nG) (Fin nG) ℚ) (0 : Matrix (Fin nG) (Fin nN) ℚ)))
      (ratFreeRows nN nG (-1 : Matrix (Fin nG) (Fin nG) ℚ) (0 : Matrix (Fin nG) (Fin nN) ℚ)))
      (ratFreeRows nN nG (0 : Matrix (Fin nE) (Fin nG) ℚ) (ratBranchFlowMatrix nN nE tail head b)))
      (ratFreeRows nN nG (0 : Matrix (Fin nE) (Fin nG) ℚ) (-ratBranchFlowMatrix nN nE tail head b))

/-- Rational LP constraint matrix: the rational free constraint matrix on
the positive parts and its negation on the negative parts. -/
def ratLpMatrix (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (ref : Fin nN) :
    Matrix (Fin (numRows nN nE nG)) (Fin (numVars nN nG)) ℚ :=
  Matrix.of fun i =>
    Fin.append (ratFreeConstraintMatrix nN nE nG tail head b gbus ref i)
      (-ratFreeConstraintMatrix nN nE nG tail head b gbus ref i)

/-- Rational LP right-hand side, in the row order of the canonical `lpRhs`. -/
def ratLpRhs (nN nE nG : ℕ) (d : Fin nN → ℚ) (pmin pmax : Fin nG → ℚ)
    (fmin fmax : Fin nE → ℚ) : Fin (numRows nN nE nG) → ℚ :=
  Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append
    (-d) d) (0 : Fin 1 → ℚ)) (0 : Fin 1 → ℚ)) pmax) (-pmin)) fmax) (-fmin)

/-- Rational LP objective (maximized), in the column order of the
canonical `lpObjective`. -/
def ratLpObjective (nN nG : ℕ) (cost : Fin nG → ℚ) : Fin (numVars nN nG) → ℚ :=
  Fin.append (Fin.append (-cost) (0 : Fin nN → ℚ)) (Fin.append cost (0 : Fin nN → ℚ))

/-- Rational LP point of a rational primal witness: positive parts
`max z 0` followed by negative parts `max (-z) 0` of `z = (pg, θ)`. -/
def ratEncode (nN nG : ℕ) (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) : Fin (numVars nN nG) → ℚ :=
  Fin.append (fun a => max (Fin.append pg θ a) 0) (fun a => max (-Fin.append pg θ a) 0)

/-! ## B. Dual witnesses -/

/-- LP dual vector of a dispatch dual witness, in the row order of the
canonical LP. The nodal prices `lam` are free multipliers of the balance
`L_b * θ - Cgen * pg = -d`: their positive parts go to the first balance
block and their negative parts to the second. The free reference
multiplier `ρ` is split the same way over the two reference rows. The
generator and flow bound multipliers `μhi, μlo, ηhi, ηlo` are passed
unchanged, so a negative entry fails the checker's sign test. -/
def dualVector (nN nE nG : ℕ) (lam : Fin nN → ℚ) (ρ : ℚ) (μhi μlo : Fin nG → ℚ)
    (ηhi ηlo : Fin nE → ℚ) : Fin (numRows nN nE nG) → ℚ :=
  Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append
    (fun v => max (lam v) 0) (fun v => max (-lam v) 0))
    (fun _ : Fin 1 => max ρ 0)) (fun _ : Fin 1 => max (-ρ) 0)) μhi) μlo) ηhi) ηlo

/-- Certified lower bound on the dispatch cost: demand revenue at the
nodal prices plus the generator and flow bound terms,
`d ⬝ lam + pmin ⬝ μlo - pmax ⬝ μhi + fmin ⬝ ηlo - fmax ⬝ ηhi`. -/
def dualLowerBound (nN nE nG : ℕ) (d : Fin nN → ℚ) (pmin pmax : Fin nG → ℚ)
    (fmin fmax : Fin nE → ℚ) (lam : Fin nN → ℚ) (μhi μlo : Fin nG → ℚ)
    (ηhi ηlo : Fin nE → ℚ) : ℚ :=
  d ⬝ᵥ lam + pmin ⬝ᵥ μlo - pmax ⬝ᵥ μhi + fmin ⬝ᵥ ηlo - fmax ⬝ᵥ ηhi

/-- Dual feasibility of a dispatch dual witness: nonnegative bound
multipliers, generator stationarity `lam (gbus g) = cost g + μhi g - μlo g`
(the price at a generator's bus is its marginal cost corrected by its
bound multipliers), and angle stationarity
`L_bᵀ lam + ρ e_ref + (diag(b) Bᵀ)ᵀ (ηhi - ηlo) = 0`. -/
def IsDualFeasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℚ)
    (gbus : Fin nG → Fin nN) (ref : Fin nN) (cost : Fin nG → ℚ) (lam : Fin nN → ℚ)
    (ρ : ℚ) (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) : Prop :=
  (∀ g, 0 ≤ μhi g) ∧ (∀ g, 0 ≤ μlo g) ∧ (∀ e, 0 ≤ ηhi e) ∧ (∀ e, 0 ≤ ηlo e) ∧
    (∀ g, lam (gbus g) = cost g + μhi g - μlo g) ∧
    ∀ v, (Matrix.transpose (ratLaplacian nN nE tail head b) *ᵥ lam) v +
        (if v = ref then ρ else 0) +
        (Matrix.transpose (ratBranchFlowMatrix nN nE tail head b) *ᵥ (ηhi - ηlo)) v = 0

/-! ## C. The certificate checker -/

/-- Exact certificate checker for DC dispatch: the existing rational LP
gap checker run on the rational LP, the encoded primal witness and the
dual vector of the dual witness. A computable `Bool`. -/
def checksDispatchCertificate (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ) : Bool :=
  checksLPGap (numRows nN nE nG) (numVars nN nG) (ratLpMatrix nN nE nG tail head b gbus ref)
    (ratLpRhs nN nE nG d pmin pmax fmin fmax) (ratLpObjective nN nG cost)
    (ratEncode nN nG pg θ) (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ε

/-! ## D. Encoding equivalence -/

/-- The cast rational LP matrix is the canonical LP matrix of the cast
susceptances. -/
lemma ratLpMatrix_map (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (ref : Fin nN) :
    Matrix.map (ratLpMatrix nN nE nG tail head b gbus ref) (fun q : ℚ => (q : ℝ)) =
      lpMatrix nN nE nG tail head (castVec b) gbus ref := by
  have hc : (fun q : ℚ => (q : ℝ)) = ⇑(Rat.castHom ℝ) := rfl
  have hI : Matrix.map (ratIncidence nN nE tail head) (fun q : ℚ => (q : ℝ)) =
      PhyslibExt.Circuits.ArcPortSigns.electricalIncidence tail head := by
    ext v e
    simp only [Matrix.map_apply, ratIncidence,
      PhyslibExt.Circuits.ArcPortSigns.electricalIncidence_apply]
    split_ifs <;> norm_num
  have hD : Matrix.map (Matrix.diagonal b) (fun q : ℚ => (q : ℝ)) =
      Matrix.diagonal (castVec b) := Matrix.diagonal_map (by simp)
  have hL : ∀ w v, ((ratLaplacian nN nE tail head b w v : ℚ) : ℝ) =
      PhyslibExt.Circuits.LosslessDCFlowModel.weightedLaplacian nN nE tail head (castVec b)
        w v := by
    intro w v
    have h : Matrix.map (ratLaplacian nN nE tail head b) (fun q : ℚ => (q : ℝ)) =
        PhyslibExt.Circuits.LosslessDCFlowModel.weightedLaplacian nN nE tail head
          (castVec b) := by
      rw [ratLaplacian, PhyslibExt.Circuits.LosslessDCFlowModel.weightedLaplacian, hc,
        Matrix.map_mul, Matrix.map_mul, ← hc, Matrix.transpose_map, hI, hD]
    exact congrFun (congrFun h w) v
  have hB : ∀ e v, ((ratBranchFlowMatrix nN nE tail head b e v : ℚ) : ℝ) =
      branchFlowMatrix nN nE tail head (castVec b) e v := by
    intro e v
    have h : Matrix.map (ratBranchFlowMatrix nN nE tail head b) (fun q : ℚ => (q : ℝ)) =
        branchFlowMatrix nN nE tail head (castVec b) := by
      rw [ratBranchFlowMatrix, branchFlowMatrix, hc, Matrix.map_mul, ← hc,
        Matrix.transpose_map, hI, hD]
    exact congrFun (congrFun h e) v
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  simp only [Matrix.map_apply, ratLpMatrix, lpMatrix, Matrix.of_apply,
    ratFreeConstraintMatrix, freeConstraintMatrix, ratFreeRows, freeRows, Fin.append_left,
    Fin.append_right, Pi.neg_apply, Matrix.neg_apply, Rat.cast_neg, hL, hB,
    ratGeneratorIncidence, generatorIncidence, ratReferenceRow, referenceRow,
    Matrix.zero_apply, Matrix.one_apply, Rat.cast_zero, apply_ite (fun q : ℚ => (q : ℝ)),
    Rat.cast_one]

/-- The cast rational right-hand side is the canonical right-hand side of
the cast data. -/
lemma castVec_ratLpRhs (nN nE nG : ℕ) (d : Fin nN → ℚ) (pmin pmax : Fin nG → ℚ)
    (fmin fmax : Fin nE → ℚ) :
    castVec (ratLpRhs nN nE nG d pmin pmax fmin fmax) =
      lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
        (castVec fmax) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  (try refine Fin.addCases (fun i => ?_) (fun i => ?_) i) <;>
  simp only [castVec, ratLpRhs, lpRhs, Fin.append_left, Fin.append_right, Pi.neg_apply,
    Pi.zero_apply, Rat.cast_neg, Rat.cast_zero]

/-- The cast rational objective is the canonical objective of the cast cost. -/
lemma castVec_ratLpObjective (nN nG : ℕ) (cost : Fin nG → ℚ) :
    castVec (ratLpObjective nN nG cost) = lpObjective nN nG (castVec cost) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  simp only [castVec, ratLpObjective, lpObjective, Fin.append_left, Fin.append_right,
    Pi.neg_apply, Pi.zero_apply, Rat.cast_neg, Rat.cast_zero]

/-- The cast rational encoding is the canonical encoding of the cast witness. -/
lemma castVec_ratEncode (nN nG : ℕ) (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) :
    castVec (ratEncode nN nG pg θ) = encode nN nG (castVec pg) (castVec θ) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
  simp only [castVec, ratEncode, encode, Fin.append_left, Fin.append_right,
    Rat.cast_max, Rat.cast_neg, Rat.cast_zero]

/-- The encoded primal witness passes the primal checks exactly when the
cast witness is a feasible dispatch of the cast data. -/
lemma ratPrimal_feasible_iff (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (pg : Fin nG → ℚ)
    (θ : Fin nN → ℚ) :
    ((∀ i, 0 ≤ ratEncode nN nG pg θ i) ∧
      ∀ j, (ratLpMatrix nN nE nG tail head b gbus ref *ᵥ ratEncode nN nG pg θ) j ≤
        ratLpRhs nN nE nG d pmin pmax fmin fmax j) ↔
      IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
        (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
        (castVec pg) (castVec θ) := by
  have hx : ∀ i, ((ratEncode nN nG pg θ i : ℚ) : ℝ) = encode nN nG (castVec pg) (castVec θ) i :=
    fun i => congrFun (castVec_ratEncode nN nG pg θ) i
  have hr : ∀ j, ((ratLpRhs nN nE nG d pmin pmax fmin fmax j : ℚ) : ℝ) =
      lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
        (castVec fmax) j :=
    fun j => congrFun (castVec_ratLpRhs nN nE nG d pmin pmax fmin fmax) j
  have hm : ∀ j, (((ratLpMatrix nN nE nG tail head b gbus ref *ᵥ ratEncode nN nG pg θ) j :
      ℚ) : ℝ) = (lpMatrix nN nE nG tail head (castVec b) gbus ref *ᵥ
        encode nN nG (castVec pg) (castVec θ)) j := by
    intro j
    have h := RingHom.map_mulVec (Rat.castHom ℝ) (ratLpMatrix nN nE nG tail head b gbus ref)
      (ratEncode nN nG pg θ) j
    rw [Rat.coe_castHom] at h
    rw [h, ratLpMatrix_map, ← castVec_ratEncode]
    rfl
  constructor
  · rintro ⟨h0, h1⟩
    have hf := decode_feasible nN nE nG tail head (castVec b) gbus (castVec d) ref
      (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
      (encode nN nG (castVec pg) (castVec θ))
      (fun i => by rw [← hx]; exact_mod_cast h0 i)
      (fun j => by rw [← hm, ← hr]; exact_mod_cast h1 j)
    rwa [decodeGeneration_encode, decodeAngle_encode] at hf
  · intro h
    obtain ⟨h0, h1⟩ := encode_feasible nN nE nG tail head (castVec b) gbus (castVec d) ref
      (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) (castVec pg) (castVec θ) h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := h0 i
      rw [← hx] at this
      exact_mod_cast this
    · have := h1 j
      rw [← hm, ← hr] at this
      exact_mod_cast this

/-- The dual vector passes the dual checks exactly when the dual witness
is dual feasible. -/
lemma dualVector_feasible_iff (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (ref : Fin nN) (cost : Fin nG → ℚ)
    (lam : Fin nN → ℚ) (ρ : ℚ) (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) :
    ((∀ j, 0 ≤ dualVector nN nE nG lam ρ μhi μlo ηhi ηlo j) ∧
      ∀ i, ratLpObjective nN nG cost i ≤
        (Matrix.transpose (ratLpMatrix nN nE nG tail head b gbus ref) *ᵥ
          dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) i) ↔
      IsDualFeasible nN nE nG tail head b gbus ref cost lam ρ μhi μlo ηhi ηlo := by
  have hgen : ∀ g, ∑ j, ratFreeConstraintMatrix nN nE nG tail head b gbus ref j
      (Fin.castAdd nN g) * dualVector nN nE nG lam ρ μhi μlo ηhi ηlo j =
      -lam (gbus g) + μhi g - μlo g := by
    intro g
    simp only [Fin.sum_univ_add, ratFreeConstraintMatrix, dualVector, Matrix.of_apply, ratFreeRows,
      Fin.append_left, Fin.append_right]
    simp [ratGeneratorIncidence, Matrix.one_apply]
    have := max_zero_sub_max_neg_zero_eq_self (lam (gbus g))
    grind
  have hang : ∀ v, ∑ j, ratFreeConstraintMatrix nN nE nG tail head b gbus ref j
      (Fin.natAdd nG v) * dualVector nN nE nG lam ρ μhi μlo ηhi ηlo j =
      (Matrix.transpose (ratLaplacian nN nE tail head b) *ᵥ lam) v +
        (if v = ref then ρ else 0) +
        (Matrix.transpose (ratBranchFlowMatrix nN nE tail head b) *ᵥ (ηhi - ηlo)) v := by
    intro v
    simp only [Fin.sum_univ_add, ratFreeConstraintMatrix, dualVector, Matrix.of_apply, ratFreeRows,
      Fin.append_left, Fin.append_right]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, ratReferenceRow, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Pi.sub_apply]
    have e1 : ∑ i, ratLaplacian nN nE tail head b i v * lam i =
        ∑ x, ratLaplacian nN nE tail head b x v * max (lam x) 0 -
          ∑ x, ratLaplacian nN nE tail head b x v * max (-lam x) 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    have e2 : ∑ i, ratBranchFlowMatrix nN nE tail head b i v * (ηhi i - ηlo i) =
        ∑ x, ratBranchFlowMatrix nN nE tail head b x v * ηhi x -
          ∑ x, ratBranchFlowMatrix nN nE tail head b x v * ηlo x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun e _ => mul_sub _ _ _)
    rw [e1, e2]
    split_ifs
    · have := max_zero_sub_max_neg_zero_eq_self ρ
      grind
    · ring
  have hAT1 : ∀ a, (Matrix.transpose (ratLpMatrix nN nE nG tail head b gbus ref) *ᵥ
      dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) (Fin.castAdd (nG + nN) a) =
      ∑ j, ratFreeConstraintMatrix nN nE nG tail head b gbus ref j a *
        dualVector nN nE nG lam ρ μhi μlo ηhi ηlo j := by
    intro a
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, ratLpMatrix,
      Matrix.of_apply, Fin.append_left]
  have hAT2 : ∀ a, (Matrix.transpose (ratLpMatrix nN nE nG tail head b gbus ref) *ᵥ
      dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) (Fin.natAdd (nG + nN) a) =
      -∑ j, ratFreeConstraintMatrix nN nE nG tail head b gbus ref j a *
        dualVector nN nE nG lam ρ μhi μlo ηhi ηlo j := by
    intro a
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, ratLpMatrix,
      Matrix.of_apply, Fin.append_right, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  constructor
  · rintro ⟨hy, hc⟩
    refine ⟨fun g => ?_, fun g => ?_, fun e => ?_, fun e => ?_, fun g => ?_, fun v => ?_⟩
    · simpa [dualVector, Fin.append_left, Fin.append_right] using
        hy (Fin.castAdd _ (Fin.castAdd _ (Fin.castAdd _ (Fin.natAdd _ g))))
    · simpa [dualVector, Fin.append_left, Fin.append_right] using
        hy (Fin.castAdd _ (Fin.castAdd _ (Fin.natAdd _ g)))
    · simpa [dualVector, Fin.append_left, Fin.append_right] using
        hy (Fin.castAdd _ (Fin.natAdd _ e))
    · simpa [dualVector, Fin.append_left, Fin.append_right] using
        hy (Fin.natAdd _ e)
    · have h1 := hc (Fin.castAdd (nG + nN) (Fin.castAdd nN g))
      have h2 := hc (Fin.natAdd (nG + nN) (Fin.castAdd nN g))
      rw [hAT1, hgen] at h1
      rw [hAT2, hgen] at h2
      simp only [ratLpObjective, Fin.append_left, Fin.append_right, Pi.neg_apply] at h1 h2
      grind
    · have h1 := hc (Fin.castAdd (nG + nN) (Fin.natAdd nG v))
      have h2 := hc (Fin.natAdd (nG + nN) (Fin.natAdd nG v))
      rw [hAT1, hang] at h1
      rw [hAT2, hang] at h2
      simp only [ratLpObjective, Fin.append_left, Fin.append_right, Pi.zero_apply] at h1 h2
      grind
  · rintro ⟨hμh, hμl, hηh, hηl, hst, han⟩
    constructor
    · intro j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      (try refine Fin.addCases (fun j => ?_) (fun j => ?_) j) <;>
      simp only [dualVector, Fin.append_left, Fin.append_right] <;>
      first
        | exact le_max_right _ _
        | exact hμh _
        | exact hμl _
        | exact hηh _
        | exact hηl _
    · intro i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · rw [hAT1]
        refine Fin.addCases (fun g => ?_) (fun v => ?_) a
        · rw [hgen]
          simp only [ratLpObjective, Fin.append_left, Pi.neg_apply]
          have := hst g; grind
        · rw [hang, han v]
          simp only [ratLpObjective, Fin.append_left, Fin.append_right, Pi.zero_apply, le_refl]
      · rw [hAT2]
        refine Fin.addCases (fun g => ?_) (fun v => ?_) a
        · rw [hgen]
          simp only [ratLpObjective, Fin.append_left, Fin.append_right]
          have := hst g; grind
        · rw [hang, han v]
          simp only [ratLpObjective, Fin.append_right, Pi.zero_apply, neg_zero, le_refl]

/-- The LP dual objective of the dual vector is minus the certified lower
bound. -/
lemma ratLpRhs_dotProduct_dualVector (nN nE nG : ℕ) (d : Fin nN → ℚ)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) :
    ratLpRhs nN nE nG d pmin pmax fmin fmax ⬝ᵥ dualVector nN nE nG lam ρ μhi μlo ηhi ηlo =
      -dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo := by
  have e1 : ∑ v, d v * lam v = ∑ v, d v * max (lam v) 0 - ∑ v, d v * max (-lam v) 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  simp only [dotProduct, Fin.sum_univ_add, ratLpRhs, dualVector, Fin.append_left, Fin.append_right]
  simp [dualLowerBound, dotProduct, e1]
  ring

/-- The LP objective of the encoded primal witness is minus its cost. -/
lemma ratLpObjective_dotProduct_ratEncode (nN nG : ℕ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) :
    ratLpObjective nN nG cost ⬝ᵥ ratEncode nN nG pg θ = -(cost ⬝ᵥ pg) := by
  have e1 : ∑ g, cost g * pg g =
      ∑ g, cost g * max (pg g) 0 - ∑ g, cost g * max (-pg g) 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
  simp only [dotProduct, Fin.sum_univ_add, ratLpObjective, ratEncode, Fin.append_left,
    Fin.append_right]
  simp [e1]
  ring

/-! ## E. Acceptance and rejection -/

/-- The checker accepts exactly the witnesses whose primal part is a
feasible dispatch, whose dual part is dual feasible, and whose gap
`cost ⬝ pg - dualLowerBound` lies in `[0, ε]`. -/
lemma checksDispatchCertificate_eq_true_iff (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ) :
    checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
        pg θ lam ρ μhi μlo ηhi ηlo ε = true ↔
      IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
          (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
          (castVec pg) (castVec θ) ∧
        IsDualFeasible nN nE nG tail head b gbus ref cost lam ρ μhi μlo ηhi ηlo ∧
        0 ≤ cost ⬝ᵥ pg - dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo ∧
        cost ⬝ᵥ pg - dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo ≤ ε := by
  unfold checksDispatchCertificate
  rw [checksLPGap_eq_true_iff, ratLpRhs_dotProduct_dualVector,
    ratLpObjective_dotProduct_ratEncode, ← ratPrimal_feasible_iff, ← dualVector_feasible_iff]
  have hg : -dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo - -(cost ⬝ᵥ pg) =
      cost ⬝ᵥ pg - dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo := by ring
  rw [hg]
  simp only [and_assoc]

/-- An infeasible primal witness is rejected. -/
lemma checks_eq_false_of_not_dispatchFeasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ)
    (h : ¬ IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
      (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
      (castVec pg) (castVec θ)) :
    checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε = false := by
  cases hc : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε
  · rfl
  · exact absurd ((checksDispatchCertificate_eq_true_iff nN nE nG tail head b gbus d ref pmin pmax
      fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo ε).1 hc).1 h

/-- A dual witness that is not dual feasible (a negative bound multiplier
or a failed stationarity equation) is rejected. -/
lemma checks_eq_false_of_not_dualFeasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ)
    (h : ¬ IsDualFeasible nN nE nG tail head b gbus ref cost lam ρ μhi μlo ηhi ηlo) :
    checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε = false := by
  cases hc : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε
  · rfl
  · exact absurd ((checksDispatchCertificate_eq_true_iff nN nE nG tail head b gbus d ref pmin pmax
      fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo ε).1 hc).2.1 h

/-- A witness whose gap exceeds the budget is rejected. -/
lemma checks_eq_false_of_lt_gap (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ)
    (h : ε < cost ⬝ᵥ pg - dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo) :
    checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε = false := by
  cases hc : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε
  · rfl
  · exact absurd ((checksDispatchCertificate_eq_true_iff nN nE nG tail head b gbus d ref pmin pmax
      fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo ε).1 hc).2.2.2 (not_le.mpr h)

/-! ## F. Soundness through the encoding -/

/-- LP-level transfer: an accepted certificate makes the encoded cast
witness a feasible point of the canonical real LP whose objective is
within `ε` of every feasible real LP point. -/
lemma checks_lp_certificate (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ)
    (h : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε = true) :
    (∀ i, 0 ≤ encode nN nG (castVec pg) (castVec θ) i) ∧
      (∀ j, (lpMatrix nN nE nG tail head (castVec b) gbus ref *ᵥ
          encode nN nG (castVec pg) (castVec θ)) j ≤
        lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
          (castVec fmax) j) ∧
      ∀ z : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ z i) →
        (∀ j, (lpMatrix nN nE nG tail head (castVec b) gbus ref *ᵥ z) j ≤
          lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
            (castVec fmax) j) →
        lpObjective nN nG (castVec cost) ⬝ᵥ z ≤
          lpObjective nN nG (castVec cost) ⬝ᵥ encode nN nG (castVec pg) (castVec θ) + ε := by
  have hr := real_feasible_and_gap_le_of_checks (numRows nN nE nG) (numVars nN nG)
    (ratLpMatrix nN nE nG tail head b gbus ref) (ratLpRhs nN nE nG d pmin pmax fmin fmax)
    (ratLpObjective nN nG cost) (ratEncode nN nG pg θ)
    (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ε h
  have ex : (fun i => ((ratEncode nN nG pg θ i : ℚ) : ℝ)) =
      encode nN nG (castVec pg) (castVec θ) := castVec_ratEncode nN nG pg θ
  have eb : (fun j => ((ratLpRhs nN nE nG d pmin pmax fmin fmax j : ℚ) : ℝ)) =
      lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) :=
    castVec_ratLpRhs nN nE nG d pmin pmax fmin fmax
  have ec : (fun i => ((ratLpObjective nN nG cost i : ℚ) : ℝ)) =
      lpObjective nN nG (castVec cost) := castVec_ratLpObjective nN nG cost
  have ex' : ∀ i, ((ratEncode nN nG pg θ i : ℚ) : ℝ) = encode nN nG (castVec pg) (castVec θ) i :=
    fun i => congrFun ex i
  have eb' : ∀ j, ((ratLpRhs nN nE nG d pmin pmax fmin fmax j : ℚ) : ℝ) =
      lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) j :=
    fun j => congrFun eb j
  have ec' : ∀ i, ((ratLpObjective nN nG cost i : ℚ) : ℝ) = lpObjective nN nG (castVec cost) i :=
    fun i => congrFun ec i
  rw [ratLpMatrix_map] at hr
  simp only [ex', eb', ec'] at hr
  obtain ⟨⟨h0, h1⟩, -, -, h4⟩ := hr
  exact ⟨h0, h1, h4⟩

/-! ## G. Headline -/

/-- Headline: an accepted exact rational certificate proves that its
primal dispatch is feasible for the cast data, that `dualLowerBound`
bounds the cost of every feasible real dispatch, that the witness cost
lies within `ε` above that bound, and hence that the witness cost is
within `ε` of the cost of every feasible real dispatch. -/
theorem dispatch_certificate_correct (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ) (ε : ℚ)
    (h : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo ε = true) :
    IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
        (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
        (castVec pg) (castVec θ) ∧
      (∀ pg' θ', IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
          (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) pg' θ' →
        ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) ≤
          dispatchCost nG (castVec cost) pg') ∧
      0 ≤ dispatchCost nG (castVec cost) (castVec pg) -
          ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) ∧
      dispatchCost nG (castVec cost) (castVec pg) -
          ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) ≤
        (ε : ℝ) ∧
      ∀ pg' θ', IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
          (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) pg' θ' →
        dispatchCost nG (castVec cost) (castVec pg) ≤
          dispatchCost nG (castVec cost) pg' + (ε : ℝ) := by
  obtain ⟨hfeas, -, hg0, hgε⟩ := (checksDispatchCertificate_eq_true_iff nN nE nG tail head b
    gbus d ref pmin pmax fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo ε).1 h
  have hr := real_feasible_and_gap_le_of_checks (numRows nN nE nG) (numVars nN nG)
    (ratLpMatrix nN nE nG tail head b gbus ref) (ratLpRhs nN nE nG d pmin pmax fmin fmax)
    (ratLpObjective nN nG cost) (ratEncode nN nG pg θ)
    (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ε h
  have ec : (fun i => ((ratLpObjective nN nG cost i : ℚ) : ℝ)) =
      lpObjective nN nG (castVec cost) := castVec_ratLpObjective nN nG cost
  have ec' : ∀ i, ((ratLpObjective nN nG cost i : ℚ) : ℝ) = lpObjective nN nG (castVec cost) i :=
    fun i => congrFun ec i
  rw [ratLpMatrix_map] at hr
  simp only [ec'] at hr
  obtain ⟨-, ⟨hy, hc⟩, -, -⟩ := hr
  have hdot : ∀ {k : ℕ} (u v : Fin k → ℚ), ((u ⬝ᵥ v : ℚ) : ℝ) = castVec u ⬝ᵥ castVec v := by
    intro k u v
    have := RingHom.map_dotProduct (Rat.castHom ℝ) u v
    rw [Rat.coe_castHom] at this
    exact this
  have hcost : dispatchCost nG (castVec cost) (castVec pg) = ((cost ⬝ᵥ pg : ℚ) : ℝ) :=
    (hdot cost pg).symm
  have hlb : ∀ pg' θ', IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
      (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) pg' θ' →
      ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) ≤
        dispatchCost nG (castVec cost) pg' := by
    intro pg' θ' hf
    obtain ⟨hz, hAz⟩ := encode_feasible nN nE nG tail head (castVec b) gbus (castVec d) ref
      (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) pg' θ' hf
    have w1 : lpObjective nN nG (castVec cost) ⬝ᵥ encode nN nG pg' θ' ≤
        (Matrix.transpose (lpMatrix nN nE nG tail head (castVec b) gbus ref) *ᵥ
          castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo)) ⬝ᵥ encode nN nG pg' θ' :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hc i) (hz i))
    have w2 : (Matrix.transpose (lpMatrix nN nE nG tail head (castVec b) gbus ref) *ᵥ
          castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo)) ⬝ᵥ encode nN nG pg' θ' =
        castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ⬝ᵥ
          (lpMatrix nN nE nG tail head (castVec b) gbus ref *ᵥ encode nN nG pg' θ') := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    have w3 : castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ⬝ᵥ
          (lpMatrix nN nE nG tail head (castVec b) gbus ref *ᵥ encode nN nG pg' θ') ≤
        castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ⬝ᵥ
          lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
            (castVec fmax) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hAz j) (hy j))
    have w4 : castVec (dualVector nN nE nG lam ρ μhi μlo ηhi ηlo) ⬝ᵥ
          lpRhs nN nE nG (castVec d) (castVec pmin) (castVec pmax) (castVec fmin)
            (castVec fmax) =
        -((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) := by
      rw [← castVec_ratLpRhs, dotProduct_comm, ← hdot, ratLpRhs_dotProduct_dualVector,
        Rat.cast_neg]
    have w5 := lpObjective_encode nN nG (castVec cost) pg' θ'
    have key := w1.trans (w2 ▸ w3)
    rw [w4, w5] at key
    exact neg_le_neg_iff.mp key
  have hg0R : (0 : ℝ) ≤ dispatchCost nG (castVec cost) (castVec pg) -
      ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) := by
    rw [hcost, ← Rat.cast_sub]
    exact_mod_cast hg0
  have hgεR : dispatchCost nG (castVec cost) (castVec pg) -
      ((dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo : ℚ) : ℝ) ≤
        (ε : ℝ) := by
    rw [hcost, ← Rat.cast_sub]
    exact_mod_cast hgε
  refine ⟨hfeas, hlb, hg0R, hgεR, fun pg' θ' hf => ?_⟩
  have := hlb pg' θ' hf
  grind

/-- Zero checked gap proves global optimality: an accepted certificate at
`ε = 0` gives a feasible dispatch of minimum cost over all feasible real
dispatches, and that cost equals the certified lower bound. -/
theorem dispatch_optimal_of_checks_zero (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℚ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℚ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℚ) (fmin fmax : Fin nE → ℚ) (cost : Fin nG → ℚ)
    (pg : Fin nG → ℚ) (θ : Fin nN → ℚ) (lam : Fin nN → ℚ) (ρ : ℚ)
    (μhi μlo : Fin nG → ℚ) (ηhi ηlo : Fin nE → ℚ)
    (h : checksDispatchCertificate nN nE nG tail head b gbus d ref pmin pmax fmin fmax cost
      pg θ lam ρ μhi μlo ηhi ηlo 0 = true) :
    IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
        (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax)
        (castVec pg) (castVec θ) ∧
      (∀ pg' θ', IsDispatchFeasible nN nE nG tail head (castVec b) gbus (castVec d) ref
          (castVec pmin) (castVec pmax) (castVec fmin) (castVec fmax) pg' θ' →
        dispatchCost nG (castVec cost) (castVec pg) ≤ dispatchCost nG (castVec cost) pg') ∧
      cost ⬝ᵥ pg = dualLowerBound nN nE nG d pmin pmax fmin fmax lam μhi μlo ηhi ηlo := by
  obtain ⟨hfeas, -, hg0, hgε⟩ := (checksDispatchCertificate_eq_true_iff nN nE nG tail head b
    gbus d ref pmin pmax fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo 0).1 h
  obtain ⟨-, -, -, -, hopt⟩ := dispatch_certificate_correct nN nE nG tail head b gbus d ref
    pmin pmax fmin fmax cost pg θ lam ρ μhi μlo ηhi ηlo 0 h
  refine ⟨hfeas, fun pg' θ' hf => ?_, ?_⟩
  · have := hopt pg' θ' hf
    rwa [Rat.cast_zero, add_zero] at this
  · exact sub_eq_zero.mp (le_antisymm hgε hg0)

end PhyslibExt.Circuits.DCDispatchCertificate
