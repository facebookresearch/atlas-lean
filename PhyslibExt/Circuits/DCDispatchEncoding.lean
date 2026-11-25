/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.LosslessDCFlowModel
public import MathlibExt.Analysis.Convex.LinearProgrammingCertificate
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# DC economic dispatch as a canonical linear program

## i. Overview

A finite network has buses `Fin nN`, labeled oriented branches `Fin nE`
with tail and head maps and real susceptances `b`, and generators
`Fin nG` placed at buses by `gbus`. The network model is the lossless DC
model of `PhyslibExt.Circuits.LosslessDCFlowModel`: the full weighted
Laplacian `L_b = B * diag(b) * Bᵀ` and the branch flow
`f = diag(b) * Bᵀ * θ` for the tail-positive incidence `B`. A dispatch
`(pg, θ)` is feasible for a fixed demand `d`, reference bus `ref`,
generator limits `pmin ≤ pg ≤ pmax` and flow limits `fmin ≤ f ≤ fmax`
when `L_b * θ = Cgen * pg - d` and `θ ref = 0`, where `Cgen` places each
generator at its bus. Its cost is the linear objective `cost ⬝ᵥ pg`, to
be minimized.

The dispatch problem is encoded into the inequality form used by
`MathlibExt.Analysis.Convex.LPWeakDuality.weak_linear_programming_duality`,
`MathlibExt.Analysis.Convex.LPCertificate.feasible_pair_equal_objectives_optimal`
and `MathlibExt.Analysis.Convex.RationalLPCertificate.checksLPGap`:
maximize `c ⬝ᵥ x` subject to `x ≥ 0` and `A *ᵥ x ≤ rhs`, with `Fin m`
rows and `Fin n` columns. The free variables `(pg, θ)` are split into
nonnegative positive and negative parts, each equality becomes two
opposite inequalities, the reference equation becomes two rows, and each
two-sided bound becomes two rows; the minimized cost becomes the
maximized objective `-cost ⬝ᵥ pg`. The split is carried out for this
model only: no general linear-program structure or generic conversion
is introduced.

Feasible dispatches and feasible LP points correspond in both
directions through `encode` and the decoding maps, `decode ∘ encode` is
the identity, and the LP objective of every LP point is minus the
dispatch cost of its decoding, so LP optimality and minimum-cost
dispatch transfer both ways. The split is not unique, so the converse
direction is existential. Neither direction needs a grounded Laplacian
solve, positive susceptances, or ordered bounds: inconsistent data make
both problems infeasible.

## ii. Key results

- `dispatch_encoding_correct`: encoded feasible dispatches are feasible
  LP points with the same decoding and objective minus the cost, and
  every feasible LP point decodes to a feasible dispatch with that
  objective.
- `dispatchFeasible_iff_exists_lp`, `dispatch_nonempty_iff_lp_nonempty`:
  feasibility in both directions.
- `decode_optimal`, `encode_optimal`: optimality transfer.

## iii. Table of contents

- A. The DC dispatch problem
- B. The canonical LP encoding
- C. Reuse of the canonical DC model
- D. Encoding and decoding
- E. Feasibility in both directions
- F. Optimality transfer
- G. Headline

## iv. References

- A. J. Wood, B. F. Wollenberg, and G. B. Sheblé, *Power Generation,
  Operation, and Control*, 3rd ed., Wiley, 2014: economic dispatch and
  the DC optimal power flow as a linear program.
- B. Stott, J. Jardim, and O. Alsaç, "DC Power Flow Revisited,"
  *IEEE Transactions on Power Systems* 24(3), 2009, 1290-1300: the
  lossless DC network model.
- D. Bertsimas and J. N. Tsitsiklis, *Introduction to Linear
  Optimization*, Athena Scientific, 1997, Section 1.1: reduction to
  inequality form by splitting free variables and equalities.

## A. The DC dispatch problem
-/

@[expose] public section

namespace PhyslibExt.Circuits.DCDispatchEncoding

open Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.LosslessDCFlowModel

/-- Generator-to-bus incidence `Cgen v g = 1` when generator `g` sits at
bus `v`, and `0` otherwise. -/
def generatorIncidence (nN nG : ℕ) (gbus : Fin nG → Fin nN) :
    Matrix (Fin nN) (Fin nG) ℝ :=
  fun v g => if gbus g = v then 1 else 0

/-- Branch-flow coefficient matrix `diag(b) * Bᵀ`, the matrix through
which the canonical DC branch flow is defined. -/
noncomputable def branchFlowMatrix (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) : Matrix (Fin nE) (Fin nN) ℝ :=
  Matrix.diagonal b * Matrix.transpose (electricalIncidence tail head)

/-- DC dispatch feasibility: the nodal balance `L_b * θ = Cgen * pg - d`,
the reference angle `θ ref = 0`, the generator limits and the branch
flow limits, all on the canonical DC model. -/
def IsDispatchFeasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ)
    (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) : Prop :=
  weightedLaplacian nN nE tail head b *ᵥ θ = generatorIncidence nN nG gbus *ᵥ pg - d ∧
    θ ref = 0 ∧
    (∀ g, pmin g ≤ pg g ∧ pg g ≤ pmax g) ∧
    (∀ e, fmin e ≤ dcBranchFlow nN nE tail head b θ e ∧
      dcBranchFlow nN nE tail head b θ e ≤ fmax e)

/-- Linear dispatch cost `cost ⬝ᵥ pg`, to be minimized. -/
def dispatchCost (nG : ℕ) (cost : Fin nG → ℝ) (pg : Fin nG → ℝ) : ℝ :=
  cost ⬝ᵥ pg

/-! ## B. The canonical LP encoding -/

/-- Number of LP columns: positive and negative parts of the free
variables `(pg, θ)`. -/
abbrev numVars (nN nG : ℕ) : ℕ :=
  (nG + nN) + (nG + nN)

/-- Number of LP rows: balance (twice), reference (twice), generator
limits (twice), flow limits (twice). -/
abbrev numRows (nN nE nG : ℕ) : ℕ :=
  nN + nN + 1 + 1 + nG + nG + nE + nE

/-- One block of constraint rows on the free variables `(pg, θ)`, with
generation coefficients `P` and angle coefficients `T`. -/
def freeRows {r : ℕ} (nN nG : ℕ) (P : Matrix (Fin r) (Fin nG) ℝ)
    (T : Matrix (Fin r) (Fin nN) ℝ) : Fin r → Fin (nG + nN) → ℝ :=
  fun i => Fin.append (P i) (T i)

/-- Reference row selecting the angle of bus `ref`. -/
def referenceRow (nN : ℕ) (ref : Fin nN) : Matrix (Fin 1) (Fin nN) ℝ :=
  fun _ v => if v = ref then 1 else 0

/-- Constraint matrix on the free variables `(pg, θ)`, in row order:
`-Cgen pg + L_b θ ≤ -d`, `Cgen pg - L_b θ ≤ d`, `θ ref ≤ 0`,
`-θ ref ≤ 0`, `pg ≤ pmax`, `-pg ≤ -pmin`, `f ≤ fmax`, `-f ≤ -fmin`. -/
noncomputable def freeConstraintMatrix (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (ref : Fin nN) :
    Matrix (Fin (numRows nN nE nG)) (Fin (nG + nN)) ℝ :=
  Matrix.of <|
    Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append
      (freeRows nN nG (-generatorIncidence nN nG gbus) (weightedLaplacian nN nE tail head b))
      (freeRows nN nG (generatorIncidence nN nG gbus) (-weightedLaplacian nN nE tail head b)))
      (freeRows nN nG (0 : Matrix (Fin 1) (Fin nG) ℝ) (referenceRow nN ref)))
      (freeRows nN nG (0 : Matrix (Fin 1) (Fin nG) ℝ) (-referenceRow nN ref)))
      (freeRows nN nG (1 : Matrix (Fin nG) (Fin nG) ℝ) (0 : Matrix (Fin nG) (Fin nN) ℝ)))
      (freeRows nN nG (-1 : Matrix (Fin nG) (Fin nG) ℝ) (0 : Matrix (Fin nG) (Fin nN) ℝ)))
      (freeRows nN nG (0 : Matrix (Fin nE) (Fin nG) ℝ) (branchFlowMatrix nN nE tail head b)))
      (freeRows nN nG (0 : Matrix (Fin nE) (Fin nG) ℝ) (-branchFlowMatrix nN nE tail head b))

/-- Canonical LP constraint matrix `A`: the free constraint matrix on
the positive parts and its negation on the negative parts. -/
noncomputable def lpMatrix (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (ref : Fin nN) :
    Matrix (Fin (numRows nN nE nG)) (Fin (numVars nN nG)) ℝ :=
  Matrix.of fun i =>
    Fin.append (freeConstraintMatrix nN nE nG tail head b gbus ref i)
      (-freeConstraintMatrix nN nE nG tail head b gbus ref i)

/-- Canonical LP right-hand side, in the row order of
`freeConstraintMatrix`. -/
def lpRhs (nN nE nG : ℕ) (d : Fin nN → ℝ) (pmin pmax : Fin nG → ℝ)
    (fmin fmax : Fin nE → ℝ) : Fin (numRows nN nE nG) → ℝ :=
  Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append (Fin.append
    (-d) d) (0 : Fin 1 → ℝ)) (0 : Fin 1 → ℝ)) pmax) (-pmin)) fmax) (-fmin)

/-- Canonical LP objective (maximized): `-cost` on the positive
generation parts, `cost` on the negative generation parts, zero on the
angle parts. -/
def lpObjective (nN nG : ℕ) (cost : Fin nG → ℝ) : Fin (numVars nN nG) → ℝ :=
  Fin.append (Fin.append (-cost) (0 : Fin nN → ℝ)) (Fin.append cost (0 : Fin nN → ℝ))

/-- Free variables recovered from an LP point: positive part minus
negative part. -/
def freePart (nN nG : ℕ) (x : Fin (numVars nN nG) → ℝ) : Fin (nG + nN) → ℝ :=
  fun a => x (Fin.castAdd (nG + nN) a) - x (Fin.natAdd (nG + nN) a)

/-- Generation decoded from an LP point. -/
def decodeGeneration (nN nG : ℕ) (x : Fin (numVars nN nG) → ℝ) : Fin nG → ℝ :=
  fun g => freePart nN nG x (Fin.castAdd nN g)

/-- Angles decoded from an LP point. -/
def decodeAngle (nN nG : ℕ) (x : Fin (numVars nN nG) → ℝ) : Fin nN → ℝ :=
  fun v => freePart nN nG x (Fin.natAdd nG v)

/-- LP point encoding a dispatch: positive parts `max z 0` followed by
negative parts `max (-z) 0` of the free vector `z = (pg, θ)`. -/
noncomputable def encode (nN nG : ℕ) (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    Fin (numVars nN nG) → ℝ :=
  Fin.append (fun a => max (Fin.append pg θ a) 0) (fun a => max (-Fin.append pg θ a) 0)

private lemma forall_fin_add (m n : ℕ) (P : Fin (m + n) → Prop) :
    (∀ j, P j) ↔ (∀ a : Fin m, P (Fin.castAdd n a)) ∧ (∀ b : Fin n, P (Fin.natAdd m b)) := by
  constructor
  · intro h; exact ⟨fun a => h _, fun b => h _⟩
  · rintro ⟨h1, h2⟩ j; exact Fin.addCases h1 h2 j

private lemma append_dotProduct (m n : ℕ) (u1 : Fin m → ℝ) (v1 : Fin n → ℝ)
    (z : Fin (m + n) → ℝ) :
    (Fin.append u1 v1) ⬝ᵥ z =
      u1 ⬝ᵥ (fun i => z (Fin.castAdd n i)) + v1 ⬝ᵥ (fun j => z (Fin.natAdd m j)) := by
  simp only [dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

private lemma max_pos_neg (z : ℝ) : max z 0 - max (-z) 0 = z := by
  rcases le_total z 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]

private lemma freePart_encode (nN nG : ℕ) (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    freePart nN nG (encode nN nG pg θ) = Fin.append pg θ := by
  funext a
  simp only [freePart, encode, Fin.append_left, Fin.append_right]
  exact max_pos_neg _

private lemma freeRows_dotProduct (nN nG : ℕ) (r : ℕ) (P : Matrix (Fin r) (Fin nG) ℝ)
    (T : Matrix (Fin r) (Fin nN) ℝ) (i : Fin r) (z : Fin (nG + nN) → ℝ) :
    (freeRows nN nG P T i) ⬝ᵥ z =
      (P i) ⬝ᵥ (fun g => z (Fin.castAdd nN g)) + (T i) ⬝ᵥ (fun v => z (Fin.natAdd nG v)) := by
  have h : freeRows nN nG P T i = Fin.append (P i) (T i) := rfl
  rw [h]
  exact append_dotProduct nG nN (P i) (T i) z

private lemma mulVec_apply_dot (m n : ℕ) (M : Matrix (Fin m) (Fin n) ℝ)
    (v : Fin n → ℝ) (i : Fin m) : (M *ᵥ v) i = (M i) ⬝ᵥ v := rfl

private lemma of_apply_row (m n : ℕ) (f : Fin m → Fin n → ℝ) (j : Fin m) :
    (Matrix.of f) j = f j := rfl

private lemma row_dot (r s : ℕ) (M : Matrix (Fin r) (Fin s) ℝ) (i : Fin r)
    (w : Fin s → ℝ) : (M i) ⬝ᵥ w = (M *ᵥ w) i := rfl

private lemma neg_row_dot (r s : ℕ) (M : Matrix (Fin r) (Fin s) ℝ) (i : Fin r)
    (w : Fin s → ℝ) : (((-M) i) ⬝ᵥ w) = -((M *ᵥ w) i) := by
  change (-(M i)) ⬝ᵥ w = -((M *ᵥ w) i)
  rw [neg_dotProduct, row_dot]

private lemma zero_dot (r s : ℕ) (i : Fin r) (w : Fin s → ℝ) :
    (((0 : Matrix (Fin r) (Fin s) ℝ) i) ⬝ᵥ w) = 0 := by
  change (0 : Fin s → ℝ) ⬝ᵥ w = 0
  exact zero_dotProduct _

private lemma one_dot (n : ℕ) (i : Fin n) (w : Fin n → ℝ) :
    (((1 : Matrix (Fin n) (Fin n) ℝ) i) ⬝ᵥ w) = w i := by
  change ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ w) i = w i
  rw [Matrix.one_mulVec]

private lemma neg_one_dot (n : ℕ) (i : Fin n) (w : Fin n → ℝ) :
    (((-1 : Matrix (Fin n) (Fin n) ℝ) i) ⬝ᵥ w) = -(w i) := by
  change (-((1 : Matrix (Fin n) (Fin n) ℝ) i)) ⬝ᵥ w = -(w i)
  rw [neg_dotProduct, one_dot]

private lemma refRow_dot (nN : ℕ) (ref : Fin nN) (u : Fin 1) (w : Fin nN → ℝ) :
    ((referenceRow nN ref u) ⬝ᵥ w) = w ref := by
  change ∑ v, (referenceRow nN ref u v) * w v = _
  change ∑ v, ((if v = ref then (1 : ℝ) else 0) * w v) = _
  have h1 : ∀ v : Fin nN, ((if v = ref then (1 : ℝ) else 0) * w v) =
      (if v = ref then w v else 0) := by
    intro v; by_cases h : v = ref <;> simp [h]
  simp only [h1]
  rw [Finset.sum_ite_eq']
  simp

private lemma neg_refRow_dot (nN : ℕ) (ref : Fin nN) (u : Fin 1) (w : Fin nN → ℝ) :
    (((-referenceRow nN ref) u) ⬝ᵥ w) = -(w ref) := by
  change (-(referenceRow nN ref u)) ⬝ᵥ w = -(w ref)
  rw [neg_dotProduct, refRow_dot]

/-! ## C. Reuse of the canonical DC model -/

/-- The generator incidence collects the generation placed at each bus. -/
lemma generatorIncidence_mulVec_apply (nN nG : ℕ) (gbus : Fin nG → Fin nN)
    (pg : Fin nG → ℝ) (v : Fin nN) :
    (generatorIncidence nN nG gbus *ᵥ pg) v =
      ∑ g ∈ (Finset.univ : Finset (Fin nG)).filter (fun g => gbus g = v), pg g := by
  change (generatorIncidence nN nG gbus v) ⬝ᵥ pg = _
  change ∑ g, (generatorIncidence nN nG gbus v g) * pg g = _
  change ∑ g, ((if gbus g = v then (1 : ℝ) else 0) * pg g) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases h : gbus g = v <;> simp [h]

/-- The branch-flow coefficient matrix applied to the angles is the
canonical DC branch flow. -/
lemma branchFlowMatrix_mulVec (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    branchFlowMatrix nN nE tail head b *ᵥ θ = dcBranchFlow nN nE tail head b θ := by
  rfl

/-- The dispatch balance is the canonical DC injection balance
`p = Cgen * pg - d`. -/
lemma balance_iff_dcInjection (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ)
    (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    weightedLaplacian nN nE tail head b *ᵥ θ = generatorIncidence nN nG gbus *ᵥ pg - d ↔
      dcInjection nN nE tail head b θ = generatorIncidence nN nG gbus *ᵥ pg - d := by
  rw [dcInjection_eq_weightedLaplacian_mulVec]

/-! ## D. Encoding and decoding -/

/-- Encoded LP points are nonnegative. -/
lemma encode_nonneg (nN nG : ℕ) (pg : Fin nG → ℝ) (θ : Fin nN → ℝ)
    (i : Fin (numVars nN nG)) : 0 ≤ encode nN nG pg θ i := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
    simp only [encode, Fin.append_left, Fin.append_right]
  · exact le_max_right _ _
  · exact le_max_right _ _

/-- Decoding an encoded point returns its generation. -/
lemma decodeGeneration_encode (nN nG : ℕ) (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    decodeGeneration nN nG (encode nN nG pg θ) = pg := by
  funext g
  change freePart nN nG (encode nN nG pg θ) (Fin.castAdd nN g) = pg g
  rw [freePart_encode]
  exact Fin.append_left pg θ g

/-- Decoding an encoded point returns its angles. -/
lemma decodeAngle_encode (nN nG : ℕ) (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    decodeAngle nN nG (encode nN nG pg θ) = θ := by
  funext v
  change freePart nN nG (encode nN nG pg θ) (Fin.natAdd nG v) = θ v
  rw [freePart_encode]
  exact Fin.append_right pg θ v

/-- The LP matrix acts through the free part of its argument. -/
lemma lpMatrix_mulVec (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (ref : Fin nN)
    (x : Fin (numVars nN nG) → ℝ) :
    lpMatrix nN nE nG tail head b gbus ref *ᵥ x =
      freeConstraintMatrix nN nE nG tail head b gbus ref *ᵥ freePart nN nG x := by
  have hF : ∀ j, lpMatrix nN nE nG tail head b gbus ref j =
      Fin.append (freeConstraintMatrix nN nE nG tail head b gbus ref j)
        (-freeConstraintMatrix nN nE nG tail head b gbus ref j) := fun j => rfl
  funext j
  change (lpMatrix nN nE nG tail head b gbus ref j) ⬝ᵥ x =
    (freeConstraintMatrix nN nE nG tail head b gbus ref j) ⬝ᵥ freePart nN nG x
  rw [hF j, append_dotProduct, neg_dotProduct]
  rw [show freePart nN nG x = (fun a => x (Fin.castAdd (nG + nN) a)) -
      (fun a => x (Fin.natAdd (nG + nN) a)) from rfl, dotProduct_sub, sub_eq_add_neg]

/-- The LP objective of any LP point is minus the dispatch cost of its
decoded generation. -/
theorem lpObjective_dotProduct (nN nG : ℕ) (cost : Fin nG → ℝ)
    (x : Fin (numVars nN nG) → ℝ) :
    lpObjective nN nG cost ⬝ᵥ x = -dispatchCost nG cost (decodeGeneration nN nG x) := by
  have hA : ∀ z : Fin (nG + nN) → ℝ, (Fin.append (-cost) (0 : Fin nN → ℝ)) ⬝ᵥ z =
      (-cost) ⬝ᵥ (fun g => z (Fin.castAdd nN g)) := by
    intro z
    rw [append_dotProduct, zero_dotProduct, add_zero]
  have hB : ∀ z : Fin (nG + nN) → ℝ, (Fin.append cost (0 : Fin nN → ℝ)) ⬝ᵥ z =
      cost ⬝ᵥ (fun g => z (Fin.castAdd nN g)) := by
    intro z
    rw [append_dotProduct, zero_dotProduct, add_zero]
  have hdec : decodeGeneration nN nG x =
      (fun g => x (Fin.castAdd (nG + nN) (Fin.castAdd nN g))) -
      (fun g => x (Fin.natAdd (nG + nN) (Fin.castAdd nN g))) := rfl
  unfold dispatchCost
  change (Fin.append (Fin.append (-cost) (0 : Fin nN → ℝ))
      (Fin.append cost (0 : Fin nN → ℝ))) ⬝ᵥ x = -(cost ⬝ᵥ decodeGeneration nN nG x)
  rw [append_dotProduct, hA, hB, neg_dotProduct, hdec, dotProduct_sub]
  ring

/-- The LP objective of an encoded dispatch is minus its cost. -/
theorem lpObjective_encode (nN nG : ℕ) (cost : Fin nG → ℝ) (pg : Fin nG → ℝ)
    (θ : Fin nN → ℝ) :
    lpObjective nN nG cost ⬝ᵥ encode nN nG pg θ = -dispatchCost nG cost pg := by
  rw [lpObjective_dotProduct, decodeGeneration_encode]

/-! ## E. Feasibility in both directions -/

/-- A feasible dispatch encodes to a feasible point of the canonical LP. -/
theorem encode_feasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ)
    (pg : Fin nG → ℝ) (θ : Fin nN → ℝ)
    (h : IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ) :
    (∀ i, 0 ≤ encode nN nG pg θ i) ∧
      ∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ encode nN nG pg θ) j ≤
        lpRhs nN nE nG d pmin pmax fmin fmax j := by
  have h' : (weightedLaplacian nN nE tail head b *ᵥ θ =
      generatorIncidence nN nG gbus *ᵥ pg - d) ∧
      (θ ref = 0) ∧
      (∀ g, pmin g ≤ pg g ∧ pg g ≤ pmax g) ∧
      (∀ e, fmin e ≤ dcBranchFlow nN nE tail head b θ e ∧
        dcBranchFlow nN nE tail head b θ e ≤ fmax e) := h
  obtain ⟨hbal, href, hgen, hflow⟩ := h'
  refine ⟨fun i => encode_nonneg _ _ _ _ i, ?_⟩
  rw [lpMatrix_mulVec, freePart_encode]
  rw [forall_fin_add, forall_fin_add, forall_fin_add, forall_fin_add,
    forall_fin_add, forall_fin_add, forall_fin_add]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro v
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [neg_row_dot, row_dot]
    simp only [Pi.neg_apply]
    have hbalv := congrFun hbal v
    simp only [Pi.sub_apply] at hbalv
    linarith
  · intro v
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [neg_row_dot, row_dot]
    have hbalv := congrFun hbal v
    simp only [Pi.sub_apply] at hbalv
    linarith
  · intro u
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [zero_dot, refRow_dot, zero_add]
    have h0 : ((0 : Fin 1 → ℝ) u) = 0 := rfl
    rw [h0]
    linarith
  · intro u
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [zero_dot, neg_refRow_dot, zero_add]
    have h0 : ((0 : Fin 1 → ℝ) u) = 0 := rfl
    rw [h0]
    linarith
  · intro g
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [one_dot, zero_dot, add_zero]
    exact (hgen g).2
  · intro g
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [neg_one_dot, zero_dot, add_zero]
    simp only [Pi.neg_apply]
    exact neg_le_neg (hgen g).1
  · intro e
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [zero_dot, row_dot, zero_add, branchFlowMatrix_mulVec]
    exact (hflow e).2
  · intro e
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_right, lpRhs]
    rw [freeRows_dotProduct]
    simp only [Fin.append_left, Fin.append_right]
    rw [zero_dot, neg_row_dot, zero_add, branchFlowMatrix_mulVec]
    simp only [Pi.neg_apply]
    exact neg_le_neg (hflow e).1

/-- A feasible point of the canonical LP decodes to a feasible dispatch. -/
theorem decode_feasible (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ)
    (x : Fin (numVars nN nG) → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x) j ≤
      lpRhs nN nE nG d pmin pmax fmin fmax j) :
    IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax
      (decodeGeneration nN nG x) (decodeAngle nN nG x) := by
  rw [lpMatrix_mulVec] at hAx
  rw [forall_fin_add, forall_fin_add, forall_fin_add, forall_fin_add,
    forall_fin_add, forall_fin_add, forall_fin_add] at hAx
  obtain ⟨⟨⟨⟨⟨⟨⟨hAx0, hAx1⟩, hAx2⟩, hAx3⟩, hAx4⟩, hAx5⟩, hAx6⟩, hAx7⟩ := hAx
  have h0 : ∀ v : Fin nN, -((generatorIncidence nN nG gbus *ᵥ decodeGeneration nN nG x) v) +
      ((weightedLaplacian nN nE tail head b *ᵥ decodeAngle nN nG x) v) ≤ -(d v) := by
    intro v
    have hv := hAx0 v
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, lpRhs] at hv
    rw [freeRows_dotProduct, neg_row_dot, row_dot] at hv
    simp only [Pi.neg_apply] at hv
    exact hv
  have h1 : ∀ v : Fin nN, ((generatorIncidence nN nG gbus *ᵥ decodeGeneration nN nG x) v) +
      (-((weightedLaplacian nN nE tail head b *ᵥ decodeAngle nN nG x) v)) ≤ d v := by
    intro v
    have hv := hAx1 v
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, neg_row_dot, row_dot] at hv
    exact hv
  have h2 : ∀ u : Fin 1, decodeAngle nN nG x ref ≤ 0 := by
    intro u
    have hv := hAx2 u
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, zero_dot, refRow_dot, zero_add] at hv
    exact hv
  have h3 : ∀ u : Fin 1, -(decodeAngle nN nG x ref) ≤ 0 := by
    intro u
    have hv := hAx3 u
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, zero_dot, neg_refRow_dot, zero_add] at hv
    exact hv
  have h4 : ∀ g : Fin nG, decodeGeneration nN nG x g ≤ pmax g := by
    intro g
    have hv := hAx4 g
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, one_dot, zero_dot, add_zero] at hv
    exact hv
  have h5 : ∀ g : Fin nG, -(decodeGeneration nN nG x g) ≤ -(pmin g) := by
    intro g
    have hv := hAx5 g
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, neg_one_dot, zero_dot, add_zero] at hv
    simp only [Pi.neg_apply] at hv
    exact hv
  have h6 : ∀ e : Fin nE, dcBranchFlow nN nE tail head b (decodeAngle nN nG x) e ≤ fmax e := by
    intro e
    have hv := hAx6 e
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_left, Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, zero_dot, row_dot, zero_add, branchFlowMatrix_mulVec] at hv
    exact hv
  have h7 : ∀ e : Fin nE,
      -(dcBranchFlow nN nE tail head b (decodeAngle nN nG x) e) ≤ -(fmin e) := by
    intro e
    have hv := hAx7 e
    simp only [mulVec_apply_dot, freeConstraintMatrix, of_apply_row,
      Fin.append_right, lpRhs] at hv
    rw [freeRows_dotProduct, zero_dot, neg_row_dot, zero_add, branchFlowMatrix_mulVec] at hv
    simp only [Pi.neg_apply] at hv
    exact hv
  change (weightedLaplacian nN nE tail head b *ᵥ decodeAngle nN nG x =
      generatorIncidence nN nG gbus *ᵥ decodeGeneration nN nG x - d) ∧
    (decodeAngle nN nG x ref = 0) ∧
    (∀ g, pmin g ≤ decodeGeneration nN nG x g ∧ decodeGeneration nN nG x g ≤ pmax g) ∧
    (∀ e, fmin e ≤ dcBranchFlow nN nE tail head b (decodeAngle nN nG x) e ∧
      dcBranchFlow nN nE tail head b (decodeAngle nN nG x) e ≤ fmax e)
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext v
    have h0v := h0 v
    have h1v := h1 v
    simp only [Pi.sub_apply]
    linarith
  · apply le_antisymm (h2 0)
    have h3' := h3 0
    linarith
  · intro g
    constructor
    · have h5g := h5 g; linarith
    · exact h4 g
  · intro e
    constructor
    · have h7e := h7 e; linarith
    · exact h6 e

/-- Feasible dispatches are exactly the decodings of feasible LP points. -/
theorem dispatchFeasible_iff_exists_lp (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ)
    (pg : Fin nG → ℝ) (θ : Fin nN → ℝ) :
    IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ ↔
      ∃ x : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ x i) ∧
        (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x) j ≤
          lpRhs nN nE nG d pmin pmax fmin fmax j) ∧
        decodeGeneration nN nG x = pg ∧ decodeAngle nN nG x = θ := by
  constructor
  · intro h
    obtain ⟨hnn, hle⟩ := encode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ h
    exact ⟨_, hnn, hle, decodeGeneration_encode nN nG pg θ, decodeAngle_encode nN nG pg θ⟩
  · rintro ⟨x, hx, hAx, rfl, rfl⟩
    exact decode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax x hx hAx

/-- The dispatch problem is feasible exactly when the canonical LP is. -/
theorem dispatch_nonempty_iff_lp_nonempty (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ) :
    (∃ pg θ, IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ) ↔
      ∃ x : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ x i) ∧
        ∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x) j ≤
          lpRhs nN nE nG d pmin pmax fmin fmax j := by
  constructor
  · rintro ⟨pg, θ, h⟩
    obtain ⟨hnn, hle⟩ := encode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ h
    exact ⟨_, hnn, hle⟩
  · rintro ⟨x, hx, hAx⟩
    exact ⟨_, _, decode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax x hx hAx⟩

/-! ## F. Optimality transfer -/

/-- An optimal point of the canonical LP decodes to a minimum-cost
feasible dispatch. -/
theorem decode_optimal (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ) (cost : Fin nG → ℝ)
    (x : Fin (numVars nN nG) → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x) j ≤
      lpRhs nN nE nG d pmin pmax fmin fmax j)
    (hopt : ∀ x' : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ x' i) →
      (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x') j ≤
        lpRhs nN nE nG d pmin pmax fmin fmax j) →
      lpObjective nN nG cost ⬝ᵥ x' ≤ lpObjective nN nG cost ⬝ᵥ x) :
    ∀ pg θ, IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ →
      dispatchCost nG cost (decodeGeneration nN nG x) ≤ dispatchCost nG cost pg := by
  intro pg θ h
  obtain ⟨hnn, hle⟩ := encode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ h
  have hopt' := hopt (encode nN nG pg θ) hnn hle
  rw [lpObjective_encode, lpObjective_dotProduct] at hopt'
  linarith

/-- A minimum-cost feasible dispatch encodes to a feasible and optimal
point of the canonical LP. -/
theorem encode_optimal (nN nE nG : ℕ) (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ)
    (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ) (cost : Fin nG → ℝ)
    (pg : Fin nG → ℝ) (θ : Fin nN → ℝ)
    (h : IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ)
    (hopt : ∀ pg' θ',
      IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg' θ' →
        dispatchCost nG cost pg ≤ dispatchCost nG cost pg') :
    (∀ i, 0 ≤ encode nN nG pg θ i) ∧
      (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ encode nN nG pg θ) j ≤
        lpRhs nN nE nG d pmin pmax fmin fmax j) ∧
      ∀ x' : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ x' i) →
        (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x') j ≤
          lpRhs nN nE nG d pmin pmax fmin fmax j) →
        lpObjective nN nG cost ⬝ᵥ x' ≤ lpObjective nN nG cost ⬝ᵥ encode nN nG pg θ := by
  obtain ⟨hnn, hle⟩ := encode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ h
  refine ⟨hnn, hle, ?_⟩
  intro x' hx' hAx'
  have hdec := decode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax x' hx' hAx'
  have hle' := hopt _ _ hdec
  rw [lpObjective_dotProduct, lpObjective_encode]
  linarith

/-! ## G. Headline -/

/-- Headline: feasible dispatches correspond to feasible points of the
canonical LP in both directions, decoding inverts encoding, and the LP
objective is minus the dispatch cost, so the linear dispatch objective
is preserved up to the min-to-max sign. -/
theorem dispatch_encoding_correct (nN nE nG : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (gbus : Fin nG → Fin nN) (d : Fin nN → ℝ) (ref : Fin nN)
    (pmin pmax : Fin nG → ℝ) (fmin fmax : Fin nE → ℝ) (cost : Fin nG → ℝ) :
    (∀ pg θ,
      IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ →
        (∀ i, 0 ≤ encode nN nG pg θ i) ∧
        (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ encode nN nG pg θ) j ≤
          lpRhs nN nE nG d pmin pmax fmin fmax j) ∧
        decodeGeneration nN nG (encode nN nG pg θ) = pg ∧
        decodeAngle nN nG (encode nN nG pg θ) = θ ∧
        lpObjective nN nG cost ⬝ᵥ encode nN nG pg θ = -dispatchCost nG cost pg) ∧
    (∀ x : Fin (numVars nN nG) → ℝ, (∀ i, 0 ≤ x i) →
      (∀ j, (lpMatrix nN nE nG tail head b gbus ref *ᵥ x) j ≤
        lpRhs nN nE nG d pmin pmax fmin fmax j) →
        IsDispatchFeasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax
          (decodeGeneration nN nG x) (decodeAngle nN nG x) ∧
        lpObjective nN nG cost ⬝ᵥ x =
          -dispatchCost nG cost (decodeGeneration nN nG x)) := by
  constructor
  · intro pg θ h
    obtain ⟨hnn, hle⟩ := encode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax pg θ h
    exact ⟨hnn, hle, decodeGeneration_encode nN nG pg θ, decodeAngle_encode nN nG pg θ,
      lpObjective_encode nN nG cost pg θ⟩
  · intro x hx hAx
    exact ⟨decode_feasible nN nE nG tail head b gbus d ref pmin pmax fmin fmax x hx hAx,
      lpObjective_dotProduct nN nG cost x⟩

end PhyslibExt.Circuits.DCDispatchEncoding
