/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Rung-2 diagonal gap: diagonal + nondegeneracy does not imply `hsucc`
The only open rung-`≥ 2` input was `hsucc` at `j.val ≥ 2` / `n ≥ 3` under
diagonal/`IsDiagonalQuad` narrowing (`ConeNoEmbeddedRungs` §7 remainder item 1,
the (t3) obstruction). This module closes the question in the negative:

**Diagonality — even with pointwise nondegeneracy — does not imply rung-2
regularity.** Every diagonal `∀`-form over `hsucc`/`hreg` is false, with an
explicit witness needing only `(2 : K) ≠ 0` (no algebraic closedness).

## The witness

At `n = 3`, the diagonal structure constants `c` with diagonal vector
`d = (1, -1, 0)` at every equation index give bridge forms
`Fₖ = X₀² - X₁² =: S` for all `k`, hence
`Gₖ = rename(S) - z·xₖ`. Then with `H = x₀ - x₁`:

* `H * G₂ = (x₂ - x₁) * G₀ + (x₀ - x₂) * G₁ ∈ (G₀, G₁)`
  (`rung2_relation_of_diffs`, pure ring arithmetic from the `z`-linear
  differences `G₁ - G₀ = z * H`, `G₂ - G₀ = z * (x₀ - x₂)`);
* `H ∉ (G₀, G₁)`: evaluation at `(1, -1, 0, 0)` kills `G₀, G₁`
  (`S(1,-1,0) = 0`, `z = 0`) but sends `H ↦ 2 ≠ 0`.

So `G₂` is a zerodivisor mod `(G₀, G₁)` and rung-2 regularity fails, while
all `Fₖ = S ≠ 0` (pointwise nondegeneracy holds).

## What is proved here

* §0 `mkQuot_smul`, `rung2_relation_of_diffs`,
  `not_isSMulRegular_of_rung2_witness` (unconditional, general rings): the
  witness machine — a zerodivisor relation plus separating evaluation point
  kills `IsSMulRegular` on a two-generator quotient.
* §1 `not_hsucc_mkSystem_const_of_zero` (unconditional): for a constant
  family `F = const S` at `mkSystem 2`, zero data
  (`eval (v ∘ castSucc) S = 0`, `v last = 0`, `v x₀ ≠ v x₁`) implies
  `¬ SuccessiveSMulRegular`. Sharp necessary-condition form: any
  sufficient condition for rung-2 `hsucc` must exclude constant families
  (e.g. require independent/distinct coefficient vectors).
* §1 `hsucc_quad_forall_false` (unconditional given `(2 : K) ≠ 0`): the
  `IsDiagonalQuad` `hsucc` `∀`-form at `n = 2` is false
  (`S = X₀² - X₁²` is a diagonal quadric, `isDiagonalQuad_sgap`).
* §2 `diagWitness`, `isDiagonal_diagWitness`, `bridgeForms_diagWitness`:
  the diagonal-`c` witness at `n = 3` with computed bridge forms.
* §2 `hge2narrow_diagonal_forall_false`, `hge2_diagonal_forall_false`,
  `hsucc_diagonal_forall_false`, `hsucc_diagonal_nondeg_forall_false`
  (unconditional given `(2 : K) ≠ 0`): the `hge2` inputs of
  `RungDiagonal.hreg_ge1_diagonal_of_ge2narrow` /
  `RungDiagonal.hreg_ge1_diagonal_of_ge2`, the diagonal `hsucc` `∀`-form,
  and diagonal + rung-1-nondegeneracy `hsucc` `∀`-form are all false.

## Precise remainder (out of scope)

1. The obstruction is coefficient-matrix degeneracy (the witness has rank-1
   diagonal coefficients: every equation sees the same `S`). A
   sufficient condition for rung-2 `hsucc` must add coefficient genericity
   (e.g. linear independence of the diagonal coefficient vectors, or
   triangular support) — diagonality plus pointwise `F ≠ 0` is provably
   not enough (this file).
2. Even under such genericity, proving rung-2 regularity needs `k = 2`
   unmixedness machinery (the `HdimEq` route), the standing
   crux — the (t3) verdict (`TriangularRegularity`) is unaffected.
3. Characteristic 2 is out of scope for diagonal `hsucc`: the refutations in
   this file assume `(2 : K) ≠ 0` (the `H ↦ 2 = 0` witness here
   degenerates there).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint.Rung.RungRegular` §4 (`badConsts`, `hreg_forall_false`): proof pattern
  mirrored (zerodivisor relation + separating evaluation + prefix-span
  identification).
* `BridgeToFixedPoint.Rung.RungDiagonal`, `IsDiagonal`, `hreg_ge1_diagonal_of_ge2narrow`
  (refuted inputs live here); `BridgeToFixedPoint.ConeNoEmbeddedRungs`, `IsDiagonalQuad`
  (§6 SPEC), §7 remainder item 1 (closed here in the negative).
* `BridgeToFixedPoint.FixedPointFromBezout`, `bridgeSystem`, `bridgeForms`,
  `shiftConsts`, `shiftEquiv`, `statementIndex`.
* `Regularity.Avoid.AvoidanceApply`, `ofList_take_eq_span_image`;
  `Regularity.Avoid.RegularityBridge`, `SuccessiveSMulRegular`;
  `Dimension.RegularSequenceDimDrop`, `span_smul_top`;
  `Statement.Definitions`, `mkSystem`.

Mathlib v4.34.0:

* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/Algebra/GroupWithZero/Action/Regular.lean`).
* `Submodule.mkQ`, `map_smul` (as in `AvoidanceStep.quot_mk_smul`).
* `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.span_le`, `Ideal.subset_span`,
  `Ideal.mul_mem_left`, `RingHom.mem_ker`.
* `MvPolynomial.eval_rename`, `MvPolynomial.eval_X`, `Fin.sum_univ_three`.
-/


namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungDiagonalGap

open scoped BigOperators

/-! ## §0 The rung-2 witness machine (general rings) -/

/-- Quotient-smul push-through for a general ideal quotient (the
`AvoidanceStep.quot_mk_smul` proof, generalized from `Fin (n + 2)` to any
`R`; needed here at both `Fin 4` and `Fin (statementIndex 3 + 2)`). -/
theorem mkQuot_smul {R : Type*} [CommRing R] (J : Ideal R) (r f : R) :
    Ideal.Quotient.mk J (r • f) = r • Ideal.Quotient.mk J f :=
  map_smul (Submodule.mkQ J) r f

/-- The rung-2 relation: for `G`-values with `z`-linear differences, the
rung-0/rung-1 differences determine `H * G₂` in the span of `G₀, G₁`.
Pure commutative-ring arithmetic (`linear_combination`). -/
theorem rung2_relation_of_diffs {R : Type*} [CommRing R]
    (G₀ G₁ G₂ z x₀ x₁ x₂ : R)
    (e10 : G₁ - G₀ = z * (x₀ - x₁))
    (e20 : G₂ - G₀ = z * (x₀ - x₂)) :
    (x₀ - x₁) * G₂ = (x₂ - x₁) * G₀ + (x₀ - x₂) * G₁ := by
  linear_combination (x₀ - x₁) * e20 - (x₀ - x₂) * e10

/-- A zerodivisor relation plus a separating evaluation point kills
`IsSMulRegular` on a two-generator quotient: `G₂ • mk H = 0` (the relation
lies in the span) while `mk H ≠ 0` (the span lies in `ker φ` but
`φ H ≠ 0`). -/
theorem not_isSMulRegular_of_rung2_witness {R S : Type*} [CommRing R]
    [CommRing S] (G₀ G₁ G₂ H A B : R) (φ : R →+* S)
    (hrel : H * G₂ = A * G₀ + B * G₁)
    (hG0 : φ G₀ = 0) (hG1 : φ G₁ = 0) (hH : φ H ≠ 0) :
    ¬ IsSMulRegular
      (R ⧸ (Ideal.span {G₀, G₁} • (⊤ : Submodule R R))) G₂ := by
  intro hreg
  rw [RegularSequenceDimDrop.span_smul_top] at hreg
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg
  have hmem : H * G₂ ∈ Ideal.span {G₀, G₁} := by
    rw [hrel]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  have hsmul : G₂ • Ideal.Quotient.mk (Ideal.span {G₀, G₁}) H = 0 := by
    rw [← mkQuot_smul, smul_eq_mul, mul_comm G₂ H]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hne : Ideal.Quotient.mk (Ideal.span {G₀, G₁}) H ≠ 0 := by
    intro hcon
    rw [Ideal.Quotient.eq_zero_iff_mem] at hcon
    have hle : Ideal.span {G₀, G₁} ≤ RingHom.ker φ := by
      apply Ideal.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact RingHom.mem_ker.mpr hG0
      · exact RingHom.mem_ker.mpr hG1
    have hker := hle hcon
    rw [RingHom.mem_ker] at hker
    exact hH hker
  exact hne (hreg _ hsmul)

#print axioms mkQuot_smul
#print axioms rung2_relation_of_diffs
#print axioms not_isSMulRegular_of_rung2_witness

/-! ## §1 Constant diagonal families at `mkSystem`: sharp non-regularity -/

/-- The gap quadric `S = X₀² - X₁²`: diagonal, nonzero, vanishing at
`(1, -1, 0)` with `x₀ ≠ x₁`. -/
noncomputable def Sgap (K : Type*) [Field K] : MvPolynomial (Fin 3) K :=
  MvPolynomial.X (0 : Fin 3) ^ 2 - MvPolynomial.X (1 : Fin 3) ^ 2

/-- The gap evaluation point `(1, -1, 0, 0)` on `Fin 4` (val-defined, so
every coordinate reduces by `decide`). -/
def vgap (K : Type*) [Field K] : Fin 4 → K :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0

/-- `vgap` at `0` is `1`. -/
theorem vgap_castSucc_zero (K : Type*) [Field K] :
    vgap K (Fin.castSucc (0 : Fin 3)) = 1 := by
  simp [vgap]

/-- `vgap` at `1` is `-1`. -/
theorem vgap_castSucc_one (K : Type*) [Field K] :
    vgap K (Fin.castSucc (1 : Fin 3)) = -1 := by
  have n10 : (1 : ℕ) ≠ 0 := by decide
  simp [vgap, n10]

/-- `vgap` at the last index is `0`. -/
theorem vgap_last (K : Type*) [Field K] :
    vgap K (Fin.last (2 + 1)) = 0 := by
  have n30 : 2 + 1 ≠ 0 := by decide
  have n31 : 2 + 1 ≠ 1 := by decide
  simp [vgap, n30, n31]

/-- `z`-linear differences for a constant `mkSystem 2` family: the renamed
quadrics cancel. -/
theorem mkSystem_const_diff (K : Type*) [Field K]
    (S : MvPolynomial (Fin 3) K) (a b : Fin 3) :
    mkSystem 2 K (fun _ => S) a - mkSystem 2 K (fun _ => S) b =
      MvPolynomial.X (Fin.last (2 + 1)) *
        (MvPolynomial.X (Fin.castSucc b) -
          MvPolynomial.X (Fin.castSucc a)) := by
  simp only [mkSystem]
  ring

/-- Sharp necessary condition: a constant family `F = const S` at
`mkSystem 2` with zero data (`S` vanishing at a point with `x₀ ≠ x₁`,
`z = 0`) is never successively regular — `G₂` is a zerodivisor mod
`(G₀, G₁)` via §0. Any sufficient condition for rung-2 `hsucc`
must exclude this case. -/
theorem not_hsucc_mkSystem_const_of_zero (K : Type*) [Field K]
    (S : MvPolynomial (Fin 3) K) (v : Fin 4 → K)
    (hS : MvPolynomial.eval (v ∘ Fin.castSucc) S = 0)
    (hz : v (Fin.last (2 + 1)) = 0)
    (hne : v (Fin.castSucc (0 : Fin 3)) ≠
      v (Fin.castSucc (1 : Fin 3))) :
    ¬ RegularityBridge.SuccessiveSMulRegular (mkSystem 2 K (fun _ => S)) := by
  have e10 := mkSystem_const_diff K S (1 : Fin 3) (0 : Fin 3)
  have e20 := mkSystem_const_diff K S (2 : Fin 3) (0 : Fin 3)
  have hrel := rung2_relation_of_diffs _ _ _ _ _ _ _ e10 e20
  have hG0 : MvPolynomial.eval v
      (mkSystem 2 K (fun _ => S) (0 : Fin 3)) = 0 := by
    simp only [mkSystem, map_sub, map_mul, MvPolynomial.eval_rename,
      MvPolynomial.eval_X]
    rw [hS, hz, zero_mul, sub_zero]
  have hG1 : MvPolynomial.eval v
      (mkSystem 2 K (fun _ => S) (1 : Fin 3)) = 0 := by
    simp only [mkSystem, map_sub, map_mul, MvPolynomial.eval_rename,
      MvPolynomial.eval_X]
    rw [hS, hz, zero_mul, sub_zero]
  have hH : MvPolynomial.eval v
      (MvPolynomial.X (Fin.castSucc (0 : Fin 3)) -
        MvPolynomial.X (Fin.castSucc (1 : Fin 3))) ≠ 0 := by
    have eH : MvPolynomial.eval v
        (MvPolynomial.X (Fin.castSucc (0 : Fin 3)) -
          MvPolynomial.X (Fin.castSucc (1 : Fin 3))) =
        v (Fin.castSucc (0 : Fin 3)) - v (Fin.castSucc (1 : Fin 3)) := by
      simp [map_sub, MvPolynomial.eval_X]
    rw [eH]
    exact sub_ne_zero.mpr hne
  have v0 : ((0 : Fin 3)).val = 0 := by decide
  have v1 : ((1 : Fin 3)).val = 1 := by decide
  have v2 : ((2 : Fin 3)).val = 2 := by decide
  have himage : Set.image (mkSystem 2 K (fun _ => S))
      {k : Fin 3 | k.val < 2} =
      {(mkSystem 2 K (fun _ => S)) (0 : Fin 3),
        (mkSystem 2 K (fun _ => S)) (1 : Fin 3)} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk2 with h0 | h1
      · left
        have e : k = (0 : Fin 3) := Fin.ext (h0.trans v0.symm)
        rw [e]
      · right
        have e : k = (1 : Fin 3) := Fin.ext (h1.trans v1.symm)
        rw [e]
    · rintro (rfl | rfl)
      · exact ⟨(0 : Fin 3), by decide, rfl⟩
      · exact ⟨(1 : Fin 3), by decide, rfl⟩
  intro h
  have h2 := h (2 : Fin 3)
  rw [v2, himage] at h2
  exact not_isSMulRegular_of_rung2_witness _ _ _ _ _ _ _ hrel hG0 hG1 hH h2

/-- The gap quadric is nonzero (evaluation at `(1, 0, 0)` gives `1`). -/
theorem sgap_ne_zero (K : Type*) [Field K] : Sgap K ≠ 0 := by
  have n10 : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
  have heval : MvPolynomial.eval (Pi.single (0 : Fin 3) (1 : K))
      (Sgap K) = 1 := by
    simp only [Sgap, map_sub, map_pow, MvPolynomial.eval_X,
      Pi.single_eq_same, Pi.single_eq_of_ne n10]
    ring
  intro hcon
  rw [hcon, map_zero] at heval
  exact one_ne_zero heval.symm

/-- The gap quadric is a diagonal quadric (`c = (1, -1, 0)`). -/
theorem isDiagonalQuad_sgap (K : Type*) [Field K] :
    ConeNoEmbeddedRungs.IsDiagonalQuad K (Sgap K) := by
  refine ⟨fun l => if l.val = 0 then (1 : K)
    else if l.val = 1 then -1 else 0, ?_⟩
  have n10 : (1 : ℕ) ≠ 0 := by decide
  have n20 : (2 : ℕ) ≠ 0 := by decide
  have n21 : (2 : ℕ) ≠ 1 := by decide
  have f0 : (if ((0 : Fin 3)).val = 0 then (1 : K)
      else if ((0 : Fin 3)).val = 1 then -1 else 0) = 1 := by
    simp
  have f1 : (if ((1 : Fin 3)).val = 0 then (1 : K)
      else if ((1 : Fin 3)).val = 1 then -1 else 0) = -1 := by
    simp [n10]
  have f2 : (if ((2 : Fin 3)).val = 0 then (1 : K)
      else if ((2 : Fin 3)).val = 1 then -1 else 0) = 0 := by
    simp [n20, n21]
  simp only [Sgap, Fin.sum_univ_three]
  rw [f0, f1, f2]
  simp only [map_one, one_mul, map_neg, map_zero, zero_mul]
  ring

/-- The constant-`Sgap` family is not successively regular (`(2:K) ≠ 0`
gives `1 ≠ -1` at the gap point). -/
theorem not_hsucc_gap_mkSystem (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    ¬ RegularityBridge.SuccessiveSMulRegular
      (mkSystem 2 K (fun _ => Sgap K)) := by
  have hS : MvPolynomial.eval (vgap K ∘ Fin.castSucc) (Sgap K) = 0 := by
    have hv0 := vgap_castSucc_zero K
    have hv1 := vgap_castSucc_one K
    simp only [Sgap, map_sub, map_pow, MvPolynomial.eval_X,
      Function.comp_apply, hv0, hv1]
    ring
  have hz : vgap K (Fin.last (2 + 1)) = 0 := vgap_last K
  have hne : vgap K (Fin.castSucc (0 : Fin 3)) ≠
      vgap K (Fin.castSucc (1 : Fin 3)) := by
    have hv0 := vgap_castSucc_zero K
    have hv1 := vgap_castSucc_one K
    rw [hv0, hv1]
    intro h
    exact h2 (by linear_combination h)
  exact not_hsucc_mkSystem_const_of_zero K (Sgap K) (vgap K) hS hz hne

/-- The `IsDiagonalQuad` `hsucc` `∀`-form at `n = 2` is false
(`(2:K) ≠ 0` only — no algebraic closedness needed). -/
theorem hsucc_quad_forall_false (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    ¬ ∀ F : Fin 3 → MvPolynomial (Fin 3) K,
      (∀ k, ConeNoEmbeddedRungs.IsDiagonalQuad K (F k)) →
      RegularityBridge.SuccessiveSMulRegular (mkSystem 2 K F) := by
  intro hall
  exact not_hsucc_gap_mkSystem K h2
    (hall (fun _ => Sgap K) (fun _ => isDiagonalQuad_sgap K))

#print axioms mkSystem_const_diff
#print axioms not_hsucc_mkSystem_const_of_zero
#print axioms sgap_ne_zero
#print axioms isDiagonalQuad_sgap
#print axioms not_hsucc_gap_mkSystem
#print axioms hsucc_quad_forall_false

/-! ## §2 The diagonal-`c` witness at `n = 3` -/

/-- The gap structure constants at `n = 3`: diagonal with `d = (1, -1, 0)`
at every equation index, so every bridge form is `X₀² - X₁²`. -/
def diagWitness (K : Type*) [Field K] : Fin 3 → Fin 3 → Fin 3 → K :=
  fun a b _ => if a.val = b.val then
    (if a.val = 0 then 1 else if a.val = 1 then -1 else 0) else 0

/-- The witness is diagonal (off-diagonal constants vanish). -/
theorem isDiagonal_diagWitness (K : Type*) [Field K] :
    RungDiagonal.IsDiagonal K (diagWitness K) := by
  intro a b d hab
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp [diagWitness, hval]

/-- The shift equivalence fixes `0 : Fin 3` (mirrors
`RungRegular.shiftEquiv_two_zero`). -/
theorem shiftEquiv_three_zero (hn : 0 < 3) :
    shiftEquiv 3 hn (0 : Fin 3) = (0 : Fin 3) := Fin.ext rfl

/-- The shift equivalence fixes `1 : Fin 3`. -/
theorem shiftEquiv_three_one (hn : 0 < 3) :
    shiftEquiv 3 hn (1 : Fin 3) = (1 : Fin 3) := Fin.ext rfl

/-- The shift equivalence fixes `2 : Fin 3`. -/
theorem shiftEquiv_three_two (hn : 0 < 3) :
    shiftEquiv 3 hn (2 : Fin 3) = (2 : Fin 3) := Fin.ext rfl

/-- The witness bridge-form computation, stated over `Fin 3`: only the
`(0, 0)` and `(1, 1)` summands survive. Proved standalone (fresh
elaboration) rather than via `change`: `change` elaborates against the old
goal's expected type, which pollutes `C`'s implicit `σ` with
`Fin (statementIndex 3 + 1)` while the `X`s stay `Fin 3` (a hybrid goal
that `ring` cannot close); `bridgeForms_diagWitness` below bridges by
defeq instead. -/
theorem bridgeForms_sum_fin3 (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    (∑ i : Fin 3, ∑ j : Fin 3, MvPolynomial.C
        (diagWitness K (shiftEquiv 3 hn i) (shiftEquiv 3 hn j)
          (shiftEquiv 3 hn k)) *
        (MvPolynomial.X i * MvPolynomial.X j)) =
      MvPolynomial.X (0 : Fin 3) ^ 2 - MvPolynomial.X (1 : Fin 3) ^ 2 := by
  have n01 : (0 : ℕ) ≠ 1 := by decide
  have n02 : (0 : ℕ) ≠ 2 := by decide
  have n10 : (1 : ℕ) ≠ 0 := by decide
  have n12 : (1 : ℕ) ≠ 2 := by decide
  have n20 : (2 : ℕ) ≠ 0 := by decide
  have n21 : (2 : ℕ) ≠ 1 := by decide
  have c00 : diagWitness K (shiftEquiv 3 hn (0 : Fin 3))
      (shiftEquiv 3 hn (0 : Fin 3)) (shiftEquiv 3 hn k) = 1 := by
    rw [shiftEquiv_three_zero]
    simp [diagWitness]
  have c01 : diagWitness K (shiftEquiv 3 hn (0 : Fin 3))
      (shiftEquiv 3 hn (1 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_zero, shiftEquiv_three_one]
    simp [diagWitness, n01]
  have c02 : diagWitness K (shiftEquiv 3 hn (0 : Fin 3))
      (shiftEquiv 3 hn (2 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_zero, shiftEquiv_three_two]
    simp [diagWitness, n02]
  have c10 : diagWitness K (shiftEquiv 3 hn (1 : Fin 3))
      (shiftEquiv 3 hn (0 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_one, shiftEquiv_three_zero]
    simp [diagWitness, n10]
  have c11 : diagWitness K (shiftEquiv 3 hn (1 : Fin 3))
      (shiftEquiv 3 hn (1 : Fin 3)) (shiftEquiv 3 hn k) = -1 := by
    rw [shiftEquiv_three_one]
    simp [diagWitness, n10]
  have c12 : diagWitness K (shiftEquiv 3 hn (1 : Fin 3))
      (shiftEquiv 3 hn (2 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_one, shiftEquiv_three_two]
    simp [diagWitness, n12]
  have c20 : diagWitness K (shiftEquiv 3 hn (2 : Fin 3))
      (shiftEquiv 3 hn (0 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_two, shiftEquiv_three_zero]
    simp [diagWitness, n20]
  have c21 : diagWitness K (shiftEquiv 3 hn (2 : Fin 3))
      (shiftEquiv 3 hn (1 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_two, shiftEquiv_three_one]
    simp [diagWitness, n21]
  have c22 : diagWitness K (shiftEquiv 3 hn (2 : Fin 3))
      (shiftEquiv 3 hn (2 : Fin 3)) (shiftEquiv 3 hn k) = 0 := by
    rw [shiftEquiv_three_two]
    simp [diagWitness, n20, n21]
  simp only [Fin.sum_univ_three]
  rw [c00, c01, c02, c10, c11, c12, c20, c21, c22]
  simp only [map_one, one_mul, map_neg, map_zero, zero_mul, add_zero,
    zero_add]
  ring

/-- At the witness, every bridge form is `X₀² - X₁²` (the `Fin 3`
computation above, bridged by defeq). -/
theorem bridgeForms_diagWitness (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    bridgeForms 3 K (diagWitness K) hn k =
      MvPolynomial.X (0 : Fin (statementIndex 3 + 1)) ^ 2 -
        MvPolynomial.X (1 : Fin (statementIndex 3 + 1)) ^ 2 :=
  bridgeForms_sum_fin3 K hn k

/-- The gap evaluation point `(1, -1, 0, 0)` on
`Fin (statementIndex 3 + 2)`. -/
def vgapB (K : Type*) [Field K] : Fin (statementIndex 3 + 2) → K :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then -1 else 0

/-- `vgapB` at `0` is `1`. -/
theorem vgapB_castSucc_zero (K : Type*) [Field K] :
    vgapB K (Fin.castSucc (0 : Fin (statementIndex 3 + 1))) = 1 := by
  simp [vgapB]

/-- `vgapB` at `1` is `-1`. -/
theorem vgapB_castSucc_one (K : Type*) [Field K] :
    vgapB K (Fin.castSucc (1 : Fin (statementIndex 3 + 1))) = -1 := by
  have n10 : (1 : ℕ) ≠ 0 := by decide
  simp [vgapB, n10]

/-- `vgapB` at the last index is `0`. -/
theorem vgapB_last (K : Type*) [Field K] :
    vgapB K (Fin.last (statementIndex 3 + 1)) = 0 := by
  have n3 : statementIndex 3 ≠ 0 := by decide
  simp [vgapB, n3]

/-- `z`-linear differences for the witness bridge family: the bridge forms
are all equal, so the renamed quadrics cancel. -/
theorem bridgeSystem_gap_diff (K : Type*) [Field K] (hn : 0 < 3)
    (a b : Fin (statementIndex 3 + 1)) :
    bridgeSystem 3 K (diagWitness K) hn a -
        bridgeSystem 3 K (diagWitness K) hn b =
      MvPolynomial.X (Fin.last (statementIndex 3 + 1)) *
        (MvPolynomial.X (Fin.castSucc b) -
          MvPolynomial.X (Fin.castSucc a)) := by
  simp only [bridgeSystem, mkSystem]
  rw [bridgeForms_diagWitness, bridgeForms_diagWitness]
  ring

/-- Every witness equation vanishes at the gap point (all `k`: the
`S`-evaluation is `1 - 1 = 0` and the `z`-factor is `0`). -/
theorem eval_bridge_gap (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    MvPolynomial.eval (vgapB K)
        (bridgeSystem 3 K (diagWitness K) hn k) = 0 := by
  have hv0 := vgapB_castSucc_zero K
  have hv1 := vgapB_castSucc_one K
  have hvz := vgapB_last K
  simp only [bridgeSystem, mkSystem, map_sub, map_mul,
    MvPolynomial.eval_rename, MvPolynomial.eval_X]
  rw [bridgeForms_diagWitness]
  simp only [map_sub, map_pow, MvPolynomial.eval_X, Function.comp_apply,
    hv0, hv1, hvz, zero_mul]
  ring

/-- The zerodivisor witness evaluates to `2 ≠ 0` at the gap point. -/
theorem eval_gapB_H (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    MvPolynomial.eval (vgapB K)
        (MvPolynomial.X
            (Fin.castSucc (0 : Fin (statementIndex 3 + 1))) -
          MvPolynomial.X
            (Fin.castSucc (1 : Fin (statementIndex 3 + 1)))) ≠ 0 := by
  have hv0 := vgapB_castSucc_zero K
  have hv1 := vgapB_castSucc_one K
  have eH : MvPolynomial.eval (vgapB K)
        (MvPolynomial.X
            (Fin.castSucc (0 : Fin (statementIndex 3 + 1))) -
          MvPolynomial.X
            (Fin.castSucc (1 : Fin (statementIndex 3 + 1)))) = 2 := by
    simp only [map_sub, MvPolynomial.eval_X, hv0, hv1]
    ring
  rw [eH]
  exact h2

/-- The rung-2 prefix span at the witness is the pair span `(G₀, G₁)`. -/
theorem himage_bridge_gap (K : Type*) [Field K] (hn : 0 < 3) :
    Set.image (bridgeSystem 3 K (diagWitness K) hn)
        {k : Fin (statementIndex 3 + 1) | k.val < 2} =
      {(bridgeSystem 3 K (diagWitness K) hn)
          (0 : Fin (statementIndex 3 + 1)),
        (bridgeSystem 3 K (diagWitness K) hn)
          (1 : Fin (statementIndex 3 + 1))} := by
  have v0 : ((0 : Fin (statementIndex 3 + 1))).val = 0 := by decide
  have v1 : ((1 : Fin (statementIndex 3 + 1))).val = 1 := by decide
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k.val = 0 ∨ k.val = 1 := by omega
    rcases hk2 with h0 | h1
    · left
      have e : k = (0 : Fin (statementIndex 3 + 1)) :=
        Fin.ext (h0.trans v0.symm)
      rw [e]
    · right
      have e : k = (1 : Fin (statementIndex 3 + 1)) :=
        Fin.ext (h1.trans v1.symm)
      rw [e]
  · rintro (rfl | rfl)
    · exact ⟨(0 : Fin (statementIndex 3 + 1)), by decide, rfl⟩
    · exact ⟨(1 : Fin (statementIndex 3 + 1)), by decide, rfl⟩

/-- The rung-2 zerodivisor relation at the witness bridge family. -/
theorem rung2_rel_bridge (K : Type*) [Field K] (hn : 0 < 3) :
    (MvPolynomial.X (Fin.castSucc (0 : Fin (statementIndex 3 + 1))) -
        MvPolynomial.X (Fin.castSucc (1 : Fin (statementIndex 3 + 1)))) *
        (bridgeSystem 3 K (diagWitness K) hn
          (2 : Fin (statementIndex 3 + 1))) =
      (MvPolynomial.X (Fin.castSucc (2 : Fin (statementIndex 3 + 1))) -
          MvPolynomial.X (Fin.castSucc (1 : Fin (statementIndex 3 + 1)))) *
          (bridgeSystem 3 K (diagWitness K) hn
            (0 : Fin (statementIndex 3 + 1))) +
        (MvPolynomial.X (Fin.castSucc (0 : Fin (statementIndex 3 + 1))) -
            MvPolynomial.X
              (Fin.castSucc (2 : Fin (statementIndex 3 + 1)))) *
          (bridgeSystem 3 K (diagWitness K) hn
            (1 : Fin (statementIndex 3 + 1))) := by
  have e10 := bridgeSystem_gap_diff K hn (1 : Fin (statementIndex 3 + 1))
    (0 : Fin (statementIndex 3 + 1))
  have e20 := bridgeSystem_gap_diff K hn (2 : Fin (statementIndex 3 + 1))
    (0 : Fin (statementIndex 3 + 1))
  exact rung2_relation_of_diffs _ _ _ _ _ _ _ e10 e20

/-- The witness bridge family is not successively regular: `G₂` is a
zerodivisor mod `(G₀, G₁)`. -/
theorem not_hsucc_bridge_gap (K : Type*) [Field K] (hn : 0 < 3)
    (h2 : (2 : K) ≠ 0) :
    ¬ RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem 3 K (diagWitness K) hn) := by
  have hrel := rung2_rel_bridge K hn
  have hG0 := eval_bridge_gap K hn (0 : Fin (statementIndex 3 + 1))
  have hG1 := eval_bridge_gap K hn (1 : Fin (statementIndex 3 + 1))
  have hH := eval_gapB_H K h2
  have v2 : ((2 : Fin (statementIndex 3 + 1))).val = 2 := by decide
  have himage := himage_bridge_gap K hn
  intro h
  have h2r := h (2 : Fin (statementIndex 3 + 1))
  rw [v2, himage] at h2r
  exact not_isSMulRegular_of_rung2_witness _ _ _ _ _ _ _ hrel hG0 hG1 hH h2r

/-- Rung-2 `IsSMulRegular` (the `ofList`-prefix shape) fails at the
witness. -/
theorem not_hreg_bridge_gap (K : Type*) [Field K] (hn : 0 < 3)
    (h2 : (2 : K) ≠ 0) :
    ¬ IsSMulRegular
      (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸ (Ideal.ofList
        (List.take ((2 : Fin (statementIndex 3 + 1))).val
          (List.ofFn (bridgeSystem 3 K (diagWitness K) hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
          (MvPolynomial (Fin (statementIndex 3 + 2)) K))))
      ((bridgeSystem 3 K (diagWitness K) hn)
        (2 : Fin (statementIndex 3 + 1))) := by
  have hrel := rung2_rel_bridge K hn
  have hG0 := eval_bridge_gap K hn (0 : Fin (statementIndex 3 + 1))
  have hG1 := eval_bridge_gap K hn (1 : Fin (statementIndex 3 + 1))
  have hH := eval_gapB_H K h2
  have v2 : ((2 : Fin (statementIndex 3 + 1))).val = 2 := by decide
  have himage := himage_bridge_gap K hn
  intro h
  rw [AvoidanceApply.ofList_take_eq_span_image, v2, himage] at h
  exact not_isSMulRegular_of_rung2_witness _ _ _ _ _ _ _ hrel hG0 hG1 hH h

/-- Every witness bridge form is nonzero (evaluation at `(1, 0, 0)`
gives `1`), so the witness satisfies pointwise nondegeneracy. -/
theorem bridgeForms_gap_ne_zero (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    bridgeForms 3 K (diagWitness K) hn k ≠ 0 := by
  rw [bridgeForms_diagWitness]
  intro hcon
  have n10 : (1 : Fin (statementIndex 3 + 1)) ≠
      (0 : Fin (statementIndex 3 + 1)) := by decide
  have heval : MvPolynomial.eval
      (Pi.single (0 : Fin (statementIndex 3 + 1)) (1 : K))
      (MvPolynomial.X (0 : Fin (statementIndex 3 + 1)) ^ 2 -
        MvPolynomial.X (1 : Fin (statementIndex 3 + 1)) ^ 2) = 1 := by
    simp only [map_sub, map_pow, MvPolynomial.eval_X, Pi.single_eq_same,
      Pi.single_eq_of_ne n10]
    ring
  rw [hcon, map_zero] at heval
  exact one_ne_zero heval.symm

/-- The narrowed rung-`≥ 2` diagonal `hreg` input (the `hge2` hypothesis of
`RungDiagonal.hreg_ge1_diagonal_of_ge2narrow`) is false. -/
theorem hge2narrow_diagonal_forall_false (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) :
    ¬ ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c → ∀ j : Fin (statementIndex n + 1),
      2 ≤ j.val → IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  intro hall
  have h3 : (3 : ℕ) ≤ 3 := by decide
  have hn3 : 0 < 3 := by decide
  have hj2 : 2 ≤ ((2 : Fin (statementIndex 3 + 1))).val := by decide
  exact not_hreg_bridge_gap K hn3 h2
    (hall 3 hn3 h3 (diagWitness K) (isDiagonal_diagWitness K)
      (2 : Fin (statementIndex 3 + 1)) hj2)

/-- The un-narrowed rung-`≥ 2` diagonal `hreg` input (the `hge2`
hypothesis of `RungDiagonal.hreg_ge1_diagonal_of_ge2`) is false. -/
theorem hge2_diagonal_forall_false (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c → ∀ j : Fin (statementIndex n + 1),
      2 ≤ j.val → IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  intro hall
  exact hge2narrow_diagonal_forall_false K h2
    (fun n hn h3 c hc j hj => hall n hn c hc j hj)

/-- The diagonal-`c` `hsucc` `∀`-form is false. -/
theorem hsucc_diagonal_forall_false (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  intro hall
  have hn3 : 0 < 3 := by decide
  exact not_hsucc_bridge_gap K hn3 h2
    (hall 3 hn3 (diagWitness K) (isDiagonal_diagWitness K))

/-- Even diagonal-`c` + the rung-1 nondegeneracy `∀`-form does not imply
`hsucc`: the witness has all bridge forms nonzero. -/
theorem hsucc_diagonal_nondeg_forall_false (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      (∀ j : Fin (statementIndex n + 1), j.val = 1 →
        bridgeForms n K c hn (RungDiagonal.rungI0 n) ≠ 0 ∨
          bridgeForms n K c hn j ≠ 0) →
      RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  intro hall
  have hn3 : 0 < 3 := by decide
  exact not_hsucc_bridge_gap K hn3 h2
    (hall 3 hn3 (diagWitness K) (isDiagonal_diagWitness K)
      (fun j _ => Or.inl (bridgeForms_gap_ne_zero K hn3 _)))

#print axioms isDiagonal_diagWitness
#print axioms shiftEquiv_three_zero
#print axioms shiftEquiv_three_one
#print axioms shiftEquiv_three_two
#print axioms bridgeForms_sum_fin3
#print axioms bridgeForms_diagWitness
#print axioms vgapB_castSucc_zero
#print axioms vgapB_castSucc_one
#print axioms vgapB_last
#print axioms bridgeSystem_gap_diff
#print axioms eval_bridge_gap
#print axioms eval_gapB_H
#print axioms himage_bridge_gap
#print axioms rung2_rel_bridge
#print axioms not_hsucc_bridge_gap
#print axioms not_hreg_bridge_gap
#print axioms bridgeForms_gap_ne_zero
#print axioms hge2narrow_diagonal_forall_false
#print axioms hge2_diagonal_forall_false
#print axioms hsucc_diagonal_forall_false
#print axioms hsucc_diagonal_nondeg_forall_false

end RungDiagonalGap
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
