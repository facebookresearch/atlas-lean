/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.DiagonalQuadBridge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Diagonal sufficiency under coefficient genericity
Alternate rb-1 route around the S1 refutation: `RungDiagonalGap`
proves diagonality — even with pointwise nondegeneracy (`Fₖ ≠ 0`) — does
not imply rung-2 `hsucc`, via the constant-family witness
(`diagWitness`, every equation seeing the same `S = X₀² - X₁²`: rank-1
diagonal coefficients). Its remainder item 1 prescribes the fix: a future
sufficient condition must add **coefficient genericity**. This module proves
that genericity definition and the sufficiency lemmas it supports.

## Genericity (what must be excluded)

* `CoeffGeneric e` (§0): the diagonal coefficient vectors `e: Fin N →
  Fin N → K` are pairwise distinct (`Function.Injective`).
* `CoeffIndependent N K e` (§0): the strong form (`LinearIndependent K e`;
  implies `CoeffGeneric` by `generic_of_independent`, one Mathlib line).
* `diagCoeffVec` / `CoeffGenericBridge` (§0): the bridge-level vectors
  `k ↦ (l ↦ shiftConsts … l l k)` and their injectivity.

## What is proved here

* §1 Coefficient injectivity: the diagonal-sum presentation is injective
  (`diagSum_coeff_injective`, `coeffVec_eq_zero_of_diagSum_eq_zero`), so
  distinct vectors give distinct forms (`forms_ne_of_coeff_ne`) and
  genericity derives the rung-1 nondegeneracy disjunct
  (`nondeg_disjunct_of_generic`).
* §2 Witness exclusion: constant coefficient families are never generic
  (`not_generic_const`); the Gap witness fails genericity
  (`not_generic_diagWitness`, `not_independent_diagWitness`) while
  satisfying diagonality + pointwise nondegeneracy — hence genericity is
  a strictly stronger hypothesis than both combined (`genericity_sharp`).
* §3 Mechanism-breaking: under distinct coefficient vectors the
  `mkSystem` difference is not the pure `z`-linear form
  (`mkSystem_diff_ne_zlinear_of_coeff_ne`, via the general difference
  formula `mkSystem_diff_general` and the nonzero renamed part
  `rename_sub_ne_zero_of_coeff_ne`). This is the exact RHS identity of
  `RungDiagonalGap.mkSystem_const_diff` that §1 there feeds into
  `rung2_relation_of_diffs` — genericity cuts the refutation's feed, at
  both `mkSystem` and `bridgeSystem` level
  (`bridgeSystem_diff_ne_zlinear_of_generic`).
* §4 Assembly (the sufficiency headline): rung-1 regularity from
  diagonal + genericity with nondegeneracy derived, not assumed
  (`hreg_rung1_of_generic`); the rung-`≥ 1` input from rung-`≥ 2` generic
  data (`hreg_ge1_generic_of_ge2narrow`, tightening
  `RungDiagonal.hreg_ge1_diagonal_of_ge2narrow` by replacing its
  rung-1-nondegeneracy `∀`-form with genericity); full `hsucc` from
  diagonal + generic + rung-`≥ 2` step data (`hsucc_generic_of_ge2`).

Status: `generic_of_independent`, `not_generic_const`,
`not_generic_diagWitness`, `not_independent_diagWitness`,
`genericity_sharp`, `mkSystem_diff_general`,
`rename_sub_ne_zero_of_coeff_ne`, `mkSystem_diff_ne_zlinear_of_coeff_ne`,
`bridgeSystem_diff_ne_zlinear_of_generic`, `hreg_rung1_of_generic`
unconditional given the stated inputs; `hreg_ge1_generic_of_ge2narrow`
conditional-exact on rung-`≥ 2` generic data over `n ≥ 3`;
`hsucc_generic_of_ge2` conditional-exact on rung-`≥ 2` step data.

## Precise remainder (out of scope)

Rung-`≥ 2` regularity itself (`hge2`) still needs the `k = 2`
unmixedness machinery (the `HdimEq` route) — exactly
`RungDiagonalGap` remainder item 2; genericity removes the
coefficient-degeneracy obstruction, not the (t3) obstruction
(`TriangularRegularity`). Characteristic 2 needs no caveat here: every result
is characteristic-free (the Gap witness's `(2 : K) ≠ 0` was needed only
for the refutation direction).

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint.Rung.RungDiagonalGap`, `diagWitness`, `isDiagonal_diagWitness`,
  `bridgeForms_gap_ne_zero`, `mkSystem_const_diff`,
  `rung2_relation_of_diffs` (refutation consumed; remainder item 1
  discharged by the genericity definition, item 2 restated above).
* `BridgeToFixedPoint.Rung.RungDiagonal`, `IsDiagonal`, `shiftConsts_diag`,
  `bridgeForms_eq_diagQuad`, `hreg_rung1_diagonal`,
  `hreg_ge1_diagonal_of_ge2narrow` (toolkit consumed; narrowed input
  tightened).
* `BridgeToFixedPoint.Rung.DiagonalQuadBridge`, `eval_diagonal_sum_single`,
  `diagQuad_eq_diagonal_sum` (evaluation + collapse toolkit).
* `BridgeToFixedPoint.Rung.RungRegular`, `hreg_rung0` (unconditional rung 0 in
  the assembly).
* `BridgeToFixedPoint.FixedPointFromBezout`, `bridgeSystem`, `bridgeForms`,
  `shiftConsts`, `shift_add_one`, `statementIndex`.
* `Regularity.Avoid.AvoidanceApply`, `hsucc_of_step_outputs`;
  `Regularity.Avoid.RegularityBridge`, `SuccessiveSMulRegular`;
  `Statement.Definitions`, `mkSystem`.

Mathlib (v4.34.0, `grep`-verified):

* `LinearIndependent.injective`, `LinearIndependent.ne_zero`
  (`Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`).
* `MvPolynomial.eval_rename`
  (`Mathlib/Algebra/MvPolynomial/Rename.lean`).
* `Function.ne_iff` (`Mathlib/Logic/Function/Basic.lean`).
* `Fin.lastCases` (`Init`/`Batteries`; applied-to-`castSucc` equation
  closed by `simp`, mirroring `FixedPointFromBezout`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungDiagonalGeneric

open scoped BigOperators

/-! ## §0 Genericity: definitions -/

/-- Diagonal-coefficient presentation of a family: every `F k` is the
diagonal sum with coefficient vector `e k`. -/
def DiagCoeff (N : ℕ) (K : Type*) [Field K]
    (F : Fin N → MvPolynomial (Fin N) K)
    (e : Fin N → Fin N → K) : Prop :=
  ∀ k, F k = ∑ l, MvPolynomial.C (e k l) *
    (MvPolynomial.X l * MvPolynomial.X l)

/-- Coefficient genericity: the diagonal coefficient vectors are pairwise
distinct. This is exactly what the Gap witness violates (all its vectors
are `(1, -1, 0)`). -/
def CoeffGeneric {N : ℕ} {K : Type*} (e : Fin N → Fin N → K) : Prop :=
  Function.Injective e

/-- Strong coefficient genericity: the diagonal coefficient vectors are
linearly independent (implies `CoeffGeneric`). -/
def CoeffIndependent (N : ℕ) (K : Type*) [Field K]
    (e : Fin N → Fin N → K) : Prop :=
  LinearIndependent K e

/-- The bridge-level diagonal coefficient vector at equation index `k`:
`l ↦ shiftConsts … l l k` (the vector implicitly used by
`bridgeForms_diagonalQuad_of_diagonal`). -/
noncomputable def diagCoeffVec (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) :
    Fin (statementIndex n + 1) → K :=
  fun l => shiftConsts n K c hn l l k

/-- Bridge-level genericity: distinct diagonal coefficient vectors across
equation indices. -/
def CoeffGenericBridge (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) : Prop :=
  CoeffGeneric (diagCoeffVec n K c hn)

/-- Independence implies genericity (one Mathlib line). -/
theorem generic_of_independent (N : ℕ) (K : Type*) [Field K]
    (e : Fin N → Fin N → K) (h : CoeffIndependent N K e) :
    CoeffGeneric e :=
  LinearIndependent.injective h

/-! ## §1 Coefficient injectivity and derived nondegeneracy -/

/-- The diagonal-sum presentation is injective: equal sums give equal
coefficient vectors (evaluate at each coordinate point). -/
theorem diagSum_coeff_injective (K : Type*) [Field K] (N : ℕ)
    (e e' : Fin N → K)
    (h : (∑ l, MvPolynomial.C (e l) *
        (MvPolynomial.X l * MvPolynomial.X l)) =
      (∑ l, MvPolynomial.C (e' l) *
        (MvPolynomial.X l * MvPolynomial.X l))) :
    e = e' := by
  funext m
  have hcon :=
    congrArg (MvPolynomial.eval (Pi.single m (1 : K))) h
  rw [DiagonalQuadBridge.eval_diagonal_sum_single,
    DiagonalQuadBridge.eval_diagonal_sum_single] at hcon
  exact hcon

/-- A diagonal sum is zero only for the zero vector. -/
theorem coeffVec_eq_zero_of_diagSum_eq_zero (K : Type*) [Field K]
    (N : ℕ) (e : Fin N → K)
    (h0 : (∑ l, MvPolynomial.C (e l) *
        (MvPolynomial.X l * MvPolynomial.X l)) = 0) :
    e = 0 := by
  funext m
  have h := congrArg (MvPolynomial.eval (Pi.single m (1 : K))) h0
  rw [DiagonalQuadBridge.eval_diagonal_sum_single, map_zero] at h
  exact h

/-- Distinct coefficient vectors give distinct forms. -/
theorem forms_ne_of_coeff_ne (K : Type*) [Field K] (N : ℕ)
    (F : Fin N → MvPolynomial (Fin N) K)
    (e : Fin N → Fin N → K) (hF : DiagCoeff N K F e)
    (a b : Fin N) (hne : e a ≠ e b) :
    F a ≠ F b := by
  intro hcon
  exact hne (diagSum_coeff_injective K N (e a) (e b)
    (by rw [← hF a, ← hF b, hcon]))

/-- Genericity derives the rung-1 nondegeneracy disjunct: two distinct
indices cannot both carry the zero form (both zero would force equal —
zero — coefficient vectors, against injectivity). -/
theorem nondeg_disjunct_of_generic (K : Type*) [Field K] (N : ℕ)
    (F : Fin N → MvPolynomial (Fin N) K)
    (e : Fin N → Fin N → K) (hF : DiagCoeff N K F e)
    (hgen : CoeffGeneric e) (i j : Fin N) (hij : i ≠ j) :
    F i ≠ 0 ∨ F j ≠ 0 := by
  by_contra hcon
  have hFi : F i = 0 := by
    by_contra hc
    exact hcon (Or.inl hc)
  have hFj : F j = 0 := by
    by_contra hc
    exact hcon (Or.inr hc)
  have hei : e i = 0 :=
    coeffVec_eq_zero_of_diagSum_eq_zero K N (e i)
      (by rw [← hF i, hFi])
  have hej : e j = 0 :=
    coeffVec_eq_zero_of_diagSum_eq_zero K N (e j)
      (by rw [← hF j, hFj])
  exact hij (hgen (hei.trans hej.symm))

#print axioms generic_of_independent
#print axioms diagSum_coeff_injective
#print axioms coeffVec_eq_zero_of_diagSum_eq_zero
#print axioms forms_ne_of_coeff_ne
#print axioms nondeg_disjunct_of_generic

/-! ## §2 The Gap witness is excluded -/

/-- Constant coefficient families are never generic (any two distinct
indices collide). -/
theorem not_generic_const (N : ℕ) (K : Type*) [Field K]
    (v : Fin N → K) (i j : Fin N) (hij : i ≠ j) :
    ¬ CoeffGeneric (fun _ : Fin N => v) := by
  intro h
  exact hij (h rfl)

/-- The Gap witness fails genericity: every equation index carries the
same diagonal vector, so indices `0 ≠ 1` collide. -/
theorem not_generic_diagWitness (K : Type*) [Field K] (hn : 0 < 3) :
    ¬ CoeffGenericBridge 3 K (RungDiagonalGap.diagWitness K) hn := by
  intro h
  have heq : diagCoeffVec 3 K (RungDiagonalGap.diagWitness K) hn 0 =
      diagCoeffVec 3 K (RungDiagonalGap.diagWitness K) hn 1 := by
    funext l
    simp [diagCoeffVec, shiftConsts, RungDiagonalGap.diagWitness]
  have h01 : (0 : Fin (statementIndex 3 + 1)) ≠ 1 := by decide
  exact h01 (h heq)

/-- The Gap witness fails strong genericity (via §0). -/
theorem not_independent_diagWitness (K : Type*) [Field K]
    (hn : 0 < 3) :
    ¬ CoeffIndependent (statementIndex 3 + 1) K
      (diagCoeffVec 3 K (RungDiagonalGap.diagWitness K) hn) := by
  intro h
  exact not_generic_diagWitness K hn
    (generic_of_independent (statementIndex 3 + 1) K _ h)

/-- Sharpness: genericity is strictly stronger than diagonality plus
pointwise nondegeneracy — the Gap witness satisfies both and fails
genericity. -/
theorem genericity_sharp (K : Type*) [Field K] :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      (∀ k, bridgeForms n K c hn k ≠ 0) →
      CoeffGenericBridge n K c hn := by
  intro hall
  have hn3 : 0 < 3 := by decide
  exact not_generic_diagWitness K hn3
    (hall 3 hn3 (RungDiagonalGap.diagWitness K)
      (RungDiagonalGap.isDiagonal_diagWitness K)
      (fun k => RungDiagonalGap.bridgeForms_gap_ne_zero K hn3 k))

#print axioms not_generic_const
#print axioms not_generic_diagWitness
#print axioms not_independent_diagWitness
#print axioms genericity_sharp

/-! ## §3 Genericity cuts the refutation's feed -/

/-- The general `mkSystem` difference formula: the difference of two
rungs is the renamed form-difference minus the `z`-linear part (the
constant-family case `mkSystem_const_diff` is the `F a = F b`
specialization). -/
theorem mkSystem_diff_general (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (a b : Fin (n + 1)) :
    mkSystem n K F a - mkSystem n K F b =
      MvPolynomial.rename Fin.castSucc (F a - F b) -
        MvPolynomial.X (Fin.last (n + 1)) *
          (MvPolynomial.X (Fin.castSucc a) -
            MvPolynomial.X (Fin.castSucc b)) := by
  simp only [mkSystem, map_sub]
  ring

/-- Under distinct coefficient vectors the renamed form-difference is
nonzero: some coordinate `m` separates the vectors, and evaluation at
that coordinate point (lifted through `Fin.lastCases`) witnesses it. -/
theorem rename_sub_ne_zero_of_coeff_ne (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (e : Fin (n + 1) → Fin (n + 1) → K)
    (hF : DiagCoeff (n + 1) K F e)
    (a b : Fin (n + 1)) (hne : e a ≠ e b) :
    MvPolynomial.rename Fin.castSucc (F a - F b) ≠ 0 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hne
  have heval : MvPolynomial.eval (Pi.single m (1 : K)) (F a - F b) ≠ 0 := by
    rw [map_sub, hF a, hF b,
      DiagonalQuadBridge.eval_diagonal_sum_single,
      DiagonalQuadBridge.eval_diagonal_sum_single]
    exact sub_ne_zero.mpr hm
  intro hcon
  have hcomp : (Fin.lastCases (motive := fun _ => K) (0 : K)
      (Pi.single m (1 : K))) ∘ Fin.castSucc =
      Pi.single m (1 : K) := by
    funext j
    simp
  have hzero := congrArg (MvPolynomial.eval
    (Fin.lastCases (motive := fun _ => K) (0 : K)
      (Pi.single m (1 : K)))) hcon
  rw [map_zero, MvPolynomial.eval_rename, hcomp] at hzero
  exact heval hzero

/-- Under distinct coefficient vectors, the `mkSystem` difference is not
the pure `z`-linear form: the exact RHS identity of
`RungDiagonalGap.mkSystem_const_diff` — which §1 there feeds into
`rung2_relation_of_diffs` — fails. -/
theorem mkSystem_diff_ne_zlinear_of_coeff_ne (n : ℕ) (K : Type*)
    [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (e : Fin (n + 1) → Fin (n + 1) → K)
    (hF : DiagCoeff (n + 1) K F e)
    (a b : Fin (n + 1)) (hne : e a ≠ e b) :
    mkSystem n K F a - mkSystem n K F b ≠
      MvPolynomial.X (Fin.last (n + 1)) *
        (MvPolynomial.X (Fin.castSucc b) -
          MvPolynomial.X (Fin.castSucc a)) := by
  have hdiff := mkSystem_diff_general n K F a b
  have hR := rename_sub_ne_zero_of_coeff_ne n K F e hF a b hne
  intro hcon
  have h0 : MvPolynomial.rename Fin.castSucc (F a - F b) = 0 := by
    linear_combination hcon - hdiff
  exact hR h0

/-- Bridge forms carry the `diagCoeffVec` presentation (the equation
inside `bridgeForms_diagonalQuad_of_diagonal`, exposed). -/
theorem bridgeForms_eq_diagSum (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (k : Fin (statementIndex n + 1)) :
    bridgeForms n K c hn k =
      ∑ l, MvPolynomial.C (diagCoeffVec n K c hn k l) *
        (MvPolynomial.X l * MvPolynomial.X l) := by
  rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c k]
  exact DiagonalQuadBridge.diagQuad_eq_diagonal_sum K
    (statementIndex n + 1) (fun i j => shiftConsts n K c hn i j k)
    (RungDiagonal.shiftConsts_diag K n hn c hdiag k)

/-- Bridge-level mechanism-breaking: under diagonality + genericity, no
rung difference is pure `z`-linear. -/
theorem bridgeSystem_diff_ne_zlinear_of_generic (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : CoeffGenericBridge n K c hn)
    (a b : Fin (statementIndex n + 1)) (hab : a ≠ b) :
    bridgeSystem n K c hn a - bridgeSystem n K c hn b ≠
      MvPolynomial.X (Fin.last (statementIndex n + 1)) *
        (MvPolynomial.X (Fin.castSucc b) -
          MvPolynomial.X (Fin.castSucc a)) := by
  have hF : DiagCoeff (statementIndex n + 1) K
      (bridgeForms n K c hn) (diagCoeffVec n K c hn) :=
    fun k => bridgeForms_eq_diagSum K n hn c hdiag k
  have hne : diagCoeffVec n K c hn a ≠ diagCoeffVec n K c hn b :=
    fun h => hab (hgen h)
  exact mkSystem_diff_ne_zlinear_of_coeff_ne (statementIndex n) K _ _ hF
    a b hne

#print axioms mkSystem_diff_general
#print axioms rename_sub_ne_zero_of_coeff_ne
#print axioms mkSystem_diff_ne_zlinear_of_coeff_ne
#print axioms bridgeForms_eq_diagSum
#print axioms bridgeSystem_diff_ne_zlinear_of_generic

/-! ## §4 Sufficiency assembly -/

/-- Genericity derives bridge-level rung-1 nondegeneracy (§1, at the
bridge presentation). -/
theorem nondeg_of_generic_bridge (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : CoeffGenericBridge n K c hn)
    (i j : Fin (statementIndex n + 1)) (hij : i ≠ j) :
    bridgeForms n K c hn i ≠ 0 ∨ bridgeForms n K c hn j ≠ 0 := by
  have hF : DiagCoeff (statementIndex n + 1) K
      (bridgeForms n K c hn) (diagCoeffVec n K c hn) :=
    fun k => bridgeForms_eq_diagSum K n hn c hdiag k
  exact nondeg_disjunct_of_generic K (statementIndex n + 1) _ _ hF hgen
    i j hij

/-- Rung-1 regularity from diagonal `c` + genericity: the nondegeneracy
input of `hreg_rung1_diagonal` is derived (§1), not assumed. -/
theorem hreg_rung1_of_generic (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : CoeffGenericBridge n K c hn) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have hrj : RungDiagonal.rungI0 n ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    rw [hj] at hv
    have hv0 : (RungDiagonal.rungI0 n).val = 0 := rfl
    rw [hv0] at hv
    exact one_ne_zero hv.symm
  exact RungDiagonal.hreg_rung1_diagonal K n hn c j hj hdiag
    (nondeg_of_generic_bridge K n hn c hdiag hgen _ _ hrj)

/-- The diagonal rung-`≥ 1` `hreg` input from rung-`≥ 2` generic data
over `n ≥ 3`: `j.val = 1` is `hreg_rung1_of_generic`, the `n ≤ 2`,
`j.val ≠ 1` case is vacuous, and `j.val ≥ 2` at `n ≥ 3` is the
explicit hypothesis. Strictly tightens
`RungDiagonal.hreg_ge1_diagonal_of_ge2narrow` by replacing its
rung-1-nondegeneracy `∀`-form with genericity. -/
theorem hreg_ge1_generic_of_ge2narrow (K : Type*) [Field K]
    (hge2 : ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      CoeffGenericBridge n K c hn →
      ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j)) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      RungDiagonal.IsDiagonal K c →
      CoeffGenericBridge n K c hn →
      ∀ j : Fin (statementIndex n + 1), 1 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j) := by
  intro n hn c hdiag hgen j hj1
  by_cases hj : j.val = 1
  · exact hreg_rung1_of_generic K n hn c j hj hdiag hgen
  · by_cases hn2 : n ≤ 2
    · exfalso
      have hlt := j.isLt
      have hshift := shift_add_one n hn
      omega
    · exact hge2 n hn (by omega) c hdiag hgen j (by omega)

/-- Full `hsucc` from diagonal `c` + genericity + rung-`≥ 2` step data:
rung 0 is unconditional (`hreg_rung0`), rung 1 derives its nondegeneracy
from genericity, rungs `≥ 2` are the explicit hypothesis (the (t3)
remainder: needs the `HdimEq` unmixedness route). -/
theorem hsucc_generic_of_ge2 (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c)
    (hgen : CoeffGenericBridge n K c hn)
    (hge2 : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) := by
  apply AvoidanceApply.hsucc_of_step_outputs
  intro j
  by_cases hj0 : j.val = 0
  · exact RungRegular.hreg_rung0 K n hn c j hj0
  · by_cases hj1 : j.val = 1
    · exact hreg_rung1_of_generic K n hn c j hj1 hdiag hgen
    · exact hge2 j (by omega)

#print axioms nondeg_of_generic_bridge
#print axioms hreg_rung1_of_generic
#print axioms hreg_ge1_generic_of_ge2narrow
#print axioms hsucc_generic_of_ge2

end RungDiagonalGeneric
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
