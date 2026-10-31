/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.HilbertFunctionCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# `mkSystem`-specific regular sequences and the `hSES`/`hSEC` feed

This file proves regularity for the `mkSystem` quadrics
`Gᵢ = Fᵢ(x) − z·xᵢ` (`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`) by exploiting
their
explicit triangular/`z`-linear structure — not via the general unmixedness
route (`ResultantLemmas.exists_regular_quadrics`, which needs the
`hZd`/`hlow`/`hunmixed_ge2` inputs).

All results in this file are fully proved.

## Main results

* (t1, unconditional) `mkSystem_ne_zero` / `mkSystem_isSMulRegular` /
  `mkSystem_singleton_isRegular`: each `Gᵢ ≠ 0` (the `−z·xᵢ` monomial
  argument), hence
  regular on the domain, hence a length-1 `RingTheory.Sequence.IsRegular`
  family (properness from evaluation at the origin, via homogeneity).
* (assembly, conditional) `isRegular_ofFn_of_successive_of_evalZero` /
  `mkSystem_isRegular_of_successive`: successive SMul-regularity data
  (`RegularityBridge.SuccessiveSMulRegular`) plus origin-vanishing assemble to
  `IsRegular (List.ofFn q)` for `q` either the raw generators or `K`-linear
  `F`-combinations `∑ j, M k j • G j`; `combo_span_eq` repairs the span from
  `IsUnit M` by the inverse matrix.
* (SES feed, exact shapes) `hSEC_step_of_pieceSES` (the shift-1 mirror of
  `hSES_step_of_pieceSES`) and `hSEC_of_steps` (the `hSEC` mirror of
  `hSES_of_steps`), both via `graded_piece_ses` (itself `ses_finrank_add`);
  `mkSystem_hSES_of_steps` / `mkSystem_hSEC_of_steps` give the exact
  `length_section_eq_two_pow` / `bezout_quadratic` numerical input shapes
  (`hSES`, `hSEC`) with the per-step data enumerated as explicit hypotheses.

## Status: hypotheses

The results above assume exactly the following (nothing else):

1. `hsucc : RegularityBridge.SuccessiveSMulRegular q` at rungs `≥ 2`: rung 0 is
   (t1) above; rung 1 is the t2a/t2b dichotomy of `TriangularRegularity.lean`
   (cited, not imported — see the dependencies note); rungs `≥ 2` are the
   `hunmixed_ge2` residual (the (t3) obstruction is documented in
   `TriangularRegularity.lean`: after quotienting by the non-monic step-2 prime
   there is no division algorithm).
2. Per-`(k,d)` graded-piece SES data (`f`/`e`/`hinj` plus finrank
   identifications) for `k ≥ 1`: these await the graded-quotient API
   (Mathlib v4.34.0 provides `homogeneousSubmodule` only for the polynomial
   ring; the `gradeMul` construction is proved in `MkSystemSESData`,
   cited not imported). The `hlow`
   half (degrees `< 2` / `< 1`) is taken explicitly for the same reason.

## Dependencies

This file deliberately avoids importing the following modules:

* `Statement/Statement`: never imported (DAG hygiene).
  `mkSystem_homogeneous` there is re-proved below as
  `mkSystem_isHomogeneous_of` (same 5-line proof).
* `Regularity/GradeDepthFragment`: never imported (it imports
  `Regularity/HeightDrop`, which this file must not depend on); only
  `RegularityBridge` (its `Statement`-free dependency) is imported.
* `Regularity/ResultantLemmas`, `Regularity/TriangularRegularity`,
  `BridgeToFixedPoint/MkSystemBridge`, `Geometry/Counting`,
  `BridgeToFixedPoint/FixedPointFromBezout`: all transitively import
  `Statement` and/or `FixedPointFromBezout` (excluded for DAG hygiene);
  their proof arguments (t1 monomial argument, `heval0`, span repair)
  are re-proved here from primary Mathlib API, never imported.
* `Geometry/HilbertFunctionCount` (hence `ChartFiltration`, `Elimination`,
  `LocalMultiplicity`) is `Statement`-free (its closure is only `Statement/Definitions`
  plus Mathlib).

`E` (`NonUnitalNonAssocRing E`, `Module K E`) is carried as a variable but
plays no role: this route uses only fields and multivariate polynomials. No
`IsAlgClosed` hypothesis is needed anywhere below (no prime avoidance is
used).

## References

Mathlib v4.34.0 exact names (with source locations under
`.lake/packages/mathlib`):

* `MvPolynomial.ne_zero_iff`, `MvPolynomial.coeff_X_mul`,
  `MvPolynomial.coeff_X_same`, `MvPolynomial.smul_eq_C_mul`,
  `MvPolynomial.constantCoeff_eq`
  (`Mathlib/Algebra/MvPolynomial/Basic.lean`).
* `MvPolynomial.coeff_rename_eq_zero`
  (`Mathlib/Algebra/MvPolynomial/Rename.lean`).
* `MvPolynomial.eval` (a `→+*` def), `MvPolynomial.eval_zero`
  (`Mathlib/Algebra/MvPolynomial/Eval.lean`).
* `Finsupp.mapDomain_of_notMem_range`
  (`Mathlib/Data/Finsupp/Basic.lean`); `Finsupp.single_eq_same`,
  `Finsupp.single_eq_of_ne` (`Mathlib/Data/Finsupp/Single.lean`).
* `Fin.castSucc_lt_last` (`Mathlib/Data/Fin/Basic.lean`).
* `isSMulRegular_iff_right_eq_zero_of_smul`
  (`Mathlib/Algebra/GroupWithZero/Action/Regular.lean`);
  `eq_zero_of_ne_zero_of_mul_left_eq_zero`
  (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`).
* `MvPolynomial.IsHomogeneous.coeff_eq_zero`,
  `MvPolynomial.IsHomogeneous.sub`, `MvPolynomial.IsHomogeneous.sum`,
  `MvPolynomial.IsHomogeneous.mul`, `MvPolynomial.IsHomogeneous.C_mul`,
  `MvPolynomial.isHomogeneous_X`, `MvPolynomial.rename_isHomogeneous`
  (`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`).
* `RingTheory.Sequence.IsRegular` (`top_ne_smul`),
  `RingTheory.Sequence.isWeaklyRegular_singleton_iff`
  (`Mathlib/RingTheory/Regular/RegularSequence.lean`).
* `Matrix.isUnit_iff_isUnit_det`, `Matrix.nonsing_inv_mul`
  (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`);
  `Matrix.mul_apply` (`Mathlib/Data/Matrix/Mul.lean`);
  `Matrix.one_apply` (`Mathlib/Data/Matrix/Diagonal.lean`).
* `Ideal.span_le`, `Ideal.subset_span`
  (`Mathlib/RingTheory/Ideal/Span.lean`); `Ideal.sum_mem`,
  `Ideal.mul_mem_left` (`Mathlib/RingTheory/Ideal/Operations.lean`).

Project (cited, only the DAG-safe ones imported):

* `Appendix_FixedPoint.BezoutChain.mkSystem` (`Statement/Definitions.lean`).
* `Appendix_FixedPoint.BezoutChain.RegularityBridge.SuccessiveSMulRegular`,
  `Appendix_FixedPoint.BezoutChain.RegularityBridge.isRegular_ofFn_of_successive`,
  `Appendix_FixedPoint.BezoutChain.RegularityBridge.top_ne_smul_ofList_of_forall_map_zero`,
  `Appendix_FixedPoint.BezoutChain.RegularityBridge.top_ne_smul_ofFn_of_forall_map_zero`
  (`Regularity/Avoid/RegularityBridge.lean`).
* `Appendix_FixedPoint.BezoutChain.graded_piece_ses`,
  `Appendix_FixedPoint.BezoutChain.hSES_step_of_pieceSES`,
  `Appendix_FixedPoint.BezoutChain.hSES_of_steps`,
  `Appendix_FixedPoint.BezoutChain.length_section_eq_two_pow`
  (`Geometry/HilbertFunctionCount.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MkSystemRegular

open scoped BigOperators

variable (n : ℕ) (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-! ## (t1) Each `Gᵢ` is nonzero, hence regular — the `−z·xᵢ` monomial.

This is the nonvanishing half: the monomial `z¹xᵢ¹` occurs with
coefficient `−1` and cannot be
cancelled since `Fᵢ` involves no `z`. The proof is the (t1) argument of
`TriangularRegularity.lean`, re-proved here to avoid depending on `Statement`.
-/

/-- (t1) Each `Gᵢ = Fᵢ(x) − z·xᵢ` is nonzero. -/
theorem mkSystem_ne_zero
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) :
    mkSystem n K F i ≠ 0 := by
  rw [MvPolynomial.ne_zero_iff]
  refine ⟨Finsupp.single (Fin.last (n + 1)) 1 +
    Finsupp.single (Fin.castSucc i) 1, ?_⟩
  have hxi : Fin.castSucc i ≠ Fin.last (n + 1) := by
    intro h
    have hlt := Fin.castSucc_lt_last i
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hlast : Fin.last (n + 1) ∉
      Set.range (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
    rintro ⟨j, hj⟩
    have hlt := Fin.castSucc_lt_last j
    rw [hj] at hlt
    exact lt_irrefl _ hlt
  have hren : (MvPolynomial.rename Fin.castSucc (F i)).coeff
        (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1) = 0 := by
    apply MvPolynomial.coeff_rename_eq_zero
    intro u hu
    exfalso
    have h1 : (u.mapDomain Fin.castSucc) (Fin.last (n + 1)) = 0 :=
      Finsupp.mapDomain_of_notMem_range _ _ hlast
    have h2 : (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1 : Fin (n + 2) →₀ ℕ)
        (Fin.last (n + 1)) = 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (Ne.symm hxi), add_zero]
    rw [hu, h2] at h1
    exact one_ne_zero h1
  have hprod : (MvPolynomial.X (Fin.last (n + 1)) *
        MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (n + 2)) K).coeff
        (Finsupp.single (Fin.last (n + 1)) 1 +
          Finsupp.single (Fin.castSucc i) 1) = 1 := by
    rw [MvPolynomial.coeff_X_mul]
    exact MvPolynomial.coeff_X_same _
  have hG : mkSystem n K F i = MvPolynomial.rename Fin.castSucc (F i) -
      MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) := rfl
  rw [hG, MvPolynomial.coeff_sub, hren, hprod]
  simp

/-- (t1, regularity form) Each `Gᵢ` is regular on the domain. -/
theorem mkSystem_isSMulRegular
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) :
    IsSMulRegular (MvPolynomial (Fin (n + 2)) K) (mkSystem n K F i) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  rw [smul_eq_mul] at hm
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero
    (mkSystem_ne_zero n K F i) hm

/-! ## Homogeneity and origin-vanishing (properness input).

`mkSystem_isHomogeneous_of` re-proves `Statement/Statement.mkSystem_homogeneous`
(verbatim proof) to avoid depending on `Statement`; `mkSystem_eval_zero`
is the `heval0` argument of `ResultantLemmas.lean`, re-proved.
-/

/-- Each `Gᵢ` is homogeneous of degree `2` when the input forms are
(`Statement/Statement.mkSystem_homogeneous`, re-proved here to avoid depending
on `Statement`). -/
theorem mkSystem_isHomogeneous_of
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous 2) (i : Fin (n + 1)) :
    (mkSystem n K F i).IsHomogeneous 2 := by
  simp only [mkSystem]
  exact ((hF i).rename_isHomogeneous).sub
    (by simpa using
      (MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- Each `Gᵢ` vanishes at the origin (positive-degree homogeneous part has
zero constant coefficient). -/
theorem mkSystem_eval_zero
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) (hF : ∀ i, (F i).IsHomogeneous 2) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i) = 0 := by
  have hG := mkSystem_isHomogeneous_of n K F hF i
  have h1 : MvPolynomial.eval (0 : Fin (n + 2) → K) (mkSystem n K F i)
      = MvPolynomial.constantCoeff (mkSystem n K F i) :=
    congrFun (congrArg DFunLike.coe MvPolynomial.eval_zero) _
  rw [h1, MvPolynomial.constantCoeff_eq]
  exact MvPolynomial.IsHomogeneous.coeff_eq_zero hG (by
    have hdeg : (0 : Fin (n + 2) →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega)

/-- (t1, assembled) Each single generator is a length-1 regular sequence:
weak regularity is (t1); properness is origin-vanishing. -/
theorem mkSystem_singleton_isRegular
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (i : Fin (n + 1)) (hF : ∀ i, (F i).IsHomogeneous 2) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
      [mkSystem n K F i] := by
  refine ⟨?_, ?_⟩
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact mkSystem_isSMulRegular n K F i
  · apply RegularityBridge.top_ne_smul_ofList_of_forall_map_zero
      (MvPolynomial.eval (0 : Fin (n + 2) → K))
    intro r hr
    simp only [List.mem_singleton] at hr
    rw [hr]
    exact mkSystem_eval_zero n K F i hF

/-! ## Conditional assembly: successive data + origin-vanishing `⇒ IsRegular`.

The successive SMul-regularity hypothesis `hsucc` is rung 0 by (t1) above,
rung 1 by the t2a/t2b dichotomy (`TriangularRegularity.lean`, cited not imported),
and rungs `≥ 2` the `hunmixed_ge2` residual. Given `hsucc`, the assembly
below is unconditional.
-/

/-- `K`-linear combinations vanish at the origin when the generators do. -/
theorem combo_eval_zero
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (heval : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (G i) = 0)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (∑ j, M k j • G j) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, heval j,
    mul_zero]

/-- `K`-linear combinations of quadrics are quadrics. -/
theorem combo_isHomogeneous
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hG : ∀ j, (G j).IsHomogeneous 2)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    (∑ j, M k j • G j).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (hG j).C_mul _

/-- A unit change of generators preserves the span (inverse-matrix repair).
`N := M⁻¹` with `N * M = 1` expands each `G i` in the combinations. -/
theorem combo_span_eq
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hM : IsUnit M) :
    Ideal.span (Set.range fun k => ∑ j, M k j • G j)
      = Ideal.span (Set.range G) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr (fun x hx => ?_)
    obtain ⟨k, rfl⟩ := hx
    refine Ideal.sum_mem _ (fun j _ => ?_)
    rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · refine Ideal.span_le.mpr (fun x hx => ?_)
    obtain ⟨i, rfl⟩ := hx
    have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
    have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
    have hsum : ∀ j, (∑ k, M⁻¹ i k * M k j)
        = (if i = j then (1 : K) else 0) := by
      intro j
      rw [← Matrix.mul_apply, hNM]
      exact Matrix.one_apply
    have e1 : ∀ k, M⁻¹ i k • (∑ j, M k j • G j)
        = ∑ j, (M⁻¹ i k * M k j) • G j := by
      intro k
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul]
    have hexpand : G i = ∑ k, M⁻¹ i k • (∑ j, M k j • G j) := by
      calc G i = ∑ j, (if i = j then (1 : K) else 0) • G j := by
              have hss := Finset.sum_eq_single (s := Finset.univ)
                (f := fun j => (if i = j then (1 : K) else 0) • G j) i
                (fun j _ hji => by
                  rw [ite_eq_right (fun h => hji h.symm), zero_smul])
                (fun hcon => absurd (Finset.mem_univ i) hcon)
              rw [ite_eq_left (show i = i from rfl), one_smul] at hss
              exact hss.symm
        _ = ∑ k, M⁻¹ i k • (∑ j, M k j • G j) := by
              simp only [e1]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j _
              rw [← Finset.sum_smul, hsum j]
    rw [hexpand]
    refine Ideal.sum_mem _ (fun k _ => ?_)
    have hmem : (∑ j, M k j • G j)
        ∈ Ideal.span (Set.range fun k => ∑ j, M k j • G j) :=
      Ideal.subset_span ⟨k, rfl⟩
    rw [MvPolynomial.smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ hmem

/-- Successive regularity + origin-vanishing assemble to `IsRegular` for any
`Fin k`-indexed family (properness via evaluation at the origin). -/
theorem isRegular_ofFn_of_successive_of_evalZero {k : ℕ}
    (q : Fin k → MvPolynomial (Fin (n + 2)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (heval : ∀ i, MvPolynomial.eval (0 : Fin (n + 2) → K) (q i) = 0) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
      (List.ofFn q) :=
  RegularityBridge.isRegular_ofFn_of_successive q hsucc
    (RegularityBridge.top_ne_smul_ofFn_of_forall_map_zero q
      (MvPolynomial.eval (0 : Fin (n + 2) → K)) heval)

/-- The `mkSystem` conditional assembly: `F`-combinations of the `mkSystem`
generators form a regular sequence with the same span, given successive
regularity data (hypothesis (1) above) and homogeneous input forms. -/
theorem mkSystem_isRegular_of_successive
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hM : IsUnit M)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (fun k => ∑ j, M k j • mkSystem n K F j))
    (hF : ∀ i, (F i).IsHomogeneous 2) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 2)) K)
        (List.ofFn fun k => ∑ j, M k j • mkSystem n K F j)
      ∧ Ideal.span (Set.range fun k => ∑ j, M k j • mkSystem n K F j)
        = Ideal.span (Set.range (mkSystem n K F)) := by
  refine ⟨?_, combo_span_eq n K (mkSystem n K F) M hM⟩
  apply isRegular_ofFn_of_successive_of_evalZero n K _ hsucc
  intro k
  show MvPolynomial.eval (0 : Fin (n + 2) → K)
    (∑ j, M k j • mkSystem n K F j) = 0
  apply combo_eval_zero n K _ _ M k
  intro i
  exact mkSystem_eval_zero n K F i hF

/-! ## The `hSES`/`hSEC` feed in exact consumer shapes.

`hSEC_step_of_pieceSES` / `hSEC_of_steps` are the shift-1 mirrors of the
shift-2 `hSES` pair; both go through `graded_piece_ses` (itself
`ses_finrank_add`). The `mkSystem_hSES_of_steps` / `mkSystem_hSEC_of_steps`
corollaries give the exact `length_section_eq_two_pow` / `bezout_quadratic`
numerical input shapes; the per-step graded-piece data stay explicit
(hypothesis (2) above).
-/

/-- Single-step section recurrence from graded-piece data: the exact inputs
of `graded_piece_ses` plus the three finrank identifications give one
`F d + H (d-1) = H d` equation (shift-1 mirror of `hSES_step_of_pieceSES`). -/
theorem hSEC_step_of_pieceSES
    (a b c : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (ha : a = Module.finrank K R)
    (hb : b = Module.finrank K P)
    (hc : c = Module.finrank K Q) :
    a + b = c := by
  rw [ha, hb, hc]
  have h := graded_piece_ses K P Q R f e hinj
  omega

/-- Assembly of per-degree section steps into the exact `hSEC` input shape
of `length_section_eq_two_pow` (mirror of `hSES_of_steps`). -/
theorem hSEC_of_steps (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hstep : ∀ d, 1 ≤ d → F d + H (n + 1) (d - 1) = H (n + 1) d)
    (hlow : F 0 = H (n + 1) 0) :
    ∀ d, F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d := by
  intro d
  by_cases hd : 1 ≤ d
  · simp only [hd, ite_true]; exact hstep d hd
  · simp only [hd, ite_false, add_zero]
    have hd0 : d = 0 := by omega
    rw [hd0]; exact hlow

/-- Per-`(k,d)` `hSES` step from graded-piece SES data at the `mkSystem`
system: `H (k+1) d + H k (d-2) = H k d` for `2 ≤ d`, via
`hSES_step_of_pieceSES`. The `f`/`e`/`hinj` inputs are the
multiplication-by-the-stage-`k`-quadric SES data (regularity from the
`IsRegular` family above; the cokernel identification for `k ≥ 1` is
hypothesis (2)). -/
theorem mkSystem_hstep_of_pieceSES (H : ℕ → ℕ → ℕ) (k d : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (ha : H (k + 1) d = Module.finrank K R)
    (hb : H k (d - 2) = Module.finrank K P)
    (hc : H k d = Module.finrank K Q) :
    H (k + 1) d + H k (d - 2) = H k d :=
  hSES_step_of_pieceSES K _ _ _ P Q R f e hinj ha hb hc

/-- The exact `hSES` input shape of `length_section_eq_two_pow`, from the
per-`(k,d)` steps (discharged per-step by `mkSystem_hstep_of_pieceSES`) and
the low-degree agreement `hlow`. -/
theorem mkSystem_hSES_of_steps (H : ℕ → ℕ → ℕ)
    (hstep : ∀ k, k < n + 1 → ∀ d, 2 ≤ d →
      H (k + 1) d + H k (d - 2) = H k d)
    (hlow : ∀ k, k < n + 1 → ∀ d, d < 2 → H (k + 1) d = H k d) :
    ∀ k, k < n + 1 → ∀ d,
      H (k + 1) d + (if 2 ≤ d then H k (d - 2) else 0) = H k d :=
  hSES_of_steps n H hstep hlow

/-- Per-degree `hSEC` step from graded-piece SES data: `F d + H (d-1) = H d`
for `1 ≤ d`, via the new `hSEC_step_of_pieceSES` (shift 1: the section form
`ℓ` is linear). -/
theorem mkSystem_hSECstep_of_pieceSES (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ) (d : ℕ)
    (P Q R : Type*) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup R]
    [Module K P] [Module K Q] [Module K R]
    [Module.Finite K P] [Module.Finite K Q]
    (f : P →ₗ[K] Q) (e : (Q ⧸ LinearMap.range f) ≃ₗ[K] R)
    (hinj : Function.Injective f)
    (ha : F d = Module.finrank K R)
    (hb : H (n + 1) (d - 1) = Module.finrank K P)
    (hc : H (n + 1) d = Module.finrank K Q) :
    F d + H (n + 1) (d - 1) = H (n + 1) d :=
  hSEC_step_of_pieceSES K _ _ _ P Q R f e hinj ha hb hc

/-- The exact `hSEC` input shape of `length_section_eq_two_pow`, from the
per-degree steps (discharged per-`d` by `mkSystem_hSECstep_of_pieceSES`) and
the degree-`0` agreement `hlow`. -/
theorem mkSystem_hSEC_of_steps (H : ℕ → ℕ → ℕ) (F : ℕ → ℕ)
    (hstep : ∀ d, 1 ≤ d → F d + H (n + 1) (d - 1) = H (n + 1) d)
    (hlow : F 0 = H (n + 1) 0) :
    ∀ d, F d + (if 1 ≤ d then H (n + 1) (d - 1) else 0) = H (n + 1) d :=
  hSEC_of_steps n H F hstep hlow

end MkSystemRegular
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
