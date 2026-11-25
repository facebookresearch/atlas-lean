/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary.Dense

import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.Positivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Dense-range polar decomposition of adjointable maps

Let `T : E → F` be adjointable between complete right C-star modules over a nonunital algebra
`B` with star-compatible coefficient order. In `End_B(E)`, put `|T| = sqrt(T* T)` using
continuous functional calculus. Then `|T| ≥ 0` and `|T|² = T* T` in the spectral order.

If `|T|` and `T` have dense ranges, the rule `|T| x ↦ T x` extends to a unique unitary `U : E ≃
F` and `T = U |T|`. Dense range of `T* T` suffices for dense range of `|T|`, so it gives the
same decomposition when `T` also has dense range.

This dense-range argument appears in Blackadar, K-Theory for Operator Algebras, second edition,
Theorem 13.6.2.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace CStarModule.AdjointableOperator

noncomputable section

universe uB uE uF

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
  [StarOrderedRing Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F] [CompleteSpace F]

/-- **Adjoint square of a module map.** For an adjointable `T : E → F`, `T.adjointSquare =
T.adjointOperator.comp T` is the endomorphism `T* T` of `E`. -/
abbrev adjointSquare (T : AdjointableOperator B E F) : End B E :=
  T.adjointOperator.comp T

/-- **Absolute value of an adjointable map.** For an adjointable map between complete right C-star
modules, `T.absoluteValue` is the positive continuous-functional-calculus square root of `T*
T` in `End_B(E)`. -/
noncomputable def absoluteValue
    (T : AdjointableOperator B E F) : End B E := by
  letI : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  exact CFC.sqrt T.adjointSquare

omit [CompleteSpace F] in
/-- **Positivity of the absolute value.** `0 ≤ T.absoluteValue` in the C-star spectral order on
`End_B(E)`. -/
theorem absoluteValue_nonnegative (T : AdjointableOperator B E F) :
    @LE.le (End B E) (CStarAlgebra.spectralOrder (End B E)).toLE
      0 T.absoluteValue := by
  let _ : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  exact CFC.sqrt_nonneg T.adjointSquare

/-- **Square of the absolute value.** For an adjointable map, `T.absoluteValue * T.absoluteValue =
T.adjointSquare`. -/
theorem absoluteValue_sq (T : AdjointableOperator B E F) :
    T.absoluteValue * T.absoluteValue = T.adjointSquare := by
  let _ : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  have hnonneg : (0 : End B E) ≤ T.adjointSquare :=
    adjoint_comp_self_nonneg T
  simpa only [absoluteValue] using
    CFC.sqrt_mul_sqrt_self T.adjointSquare hnonneg

omit [CompleteSpace F] in
private theorem absoluteValue_adjointOperator
    (T : AdjointableOperator B E F) :
    T.absoluteValue.adjointOperator = T.absoluteValue := by
  change star T.absoluteValue = T.absoluteValue
  let _ : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  exact (IsSelfAdjoint.of_nonneg (absoluteValue_nonnegative T)).star_eq

/-- **Dense range of the absolute value.** If `T* T` has dense range on `E`, its positive square
root `T.absoluteValue` has dense range. -/
theorem denseRange_absoluteValue_of_denseRange_adjointSquare
    (T : AdjointableOperator B E F)
    (hDense : DenseRange T.adjointSquare) :
    DenseRange T.absoluteValue := by
  refine Dense.mono ?_ hDense
  rintro _ ⟨x, rfl⟩
  refine ⟨T.absoluteValue x, ?_⟩
  have h := congrArg (fun S : End B E => S x) (absoluteValue_sq T)
  simpa only [mul_apply] using h

private theorem absoluteValue_gram
    (T : AdjointableOperator B E F)
    (x y : E) :
    rightInner (B := B) (T x) (T y) =
      rightInner (B := B) (T.absoluteValue x) (T.absoluteValue y) := by
  have hSquareApply :
      T.absoluteValue (T.absoluteValue y) = T.adjointSquare y := by
    have h := congrArg (fun S : End B E => S y) (absoluteValue_sq T)
    simpa only [mul_apply] using h
  have hAdjointApply :
      T.absoluteValue.adjoint (T.absoluteValue y) =
        T.absoluteValue (T.absoluteValue y) := by
    have h := congrArg (fun S : End B E => S (T.absoluteValue y))
      (absoluteValue_adjointOperator T)
    exact h
  calc
    rightInner (B := B) (T x) (T y) =
        rightInner (B := B) x (T.adjoint (T y)) :=
      T.adjoint_inner x (T y)
    _ = rightInner (B := B) x (T.adjointSquare y) := by
      rfl
    _ = rightInner (B := B) x
        (T.absoluteValue (T.absoluteValue y)) := by
      rw [hSquareApply]
    _ = rightInner (B := B) x
        (T.absoluteValue.adjoint (T.absoluteValue y)) := by
      rw [hAdjointApply]
    _ = rightInner (B := B) (T.absoluteValue x)
        (T.absoluteValue y) := by
      exact (T.absoluteValue.adjoint_inner x (T.absoluteValue y)).symm

/-- **Unitary factor in a dense-range polar decomposition.** When `T.absoluteValue` and `T` have
dense ranges between complete right C-star modules, `polarUnitary` is the unitary
characterized by `U (T.absoluteValue x) = T x`. -/
@[no_expose]
noncomputable def polarUnitary
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) :
    CStarModule.UnitaryEquiv B E F :=
  CStarModule.UnitaryEquiv.ofDenseLinearMaps
    T.absoluteValue.toContinuousLinearMap.toLinearMap
    T.toContinuousLinearMap.toLinearMap
    (by
      change DenseRange T.absoluteValue
      exact hAbsoluteDense)
    (by
      change DenseRange T
      exact hDense)
    T.absoluteValue_gram

/-- **Polar unitary on the absolute-value range.** Assuming dense ranges of `|T|` and `T`,
`T.polarUnitary hAbsoluteDense hDense (T.absoluteValue x) = T x` for every `x : E`. -/
@[simp]
theorem polarUnitary_absoluteValue_apply
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) (x : E) :
    T.polarUnitary hAbsoluteDense hDense (T.absoluteValue x) = T x := by
  exact CStarModule.UnitaryEquiv.ofDenseLinearMaps_apply
    T.absoluteValue.toContinuousLinearMap.toLinearMap
    T.toContinuousLinearMap.toLinearMap _ _ T.absoluteValue_gram x

/-- **Adjoint of the polar unitary.** Assuming dense ranges of `|T|` and `T`, `U* (T x) = |T| x`,
where `U = T.polarUnitary hAbsoluteDense hDense`. -/
@[simp]
theorem polarUnitary_adjoint_apply
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) (x : E) :
    (T.polarUnitary hAbsoluteDense hDense).toAdjointable.adjoint (T x) =
      T.absoluteValue x := by
  exact CStarModule.UnitaryEquiv.ofDenseLinearMaps_adjoint_apply
    T.absoluteValue.toContinuousLinearMap.toLinearMap
    T.toContinuousLinearMap.toLinearMap _ _ T.absoluteValue_gram x

/-- **Dense-range polar decomposition.** If `|T|` and `T` have dense ranges, `T =
U.toAdjointable.comp T.absoluteValue` for the unitary `U = T.polarUnitary hAbsoluteDense
hDense`. -/
theorem polarDecomposition
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) :
    T = (T.polarUnitary hAbsoluteDense hDense).toAdjointable.comp
      T.absoluteValue := by
  apply AdjointableOperator.ext
  intro x
  exact (T.polarUnitary_absoluteValue_apply hAbsoluteDense hDense x).symm

/-- **Existence of a unitary polar factor.** For an adjointable map between complete right C-star
modules, dense ranges of `T* T` and `T` imply existence of a unitary `U` with `T = U |T|` and
`U (|T| x) = T x` for every `x`. -/
theorem exists_polarDecomposition
    (T : AdjointableOperator B E F)
    (hSquareDense : DenseRange T.adjointSquare)
    (hDense : DenseRange T) :
    ∃ U : CStarModule.UnitaryEquiv B E F,
      T = U.toAdjointable.comp T.absoluteValue ∧
        ∀ x, U (T.absoluteValue x) = T x := by
  let hAbsoluteDense : DenseRange T.absoluteValue :=
    T.denseRange_absoluteValue_of_denseRange_adjointSquare hSquareDense
  exact ⟨T.polarUnitary hAbsoluteDense hDense,
    T.polarDecomposition hAbsoluteDense hDense,
    T.polarUnitary_absoluteValue_apply hAbsoluteDense hDense⟩

/-- **Uniqueness of the dense-range polar factor.** If `|T|` and `T` have dense ranges, every
unitary `U` satisfying `T = U |T|` equals `T.polarUnitary hAbsoluteDense hDense`. -/
theorem polarUnitary_unique
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T)
    (U : CStarModule.UnitaryEquiv B E F)
    (hU : T = U.toAdjointable.comp T.absoluteValue) :
    U = T.polarUnitary hAbsoluteDense hDense := by
  apply CStarModule.UnitaryEquiv.ofDenseLinearMaps_unique
    T.absoluteValue.toContinuousLinearMap.toLinearMap
    T.toContinuousLinearMap.toLinearMap
    (by
      change DenseRange T.absoluteValue
      exact hAbsoluteDense)
    (by
      change DenseRange T
      exact hDense)
    T.absoluteValue_gram
  intro x
  change U (T.absoluteValue x) = T x
  calc
    U (T.absoluteValue x) =
        (U.toAdjointable.comp T.absoluteValue) x := by rfl
    _ = T x := (congrArg (fun S : AdjointableOperator B E F => S x) hU).symm

end

end CStarModule.AdjointableOperator
