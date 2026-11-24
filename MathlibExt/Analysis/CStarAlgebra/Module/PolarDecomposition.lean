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
# Dense-range polar decomposition for adjointable module maps

For an adjointable map `T : E → F`, suppose the adjoint square `T* T` and `T`
have dense range.  The existing rectangular-operator positivity theorem makes
`T* T` nonnegative in the canonical spectral order.  Its
continuous-functional-calculus square root has dense range, and the rule
`sqrt (T* T) x ↦ T x` extends to a unique unitary equivalence.

This is the source-neutral analytic step used in Blackadar, *K-Theory for
Operator Algebras*, second edition, in the proof of Theorem 13.6.2.  The
compactness of the particular operator constructed there is not used here.

No compactness, fullness, countability, or closed-range hypothesis is used.
The cross-module positivity input is the actual
`AdjointableOperator.adjoint_comp_self_nonneg` theorem, not a supplied model or
an inferred global order instance.
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

/-- The endomorphism `T* T` belonging to a cross-module adjointable map. -/
abbrev adjointSquare (T : AdjointableOperator B E F) : End B E :=
  T.adjointOperator.comp T

/-- The positive square root of `T* T` in the adjointable endomorphism
C-star algebra. -/
noncomputable def absoluteValue
    (T : AdjointableOperator B E F) : End B E := by
  letI : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  exact CFC.sqrt T.adjointSquare

omit [CompleteSpace F] in
/-- The absolute value is nonnegative in the canonical spectral order. -/
theorem absoluteValue_nonnegative (T : AdjointableOperator B E F) :
    @LE.le (End B E) (CStarAlgebra.spectralOrder (End B E)).toLE
      0 T.absoluteValue := by
  let _ : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  exact CFC.sqrt_nonneg T.adjointSquare

/-- The square of the absolute value is the adjoint square. -/
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

/-- Dense range of `T* T` implies dense range of its positive square root. -/
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

/-- The canonical unitary factor in the dense-range polar decomposition. -/
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

/-- The polar unitary is characterized on the dense range of the absolute
value by `U (|T| x) = T x`. -/
@[simp]
theorem polarUnitary_absoluteValue_apply
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) (x : E) :
    T.polarUnitary hAbsoluteDense hDense (T.absoluteValue x) = T x := by
  exact CStarModule.UnitaryEquiv.ofDenseLinearMaps_apply
    T.absoluteValue.toContinuousLinearMap.toLinearMap
    T.toContinuousLinearMap.toLinearMap _ _ T.absoluteValue_gram x

/-- The adjoint of the polar unitary sends `T x` back to `|T| x`. -/
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

/-- Dense-range polar decomposition in source orientation `T = U |T|`. -/
theorem polarDecomposition
    (T : AdjointableOperator B E F)
    (hAbsoluteDense : DenseRange T.absoluteValue)
    (hDense : DenseRange T) :
    T = (T.polarUnitary hAbsoluteDense hDense).toAdjointable.comp
      T.absoluteValue := by
  apply AdjointableOperator.ext
  intro x
  exact (T.polarUnitary_absoluteValue_apply hAbsoluteDense hDense x).symm

/-- Dense ranges of `T* T` and `T` give one unitary polar decomposition,
with the unitary characterized on every square-root image. -/
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

/-- The unitary in the dense-range polar decomposition is unique. -/
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
