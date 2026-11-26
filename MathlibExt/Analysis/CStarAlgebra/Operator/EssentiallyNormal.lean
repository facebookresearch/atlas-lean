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

public import MathlibExt.Analysis.Normed.Operator.Compact.EssentialSpectrum
public import MathlibExt.Analysis.CStarAlgebra.Operator.FredholmCalkin

/-!
# Essential normality and scalar Fredholm resolvents

For a bounded operator `T` on a complex Hilbert space, essential normality means star-normality
of its Calkin class `q(T)`. Equivalently, `T* T - T T*` is compact. Adding or subtracting a
compact operator preserves this property.

The essential spectrum is `σ(q(T))`. Atkinson's theorem identifies `z ∉ σ_ess(T)` with
Fredholmness of `T-z I`. Finite-dimensional and zero Hilbert spaces are allowed.
-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Essential normality of a Hilbert operator.** For a complex Hilbert space `H`, a bounded `T`
is essentially normal when its class `q(T) : Q(H)` satisfies `q(T)* q(T) = q(T) q(T)*`. -/
def IsEssentiallyNormal (T : H →L[ℂ] H) : Prop :=
  IsStarNormal (CalkinAlgebra.classStarMap (H := H) T)

/-- **Compact commutator criterion for essential normality.** For a complex Hilbert space `H`,
`T.IsEssentiallyNormal ↔ IsCompactOperator (star T*T - T*star T)` for a bounded operator `T`. -/
theorem isEssentiallyNormal_iff_isCompactOperator_commutator (T : H →L[ℂ] H) :
    T.IsEssentiallyNormal ↔ IsCompactOperator (star T * T - T * star T) := by
  rw [IsEssentiallyNormal, isStarNormal_iff, commute_iff_eq,
    ← CalkinAlgebra.classStarMap_eq_zero_iff]
  simp only [map_sub, map_mul, map_star, sub_eq_zero]

/-- **Calkin spectrum of a Hilbert operator.** For a complex Hilbert space `H`,
`T.essentialSpectrum = spectrum ℂ (classStarMap T)` for every bounded complex-linear `T`. -/
theorem essentialSpectrum_eq_spectrum_classStarMap (T : H →L[ℂ] H) :
    T.essentialSpectrum = spectrum ℂ (CalkinAlgebra.classStarMap (H := H) T) :=
  rfl

/-- **Essential normality under compact addition.** For a complex Hilbert space `H`, if the
bounded operator `K` is compact, `(T+K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal`. -/
theorem isEssentiallyNormal_add_compact_iff (T K : H →L[ℂ] H)
    (hK : IsCompactOperator K) :
    (T + K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal := by
  simp only [IsEssentiallyNormal, map_add,
    (CalkinAlgebra.classStarMap_eq_zero_iff K).mpr hK, add_zero]

/-- **Essential normality under compact subtraction.** For a complex Hilbert space `H`, if `K` is
compact, `(T-K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal`. -/
theorem isEssentiallyNormal_sub_compact_iff (T K : H →L[ℂ] H)
    (hK : IsCompactOperator K) :
    (T - K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal := by
  simp only [IsEssentiallyNormal, map_sub,
    (CalkinAlgebra.classStarMap_eq_zero_iff K).mpr hK, sub_zero]

/-- **Fredholm criterion for a scalar resolvent.** For a complex Hilbert space `H`, for bounded
`T` and `z : ℂ`, `z ∉ T.essentialSpectrum ↔ (T-z • 1).IsFredholm`. -/
theorem notMem_essentialSpectrum_iff_isFredholm (T : H →L[ℂ] H) (z : ℂ) :
    z ∉ T.essentialSpectrum ↔ (T - z • 1).IsFredholm := by
  rw [notMem_essentialSpectrum_iff_isUnit]
  exact CalkinAlgebra.isUnit_classStarMap_iff_isFredholm (T - z • 1)

/-- **Fredholm operator outside the essential spectrum.** For a complex Hilbert space `H`, if `z :
ℂ` lies outside the essential spectrum of `T`, then `T-z I` is Fredholm. -/
theorem isFredholm_of_notMem_essentialSpectrum (T : H →L[ℂ] H) (z : ℂ)
    (hz : z ∉ T.essentialSpectrum) : (T - z • 1).IsFredholm :=
  (T.notMem_essentialSpectrum_iff_isFredholm z).mp hz

end ContinuousLinearMap
