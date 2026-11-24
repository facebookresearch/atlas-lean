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
# Essentially normal Hilbert operators

Essential normality is normality of the actual Calkin class. Its compact
commutator characterization and invariance under compact perturbations use
the existing star class map. The Banach-space essential spectrum is reused
without changing its carrier or scalar action.

Atkinson's theorem identifies the complement of that spectrum with Fredholm
scalar resolvents. Hilbert spaces may be finite-dimensional or zero; neither
an infinite-dimensional assumption nor a global nontriviality instance is added.
-/

@[expose] public section

noncomputable section

namespace ContinuousLinearMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An operator is essentially normal when its class modulo compact operators
is star-normal. -/
def IsEssentiallyNormal (T : H →L[ℂ] H) : Prop :=
  IsStarNormal (CalkinAlgebra.classStarMap (H := H) T)

/-- Essential normality is equivalent to compactness of the adjoint commutator. -/
theorem isEssentiallyNormal_iff_isCompactOperator_commutator (T : H →L[ℂ] H) :
    T.IsEssentiallyNormal ↔ IsCompactOperator (star T * T - T * star T) := by
  rw [IsEssentiallyNormal, isStarNormal_iff, commute_iff_eq,
    ← CalkinAlgebra.classStarMap_eq_zero_iff]
  simp only [map_sub, map_mul, map_star, sub_eq_zero]

/-- The generic Banach-space definition uses the same class as the Hilbert
star-algebra projection. -/
theorem essentialSpectrum_eq_spectrum_classStarMap (T : H →L[ℂ] H) :
    T.essentialSpectrum = spectrum ℂ (CalkinAlgebra.classStarMap (H := H) T) :=
  rfl

/-- Compact perturbations preserve and reflect essential normality. -/
theorem isEssentiallyNormal_add_compact_iff (T K : H →L[ℂ] H)
    (hK : IsCompactOperator K) :
    (T + K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal := by
  simp only [IsEssentiallyNormal, map_add,
    (CalkinAlgebra.classStarMap_eq_zero_iff K).mpr hK, add_zero]

/-- Subtracting a compact operator preserves and reflects essential normality. -/
theorem isEssentiallyNormal_sub_compact_iff (T K : H →L[ℂ] H)
    (hK : IsCompactOperator K) :
    (T - K).IsEssentiallyNormal ↔ T.IsEssentiallyNormal := by
  simp only [IsEssentiallyNormal, map_sub,
    (CalkinAlgebra.classStarMap_eq_zero_iff K).mpr hK, sub_zero]

/-- Atkinson's theorem for the exact essential-spectrum resolvent. -/
theorem notMem_essentialSpectrum_iff_isFredholm (T : H →L[ℂ] H) (z : ℂ) :
    z ∉ T.essentialSpectrum ↔ (T - z • 1).IsFredholm := by
  rw [notMem_essentialSpectrum_iff_isUnit]
  exact CalkinAlgebra.isUnit_classStarMap_iff_isFredholm (T - z • 1)

/-- An off-essential-spectrum scalar resolvent is Fredholm. -/
theorem isFredholm_of_notMem_essentialSpectrum (T : H →L[ℂ] H) (z : ℂ)
    (hz : z ∉ T.essentialSpectrum) : (T - z • 1).IsFredholm :=
  (T.notMem_essentialSpectrum_iff_isFredholm z).mp hz

end ContinuousLinearMap
