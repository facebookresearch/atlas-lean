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

public import MathlibExt.Analysis.CStarAlgebra.Operator.CalkinOrthogonalSum
public import MathlibExt.Analysis.CStarAlgebra.Operator.FredholmCalkin
public import MathlibExt.Analysis.Normed.Operator.Compact.EssentialSpectrum
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Literal orthogonal Calkin units and essential-spectrum union

The existing block-diagonal Calkin map has unit detection by its two original
coordinates. Actual bounded lifts of an inverse have compact left/right
remainder; their two diagonal blocks are the actual inverses modulo compacts.
No inverse, spectrum model or result certificate is a supplied constructor
input. The resulting essential-spectrum union is needed to keep the original
Ext(X) sum within its exact source spectrum. The arguments retain independent
Hilbert universes and include zero/finite/infinite spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace CalkinAlgebra

universe uH uK
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Compactness of the proof-local first coordinate follows from the existing composition API. -/
private theorem compact_block11 (R : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)
    (hR : IsCompactOperator R) : IsCompactOperator (OrthogonalSum.block11 R) := by
  simpa only [OrthogonalSum.block11_eq, ContinuousLinearMap.coe_comp] using
    (hR.comp_clm (OrthogonalSum.inl (𝕜 := ℂ) H K).toContinuousLinearMap).clm_comp
      (WithLp.fstL 2 ℂ H K)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Compactness of the proof-local second coordinate follows from the existing composition API. -/
private theorem compact_block22 (R : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)
    (hR : IsCompactOperator R) : IsCompactOperator (OrthogonalSum.block22 R) := by
  simpa only [OrthogonalSum.block22_eq, ContinuousLinearMap.coe_comp] using
    (hR.comp_clm (OrthogonalSum.inr (𝕜 := ℂ) H K).toContinuousLinearMap).clm_comp
      (WithLp.sndL 2 ℂ H K)

/-- The actual product Calkin block map is injective on all original complete Hilbert carriers. -/
theorem blockDiagonalStarAlgHom_injective :
    Function.Injective (CalkinAlgebra.blockDiagonalStarAlgHom (H := H) (K := K)) := by
  intro x y hxy
  obtain ⟨T, hT⟩ := CalkinAlgebra.classStarMap_surjective (H := H) (x.1 - y.1)
  obtain ⟨S, hS⟩ := CalkinAlgebra.classStarMap_surjective (H := K) (x.2 - y.2)
  have hz : CalkinAlgebra.blockDiagonalStarAlgHom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hDiag : IsCompactOperator (OrthogonalSum.blockDiagonal T S) := by
    apply (CalkinAlgebra.classStarMap_eq_zero_iff _).mp
    rw [← CalkinAlgebra.blockDiagonalStarAlgHom_apply, hT, hS]
    exact hz
  have hTc := compact_block11 _ hDiag
  have hSc := compact_block22 _ hDiag
  rw [OrthogonalSum.block11_blockDiagonal] at hTc
  rw [OrthogonalSum.block22_blockDiagonal] at hSc
  have hTz := (CalkinAlgebra.classStarMap_eq_zero_iff _).mpr hTc
  have hSz := (CalkinAlgebra.classStarMap_eq_zero_iff _).mpr hSc
  rw [hT, sub_eq_zero] at hTz
  rw [hS, sub_eq_zero] at hSz
  exact Prod.ext hTz hSz

/-- The original block-diagonal Calkin class is a unit exactly when its two actual coordinates are
  units. -/
theorem isUnit_blockDiagonal_iff (x : CalkinAlgebra ℂ H) (y : CalkinAlgebra ℂ K) :
    IsUnit (blockDiagonalStarAlgHom (x, y)) ↔ IsUnit x ∧ IsUnit y := by
  constructor
  · intro h
    obtain ⟨T, rfl⟩ := classStarMap_surjective (H := H) x
    obtain ⟨S, rfl⟩ := classStarMap_surjective (H := K) y
    rw [blockDiagonalStarAlgHom_apply] at h
    obtain ⟨b, hDb, hbD⟩ := isUnit_iff_exists.mp h
    obtain ⟨R, hR⟩ := classStarMap_surjective (H := OrthogonalSum H K) b
    have hRD : IsCompactOperator (R * OrthogonalSum.blockDiagonal T S -
        (1 : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)) := by
      apply (classStarMap_eq_zero_iff _).mp
      rw [map_sub, map_mul, map_one, hR, hbD, sub_self]
    have hDR : IsCompactOperator (OrthogonalSum.blockDiagonal T S * R -
        (1 : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)) := by
      apply (classStarMap_eq_zero_iff _).mp
      rw [map_sub, map_mul, map_one, hR, hDb, sub_self]
    have hRT := compact_block11 _ hRD
    have hTR := compact_block11 _ hDR
    have hRS := compact_block22 _ hRD
    have hSR := compact_block22 _ hDR
    rw [map_sub, OrthogonalSum.block11_one] at hRT hTR
    rw [map_sub, OrthogonalSum.block22_one] at hRS hSR
    change IsCompactOperator
      (((OrthogonalSum.block11 (R.comp (OrthogonalSum.blockDiagonal T S)) : H →L[ℂ] H) -
        (1 : H →L[ℂ] H)) : H → H) at hRT
    change IsCompactOperator
      (((OrthogonalSum.block11 ((OrthogonalSum.blockDiagonal T S).comp R) : H →L[ℂ] H) -
        (1 : H →L[ℂ] H)) : H → H) at hTR
    change IsCompactOperator
      (((OrthogonalSum.block22 (R.comp (OrthogonalSum.blockDiagonal T S)) : K →L[ℂ] K) -
        (1 : K →L[ℂ] K)) : K → K) at hRS
    change IsCompactOperator
      (((OrthogonalSum.block22 ((OrthogonalSum.blockDiagonal T S).comp R) : K →L[ℂ] K) -
        (1 : K →L[ℂ] K)) : K → K) at hSR
    simp only [OrthogonalSum.block11_comp, OrthogonalSum.block11_blockDiagonal,
      OrthogonalSum.block21_blockDiagonal, ContinuousLinearMap.comp_zero, add_zero] at hRT
    simp only [OrthogonalSum.block11_comp, OrthogonalSum.block11_blockDiagonal,
      OrthogonalSum.block12_blockDiagonal, ContinuousLinearMap.zero_comp, add_zero] at hTR
    simp only [OrthogonalSum.block22_comp, OrthogonalSum.block22_blockDiagonal,
      OrthogonalSum.block12_blockDiagonal, ContinuousLinearMap.comp_zero, zero_add] at hRS
    simp only [OrthogonalSum.block22_comp, OrthogonalSum.block22_blockDiagonal,
      OrthogonalSum.block21_blockDiagonal, ContinuousLinearMap.zero_comp, zero_add] at hSR
    change IsCompactOperator (OrthogonalSum.block11 R * T - (1 : H →L[ℂ] H)) at hRT
    change IsCompactOperator (T * OrthogonalSum.block11 R - (1 : H →L[ℂ] H)) at hTR
    change IsCompactOperator (OrthogonalSum.block22 R * S - (1 : K →L[ℂ] K)) at hRS
    change IsCompactOperator (S * OrthogonalSum.block22 R - (1 : K →L[ℂ] K)) at hSR
    have hRT' := (classStarMap_eq_zero_iff (H := H)
      (OrthogonalSum.block11 R * T - 1)).mpr hRT
    have hTR' := (classStarMap_eq_zero_iff (H := H)
      (T * OrthogonalSum.block11 R - 1)).mpr hTR
    have hRS' := (classStarMap_eq_zero_iff (H := K)
      (OrthogonalSum.block22 R * S - 1)).mpr hRS
    have hSR' := (classStarMap_eq_zero_iff (H := K)
      (S * OrthogonalSum.block22 R - 1)).mpr hSR
    rw [map_sub, map_mul, map_one, sub_eq_zero] at hRT' hTR' hRS' hSR'
    exact ⟨isUnit_iff_exists.mpr ⟨classStarMap (OrthogonalSum.block11 R), hTR', hRT'⟩,
      isUnit_iff_exists.mpr ⟨classStarMap (OrthogonalSum.block22 R), hSR', hRS'⟩⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨a, hxa, hax⟩ := isUnit_iff_exists.mp hx
    obtain ⟨b, hyb, hby⟩ := isUnit_iff_exists.mp hy
    refine isUnit_iff_exists.mpr ⟨blockDiagonalStarAlgHom (a, b), ?_, ?_⟩
    · rw [← map_mul]
      change blockDiagonalStarAlgHom (x * a, y * b) = 1
      rw [hxa, hyb]
      exact map_one _
    · rw [← map_mul]
      change blockDiagonalStarAlgHom (a * x, b * y) = 1
      rw [hax, hby]
      exact map_one _

/-- The original scalar shift of a literal block diagonal is the literal diagonal of the two
  scalar shifts. -/
private theorem blockDiagonal_scalar_shift (T : H →L[ℂ] H) (S : K →L[ℂ] K) (z : ℂ) :
    OrthogonalSum.blockDiagonal T S - z • (1 : OrthogonalSum H K →L[ℂ] OrthogonalSum H K) =
      OrthogonalSum.blockDiagonal (T - z • (1 : H →L[ℂ] H)) (S - z • (1 : K →L[ℂ] K)) := by
  let d := OrthogonalSum.blockDiagonalStarAlgHom (𝕜 := ℂ) (H := H) (K := K)
  have h : d ((T, S) - z • (1 : (H →L[ℂ] H) × (K →L[ℂ] K))) = d (T, S) - z • 1 := by
    rw [map_sub, map_smul, map_one]
  exact h.symm

/-- The actual essential spectrum of the original orthogonal sum is the union of its two original
  spectra. -/
theorem essentialSpectrum_blockDiagonal (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    (OrthogonalSum.blockDiagonal T S).essentialSpectrum = T.essentialSpectrum ∪
      S.essentialSpectrum := by
  ext z
  apply not_iff_not.mp
  have hClass : classStarMap
      (OrthogonalSum.blockDiagonal T S - z • (1 : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)) =
      blockDiagonalStarAlgHom
        (classStarMap (T - z • (1 : H →L[ℂ] H)), classStarMap (S - z • (1 : K →L[ℂ] K))) := by
    rw [blockDiagonal_scalar_shift]
    exact (blockDiagonalStarAlgHom_apply _ _).symm
  calc
    z ∉ (OrthogonalSum.blockDiagonal T S).essentialSpectrum ↔
        IsUnit (classStarMap
          (OrthogonalSum.blockDiagonal T S - z • (1 : OrthogonalSum H K →L[ℂ] OrthogonalSum H K)))
            :=
      (OrthogonalSum.blockDiagonal T S).notMem_essentialSpectrum_iff_isUnit z
    _ ↔ IsUnit (blockDiagonalStarAlgHom
        (classStarMap (T - z • (1 : H →L[ℂ] H)), classStarMap (S - z • (1 : K →L[ℂ] K)))) := by
      rw [hClass]
    _ ↔ IsUnit (classStarMap (T - z • (1 : H →L[ℂ] H))) ∧
        IsUnit (classStarMap (S - z • (1 : K →L[ℂ] K))) := isUnit_blockDiagonal_iff _ _
    _ ↔ z ∉ T.essentialSpectrum ∧ z ∉ S.essentialSpectrum :=
      (T.notMem_essentialSpectrum_iff_isUnit z).symm.and
        (S.notMem_essentialSpectrum_iff_isUnit z).symm
    _ ↔ z ∉ T.essentialSpectrum ∪ S.essentialSpectrum := by
      simp only [Set.mem_union, not_or]

end CalkinAlgebra

end
