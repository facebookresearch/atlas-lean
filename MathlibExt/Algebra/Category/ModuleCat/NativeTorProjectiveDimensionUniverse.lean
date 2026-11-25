/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorEulerAdditivityUniverse
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import MathlibExt.CategoryTheory.Monoidal.Tor.Additive

/-!
# Native Tor vanishing from actual projective bounds

A genuine projective resolution with zero terms above a bound has zero native
Tor there. Stock projective dimension also earns vanishing: successive actual
free covers and the native long exact window reduce the bound to a projective
coefficient. Canonical symmetry retains either original coefficient and all
ring and module universes. No Tor-vanishing certificate is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v
variable (R : Type u) [CommRing R]

/-- A zero term in a real projective resolution gives zero native Tor in that degree. -/
theorem nativeTor_isZero_of_projectiveResolution_term (M N : ModuleCat.{max u v} R)
    (P : ProjectiveResolution N) (q : ℕ) (hP : IsZero (P.complex.X q)) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  have hX : IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).X q) :=
    F.map_isZero hP
  have hH := (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology
  exact hH.of_iso (P.isoLeftDerivedObj F q)

/-- A real bounded projective resolution earns the complete native Tor vanishing range. -/
theorem nativeTor_isZero_of_projectiveResolution_bound (M N : ModuleCat.{max u v} R)
    (P : ProjectiveResolution N) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q)) (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  nativeTor_isZero_of_projectiveResolution_term R M N P q (hP q hq)

/-- A real bounded resolution of the other original coefficient gives the same native range. -/
theorem nativeTor_isZero_of_projectiveResolution_bound_coefficient
    (M N : ModuleCat.{max u v} R) (P : ProjectiveResolution M) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q)) (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveResolution_bound R N M P n hP q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- Stock projective dimension of the resolved coefficient earns native Tor vanishing. -/
theorem nativeTor_isZero_of_projectiveDimensionLE_resolved (M N : ModuleCat.{max u v} R)
    (d : ℕ) [HasProjectiveDimensionLE N d] (q : ℕ) (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  induction d generalizing N q with
  | zero =>
    have : Projective N := (projective_iff_hasProjectiveDimensionLE_zero N).mpr inferInstance
    cases q with
    | zero => omega
    | succ q => exact isZero_Tor_succ_of_projective (ModuleCat.{max u v} R) M N q
  | succ d ih =>
    cases q with
    | zero => omega
    | succ q =>
      let S := N.projectiveShortComplex
      have hS : S.ShortExact := N.shortExact_projectiveShortComplex
      have hP : Projective S.X₂ := by
        dsimp [S]
        infer_instance
      have hN : HasProjectiveDimensionLT S.X₃ (d + 2) := by
        change HasProjectiveDimensionLT N (d + 2)
        infer_instance
      have : HasProjectiveDimensionLE S.X₁ d :=
        (hS.hasProjectiveDimensionLT_X₃_iff d hP).mp hN
      have hK := ih S.X₁ q (by omega)
      let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
      obtain ⟨_, hExact⟩ := LeftDerivedDelta.LDexact_C F q S hS
      let : Projective S.X₂ := hP
      exact hExact.isZero_of_both_isZero
        (isZero_Tor_succ_of_projective (ModuleCat.{max u v} R) M S.X₂ q) hK

/-- Stock projective dimension of the other original coefficient gives the same native range. -/
theorem nativeTor_isZero_of_projectiveDimensionLE_coefficient (M N : ModuleCat.{max u v} R)
    (d : ℕ) [HasProjectiveDimensionLE M d] (q : ℕ) (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveDimensionLE_resolved R N M d q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- A strict stock dimension bound includes the genuine zero-object bound. -/
theorem nativeTor_isZero_of_projectiveDimensionLT_resolved (M N : ModuleCat.{max u v} R)
    (n : ℕ) [HasProjectiveDimensionLT N n] (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) := by
  cases n with
  | zero =>
    exact ((Tor (ModuleCat.{max u v} R) q).obj M).map_isZero
      (isZero_of_hasProjectiveDimensionLT_zero N)
  | succ d =>
    exact nativeTor_isZero_of_projectiveDimensionLE_resolved R M N d q (by omega)

/-- The strict stock dimension bound applies to either original coefficient. -/
theorem nativeTor_isZero_of_projectiveDimensionLT_coefficient (M N : ModuleCat.{max u v} R)
    (n : ℕ) [HasProjectiveDimensionLT M n] (q : ℕ) (hq : n ≤ q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  (nativeTor_isZero_of_projectiveDimensionLT_resolved R N M n q hq).of_iso
    (nativeTorSymmetry R M N q)

/-- A real projective bound on the fixed coefficient supplies the native Euler cutoff. -/
theorem rawNativeTorEulerSum_shortExactSecond_of_projectiveDimension
    (M : ModuleCat.{max u v} R) (d : ℕ) [HasProjectiveDimensionLE M d]
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤) :
    rawNativeTorEulerSum R M S.X₂ (d + 1) =
      rawNativeTorEulerSum R M S.X₁ (d + 1) + rawNativeTorEulerSum R M S.X₃ (d + 1) :=
  rawNativeTorEulerSum_shortExactSecond R M S hS (d + 1) h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveDimensionLE_coefficient R M S.X₃ d (d + 1) (by omega))

/-- A real bounded resolution of the fixed coefficient supplies the actual native Euler boundary. -/
theorem rawNativeTorEulerSum_shortExactSecond_of_projectiveResolution
    (M : ModuleCat.{max u v} R) (P : ProjectiveResolution M) (n : ℕ)
    (hP : ∀ q, n ≤ q → IsZero (P.complex.X q))
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤) :
    rawNativeTorEulerSum R M S.X₂ n =
      rawNativeTorEulerSum R M S.X₁ n + rawNativeTorEulerSum R M S.X₃ n :=
  rawNativeTorEulerSum_shortExactSecond R M S hS n h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveResolution_bound_coefficient R M S.X₃ P n hP n le_rfl)

/-- A real projective bound also supplies the first-variable native Euler cutoff. -/
theorem rawNativeTorEulerSum_shortExactFirst_of_projectiveDimension
    (N : ModuleCat.{max u v} R) (d : ℕ) [HasProjectiveDimensionLE N d]
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ q < d + 1,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₃).obj N) ≠ ⊤) :
    rawNativeTorEulerSum R S.X₂ N (d + 1) =
      rawNativeTorEulerSum R S.X₁ N (d + 1) + rawNativeTorEulerSum R S.X₃ N (d + 1) :=
  rawNativeTorEulerSum_shortExactFirst R N S hS (d + 1) h₁ h₂ h₃
    (nativeTor_isZero_of_projectiveDimensionLE_resolved R S.X₃ N d (d + 1) (by omega))

end ModuleCat.UniverseTensor
