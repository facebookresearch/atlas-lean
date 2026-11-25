/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExtTest.Algebra.Category.ModuleCat.NativeTorEulerAdditivityUniverse
public import MathlibExt.CategoryTheory.Abelian.Projective.PresentationComplex

/-!
# A bounded projective resolution of the mod-two module

The integral multiplication-by-two presentation gives a two-term projective
resolution of `ℤ/2`. It vanishes from degree two and gives native Tor
cutoffs and Euler additivity laws. The examples retain separate scalar
and coefficient universes.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor ZeroObject

namespace NativeTorBoundaryTests

open ModuleCat.UniverseTensor

/-- The two-term projective resolution from the integral presentation. -/
def actualPresentationResolution : ProjectiveResolution Q := by
  have : Projective integralShortComplex.X₁ := by
    change Projective Z
    infer_instance
  have : Projective integralShortComplex.X₂ := by
    change Projective Z
    infer_instance
  exact ProjectiveResolution.ofPresentation integralShortComplex integralShortComplex_shortExact

theorem actualPresentationResolution_bound (q : ℕ) (hq : 2 ≤ q) :
    IsZero (actualPresentationResolution.complex.X q) := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => omega
    | succ q =>
      change IsZero (0 : ModuleCat ℤ)
      exact isZero_zero (ModuleCat ℤ)

example (q : ℕ) (hq : 2 ≤ q) : IsZero (((Tor (ModuleCat ℤ) q).obj Q).obj Q) :=
  nativeTor_isZero_of_projectiveResolution_bound ℤ Q Q actualPresentationResolution 2
    actualPresentationResolution_bound q hq

example (q : ℕ) (hq : 2 ≤ q) : IsZero (((Tor (ModuleCat ℤ) q).obj Q).obj Z) :=
  nativeTor_isZero_of_projectiveResolution_bound_coefficient ℤ Q Z
    actualPresentationResolution 2 actualPresentationResolution_bound q hq

example : rawNativeTorEulerSum ℤ Q Z 2 =
    rawNativeTorEulerSum ℤ Q Z 2 + rawNativeTorEulerSum ℤ Q Q 2 :=
  rawNativeTorEulerSum_shortExactSecond_of_projectiveResolution ℤ Q actualPresentationResolution 2
    actualPresentationResolution_bound integralShortComplex integralShortComplex_shortExact
    (fun q _ => nativeTor_free_length_ne_top q) (fun q _ => nativeTor_free_length_ne_top q)
    nativeTor_quotient_length_ne_top

end NativeTorBoundaryTests

universe u v

open ModuleCat.UniverseTensor

example {R : Type u} [CommRing R] (M N : ModuleCat.{max u v} R)
    (d q : ℕ) [HasProjectiveDimensionLE N d] (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  nativeTor_isZero_of_projectiveDimensionLE_resolved R M N d q hq

example {R : Type u} [CommRing R] (M N : ModuleCat.{max u v} R)
    (d q : ℕ) [HasProjectiveDimensionLE M d] (hq : d < q) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) :=
  nativeTor_isZero_of_projectiveDimensionLE_coefficient R M N d q hq

example {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) (q : ℕ) :
    IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj (0 : ModuleCat.{max u v} R)) :=
  nativeTor_isZero_of_projectiveDimensionLT_resolved R M (0 : ModuleCat.{max u v} R)
    0 q (Nat.zero_le q)

example {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) :
    rawNativeTorEulerSum R M (0 : ModuleCat.{max u v} R) 0 = 0 :=
  rawNativeTorEulerSum_zero R M (0 : ModuleCat.{max u v} R)
