/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Linear.ScalarDetection
public import MathlibExt.Algebra.Homology.LocallyFiniteIdempotentImages
public import MathlibExt.Algebra.Homology.Linear
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Nat.Basic

/-!
# Scalar detection on native idempotent-image homology

Actual native chain-idempotent images, their split/cross maps and finite
homology projector sums give scalar detection in semiring-linear abelian
categories. The module API requires regularity on actual image homology;
the actual annihilation equation is required for the kernel isomorphism.
No countable coproduct or AB5 certificate is an input. Rational-ring dyadic
units and original carrier universes are retained.

The field homology primitive specialization is provided separately by
`UniverseKunneth.PrimitiveScalarDetection`. Its outputs and assumptions
remain in the library; this general owner does not need field Künneth.
-/

@[expose] public section

noncomputable section

universe t u v w

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace HomologicalComplex

variable {R : Type t} [Semiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))

include hsum in
omit [Linear R C] in
/-- The actual finite sum of the original chain idempotents induces the
actual identity sum on native homology, without coproduct exactness. -/
theorem idempotentHomology_sum (n : ι) :
    (∑ j : Fin (N n + 1), homologyMap (e j.val) n) = 𝟙 (K.homology n) := by
  classical
  let s : K ⟶ K := ∑ j : Fin (N n + 1), e j.val
  have hs : s.f n = 𝟙 (K.X n) :=
    ((eval C c n).map_sum (fun j : Fin (N n + 1) => e j.val) Finset.univ).trans
      (hsum n)
  change (∑ j : Fin (N n + 1), (homologyFunctor C c n).map (e j.val)) = _
  rw [← Functor.map_sum]
  exact homologyMap_eq_id_of_component n s hs

include he in
omit [Linear R C] in
/-- The native inclusion and projection of an actual idempotent image
remain split after homology. -/
theorem imageHomology_split (n : ι) (j : ℕ) :
    homologyMap (image.ι (e j)) n ≫ homologyMap (factorThruImage (e j)) n =
      𝟙 ((image (e j)).homology n) := by
  rw [← homologyMap_comp, idempotentImage_split K e he j, homologyMap_id]

include he in
omit [Linear R C] in
/-- Orthogonal chain idempotents give zero cross maps between their
actual image homologies. -/
theorem imageHomology_cross (n : ι) (j k : ℕ) (hjk : j ≠ k) :
    homologyMap (image.ι (e j)) n ≫ homologyMap (factorThruImage (e k)) n = 0 := by
  rw [← homologyMap_comp, idempotentImage_cross K e he j k hjk, homologyMap_zero]

include hsupport in
omit [Linear R C] in
/-- A chain projector vanishing in a degree induces zero projection to
its actual image homology in that degree. -/
theorem imageHomology_support (n : ι) (j : ℕ) (hj : N n < j) :
    homologyMap (factorThruImage (e j)) n = 0 :=
  homologyMap_eq_zero_of_component n (factorThruImage (e j))
    (idempotentImage_factor_support K e N hsupport n j hj)

include hsum in
omit [Linear R C] in
/-- The original finite projector sum induces the identity sum of actual
image-homology projections followed by inclusions. -/
theorem imageHomology_sum (n : ι) :
    (∑ j : Fin (N n + 1), homologyMap (factorThruImage (e j.val)) n ≫
      homologyMap (image.ι (e j.val)) n) = 𝟙 (K.homology n) := by
  simp_rw [← homologyMap_comp, image.fac]
  exact idempotentHomology_sum K e N hsum n

variable {D : HomologicalComplex C c}
    (d : K ⟶ D) (m : D ⟶ K) (a : ℕ → R)
    (hweight : ∀ j, e j ≫ d ≫ m = a j • e j)

include hweight in
private theorem idempotentImage_inclusion_weight (j : ℕ) :
    image.ι (e j) ≫ d ≫ m = a j • image.ι (e j) := by
  apply (cancel_epi (factorThruImage (e j))).mp
  simpa only [Category.assoc, image.fac_assoc, image.fac, Linear.comp_smul] using hweight j

include hweight in
/-- The original chain operator law induces its scalar weight on the
actual image-homology inclusion. -/
theorem imageHomology_weight (n : ι) (j : ℕ) :
    homologyMap (image.ι (e j)) n ≫ homologyMap d n ≫ homologyMap m n =
      a j • homologyMap (image.ι (e j)) n := by
  let H := homologyFunctor C c n
  change H.map (image.ι (e j)) ≫ H.map d ≫ H.map m = a j • H.map (image.ι (e j))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_smul]
  exact congrArg H.map (idempotentImage_inclusion_weight K e d m a hweight j)

include he hsupport hsum hweight in
/-- The actual chain scalar equation and actual image splitting imply
the post-projection scalar equation on original native homology. -/
theorem idempotentHomology_operator_projection (n : ι) (j : ℕ) :
    homologyMap d n ≫ homologyMap m n ≫ homologyMap (factorThruImage (e j)) n =
      a j • homologyMap (factorThruImage (e j)) n :=
  finiteSplit_operator_projection
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j) j

include he hsupport hsum hweight in
/-- Regular scalar action on an actual image homology kills its projection
of every actual map annihilated by the original homology map. -/
theorem idempotentHomology_projection_zero_of_annihilated_map (n : ι) {Z : C}
    (f : Z ⟶ K.homology n) (hf : f ≫ homologyMap d n = 0) (j : ℕ)
    [Mono (a j • 𝟙 ((image (e j)).homology n))] :
    f ≫ homologyMap (factorThruImage (e j)) n = 0 :=
  finiteSplit_projection_zero_of_annihilated_map
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    f hf j

include he hsupport hsum hweight in
/-- Every map annihilated by the original homology map is fixed by the
distinguished actual chain-idempotent homology projector if the other
actual image-homology scalar actions are monic. -/
theorem idempotentHomology_projector_of_annihilated_map (n : ι) {Z : C}
    (f : Z ⟶ K.homology n) (hf : f ≫ homologyMap d n = 0) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → Mono (a k • 𝟙 ((image (e k)).homology n))) :
    f ≫ homologyMap (e j) n = f := by
  have h := finiteSplit_single_projector_of_annihilated_map
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    f hf j hregular
  simpa only [← homologyMap_comp, image.fac] using h

include he hsupport hsum hweight in
/-- The actual distinguished idempotent-image homology is the kernel of
the original homology map when that image is annihilated and all other
image-homology scalar actions are monic. This is a kernel in homology;
homology of the chain kernel is not used. -/
def idempotentHomologyScalarKernelIso (n : ι) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → Mono (a k • 𝟙 ((image (e k)).homology n)))
    (hzero : e j ≫ d = 0) : (image (e j)).homology n ≅ kernel (homologyMap d n) := by
  have hi : image.ι (e j) ≫ d = 0 := by
    apply (cancel_epi (factorThruImage (e j))).mp
    simpa only [Category.assoc, image.fac_assoc, image.fac, comp_zero] using hzero
  have hiH : homologyMap (image.ι (e j)) n ≫ homologyMap d n = 0 := by
    rw [← homologyMap_comp, hi, homologyMap_zero]
  exact finiteSplitScalarKernelIso
    (fun k => (image (e k)).homology n)
    (fun k => homologyMap (image.ι (e k)) n)
    (fun k => homologyMap (factorThruImage (e k)) n)
    (imageHomology_split K e he n) (imageHomology_cross K e he n)
    (N n) (imageHomology_support K e N hsupport n) (imageHomology_sum K e N hsum n)
    (homologyMap d n) (homologyMap m n) a
    (fun j _ => imageHomology_weight K e d m a hweight n j)
    j hregular hiH

end HomologicalComplex

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Native module scalar monicity is earned from actual module scalar
regularity. The carrier and the coefficient ring have independent worlds. -/
theorem mono_smul_id_of_isSMulRegular (M : ModuleCat.{v} R) (a : R)
    (ha : IsSMulRegular M a) : Mono (a • 𝟙 M) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (fun x : M => a • x)
  exact ha

end ModuleCat

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))
    {D : HomologicalComplex (ModuleCat.{v} R) c}
    (d : K ⟶ D) (m : D ⟶ K) (a : ℕ → R)
    (hweight : ∀ j, e j ≫ d ≫ m = a j • e j)

include he hsupport hsum hweight in
/-- The arbitrary-ring module specialization requires scalar regularity
on the actual image homologies. Ground-ring regularity alone is not an
input to this theorem. -/
def moduleCatIdempotentHomologyScalarKernelIso (n : ι) (j : ℕ)
    (hregular : ∀ k, k ≤ N n → k ≠ j → IsSMulRegular ((image (e k)).homology n) (a k))
    (hzero : e j ≫ d = 0) : (image (e j)).homology n ≅ kernel (homologyMap d n) :=
  idempotentHomologyScalarKernelIso K e he N hsupport hsum d m a hweight n j
    (fun k hk hj => ModuleCat.mono_smul_id_of_isSMulRegular _ _ (hregular k hk hj)) hzero

end HomologicalComplex

/-- The original dyadic detection scalar is nonzero in every
characteristic-zero ring outside weight one, including weight zero. -/
theorem two_pow_sub_two_ne_zero (R : Type u) [Ring R] [CharZero R]
    (j : ℕ) (hj : j ≠ 1) : (2 : R) ^ j - 2 ≠ 0 := by
  intro h
  have hcast : (((2 : ℕ) ^ j : ℕ) : R) = ((2 : ℕ) : R) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (sub_eq_zero.mp h)
  have hnat : (2 : ℕ) ^ j = 2 := Nat.cast_injective hcast
  have hpow : (2 : ℕ) ^ j = (2 : ℕ) ^ 1 := by simpa only [pow_one] using hnat
  exact hj (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hpow)

/-- Every dyadic detection scalar outside weight one is an actual unit
over an arbitrary rational algebra, without a nontriviality assumption. -/
theorem two_pow_sub_two_isUnit (R : Type u) [CommRing R] [Algebra ℚ R]
    (j : ℕ) (hj : j ≠ 1) : IsUnit ((2 : R) ^ j - 2) := by
  have hq : IsUnit ((2 : ℚ) ^ j - 2) :=
    isUnit_iff_ne_zero.mpr (two_pow_sub_two_ne_zero ℚ j hj)
  have htwo : (algebraMap ℚ R) (2 : ℚ) = (2 : R) :=
    map_ofNat (algebraMap ℚ R) 2
  simpa only [map_sub, map_pow, htwo] using hq.map (algebraMap ℚ R)

namespace HomologicalComplex

variable {R : Type u} [CommRing R] [Algebra ℚ R]
    {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (e : ℕ → (K ⟶ K))
    (he : ∀ i j : ℕ, e i ≫ e j = if i = j then e i else 0)
    (N : ι → ℕ)
    (hsupport : ∀ n j, N n < j → (e j).f n = 0)
    (hsum : ∀ n, (∑ j : Fin (N n + 1), (e j.val).f n) = 𝟙 (K.X n))
    {D : HomologicalComplex (ModuleCat.{v} R) c}
    (d : K ⟶ D) (m : D ⟶ K)
    (hweight : ∀ j, e j ≫ d ≫ m = ((2 : R) ^ j - 2) • e j)

include he hsupport hsum hweight in
/-- Over any rational ground algebra, actual dyadic scalar units give
the kernel of the original homology map from the actual weight-one image
homology. The original chain annihilation equation is still required. -/
def moduleCatIdempotentHomologyDyadicKernelIso (n : ι) (hzero : e 1 ≫ d = 0) :
    (image (e 1)).homology n ≅ kernel (homologyMap d n) :=
  moduleCatIdempotentHomologyScalarKernelIso K e he N hsupport hsum d m
    (fun j => (2 : R) ^ j - 2) hweight n 1
    (fun j _ hj => (two_pow_sub_two_isUnit R j hj).isSMulRegular _) hzero

end HomologicalComplex
