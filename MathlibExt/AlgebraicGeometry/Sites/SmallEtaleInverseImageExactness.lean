/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageStalks
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # Exactness of actual inverse image on the original small étale sites

The same canonical geometric stalk comparisons identify inverse image at
every original point with the stalk at its image. Their conservative family
reflects finite limits; the actual left adjunction preserves finite colimits.
Both original arrows are sent by this same constructed inverse-image functor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The canonical common-universe geometric stalks jointly reflect actual
sheaf isomorphisms, using the preceding original cover detector. -/
theorem smallEtaleCommonGeometricSheafFibers_jointlyReflectIsomorphisms (X : Scheme.{u}) :
    JointlyReflectIsomorphisms
      (fun (Φ : (smallEtaleCanonicalGeometricPointsCommon.{u, w} X).FullSubcategory) =>
        Φ.obj.sheafFiber (A := AddCommGrpCat.{max u w})) :=
  (smallEtaleCanonicalGeometricPointsCommon_conservative.{u, w} X).jointlyReflectIsomorphisms
    AddCommGrpCat.{max u w}

/-- The actual inverse image preserves finite limits, reflected through the
same original geometric stalks and their canonical comparison. -/
theorem smallEtaleInverseImage_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleInverseImage.{u, w} f) := by
  refine ⟨fun J _ _ => ⟨?_⟩⟩
  intro K
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  apply
    (smallEtaleCommonGeometricSheafFibers_jointlyReflectIsomorphisms.{u, w} X).jointlyReflectsLimit
  rintro ⟨Φ, hΦ⟩
  have hPres : PreservesFiniteLimits
      (smallEtaleInverseImage.{u, w} f ⋙ Φ.sheafFiber (A := AddCommGrpCat.{max u w})) := by
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ Φ).mp hΦ
    subst Φ
    exact smallEtaleInverseImageAtCommonGeometricPoint_preservesFiniteLimits.{u, w} f
      (smallEtaleCanonicalGeometricMorphism X x)
  let : PreservesFiniteLimits
      (smallEtaleInverseImage.{u, w} f ⋙ Φ.sheafFiber (A := AddCommGrpCat.{max u w})) := hPres
  exact isLimitOfPreserves
    (smallEtaleInverseImage.{u, w} f ⋙ Φ.sheafFiber (A := AddCommGrpCat.{max u w})) hc

/-- The same actual left adjunction preserves finite colimits. -/
theorem smallEtaleInverseImage_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallEtaleInverseImage.{u, w} f) := by
  let : PreservesColimitsOfSize.{0, 0} (smallEtaleInverseImage.{u, w} f) :=
    (smallEtaleInverseImageAdjunction.{u, w} f).leftAdjoint_preservesColimits
  infer_instance

/-- Every actual short exact sequence is sent to a short exact sequence by
this same inverse image, without a flatness or exactness premise. -/
theorem smallEtaleInverseImage_shortExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) :
    letI : (smallEtaleInverseImage.{u, w} f).Additive :=
      smallEtaleInverseImage_additive.{u, w} f
    (S.map (smallEtaleInverseImage.{u, w} f)).ShortExact := by
  let : PreservesFiniteLimits (smallEtaleInverseImage.{u, w} f) :=
    smallEtaleInverseImage_preservesFiniteLimits.{u, w} f
  let : PreservesFiniteColimits (smallEtaleInverseImage.{u, w} f) :=
    smallEtaleInverseImage_preservesFiniteColimits.{u, w} f
  exact hS.map_of_exact (smallEtaleInverseImage.{u, w} f)

/-- Exactness and literal transport of both original arrows belong to the
same constructed inverse image, for every scheme morphism and coefficient size. -/
theorem original_small_etale_inverse_image_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let L := smallEtaleInverseImage.{u, w} f
    letI : L.Additive := smallEtaleInverseImage_additive.{u, w} f
    PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧
    ∀ S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w}),
      (S.map L).f = L.map S.f ∧ (S.map L).g = L.map S.g ∧
        (S.ShortExact → (S.map L).ShortExact) := by
  dsimp only
  refine ⟨smallEtaleInverseImage_preservesFiniteLimits.{u, w} f,
    smallEtaleInverseImage_preservesFiniteColimits.{u, w} f, ?_⟩
  intro S
  exact ⟨rfl, rfl, fun hS => smallEtaleInverseImage_shortExact.{u, w} f S hS⟩

end AlgebraicGeometry.Scheme.DerivedSections
