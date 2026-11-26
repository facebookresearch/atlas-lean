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

/-!
# Exact inverse image on small étale sites

Let f : X → Y be a morphism of schemes in universe u and c = max(u, w).
Inverse image f* sends AddCommGrpCat c-valued sheaves on the small étale
site of Y to those on X. It preserves finite limits and finite colimits
and therefore sends short exact sequences to short exact sequences.

The canonical geometric stalks on X jointly reflect sheaf isomorphisms.
The comparison (f*Q)_x ≅ Q_(f∘x) at these points yields finite-limit
preservation; the inverse-image/direct-image adjunction gives finite-colimit
preservation. The transported short-complex arrows are precisely f*(a)
and f*(b). The coefficient universe w is independent of u.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- For a scheme X in universe u and c = max(u, w), the stalk
functors at its canonical common-universe geometric points jointly reflect
isomorphisms of AddCommGrpCat c-valued étale sheaves.
A sheaf morphism whose maps on all these stalks are isomorphisms
is itself an isomorphism. -/
theorem smallEtaleCommonGeometricSheafFibers_jointlyReflectIsomorphisms (X : Scheme.{u}) :
    JointlyReflectIsomorphisms
      (fun (Φ : (smallEtaleCanonicalGeometricPointsCommon.{u, w} X).FullSubcategory) =>
        Φ.obj.sheafFiber (A := AddCommGrpCat.{max u w})) :=
  (smallEtaleCanonicalGeometricPointsCommon_conservative.{u, w} X).jointlyReflectIsomorphisms
    AddCommGrpCat.{max u w}

/-- Let f : X → Y be a morphism of schemes in universe u and
c = max(u, w). Write f* for inverse image on the small étale sites,
from AddCommGrpCat c-valued sheaves on Y to those on X.
The functor f* preserves finite limits. At a canonical geometric
point x of X, its stalk agrees with the stalk on Y at f ∘ x,
and these stalk comparisons identify the finite-limit maps. -/
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

/-- Let f : X → Y be a morphism of schemes in universe u and
c = max(u, w). Write f* for inverse image on the small étale sites,
from AddCommGrpCat c-valued sheaves on Y to those on X.
The functor f* preserves finite colimits, as the left adjoint
of the small étale direct-image functor f_*. -/
theorem smallEtaleInverseImage_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (smallEtaleInverseImage.{u, w} f) := by
  let : PreservesColimitsOfSize.{0, 0} (smallEtaleInverseImage.{u, w} f) :=
    (smallEtaleInverseImageAdjunction.{u, w} f).leftAdjoint_preservesColimits
  infer_instance

/-- Let f : X → Y be a morphism of schemes in universe u and
c = max(u, w). Write f* for inverse image on the small étale sites,
from AddCommGrpCat c-valued sheaves on Y to those on X.
For a short exact sequence S of coefficient sheaves on Y,
the short complex obtained by applying f* to its three objects and
two arrows is short exact on X. The additivity and exactness used here
belong to this inverse-image functor. -/
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

/-- Let f : X → Y be a morphism of schemes in universe u and
c = max(u, w). Write f* for inverse image on the small étale sites,
from AddCommGrpCat c-valued sheaves on Y to those on X.
Finite-limit and finite-colimit preservation hold together.
For every short complex S on Y, its transported arrows are
f*(S.a) and f*(S.b), and S short exact implies f*(S) short exact. -/
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
