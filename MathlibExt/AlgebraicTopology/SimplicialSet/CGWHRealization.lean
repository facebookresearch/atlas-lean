/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.Realization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Simplicial-set realization and singular adjunction in CGWH

The canonical realization of a simplicial set is bundled as a CGWH space.
After forgetting to topological spaces it is literally the existing
realization, so the realization--singular adjunction restricts along the
fully faithful CGWH inclusion.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace SSet

/-- Geometric realization of simplicial sets, bundled natively in CGWH. -/
noncomputable def toCGWH : SSet.{v} ⥤ CGWH.{u, v} where
  obj K := by
    let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj K) :=
      SSet.uCompactlyGeneratedSpace_realization K
    let _ : UWeakHausdorffSpace.{u} (SSet.toTop.obj K) :=
      SSet.uWeakHausdorffSpace_realization K
    exact CGWH.of (SSet.toTop.obj K)
  map f := ConcreteCategory.ofHom (SSet.toTop.map f).hom
  map_id K := by
    apply CGWH.fullyFaithfulCgwhToTop.map_injective
    change SSet.toTop.map (𝟙 K) = 𝟙 (SSet.toTop.obj K)
    exact SSet.toTop.map_id K
  map_comp f g := by
    apply CGWH.fullyFaithfulCgwhToTop.map_injective
    change SSet.toTop.map (f ≫ g) =
      SSet.toTop.map f ≫ SSet.toTop.map g
    exact SSet.toTop.map_comp f g

/-- Forgetting native realization to TopCat gives the original realization,
with identity components. -/
noncomputable def realizationToTopIso :
    SSet.toCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v} ≅ SSet.toTop.{v} :=
  NatIso.ofComponents (fun K => Iso.refl (SSet.toTop.obj K))
    (fun _ => by rfl)

/-- The direct realization--singular adjunction between simplicial sets and
CGWH spaces. -/
noncomputable def sSetCGWHAdj :
    SSet.toCGWH.{u, v} ⊣
      CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v} :=
  sSetTopAdj.restrictFullyFaithful
    (Functor.FullyFaithful.id SSet.{v})
    CGWH.fullyFaithfulCgwhToTop
    ((Functor.leftUnitor SSet.toTop) ≪≫
      SSet.realizationToTopIso.{u, v}.symm)
    ((Functor.rightUnitor
      (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v})).symm)

end SSet

namespace CGWH

set_option backward.isDefEq.respectTransparency false in
/-- The exact general native realization is compared to its original finite realization. -/
@[no_expose]
def finiteRealizationIso (K : SSet.{v}) [K.Finite] :
    SSet.toCGWH.{u, v}.obj K ≅ (SSet.toCGWHOfFinite K : CGWH.{u, v}) :=
  CGWH.fullyFaithfulCgwhToTop.preimageIso (Iso.refl (SSet.toTop.obj K))

set_option backward.isDefEq.respectTransparency false in
/-- The complete general-to-finite comparison has the original identity underlying map. -/
theorem finiteRealizationIso_hom_top (K : SSet.{v}) [K.Finite] :
    CGWH.cgwhToTop.{u, v}.map (finiteRealizationIso.{u, v} K).hom =
      𝟙 (SSet.toTop.obj K) :=
  CGWH.fullyFaithfulCgwhToTop.map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- The complete finite-to-general comparison has the original identity underlying map. -/
theorem finiteRealizationIso_inv_top (K : SSet.{v}) [K.Finite] :
    CGWH.cgwhToTop.{u, v}.map (finiteRealizationIso.{u, v} K).inv =
      𝟙 (SSet.toTop.obj K) :=
  CGWH.fullyFaithfulCgwhToTop.map_preimage _

end CGWH
