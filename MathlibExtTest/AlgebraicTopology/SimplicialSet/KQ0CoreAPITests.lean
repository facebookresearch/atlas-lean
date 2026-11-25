/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible

/-!
# KQ0 core API consumer checks

Small generic checks that the KQ0 nerve homotopy and nerve contraction
APIs compose as downstream users need: functoriality of the nerve on
identities and composites, the natural-transformation homotopy
as a simplicial homotopy with its two endpoint equations, compatibility of
the cylinder map with pre- and postcomposition, and the two contraction maps from
categories with initial or terminal objects. Each check is a direct use of
one public production lemma.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.KQ0CoreAPITests

universe v u

open CategoryTheory Simplicial MonoidalCategory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {F G : C ⥤ D}

theorem nerveMap_id_client :
    CategoryTheory.nerveMap (𝟭 C) = 𝟙 (CategoryTheory.nerve C) :=
  CategoryTheory.nerveMap_id

theorem nerveMap_comp_client {E : Type u} [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    CategoryTheory.nerveMap F ≫ CategoryTheory.nerveMap G =
      CategoryTheory.nerveMap (F ⋙ G) :=
  CategoryTheory.nerveMap_comp F G

noncomputable def nerveHomotopy_isHomotopy_client (α : F ⟶ G) :
    SSet.Homotopy (CategoryTheory.nerveMap F) (CategoryTheory.nerveMap G) :=
  CategoryTheory.NatTrans.nerveHomotopy α

theorem nerveHomotopy_h₀_client (α : F ⟶ G) :
    SSet.ι₀ ≫ (CategoryTheory.NatTrans.nerveHomotopy α).h =
      CategoryTheory.nerveMap F :=
  (CategoryTheory.NatTrans.nerveHomotopy α).h₀

theorem nerveHomotopy_h₁_client (α : F ⟶ G) :
    SSet.ι₁ ≫ (CategoryTheory.NatTrans.nerveHomotopy α).h =
      CategoryTheory.nerveMap G :=
  (CategoryTheory.NatTrans.nerveHomotopy α).h₁

theorem nerveHomotopyMap_precomp_client {B : Type u} [Category.{v} B]
    (K : B ⥤ C) (α : F ⟶ G) :
    (CategoryTheory.nerveMap K ▷ (Δ[1] : SSet.{max u v})) ≫
      CategoryTheory.NatTrans.nerveHomotopyMap α =
      CategoryTheory.NatTrans.nerveHomotopyMap
        (CategoryTheory.Functor.whiskerLeft K α) :=
  CategoryTheory.NatTrans.nerveHomotopyMap_precomp K α

theorem nerveHomotopyMap_postcomp_client {E : Type u} [Category.{v} E]
    (α : F ⟶ G) (L : D ⥤ E) :
    CategoryTheory.NatTrans.nerveHomotopyMap α ≫ CategoryTheory.nerveMap L =
      CategoryTheory.NatTrans.nerveHomotopyMap
        (CategoryTheory.Functor.whiskerRight α L) :=
  CategoryTheory.NatTrans.nerveHomotopyMap_postcomp α L

noncomputable def nerve_initial_contraction_client {X : C}
    (hX : CategoryTheory.Limits.IsInitial X) :
    SimplicialObject.Homotopy (NerveContractible.constNerveMap (C := C) X)
      (𝟙 (CategoryTheory.nerve C : SSet.{max u v})) :=
  NerveContractible.homotopyOfIsInitial hX

noncomputable def nerve_terminal_contraction_client {Y : C}
    (hY : CategoryTheory.Limits.IsTerminal Y) :
    SimplicialObject.Homotopy (𝟙 (CategoryTheory.nerve C : SSet.{max u v}))
      (NerveContractible.constNerveMap (C := C) Y) :=
  NerveContractible.homotopyOfIsTerminal hY

end MathlibExtTest.AlgebraicTopology.SimplicialSet.KQ0CoreAPITests

end
