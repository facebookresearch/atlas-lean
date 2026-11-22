/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreeRelativeTensor

/-!
# The actual relative tensor of two free internal modules

The complete free-relative contraction identifies the tensor of the original
free modules with the original free module on the coefficient tensor. The
remaining comparison is the actual associator and coefficient/scalar braid.
Its forward module map is the original free extension of the second free
unit. All original coefficient maps are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v uD vD

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalCategory CategoryTheory.MonObj

private theorem reassociate_square
    {D : Type uD} [Category.{vD} D] {L L' T T' K K' : D}
    (e : K ≅ T) (e' : K' ≅ T') (d : L ⟶ T) (d' : L' ⟶ T')
    (l : L ⟶ L') (k : K ⟶ K') (t : T ⟶ T')
    (hd : l ≫ d' = d ≫ t) (he : k ≫ e'.hom = e.hom ≫ t) :
    l ≫ (d' ≫ e'.inv) = (d ≫ e.inv) ≫ k := by
  apply (cancel_mono e'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  simp only [Iso.inv_hom_id_assoc]
  exact hd

namespace CategoryTheory.Mod.FreePairRelativeTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C)

/-- The whole original free carrier is reassociated and moved through the
inverse coefficient/scalar braid to the actual tensor module. -/
def ambientIso (P Q : C) :
    ((Mod.free A.X).obj (P ⊗ Q)).X ≅
      (Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q)).X :=
  (α_ A.X P Q).symm ≪≫ ((β_ P A.X).symm ⊗ᵢ Iso.refl Q) ≪≫ (α_ P A.X Q)

/-- The forward carrier map retains both original associators and the
inverse scalar/coefficient braid. -/
theorem ambientIso_hom (P Q : C) :
    (ambientIso A P Q).hom =
      (α_ A.X P Q).inv ≫ ((β_ P A.X).inv ▷ Q) ≫ (α_ P A.X Q).hom := by
  change (α_ A.X P Q).inv ≫ ((β_ P A.X).inv ⊗ₘ 𝟙 Q) ≫ (α_ P A.X Q).hom = _
  rw [tensorHom_id]

/-- The inverse carrier map uses the original forward coefficient braid. -/
theorem ambientIso_inv (P Q : C) :
    (ambientIso A P Q).inv =
      (α_ P A.X Q).inv ≫ ((β_ P A.X).hom ▷ Q) ≫ (α_ A.X P Q).hom := by
  change ((α_ P A.X Q).inv ≫ ((β_ P A.X).hom ⊗ₘ 𝟙 Q)) ≫ (α_ A.X P Q).hom = _
  rw [tensorHom_id, Category.assoc]

/-- The original free-adjunction unit followed by the actual free action is the identity. -/
theorem originalFreeUnit_action (Q : C) :
    (A.X ◁ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        ((Mod.free A.X).obj Q).mod.smul = 𝟙 _ := by
  let F := (Mod.free A.X).obj Q
  have hId : (Mod.freeForgetAdjunction A.X).homEquiv Q F (𝟙 F) =
      Mod.FreeRelativeTensor.freeUnit A Q := by
    rw [Adjunction.homEquiv_unit]
    change Mod.FreeRelativeTensor.freeUnit A Q ≫ 𝟙 F.X = _
    exact Category.comp_id _
  have h := congrArg (fun f : F ⟶ F => f.hom)
    (((Mod.freeForgetAdjunction A.X).homEquiv Q F).symm_apply_apply (𝟙 F))
  rw [hId, Mod.freeForgetAdjunction_homEquiv_symm_apply_hom] at h
  change 𝟙 (A.X ⊗ Q) ≫ (A.X ◁ Mod.FreeRelativeTensor.freeUnit A Q) ≫
    ((Mod.free A.X).obj Q).mod.smul = 𝟙 (A.X ⊗ Q) at h
  simpa only [Category.id_comp] using h

/-- The original free extension of the second full free-adjunction unit. -/
def unitExtension (P Q : C) :
    (Mod.free A.X).obj (P ⊗ Q) ⟶
      Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q) :=
  ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q)
    (Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q))).symm
      (P ◁ Mod.FreeRelativeTensor.freeUnit A Q)

/-- Original free extension is exactly the whole inverse-braid carrier
reassociation, before any coequalizer is specialized. -/
theorem unitExtension_hom (P Q : C) :
    (unitExtension A P Q).hom = (ambientIso A P Q).hom := by
  rw [ambientIso_hom]
  unfold unitExtension
  rw [Mod.freeForgetAdjunction_homEquiv_symm_apply_hom]
  change 𝟙 (A.X ⊗ (P ⊗ Q)) ≫ (A.X ◁ (P ◁ Mod.FreeRelativeTensor.freeUnit A Q)) ≫
    (Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q)).mod.smul = _
  rw [Category.id_comp]
  rw [Mod.FreeRelativeTensor.tensorModule_smul]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp, originalFreeUnit_action]
  change (α_ A.X P Q).inv ≫ ((β_ P A.X).inv ▷ Q) ≫
      (α_ P A.X Q).hom ≫ (P ◁ 𝟙 (A.X ⊗ Q)) =
    (α_ A.X P Q).inv ≫ ((β_ P A.X).inv ▷ Q) ≫ (α_ P A.X Q).hom
  rw [whiskerLeft_id, Category.comp_id]

/-- Both full original module actions are preserved by the same carrier
reassociation and its actual inverse. -/
def ambientModuleIso (P Q : C) :
    (Mod.free A.X).obj (P ⊗ Q) ≅
      Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q) := by
  let M := (Mod.free A.X).obj (P ⊗ Q)
  let N := Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q)
  let _ : ModObj A.X M.X := M.mod
  let _ : ModObj A.X N.X := N.mod
  let e : M.X ≅ N.X := ambientIso A P Q
  have he : e.hom = (unitExtension A P Q).hom := (unitExtension_hom A P Q).symm
  have hLin : M.mod.smul ≫ e.hom = (A.X ◁ e.hom) ≫ N.mod.smul := by
    rw [he]
    exact (unitExtension A P Q).isModHom.smul_hom
  let _ : IsModHom A.X e.hom := ⟨hLin⟩
  exact
    { hom := Mod.Hom.mk' e.hom (IsModHom.smul_hom (A := A.X) (f := e.hom))
      inv := Mod.Hom.mk' e.inv (IsModHom.smul_hom (A := A.X) (f := e.inv))
      hom_inv_id := by
        apply Mod.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Mod.hom_ext
        exact e.inv_hom_id }

/-- The forward module comparison is the original free extension. -/
theorem ambientModuleIso_hom (P Q : C) :
    (ambientModuleIso A P Q).hom = unitExtension A P Q := by
  apply Mod.hom_ext
  exact (unitExtension_hom A P Q).symm

/-- Free extension recovers exactly the second original generator after
the whole free unit on the coefficient tensor. -/
theorem unitExtension_generator (P Q : C) :
    Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫ (unitExtension A P Q).hom =
      P ◁ Mod.FreeRelativeTensor.freeUnit A Q :=
  ((Mod.freeForgetAdjunction A.X).homEquiv_unit (P ⊗ Q)
    (Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q))
    (unitExtension A P Q)).symm.trans
      (Equiv.apply_symm_apply _ (P ◁ Mod.FreeRelativeTensor.freeUnit A Q))

section Tensor

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Both original coefficient arrows commute with free extension into
the actual inverse-braid tensor module. -/
theorem unitExtension_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Mod.free A.X).map (f ⊗ₘ g) ≫ unitExtension A P' Q' =
      unitExtension A P Q ≫
        Mod.FreeRelativeTensor.comparisonMap A ((Mod.free A.X).map f) ((Mod.free A.X).map g) := by
  apply ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q)
    (Mod.FreeRelativeTensor.tensorModule A P' ((Mod.free A.X).obj Q'))).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [unitExtension]
  have hL := Equiv.apply_symm_apply
    ((Mod.freeForgetAdjunction A.X).homEquiv (P' ⊗ Q')
      (Mod.FreeRelativeTensor.tensorModule A P' ((Mod.free A.X).obj Q')))
    (P' ◁ Mod.FreeRelativeTensor.freeUnit A Q')
  have hR := Equiv.apply_symm_apply
    ((Mod.freeForgetAdjunction A.X).homEquiv (P ⊗ Q)
      (Mod.FreeRelativeTensor.tensorModule A P ((Mod.free A.X).obj Q)))
    (P ◁ Mod.FreeRelativeTensor.freeUnit A Q)
  rw [hL, hR]
  change (f ⊗ₘ g) ≫ (P' ◁ Mod.FreeRelativeTensor.freeUnit A Q') =
    (P ◁ Mod.FreeRelativeTensor.freeUnit A Q) ≫
      (Mod.FreeRelativeTensor.comparisonMap A
        ((Mod.free A.X).map f) ((Mod.free A.X).map g)).hom
  rw [Mod.FreeRelativeTensor.comparisonMap_coefficient_hom]
  have hu : g ≫ Mod.FreeRelativeTensor.freeUnit A Q' =
      Mod.FreeRelativeTensor.freeUnit A Q ≫ ((Mod.free A.X).map g).hom :=
    (Mod.freeForgetAdjunction A.X).unit.naturality g
  rw [← id_tensorHom P' (Mod.FreeRelativeTensor.freeUnit A Q'),
    ← id_tensorHom P (Mod.FreeRelativeTensor.freeUnit A Q),
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp, hu]

/-- The module reassociation is natural in the two full original
coefficient maps, with the actual relative-tensor comparison maps. -/
theorem ambientModuleIso_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Mod.free A.X).map (f ⊗ₘ g) ≫ (ambientModuleIso A P' Q').hom =
      (ambientModuleIso A P Q).hom ≫
        Mod.FreeRelativeTensor.comparisonMap A ((Mod.free A.X).map f) ((Mod.free A.X).map g) := by
  rw [ambientModuleIso_hom, ambientModuleIso_hom]
  exact unitExtension_naturality A f g

/-- The actual balanced tensor of two original free modules is the
original free module on the entire coefficient tensor. -/
def iso (P Q : C) :
    ((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj ((Mod.free A.X).obj Q) ≅
      (Mod.free A.X).obj (P ⊗ Q) :=
  Mod.FreeRelativeTensor.balancedIso A P ((Mod.free A.X).obj Q) ≪≫
    (ambientModuleIso A P Q).symm

/-- The forward map retains the whole balancing projection, contraction
and original forward coefficient braid. -/
@[reassoc]
theorem iso_projection (P Q : C) :
    Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q) ≫
        (iso A P Q).hom.hom =
      Mod.FreeRelativeTensor.forwardRaw A P ((Mod.free A.X).obj Q) ≫
        (ambientIso A P Q).inv := by
  change Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q) ≫
    ((Mod.FreeRelativeTensor.forward A P ((Mod.free A.X).obj Q)).hom ≫
      (ambientModuleIso A P Q).inv.hom) = _
  rw [← Category.assoc, Mod.FreeRelativeTensor.forward_projection]
  rfl

/-- The inverse uses the full original free extension, first free unit
and literal relative-tensor projection. -/
theorem iso_inverse_unit (P Q : C) :
    (iso A P Q).inv.hom =
      (ambientIso A P Q).hom ≫
        (Mod.FreeRelativeTensor.freeUnit A P ▷ ((Mod.free A.X).obj Q).X) ≫
          Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q) := by
  change (ambientModuleIso A P Q).hom.hom ≫
    (Mod.FreeRelativeTensor.inverse A P ((Mod.free A.X).obj Q)).hom = _
  rw [Mod.FreeRelativeTensor.inverse_unit]
  rfl

/-- The complete pair generator is the tensor of both original free
units, followed by the actual balancing projection. -/
theorem iso_generator (P Q : C) :
    Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫ (iso A P Q).inv.hom =
      (Mod.FreeRelativeTensor.freeUnit A P ⊗ₘ Mod.FreeRelativeTensor.freeUnit A Q) ≫
        Mod.relativeTensorπ A ((Mod.free A.X).obj P) ((Mod.free A.X).obj Q) := by
  change Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) ≫
    ((ambientModuleIso A P Q).hom.hom ≫
      (Mod.FreeRelativeTensor.inverse A P ((Mod.free A.X).obj Q)).hom) = _
  rw [ambientModuleIso_hom, ← Category.assoc, unitExtension_generator,
    Mod.FreeRelativeTensor.inverse_unit]
  rw [tensorHom_def', Category.assoc]

/-- The actual pair collapse preserves both entire original coefficient
maps on the original relative-tensor arrows. -/
theorem iso_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    Mod.relativeTensorMap A ((Mod.free A.X).map f) ((Mod.free A.X).map g) ≫
        (iso A P' Q').hom =
      (iso A P Q).hom ≫ (Mod.free A.X).map (f ⊗ₘ g) := by
  exact reassociate_square (ambientModuleIso A P Q) (ambientModuleIso A P' Q')
    (Mod.FreeRelativeTensor.forward A P ((Mod.free A.X).obj Q))
    (Mod.FreeRelativeTensor.forward A P' ((Mod.free A.X).obj Q'))
    (Mod.relativeTensorMap A ((Mod.free A.X).map f) ((Mod.free A.X).map g))
    ((Mod.free A.X).map (f ⊗ₘ g))
    (Mod.FreeRelativeTensor.comparisonMap A ((Mod.free A.X).map f) ((Mod.free A.X).map g))
    (Mod.FreeRelativeTensor.comparison_naturality A
      ((Mod.free A.X).map f) ((Mod.free A.X).map g))
    (ambientModuleIso_naturality A f g)

/-- The original module monoidal structure used by the two-coefficient free comparison. -/
local instance pairModuleMonoidal : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A

/-- The actual free pair comparison as a natural isomorphism of the full
two coefficient functors, with the original relative tensor on modules. -/
def bifunctorIso :
    (Mod.free A.X).prod (Mod.free A.X) ⋙ tensor (Mod C A.X) ≅
      tensor C ⋙ Mod.free A.X :=
  NatIso.ofComponents (fun p => iso A p.1 p.2) (by
    intro p p' f
    exact iso_naturality A f.1 f.2)

end Tensor

end CategoryTheory.Mod.FreePairRelativeTensor
