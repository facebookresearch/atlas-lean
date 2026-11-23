/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom
import MathlibExt.CategoryTheory.Monoidal.Mod.AmbientTensor

/-!
# The actual relative tensor with a free internal module

The ambient tensor `P ⊗ N.X` has the module action transported by the
inverse braid from the right tensor `N.X ⊗ P`. This is the convention
determined by the existing relative tensor's braided right action. The
free relative tensor will be compared with that module by its actual
balancing coequalizer and the original free-adjunction unit.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory.Mod.FreeRelativeTensor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C)

private abbrev rightTensorAction (P : C) (N : Mod C A.X) :
    A.X ⊗ (N.X ⊗ P) ⟶ N.X ⊗ P :=
  Mod.AmbientTensor.rightAction A.X P N

/-- The original right tensor uses the shared general monoid action. -/
noncomputable abbrev rightTensorModule (P : C) (N : Mod C A.X) : Mod C A.X :=
  Mod.AmbientTensor.rightModule A.X P N

/-- The original commutative API retains the shared inverse-braid ambient left tensor. -/
noncomputable abbrev tensorModule (P : C) (N : Mod C A.X) : Mod C A.X :=
  Mod.AmbientTensor.tensorModule A.X P N

/-- The carrier is the whole ambient tensor, before any specialization. -/
theorem tensorModule_carrier (P : C) (N : Mod C A.X) :
    (tensorModule A P N).X = P ⊗ N.X := rfl

/-- The complete target action retains the actual inverse scalar braid,
all associators and the original target module action. -/
theorem tensorModule_smul (P : C) (N : Mod C A.X) :
    (tensorModule A P N).mod.smul =
      (α_ A.X P N.X).inv ≫ ((β_ P A.X).inv ▷ N.X) ≫
        (α_ P A.X N.X).hom ≫ (P ◁ N.mod.smul) :=
  Mod.AmbientTensor.module_smul A.X P N

/-- The source generator is the existing complete free-adjunction unit. -/
abbrev freeUnit (P : C) : P ⟶ ((Mod.free A.X).obj P).X :=
  (Mod.freeForgetAdjunction A.X).unit.app P

/-- The same original free unit retains its actual scalar insertion. -/
theorem freeUnit_eq (P : C) :
    freeUnit A P = (λ_ P).inv ≫ (η[A.X] ▷ P) := by
  have h := Mod.freeForgetAdjunction_unit_app A.X P
  change freeUnit A P = (λ_ P).inv ≫ (η[A.X] ▷ P) ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

private theorem freeUnit_action (P : C) :
    (A.X ◁ freeUnit A P) ≫ ((Mod.free A.X).obj P).mod.smul = 𝟙 _ := by
  let F := (Mod.free A.X).obj P
  have hId : (Mod.freeForgetAdjunction A.X).homEquiv P F (𝟙 F) = freeUnit A P := by
    rw [Adjunction.homEquiv_unit]
    change freeUnit A P ≫ 𝟙 F.X = freeUnit A P
    exact Category.comp_id _
  have h := congrArg (fun f : F ⟶ F => f.hom)
    (((Mod.freeForgetAdjunction A.X).homEquiv P F).symm_apply_apply (𝟙 F))
  rw [hId, Mod.freeForgetAdjunction_homEquiv_symm_apply_hom] at h
  change 𝟙 (A.X ⊗ P) ≫ (A.X ◁ freeUnit A P) ≫
    ((Mod.free A.X).obj P).mod.smul = 𝟙 (A.X ⊗ P) at h
  simpa only [Category.id_comp] using h

/-- The contraction of the complete free carrier moves the scalar through
the coefficient by the original inverse braid and applies the target action. -/
def forwardRaw (P : C) (N : Mod C A.X) :
    ((Mod.free A.X).obj P).X ⊗ N.X ⟶ P ⊗ N.X :=
  ((β_ P A.X).inv ▷ N.X) ≫ (α_ P A.X N.X).hom ≫ (P ◁ N.mod.smul)

private theorem forwardRaw_eq_extension (P : C) (N : Mod C A.X) :
    forwardRaw A P N = Mod.FreeInternalHom.parameterExtension A P N.X
      (tensorModule A P N) (𝟙 (P ⊗ N.X)) := by
  unfold Mod.FreeInternalHom.parameterExtension
  rw [tensorModule_smul]
  simp only [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
  rfl

/-- The full contraction is linear for the original left action on the
free module and the actual inverse-braid action on the target tensor. -/
theorem forward_linear (P : C) (N : Mod C A.X) :
    (α_ A.X ((Mod.free A.X).obj P).X N.X).inv ≫
        (((Mod.free A.X).obj P).mod.smul ▷ N.X) ≫ forwardRaw A P N =
      (A.X ◁ forwardRaw A P N) ≫ (tensorModule A P N).mod.smul := by
  rw [forwardRaw_eq_extension]
  have h := Mod.FreeInternalHom.parameterExtension_linear A P N.X
    (tensorModule A P N) (𝟙 (P ⊗ N.X))
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun t => (α_ A.X ((Mod.free A.X).obj P).X N.X).inv ≫ t) h

/-- Inserting the original whole free-adjunction unit recovers the entire
ambient coefficient tensor. -/
theorem forward_unit (P : C) (N : Mod C A.X) :
    (freeUnit A P ▷ N.X) ≫ forwardRaw A P N = 𝟙 (P ⊗ N.X) := by
  rw [forwardRaw_eq_extension]
  exact Mod.FreeInternalHom.parameterExtension_generator A P N.X
    (tensorModule A P N) (𝟙 (P ⊗ N.X))

private theorem freeRightAction_transport (P : C) :
    Mod.braidedRightAction A ((Mod.free A.X).obj P) ≫ (β_ P A.X).inv =
      ((β_ P A.X).inv ▷ A.X) ≫ (α_ P A.X A.X).hom ≫ (P ◁ μ[A.X]) := by
  unfold Mod.braidedRightAction
  change ((β_ (A.X ⊗ P) A.X).hom ≫
    ((α_ A.X A.X P).inv ≫ (μ[A.X] ▷ P))) ≫ (β_ P A.X).inv = _
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]
  rw [braiding_inv_naturality_left (X := A.X ⊗ A.X) μ[A.X] P,
    braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id_assoc]

private theorem tensorContraction_balanced (P M T : C)
    (r : M ⊗ A.X ⟶ M) (c : M ⟶ P ⊗ A.X) (s : A.X ⊗ T ⟶ T)
    (hc : r ≫ c = (c ▷ A.X) ≫ (α_ P A.X A.X).hom ≫ (P ◁ μ[A.X]))
    (hs : (μ[A.X] ▷ T) ≫ s = (α_ A.X A.X T).hom ≫ (A.X ◁ s) ≫ s) :
    (r ▷ T) ≫ (c ▷ T) ≫ (α_ P A.X T).hom ≫ (P ◁ s) =
      (α_ M A.X T).hom ≫ (M ◁ s) ≫ (c ▷ T) ≫
        (α_ P A.X T).hom ≫ (P ◁ s) := by
  have hA : ((α_ P A.X A.X).hom ▷ T) ≫ (α_ P (A.X ⊗ A.X) T).hom ≫
      (P ◁ (α_ A.X A.X T).hom) =
      (α_ (P ⊗ A.X) A.X T).hom ≫ (α_ P A.X (A.X ⊗ T)).hom := by monoidal
  have hEx : (M ◁ s) ≫ (c ▷ T) =
      (c ▷ (A.X ⊗ T)) ≫ ((P ⊗ A.X) ◁ s) := whisker_exchange c s
  calc
    _ = ((c ▷ A.X) ▷ T) ≫ ((α_ P A.X A.X).hom ▷ T) ≫
        ((P ◁ μ[A.X]) ▷ T) ≫ (α_ P A.X T).hom ≫ (P ◁ s) := by
      rw [← comp_whiskerRight_assoc, hc]
      simp only [comp_whiskerRight, Category.assoc]
    _ = ((c ▷ A.X) ▷ T) ≫ ((α_ P A.X A.X).hom ▷ T) ≫
        (α_ P (A.X ⊗ A.X) T).hom ≫ (P ◁ (μ[A.X] ▷ T)) ≫ (P ◁ s) := by
      rw [associator_naturality_middle_assoc]
    _ = ((c ▷ A.X) ▷ T) ≫ ((α_ P A.X A.X).hom ▷ T) ≫
        (α_ P (A.X ⊗ A.X) T).hom ≫ (P ◁ (α_ A.X A.X T).hom) ≫
        (P ◁ (A.X ◁ s)) ≫ (P ◁ s) := by
      rw [← whiskerLeft_comp, hs]
      simp only [whiskerLeft_comp]
    _ = ((c ▷ A.X) ▷ T) ≫ (α_ (P ⊗ A.X) A.X T).hom ≫
        (α_ P A.X (A.X ⊗ T)).hom ≫ (P ◁ (A.X ◁ s)) ≫ (P ◁ s) := by
      simpa only [Category.assoc] using congrArg
        (fun t => ((c ▷ A.X) ▷ T) ≫ t ≫ (P ◁ (A.X ◁ s)) ≫ (P ◁ s)) hA
    _ = _ := by
      rw [reassoc_of% hEx, ← associator_naturality_left_assoc,
        associator_naturality_right_assoc]

/-- The complete contraction equalizes the two original relative-tensor
arrows, with the full free right action and the original target left action. -/
theorem forward_balanced (P : C) (N : Mod C A.X) :
    (Mod.braidedRightAction A ((Mod.free A.X).obj P) ▷ N.X) ≫ forwardRaw A P N =
      (α_ ((Mod.free A.X).obj P).X A.X N.X).hom ≫
        (((Mod.free A.X).obj P).X ◁ N.mod.smul) ≫ forwardRaw A P N := by
  exact tensorContraction_balanced A P
    ((Mod.free A.X).obj P).X N.X
    (Mod.braidedRightAction A ((Mod.free A.X).obj P)) (β_ P A.X).inv N.mod.smul
    (freeRightAction_transport A P) (ModObj.mul_smul_self A.X N.X)

private theorem freeUnit_rightAction (P : C) :
    (freeUnit A P ▷ A.X) ≫ Mod.braidedRightAction A ((Mod.free A.X).obj P) =
      (β_ P A.X).hom := by
  unfold Mod.braidedRightAction
  rw [← Category.assoc, braiding_naturality_left, Category.assoc,
    freeUnit_action]
  change (β_ P A.X).hom ≫ 𝟙 (A.X ⊗ P) = (β_ P A.X).hom
  exact Category.comp_id _

private theorem tensorContraction_projection (P M T Z : C)
    (r : M ⊗ A.X ⟶ M) (c : M ⟶ P ⊗ A.X) (s : A.X ⊗ T ⟶ T)
    (e : P ⟶ M) (π : M ⊗ T ⟶ Z)
    (he : c ≫ (e ▷ A.X) ≫ r = 𝟙 M)
    (hπ : (r ▷ T) ≫ π = (α_ M A.X T).hom ≫ (M ◁ s) ≫ π) :
    (c ▷ T) ≫ (α_ P A.X T).hom ≫ (P ◁ s) ≫ (e ▷ T) ≫ π = π := by
  have hEx : (P ◁ s) ≫ (e ▷ T) =
      (e ▷ (A.X ⊗ T)) ≫ (M ◁ s) := whisker_exchange e s
  calc
    _ = (c ▷ T) ≫ ((e ▷ A.X) ▷ T) ≫
        (α_ M A.X T).hom ≫ (M ◁ s) ≫ π := by
      rw [reassoc_of% hEx, ← associator_naturality_left_assoc]
    _ = (c ▷ T) ≫ ((e ▷ A.X) ▷ T) ≫ (r ▷ T) ≫ π := by rw [← hπ]
    _ = ((c ≫ (e ▷ A.X) ≫ r) ▷ T) ≫ π := by
      simp only [comp_whiskerRight, Category.assoc]
    _ = π := by rw [he, id_whiskerRight, Category.id_comp]

section Tensor

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The actual full contraction descended through the existing relative
coequalizer, with both its original balancing and left action equations. -/
def forward (P : C) (N : Mod C A.X) :
    ((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N ⟶ tensorModule A P N :=
  Mod.relativeTensorDesc A ((Mod.free A.X).obj P) N (tensorModule A P N)
    (forwardRaw A P N) (forward_balanced A P N) (forward_linear A P N)

/-- The quotient map followed by the comparison is the literal whole
free-carrier contraction. -/
@[reassoc]
theorem forward_projection (P : C) (N : Mod C A.X) :
    Mod.relativeTensorπ A ((Mod.free A.X).obj P) N ≫ (forward A P N).hom =
      forwardRaw A P N :=
  Mod.relativeTensorDesc_π A ((Mod.free A.X).obj P) N (tensorModule A P N)
    (forwardRaw A P N) (forward_balanced A P N) (forward_linear A P N)

/-- The inverse on the whole ambient carrier inserts the actual original
free-adjunction unit and then the original balancing projection. -/
def inverseRaw (P : C) (N : Mod C A.X) :
    P ⊗ N.X ⟶ (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X :=
  (freeUnit A P ▷ N.X) ≫ Mod.relativeTensorπ A ((Mod.free A.X).obj P) N

private theorem inverseRaw_forward (P : C) (N : Mod C A.X) :
    inverseRaw A P N ≫ (forward A P N).hom = 𝟙 (P ⊗ N.X) := by
  unfold inverseRaw
  rw [Category.assoc, forward_projection, forward_unit]

private theorem forward_inverseRaw (P : C) (N : Mod C A.X) :
    (forward A P N).hom ≫ inverseRaw A P N =
      𝟙 (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X := by
  let _ := Mod.relativeTensorπ_epi A ((Mod.free A.X).obj P) N
  apply (cancel_epi (Mod.relativeTensorπ A ((Mod.free A.X).obj P) N)).1
  rw [← Category.assoc, forward_projection, Category.comp_id]
  have he : (β_ P A.X).inv ≫ (freeUnit A P ▷ A.X) ≫
      Mod.braidedRightAction A ((Mod.free A.X).obj P) =
      𝟙 ((Mod.free A.X).obj P).X := by
    rw [freeUnit_rightAction]
    change (β_ P A.X).inv ≫ (β_ P A.X).hom = 𝟙 (A.X ⊗ P)
    exact Iso.inv_hom_id _
  unfold forwardRaw inverseRaw
  change (((β_ P A.X).inv ▷ N.X) ≫ (α_ P A.X N.X).hom ≫ (P ◁ N.mod.smul)) ≫
    ((freeUnit A P ▷ N.X) ≫ Mod.relativeTensorπ A ((Mod.free A.X).obj P) N) =
      Mod.relativeTensorπ A ((Mod.free A.X).obj P) N
  simp only [Category.assoc]
  exact tensorContraction_projection A P (A.X ⊗ P) N.X
    (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X
    (Mod.braidedRightAction A ((Mod.free A.X).obj P)) (β_ P A.X).inv N.mod.smul
    (freeUnit A P) (Mod.relativeTensorπ A ((Mod.free A.X).obj P) N) he
    (Mod.relativeTensorπ_balance_rightAction A ((Mod.free A.X).obj P) N)

/-- The actual free-relative coequalizer and the whole ambient tensor are
isomorphic by the original contraction and free-unit insertion. -/
def underlyingIso (P : C) (N : Mod C A.X) :
    (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).X ≅ P ⊗ N.X where
  hom := (forward A P N).hom
  inv := inverseRaw A P N
  hom_inv_id := forward_inverseRaw A P N
  inv_hom_id := inverseRaw_forward A P N

/-- The original free-unit insertion is a module map, as the inverse of
the linear whole coequalizer contraction. -/
def inverse (P : C) (N : Mod C A.X) :
    tensorModule A P N ⟶ ((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N := by
  let M := ((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N
  let T := tensorModule A P N
  let _ : ModObj A.X M.X := M.mod
  let _ : ModObj A.X T.X := T.mod
  let e : M.X ≅ T.X := underlyingIso A P N
  let _ : IsModHom A.X e.hom := (forward A P N).isModHom
  exact Mod.Hom.mk' e.inv (IsModHom.smul_hom (A := A.X) (f := e.inv))

/-- The inverse module map retains its literal original free-unit and
coequalizer projection on the full ambient carrier. -/
@[reassoc]
theorem inverse_unit (P : C) (N : Mod C A.X) :
    (inverse A P N).hom =
      (freeUnit A P ▷ N.X) ≫ Mod.relativeTensorπ A ((Mod.free A.X).obj P) N := rfl

/-- Both complete scalar actions are respected by original unit insertion. -/
theorem inverse_linear (P : C) (N : Mod C A.X) :
    (tensorModule A P N).mod.smul ≫ (inverse A P N).hom =
      (A.X ◁ (inverse A P N).hom) ≫
        (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N).mod.smul :=
  (inverse A P N).isModHom.smul_hom

/-- Contraction followed by original unit insertion is the identity on
the actual relative-tensor module. -/
@[simp]
theorem forward_inverse (P : C) (N : Mod C A.X) :
    forward A P N ≫ inverse A P N =
      𝟙 (((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N) := by
  apply Mod.hom_ext
  change (forward A P N).hom ≫ inverseRaw A P N = _
  exact forward_inverseRaw A P N

/-- Original unit insertion followed by contraction is the identity on
the whole ambient tensor module. -/
@[simp]
theorem inverse_forward (P : C) (N : Mod C A.X) :
    inverse A P N ≫ forward A P N = 𝟙 (tensorModule A P N) := by
  apply Mod.hom_ext
  change inverseRaw A P N ≫ (forward A P N).hom = _
  exact inverseRaw_forward A P N

/-- The actual free-relative collapse is an isomorphism of the original
modules, with the full inverse-braid target action. -/
def balancedIso (P : C) (N : Mod C A.X) :
    ((Mod.relativeTensor A).obj ((Mod.free A.X).obj P)).obj N ≅ tensorModule A P N where
  hom := forward A P N
  inv := inverse A P N
  hom_inv_id := forward_inverse A P N
  inv_hom_id := inverse_forward A P N

/-- An arbitrary original free-module source map and an arbitrary target
module map induce their actual map between the compared tensor modules. -/
def comparisonMap {P Q : C}
    (h : (Mod.free A.X).obj P ⟶ (Mod.free A.X).obj Q)
    {N N' : Mod C A.X} (g : N ⟶ N') : tensorModule A P N ⟶ tensorModule A Q N' :=
  inverse A P N ≫ Mod.relativeTensorMap A h g ≫ forward A Q N'

/-- The whole comparison map is the original free-unit adjunct, followed
by the complete source/target tensor map and the actual contraction. -/
theorem comparisonMap_hom {P Q : C}
    (h : (Mod.free A.X).obj P ⟶ (Mod.free A.X).obj Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    (comparisonMap A h g).hom =
      (freeUnit A P ▷ N.X) ≫ (h.hom ⊗ₘ g.hom) ≫ forwardRaw A Q N' := by
  have hπ := Mod.relativeTensorMap_π A h g
  change (inverse A P N).hom ≫
    (Mod.relativeTensorMap A h g).hom ≫ (forward A Q N').hom = _
  rw [inverse_unit]
  simp only [Category.assoc]
  have hPre := congrArg
    (fun t => (freeUnit A P ▷ N.X) ≫ t ≫ (forward A Q N').hom) hπ
  have hOut := congrArg
    (fun t => (freeUnit A P ▷ N.X) ≫ (h.hom ⊗ₘ g.hom) ≫ t)
    (forward_projection A Q N')
  simp only [Category.assoc] at hPre hOut
  exact hPre.trans hOut

/-- The actual relative-tensor map agrees with the complete comparison
on every free-source arrow and every original target-module arrow. -/
theorem comparison_naturality {P Q : C}
    (h : (Mod.free A.X).obj P ⟶ (Mod.free A.X).obj Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    Mod.relativeTensorMap A h g ≫ forward A Q N' =
      forward A P N ≫ comparisonMap A h g := by
  rw [comparisonMap, ← Category.assoc, forward_inverse, Category.id_comp]

omit [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
private theorem freeUnit_tensor_coefficient {P Q : C} (f : P ⟶ Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    (freeUnit A P ▷ N.X) ≫ (((Mod.free A.X).map f).hom ⊗ₘ g.hom) =
      (f ⊗ₘ g.hom) ≫ (freeUnit A Q ▷ N'.X) := by
  have hu : freeUnit A P ≫ ((Mod.free A.X).map f).hom = f ≫ freeUnit A Q :=
    ((Mod.freeForgetAdjunction A.X).unit.naturality f).symm
  rw [← tensorHom_id (freeUnit A P) N.X, ← tensorHom_id (freeUnit A Q) N'.X,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, hu]

/-- For original coefficient arrows, the complete comparison map is the
literal ambient tensor of both original coefficient and target maps. -/
theorem comparisonMap_coefficient_hom {P Q : C} (f : P ⟶ Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    (comparisonMap A ((Mod.free A.X).map f) g).hom = f ⊗ₘ g.hom := by
  rw [comparisonMap_hom, ← Category.assoc, freeUnit_tensor_coefficient,
    Category.assoc, forward_unit, Category.comp_id]

/-- Every original free-source module map, including those not induced
by a coefficient arrow, retains its actual full free-unit adjunct. -/
theorem source_naturality {P Q : C}
    (h : (Mod.free A.X).obj P ⟶ (Mod.free A.X).obj Q) (N : Mod C A.X) :
    (Mod.relativeTensorMap A h (𝟙 N)).hom ≫ (forward A Q N).hom =
      (forward A P N).hom ≫ (freeUnit A P ▷ N.X) ≫
        (h.hom ▷ N.X) ≫ forwardRaw A Q N := by
  have hn := congrArg (fun k => k.hom) (comparison_naturality A h (𝟙 N))
  simpa only [Mod.comp_hom', comparisonMap_hom, Mod.id_hom', tensorHom_id,
    Category.assoc] using hn

/-- The actual quotient comparison is natural simultaneously in every
original coefficient arrow and every original target-module arrow. -/
theorem coefficient_naturality {P Q : C} (f : P ⟶ Q)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    (Mod.relativeTensorMap A ((Mod.free A.X).map f) g).hom ≫ (forward A Q N').hom =
      (forward A P N).hom ≫ (f ⊗ₘ g.hom) := by
  have hn := congrArg (fun k => k.hom)
    (comparison_naturality A ((Mod.free A.X).map f) g)
  simpa only [Mod.comp_hom', comparisonMap_coefficient_hom] using hn

/-- Every entire target-module arrow acts by the original ambient
left-tensor map through the complete free-relative comparison. -/
theorem target_naturality (P : C) {N N' : Mod C A.X} (g : N ⟶ N') :
    (Mod.relativeTensorMap A (𝟙 ((Mod.free A.X).obj P)) g).hom ≫
        (forward A P N').hom =
      (forward A P N).hom ≫ (P ◁ g.hom) := by
  simpa only [Functor.map_id, id_tensorHom] using
    coefficient_naturality A (𝟙 P) g

end Tensor

end CategoryTheory.Mod.FreeRelativeTensor
