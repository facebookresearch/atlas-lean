/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Transport.PairLeftUnitSource
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairAugmentationSource
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairRelativeTensor

/-!
# Original free-pair source arrows under monoidal transport

The actual carrier unit and counit carry both original free-source maps and
the complete pair inverse. The component identities retain the original
whiskered tensor and balanced free comparison. On an original free target,
the full generator becomes the first coefficient map tensored with the
second coefficient, through the actual free-adjunction unit and action.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uD vD
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Monoidal.TransportPairSource
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The original carrier image of a free comparison, with its actual counit. -/
def carrierFreeIso (E : C ≌ D) {H : C} {T : D} (eH : H ≅ E.inverse.obj T) :
    E.functor.obj H ≅ T := E.functor.mapIso eH ≪≫ E.counitIso.app T

theorem map_original_source_arrow (E : C ≌ D) {F G : C} {A B : D}
    (eF : F ≅ E.inverse.obj A) (eG : G ≅ E.inverse.obj B) (f : A ⟶ B) :
    E.functor.map (eF.hom ≫ E.inverse.map f ≫ eG.inv) =
      (carrierFreeIso E eF).hom ≫ f ≫ (carrierFreeIso E eG).inv := by
  have h : E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app B =
      E.counitIso.hom.app A ≫ f := E.counitIso.hom.naturality f
  have hc : E.functor.map (E.inverse.map f) =
      E.counitIso.hom.app A ≫ f ≫ E.counitIso.inv.app B := by
    apply (cancel_mono (E.counitIso.hom.app B)).1
    simp only [Category.assoc, E.counitIso.inv_hom_id_app]
    simpa only [Functor.id_obj, Category.comp_id] using h
  simp only [Functor.map_comp, carrierFreeIso, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  rw [hc]
  simp only [Category.assoc]
  rfl

variable [MonoidalCategory C]

/-- The original pair-left-unit arrow has the actual module source word. -/
theorem pair_original_source_leftUnit (E : C ≌ D) {F G H : C} {A B T : D}
    (eF : F ≅ E.inverse.obj A) (eG : G ≅ E.inverse.obj B)
    (eH : H ≅ E.inverse.obj T) (p : F ⊗ G ≅ H)
    (c : letI : MonoidalCategory D := Monoidal.transport E; A ⊗ B ≅ T)
    (hc : c.inv = (carrierFreeIso E eH).inv ≫ E.functor.map p.inv ≫
      E.functor.map (eF.hom ⊗ₘ eG.hom)) (l : A ⟶ E.functor.obj (𝟙_ C)) :
    letI : MonoidalCategory D := Monoidal.transport E
    eH.hom ≫ E.inverse.map (c.inv ≫ (l ▷ B) ≫ (λ_ B).hom) ≫ eG.inv =
      p.inv ≫ ((eF.hom ≫ E.inverse.map l ≫ (E.unitIso.app (𝟙_ C)).inv) ▷ G) ≫
        (λ_ G).hom := by
  let : MonoidalCategory D := Monoidal.transport E
  have ht := pairInverse_leftUnit E eF eG (carrierFreeIso E eH) p l
  have hf : c.inv ≫ (l ▷ B) ≫ (λ_ B).hom =
      (carrierFreeIso E eH).inv ≫ E.functor.map
        (p.inv ≫ ((eF.hom ≫ E.inverse.map l ≫ (E.unitIso.app (𝟙_ C)).inv) ▷ G) ≫
          (λ_ G).hom) ≫ (carrierFreeIso E eG).hom := by
    rw [hc]
    exact ht
  apply E.functor.map_injective
  rw [map_original_source_arrow, hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]


universe uK vK

variable {K : Type uK} [Category.{vK} K]

/-- The complete original equivalence and two coefficient functors, before evaluation. -/
structure TransportPairData where
  /-- The original carrier equivalence between `C` and `D`. -/
  equivalence : C ≌ D
  /-- The original left coefficient functor into `D`. -/
  leftFree : K ⥤ D
  /-- The original right coefficient functor into `D`. -/
  rightFree : K ⥤ D

namespace TransportPairData

/-- The original tensor of the two complete coefficient functors. -/
def tensorSource (d : TransportPairData (C := C) (D := D) (K := K)) : K × K ⥤ D :=
  letI : MonoidalCategory D := Monoidal.transport d.equivalence
  d.leftFree.prod d.rightFree ⋙ tensor D

/-- The original inverse-carrier tensor followed by the complete forward equivalence. -/
def inverseSource (d : TransportPairData (C := C) (D := D) (K := K)) : K × K ⥤ D :=
  ((d.leftFree ⋙ d.equivalence.inverse).prod (d.rightFree ⋙ d.equivalence.inverse) ⋙
    tensor C) ⋙ d.equivalence.functor

/-- Both original coefficient arrows have their full inverse-carrier tensor word. -/
theorem tensorSource_map (d : TransportPairData (C := C) (D := D) (K := K))
    {X X' Y Y' : K} (f : X ⟶ X') (g : Y ⟶ Y') :
    (tensorSource d).map (X := (X, Y)) (Y := (X', Y')) (f, g) =
      d.equivalence.functor.map
        (d.equivalence.inverse.map (d.leftFree.map f) ⊗ₘ
          d.equivalence.inverse.map (d.rightFree.map g)) := rfl

/-- The equality of the complete actual transported tensor functors. -/
theorem source_eq_inverse (d : TransportPairData (C := C) (D := D) (K := K)) :
    tensorSource d = inverseSource d := rfl

/-- The original whole equality-cast comparison. -/
def castIso (d : TransportPairData (C := C) (D := D) (K := K)) :
    tensorSource d ≅ inverseSource d := eqToIso (source_eq_inverse d)

/-- The entire original transport inverse is the identity natural transformation. -/
theorem castIso_inv (d : TransportPairData (C := C) (D := D) (K := K)) :
    (castIso d).inv = 𝟙 (tensorSource d) := rfl

end TransportPairData

universe uS vS uM vM uB vB uO vO

/-- The complete free, tensor, carrier and represented-pair data of an original balanced comparison. -/
structure BalancedPairData {S : Type uS} [Category.{vS} S]
    {M : Type uM} [Category.{vM} M] {B : Type uB} [Category.{vB} B]
    {O : Type uO} [Category.{vO} O] where
  /-- The specified original free-source functor. -/
  free : S ⥤ M
  /-- The original tensor functor on the module-side category. -/
  moduleTensor : M × M ⥤ M
  /-- The original tensor functor on the source-side category. -/
  sequenceTensor : S × S ⥤ S
  /-- The specified original carrier functor. -/
  carrier : M ⥤ O
  /-- The original left coefficient functor into the source-side category. -/
  left : B ⥤ S
  /-- The original right coefficient functor into the source-side category. -/
  right : B ⥤ S
  /-- The specified comparison of free-source tensor with tensor followed by the free functor. -/
  comparison : free.prod free ⋙ moduleTensor ≅ sequenceTensor ⋙ free

namespace BalancedPairData
variable {S : Type uS} [Category.{vS} S] {M : Type uM} [Category.{vM} M]
  {B : Type uB} [Category.{vB} B] {O : Type uO} [Category.{vO} O]

/-- The original tensor of the two represented free-module functors. -/
def source (d : BalancedPairData (S := S) (M := M) (B := B) (O := O)) : B × B ⥤ O :=
  ((d.left ⋙ d.free).prod (d.right ⋙ d.free) ⋙ d.moduleTensor) ⋙ d.carrier

/-- The original free module on the represented Day tensor, in the same carrier. -/
def target (d : BalancedPairData (S := S) (M := M) (B := B) (O := O)) : B × B ⥤ O :=
  (d.left.prod d.right ⋙ (d.sequenceTensor ⋙ d.free)) ⋙ d.carrier

/-- The original complete balanced comparison uses ordinary left and right whiskering. -/
def iso (d : BalancedPairData (S := S) (M := M) (B := B) (O := O)) : source d ≅ target d :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (d.left.prod d.right) d.comparison) d.carrier

end BalancedPairData

end CategoryTheory.Monoidal.TransportPairSource


namespace CategoryTheory.Mod.FreePairAugmentation
universe uT vT
private theorem tensorActionUnit
    {C : Type uT} [CategoryTheory.Category.{vT} C] [CategoryTheory.MonoidalCategory C]
    {P Q A T : C} (c : P ⟶ A) (u : Q ⟶ T) (a : A ⊗ T ⟶ A ⊗ Q)
    (h : (A ◁ u) ≫ a = 𝟙 (A ⊗ Q)) : (c ⊗ₘ u) ≫ a = c ▷ Q := by
  rw [tensorHom_def, Category.assoc, h, Category.comp_id]

universe uF vF
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj
variable {C : Type uF} [Category.{vF} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C)

/-- A free target retains the first entire generator map and second coefficient. -/
theorem original_pair_free_action (P Q : C)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X) :
    ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        Mod.FreeRelativeTensor.freeUnit A Q) ≫ ((Mod.free A.X).obj Q).mod.smul =
      (Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ▷ Q := by
  let c : P ⟶ A.X := Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom
  exact tensorActionUnit c (Mod.FreeRelativeTensor.freeUnit A Q)
    ((Mod.free A.X).obj Q).mod.smul (Mod.FreePairRelativeTensor.originalFreeUnit_action A Q)

variable [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
/-- The original monoidal structure on modules over `A`. -/
local instance augmentationModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A

/-- The full pair arrow into the original free target has its actual coefficient generator. -/
theorem original_pair_free_generator (R P Q : C) (h : R ⟶ P ⊗ Q)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X) :
    Mod.FreeRelativeTensor.freeUnit A R ≫
        ((Mod.free A.X).map h ≫ (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
          (f ⊗ₘ 𝟙 ((Mod.free A.X).obj Q)) ≫ (λ_ ((Mod.free A.X).obj Q)).hom).hom =
      h ≫ ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ▷ Q) := by
  let G : Mod C A.X := (Mod.free A.X).obj Q
  let g : G ⟶ G := 𝟙 G
  have hs := tensor_left_unit_generator_precompose A R P Q G h f g
  have hi : g.hom = 𝟙 G.X := rfl
  let u : Q ⟶ G.X := Mod.FreeRelativeTensor.freeUnit A Q
  have hu : Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom =
      Mod.FreeRelativeTensor.freeUnit A Q := by
    rw [hi]
    change u ≫ 𝟙 G.X = u
    exact Category.comp_id u
  rw [hu] at hs
  exact hs.trans (congrArg (fun q => h ≫ q) (original_pair_free_action A P Q f))

end CategoryTheory.Mod.FreePairAugmentation
