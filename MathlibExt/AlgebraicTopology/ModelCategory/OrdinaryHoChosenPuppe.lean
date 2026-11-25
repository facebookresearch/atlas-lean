/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoCofiberKernel
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Chosen ordinary Puppe maps and their actual kernels

The whole cone functor, insertion, caller-selected cofiber cocones and
colimit witnesses remain explicit. Every map is their original desc
function. The target quotient is constructed from those same witnesses.
The source zero object is supplied separately and compared with the
model category's chosen zero by actual endpoint functions.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ZeroObject

namespace HomotopicalAlgebra.OrdinaryHoChosenPuppe

variable {C : Type u} [Category.{v} C]

section Zero

variable (Z : C) (hZ : IsZero Z)

/-- The actual caller's complete terminal endpoint function. -/
def toZero (X : C) : X ⟶ Z := hZ.isTerminal.from X

/-- The actual caller's complete initial endpoint function. -/
def fromZero (X : C) : Z ⟶ X := hZ.isInitial.to X

/-- Both actual endpoint functions give the original null source map. -/
def nullMap (X Y : C) : X ⟶ Y := toZero Z hZ X ≫ fromZero Z hZ Y

/-- Every original source arrow preserves the actual terminal endpoint. -/
theorem toZero_comp {X Y : C} (f : X ⟶ Y) : f ≫ toZero Z hZ Y = toZero Z hZ X :=
  hZ.isTerminal.hom_ext _ _

/-- Every original target arrow preserves the actual initial endpoint. -/
theorem fromZero_comp {X Y : C} (f : X ⟶ Y) : fromZero Z hZ X ≫ f = fromZero Z hZ Y :=
  hZ.isInitial.hom_ext _ _

/-- The full zero-target Arrow functor keeps both original input components. -/
def zeroArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (toZero Z hZ X)
  map {X Y} f := Arrow.homMk f (𝟙 Z) (by
    change f ≫ toZero Z hZ Y = toZero Z hZ X ≫ 𝟙 Z
    rw [toZero_comp, Category.comp_id])
  map_id X := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · exact (Category.comp_id _).symm

end Zero

section Categorical

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

include hc

/-- Every entire chosen cofiber map is the same original colimit desc. -/
def cofiberMap {F G : Arrow C} (q : F ⟶ G) : (c F).pt ⟶ (c G).pt :=
  PushoutCocone.IsColimit.desc (hc F)
    (cone.map q.left ≫ (c G).inl) (q.right ≫ (c G).inr) (by
      have hn : ι.app F.left ≫ cone.map q.left = q.left ≫ ι.app G.left :=
        (ι.naturality q.left).symm
      rw [← Category.assoc, hn, Category.assoc, (c G).condition,
        ← Category.assoc, q.w, Category.assoc])

/-- The full cone-source component retains the original functor map and target leg. -/
theorem cofiberMap_cone {F G : Arrow C} (q : F ⟶ G) :
    (c F).inl ≫ cofiberMap cone ι c hc q = cone.map q.left ≫ (c G).inl :=
  PushoutCocone.IsColimit.inl_desc (hc F) _ _ _

/-- The whole target component retains the caller's actual Arrow right map. -/
theorem cofiberMap_target {F G : Arrow C} (q : F ⟶ G) :
    (c F).inr ≫ cofiberMap cone ι c hc q = q.right ≫ (c G).inr :=
  PushoutCocone.IsColimit.inr_desc (hc F) _ _ _

/-- Every whole actual identity is preserved on both original colimit legs. -/
theorem cofiberMap_id (F : Arrow C) : cofiberMap cone ι c hc (𝟙 F) = 𝟙 (c F).pt := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [cofiberMap_cone]
    change cone.map (𝟙 F.left) ≫ (c F).inl = (c F).inl ≫ 𝟙 (c F).pt
    rw [cone.map_id, Category.id_comp, Category.comp_id]
  · rw [cofiberMap_target]
    change 𝟙 F.right ≫ (c F).inr = (c F).inr ≫ 𝟙 (c F).pt
    rw [Category.id_comp, Category.comp_id]

/-- Full actual Arrow composition is preserved on both selected colimit legs. -/
theorem cofiberMap_comp {F G H : Arrow C} (q : F ⟶ G) (r : G ⟶ H) :
    cofiberMap cone ι c hc (q ≫ r) =
      cofiberMap cone ι c hc q ≫ cofiberMap cone ι c hc r := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [cofiberMap_cone, ← Category.assoc, cofiberMap_cone, Category.assoc,
      cofiberMap_cone]
    change cone.map (q.left ≫ r.left) ≫ (c H).inl =
      cone.map q.left ≫ (cone.map r.left ≫ (c H).inl)
    rw [cone.map_comp, Category.assoc]
  · rw [cofiberMap_target, ← Category.assoc, cofiberMap_target, Category.assoc,
      cofiberMap_target]
    change (q.right ≫ r.right) ≫ (c H).inr = q.right ≫ (r.right ≫ (c H).inr)
    exact Category.assoc _ _ _

/-- The whole chosen cofiber functor retains all original c/hc functions. -/
def cofiberFunctor : Arrow C ⥤ C where
  obj F := (c F).pt
  map q := cofiberMap cone ι c hc q
  map_id := cofiberMap_id cone ι c hc
  map_comp q r := cofiberMap_comp cone ι c hc q r

variable (Z : C) (hZ : IsZero Z)

/-- The actual chosen suspension is the same cofiber functor on the original zero Arrows. -/
def suspensionFunctor : C ⥤ C := zeroArrowFunctor Z hZ ⋙ cofiberFunctor cone ι c hc

/-- Retain the entire selected suspension cocone, with the original zero endpoint. -/
abbrev suspensionCone (X : C) := c (Arrow.mk (toZero Z hZ X))

/-- The whole actual suspension map is typed at its literal original chosen carriers. -/
def suspensionMap {X Y : C} (f : X ⟶ Y) :
    (suspensionCone cone ι c Z hZ X).pt ⟶ (suspensionCone cone ι c Z hZ Y).pt :=
  cofiberMap cone ι c hc ((zeroArrowFunctor Z hZ).map f)

/-- The full functor map is the same original chosen-carrier suspension function. -/
theorem suspensionFunctor_map {X Y : C} (f : X ⟶ Y) :
    (suspensionFunctor cone ι c hc Z hZ).map f = suspensionMap cone ι c hc Z hZ f := rfl

/-- The full boundary uses the original cofiber desc and selected suspension legs. -/
def boundary (F : Arrow C) : (c F).pt ⟶ (suspensionCone cone ι c Z hZ F.left).pt :=
  PushoutCocone.IsColimit.desc (hc F)
    (suspensionCone cone ι c Z hZ F.left).inl
    (toZero Z hZ F.right ≫ (suspensionCone cone ι c Z hZ F.left).inr) (by
      have hs : ι.app F.left ≫ (suspensionCone cone ι c Z hZ F.left).inl =
          toZero Z hZ F.left ≫ (suspensionCone cone ι c Z hZ F.left).inr :=
        (suspensionCone cone ι c Z hZ F.left).condition
      rw [hs, ← Category.assoc, toZero_comp]
      rfl)

/-- Every complete boundary retains the actual original cone-to-suspension leg. -/
theorem boundary_cone (F : Arrow C) :
    (c F).inl ≫ boundary cone ι c hc Z hZ F = (suspensionCone cone ι c Z hZ F.left).inl :=
  PushoutCocone.IsColimit.inl_desc (hc F) _ _ _

/-- Every complete boundary retains the actual original zero/target leg. -/
theorem boundary_target (F : Arrow C) :
    (c F).inr ≫ boundary cone ι c hc Z hZ F =
      toZero Z hZ F.right ≫ (suspensionCone cone ι c Z hZ F.left).inr :=
  PushoutCocone.IsColimit.inr_desc (hc F) _ _ _

/-- The whole suspension source function retains the actual cone functor map. -/
theorem suspensionMap_cone {X Y : C} (f : X ⟶ Y) :
    (suspensionCone cone ι c Z hZ X).inl ≫ suspensionMap cone ι c hc Z hZ f =
      cone.map f ≫ (suspensionCone cone ι c Z hZ Y).inl :=
  cofiberMap_cone cone ι c hc ((zeroArrowFunctor Z hZ).map f)

/-- The full suspension zero function is the same original zero leg. -/
theorem suspensionMap_zero {X Y : C} (f : X ⟶ Y) :
    (suspensionCone cone ι c Z hZ X).inr ≫ suspensionMap cone ι c hc Z hZ f =
      (suspensionCone cone ι c Z hZ Y).inr := by
  have h := cofiberMap_target cone ι c hc ((zeroArrowFunctor Z hZ).map f)
  exact h.trans (Category.id_comp _)

/-- The full original chosen boundary is natural on every actual Arrow square. -/
theorem boundary_naturality {F G : Arrow C} (q : F ⟶ G) :
    cofiberMap cone ι c hc q ≫ boundary cone ι c hc Z hZ G =
      boundary cone ι c hc Z hZ F ≫ suspensionMap cone ι c hc Z hZ q.left := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, cofiberMap_cone, Category.assoc, boundary_cone,
      ← Category.assoc, boundary_cone, suspensionMap_cone]
  · rw [← Category.assoc, cofiberMap_target, Category.assoc, boundary_target,
      ← Category.assoc, toZero_comp, ← Category.assoc,
      boundary_target, Category.assoc, suspensionMap_zero]

/-- The whole original chosen boundary family is a complete actual natural transformation. -/
def boundaryNatTrans : cofiberFunctor cone ι c hc ⟶
    Arrow.leftFunc ⋙ suspensionFunctor cone ι c hc Z hZ where
  app F := boundary cone ι c hc Z hZ F
  naturality _ _ q := boundary_naturality cone ι c hc Z hZ q

/-- The same original quotient cocone has the actual selected suspension carrier. -/
def targetQuotientCocone (F : Arrow C) : PushoutCocone (c F).inr (toZero Z hZ F.right) :=
  PushoutCocone.mk (boundary cone ι c hc Z hZ F)
    (suspensionCone cone ι c Z hZ F.left).inr (boundary_target cone ι c hc Z hZ F)

/-- Every quotient desc is the SAME original chosen suspension-colimit desc. -/
def targetQuotientDesc (F : Arrow C)
    (t : PushoutCocone (c F).inr (toZero Z hZ F.right)) :
    (suspensionCone cone ι c Z hZ F.left).pt ⟶ t.pt :=
  PushoutCocone.IsColimit.desc (hc (Arrow.mk (toZero Z hZ F.left)))
    ((c F).inl ≫ t.inl) t.inr (by
      change ι.app F.left ≫ ((c F).inl ≫ t.inl) = toZero Z hZ F.left ≫ t.inr
      rw [← Category.assoc, (c F).condition, Category.assoc, t.condition,
        ← Category.assoc, toZero_comp]
      rfl)

/-- The full quotient lift preserves the original cone component. -/
theorem targetQuotientDesc_cone (F : Arrow C)
    (t : PushoutCocone (c F).inr (toZero Z hZ F.right)) :
    (suspensionCone cone ι c Z hZ F.left).inl ≫ targetQuotientDesc cone ι c hc Z hZ F t =
      (c F).inl ≫ t.inl :=
  PushoutCocone.IsColimit.inl_desc (hc (Arrow.mk (toZero Z hZ F.left))) _ _ _

/-- The full quotient lift preserves the actual supplied zero component. -/
theorem targetQuotientDesc_zero (F : Arrow C)
    (t : PushoutCocone (c F).inr (toZero Z hZ F.right)) :
    (suspensionCone cone ι c Z hZ F.left).inr ≫ targetQuotientDesc cone ι c hc Z hZ F t = t.inr :=
  PushoutCocone.IsColimit.inr_desc (hc (Arrow.mk (toZero Z hZ F.left))) _ _ _

/-- Both original cofiber legs identify the complete quotient boundary function. -/
theorem targetQuotientDesc_boundary (F : Arrow C)
    (t : PushoutCocone (c F).inr (toZero Z hZ F.right)) :
    boundary cone ι c hc Z hZ F ≫ targetQuotientDesc cone ι c hc Z hZ F t = t.inl := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, boundary_cone, targetQuotientDesc_cone]
  · rw [← Category.assoc, boundary_target, Category.assoc, targetQuotientDesc_zero]
    exact t.condition.symm

/-- The complete quotient function is unique on both original selected suspension legs. -/
theorem targetQuotientDesc_unique (F : Arrow C)
    (t : PushoutCocone (c F).inr (toZero Z hZ F.right))
    (m : (suspensionCone cone ι c Z hZ F.left).pt ⟶ t.pt)
    (hm : boundary cone ι c hc Z hZ F ≫ m = t.inl)
    (hz : (suspensionCone cone ι c Z hZ F.left).inr ≫ m = t.inr) :
    m = targetQuotientDesc cone ι c hc Z hZ F t := by
  apply PushoutCocone.IsColimit.hom_ext (hc (Arrow.mk (toZero Z hZ F.left)))
  · calc
      (suspensionCone cone ι c Z hZ F.left).inl ≫ m =
          ((c F).inl ≫ boundary cone ι c hc Z hZ F) ≫ m :=
        congrArg (fun q => q ≫ m) (boundary_cone cone ι c hc Z hZ F).symm
      _ = (c F).inl ≫ t.inl := by rw [Category.assoc, hm]
      _ = (suspensionCone cone ι c Z hZ F.left).inl ≫
          targetQuotientDesc cone ι c hc Z hZ F t :=
        (targetQuotientDesc_cone cone ι c hc Z hZ F t).symm
  · rw [hz, targetQuotientDesc_zero]

/-- The quotient universal property is CONSTRUCTED from the two original c/hc witnesses. -/
def targetQuotientIsColimit (F : Arrow C) : IsColimit (targetQuotientCocone cone ι c hc Z hZ F) :=
  PushoutCocone.IsColimit.mk (boundary_target cone ι c hc Z hZ F)
    (targetQuotientDesc cone ι c hc Z hZ F)
    (targetQuotientDesc_boundary cone ι c hc Z hZ F)
    (targetQuotientDesc_zero cone ι c hc Z hZ F)
    (fun t m hm hz => targetQuotientDesc_unique cone ι c hc Z hZ F t m hm hz)

/-- The entire actual target quotient square is the original selected suspension. -/
theorem targetQuotientIsPushout (F : Arrow C) :
    IsPushout (c F).inr (toZero Z hZ F.right) (boundary cone ι c hc Z hZ F)
      (suspensionCone cone ι c Z hZ F.left).inr :=
  IsPushout.of_isColimit (targetQuotientIsColimit cone ι c hc Z hZ F)

/-- The cone-comparison function uses the same actual cofiber desc and original insertion. -/
def coneComparison (F : Arrow C) : (c F).pt ⟶ cone.obj F.right :=
  PushoutCocone.IsColimit.desc (hc F) (cone.map F.hom) (ι.app F.right)
    (ι.naturality F.hom).symm

/-- Its entire first leg is the original cone map on the input morphism. -/
theorem coneComparison_cone (F : Arrow C) :
    (c F).inl ≫ coneComparison cone ι c hc F = cone.map F.hom :=
  PushoutCocone.IsColimit.inl_desc (hc F) _ _ _

/-- Its complete second leg is the same original insertion at the input target. -/
theorem coneComparison_target (F : Arrow C) :
    (c F).inr ≫ coneComparison cone ι c hc F = ι.app F.right :=
  PushoutCocone.IsColimit.inr_desc (hc F) _ _ _

/-- The entire boundary/suspension composite factors through the ACTUAL original target cone. -/
theorem boundary_suspension_factors_cone (F : Arrow C) :
    boundary cone ι c hc Z hZ F ≫ suspensionMap cone ι c hc Z hZ F.hom =
      coneComparison cone ι c hc F ≫ (suspensionCone cone ι c Z hZ F.right).inl := by
  apply PushoutCocone.IsColimit.hom_ext (hc F)
  · rw [← Category.assoc, boundary_cone, suspensionMap_cone,
      ← Category.assoc, coneComparison_cone]
  · rw [← Category.assoc, boundary_target, Category.assoc, suspensionMap_zero,
      ← Category.assoc, coneComparison_target]
    exact (suspensionCone cone ι c Z hZ F.right).condition.symm

end Categorical

section Model

variable [ModelCategory C] [HasZeroObject C] (Z : C) (hZ : IsZero Z)

omit [ModelCategory C] in
/-- Both complete zero endpoint functions are identified by the actual given zero-object Iso. -/
theorem actualNullMap_eq_chosen (X E : C) :
    nullMap Z hZ X E = OrdinaryHoCofiberKernel.nullMap X E := by
  let e : (0 : C) ≅ Z := HasZeroObject.zeroIsInitial.uniqueUpToIso hZ.isInitial
  have hInitial : e.hom ≫ fromZero Z hZ E = HasZeroObject.zeroIsInitial.to E :=
    HasZeroObject.zeroIsInitial.hom_ext _ _
  have hTerminal : HasZeroObject.zeroIsTerminal.from X ≫ e.hom = toZero Z hZ X :=
    hZ.isTerminal.hom_ext _ _
  unfold nullMap OrdinaryHoCofiberKernel.nullMap
  rw [← hInitial, ← Category.assoc, hTerminal]

/-- The actual original zero contraction is transported through its complete endpoint Iso. -/
theorem weak_contraction_to_chosen_zero (W : C)
    (hw : weakEquivalences C (toZero Z hZ W)) :
    weakEquivalences C (HasZeroObject.zeroIsTerminal.from W) := by
  let e : (0 : C) ≅ Z := HasZeroObject.zeroIsTerminal.uniqueUpToIso hZ.isTerminal
  have h : toZero Z hZ W ≫ e.inv = HasZeroObject.zeroIsTerminal.from W :=
    HasZeroObject.zeroIsTerminal.hom_ext _ _
  have hComp := (weakEquivalences C).comp_mem _ _ hw (mem_weakEquivalences e.inv)
  rwa [h] at hComp

omit [HasZeroObject C] in
include hZ in
/-- Every actual zero-source Ho morphism is unique by the original fundamental lemma. -/
theorem actualZeroHom_subsingleton (E : C) [IsFibrant E] :
    Subsingleton (((weakEquivalences C).Q).obj Z ⟶ ((weakEquivalences C).Q).obj E) := by
  let _ : IsCofibrant Z := by
    rw [isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial]
    infer_instance
  refine ⟨fun a b => ?_⟩
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) Z E a
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) Z E b
  exact ((weakEquivalences C).Q).congr_map (hZ.isInitial.hom_ext f g)

/-- The quotient image law retains the actual caller's zero and the SAME c/hc desc. -/
theorem actual_quotient_image_iff {X Y E : C} [IsCofibrant X] [IsFibrant E]
    (i : X ⟶ Y) [Cofibration i]
    (q : PushoutCocone i (toZero Z hZ X)) (hq : IsColimit q)
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj q.pt ⟶ ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map q.inl ≫ h = g) ↔
      ((weakEquivalences C).Q).map i ≫ g = OrdinaryHoCofiberKernel.nullHom X E := by
  constructor
  · rintro ⟨h, rfl⟩
    have hZero := actualZeroHom_subsingleton Z hZ E
    rw [← Category.assoc, ← Functor.map_comp, q.condition, Functor.map_comp,
      Category.assoc]
    have hValue : ((weakEquivalences C).Q).map q.inr ≫ h =
        ((weakEquivalences C).Q).map (fromZero Z hZ E) := hZero.elim _ _
    rw [hValue, ← Functor.map_comp]
    exact ((weakEquivalences C).Q).congr_map (actualNullMap_eq_chosen Z hZ X E)
  · intro hg
    let _ : IsCofibrant Y := isCofibrant_of_cofibration i
    obtain ⟨g₀, g₁, P, H, _, hg₀, hi, _, _⟩ :=
      OrdinaryHoCofiberKernel.nullification_of_map_eq i g hg
    have hiActual : i ≫ g₁ = toZero Z hZ X ≫ fromZero Z hZ E :=
      hi.trans (actualNullMap_eq_chosen Z hZ X E).symm
    let h := PushoutCocone.IsColimit.desc hq g₁ (fromZero Z hZ E) hiActual
    have hLeg : q.inl ≫ h = g₁ := PushoutCocone.IsColimit.inl_desc hq _ _ hiActual
    have hSame : ((weakEquivalences C).Q).map g₁ = g :=
      ((RightHomotopyRel.iff_map_eq ((weakEquivalences C).Q) Y E).mp
        H.rightHomotopyRel).symm.trans hg₀
    refine ⟨((weakEquivalences C).Q).map h, ?_⟩
    rw [← Functor.map_comp, hLeg]
    exact hSame

variable (cone : C ⥤ C) (ι : 𝟭 C ⟶ cone)
  (c : ∀ F : Arrow C, PushoutCocone (ι.app F.left) F.hom)
  (hc : ∀ F, IsColimit (c F))

omit [HasZeroObject C] in
include hc in
/-- The actual original source cofibration makes its SAME chosen cofiber target leg cofibrant. -/
theorem cofiberTarget_cofibration (F : Arrow C) [Cofibration (ι.app F.left)] :
    Cofibration (c F).inr := by
  rw [cofibration_iff]
  exact (cofibrations C).of_isPushout (IsPushout.of_isColimit (hc F)).flip
    (mem_cofibrations (ι.app F.left))

include hc in
/-- The first ordinary Puppe image is the exact original source-map null kernel. -/
theorem first_exact (F : Arrow C) [IsCofibrant F.left] [IsCofibrant F.right]
    [Cofibration (ι.app F.left)] (E : C) [IsFibrant E]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj F.left)))
    (g : ((weakEquivalences C).Q).obj F.right ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj (c F).pt ⟶ ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map (c F).inr ≫ h =
        g) ↔
      ((weakEquivalences C).Q).map F.hom ≫ g = OrdinaryHoCofiberKernel.nullHom F.left E := by
  let _ : IsCofibrant ((𝟭 C).obj F.left) := inferInstanceAs (IsCofibrant F.left)
  exact OrdinaryHoCofiberKernel.chosen_cone_cofiber_image_iff (ι.app F.left)
    (weak_contraction_to_chosen_zero Z hZ (cone.obj F.left) hCone) F.hom (c F) (hc F) g

/-- The second ordinary Puppe image is the exact SAME chosen target-restriction kernel. -/
theorem second_exact (F : Arrow C) [IsCofibrant F.right] [Cofibration (ι.app F.left)]
    (E : C) [IsFibrant E]
    (g : ((weakEquivalences C).Q).obj (c F).pt ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ F.left).pt ⟶
        ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map (boundary cone ι c hc Z hZ F) ≫ h = g) ↔
      ((weakEquivalences C).Q).map (c F).inr ≫ g =
        OrdinaryHoCofiberKernel.nullHom F.right E := by
  let _ : Cofibration (c F).inr := cofiberTarget_cofibration cone ι c hc F
  exact actual_quotient_image_iff Z hZ (c F).inr
    (targetQuotientCocone cone ι c hc Z hZ F)
    (targetQuotientIsColimit cone ι c hc Z hZ F) g

/-- The actual boundary/suspension composite is null after every full fibrant target Hom. -/
theorem boundary_suspension_post_null (F : Arrow C) (E : C) [IsFibrant E]
    (hCone : weakEquivalences C (toZero Z hZ (cone.obj F.right)))
    (g : ((weakEquivalences C).Q).obj (suspensionCone cone ι c Z hZ F.right).pt ⟶
      ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map (boundary cone ι c hc Z hZ F) ≫
        (((weakEquivalences C).Q).map (suspensionMap cone ι c hc Z hZ F.hom) ≫ g) =
      OrdinaryHoCofiberKernel.nullHom (c F).pt E := by
  have hNull := OrdinaryHoCofiberKernel.subsingleton_hom_of_weak_contraction
    (cone.obj F.right) E
    (weak_contraction_to_chosen_zero Z hZ (cone.obj F.right) hCone)
  rw [← Category.assoc, ← Functor.map_comp,
    boundary_suspension_factors_cone, Functor.map_comp, Category.assoc]
  rw [hNull.elim (((weakEquivalences C).Q).map (suspensionCone cone ι c Z hZ F.right).inl ≫ g)
      (OrdinaryHoCofiberKernel.nullHom (cone.obj F.right) E),
    OrdinaryHoCofiberKernel.precomp_nullHom]

end Model

end HomotopicalAlgebra.OrdinaryHoChosenPuppe
