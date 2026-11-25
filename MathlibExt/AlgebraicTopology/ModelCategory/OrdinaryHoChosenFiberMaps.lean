/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenFiberKernel
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Actual chosen-fiber maps, choices and ordinary Ho coefficient functions

The complete chosen fiber functor is built from the caller's actual cones
and limits. Both legs determine all identity, composition and choice laws.
The actual Arrow null-fiber functor retains both original square components
and all coefficient precomposition functions.

The first-leg natural transformation is defined on actual fibrations over
fibrant bases. Every coefficient component is surjective by the actual
model covering-homotopy image-exactness theorem. Both full chosen-carrier functions
and their Ho Hom functions are compared by the original two limit proofs.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

universe u₁ u₂ v₁ v₂

private theorem actualMappedProjection {C₁ : Type u₁} [Category.{v₁} C₁]
    {D : Type u₂} [Category.{v₂} D] (J : C₁ ⥤ D) {X Y Z : C₁} {T : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c) (f : T ⟶ J.obj X) :
    (f ≫ J.map a) ≫ J.map b = f ≫ J.map c :=
  (Category.assoc f (J.map a) (J.map b)).trans
    ((congrArg (fun r => f ≫ r) (J.map_comp a b).symm).trans
      (congrArg (fun r => f ≫ J.map r) hc))

private theorem actualMappedSquare {C₁ : Type u₁} [Category.{v₁} C₁]
    {D : Type u₂} [Category.{v₂} D] (J : C₁ ⥤ D) {X Y Z W : C₁} {T : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) (f : T ⟶ J.obj X) :
    (f ≫ J.map a) ≫ J.map b = (f ≫ J.map c) ≫ J.map d :=
  (actualMappedProjection J a b (c ≫ d) h f).trans
    ((congrArg (fun r => f ≫ r) (J.map_comp c d)).trans
      (Category.assoc f (J.map c) (J.map d)).symm)

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberMaps

variable {C : Type u} [Category.{v} C] (Z : C) (hZ : IsZero Z)
  (s : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (hs : ∀ F, IsLimit (s F))

/-- The complete given-fiber map is the actual limit lift with both original components. -/
def chosenMap {F G : Arrow C} (q : F ⟶ G) : (s F).pt ⟶ (s G).pt :=
  (hs G).lift (PullbackCone.mk ((s F).fst ≫ q.left) (s F).snd (by
    rw [Category.assoc, q.w, ← Category.assoc, (s F).condition, Category.assoc]
    exact congrArg (fun r => (s F).snd ≫ r) (hZ.isInitial.hom_ext _ _)))

/-- The complete chosen map retains the original first projection and Arrow source component. -/
theorem chosenMap_fst {F G : Arrow C} (q : F ⟶ G) :
    chosenMap Z hZ s hs q ≫ (s G).fst = (s F).fst ≫ q.left :=
  (hs G).fac _ WalkingCospan.left

/-- The complete chosen map retains the caller's actual zero projection. -/
theorem chosenMap_snd {F G : Arrow C} (q : F ⟶ G) :
    chosenMap Z hZ s hs q ≫ (s G).snd = (s F).snd :=
  (hs G).fac _ WalkingCospan.right

/-- Both original legs identify the whole actual identity function. -/
theorem chosenMap_id (F : Arrow C) : chosenMap Z hZ s hs (𝟙 F) = 𝟙 (s F).pt := by
  apply PullbackCone.IsLimit.hom_ext (hs F)
  · rw [chosenMap_fst]
    change (s F).fst ≫ 𝟙 F.left = 𝟙 (s F).pt ≫ (s F).fst
    rw [Category.comp_id, Category.id_comp]
  · rw [chosenMap_snd, Category.id_comp]

/-- Both original legs preserve the entire actual Arrow composition in its original order. -/
theorem chosenMap_comp {F G H : Arrow C} (q : F ⟶ G) (r : G ⟶ H) :
    chosenMap Z hZ s hs (q ≫ r) = chosenMap Z hZ s hs q ≫ chosenMap Z hZ s hs r := by
  apply PullbackCone.IsLimit.hom_ext (hs H)
  · rw [chosenMap_fst, Category.assoc, chosenMap_fst,
      ← Category.assoc, chosenMap_fst]
    change (s F).fst ≫ (q.left ≫ r.left) = ((s F).fst ≫ q.left) ≫ r.left
    exact (Category.assoc _ _ _).symm
  · rw [chosenMap_snd, Category.assoc, chosenMap_snd, chosenMap_snd]

/-- The whole actual chosen-fiber functor retains every original cone and limit function. -/
def chosenFunctor : Arrow C ⥤ C where
  obj F := (s F).pt
  map q := chosenMap Z hZ s hs q
  map_id := chosenMap_id Z hZ s hs
  map_comp q r := chosenMap_comp Z hZ s hs q r

/-- The original first-projection family is the complete source natural transformation. -/
def firstLegNatTrans : chosenFunctor Z hZ s hs ⟶ Arrow.leftFunc where
  app F := (s F).fst
  naturality _ _ q := chosenMap_fst Z hZ s hs q

/-- The original zero-projection family is the complete chosen point natural transformation. -/
def zeroLegNatTrans : chosenFunctor Z hZ s hs ⟶ (Functor.const (Arrow C)).obj Z where
  app F := (s F).snd
  naturality {F G} q := by
    change chosenMap Z hZ s hs q ≫ (s G).snd = (s F).snd ≫ 𝟙 Z
    exact (chosenMap_snd Z hZ s hs q).trans (Category.comp_id _).symm

variable (t : ∀ F : Arrow C, PullbackCone F.hom (hZ.isInitial.to F.right))
  (ht : ∀ F, IsLimit (t F))

/-- Both full carrier functions are the original limit-uniqueness comparison. -/
def choiceIso (F : Arrow C) : (s F).pt ≅ (t F).pt :=
  (hs F).conePointUniqueUpToIso (ht F)

/-- The forward carrier function retains the caller's entire original first leg. -/
theorem choiceIso_hom_fst (F : Arrow C) :
    (choiceIso Z hZ s hs t ht F).hom ≫ (t F).fst = (s F).fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

/-- The forward carrier function retains the caller's entire original zero leg. -/
theorem choiceIso_hom_snd (F : Arrow C) :
    (choiceIso Z hZ s hs t ht F).hom ≫ (t F).snd = (s F).snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

/-- The inverse carrier function retains the original first leg from the other given choice. -/
theorem choiceIso_inv_fst (F : Arrow C) :
    (choiceIso Z hZ s hs t ht F).inv ≫ (s F).fst = (t F).fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

/-- The inverse carrier function retains the original zero leg from the other given choice. -/
theorem choiceIso_inv_snd (F : Arrow C) :
    (choiceIso Z hZ s hs t ht F).inv ≫ (s F).snd = (t F).snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

/-- Every input square commutes with both actual chosen carriers and their first/zero legs. -/
theorem choiceIso_naturality {F G : Arrow C} (q : F ⟶ G) :
    chosenMap Z hZ s hs q ≫ (choiceIso Z hZ s hs t ht G).hom =
      (choiceIso Z hZ s hs t ht F).hom ≫ chosenMap Z hZ t ht q := by
  apply PullbackCone.IsLimit.hom_ext (ht G)
  · rw [Category.assoc, choiceIso_hom_fst, chosenMap_fst,
      Category.assoc, chosenMap_fst, ← Category.assoc, choiceIso_hom_fst]
  · rw [Category.assoc, choiceIso_hom_snd, chosenMap_snd,
      Category.assoc, chosenMap_snd, choiceIso_hom_snd]

/-- The full original carrier comparison is a natural Iso on the whole chosen-fiber functors. -/
def choiceNatIso : chosenFunctor Z hZ s hs ≅ chosenFunctor Z hZ t ht :=
  NatIso.ofComponents (choiceIso Z hZ s hs t ht) (choiceIso_naturality Z hZ s hs t ht)

section Ho

variable [ModelCategory C]

local notation "Null" => HomotopicalAlgebra.OrdinaryHoChosenFiberKernel.nullMap Z hZ

local notation "H" => CategoryTheory.MorphismProperty.Q (weakEquivalences C)

/-- The actual full null-fiber map retains the original Arrow source function. -/
def nullFiberMap (K : C) {F G : Arrow C} (q : F ⟶ G)
    (f : {f : (H).obj K ⟶ (H).obj F.left |
      f ≫ (H).map F.hom = (H).map (Null K F.right)}) :
    {f : (H).obj K ⟶ (H).obj G.left |
      f ≫ (H).map G.hom = (H).map (Null K G.right)} :=
  ⟨f.val ≫ (H).map q.left, by
    change (f.val ≫ (H).map q.left) ≫ (H).map G.hom = _
    rw [Category.assoc, ← (H).map_comp, q.w, (H).map_comp,
      ← Category.assoc, f.property, ← (H).map_comp,
      HomotopicalAlgebra.OrdinaryHoChosenFiberKernel.nullMap_postcomp]⟩

/-- The whole original null-fiber construction is a functor on every actual input square. -/
def nullFiberFunctor (K : C) : Arrow C ⥤ Type _ where
  obj F := {f : (H).obj K ⟶ (H).obj F.left |
    f ≫ (H).map F.hom = (H).map (Null K F.right)}
  map q := TypeCat.ofHom (nullFiberMap Z hZ K q)
  map_id F := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change f.val ≫ (H).map (𝟙 F.left) = f.val
    rw [(H).map_id, Category.comp_id]
  map_comp {F G J} q r := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change f.val ≫ (H).map (q.left ≫ r.left) =
      (f.val ≫ (H).map q.left) ≫ (H).map r.left
    rw [(H).map_comp, Category.assoc]

/-- Every actual coefficient map gives the original full precomposition natural transformation. -/
def coefficientNatTrans {K K' : C} (a : K' ⟶ K) :
    nullFiberFunctor Z hZ K ⟶ nullFiberFunctor Z hZ K' where
  app F := TypeCat.ofHom fun f => ⟨(H).map a ≫ f.val, by
    change ((H).map a ≫ f.val) ≫ (H).map F.hom = _
    rw [Category.assoc, f.property, ← (H).map_comp,
      HomotopicalAlgebra.OrdinaryHoChosenFiberKernel.nullMap_precomp]⟩
  naturality {F G} q := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact (Category.assoc ((H).map a) f.val ((H).map q.left)).symm

/-- Every entire coefficient identity retains the complete identity transformation. -/
theorem coefficientNatTrans_id (K : C) :
    coefficientNatTrans Z hZ (𝟙 K) = 𝟙 (nullFiberFunctor Z hZ K) := by
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  change (H).map (𝟙 K) ≫ f.val = f.val
  rw [(H).map_id, Category.id_comp]

/-- Every actual coefficient composition preserves its original full contravariant order. -/
theorem coefficientNatTrans_comp {K₀ K₁ K₂ : C} (a : K₀ ⟶ K₁) (b : K₁ ⟶ K₂) :
    coefficientNatTrans Z hZ (a ≫ b) = coefficientNatTrans Z hZ b ≫ coefficientNatTrans Z hZ a := by
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  change (H).map (a ≫ b) ≫ f.val = (H).map a ≫ ((H).map b ≫ f.val)
  rw [(H).map_comp, Category.assoc]

/-- The complete actual chosen-fiber functor is followed by ordinary Ho and full coefficient Hom. -/
def fiberHoHomFunctor (K : C) : Arrow C ⥤ Type _ :=
  chosenFunctor Z hZ s hs ⋙ (H) ⋙ coyoneda.obj (op ((H).obj K))

/-- Both full carrier choice functions retain their actual Ho Hom transport. -/
def fiberHoHomChoiceNatIso (K : C) :
    fiberHoHomFunctor Z hZ s hs K ≅ fiberHoHomFunctor Z hZ t ht K :=
  Functor.isoWhiskerRight (choiceNatIso Z hZ s hs t ht)
    ((H) ⋙ coyoneda.obj (op ((H).obj K)))

/-- The entire forward Ho Hom function keeps the original limit-comparison map. -/
theorem fiberHoHomChoiceNatIso_hom (K : C) (F : Arrow C)
    (f : (H).obj K ⟶ (H).obj (s F).pt) :
    (fiberHoHomChoiceNatIso Z hZ s hs t ht K).hom.app F f =
      f ≫ (H).map (choiceIso Z hZ s hs t ht F).hom := rfl

/-- The entire inverse Ho Hom function keeps the original inverse limit-comparison map. -/
theorem fiberHoHomChoiceNatIso_inv (K : C) (F : Arrow C)
    (f : (H).obj K ⟶ (H).obj (t F).pt) :
    (fiberHoHomChoiceNatIso Z hZ s hs t ht K).inv.app F f =
      f ≫ (H).map (choiceIso Z hZ s hs t ht F).inv := rfl

/-- The complete forward and inverse Ho functions cancel on the original source carrier. -/
theorem fiberHoHomChoiceNatIso_hom_inv (K : C) (F : Arrow C)
    (f : (H).obj K ⟶ (H).obj (s F).pt) :
    (fiberHoHomChoiceNatIso Z hZ s hs t ht K).inv.app F
      ((fiberHoHomChoiceNatIso Z hZ s hs t ht K).hom.app F f) = f :=
  ConcreteCategory.congr_hom (((fiberHoHomChoiceNatIso Z hZ s hs t ht K).app F).hom_inv_id) f

/-- The complete inverse and forward Ho functions cancel on the other original carrier. -/
theorem fiberHoHomChoiceNatIso_inv_hom (K : C) (F : Arrow C)
    (f : (H).obj K ⟶ (H).obj (t F).pt) :
    (fiberHoHomChoiceNatIso Z hZ s hs t ht K).hom.app F
      ((fiberHoHomChoiceNatIso Z hZ s hs t ht K).inv.app F f) = f :=
  ConcreteCategory.congr_hom (((fiberHoHomChoiceNatIso Z hZ s hs t ht K).app F).inv_hom_id) f

/-- The actual eligible Arrow property retains both fibration and fibrant-base witnesses. -/
def fibrantFibrationProperty : ObjectProperty (Arrow C) :=
  fun F => Fibration F.hom ∧ IsFibrant F.right

/-- The full ordinary Ho first-leg function maps actual eligible arrows into their null-fibers. -/
def firstLegNullNatTrans (K : C) :
    (fibrantFibrationProperty (C := C)).ι ⋙ fiberHoHomFunctor Z hZ s hs K ⟶
      (fibrantFibrationProperty (C := C)).ι ⋙ nullFiberFunctor Z hZ K where
  app F := TypeCat.ofHom fun f => ⟨f ≫ (H).map (s F.obj).fst, by
    let : Fibration F.obj.hom := F.property.1
    let : IsFibrant F.obj.right := F.property.2
    have h := OrdinaryHoChosenFiberKernel.chosenFiberHoImage_eq_nullFiber_anyCoefficient
      Z hZ K F.obj.hom (s F.obj) (hs F.obj)
    exact (Set.ext_iff.mp h _).mp ⟨f, rfl⟩⟩
  naturality {F G} q := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    change (f ≫ (H).map (chosenMap Z hZ s hs q.hom)) ≫
      (H).map (s G.obj).fst =
        (f ≫ (H).map (s F.obj).fst) ≫ (H).map q.hom.left
    exact actualMappedSquare (H) (chosenMap Z hZ s hs q.hom) (s G.obj).fst
      (s F.obj).fst q.hom.left (chosenMap_fst Z hZ s hs q.hom) f

/-- Every actual fibration-over-fibrant-base component is surjective for every coefficient. -/
theorem firstLegNullNatTrans_surjective (K : C)
    (F : (fibrantFibrationProperty (C := C)).FullSubcategory) :
    Function.Surjective ((firstLegNullNatTrans Z hZ s hs K).app F) := by
  let : Fibration F.obj.hom := F.property.1
  let : IsFibrant F.obj.right := F.property.2
  intro f
  obtain ⟨g, hg⟩ :=
    (OrdinaryHoChosenFiberKernel.chosenFiberHoImage_anyCoefficient_iff Z hZ K F.obj.hom
      (s F.obj) (hs F.obj) f.val).2 f.property
  exact ⟨g, Subtype.ext hg⟩

/-- The two full carrier choices give the same actual first-leg transformation after transport. -/
theorem firstLegNullNatTrans_choice (K : C) :
    (Functor.isoWhiskerLeft (fibrantFibrationProperty (C := C)).ι
        (fiberHoHomChoiceNatIso Z hZ s hs t ht K)).hom ≫
      firstLegNullNatTrans Z hZ t ht K = firstLegNullNatTrans Z hZ s hs K := by
  apply NatTrans.ext
  funext F
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  change (f ≫ (H).map (choiceIso Z hZ s hs t ht F.obj).hom) ≫
    (H).map (t F.obj).fst = f ≫ (H).map (s F.obj).fst
  exact actualMappedProjection (H) (choiceIso Z hZ s hs t ht F.obj).hom
    (t F.obj).fst (s F.obj).fst (choiceIso_hom_fst Z hZ s hs t ht F.obj) f

end Ho

end HomotopicalAlgebra.OrdinaryHoChosenFiberMaps
