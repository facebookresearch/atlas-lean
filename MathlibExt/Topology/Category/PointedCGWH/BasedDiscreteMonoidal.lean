/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.BasedDiscreteTensor
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The braided monoidal based-discrete functor

The based-discrete functor from types to pointed CGWH spaces is strong monoidal for
cartesian product and smash product. Its pair injections determine maps from tensor
products and prove the naturality, associativity, unit and braiding equations of the
explicit unit and tensorator isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace PointedCGWH

private def unitPair {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {X Y : C} (x : 𝟙_ C ⟶ X) (y : 𝟙_ C ⟶ Y) : 𝟙_ C ⟶ X ⊗ Y :=
  (λ_ (𝟙_ C)).inv ≫ (x ⊗ₘ y)

private theorem unitPair_natural {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {X Y X' Y' : C} (x : 𝟙_ C ⟶ X) (y : 𝟙_ C ⟶ Y)
    (f : X ⟶ X') (g : Y ⟶ Y') :
    unitPair x y ≫ (f ⊗ₘ g) = unitPair (x ≫ f) (y ≫ g) := by
  dsimp only [unitPair]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => (λ_ (𝟙_ C)).inv ≫ q)
      (tensorHom_comp_tensorHom x y f g))

private theorem unitPair_assoc {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {X Y Z : C} (x : 𝟙_ C ⟶ X) (y : 𝟙_ C ⟶ Y) (z : 𝟙_ C ⟶ Z) :
    unitPair (unitPair x y) z ≫ (α_ X Y Z).hom = unitPair x (unitPair y z) := by
  let U : C := 𝟙_ C
  let d : U ⟶ U ⊗ U := (λ_ U).inv
  have hStruct : d ≫ (d ▷ U) ≫ (α_ U U U).hom = d ≫ (U ◁ d) := by
    dsimp only [d, U]
    monoidal
  have hNat := associator_naturality x y z
  change (d ≫ ((d ≫ (x ⊗ₘ y)) ⊗ₘ z)) ≫ (α_ X Y Z).hom =
    d ≫ (x ⊗ₘ (d ≫ (y ⊗ₘ z)))
  have hLeft : (d ≫ (x ⊗ₘ y)) ⊗ₘ z =
      (d ▷ U) ≫ ((x ⊗ₘ y) ⊗ₘ z) := by
    rw [← tensorHom_id]
    exact ((congrArg (fun q => (d ≫ (x ⊗ₘ y)) ⊗ₘ q)
      (Category.id_comp z).symm).trans
        (tensorHom_comp_tensorHom d (𝟙 U) (x ⊗ₘ y) z).symm)
  have hRight : x ⊗ₘ (d ≫ (y ⊗ₘ z)) =
      (U ◁ d) ≫ (x ⊗ₘ (y ⊗ₘ z)) := by
    rw [← id_tensorHom]
    exact ((congrArg (fun q => q ⊗ₘ (d ≫ (y ⊗ₘ z)))
      (Category.id_comp x).symm).trans
        (tensorHom_comp_tensorHom (𝟙 U) d x (y ⊗ₘ z)).symm)
  rw [hLeft, hRight]
  have hNatPre := congrArg (fun q => d ≫ (d ▷ U) ≫ q) hNat
  have hStructPost := congrArg (fun q => q ≫ (x ⊗ₘ (y ⊗ₘ z))) hStruct
  have hStep :
      (d ≫ ((d ▷ U) ≫ ((x ⊗ₘ y) ⊗ₘ z))) ≫ (α_ X Y Z).hom =
        d ≫ (d ▷ U) ≫ (α_ U U U).hom ≫ (x ⊗ₘ (y ⊗ₘ z)) := by
    simpa only [Category.assoc] using hNatPre
  have hEnd : d ≫ (d ▷ U) ≫ (α_ U U U).hom ≫ (x ⊗ₘ (y ⊗ₘ z)) =
      d ≫ ((U ◁ d) ≫ (x ⊗ₘ (y ⊗ₘ z))) := by
    simpa only [Category.assoc] using hStructPost
  exact hStep.trans hEnd

private theorem unitPair_left {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {X : C} (x : 𝟙_ C ⟶ X) : unitPair (𝟙 (𝟙_ C)) x ≫ (λ_ X).hom = x := by
  dsimp only [unitPair]
  rw [id_tensorHom, Category.assoc, leftUnitor_naturality,
    Iso.inv_hom_id_assoc]

private theorem unitPair_right {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {X : C} (x : 𝟙_ C ⟶ X) : unitPair x (𝟙 (𝟙_ C)) ≫ (ρ_ X).hom = x := by
  let U : C := 𝟙_ C
  have hUnit : (λ_ U).inv ≫ (ρ_ U).hom = 𝟙 U := by
    dsimp only [U]
    monoidal
  dsimp only [unitPair]
  rw [tensorHom_id, Category.assoc, rightUnitor_naturality]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ x) hUnit).trans (Category.id_comp x))

private theorem unitPair_braiding {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C] {X Y : C} (x : 𝟙_ C ⟶ X) (y : 𝟙_ C ⟶ Y) :
    unitPair x y ≫ (β_ X Y).hom = unitPair y x := by
  let U : C := 𝟙_ C
  have hUnit : (λ_ U).inv ≫ (β_ U U).hom = (λ_ U).inv := by
    rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc]
    have h : (ρ_ U).inv = (λ_ U).inv := by
      dsimp only [U]
      monoidal
    exact h
  dsimp only [unitPair]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => (λ_ U).inv ≫ q) (BraidedCategory.braiding_naturality x y)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ (y ⊗ₘ x)) hUnit)))

/-- Maps out of the actual tensor of based-discrete objects are determined by pair injections. -/
theorem basedDiscretePair_hom_ext (E F : Type w) {Y : PointedCGWH.{u, max v w}}
    {f g : basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F ⟶ Y}
    (h : ∀ e f', basedDiscretePairIncl.{u, v, w} E F e f' ≫ f =
      basedDiscretePairIncl.{u, v, w} E F e f' ≫ g) : f = g := by
  apply discreteSmash_hom_ext.{u, v, w} E (basedDiscreteObj.{u, v, w} F)
  intro e
  apply Cofan.IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} F)
  intro j
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let i : U ⟶ basedDiscreteObj.{u, v, w} F := basedDiscreteIncl.{u, v, w} F j
  let d := discreteSmashIncl.{u, v, w} E (basedDiscreteObj.{u, v, w} F) e
  have hp : basedDiscretePairIncl.{u, v, w} E F e j ≫ f =
      basedDiscretePairIncl.{u, v, w} E F e j ≫ g := h e j
  have hPair : basedDiscretePairIncl.{u, v, w} E F e j = i ≫ d :=
    basedDiscretePairIncl_eq.{u, v, w} E F e j
  have hL := congrArg (fun q => q ≫ f) hPair
  have hR := congrArg (fun q => q ≫ g) hPair
  change i ≫ (d ≫ f) = i ≫ (d ≫ g)
  exact (Category.assoc i d f).symm.trans
    (hL.symm.trans (hp.trans (hR.trans (Category.assoc i d g))))

/-- The actual pair injection is natural in both index maps. -/
theorem basedDiscretePairIncl_natural {E E' F F' : Type w}
    (a : E ⟶ E') (b : F ⟶ F') (e : E) (f : F) :
    basedDiscretePairIncl.{u, v, w} E F e f ≫
        (basedDiscreteFunctor.{u, v, w}.map a ⊗ₘ basedDiscreteFunctor.{u, v, w}.map b) =
      basedDiscretePairIncl.{u, v, w} E' F' (a e) (b f) := by
  have ha : basedDiscreteIncl.{u, v, w} E e ≫ basedDiscreteFunctor.{u, v, w}.map a =
      basedDiscreteIncl.{u, v, w} E' (a e) :=
    basedDiscreteIncl_naturality.{u, v, w} (fun x => a x) e
  have hb : basedDiscreteIncl.{u, v, w} F f ≫ basedDiscreteFunctor.{u, v, w}.map b =
      basedDiscreteIncl.{u, v, w} F' (b f) :=
    basedDiscreteIncl_naturality.{u, v, w} (fun y => b y) f
  change unitPair (basedDiscreteIncl.{u, v, w} E e) (basedDiscreteIncl.{u, v, w} F f) ≫
      (basedDiscreteFunctor.{u, v, w}.map a ⊗ₘ basedDiscreteFunctor.{u, v, w}.map b) =
    unitPair (basedDiscreteIncl.{u, v, w} E' (a e)) (basedDiscreteIncl.{u, v, w} F' (b f))
  exact (unitPair_natural _ _ _ _).trans (congrArg₂ unitPair ha hb)

/-- The original tensorator is natural in both actual Type-category arrows. -/
theorem basedDiscreteTensorProductHom_natural {E E' F F' : Type w}
    (a : E ⟶ E') (b : F ⟶ F') :
    (basedDiscreteFunctor.{u, v, w}.map a ⊗ₘ basedDiscreteFunctor.{u, v, w}.map b) ≫
        basedDiscreteTensorProductHom.{u, v, w} E' F' =
      basedDiscreteTensorProductHom.{u, v, w} E F ≫
        basedDiscreteFunctor.{u, v, w}.map (a ⊗ₘ b) := by
  let m : basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F ⟶
      basedDiscreteObj.{u, v, w} E' ⊗ basedDiscreteObj.{u, v, w} F' :=
    basedDiscreteFunctor.{u, v, w}.map a ⊗ₘ basedDiscreteFunctor.{u, v, w}.map b
  let t : basedDiscreteObj.{u, v, w} (E × F) ⟶ basedDiscreteObj.{u, v, w} (E' × F') :=
    basedDiscreteFunctor.{u, v, w}.map (a ⊗ₘ b)
  change m ≫ basedDiscreteTensorProductHom.{u, v, w} E' F' =
    basedDiscreteTensorProductHom.{u, v, w} E F ≫ t
  apply basedDiscretePair_hom_ext.{u, v, w} E F
  intro e f
  have hm : basedDiscretePairIncl.{u, v, w} E F e f ≫ m =
      basedDiscretePairIncl.{u, v, w} E' F' (a e) (b f) :=
    basedDiscretePairIncl_natural.{u, v, w} a b e f
  have hL := congrArg
    (fun q => q ≫ basedDiscreteTensorProductHom.{u, v, w} E' F') hm
  have hR := congrArg (fun q => q ≫ t)
    (basedDiscreteTensorProductHom_pair.{u, v, w} E F e f)
  have hn : basedDiscreteIncl.{u, v, w} (E × F) (e, f) ≫ t =
      basedDiscreteIncl.{u, v, w} (E' × F') (a e, b f) :=
    basedDiscreteIncl_naturality.{u, v, w}
      (fun p => (a ⊗ₘ b) p) (e, f)
  have hLeft : basedDiscretePairIncl.{u, v, w} E F e f ≫
      (m ≫ basedDiscreteTensorProductHom.{u, v, w} E' F') =
        basedDiscreteIncl.{u, v, w} (E' × F') (a e, b f) :=
    (Category.assoc _ _ _).symm.trans
      (hL.trans (basedDiscreteTensorProductHom_pair.{u, v, w} E' F' (a e) (b f)))
  have hRight : basedDiscretePairIncl.{u, v, w} E F e f ≫
      (basedDiscreteTensorProductHom.{u, v, w} E F ≫ t) =
        basedDiscreteIncl.{u, v, w} (E' × F') (a e, b f) :=
    (Category.assoc _ _ _).symm.trans (hR.trans hn)
  exact hLeft.trans hRight.symm

/-- The actual native tensorator satisfies the standard strong-functor associativity law. -/
theorem basedDiscreteTensorProductHom_associativity (E F G : Type w) :
    basedDiscreteTensorProductHom.{u, v, w} E F ▷ basedDiscreteObj.{u, v, w} G ≫
        basedDiscreteTensorProductHom.{u, v, w} (E ⊗ F) G ≫
          basedDiscreteFunctor.{u, v, w}.map (α_ E F G).hom =
      (α_ (basedDiscreteObj.{u, v, w} E) (basedDiscreteObj.{u, v, w} F)
          (basedDiscreteObj.{u, v, w} G)).hom ≫
        basedDiscreteObj.{u, v, w} E ◁ basedDiscreteTensorProductHom.{u, v, w} F G ≫
          basedDiscreteTensorProductHom.{u, v, w} E (F ⊗ G) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let XE := basedDiscreteObj.{u, v, w} E
  let XF := basedDiscreteObj.{u, v, w} F
  let XG := basedDiscreteObj.{u, v, w} G
  let XEF := basedDiscreteObj.{u, v, w} (E × F)
  let XEFG := basedDiscreteObj.{u, v, w} ((E × F) × G)
  let XFG := basedDiscreteObj.{u, v, w} (F × G)
  let XTarget := basedDiscreteObj.{u, v, w} (E × (F × G))
  let t : XEFG ⟶ XTarget := basedDiscreteFunctor.{u, v, w}.map (α_ E F G).hom
  let muEF : XE ⊗ XF ⟶ XEF := basedDiscreteTensorProductHom.{u, v, w} E F
  let invEF : XEF ⟶ XE ⊗ XF := (basedDiscreteTensorProductIso.{u, v, w} E F).inv
  let muFG : XF ⊗ XG ⟶ XFG := basedDiscreteTensorProductHom.{u, v, w} F G
  let left : XEF ⊗ XG ⟶ XTarget :=
    basedDiscreteTensorProductHom.{u, v, w} (E × F) G ≫ t
  let right : (XE ⊗ XF) ⊗ XG ⟶ XTarget := (α_ XE XF XG).hom ≫ XE ◁ muFG ≫
    basedDiscreteTensorProductHom.{u, v, w} E (F ⊗ G)
  have hIso : invEF ≫ muEF = 𝟙 XEF :=
    (basedDiscreteTensorProductIso.{u, v, w} E F).inv_hom_id
  have hWhisker : (invEF ▷ XG) ≫ (muEF ▷ XG) = 𝟙 (XEF ⊗ XG) :=
    ((comp_whiskerRight invEF muEF XG).symm.trans
      ((congrArg (fun q => q ▷ XG) hIso).trans (id_whiskerRight XEF XG)))
  have hCancel : (invEF ▷ XG) ≫ ((muEF ▷ XG) ≫ left) = left :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ left) hWhisker).trans (Category.id_comp left))
  change (muEF ▷ XG) ≫ left = right
  apply (cancel_epi (invEF ▷ XG)).1
  refine hCancel.trans ?_
  apply basedDiscretePair_hom_ext.{u, v, w} (E × F) G
  intro p g
  rcases p with ⟨e, f⟩
  let iE : U ⟶ XE := basedDiscreteIncl.{u, v, w} E e
  let iF : U ⟶ XF := basedDiscreteIncl.{u, v, w} F f
  let iG : U ⟶ XG := basedDiscreteIncl.{u, v, w} G g
  have hInv : basedDiscreteIncl.{u, v, w} (E × F) (e, f) ≫
      (basedDiscreteTensorProductIso.{u, v, w} E F).inv = unitPair iE iF :=
    basedDiscreteTensorProductInv_pair.{u, v, w} E F e f
  have hLeft : basedDiscretePairIncl.{u, v, w} (E × F) G (e, f) g ≫ left =
      basedDiscreteIncl.{u, v, w} (E × (F × G)) (e, (f, g)) := by
    have hGenerator := congrArg (fun q => q ≫ t)
      (basedDiscreteTensorProductHom_pair.{u, v, w} (E × F) G (e, f) g)
    have hIndex : basedDiscreteIncl.{u, v, w} ((E × F) × G) ((e, f), g) ≫ t =
        basedDiscreteIncl.{u, v, w} (E × (F × G)) (e, (f, g)) :=
      basedDiscreteIncl_naturality.{u, v, w}
        (fun q => (α_ E F G).hom q) ((e, f), g)
    exact (Category.assoc _ _ _).symm.trans (hGenerator.trans hIndex)
  have hReindex : basedDiscretePairIncl.{u, v, w} (E × F) G (e, f) g ≫
      ((basedDiscreteTensorProductIso.{u, v, w} E F).inv ▷ XG) =
      unitPair (unitPair iE iF) iG := by
    have hNatural : unitPair (basedDiscreteIncl.{u, v, w} (E × F) (e, f)) iG ≫
        (invEF ⊗ₘ 𝟙 XG) = unitPair (unitPair iE iF) iG :=
      (unitPair_natural _ _ _ _).trans
        (congrArg₂ unitPair hInv (Category.comp_id iG))
    exact (congrArg (fun q =>
      basedDiscretePairIncl.{u, v, w} (E × F) G (e, f) g ≫ q)
      (tensorHom_id invEF XG)).symm.trans hNatural
  have hAssoc : unitPair (unitPair iE iF) iG ≫ (α_ XE XF XG).hom =
      unitPair iE (unitPair iF iG) := unitPair_assoc iE iF iG
  have hFG : unitPair iF iG ≫ muFG =
      basedDiscreteIncl.{u, v, w} (F × G) (f, g) :=
    basedDiscreteTensorProductHom_pair.{u, v, w} F G f g
  have hTensor : unitPair iE (unitPair iF iG) ≫ (XE ◁ muFG) =
      basedDiscretePairIncl.{u, v, w} E (F × G) e (f, g) := by
    have hNatural : unitPair iE (unitPair iF iG) ≫ (𝟙 XE ⊗ₘ muFG) =
        unitPair iE (basedDiscreteIncl.{u, v, w} (F × G) (f, g)) :=
      (unitPair_natural _ _ _ _).trans
        (congrArg₂ unitPair (Category.comp_id iE) hFG)
    exact (congrArg (fun q => unitPair iE (unitPair iF iG) ≫ q)
      (id_tensorHom XE muFG)).symm.trans hNatural
  have hTarget : basedDiscretePairIncl.{u, v, w} (E × F) G (e, f) g ≫
      ((basedDiscreteTensorProductIso.{u, v, w} E F).inv ▷ XG) ≫ right =
        basedDiscreteIncl.{u, v, w} (E × (F × G)) (e, (f, g)) := by
    dsimp only [right]
    let final := basedDiscreteTensorProductHom.{u, v, w} E (F × G)
    have hStart : basedDiscretePairIncl.{u, v, w} (E × F) G (e, f) g ≫
        (invEF ▷ XG) ≫ (α_ XE XF XG).hom ≫ (XE ◁ muFG) ≫ final =
      unitPair (unitPair iE iF) iG ≫ (α_ XE XF XG).hom ≫ (XE ◁ muFG) ≫ final := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (α_ XE XF XG).hom ≫ (XE ◁ muFG) ≫ final) hReindex
    have hMiddle : unitPair (unitPair iE iF) iG ≫
        (α_ XE XF XG).hom ≫ (XE ◁ muFG) ≫ final =
      unitPair iE (unitPair iF iG) ≫ (XE ◁ muFG) ≫ final := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ (XE ◁ muFG) ≫ final) hAssoc
    have hLast : unitPair iE (unitPair iF iG) ≫ (XE ◁ muFG) ≫ final =
        basedDiscretePairIncl.{u, v, w} E (F × G) e (f, g) ≫ final := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ final) hTensor
    exact hStart.trans (hMiddle.trans
      (hLast.trans (basedDiscreteTensorProductHom_pair.{u, v, w} E (F × G) e (f, g))))
  exact hLeft.trans hTarget.symm

/-- The actual singleton injection supplies the standard left-unit tensorator law. -/
theorem basedDiscreteTensorProductHom_left_unitality (E : Type w) :
    (λ_ (basedDiscreteObj.{u, v, w} E)).hom =
      (basedDiscreteUnitIso.{u, v, w}).hom ▷ basedDiscreteObj.{u, v, w} E ≫
        basedDiscreteTensorProductHom.{u, v, w} (𝟙_ (Type w)) E ≫
          basedDiscreteFunctor.{u, v, w}.map (λ_ E).hom := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let XE := basedDiscreteObj.{u, v, w} E
  let t : basedDiscreteObj.{u, v, w} (PUnit.{w + 1} × E) ⟶ XE :=
    basedDiscreteFunctor.{u, v, w}.map (λ_ E).hom
  let m := basedDiscreteTensorProductHom.{u, v, w} PUnit.{w + 1} E
  let epsilon : U ⟶ basedDiscreteObj.{u, v, w} PUnit.{w + 1} :=
    basedDiscreteUnitIso.{u, v, w}.hom
  change (λ_ XE).hom = (epsilon ▷ XE) ≫ m ≫ t
  apply (cancel_epi (λ_ XE).inv).1
  apply Cofan.IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} E)
  intro j
  let i : U ⟶ XE := basedDiscreteIncl.{u, v, w} E j
  have hPair : unitPair (𝟙 U) i ≫
      ((basedDiscreteUnitIso.{u, v, w}).hom ▷ XE) =
      basedDiscretePairIncl.{u, v, w} (𝟙_ (Type w)) E PUnit.unit j := by
    rw [← tensorHom_id]
    exact (unitPair_natural _ _ _ _).trans
      (congrArg₂ unitPair (Category.id_comp _) (Category.comp_id i))
  have hLeft : unitPair (𝟙 U) i ≫ (λ_ XE).hom = i := unitPair_left i
  have hRight : basedDiscretePairIncl.{u, v, w} (𝟙_ (Type w)) E PUnit.unit j ≫
      m ≫ t = i := by
    have hGenerator := congrArg (fun q => q ≫ t)
      (basedDiscreteTensorProductHom_pair.{u, v, w} PUnit.{w + 1} E PUnit.unit j)
    have hIndex : basedDiscreteIncl.{u, v, w} (PUnit.{w + 1} × E) (PUnit.unit, j) ≫ t = i :=
      basedDiscreteIncl_naturality.{u, v, w}
        (fun p => (λ_ E).hom p) (PUnit.unit, j)
    exact (Category.assoc _ _ _).symm.trans (hGenerator.trans hIndex)
  have hUnit : i ≫ (λ_ XE).inv = unitPair (𝟙 U) i := by
    apply (cancel_mono (λ_ XE).hom).1
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun q => i ≫ q) (Iso.inv_hom_id (λ_ XE))).trans
        (Category.comp_id i))).trans hLeft.symm
  have hReindex : i ≫ (λ_ XE).inv ≫ (epsilon ▷ XE) ≫ m ≫ t =
      unitPair (𝟙 U) i ≫ (epsilon ▷ XE) ≫ m ≫ t := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ (epsilon ▷ XE) ≫ m ≫ t) hUnit
  have hGenerator : unitPair (𝟙 U) i ≫ (epsilon ▷ XE) ≫ m ≫ t =
      basedDiscretePairIncl.{u, v, w} PUnit.{w + 1} E PUnit.unit j ≫ m ≫ t := by
    simpa only [epsilon, CategoryTheory.types_tensorUnit_def, Category.assoc] using
      congrArg (fun q => q ≫ m ≫ t) hPair
  have hResult : i ≫ (λ_ XE).inv ≫ (epsilon ▷ XE) ≫ m ≫ t = i :=
    hReindex.trans (hGenerator.trans hRight)
  have hCancel : i ≫ (λ_ XE).inv ≫ (λ_ XE).hom = i :=
    (congrArg (fun q => i ≫ q) (Iso.inv_hom_id (λ_ XE))).trans (Category.comp_id i)
  exact hCancel.trans hResult.symm

/-- The actual singleton injection supplies the standard right-unit tensorator law. -/
theorem basedDiscreteTensorProductHom_right_unitality (E : Type w) :
    (ρ_ (basedDiscreteObj.{u, v, w} E)).hom =
      basedDiscreteObj.{u, v, w} E ◁ (basedDiscreteUnitIso.{u, v, w}).hom ≫
        basedDiscreteTensorProductHom.{u, v, w} E (𝟙_ (Type w)) ≫
          basedDiscreteFunctor.{u, v, w}.map (ρ_ E).hom := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let XE := basedDiscreteObj.{u, v, w} E
  let t : basedDiscreteObj.{u, v, w} (E × PUnit.{w + 1}) ⟶ XE :=
    basedDiscreteFunctor.{u, v, w}.map (ρ_ E).hom
  let m := basedDiscreteTensorProductHom.{u, v, w} E PUnit.{w + 1}
  let epsilon : U ⟶ basedDiscreteObj.{u, v, w} PUnit.{w + 1} :=
    basedDiscreteUnitIso.{u, v, w}.hom
  change (ρ_ XE).hom = (XE ◁ epsilon) ≫ m ≫ t
  apply (cancel_epi (ρ_ XE).inv).1
  apply Cofan.IsColimit.hom_ext (basedDiscreteCofanIsColimit.{u, v, w} E)
  intro j
  let i : U ⟶ XE := basedDiscreteIncl.{u, v, w} E j
  have hPair : unitPair i (𝟙 U) ≫
      (XE ◁ (basedDiscreteUnitIso.{u, v, w}).hom) =
      basedDiscretePairIncl.{u, v, w} E (𝟙_ (Type w)) j PUnit.unit := by
    rw [← id_tensorHom]
    exact (unitPair_natural _ _ _ _).trans
      (congrArg₂ unitPair (Category.comp_id i) (Category.id_comp _))
  have hLeft : unitPair i (𝟙 U) ≫ (ρ_ XE).hom = i := unitPair_right i
  have hRight : basedDiscretePairIncl.{u, v, w} E (𝟙_ (Type w)) j PUnit.unit ≫
      m ≫ t = i := by
    have hGenerator := congrArg (fun q => q ≫ t)
      (basedDiscreteTensorProductHom_pair.{u, v, w} E PUnit.{w + 1} j PUnit.unit)
    have hIndex : basedDiscreteIncl.{u, v, w} (E × PUnit.{w + 1}) (j, PUnit.unit) ≫ t = i :=
      basedDiscreteIncl_naturality.{u, v, w}
        (fun p => (ρ_ E).hom p) (j, PUnit.unit)
    exact (Category.assoc _ _ _).symm.trans (hGenerator.trans hIndex)
  have hUnit : i ≫ (ρ_ XE).inv = unitPair i (𝟙 U) := by
    apply (cancel_mono (ρ_ XE).hom).1
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun q => i ≫ q) (Iso.inv_hom_id (ρ_ XE))).trans
        (Category.comp_id i))).trans hLeft.symm
  have hReindex : i ≫ (ρ_ XE).inv ≫ (XE ◁ epsilon) ≫ m ≫ t =
      unitPair i (𝟙 U) ≫ (XE ◁ epsilon) ≫ m ≫ t := by
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ (XE ◁ epsilon) ≫ m ≫ t) hUnit
  have hGenerator : unitPair i (𝟙 U) ≫ (XE ◁ epsilon) ≫ m ≫ t =
      basedDiscretePairIncl.{u, v, w} E PUnit.{w + 1} j PUnit.unit ≫ m ≫ t := by
    simpa only [epsilon, CategoryTheory.types_tensorUnit_def, Category.assoc] using
      congrArg (fun q => q ≫ m ≫ t) hPair
  have hResult : i ≫ (ρ_ XE).inv ≫ (XE ◁ epsilon) ≫ m ≫ t = i :=
    hReindex.trans (hGenerator.trans hRight)
  have hCancel : i ≫ (ρ_ XE).inv ≫ (ρ_ XE).hom = i :=
    (congrArg (fun q => i ≫ q) (Iso.inv_hom_id (ρ_ XE))).trans (Category.comp_id i)
  exact hCancel.trans hResult.symm

/-- The actual native braiding sends the original ordered-pair generator to its swapped pair. -/
theorem basedDiscretePairIncl_braiding (E F : Type w) (e : E) (f : F) :
    basedDiscretePairIncl.{u, v, w} E F e f ≫
        (β_ (basedDiscreteObj.{u, v, w} E) (basedDiscreteObj.{u, v, w} F)).hom =
      basedDiscretePairIncl.{u, v, w} F E f e :=
  unitPair_braiding (basedDiscreteIncl.{u, v, w} E e) (basedDiscreteIncl.{u, v, w} F f)

/-- The original tensorator respects the actual Type and native smash braidings. -/
theorem basedDiscreteTensorProductHom_braiding (E F : Type w) :
    basedDiscreteTensorProductHom.{u, v, w} E F ≫
        basedDiscreteFunctor.{u, v, w}.map (β_ E F).hom =
      (β_ (basedDiscreteObj.{u, v, w} E) (basedDiscreteObj.{u, v, w} F)).hom ≫
        basedDiscreteTensorProductHom.{u, v, w} F E := by
  let t : basedDiscreteObj.{u, v, w} (E × F) ⟶ basedDiscreteObj.{u, v, w} (F × E) :=
    basedDiscreteFunctor.{u, v, w}.map (β_ E F).hom
  let b : basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F ⟶
      basedDiscreteObj.{u, v, w} F ⊗ basedDiscreteObj.{u, v, w} E :=
    (β_ (basedDiscreteObj.{u, v, w} E) (basedDiscreteObj.{u, v, w} F)).hom
  change basedDiscreteTensorProductHom.{u, v, w} E F ≫ t =
    b ≫ basedDiscreteTensorProductHom.{u, v, w} F E
  apply basedDiscretePair_hom_ext.{u, v, w} E F
  intro e f
  have hLeft : basedDiscretePairIncl.{u, v, w} E F e f ≫
      basedDiscreteTensorProductHom.{u, v, w} E F ≫ t =
      basedDiscreteIncl.{u, v, w} (F × E) (f, e) := by
    have hGenerator := congrArg (fun q => q ≫ t)
      (basedDiscreteTensorProductHom_pair.{u, v, w} E F e f)
    have hIndex : basedDiscreteIncl.{u, v, w} (E × F) (e, f) ≫ t =
        basedDiscreteIncl.{u, v, w} (F × E) (f, e) :=
      basedDiscreteIncl_naturality.{u, v, w}
        (fun p => (β_ E F).hom p) (e, f)
    exact (Category.assoc _ _ _).symm.trans (hGenerator.trans hIndex)
  have hRight : basedDiscretePairIncl.{u, v, w} E F e f ≫
      b ≫
        basedDiscreteTensorProductHom.{u, v, w} F E =
      basedDiscreteIncl.{u, v, w} (F × E) (f, e) := by
    have hGenerator := congrArg
      (fun q => q ≫ basedDiscreteTensorProductHom.{u, v, w} F E)
      (basedDiscretePairIncl_braiding.{u, v, w} E F e f)
    exact (Category.assoc _ _ _).symm.trans
      (hGenerator.trans (basedDiscreteTensorProductHom_pair.{u, v, w} F E f e))
  exact hLeft.trans hRight.symm

/-- The actual existing based-discrete functor with its literal unit and tensorator isomorphisms. -/
def basedDiscreteCoreMonoidal : basedDiscreteFunctor.{u, v, w}.CoreMonoidal where
  εIso := basedDiscreteUnitIso.{u, v, w}
  μIso := basedDiscreteTensorProductIso.{u, v, w}
  μIso_hom_natural_left {X Y} f X' := by
    have h := basedDiscreteTensorProductHom_natural.{u, v, w} f (𝟙 X')
    have hid : basedDiscreteFunctor.{u, v, w}.map (𝟙 X') =
        𝟙 (basedDiscreteFunctor.{u, v, w}.obj X') :=
      basedDiscreteFunctor.{u, v, w}.map_id X'
    have hTensor := congrArg (fun q => basedDiscreteFunctor.{u, v, w}.map f ⊗ₘ q) hid
    have hStart := congrArg (fun q => q ≫ basedDiscreteTensorProductHom.{u, v, w} Y X')
      (hTensor.trans (tensorHom_id _ _))
    exact hStart.symm.trans h
  μIso_hom_natural_right {X Y} X' f := by
    have h := basedDiscreteTensorProductHom_natural.{u, v, w} (𝟙 X') f
    have hid : basedDiscreteFunctor.{u, v, w}.map (𝟙 X') =
        𝟙 (basedDiscreteFunctor.{u, v, w}.obj X') :=
      basedDiscreteFunctor.{u, v, w}.map_id X'
    have hTensor := congrArg (fun q => q ⊗ₘ basedDiscreteFunctor.{u, v, w}.map f) hid
    have hStart := congrArg (fun q => q ≫ basedDiscreteTensorProductHom.{u, v, w} X' Y)
      (hTensor.trans (id_tensorHom _ _))
    exact hStart.symm.trans h
  associativity := basedDiscreteTensorProductHom_associativity.{u, v, w}
  left_unitality := basedDiscreteTensorProductHom_left_unitality.{u, v, w}
  right_unitality := basedDiscreteTensorProductHom_right_unitality.{u, v, w}

/-- The standard Mathlib strong monoidal dictionary derived from the same explicit CoreMonoidal. -/
@[instance_reducible]
def basedDiscreteMonoidal : basedDiscreteFunctor.{u, v, w}.Monoidal :=
  basedDiscreteCoreMonoidal.{u, v, w}.toMonoidal

/-- The standard braided dictionary shares the exact same strong monoidal fields. -/
@[instance_reducible]
def basedDiscreteBraided : basedDiscreteFunctor.{u, v, w}.Braided where
  __ := basedDiscreteMonoidal.{u, v, w}
  braided := basedDiscreteTensorProductHom_braiding.{u, v, w}

end PointedCGWH
