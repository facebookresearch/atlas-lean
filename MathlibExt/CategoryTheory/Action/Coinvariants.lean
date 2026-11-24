/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
-- Author: @toskua

module

public import Mathlib.CategoryTheory.Action
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Coefficient diagrams for pointed coinvariants

An action-category cocone is exactly a family of coefficient maps that
coequalizes the group action with the coefficient action.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u wH wE wG

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ActionCategory

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (E : Type wE) [Monoid H] [MulAction H E]
variable (Z : C) (rho : H →* End Z)

/-- The coefficient action as an actual diagram over the action category. -/
def coefficientDiagram : ActionCategory H E ⥤ C where
  obj _ := Z
  map f := (rho f.hom).asHom
  map_id e := by
    change (rho 1).asHom = 𝟙 Z
    rw [rho.map_one]
    rfl
  map_comp f g := by
    change (rho (g.hom * f.hom)).asHom =
      (rho f.hom).asHom ≫ (rho g.hom).asHom
    rw [rho.map_mul]
    rfl

/-- A cocone's defining relation is the literal coefficient-action equation. -/
theorem coefficientDiagram_cocone_relation
    (c : Cocone (coefficientDiagram H E Z rho))
    {x y : ActionCategory H E} (f : x ⟶ y) :
    (rho f.hom).asHom ≫ c.ι.app y = c.ι.app x := by
  change (coefficientDiagram H E Z rho).map f ≫ c.ι.app y = c.ι.app x
  exact c.w f

/-- A coefficient family coequalizes exactly the action-category arrows. -/
structure CoefficientFamily (Y : C) where
  /-- The coefficient arrow at each original action label. -/
  leg : E → (Z ⟶ Y)
  relation : ∀ (a : H) (e : E),
    (rho a).asHom ≫ leg (a • e) = leg e

/-- The same family gives a genuine cocone over the coefficient diagram. -/
def CoefficientFamily.cocone {Y : C}
    (c : CoefficientFamily H E Z rho Y) :
    Cocone (coefficientDiagram H E Z rho) where
  pt := Y
  ι :=
    { app := fun e => c.leg e.back
      naturality := by
        intro x y f
        change (rho f.hom).asHom ≫ c.leg y.back = c.leg x.back ≫ 𝟙 Y
        have h : f.hom • x.back = y.back := f.map_val
        rw [Category.comp_id]
        exact (congrArg (fun e : E => (rho f.hom).asHom ≫ c.leg e) h).symm.trans
          (c.relation f.hom x.back) }

/-- An equivariant map of indices acts on the actual action-category colimit. -/
def coefficientColimitReindex [HasColimit (coefficientDiagram H E Z rho)]
    (t : E → E) (ht : ∀ (a : H) (e : E), t (a • e) = a • t e) :
    colimit (coefficientDiagram H E Z rho) ⟶ colimit (coefficientDiagram H E Z rho) :=
  colimit.desc (coefficientDiagram H E Z rho)
    (CoefficientFamily.cocone H E Z rho
      { leg := fun e => colimit.ι (coefficientDiagram H E Z rho) (t e : ActionCategory H E)
        relation := by
          intro a e
          rw [ht]
          exact colimit.w (coefficientDiagram H E Z rho)
            (show (t e : ActionCategory H E) ⟶
              ((a • t e : E) : ActionCategory H E) from ⟨a, rfl⟩) })

/-- Action-colimit reindexing sends the literal leg at e to the leg at t(e). -/
theorem coefficientColimitReindex_generator [HasColimit (coefficientDiagram H E Z rho)]
    (t : E → E) (ht : ∀ (a : H) (e : E), t (a • e) = a • t e) (e : E) :
    colimit.ι (coefficientDiagram H E Z rho) (e : ActionCategory H E) ≫
        coefficientColimitReindex H E Z rho t ht =
      colimit.ι (coefficientDiagram H E Z rho) (t e : ActionCategory H E) :=
  colimit.ι_desc _ _

section Coproducts

variable [HasCoproduct (fun _ : E => Z)]
variable [HasCoproduct (fun _ : H × E => Z)]

/-- The first action arrow retains the generator at e. -/
def coefficientSource : (∐ fun _ : H × E => Z) ⟶ ∐ fun _ : E => Z :=
  Sigma.desc (fun ae => Sigma.ι (fun _ : E => Z) ae.2)

/-- The second action arrow applies the coefficient action and changes the index. -/
def coefficientTarget : (∐ fun _ : H × E => Z) ⟶ ∐ fun _ : E => Z :=
  Sigma.desc (fun ae => (rho ae.1).asHom ≫ Sigma.ι (fun _ : E => Z) (ae.1 • ae.2))

/-- The literal coefficient relations coequalize the two coproduct arrows. -/
theorem CoefficientFamily.desc_condition {Y : C}
    (c : CoefficientFamily H E Z rho Y) :
    coefficientSource H E Z ≫ Sigma.desc c.leg =
      coefficientTarget H E Z rho ≫ Sigma.desc c.leg := by
  apply Sigma.hom_ext
  intro ae
  simpa only [coefficientSource, coefficientTarget, Sigma.ι_comp_desc_assoc,
    Category.assoc, Sigma.ι_comp_desc] using (c.relation ae.1 ae.2).symm

/-- A cofork supplies exactly the coefficient relations on its coproduct generators. -/
def coforkCoefficientFamily
    (s : Cofork (coefficientSource H E Z) (coefficientTarget H E Z rho)) :
    CoefficientFamily H E Z rho s.pt where
  leg e := Sigma.ι (fun _ : E => Z) e ≫ s.π
  relation a e := by
    have h := congrArg (fun k => Sigma.ι (fun _ : H × E => Z) (a, e) ≫ k)
      s.condition
    simpa only [coefficientSource, coefficientTarget, Sigma.ι_comp_desc_assoc,
      Category.assoc] using h.symm

/-- Every action-category cocone gives the same coefficient family. -/
def coconeCoefficientFamily (c : Cocone (coefficientDiagram H E Z rho)) :
    CoefficientFamily H E Z rho c.pt where
  leg e := c.ι.app (e : ActionCategory H E)
  relation a e := by
    exact c.w (show (e : ActionCategory H E) ⟶ ((a • e : E) : ActionCategory H E) from
      ⟨a, rfl⟩)

variable [HasCoequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)]

/-- The actual coefficient generator into the coproduct coequalizer. -/
def coefficientGenerator (e : E) :
    Z ⟶ coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) :=
  Sigma.ι (fun _ : E => Z) e ≫
    coequalizer.π (coefficientSource H E Z) (coefficientTarget H E Z rho)

/-- A balanced coefficient family descends through the actual coequalizer. -/
def CoefficientFamily.desc {Y : C} (c : CoefficientFamily H E Z rho Y) :
    coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) ⟶ Y :=
  coequalizer.desc (Sigma.desc c.leg) c.desc_condition

/-- Descent preserves each literal coefficient generator. -/
theorem CoefficientFamily.desc_generator {Y : C}
    (c : CoefficientFamily H E Z rho Y) (e : E) :
    coefficientGenerator H E Z rho e ≫ c.desc = c.leg e := by
  unfold coefficientGenerator CoefficientFamily.desc
  rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]

/-- The actual coequalizer carries the action-category cocone on each coefficient. -/
def coequalizerCoefficientCocone : Cocone (coefficientDiagram H E Z rho) :=
  (coforkCoefficientFamily H E Z rho
    (coequalizer.cofork (coefficientSource H E Z) (coefficientTarget H E Z rho))).cocone

/-- The coproduct coequalizer has the complete action-category colimit universal property. -/
def coequalizerCoefficientIsColimit :
    IsColimit (coequalizerCoefficientCocone H E Z rho) where
  desc c := coequalizer.desc
    (Sigma.desc (coconeCoefficientFamily H E Z rho c).leg)
    (coconeCoefficientFamily H E Z rho c).desc_condition
  fac c e := by
    change (Sigma.ι (fun _ : E => Z) e.back ≫
      coequalizer.π (coefficientSource H E Z) (coefficientTarget H E Z rho)) ≫
      coequalizer.desc (Sigma.desc (coconeCoefficientFamily H E Z rho c).leg)
        (coconeCoefficientFamily H E Z rho c).desc_condition = c.ι.app e
    rw [Category.assoc, coequalizer.π_desc, Sigma.ι_comp_desc]
    change c.ι.app (e.back : ActionCategory H E) = c.ι.app e
    rw [ActionCategory.back_coe]
  uniq c m hm := by
    change coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) ⟶ c.pt at m
    apply coequalizer.hom_ext
    apply Sigma.hom_ext
    intro e
    rw [coequalizer.π_desc, Sigma.ι_comp_desc]
    change Sigma.ι (fun _ : E => Z) e ≫
      coequalizer.π (coefficientSource H E Z) (coefficientTarget H E Z rho) ≫ m =
        c.ι.app (e : ActionCategory H E)
    have he := hm (e : ActionCategory H E)
    change (Sigma.ι (fun _ : E => Z) e ≫
      coequalizer.π (coefficientSource H E Z) (coefficientTarget H E Z rho)) ≫ m =
        c.ι.app (e : ActionCategory H E) at he
    simpa only [Category.assoc] using he

/-- The chosen action colimit and the actual coproduct coequalizer are canonically isomorphic. -/
def coefficientColimitIso [HasColimit (coefficientDiagram H E Z rho)] :
    colimit (coefficientDiagram H E Z rho) ≅
      coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) :=
  (colimit.isColimit (coefficientDiagram H E Z rho)).coconePointUniqueUpToIso
    (coequalizerCoefficientIsColimit H E Z rho)

/-- The comparison identifies each action-colimit leg with its actual coefficient generator. -/
theorem coefficientColimitIso_generator [HasColimit (coefficientDiagram H E Z rho)]
    (e : E) :
    colimit.ι (coefficientDiagram H E Z rho) (e : ActionCategory H E) ≫
        (coefficientColimitIso H E Z rho).hom = coefficientGenerator H E Z rho e := by
  exact (colimit.isColimit (coefficientDiagram H E Z rho)).comp_coconePointUniqueUpToIso_hom
    (coequalizerCoefficientIsColimit H E Z rho) (e : ActionCategory H E)

/-- A map of indices commuting with the action induces a map of coefficient coequalizers. -/
def coefficientCoequalizerReindex (t : E → E)
    (ht : ∀ (a : H) (e : E), t (a • e) = a • t e) :
    coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) ⟶
      coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) :=
  CoefficientFamily.desc H E Z rho
    { leg := fun e => coefficientGenerator H E Z rho (t e)
      relation := by
        intro a e
        rw [ht]
        exact (coforkCoefficientFamily H E Z rho
          (coequalizer.cofork (coefficientSource H E Z)
            (coefficientTarget H E Z rho))).relation a (t e) }

/-- Reindexing acts on the actual coefficient generators. -/
theorem coefficientCoequalizerReindex_generator (t : E → E)
    (ht : ∀ (a : H) (e : E), t (a • e) = a • t e) (e : E) :
    coefficientGenerator H E Z rho e ≫ coefficientCoequalizerReindex H E Z rho t ht =
      coefficientGenerator H E Z rho (t e) :=
  CoefficientFamily.desc_generator H E Z rho _ e

/-- The colimit comparison intertwines every actual equivariant reindexing. -/
theorem coefficientColimitIso_reindex [HasColimit (coefficientDiagram H E Z rho)]
    (t : E → E) (ht : ∀ (a : H) (e : E), t (a • e) = a • t e) :
    coefficientColimitReindex H E Z rho t ht ≫ (coefficientColimitIso H E Z rho).hom =
      (coefficientColimitIso H E Z rho).hom ≫ coefficientCoequalizerReindex H E Z rho t ht := by
  apply colimit.hom_ext
  intro e
  obtain ⟨x, hx⟩ := (ActionCategory.objEquiv H E).surjective e
  rw [← hx]
  let L := colimit (coefficientDiagram H E Z rho)
  let Q := coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)
  let lx : Z ⟶ L := colimit.ι (coefficientDiagram H E Z rho) (x : ActionCategory H E)
  let ltx : Z ⟶ L := colimit.ι (coefficientDiagram H E Z rho) (t x : ActionCategory H E)
  let cmp : L ⟶ Q := (coefficientColimitIso H E Z rho).hom
  let lc : L ⟶ L := coefficientColimitReindex H E Z rho t ht
  let lq : Q ⟶ Q := coefficientCoequalizerReindex H E Z rho t ht
  let qx : Z ⟶ Q := coefficientGenerator H E Z rho x
  let qtx : Z ⟶ Q := coefficientGenerator H E Z rho (t x)
  have hReindex : lx ≫ lc = ltx := coefficientColimitReindex_generator H E Z rho t ht x
  have hCompare : ltx ≫ cmp = qtx := coefficientColimitIso_generator H E Z rho (t x)
  have hSource : lx ≫ cmp = qx := coefficientColimitIso_generator H E Z rho x
  have hTarget : qx ≫ lq = qtx := coefficientCoequalizerReindex_generator H E Z rho t ht x
  have hLeft : (lx ≫ lc) ≫ cmp = qtx :=
    (congrArg (fun f : Z ⟶ L => f ≫ cmp) hReindex).trans hCompare
  have hRight : (lx ≫ cmp) ≫ lq = qtx :=
    (congrArg (fun f : Z ⟶ Q => f ≫ lq) hSource).trans hTarget
  change lx ≫ (lc ≫ cmp) = lx ≫ (cmp ≫ lq)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

end Coproducts

end CategoryTheory.ActionCategory

namespace CategoryTheory.ActionCategory

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (G : Type wG) [Monoid H] [Group G]
variable (Z : C) (rho : H →* End Z) (iota : H →* G)

/-- Inverse right multiplication is an explicitly chosen action, without a global instance. -/
@[instance_reducible]
def inverseRightMulAction : MulAction H G where
  smul a g := g * (iota a)⁻¹
  one_smul g := by
    change g * (iota 1)⁻¹ = g
    rw [iota.map_one, inv_one, mul_one]
  mul_smul a b g := by
    change g * (iota (a * b))⁻¹ = (g * (iota b)⁻¹) * (iota a)⁻¹
    rw [iota.map_mul, mul_inv_rev, mul_assoc]

/-- Full left multiplication commutes with the chosen inverse right action. -/
theorem inverseRightMulAction_left_commute (k : G) (a : H) (g : G) :
    letI := inverseRightMulAction H G iota
    k * (a • g) = a • (k * g) := by
  let _ := inverseRightMulAction H G iota
  exact (mul_assoc k g (iota a)⁻¹).symm

/-- The action coefficient diagram retains the actual inverse right action. -/
def inverseRightCoefficientDiagram :
    letI := inverseRightMulAction H G iota
    ActionCategory H G ⥤ C := by
  letI := inverseRightMulAction H G iota
  exact coefficientDiagram H G Z rho

/-- The chosen action diagram retains the supplied colimit dictionary. -/
private theorem inverseRightHasColimit
    [HasColimit (inverseRightCoefficientDiagram H G Z rho iota)] :
    letI := inverseRightMulAction H G iota
    HasColimit (coefficientDiagram H G Z rho) := by
  let _ := inverseRightMulAction H G iota
  change HasColimit (inverseRightCoefficientDiagram H G Z rho iota)
  infer_instance

/-- The usual balanced source labels identify with inverse-right action labels. -/
def inverseRightIndexEquiv : G × H ≃ H × G where
  toFun ga := (ga.2, ga.1 * iota ga.2)
  invFun ag := (ag.2 * (iota ag.1)⁻¹, ag.1)
  left_inv ga := by rcases ga with ⟨g, a⟩; simp only [mul_assoc, mul_inv_cancel, mul_one]
  right_inv ag := by rcases ag with ⟨a, g⟩; simp only [mul_assoc, inv_mul_cancel, mul_one]

variable [HasCoproduct (fun _ : G => Z)]
variable [HasCoproduct (fun _ : H × G => Z)]

/-- The actual second coproduct arrow of inverse-right balanced coefficients. -/
def inverseRightCoefficientTarget :
    (∐ fun _ : H × G => Z) ⟶ ∐ fun _ : G => Z := by
  letI := inverseRightMulAction H G iota
  exact coefficientTarget H G Z rho

variable [HasCoequalizer (coefficientSource H G Z)
  (inverseRightCoefficientTarget H G Z rho iota)]

/-- The provided pair uses the literal chosen inverse-right coefficient target. -/
private theorem inverseRightHasCoequalizer :
    letI := inverseRightMulAction H G iota
    HasCoequalizer (coefficientSource H G Z) (coefficientTarget H G Z rho) := by
  let _ := inverseRightMulAction H G iota
  change HasCoequalizer (coefficientSource H G Z) (inverseRightCoefficientTarget H G Z rho iota)
  infer_instance

/-- The actual coproduct coequalizer of the two coefficient-action arrows. -/
abbrev inverseRightCoinvariants : C :=
  coequalizer (coefficientSource H G Z) (inverseRightCoefficientTarget H G Z rho iota)

/-- The coefficient generator into the actual balanced coproduct coequalizer. -/
def inverseRightGenerator (g : G) : Z ⟶ inverseRightCoinvariants H G Z rho iota :=
  Sigma.ι (fun _ : G => Z) g ≫
    coequalizer.π (coefficientSource H G Z) (inverseRightCoefficientTarget H G Z rho iota)

/-- The actual inverse-right action colimit identifies with its coefficient coequalizer. -/
def inverseRightColimitIso [HasColimit (inverseRightCoefficientDiagram H G Z rho iota)] :
    colimit (inverseRightCoefficientDiagram H G Z rho iota) ≅
      inverseRightCoinvariants H G Z rho iota := by
  letI := inverseRightMulAction H G iota
  let _ : HasCoequalizer (coefficientSource H G Z) (coefficientTarget H G Z rho) := by
    change HasCoequalizer (coefficientSource H G Z)
      (inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  let _ : HasColimit (coefficientDiagram H G Z rho) := by
    change HasColimit (inverseRightCoefficientDiagram H G Z rho iota)
    infer_instance
  exact coefficientColimitIso H G Z rho

/-- Full left multiplication descends through the actual coefficient coequalizer. -/
def inverseRightLeftMap (k : G) :
    inverseRightCoinvariants H G Z rho iota ⟶ inverseRightCoinvariants H G Z rho iota := by
  letI := inverseRightMulAction H G iota
  let _ : HasCoequalizer (coefficientSource H G Z) (coefficientTarget H G Z rho) := by
    change HasCoequalizer (coefficientSource H G Z)
      (inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  exact coefficientCoequalizerReindex H G Z rho (fun g => k * g)
    (inverseRightMulAction_left_commute H G iota k)

/-- Descended left multiplication retains the literal group-index generator. -/
theorem inverseRightLeftMap_generator (k g : G) :
    inverseRightGenerator H G Z rho iota g ≫ inverseRightLeftMap H G Z rho iota k =
      inverseRightGenerator H G Z rho iota (k * g) := by
  let _ := inverseRightMulAction H G iota
  let _ : HasCoequalizer (coefficientSource H G Z) (coefficientTarget H G Z rho) := by
    change HasCoequalizer (coefficientSource H G Z)
      (inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  exact coefficientCoequalizerReindex_generator H G Z rho (fun g => k * g)
    (inverseRightMulAction_left_commute H G iota k) g

/-- Left identity acts by the actual identity map of coefficient coinvariants. -/
theorem inverseRightLeftMap_one :
    inverseRightLeftMap H G Z rho iota 1 = 𝟙 (inverseRightCoinvariants H G Z rho iota) := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro g
  simp only [← Category.assoc]
  change inverseRightGenerator H G Z rho iota g ≫ inverseRightLeftMap H G Z rho iota 1 =
    inverseRightGenerator H G Z rho iota g ≫ 𝟙 _
  rw [inverseRightLeftMap_generator, one_mul, Category.comp_id]

/-- Left multiplication has the actual reversed categorical-composition convention. -/
theorem inverseRightLeftMap_mul (k l : G) :
    inverseRightLeftMap H G Z rho iota (k * l) =
      inverseRightLeftMap H G Z rho iota l ≫ inverseRightLeftMap H G Z rho iota k := by
  apply coequalizer.hom_ext
  apply Sigma.hom_ext
  intro g
  simp only [← Category.assoc]
  change inverseRightGenerator H G Z rho iota g ≫ inverseRightLeftMap H G Z rho iota (k * l) =
    (inverseRightGenerator H G Z rho iota g ≫ inverseRightLeftMap H G Z rho iota l) ≫
      inverseRightLeftMap H G Z rho iota k
  rw [inverseRightLeftMap_generator, inverseRightLeftMap_generator,
    inverseRightLeftMap_generator, mul_assoc]

/-- The actual descended left maps give the full target automorphism action. -/
def inverseRightLeftAut : G →* Aut (inverseRightCoinvariants H G Z rho iota) where
  toFun k :=
    .of
      { hom := inverseRightLeftMap H G Z rho iota k
        inv := inverseRightLeftMap H G Z rho iota k⁻¹
        hom_inv_id := (inverseRightLeftMap_mul H G Z rho iota k⁻¹ k).symm.trans
          (by rw [inv_mul_cancel, inverseRightLeftMap_one])
        inv_hom_id := (inverseRightLeftMap_mul H G Z rho iota k k⁻¹).symm.trans
          (by rw [mul_inv_cancel, inverseRightLeftMap_one]) }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    exact inverseRightLeftMap_one H G Z rho iota
  map_mul' k l := by
    apply Aut.ext
    apply Iso.ext
    exact inverseRightLeftMap_mul H G Z rho iota k l

/-- The actual inverse-right action colimit carries the same full left multiplication. -/
def inverseRightLeftColimitMap
    [HasColimit (inverseRightCoefficientDiagram H G Z rho iota)] (k : G) :
    colimit (inverseRightCoefficientDiagram H G Z rho iota) ⟶
      colimit (inverseRightCoefficientDiagram H G Z rho iota) := by
  letI := inverseRightMulAction H G iota
  let _ : HasColimit (coefficientDiagram H G Z rho) := by
    change HasColimit (inverseRightCoefficientDiagram H G Z rho iota)
    infer_instance
  exact coefficientColimitReindex H G Z rho (fun g => k * g)
    (inverseRightMulAction_left_commute H G iota k)

/-- The actual colimit comparison is equivariant for the full left target group. -/
theorem inverseRightColimitIso_left
    [HasColimit (inverseRightCoefficientDiagram H G Z rho iota)] (k : G) :
    inverseRightLeftColimitMap H G Z rho iota k ≫ (inverseRightColimitIso H G Z rho iota).hom =
      (inverseRightColimitIso H G Z rho iota).hom ≫ inverseRightLeftMap H G Z rho iota k := by
  let _ := inverseRightMulAction H G iota
  let _ : HasCoequalizer (coefficientSource H G Z) (coefficientTarget H G Z rho) := by
    change HasCoequalizer (coefficientSource H G Z)
      (inverseRightCoefficientTarget H G Z rho iota)
    infer_instance
  let _ : HasColimit (coefficientDiagram H G Z rho) := by
    change HasColimit (inverseRightCoefficientDiagram H G Z rho iota)
    infer_instance
  exact coefficientColimitIso_reindex H G Z rho (fun g => k * g)
    (inverseRightMulAction_left_commute H G iota k)

end CategoryTheory.ActionCategory

namespace CategoryTheory.ActionCategory

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (E : Type wE) [Monoid H] [MulAction H E]
variable (Z Z' : C) (rho : H →* End Z) (rho' : H →* End Z')
variable (f : Z ⟶ Z') (hf : ∀ a : H, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)

/-- An equivariant coefficient map gives the actual constant-component diagram map. -/
def coefficientNatTrans : coefficientDiagram H E Z rho ⟶ coefficientDiagram H E Z' rho' where
  app _ := f
  naturality _ _ a := hf a.hom

variable [HasCoproduct (fun _ : E => Z)]
variable [HasCoproduct (fun _ : H × E => Z)]
variable [HasCoproduct (fun _ : E => Z')]
variable [HasCoproduct (fun _ : H × E => Z')]
variable [HasCoequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)]
variable [HasCoequalizer (coefficientSource H E Z') (coefficientTarget H E Z' rho')]

/-- Equivariant coefficient maps descend through the actual coefficient coequalizers. -/
def coefficientCoequalizerMap :
    coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) ⟶
      coequalizer (coefficientSource H E Z') (coefficientTarget H E Z' rho') :=
  CoefficientFamily.desc H E Z rho
    { leg := fun e => f ≫ coefficientGenerator H E Z' rho' e
      relation := by
        intro a e
        rw [← Category.assoc, hf a, Category.assoc]
        exact congrArg (fun k => f ≫ k)
          ((coforkCoefficientFamily H E Z' rho'
            (coequalizer.cofork (coefficientSource H E Z')
              (coefficientTarget H E Z' rho'))).relation a e) }

/-- The descended coefficient map retains the actual coefficient generator. -/
theorem coefficientCoequalizerMap_generator (e : E) :
    coefficientGenerator H E Z rho e ≫ coefficientCoequalizerMap H E Z Z' rho rho' f hf =
      f ≫ coefficientGenerator H E Z' rho' e :=
  CoefficientFamily.desc_generator H E Z rho _ e

/-- The actual colimit/coequalizer comparison is natural for every equivariant coefficient map. -/
theorem coefficientColimitIso_naturality
    [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H E Z' rho')] :
    colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        (coefficientColimitIso H E Z' rho').hom =
      (coefficientColimitIso H E Z rho).hom ≫ coefficientCoequalizerMap H E Z Z' rho rho' f hf := by
  apply colimit.hom_ext
  intro e
  obtain ⟨x, hx⟩ := (ActionCategory.objEquiv H E).surjective e
  rw [← hx]
  let L := colimit (coefficientDiagram H E Z rho)
  let L' := colimit (coefficientDiagram H E Z' rho')
  let Q := coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)
  let Q' := coequalizer (coefficientSource H E Z') (coefficientTarget H E Z' rho')
  let lx : Z ⟶ L := colimit.ι (coefficientDiagram H E Z rho) (x : ActionCategory H E)
  let lx' : Z' ⟶ L' := colimit.ι (coefficientDiagram H E Z' rho') (x : ActionCategory H E)
  let cmp : L ⟶ Q := (coefficientColimitIso H E Z rho).hom
  let cmp' : L' ⟶ Q' := (coefficientColimitIso H E Z' rho').hom
  let lm : L ⟶ L' := colimMap (coefficientNatTrans H E Z Z' rho rho' f hf)
  let qm : Q ⟶ Q' := coefficientCoequalizerMap H E Z Z' rho rho' f hf
  let qx : Z ⟶ Q := coefficientGenerator H E Z rho x
  let qx' : Z' ⟶ Q' := coefficientGenerator H E Z' rho' x
  have hMap : lx ≫ lm = f ≫ lx' :=
    ι_colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) (x : ActionCategory H E)
  have hCompare' : lx' ≫ cmp' = qx' := coefficientColimitIso_generator H E Z' rho' x
  have hCompare : lx ≫ cmp = qx := coefficientColimitIso_generator H E Z rho x
  have hGenerator : qx ≫ qm = f ≫ qx' :=
    coefficientCoequalizerMap_generator H E Z Z' rho rho' f hf x
  have hLeft : (lx ≫ lm) ≫ cmp' = f ≫ qx' :=
    (congrArg (fun k : Z ⟶ L' => k ≫ cmp') hMap).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k : Z' ⟶ Q' => f ≫ k) hCompare'))
  have hRight : (lx ≫ cmp) ≫ qm = f ≫ qx' :=
    (congrArg (fun k : Z ⟶ Q => k ≫ qm) hCompare).trans hGenerator
  change lx ≫ (lm ≫ cmp') = lx ≫ (cmp ≫ qm)
  exact (Category.assoc _ _ _).symm.trans
    (hLeft.trans (hRight.symm.trans (Category.assoc _ _ _)))

end CategoryTheory.ActionCategory

namespace CategoryTheory.ActionCategory

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (G : Type wG) [Monoid H] [Group G]
variable (Z : C) (rho : H →* End Z) (iota : H →* G)
variable [HasCoproduct (fun _ : G => Z)]
variable [HasCoproduct (fun _ : H × G => Z)]
variable [HasCoproduct (fun _ : G × H => Z)]

/-- The usual first balancing arrow acts on the group index. -/
def balancedGroupArrow : (∐ fun _ : G × H => Z) ⟶ ∐ fun _ : G => Z :=
  Sigma.desc (fun ga => Sigma.ι (fun _ : G => Z) (ga.1 * iota ga.2))

/-- The usual second balancing arrow acts on the coefficient. -/
def balancedCoefficientArrow : (∐ fun _ : G × H => Z) ⟶ ∐ fun _ : G => Z :=
  Sigma.desc (fun ga => (rho ga.2).asHom ≫ Sigma.ι (fun _ : G => Z) ga.1)

/-- The actual coproduct source comparison uses the group-index relabelling. -/
def balancedSourceIso :
    (∐ fun _ : G × H => Z) ≅ ∐ fun _ : H × G => Z := by
  let _ : HasCoproduct ((fun _ : H × G => Z) ∘ inverseRightIndexEquiv H G iota) := by
    change HasCoproduct (fun _ : G × H => Z)
    infer_instance
  exact Sigma.reindex (inverseRightIndexEquiv H G iota) (fun _ : H × G => Z)

omit [HasCoproduct (fun _ : G => Z)] in
/-- The source comparison retains the exact group/index generator. -/
theorem balancedSourceIso_generator (ga : G × H) :
    Sigma.ι (fun _ : G × H => Z) ga ≫ (balancedSourceIso H G Z iota).hom =
      Sigma.ι (fun _ : H × G => Z) (ga.2, ga.1 * iota ga.2) := by
  let _ : HasCoproduct ((fun _ : H × G => Z) ∘ inverseRightIndexEquiv H G iota) := by
    change HasCoproduct (fun _ : G × H => Z)
    infer_instance
  exact Sigma.ι_reindex_hom (inverseRightIndexEquiv H G iota) (fun _ : H × G => Z) ga

/-- Source relabelling turns inverse-right source retention into the usual group arrow. -/
theorem balancedSourceIso_group :
    (balancedSourceIso H G Z iota).hom ≫ coefficientSource H G Z =
      balancedGroupArrow H G Z iota := by
  apply Sigma.hom_ext
  intro ga
  rw [← Category.assoc, balancedSourceIso_generator]
  simp only [coefficientSource, balancedGroupArrow, Sigma.ι_comp_desc]

/-- Source relabelling turns inverse-right coefficient action into the usual coefficient arrow. -/
theorem balancedSourceIso_coefficient :
    (balancedSourceIso H G Z iota).hom ≫ inverseRightCoefficientTarget H G Z rho iota =
      balancedCoefficientArrow H G Z rho := by
  apply Sigma.hom_ext
  intro ga
  rw [← Category.assoc, balancedSourceIso_generator]
  change Sigma.ι (fun _ : H × G => Z) (ga.2, ga.1 * iota ga.2) ≫
      inverseRightCoefficientTarget H G Z rho iota =
    Sigma.ι (fun _ : G × H => Z) ga ≫ balancedCoefficientArrow H G Z rho
  let _ := inverseRightMulAction H G iota
  change Sigma.ι (fun _ : H × G => Z) (ga.2, ga.1 * iota ga.2) ≫
      coefficientTarget H G Z rho =
    Sigma.ι (fun _ : G × H => Z) ga ≫ balancedCoefficientArrow H G Z rho
  rw [coefficientTarget, balancedCoefficientArrow, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  change (rho ga.2).asHom ≫ Sigma.ι (fun _ : G => Z) ((ga.1 * iota ga.2) * (iota ga.2)⁻¹) =
    (rho ga.2).asHom ≫ Sigma.ι (fun _ : G => Z) ga.1
  rw [mul_assoc, mul_inv_cancel, mul_one]

variable [HasCoequalizer (coefficientSource H G Z)
  (inverseRightCoefficientTarget H G Z rho iota)]

/-- The actual inverse-right quotient projection is a cofork of the two usual balancing arrows. -/
def balancedCoefficientCofork :
    Cofork (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho) :=
  Cofork.ofπ (coequalizer.π (coefficientSource H G Z)
    (inverseRightCoefficientTarget H G Z rho iota)) (by
      rw [← balancedSourceIso_group H G Z iota,
        ← balancedSourceIso_coefficient H G Z rho iota, Category.assoc, Category.assoc]
      exact congrArg (fun k => (balancedSourceIso H G Z iota).hom ≫ k)
        (coequalizer.condition (coefficientSource H G Z)
          (inverseRightCoefficientTarget H G Z rho iota)))

/-- The usual group/coefficient cofork has the complete actual colimit universal property. -/
def balancedCoefficientCoforkIsColimit :
    IsColimit (balancedCoefficientCofork H G Z rho iota) :=
  (Cofork.isColimitEquivOfIsos (balancedCoefficientCofork H G Z rho iota)
    (coequalizer.cofork (coefficientSource H G Z) (inverseRightCoefficientTarget H G Z rho iota))
    (balancedSourceIso H G Z iota) (Iso.refl _) (Iso.refl _)
    (by rw [balancedSourceIso_group, Iso.refl_hom, Category.comp_id])
    (by rw [balancedSourceIso_coefficient, Iso.refl_hom, Category.comp_id])
    (by simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id,
      balancedCoefficientCofork, Cofork.π_ofπ, coequalizer.cofork_π])).symm
    (colimit.isColimit (parallelPair (coefficientSource H G Z)
      (inverseRightCoefficientTarget H G Z rho iota)))

variable [HasCoequalizer (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho)]

/-- The actual action-coefficient quotient identifies with the usual balanced coequalizer. -/
def balancedCoefficientIso :
    inverseRightCoinvariants H G Z rho iota ≅
      coequalizer (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho) :=
  (balancedCoefficientCoforkIsColimit H G Z rho iota).coconePointUniqueUpToIso
    (colimit.isColimit
      (parallelPair (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho)))

/-- The usual balanced comparison retains every actual coefficient generator. -/
theorem balancedCoefficientIso_generator (g : G) :
    inverseRightGenerator H G Z rho iota g ≫ (balancedCoefficientIso H G Z rho iota).hom =
      Sigma.ι (fun _ : G => Z) g ≫
        coequalizer.π (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho) := by
  have h := (balancedCoefficientCoforkIsColimit H G Z rho iota).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit
      (parallelPair (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho)))
    WalkingParallelPair.one
  change coequalizer.π (coefficientSource H G Z) (inverseRightCoefficientTarget H G Z rho iota) ≫
    (balancedCoefficientIso H G Z rho iota).hom =
      coequalizer.π (balancedGroupArrow H G Z iota) (balancedCoefficientArrow H G Z rho) at h
  unfold inverseRightGenerator
  rw [Category.assoc, h]

end CategoryTheory.ActionCategory
