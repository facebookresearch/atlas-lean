/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Data.Quot

/-!
# Auxiliary action category and localization of a monoidal action

For a coherent left action of a monoidal category `S` on a category `X`,
`MonoidalActionCategory S X` is the auxiliary category `⟨S, X⟩`, with the objects
of `X`. Its arrows are pairs
`(s, f : s ⊙ₗ x ⟶ y)` modulo isomorphism of the stabilizing object `s`.
The morphism `f` may be noninvertible.

The construction only needs monoidal structure, and in particular applies to
the symmetric monoidal groupoids in Weibel IV.4.7–4.7.1.

`MonoidalActionCategory.SInverse S X` is the localization `S⁻¹X`: it applies the
auxiliary construction to the diagonal action on `X × S`. Its canonical
inclusion has positive-first coordinates `x ↦ (x, 1)`.
`SInverse.toProd` and `SourceSInverse.toProd` expose the underlying pairs using
their respective canonical actions.
-/

@[expose] public section

noncomputable section

universe uS vS uX vX uY vY

namespace CategoryTheory

open MonoidalCategory
open scoped MonoidalCategory MonoidalLeftAction

/-- Objects of the auxiliary category `⟨S, X⟩` associated to a coherent monoidal action.
The action is retained as a parameter so different actions give different
category structures on this object wrapper. -/
structure MonoidalActionCategory (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] where
  /-- The underlying object of the acted-on category. -/
  of : X

namespace MonoidalActionCategory

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]

/-- A stabilized morphism, with an arbitrary morphism in `X`. -/
structure RawHom (x y : MonoidalActionCategory S X) where
  /-- The object of `S` used to translate the source before applying the morphism. -/
  stabilizer : S
  /-- The morphism in `X` from the translated source to the target. -/
  hom : stabilizer ⊙ₗ x.of ⟶ y.of

/-- Changing a stabilizer by an isomorphism does not change the arrow. -/
def RawHom.Rel {x y : MonoidalActionCategory S X} (f g : RawHom x y) : Prop :=
  ∃ e : f.stabilizer ≅ g.stabilizer, e.hom ⊵ₗ x.of ≫ g.hom = f.hom

private theorem rel_refl {x y : MonoidalActionCategory S X} (f : RawHom x y) :
    f.Rel f := by
  refine ⟨Iso.refl f.stabilizer, ?_⟩
  simp

private theorem rel_symm {x y : MonoidalActionCategory S X} {f g : RawHom x y}
    (h : f.Rel g) : g.Rel f := by
  obtain ⟨e, h⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← h]
  simp

private theorem rel_trans {x y : MonoidalActionCategory S X} {f g h : RawHom x y}
    (hfg : f.Rel g) (hgh : g.Rel h) : f.Rel h := by
  obtain ⟨e, hfg⟩ := hfg
  obtain ⟨d, hgh⟩ := hgh
  refine ⟨e.trans d, ?_⟩
  simpa only [Iso.trans_hom, MonoidalLeftAction.comp_actionHomLeft,
    Category.assoc, hgh] using hfg

/-- Stabilized morphisms modulo isomorphisms of the stabilizer. -/
instance rawHomSetoid (x y : MonoidalActionCategory S X) : Setoid (RawHom x y) where
  r := RawHom.Rel
  iseqv := by exact ⟨rel_refl, rel_symm, rel_trans⟩

/-- Morphism classes from `x` to `y`, modulo stabilizer isomorphisms intertwining
the maps in `X`. -/
abbrev Hom (x y : MonoidalActionCategory S X) := Quotient (rawHomSetoid x y)

/-- The class of a stabilized morphism. -/
def Hom.mk {x y : MonoidalActionCategory S X} (f : RawHom x y) : Hom x y :=
  Quotient.mk _ f

/-- Composition uses the action associator and keeps arbitrary morphisms in `X`. -/
def RawHom.comp {x y z : MonoidalActionCategory S X} (f : RawHom x y)
    (g : RawHom y z) : RawHom x z where
  stabilizer := g.stabilizer ⊗ f.stabilizer
  hom := (αₗ g.stabilizer f.stabilizer x.of).hom ≫
    g.stabilizer ⊴ₗ f.hom ≫ g.hom

private theorem rawComp_rel {x y z : MonoidalActionCategory S X}
    {f f' : RawHom x y} {g g' : RawHom y z}
    (hf : f.Rel f') (hg : g.Rel g') : (f.comp g).Rel (f'.comp g') := by
  obtain ⟨ef, hf⟩ := hf
  obtain ⟨eg, hg⟩ := hg
  refine ⟨tensorIso eg ef, ?_⟩
  have ha : (eg.hom ⊗ₘ ef.hom) ⊵ₗ x.of ≫
      (αₗ g'.stabilizer f'.stabilizer x.of).hom =
    (αₗ g.stabilizer f.stabilizer x.of).hom ≫
      (eg.hom ⊙ₗₘ (ef.hom ⊵ₗ x.of)) := by
    simpa only [MonoidalLeftAction.actionHom_id] using
      MonoidalLeftAction.actionAssocIso_hom_naturality eg.hom ef.hom (𝟙 x.of)
  change (eg.hom ⊗ₘ ef.hom) ⊵ₗ x.of ≫
      (αₗ g'.stabilizer f'.stabilizer x.of).hom ≫
        g'.stabilizer ⊴ₗ f'.hom ≫ g'.hom =
    (αₗ g.stabilizer f.stabilizer x.of).hom ≫
      g.stabilizer ⊴ₗ f.hom ≫ g.hom
  calc
    _ = (αₗ g.stabilizer f.stabilizer x.of).hom ≫
        (eg.hom ⊙ₗₘ (ef.hom ⊵ₗ x.of)) ≫
          g'.stabilizer ⊴ₗ f'.hom ≫ g'.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ g'.stabilizer ⊴ₗ f'.hom ≫ g'.hom) ha
    _ = (αₗ g.stabilizer f.stabilizer x.of).hom ≫
        eg.hom ⊵ₗ (f.stabilizer ⊙ₗ x.of) ≫
          g'.stabilizer ⊴ₗ f.hom ≫ g'.hom := by
      simp only [MonoidalLeftAction.actionHom_def, Category.assoc]
      rw [← MonoidalLeftAction.actionHomRight_comp_assoc, hf]
    _ = _ := by
      rw [← MonoidalLeftAction.action_exchange_assoc, hg]

/-- Composition of morphism classes, obtained from `RawHom.comp` using the action
associator and the later stabilizer tensored with the earlier stabilizer. -/
def Hom.comp {x y z : MonoidalActionCategory S X} (f : Hom x y) (g : Hom y z) :
    Hom x z :=
  Quotient.map₂ RawHom.comp (by
    intro _ _ hf _ _ hg
    exact rawComp_rel hf hg) f g

/-- The raw unit arrow is supplied by the action unitor. -/
def RawHom.id (x : MonoidalActionCategory S X) : RawHom x x where
  stabilizer := 𝟙_ S
  hom := (λₗ[S] x.of).hom

private theorem rawId_comp_rel {x y : MonoidalActionCategory S X} (f : RawHom x y) :
    ((RawHom.id x).comp f).Rel f := by
  refine ⟨ρ_ f.stabilizer, ?_⟩
  dsimp only [RawHom.comp, RawHom.id]
  rw [MonoidalLeftAction.rightUnitor_actionHom]
  simp only [Category.assoc]

private theorem rawComp_id_rel {x y : MonoidalActionCategory S X} (f : RawHom x y) :
    (f.comp (RawHom.id y)).Rel f := by
  refine ⟨λ_ f.stabilizer, ?_⟩
  dsimp only [RawHom.comp, RawHom.id]
  rw [MonoidalLeftAction.leftUnitor_actionHom, Category.assoc,
    MonoidalLeftAction.actionUnitIso_hom_naturality]

private theorem rawComp_assoc_rel {w x y z : MonoidalActionCategory S X}
    (f : RawHom w x) (g : RawHom x y) (h : RawHom y z) :
    ((f.comp g).comp h).Rel (f.comp (g.comp h)) := by
  refine ⟨(α_ h.stabilizer g.stabilizer f.stabilizer).symm, ?_⟩
  simp only [RawHom.comp, Iso.symm_hom, MonoidalLeftAction.actionHomRight_comp,
    Category.assoc, MonoidalLeftAction.tensor_actionHomRight, Iso.inv_hom_id_assoc]
  rw [← MonoidalLeftAction.associator_actionHom_assoc]
  simp only [MonoidalLeftAction.inv_hom_actionHomLeft_assoc]

/-- The identity class, represented by the tensor unit and the action unitor. -/
def Hom.id (x : MonoidalActionCategory S X) : Hom x x := Hom.mk (RawHom.id x)

private theorem quotientId_comp {x y : MonoidalActionCategory S X} (f : Hom x y) :
    Hom.comp (Hom.id x) f = f := by
  induction f using Quotient.inductionOn
  exact Quotient.sound (rawId_comp_rel _)

private theorem quotientComp_id {x y : MonoidalActionCategory S X} (f : Hom x y) :
    Hom.comp f (Hom.id y) = f := by
  induction f using Quotient.inductionOn
  exact Quotient.sound (rawComp_id_rel _)

private theorem quotientComp_assoc {w x y z : MonoidalActionCategory S X}
    (f : Hom w x) (g : Hom x y) (h : Hom y z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  induction h using Quotient.inductionOn
  exact Quotient.sound (rawComp_assoc_rel _ _ _)

/-- The auxiliary category `⟨S, X⟩` associated to the coherent action. -/
instance category : Category.{max uS vX} (MonoidalActionCategory S X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by exact quotientId_comp
  comp_id := by exact quotientComp_id
  assoc := by exact quotientComp_assoc

@[simp]
theorem Hom.mk_comp {x y z : MonoidalActionCategory S X}
    (f : RawHom x y) (g : RawHom y z) :
    CategoryStruct.comp (obj := MonoidalActionCategory S X) (X := x) (Y := y) (Z := z)
      (Hom.mk f) (Hom.mk g) = Hom.mk (f.comp g) := rfl

/-- The category identity is the class with unit stabilizer and action unitor. -/
@[simp]
theorem Hom.mk_id (x : MonoidalActionCategory S X) :
    Hom.mk (RawHom.id x) = (𝟙 x : Hom x x) := rfl

/-- Equality of morphism classes is exactly change of stabilizer by an isomorphism. -/
theorem Hom.mk_eq_mk_iff {x y : MonoidalActionCategory S X} (f g : RawHom x y) :
    Hom.mk f = Hom.mk g ↔ f.Rel g := Quotient.eq

/-- Every morphism has a stabilized representative with an arbitrary map in `X`. -/
theorem Hom.exists_rep {x y : MonoidalActionCategory S X} (f : x ⟶ y) :
    ∃ r : RawHom x y, Hom.mk r = f := by
  induction f using Quotient.inductionOn
  exact ⟨_, rfl⟩

/-- An original morphism is represented using the unit stabilizer. -/
def RawHom.ofMap {x y : X} (f : x ⟶ y) :
    RawHom (⟨x⟩ : MonoidalActionCategory S X) ⟨y⟩ where
  stabilizer := 𝟙_ S
  hom := (λₗ[S] x).hom ≫ f

private theorem ofMap_comp_rel {x y z : X} (f : x ⟶ y) (g : y ⟶ z) :
    ((RawHom.ofMap (S := S) f).comp (RawHom.ofMap (S := S) g)).Rel
      (RawHom.ofMap (S := S) (f ≫ g)) := by
  refine ⟨ρ_ (𝟙_ S), ?_⟩
  dsimp only [RawHom.ofMap, RawHom.comp]
  rw [MonoidalLeftAction.rightUnitor_actionHom]
  simp only [Category.assoc, MonoidalLeftAction.actionHomRight_comp]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

/-- The canonical functor from `X` to the auxiliary action category `⟨S, X⟩`. -/
def inclusion (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :
    X ⥤ MonoidalActionCategory S X where
  obj x := ⟨x⟩
  map f := Hom.mk (RawHom.ofMap (S := S) f)
  map_id x := by
    apply Quotient.sound
    refine ⟨Iso.refl (𝟙_ S), ?_⟩
    simp [RawHom.ofMap, RawHom.id]
  map_comp f g := by
    exact (Quotient.sound (ofMap_comp_rel (S := S) f g)).symm

@[simp]
theorem inclusion_obj (x : X) : ((inclusion S X).obj x).of = x := rfl

@[simp]
theorem inclusion_map {x y : X} (f : x ⟶ y) :
    (inclusion S X).map f = Hom.mk (RawHom.ofMap (S := S) f) := rfl

end MonoidalActionCategory

namespace MonoidalActionCategory

/-- Two coherent actions give a componentwise action on the product category. -/
@[instance_reducible]
def productAction (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]
    (Y : Type uY) [Category.{vY} Y] [MonoidalLeftAction S Y] :
    MonoidalLeftAction S (X × Y) where
  actionObj s x := (s ⊙ₗ x.1, s ⊙ₗ x.2)
  actionHomLeft f x := (f ⊵ₗ x.1, f ⊵ₗ x.2)
  actionHomRight s _ _ f := (s ⊴ₗ f.1, s ⊴ₗ f.2)
  actionHom f g := (f ⊙ₗₘ g.1, f ⊙ₗₘ g.2)
  actionAssocIso s t x := (αₗ s t x.1).prod (αₗ s t x.2)
  actionUnitIso x := (λₗ[S] x.1).prod (λₗ[S] x.2)
  actionHom_def f g := by
    apply Prod.ext
    · exact MonoidalLeftAction.actionHom_def f g.1
    · exact MonoidalLeftAction.actionHom_def f g.2
  actionHomRight_id s x := by
    apply Prod.ext
    · exact MonoidalLeftAction.actionHomRight_id s x.1
    · exact MonoidalLeftAction.actionHomRight_id s x.2
  id_actionHomLeft s x := by
    apply Prod.ext
    · exact MonoidalLeftAction.id_actionHomLeft s x.1
    · exact MonoidalLeftAction.id_actionHomLeft s x.2
  actionHom_comp f₁ f₂ g₁ g₂ := by
    apply Prod.ext
    · exact MonoidalLeftAction.actionHom_comp f₁ f₂ g₁.1 g₂.1
    · exact MonoidalLeftAction.actionHom_comp f₁ f₂ g₁.2 g₂.2
  actionAssocIso_hom_naturality f g h := by
    apply Prod.ext
    · exact MonoidalLeftAction.actionAssocIso_hom_naturality f g h.1
    · exact MonoidalLeftAction.actionAssocIso_hom_naturality f g h.2
  actionUnitIso_hom_naturality f := by
    apply Prod.ext
    · exact MonoidalLeftAction.actionUnitIso_hom_naturality f.1
    · exact MonoidalLeftAction.actionUnitIso_hom_naturality f.2
  whiskerLeft_actionHomLeft s _ _ f x := by
    apply Prod.ext
    · exact MonoidalLeftAction.whiskerLeft_actionHomLeft s f x.1
    · exact MonoidalLeftAction.whiskerLeft_actionHomLeft s f x.2
  whiskerRight_actionHomLeft s f x := by
    apply Prod.ext
    · exact MonoidalLeftAction.whiskerRight_actionHomLeft s f x.1
    · exact MonoidalLeftAction.whiskerRight_actionHomLeft s f x.2
  associator_actionHom s t u x := by
    apply Prod.ext
    · exact MonoidalLeftAction.associator_actionHom s t u x.1
    · exact MonoidalLeftAction.associator_actionHom s t u x.2
  leftUnitor_actionHom s x := by
    apply Prod.ext
    · exact MonoidalLeftAction.leftUnitor_actionHom s x.1
    · exact MonoidalLeftAction.leftUnitor_actionHom s x.2
  rightUnitor_actionHom s x := by
    apply Prod.ext
    · exact MonoidalLeftAction.rightUnitor_actionHom s x.1
    · exact MonoidalLeftAction.rightUnitor_actionHom s x.2

/-- The diagonal action on positive-first pairs. The second factor uses the
canonical tensor action of `S` on itself. -/
@[instance_reducible]
def diagonalAction (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :
    MonoidalLeftAction S (X × S) :=
  @productAction S _ _ X _ _ S _ (selfLeftAction S)

/-- The diagonal action in the source's denominator-first coordinates. -/
@[instance_reducible]
def sourceDiagonalAction (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :
    MonoidalLeftAction S (S × X) :=
  @productAction S _ _ S _ (selfLeftAction S) X _ _

/-- Categorical localization of the action, in positive-first coordinates. -/
abbrev SInverse (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :=
  @MonoidalActionCategory S _ _ (X × S) _ (diagonalAction S X)

/-- The same construction with the source's order of product factors. -/
abbrev SourceSInverse (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X] :=
  @MonoidalActionCategory S _ _ (S × X) _ (sourceDiagonalAction S X)

/-- The underlying positive-first pair, using the canonical diagonal action. -/
def SInverse.toProd {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
    {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]
    (a : SInverse S X) : X × S :=
  @MonoidalActionCategory.of S _ _ (X × S) _ (diagonalAction S X) a

/-- The underlying denominator-first pair, using the canonical source action. -/
def SourceSInverse.toProd {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
    {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]
    (a : SourceSInverse S X) : S × X :=
  @MonoidalActionCategory.of S _ _ (S × X) _ (sourceDiagonalAction S X) a

namespace SInverse

variable (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
  (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]

/-- Pair an object of `X` with the tensor unit in the denominator coordinate. -/
def positivePairs : X ⥤ X × S :=
  (𝟭 X).prod' ((Functor.const X).obj (𝟙_ S))

/-- The canonical inclusion sends `x` to the positive-first pair `(x, 1)`. -/
def inclusion : X ⥤ SInverse S X := by
  letI := diagonalAction S X
  exact positivePairs S X ⋙ MonoidalActionCategory.inclusion S (X × S)

/-- The canonical inclusion has positive-first coordinates `(x, 1)`. -/
@[simp]
theorem inclusion_obj (x : X) : ((inclusion S X).obj x).toProd = (x, 𝟙_ S) := rfl

/-- The inclusion is formed from the original morphism and the identity of the
denominator unit, followed by the unit-stabilizer inclusion. -/
theorem inclusion_map {x y : X} (f : x ⟶ y) :
    (inclusion S X).map f =
      @MonoidalActionCategory.Hom.mk S _ _ (X × S) _ (diagonalAction S X)
        ((inclusion S X).obj x) ((inclusion S X).obj y)
        (@MonoidalActionCategory.RawHom.ofMap S _ _ (X × S) _ (diagonalAction S X)
          (x, 𝟙_ S) (y, 𝟙_ S) (f, 𝟙 (𝟙_ S))) := rfl

end SInverse

section ProductSwap

variable {S : Type uS} [Category.{vS} S] [MonoidalCategory S]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction S X]
  {Y : Type uY} [Category.{vY} Y] [MonoidalLeftAction S Y]

attribute [local instance] productAction

/-- Swap the two acted-on coordinates of a stabilized product morphism. -/
def productSwapRawHom {a b : MonoidalActionCategory S (X × Y)} (f : RawHom a b) :
    RawHom (⟨(a.of.2, a.of.1)⟩ : MonoidalActionCategory S (Y × X))
      ⟨(b.of.2, b.of.1)⟩ where
  stabilizer := f.stabilizer
  hom := (f.hom.2, f.hom.1)

private theorem productSwapRawHom_rel {a b : MonoidalActionCategory S (X × Y)}
    {f g : RawHom a b} (h : f.Rel g) :
    (productSwapRawHom f).Rel (productSwapRawHom g) := by
  obtain ⟨e, h⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · exact congrArg (fun k => k.2) h
  · exact congrArg (fun k => k.1) h

/-- Product-coordinate swap descends to the action localization. -/
def productSwap (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]
    (Y : Type uY) [Category.{vY} Y] [MonoidalLeftAction S Y] :
    MonoidalActionCategory S (X × Y) ⥤ MonoidalActionCategory S (Y × X) where
  obj a := ⟨(a.of.2, a.of.1)⟩
  map f := Quotient.map (productSwapRawHom (S := S) (X := X) (Y := Y))
    (by intro _ _ h; exact productSwapRawHom_rel h) f
  map_id a := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

/-- Swapping the product coordinates twice is naturally the identity. -/
def productSwapSymmetry (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]
    (Y : Type uY) [Category.{vY} Y] [MonoidalLeftAction S Y] :
    productSwap S X Y ⋙ productSwap S Y X ≅
      𝟭 (MonoidalActionCategory S (X × Y)) :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    refine Quotient.inductionOn f ?_
    intro r
    change Hom.comp (Hom.mk r) (Hom.id b) = Hom.comp (Hom.id a) (Hom.mk r)
    exact (quotientComp_id _).trans (quotientId_comp _).symm)

/-- Swapping product coordinates gives an equivalence of localized categories. -/
def productSwapEquivalence (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
    (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]
    (Y : Type uY) [Category.{vY} Y] [MonoidalLeftAction S Y] :
    MonoidalActionCategory S (X × Y) ≌ MonoidalActionCategory S (Y × X) where
  functor := productSwap S X Y
  inverse := productSwap S Y X
  unitIso := (productSwapSymmetry S X Y).symm
  counitIso := productSwapSymmetry S Y X
  functor_unitIso_comp a := by
    change Hom.comp (Hom.id _) (Hom.id _) = Hom.id _
    exact quotientId_comp _

end ProductSwap

namespace SInverse

variable (S : Type uS) [Category.{vS} S] [MonoidalCategory S]
  (X : Type uX) [Category.{vX} X] [MonoidalLeftAction S X]

/-- Positive-first and source-order localizations are the same category up to
the canonical product-coordinate equivalence. -/
def sourceEquivalence : SInverse S X ≌ SourceSInverse S X :=
  @productSwapEquivalence S _ _ X _ _ S _ (selfLeftAction S)

/-- The source-order equivalence swaps the two underlying pair coordinates. -/
@[simp]
theorem sourceEquivalence_obj (a : SInverse S X) :
    ((sourceEquivalence S X).functor.obj a).toProd =
      (a.toProd.2, a.toProd.1) := rfl

end SInverse

end MonoidalActionCategory

end CategoryTheory

end
