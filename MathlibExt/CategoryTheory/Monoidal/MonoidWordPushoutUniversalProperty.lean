/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorWordAdjunction
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorColimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Original associative word pushouts

Sifted colimits of original monoid diagrams are constructed on their
actual underlying colimit. Their unit, multiplication, all monoid laws
and full original cocone universal property are outputs.
-/

@[expose] public section

noncomputable section

universe u v uJ vJ

namespace CategoryTheory.MonoidalCategory.MonoidWordPushout.MonSiftedColimit

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {J : Type uJ} [Category.{vJ} J]
variable (D : J ⥤ Mon C)
variable [HasColimit (D ⋙ Mon.forget C)]

/-- The actual original underlying diagram. -/
abbrev diagram : J ⥤ C := D ⋙ Mon.forget C

/-- Its constructed underlying colimit carrier. -/
abbrev carrier : C := colimit (diagram D)

/-- The original leg from each original monoid carrier. -/
def ι (j : J) : (D.obj j).X ⟶ carrier D := colimit.ι (diagram D) j

@[reassoc (attr := simp)] theorem ι_naturality {j k : J} (f : j ⟶ k) :
    (D.map f).hom ≫ ι D k = ι D j := colimit.w (diagram D) f

/-- The original unit maps form an actual cocone over the tensor-unit diagram. -/
def unitCocone : Cocone ((Functor.const J).obj (𝟙_ C)) where
  pt := carrier D
  ι :=
    { app j := (D.obj j).mon.one ≫ ι D j
      naturality j k f := by
        change 𝟙 (𝟙_ C) ≫ ((D.obj k).mon.one ≫ ι D k) =
          ((D.obj j).mon.one ≫ ι D j) ≫ 𝟙 (carrier D)
        rw [Category.comp_id, Category.id_comp, ← IsMonHom.one_hom (D.map f).hom,
          Category.assoc, ι_naturality] }

variable [IsSifted J]

/-- The constructed original unit on the actual underlying colimit. -/
def one : 𝟙_ C ⟶ carrier D :=
  (isColimitConstCocone J (𝟙_ C)).desc (unitCocone D)

/-- Every original monoid unit maps to the constructed colimit unit. -/
theorem one_eq (j : J) : one D = (D.obj j).mon.one ≫ ι D j := by
  have h := (isColimitConstCocone J (𝟙_ C)).fac (unitCocone D) j
  change 𝟙 (𝟙_ C) ≫ one D = (D.obj j).mon.one ≫ ι D j at h
  simpa only [Category.id_comp] using h

/-- The actual original multiplications followed by their original colimit legs. -/
def mulCocone : Cocone (diagram D ⊗ diagram D) where
  pt := carrier D
  ι :=
    { app j := (D.obj j).mon.mul ≫ ι D j
      naturality j k f := by
        change ((D.map f).hom ⊗ₘ (D.map f).hom) ≫
          ((D.obj k).mon.mul ≫ ι D k) = ((D.obj j).mon.mul ≫ ι D j) ≫ 𝟙 (carrier D)
        rw [Category.comp_id, ← Category.assoc, ← IsMonHom.mul_hom (D.map f).hom,
          Category.assoc, ι_naturality] }

variable [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfShape J (tensorRight X)]

/-- Separate tensor preservation and sifted diagonal finality give the
actual tensor product of both original colimit cocones. -/
def tensorIsColimit :
    IsColimit ((colimit.cocone (diagram D)).tensor (colimit.cocone (diagram D))) :=
  (colimit.isColimit (diagram D)).tensor (colimit.isColimit (diagram D))

/-- The actual multiplication descended from every original diagram multiplication. -/
def mul : carrier D ⊗ carrier D ⟶ carrier D :=
  (tensorIsColimit D).desc (mulCocone D)

/-- Every original pair of colimit legs retains its original multiplication. -/
@[reassoc (attr := simp)] theorem ι_mul (j : J) :
    (ι D j ⊗ₘ ι D j) ≫ mul D = (D.obj j).mon.mul ≫ ι D j :=
  (tensorIsColimit D).fac (mulCocone D) j

/-- All original diagram pairs jointly determine a map out of the actual colimit tensor. -/
theorem tensor_hom_ext {X : C} {f g : carrier D ⊗ carrier D ⟶ X}
    (h : ∀ j, (ι D j ⊗ₘ ι D j) ≫ f = (ι D j ⊗ₘ ι D j) ≫ g) : f = g :=
  (tensorIsColimit D).hom_ext h

/-- The unit and multiplication satisfy the full original left unit law. -/
theorem one_mul : (one D ▷ carrier D) ≫ mul D = (λ_ (carrier D)).hom := by
  apply (isColimitOfPreserves (tensorLeft (𝟙_ C)) (colimit.isColimit (diagram D))).hom_ext
  intro j
  change (𝟙_ C ◁ ι D j) ≫ (one D ▷ carrier D) ≫ mul D =
    (𝟙_ C ◁ ι D j) ≫ (λ_ (carrier D)).hom
  calc
    (𝟙_ C ◁ ι D j) ≫ (one D ▷ carrier D) ≫ mul D =
        (one D ⊗ₘ ι D j) ≫ mul D := by
      rw [← Category.assoc, tensorHom_def']
    _ = ((D.obj j).mon.one ⊗ₘ 𝟙 (D.obj j).X) ≫
        (ι D j ⊗ₘ ι D j) ≫ mul D := by
      rw [one_eq D j, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = ((D.obj j).mon.one ▷ (D.obj j).X) ≫ (D.obj j).mon.mul ≫ ι D j := by
      rw [ι_mul, tensorHom_id]
    _ = (λ_ (D.obj j).X).hom ≫ ι D j := by
      rw [← Category.assoc, (D.obj j).mon.one_mul]
    _ = (𝟙_ C ◁ ι D j) ≫ (λ_ (carrier D)).hom :=
      (leftUnitor_naturality (ι D j)).symm

/-- The unit and multiplication satisfy the full original right unit law. -/
theorem mul_one : (carrier D ◁ one D) ≫ mul D = (ρ_ (carrier D)).hom := by
  apply (isColimitOfPreserves (tensorRight (𝟙_ C)) (colimit.isColimit (diagram D))).hom_ext
  intro j
  change (ι D j ▷ 𝟙_ C) ≫ (carrier D ◁ one D) ≫ mul D =
    (ι D j ▷ 𝟙_ C) ≫ (ρ_ (carrier D)).hom
  calc
    (ι D j ▷ 𝟙_ C) ≫ (carrier D ◁ one D) ≫ mul D =
        (ι D j ⊗ₘ one D) ≫ mul D := by
      rw [← Category.assoc, tensorHom_def]
    _ = (𝟙 (D.obj j).X ⊗ₘ (D.obj j).mon.one) ≫
        (ι D j ⊗ₘ ι D j) ≫ mul D := by
      rw [one_eq D j, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = ((D.obj j).X ◁ (D.obj j).mon.one) ≫ (D.obj j).mon.mul ≫ ι D j := by
      rw [ι_mul, id_tensorHom]
    _ = (ρ_ (D.obj j).X).hom ≫ ι D j := by
      rw [← Category.assoc, (D.obj j).mon.mul_one]
    _ = (ι D j ▷ 𝟙_ C) ≫ (ρ_ (carrier D)).hom :=
      (rightUnitor_naturality (ι D j)).symm

/-- The full original multiplication associativity law on the actual colimit carrier. -/
theorem mul_assoc : (mul D ▷ carrier D) ≫ mul D =
    (α_ (carrier D) (carrier D) (carrier D)).hom ≫
      (carrier D ◁ mul D) ≫ mul D := by
  apply ((tensorIsColimit D).tensor (colimit.isColimit (diagram D))).hom_ext
  intro j
  change ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫ ((mul D ▷ carrier D) ≫ mul D) =
    ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫
      ((α_ (carrier D) (carrier D) (carrier D)).hom ≫ (carrier D ◁ mul D) ≫ mul D)
  have hleft :
      ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫ ((mul D ▷ carrier D) ≫ mul D) =
        ((D.obj j).mon.mul ▷ (D.obj j).X) ≫ (D.obj j).mon.mul ≫ ι D j := by
    calc
      ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫ ((mul D ▷ carrier D) ≫ mul D) =
          (((ι D j ⊗ₘ ι D j) ≫ mul D) ⊗ₘ ι D j) ≫ mul D := by
        rw [← tensorHom_id (mul D), ← Category.assoc,
          tensorHom_comp_tensorHom, Category.comp_id]
      _ = (((D.obj j).mon.mul ≫ ι D j) ⊗ₘ ι D j) ≫ mul D := by rw [ι_mul]
      _ = ((D.obj j).mon.mul ⊗ₘ 𝟙 (D.obj j).X) ≫
          (ι D j ⊗ₘ ι D j) ≫ mul D := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = ((D.obj j).mon.mul ▷ (D.obj j).X) ≫ (D.obj j).mon.mul ≫ ι D j := by
        rw [ι_mul, tensorHom_id]
  have hright :
      ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫
          ((α_ (carrier D) (carrier D) (carrier D)).hom ≫ (carrier D ◁ mul D) ≫ mul D) =
        (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
          ((D.obj j).X ◁ (D.obj j).mon.mul) ≫ (D.obj j).mon.mul ≫ ι D j := by
    calc
      ((ι D j ⊗ₘ ι D j) ⊗ₘ ι D j) ≫
          ((α_ (carrier D) (carrier D) (carrier D)).hom ≫ (carrier D ◁ mul D) ≫ mul D) =
          (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
            (ι D j ⊗ₘ (ι D j ⊗ₘ ι D j)) ≫ (carrier D ◁ mul D) ≫ mul D := by
        rw [← Category.assoc, ← Category.assoc, associator_naturality, Category.assoc,
          Category.assoc]
      _ = (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
          (ι D j ⊗ₘ ((ι D j ⊗ₘ ι D j) ≫ mul D)) ≫ mul D := by
        rw [← id_tensorHom (carrier D) (mul D)]
        simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]
      _ = (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
          (ι D j ⊗ₘ ((D.obj j).mon.mul ≫ ι D j)) ≫ mul D := by rw [ι_mul]
      _ = (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
          (𝟙 (D.obj j).X ⊗ₘ (D.obj j).mon.mul) ≫
            (ι D j ⊗ₘ ι D j) ≫ mul D := by
        simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
      _ = (α_ (D.obj j).X (D.obj j).X (D.obj j).X).hom ≫
          ((D.obj j).X ◁ (D.obj j).mon.mul) ≫ (D.obj j).mon.mul ≫ ι D j := by
        rw [ι_mul, id_tensorHom]
  rw [hleft, hright]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ ι D j) (D.obj j).mon.mul_assoc

/-- The actual monoid object built on the original underlying colimit. -/
def monoid : Mon C where
  X := carrier D
  mon :=
    { one := one D
      mul := mul D
      one_mul := one_mul D
      mul_one := mul_one D
      mul_assoc := mul_assoc D }

/-- Each original colimit leg is a full original monoid morphism. -/
def leg (j : J) : D.obj j ⟶ monoid D :=
  Mon.Hom.mk' (ι D j) (one_eq D j).symm (ι_mul D j).symm

/-- Every original diagram map retains its full original monoid colimit square. -/
@[reassoc (attr := simp)] theorem leg_naturality {j k : J} (f : j ⟶ k) :
    D.map f ≫ leg D k = leg D j := by
  apply Mon.Hom.ext
  exact ι_naturality D f

/-- The actual monoid cocone retains every original underlying colimit leg. -/
def cocone : Cocone D where
  pt := monoid D
  ι :=
    { app := leg D
      naturality j k f := by
        apply Mon.Hom.ext
        change (D.map f).hom ≫ ι D k = ι D j ≫ 𝟙 (carrier D)
        rw [Category.comp_id]
        exact ι_naturality D f }

/-- The actual underlying colimit descender for an original monoid cocone. -/
def underlyingDesc (c : Cocone D) : carrier D ⟶ c.pt.X :=
  colimit.desc (diagram D) ((Mon.forget C).mapCocone c)

omit [IsSifted J]
  [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape J (tensorRight X)] in
/-- The underlying descender retains each original monoid cocone leg. -/
@[reassoc (attr := simp)] theorem ι_underlyingDesc (c : Cocone D) (j : J) :
    ι D j ≫ underlyingDesc D c = (c.ι.app j).hom :=
  colimit.ι_desc ((Mon.forget C).mapCocone c) j

/-- Descend every full original monoid cocone through the constructed monoid colimit. -/
def desc (c : Cocone D) : monoid D ⟶ c.pt := by
  refine Mon.Hom.mk' (underlyingDesc D c) ?_ ?_
  · let j : J := Classical.arbitrary J
    change one D ≫ underlyingDesc D c = c.pt.mon.one
    rw [one_eq D j, Category.assoc, ι_underlyingDesc]
    exact IsMonHom.one_hom (c.ι.app j).hom
  · change mul D ≫ underlyingDesc D c =
      (underlyingDesc D c ⊗ₘ underlyingDesc D c) ≫ c.pt.mon.mul
    apply tensor_hom_ext D
    intro j
    rw [ι_mul_assoc, ι_underlyingDesc, ← Category.assoc,
      tensorHom_comp_tensorHom, ι_underlyingDesc]
    exact IsMonHom.mul_hom (c.ι.app j).hom

/-- The original descender has the actual underlying colimit descender. -/
@[simp] theorem desc_hom (c : Cocone D) :
    (desc D c).hom = colimit.desc (diagram D) ((Mon.forget C).mapCocone c) := rfl

/-- Every original leg of the monoid descender is the original cocone leg. -/
@[reassoc (attr := simp)] theorem leg_desc (c : Cocone D) (j : J) :
    leg D j ≫ desc D c = c.ι.app j := by
  apply Mon.Hom.ext
  change colimit.ι (diagram D) j ≫
    colimit.desc (diagram D) ((Mon.forget C).mapCocone c) = (c.ι.app j).hom
  exact colimit.ι_desc ((Mon.forget C).mapCocone c) j

/-- The constructed monoid cocone has the full original universal property. -/
def isColimit : IsColimit (cocone D) where
  desc := desc D
  fac := leg_desc D
  uniq c f hf := by
    apply Mon.Hom.ext
    apply colimit.hom_ext
    intro j
    change ι D j ≫ f.hom = ι D j ≫ (desc D c).hom
    rw [desc_hom]
    change ι D j ≫ f.hom = colimit.ι (diagram D) j ≫
      colimit.desc (diagram D) ((Mon.forget C).mapCocone c)
    rw [colimit.ι_desc]
    have h := congrArg Mon.Hom.hom (hf j)
    change ι D j ≫ f.hom = (c.ι.app j).hom at h
    exact h

/-- The original sifted monoid diagram has a constructed colimit. -/
theorem hasColimit : HasColimit D := ⟨⟨cocone D, isColimit D⟩⟩

end CategoryTheory.MonoidalCategory.MonoidWordPushout.MonSiftedColimit

universe w

namespace CategoryTheory.MonoidalCategory.MonoidWordPushout.Presentation

open CategoryTheory Limits MonoidalCategory TensorWord
open scoped MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance : HasColimitsOfShape (Discrete WalkingPair) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete WalkingPair)
local instance : HasColimitsOfShape WalkingReflexivePair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingReflexivePair

/-- Original old and new generating carriers, with both original injections. -/
abbrev generators (A : Mon C) (L : C) : C := A.X ⨿ L

/-- The three original relation carriers: unit, old multiplication, and original attachment. -/
abbrev relations (A : Mon C) (K : C) : C := (𝟙_ C) ⨿ ((A.X ⊗ A.X) ⨿ K)

/-- The original old generator injection into actual tensor words. -/
def oldGenerator (A : Mon C) (L : C) : A.X ⟶ tensorWordObj (generators A L) :=
  coprod.inl ≫ tensorWordGenerator (generators A L)

/-- The original new generator injection into actual tensor words. -/
def newGenerator (A : Mon C) (L : C) : L ⟶ tensorWordObj (generators A L) :=
  coprod.inr ≫ tensorWordGenerator (generators A L)

/-- Original unit, multiplication and attachment maps into the old generator. -/
def relationLeft (A : Mon C) (L : C) {K : C} (k : K ⟶ A.X) :
    relations A K ⟶ tensorWordObj (generators A L) :=
  coprod.desc (A.mon.one ≫ oldGenerator A L)
    (coprod.desc (A.mon.mul ≫ oldGenerator A L) (k ≫ oldGenerator A L))

/-- The actual tensor-word unit, multiplication and original new-letter attachment. -/
def relationRight (A : Mon C) {K L : C} (f : K ⟶ L) :
    relations A K ⟶ tensorWordObj (generators A L) :=
  coprod.desc (tensorWordOne (generators A L))
    (coprod.desc ((oldGenerator A L ⊗ₘ oldGenerator A L) ≫ tensorWordMul (generators A L))
      (f ≫ newGenerator A L))

/-- The first actual monoid map of the original reflexive word presentation. -/
def pairLeft (A : Mon C) (L : C) {K : C} (k : K ⟶ A.X) :
    tensorWordMon (relations A K ⨿ generators A L) ⟶ tensorWordMon (generators A L) :=
  tensorWordLiftHom (tensorWordMon (generators A L))
    (coprod.desc (relationLeft A L k) (tensorWordGenerator (generators A L)))

/-- The second actual monoid map of the original reflexive word presentation. -/
def pairRight (A : Mon C) {K L : C} (f : K ⟶ L) :
    tensorWordMon (relations A K ⨿ generators A L) ⟶ tensorWordMon (generators A L) :=
  tensorWordLiftHom (tensorWordMon (generators A L))
    (coprod.desc (relationRight A f) (tensorWordGenerator (generators A L)))

/-- The first original presentation map retains its full original generator map. -/
@[simp, reassoc] theorem pairLeft_generator (A : Mon C) (L : C) {K : C} (k : K ⟶ A.X) :
    tensorWordGenerator (relations A K ⨿ generators A L) ≫ (pairLeft A L k).hom =
      coprod.desc (relationLeft A L k) (tensorWordGenerator (generators A L)) :=
  tensorWordLift_beta (tensorWordMon (generators A L)) _

/-- The second original presentation map retains its full original generator map. -/
@[simp, reassoc] theorem pairRight_generator (A : Mon C) {K L : C} (f : K ⟶ L) :
    tensorWordGenerator (relations A K ⨿ generators A L) ≫ (pairRight A f).hom =
      coprod.desc (relationRight A f) (tensorWordGenerator (generators A L)) :=
  tensorWordLift_beta (tensorWordMon (generators A L)) _

/-- The actual common monoid section comes from the unchanged original generators. -/
def sectionMap (A : Mon C) (K L : C) :
    tensorWordMon (generators A L) ⟶ tensorWordMon (relations A K ⨿ generators A L) :=
  tensorWordFunctor.map coprod.inr

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The common original section is a section of the first original presentation map. -/
theorem section_left (A : Mon C) (L : C) {K : C} (k : K ⟶ A.X) :
    sectionMap A K L ≫ pairLeft A L k = 𝟙 (tensorWordMon (generators A L)) := by
  apply (tensorWordHomEquiv (generators A L) (tensorWordMon (generators A L))).symm.injective
  change tensorWordGenerator (generators A L) ≫
    (tensorWordMap coprod.inr ≫ (pairLeft A L k).hom) =
    tensorWordGenerator (generators A L) ≫ 𝟙 _
  rw [← Category.assoc, tensorWordGenerator_naturality, Category.assoc,
    pairLeft_generator, coprod.inr_desc, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The common original section is a section of the second original presentation map. -/
theorem section_right (A : Mon C) {K L : C} (f : K ⟶ L) :
    sectionMap A K L ≫ pairRight A f = 𝟙 (tensorWordMon (generators A L)) := by
  apply (tensorWordHomEquiv (generators A L) (tensorWordMon (generators A L))).symm.injective
  change tensorWordGenerator (generators A L) ≫
    (tensorWordMap coprod.inr ≫ (pairRight A f).hom) =
    tensorWordGenerator (generators A L) ≫ 𝟙 _
  rw [← Category.assoc, tensorWordGenerator_naturality, Category.assoc,
    pairRight_generator, coprod.inr_desc, Category.comp_id]

/-- The actual original word-relation diagram, including its constructed common section. -/
def diagram (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    WalkingReflexivePair ⥤ Mon C :=
  reflexivePair (pairLeft A L k) (pairRight A f) (sectionMap A K L)
    (section_left A L k) (section_right A f)

/-- The actual original monoid presentation quotient, with all monoid laws constructed. -/
def monoid (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : Mon C :=
  MonSiftedColimit.monoid (diagram A k f)

/-- The original monoid map from the original tensor-word free monoid into its quotient. -/
def quotientMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    tensorWordMon (generators A L) ⟶ monoid A k f :=
  MonSiftedColimit.leg (diagram A k f) WalkingReflexivePair.zero

/-- The original quotient map equalizes both original full monoid presentation maps. -/
theorem quotient_equalizes (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    pairLeft A L k ≫ quotientMap A k f = pairRight A f ≫ quotientMap A k f := by
  apply Mon.Hom.ext
  exact (MonSiftedColimit.ι_naturality (diagram A k f) WalkingReflexivePair.Hom.left).trans
    (MonSiftedColimit.ι_naturality (diagram A k f) WalkingReflexivePair.Hom.right).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original generating relation maps are equalized on the actual quotient carrier. -/
theorem relations_equalize (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    relationLeft A L k ≫ (quotientMap A k f).hom =
      relationRight A f ≫ (quotientMap A k f).hom := by
  let q : tensorWordObj (generators A L) ⟶ (monoid A k f).X := (quotientMap A k f).hom
  let l : tensorWordObj (relations A K ⨿ generators A L) ⟶ tensorWordObj (generators A L) :=
    (pairLeft A L k).hom
  let r : tensorWordObj (relations A K ⨿ generators A L) ⟶ tensorWordObj (generators A L) :=
    (pairRight A f).hom
  have h := congrArg Mon.Hom.hom (quotient_equalizes A k f)
  change l ≫ q = r ≫ q at h
  have h' := congrArg (fun t => (coprod.inl : relations A K ⟶ relations A K ⨿ generators A L) ≫
    tensorWordGenerator (relations A K ⨿ generators A L) ≫ t) h
  have bleft : tensorWordGenerator (relations A K ⨿ generators A L) ≫ l =
      coprod.desc (relationLeft A L k) (tensorWordGenerator (generators A L)) :=
    pairLeft_generator A L k
  have bright : tensorWordGenerator (relations A K ⨿ generators A L) ≫ r =
      coprod.desc (relationRight A f) (tensorWordGenerator (generators A L)) :=
    pairRight_generator A f
  have bl := congrArg (fun t => (coprod.inl : relations A K ⟶ relations A K ⨿ generators A L) ≫ t ≫ q)
    bleft
  have br := congrArg (fun t => (coprod.inl : relations A K ⟶ relations A K ⨿ generators A L) ≫ t ≫ q)
    bright
  simp only [Category.assoc, coprod.inl_desc_assoc] at bl br
  exact bl.symm.trans (h'.trans br)

/-- The original old-carrier leg of the actual word presentation quotient. -/
def oldMapHom (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : A.X ⟶ (monoid A k f).X :=
  oldGenerator A L ≫ (quotientMap A k f).hom

/-- The original new-letter leg of the actual word presentation quotient. -/
def newMapHom (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : L ⟶ (monoid A k f).X :=
  newGenerator A L ≫ (quotientMap A k f).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The quotient identifies the actual original unit with the original tensor-word unit. -/
theorem unit_relation (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    A.mon.one ≫ oldMapHom A k f =
      tensorWordOne (generators A L) ≫ (quotientMap A k f).hom := by
  let q : tensorWordObj (generators A L) ⟶ (monoid A k f).X := (quotientMap A k f).hom
  have h := relations_equalize A k f
  change relationLeft A L k ≫ q = relationRight A f ≫ q at h
  have h' := congrArg (fun t => (coprod.inl : 𝟙_ C ⟶ relations A K) ≫ t) h
  simpa only [oldMapHom, q, relationLeft, relationRight, Category.assoc, coprod.inl_desc_assoc] using h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The quotient identifies the actual old multiplication with its original word product. -/
theorem multiplication_relation (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    A.mon.mul ≫ oldMapHom A k f =
      (oldGenerator A L ⊗ₘ oldGenerator A L) ≫
        tensorWordMul (generators A L) ≫ (quotientMap A k f).hom := by
  let q : tensorWordObj (generators A L) ⟶ (monoid A k f).X := (quotientMap A k f).hom
  have h := relations_equalize A k f
  change relationLeft A L k ≫ q = relationRight A f ≫ q at h
  have h' := congrArg (fun t => (coprod.inl : A.X ⊗ A.X ⟶ (A.X ⊗ A.X) ⨿ K) ≫
    (coprod.inr : (A.X ⊗ A.X) ⨿ K ⟶ relations A K) ≫ t) h
  simpa only [oldMapHom, q, relationLeft, relationRight, Category.assoc, coprod.inr_desc_assoc,
    coprod.inl_desc_assoc] using h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original attachment square holds on the constructed quotient carrier. -/
theorem attachment_relation (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    k ≫ oldMapHom A k f = f ≫ newMapHom A k f := by
  let q : tensorWordObj (generators A L) ⟶ (monoid A k f).X := (quotientMap A k f).hom
  have h := relations_equalize A k f
  change relationLeft A L k ≫ q = relationRight A f ≫ q at h
  have h' := congrArg (fun t => (coprod.inr : K ⟶ (A.X ⊗ A.X) ⨿ K) ≫
    (coprod.inr : (A.X ⊗ A.X) ⨿ K ⟶ relations A K) ≫ t) h
  simpa only [oldMapHom, newMapHom, q, relationLeft, relationRight, Category.assoc,
    coprod.inr_desc_assoc] using h'

/-- The original old unit is preserved by the constructed old-carrier map. -/
theorem oldMap_one (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    A.mon.one ≫ oldMapHom A k f = (monoid A k f).mon.one := by
  exact (unit_relation A k f).trans
    (IsMonHom.one_hom (quotientMap A k f).hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original old multiplication is preserved by the constructed old-carrier map. -/
theorem oldMap_mul (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    A.mon.mul ≫ oldMapHom A k f =
      (oldMapHom A k f ⊗ₘ oldMapHom A k f) ≫ (monoid A k f).mon.mul := by
  have hq : tensorWordMul (generators A L) ≫ (quotientMap A k f).hom =
      ((quotientMap A k f).hom ⊗ₘ (quotientMap A k f).hom) ≫ (monoid A k f).mon.mul :=
    IsMonHom.mul_hom (quotientMap A k f).hom
  calc
    A.mon.mul ≫ oldMapHom A k f = (oldGenerator A L ⊗ₘ oldGenerator A L) ≫
        tensorWordMul (generators A L) ≫ (quotientMap A k f).hom :=
      multiplication_relation A k f
    _ = (oldGenerator A L ⊗ₘ oldGenerator A L) ≫
        ((quotientMap A k f).hom ⊗ₘ (quotientMap A k f).hom) ≫ (monoid A k f).mon.mul := by
      rw [hq]
    _ = (oldMapHom A k f ⊗ₘ oldMapHom A k f) ≫ (monoid A k f).mon.mul := by
      rw [← Category.assoc, tensorHom_comp_tensorHom]
      rfl

/-- The old monoid maps to the constructed quotient as an actual monoid morphism. -/
def oldMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) : A ⟶ monoid A k f :=
  Mon.Hom.mk' (oldMapHom A k f) (oldMap_one A k f) (oldMap_mul A k f)

/-- The full original free new-letter monoid maps to the constructed quotient. -/
def newMap (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L) :
    tensorWordMon L ⟶ monoid A k f :=
  tensorWordLiftHom (monoid A k f) (newMapHom A k f)

/-- The full free new-letter map has exactly the original new-letter carrier leg. -/
@[simp, reassoc] theorem newMap_generator (A : Mon C) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) :
    tensorWordGenerator L ≫ (newMap A k f).hom = newMapHom A k f :=
  tensorWordLift_beta (monoid A k f) _

/-- An arbitrary original old monoid map and original new-letter map give the actual generator map. -/
def targetGenerator (A M : Mon C) (a : A ⟶ M) {L : C} (g : L ⟶ M.X) :
    generators A L ⟶ M.X := coprod.desc a.hom g

/-- The original target generator map extends to all actual tensor words. -/
def targetMap (A M : Mon C) (a : A ⟶ M) {L : C} (g : L ⟶ M.X) :
    tensorWordMon (generators A L) ⟶ M :=
  tensorWordLiftHom M (targetGenerator A M a g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original old generator retains the original target monoid map. -/
@[reassoc (attr := simp)] theorem targetMap_old (A M : Mon C) (a : A ⟶ M)
    {L : C} (g : L ⟶ M.X) : oldGenerator A L ≫ (targetMap A M a g).hom = a.hom := by
  dsimp only [oldGenerator]
  rw [Category.assoc]
  change coprod.inl ≫
    (tensorWordGenerator (generators A L) ≫ tensorWordLift M (coprod.desc a.hom g)) = a.hom
  rw [tensorWordLift_beta, coprod.inl_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original new generator retains the original target letter map. -/
@[reassoc (attr := simp)] theorem targetMap_new (A M : Mon C) (a : A ⟶ M)
    {L : C} (g : L ⟶ M.X) : newGenerator A L ≫ (targetMap A M a g).hom = g := by
  dsimp only [newGenerator]
  rw [Category.assoc]
  change coprod.inr ≫
    (tensorWordGenerator (generators A L) ≫ tensorWordLift M (coprod.desc a.hom g)) = g
  rw [tensorWordLift_beta, coprod.inr_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original compatible target maps satisfy every original defining relation. -/
theorem target_relations (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    relationLeft A L k ≫ (targetMap A M a g).hom =
      relationRight A f ≫ (targetMap A M a g).hom := by
  let t : tensorWordObj (generators A L) ⟶ M.X := (targetMap A M a g).hom
  have ho : oldGenerator A L ≫ t = a.hom := targetMap_old A M a g
  have hn : newGenerator A L ≫ t = g := targetMap_new A M a g
  have hu : tensorWordOne (generators A L) ≫ t = M.mon.one := IsMonHom.one_hom t
  have hm : tensorWordMul (generators A L) ≫ t = (t ⊗ₘ t) ≫ M.mon.mul := IsMonHom.mul_hom t
  change relationLeft A L k ≫ t = relationRight A f ≫ t
  apply coprod.hom_ext
  · simp only [relationLeft, relationRight, Category.assoc, coprod.inl_desc_assoc]
    rw [ho, hu]
    exact IsMonHom.one_hom a.hom
  · simp only [relationLeft, relationRight, coprod.inr_desc_assoc]
    apply coprod.hom_ext
    · simp only [Category.assoc, coprod.inl_desc_assoc]
      rw [ho, hm, ← Category.assoc, tensorHom_comp_tensorHom, ho]
      exact IsMonHom.mul_hom a.hom
    · simp only [Category.assoc, coprod.inr_desc_assoc]
      rw [ho, hn]
      exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual target monoid extension equalizes the full original reflexive presentation. -/
theorem target_equalizes (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    pairLeft A L k ≫ targetMap A M a g = pairRight A f ≫ targetMap A M a g := by
  let t : tensorWordObj (generators A L) ⟶ M.X := (targetMap A M a g).hom
  let l : tensorWordObj (relations A K ⨿ generators A L) ⟶ tensorWordObj (generators A L) :=
    (pairLeft A L k).hom
  let r : tensorWordObj (relations A K ⨿ generators A L) ⟶ tensorWordObj (generators A L) :=
    (pairRight A f).hom
  have bl : tensorWordGenerator (relations A K ⨿ generators A L) ≫ l =
      coprod.desc (relationLeft A L k) (tensorWordGenerator (generators A L)) :=
    pairLeft_generator A L k
  have br : tensorWordGenerator (relations A K ⨿ generators A L) ≫ r =
      coprod.desc (relationRight A f) (tensorWordGenerator (generators A L)) :=
    pairRight_generator A f
  have hc : coprod.desc (relationLeft A L k) (tensorWordGenerator (generators A L)) ≫ t =
      coprod.desc (relationRight A f) (tensorWordGenerator (generators A L)) ≫ t := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc]
      exact target_relations A M a k f g h
    · simp only [coprod.inr_desc_assoc]
  apply (tensorWordHomEquiv (relations A K ⨿ generators A L) M).symm.injective
  change tensorWordGenerator (relations A K ⨿ generators A L) ≫ (l ≫ t) =
    tensorWordGenerator (relations A K ⨿ generators A L) ≫ (r ≫ t)
  simpa only [Category.assoc] using
    (congrArg (fun z => z ≫ t) bl).trans (hc.trans (congrArg (fun z => z ≫ t) br.symm))

/-- The actual original target data form a monoid cocone on the original word presentation. -/
def targetCocone (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    Cocone (diagram A k f) :=
  ReflexiveCofork.mk (F := diagram A k f) (targetMap A M a g) (target_equalizes A M a k f g h)

/-- The full original compatible target data have a constructed monoid descender. -/
def desc (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    monoid A k f ⟶ M :=
  MonSiftedColimit.desc (diagram A k f) (targetCocone A M a k f g h)

/-- The descender retains the full original target map on every actual tensor word. -/
@[reassoc (attr := simp)] theorem quotient_desc (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    quotientMap A k f ≫ desc A M a k f g h = targetMap A M a g :=
  MonSiftedColimit.leg_desc (diagram A k f) (targetCocone A M a k f g h) WalkingReflexivePair.zero

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original target monoid map is the old leg of the full descender. -/
@[reassoc (attr := simp)] theorem oldMap_desc (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    oldMap A k f ≫ desc A M a k f g h = a := by
  apply Mon.Hom.ext
  have hd := congrArg Mon.Hom.hom (quotient_desc A M a k f g h)
  change (quotientMap A k f).hom ≫ (desc A M a k f g h).hom = (targetMap A M a g).hom at hd
  change (oldGenerator A L ≫ (quotientMap A k f).hom) ≫ (desc A M a k f g h).hom = a.hom
  rw [Category.assoc, hd, targetMap_old]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original target new-letter map is retained by the full descender. -/
@[reassoc (attr := simp)] theorem newMapHom_desc (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    newMapHom A k f ≫ (desc A M a k f g h).hom = g := by
  have hd := congrArg Mon.Hom.hom (quotient_desc A M a k f g h)
  change (quotientMap A k f).hom ≫ (desc A M a k f g h).hom = (targetMap A M a g).hom at hd
  change (newGenerator A L ≫ (quotientMap A k f).hom) ≫ (desc A M a k f g h).hom = g
  rw [Category.assoc, hd, targetMap_new]

/-- The complete original target free-monoid map is retained by the descender. -/
theorem newMap_desc (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g) :
    newMap A k f ≫ desc A M a k f g h = tensorWordLiftHom M g := by
  apply (tensorWordHomEquiv L M).symm.injective
  change tensorWordGenerator L ≫ ((newMap A k f).hom ≫ (desc A M a k f g h).hom) =
    tensorWordGenerator L ≫ tensorWordLift M g
  have hh := congrArg (fun t => t ≫ (desc A M a k f g h).hom) (newMap_generator A k f)
  have h' := hh.trans (newMapHom_desc A M a k f g h)
  exact ((Category.assoc (tensorWordGenerator L) (newMap A k f).hom
    (desc A M a k f g h).hom).symm.trans h').trans (tensorWordLift_beta M g).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original quotient monoid is generated by the actual original full tensor-word map. -/
theorem quotient_hom_ext (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    {M : Mon C} {p q : monoid A k f ⟶ M}
    (h : quotientMap A k f ≫ p = quotientMap A k f ≫ q) : p = q := by
  apply (MonSiftedColimit.isColimit (diagram A k f)).hom_ext
  intro j
  cases j with
  | zero => exact h
  | one =>
    change MonSiftedColimit.leg (diagram A k f) WalkingReflexivePair.one ≫ p =
      MonSiftedColimit.leg (diagram A k f) WalkingReflexivePair.one ≫ q
    rw [← MonSiftedColimit.leg_naturality (diagram A k f) WalkingReflexivePair.Hom.left]
    change (pairLeft A L k ≫ quotientMap A k f) ≫ p =
      (pairLeft A L k ≫ quotientMap A k f) ≫ q
    rw [Category.assoc, Category.assoc, h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original old and new maps jointly determine every full quotient monoid map. -/
theorem hom_ext (A : Mon C) {K L : C} (k : K ⟶ A.X) (f : K ⟶ L)
    {M : Mon C} {p q : monoid A k f ⟶ M}
    (ho : oldMap A k f ≫ p = oldMap A k f ≫ q)
    (hn : newMapHom A k f ≫ p.hom = newMapHom A k f ≫ q.hom) : p = q := by
  apply quotient_hom_ext A k f
  apply (tensorWordHomEquiv (generators A L) M).symm.injective
  let z : tensorWordObj (generators A L) ⟶ (monoid A k f).X := (quotientMap A k f).hom
  change tensorWordGenerator (generators A L) ≫ (z ≫ p.hom) =
    tensorWordGenerator (generators A L) ≫ (z ≫ q.hom)
  apply coprod.hom_ext
  · have hh := congrArg Mon.Hom.hom ho
    change (oldGenerator A L ≫ z) ≫ p.hom = (oldGenerator A L ≫ z) ≫ q.hom at hh
    simpa only [oldGenerator, Category.assoc] using hh
  · change (newGenerator A L ≫ z) ≫ p.hom = (newGenerator A L ≫ z) ≫ q.hom at hn
    simpa only [newGenerator, Category.assoc] using hn

/-- Every original compatible quotient monoid map is the constructed original descender. -/
theorem desc_unique (A M : Mon C) (a : A ⟶ M) {K L : C}
    (k : K ⟶ A.X) (f : K ⟶ L) (g : L ⟶ M.X) (h : k ≫ a.hom = f ≫ g)
    (p : monoid A k f ⟶ M) (ho : oldMap A k f ≫ p = a)
    (hn : newMapHom A k f ≫ p.hom = g) : p = desc A M a k f g h :=
  hom_ext A k f (ho.trans (oldMap_desc A M a k f g h).symm)
    (hn.trans (newMapHom_desc A M a k f g h).symm)

end CategoryTheory.MonoidalCategory.MonoidWordPushout.Presentation

namespace CategoryTheory.MonoidalCategory.MonoidWordPushout

open CategoryTheory Limits MonoidalCategory TensorWord
open scoped MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]

local instance : HasColimitsOfShape (Discrete ℕ) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete ℕ)
local instance : HasColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete (Σ _ : ℕ, ℕ))
local instance : HasColimitsOfShape (Discrete WalkingPair) C :=
  HasColimitsOfShape.of_essentiallySmall C (Discrete WalkingPair)
local instance : HasColimitsOfShape WalkingReflexivePair C :=
  HasColimitsOfShape.of_essentiallySmall C WalkingReflexivePair

/-- Retain the original attaching monoid map by restricting it to its original degree-one generators. -/
def attachingValue (A : Mon C) {K : C} (a : tensorWordMon K ⟶ A) : K ⟶ A.X :=
  tensorWordGenerator K ≫ a.hom

/-- The actual monoid pushout carrier is constructed from the original arrow and original attaching monoid map. -/
def freeAttachment (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) : Mon C :=
  Presentation.monoid A (attachingValue A a) f

/-- The actual original old monoid leg of the constructed free attachment. -/
def oldι (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) : A ⟶ freeAttachment A f a :=
  Presentation.oldMap A (attachingValue A a) f

/-- The actual original free new-letter monoid leg of the constructed attachment. -/
def newι (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    tensorWordMon L ⟶ freeAttachment A f a :=
  Presentation.newMap A (attachingValue A a) f

/-- The actual original new-letter carrier leg of the constructed attachment. -/
def newLetterι (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    L ⟶ (freeAttachment A f a).X :=
  Presentation.newMapHom A (attachingValue A a) f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full original free-algebra attachment square commutes in the actual monoid category. -/
theorem originalSquare (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    a ≫ oldι A f a = tensorWordFunctor.map f ≫ newι A f a := by
  apply (tensorWordHomEquiv K (freeAttachment A f a)).symm.injective
  change tensorWordGenerator K ≫ (a.hom ≫ (oldι A f a).hom) =
    tensorWordGenerator K ≫ (tensorWordMap f ≫ (newι A f a).hom)
  calc
    tensorWordGenerator K ≫ (a.hom ≫ (oldι A f a).hom) =
        attachingValue A a ≫ Presentation.oldMapHom A (attachingValue A a) f :=
      (Category.assoc _ _ _).symm
    _ = f ≫ Presentation.newMapHom A (attachingValue A a) f :=
      Presentation.attachment_relation A (attachingValue A a) f
    _ = tensorWordGenerator K ≫ (tensorWordMap f ≫ (newι A f a).hom) := by
      rw [← Category.assoc, tensorWordGenerator_naturality, Category.assoc]
      exact congrArg (fun t => f ≫ t) (Presentation.newMap_generator A (attachingValue A a) f).symm

/-- The literal original monoid pushout cocone has the original old and new legs. -/
def originalCocone (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    PushoutCocone a (tensorWordFunctor.map f) :=
  PushoutCocone.mk (oldι A f a) (newι A f a) (originalSquare A f a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The entire original target monoid square gives precisely its original generator compatibility. -/
theorem targetCompatibility (A M : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A)
    (b : A ⟶ M) (c : tensorWordMon L ⟶ M) (h : a ≫ b = tensorWordFunctor.map f ≫ c) :
    attachingValue A a ≫ b.hom = f ≫ (tensorWordGenerator L ≫ c.hom) := by
  have ht := congrArg Mon.Hom.hom h
  have ht' := congrArg (fun t => tensorWordGenerator K ≫ t) ht
  change tensorWordGenerator K ≫ (a.hom ≫ b.hom) =
    tensorWordGenerator K ≫ (tensorWordMap f ≫ c.hom) at ht'
  calc
    attachingValue A a ≫ b.hom = tensorWordGenerator K ≫ (a.hom ≫ b.hom) :=
      Category.assoc _ _ _
    _ = tensorWordGenerator K ≫ (tensorWordMap f ≫ c.hom) := ht'
    _ = f ≫ (tensorWordGenerator L ≫ c.hom) := by
      rw [← Category.assoc, tensorWordGenerator_naturality, Category.assoc]

/-- Every entire original target cocone has its actual original monoid descender. -/
def originalDesc (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A)
    (c : PushoutCocone a (tensorWordFunctor.map f)) : freeAttachment A f a ⟶ c.pt :=
  Presentation.desc A c.pt c.inl (attachingValue A a) f (tensorWordGenerator L ≫ c.inr.hom)
    (targetCompatibility A c.pt f a c.inl c.inr c.condition)

/-- The original old target monoid map is retained by the full original descender. -/
@[reassoc (attr := simp)] theorem oldι_originalDesc (A : Mon C) {K L : C}
    (f : K ⟶ L) (a : tensorWordMon K ⟶ A) (c : PushoutCocone a (tensorWordFunctor.map f)) :
    oldι A f a ≫ originalDesc A f a c = c.inl :=
  Presentation.oldMap_desc A c.pt c.inl (attachingValue A a) f _ _

/-- The original full new target free-monoid map is retained by the full original descender. -/
@[reassoc (attr := simp)] theorem newι_originalDesc (A : Mon C) {K L : C}
    (f : K ⟶ L) (a : tensorWordMon K ⟶ A) (c : PushoutCocone a (tensorWordFunctor.map f)) :
    newι A f a ≫ originalDesc A f a c = c.inr := by
  exact (Presentation.newMap_desc A c.pt c.inl (attachingValue A a) f
    (tensorWordGenerator L ≫ c.inr.hom) _).trans (tensorWordLiftUnique _ c.inr rfl).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every full original target map is uniquely the original constructed monoid descender. -/
theorem originalDesc_unique (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A)
    (c : PushoutCocone a (tensorWordFunctor.map f)) (p : freeAttachment A f a ⟶ c.pt)
    (ho : oldι A f a ≫ p = c.inl) (hn : newι A f a ≫ p = c.inr) : p = originalDesc A f a c := by
  have hval : Presentation.newMapHom A (attachingValue A a) f ≫ p.hom =
      tensorWordGenerator L ≫ c.inr.hom := by
    have hb := congrArg (fun t => t ≫ p.hom) (Presentation.newMap_generator A (attachingValue A a) f)
    have hq := congrArg (fun t => tensorWordGenerator L ≫ t) (congrArg Mon.Hom.hom hn)
    change tensorWordGenerator L ≫ ((newι A f a).hom ≫ p.hom) =
      tensorWordGenerator L ≫ c.inr.hom at hq
    exact hb.symm.trans ((Category.assoc _ _ _).trans hq)
  exact Presentation.desc_unique A c.pt c.inl (attachingValue A a) f
    (tensorWordGenerator L ≫ c.inr.hom) _ p ho hval

/-- The full original monoid cocone is a pushout, with every original diagram map retained. -/
def originalCoconeIsColimit (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    IsColimit (originalCocone A f a) :=
  PushoutCocone.IsColimit.mk (originalSquare A f a) (originalDesc A f a)
    (oldι_originalDesc A f a) (newι_originalDesc A f a) (originalDesc_unique A f a)

/-- The constructed actual monoid is the pushout of the complete original free-algebra diagram. -/
theorem originalIsPushout (A : Mon C) {K L : C} (f : K ⟶ L) (a : tensorWordMon K ⟶ A) :
    IsPushout a (tensorWordFunctor.map f) (oldι A f a) (newι A f a) :=
  IsPushout.of_isColimit (originalCoconeIsColimit A f a)

end CategoryTheory.MonoidalCategory.MonoidWordPushout
