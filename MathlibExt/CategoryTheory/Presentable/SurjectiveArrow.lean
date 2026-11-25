/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Types.Basic
public import MathlibExt.CategoryTheory.Presentable.FullSubcategory

/-!
# The actual category of surjective arrows of sets

The full subcategory retains the original functions and commutative squares.
Colimits are the actual arrow-category colimits. Finite arrows supply compact
strong generators, so both the category and its original inclusion are
accessible. No weak-factorization or desired accessibility data is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uJ vJ

open CategoryTheory Limits Opposite TypeCat

namespace CategoryTheory.Presentable

/-- The original functions which are surjective. -/
def surjectiveArrows : ObjectProperty (Arrow (Type w)) :=
  fun f => Function.Surjective f.hom

/-- Objects are original surjective functions; morphisms are their original squares. -/
abbrev SurjectiveArrow := surjectiveArrows.{w}.FullSubcategory

instance : surjectiveArrows.{w}.IsClosedUnderIsomorphisms where
  of_iso {f g} e hf := by
    have h : (MorphismProperty.epimorphisms (Type w)) f.hom :=
      (epi_iff_surjective f.hom).mpr hf
    have h' : (MorphismProperty.epimorphisms (Type w)) g.hom :=
      ((MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff e).mp h
    exact (epi_iff_surjective g.hom).mp h'

/-- The actual colimit of surjective arrows is surjective. -/
theorem surjective_colimit {J : Type uJ} [Category.{vJ} J]
    [HasColimitsOfShape J (Type w)]
    (F : J ⥤ Arrow (Type w)) [HasColimit F]
    (hF : ∀ j, Function.Surjective (F.obj j).hom) :
    Function.Surjective (colimit F).hom := by
  let (j : J) : Epi (F.obj j).hom := (epi_iff_surjective _).mpr (hF j)
  have hRight := isColimitOfPreserves (Arrow.rightFunc : Arrow (Type w) ⥤ Type w)
    (colimit.isColimit F)
  have hEpi : Epi (colimit F).hom := by
    constructor
    intro Z g h eq
    apply hRight.hom_ext
    intro j
    change (colimit.ι F j).right ≫ g = (colimit.ι F j).right ≫ h
    apply (cancel_epi (F.obj j).hom).mp
    have hw := (colimit.ι F j).w
    calc
      (F.obj j).hom ≫ ((colimit.ι F j).right ≫ g) =
          (colimit.ι F j).left ≫ ((colimit F).hom ≫ g) := by
        rw [← Category.assoc, ← hw, Category.assoc]
      _ = (colimit.ι F j).left ≫ ((colimit F).hom ≫ h) := by rw [eq]
      _ = (F.obj j).hom ≫ ((colimit.ι F j).right ≫ h) := by
        rw [← Category.assoc, hw, Category.assoc]
  exact (epi_iff_surjective _).mp hEpi

instance (J : Type uJ) [Category.{vJ} J] [HasColimitsOfShape J (Type w)] :
    surjectiveArrows.{w}.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  exact surjective_colimit F hF

/-- Working-size colimits keep the original surjective functions and square maps. -/
instance : HasColimitsOfSize.{w, w} SurjectiveArrow.{w} where
  has_colimits_of_shape J _ := by infer_instance

/-- The actual full inclusion preserves every working-size colimit. -/
instance : PreservesColimitsOfSize.{w, w} surjectiveArrows.{w}.ι where
  preservesColimitsOfShape := by infer_instance

/-- The identity on a point detects every original source element. -/
def pointArrow : SurjectiveArrow.{w} :=
  ⟨Arrow.mk (𝟙 (PUnit.{w + 1})), fun x => ⟨x, rfl⟩⟩

/-- The fold of two points detects whether two original source elements share a fiber. -/
def relationArrow : SurjectiveArrow.{w} :=
  ⟨Arrow.mk (ofHom (fun _ : ULift.{w} Bool => (PUnit.unit : PUnit.{w + 1}))), by
    intro x
    cases x
    exact ⟨⟨false⟩, rfl⟩⟩

/-- A point of the original domain gives its actual square from the point arrow. -/
def pointMap (A : SurjectiveArrow.{w}) (x : A.obj.left) : pointArrow ⟶ A :=
  ObjectProperty.homMk (Arrow.homMk
    (ofHom (fun _ => x)) (ofHom (fun _ => A.obj.hom x)) (by ext; rfl))

@[simp]
theorem pointMap_left (A : SurjectiveArrow.{w}) (x : A.obj.left) (t : PUnit.{w + 1}) :
    (pointMap A x).hom.left t = x := rfl

attribute [local instance] Cardinal.fact_isRegular_aleph0

private theorem finite_arrow_presentable {X Y : Type w} [Finite X] [Finite Y]
    (f : X ⟶ Y) : IsCardinalPresentable (Arrow.mk f) Cardinal.aleph0.{w} := by
  have : IsCardinalPresentable X Cardinal.aleph0.{w} :=
    (hasCardinalLT_of_finite X Cardinal.aleph0.{w} le_rfl).isCardinalPresentable
  have : IsCardinalPresentable Y Cardinal.aleph0.{w} :=
    (hasCardinalLT_of_finite Y Cardinal.aleph0.{w} le_rfl).isCardinalPresentable
  exact Comma.isCardinalPresentable_mk
    (F₁ := 𝟭 (Type w)) (F₂ := 𝟭 (Type w)) (κ := Cardinal.aleph0.{w}) f

instance : IsCardinalPresentable pointArrow.{w} Cardinal.aleph0.{w} := by
  have : IsCardinalPresentable pointArrow.{w}.obj Cardinal.aleph0.{w} :=
    finite_arrow_presentable (𝟙 (PUnit.{w + 1}))
  exact surjectiveArrows.isCardinalPresentable_of_ι Cardinal.aleph0.{w} pointArrow

instance : IsCardinalPresentable relationArrow.{w} Cardinal.aleph0.{w} := by
  have : IsCardinalPresentable relationArrow.{w}.obj Cardinal.aleph0.{w} :=
    finite_arrow_presentable
      (ofHom (fun _ : ULift.{w} Bool => (PUnit.unit : PUnit.{w + 1})))
  exact surjectiveArrows.isCardinalPresentable_of_ι Cardinal.aleph0.{w} relationArrow

/-- The square equation on the original functions and elements. -/
theorem square_apply {A B : SurjectiveArrow.{w}} (f : A ⟶ B) (x : A.obj.left) :
    B.obj.hom (f.hom.left x) = f.hom.right (A.obj.hom x) :=
  congrArg (fun k : A.obj.left ⟶ B.obj.right => k x) f.hom.w

/-- The source component determines the whole original square because its source is surjective. -/
theorem hom_ext_left {A B : SurjectiveArrow.{w}} (f g : A ⟶ B)
    (h : f.hom.left = g.hom.left) : f = g := by
  apply ObjectProperty.hom_ext
  apply Arrow.hom_ext _ _ h
  ext y
  obtain ⟨x, rfl⟩ := A.property y
  calc
    f.hom.right (A.obj.hom x) = B.obj.hom (f.hom.left x) := (square_apply f x).symm
    _ = B.obj.hom (g.hom.left x) := congrArg B.obj.hom (congrArg (fun k => k x) h)
    _ = g.hom.right (A.obj.hom x) := square_apply g x

/-- Two elements in a common original fiber give an actual square from the fold arrow. -/
def relationMap (A : SurjectiveArrow.{w}) (x₀ x₁ : A.obj.left)
    (h : A.obj.hom x₀ = A.obj.hom x₁) : relationArrow ⟶ A :=
  ObjectProperty.homMk (Arrow.homMk
    (ofHom (fun b : ULift.{w} Bool => if b.down then x₁ else x₀))
    (ofHom (fun _ => A.obj.hom x₀)) (by
      ext b
      rcases b with ⟨b⟩
      cases b
      · rfl
      · exact h.symm))

@[simp]
theorem relationMap_left_false (A : SurjectiveArrow.{w}) (x₀ x₁ : A.obj.left)
    (h : A.obj.hom x₀ = A.obj.hom x₁) :
    (relationMap A x₀ x₁ h).hom.left ⟨false⟩ = x₀ := rfl

@[simp]
theorem relationMap_left_true (A : SurjectiveArrow.{w}) (x₀ x₁ : A.obj.left)
    (h : A.obj.hom x₀ = A.obj.hom x₁) :
    (relationMap A x₀ x₁ h).hom.left ⟨true⟩ = x₁ := rfl

/-- Monomorphisms of surjective arrows are injective on their original domains. -/
theorem left_injective_of_mono {A B : SurjectiveArrow.{w}} (f : A ⟶ B) [Mono f] :
    Function.Injective f.hom.left := by
  intro x y h
  have h' : pointMap A x ≫ f = pointMap A y ≫ f := by
    apply hom_ext_left
    ext t
    exact h
  have h'' := (cancel_mono f).mp h'
  exact congrArg (fun k : pointArrow ⟶ A => k.hom.left PUnit.unit) h''

/-- Actual lifting of the point and fiber squares makes a monomorphism an isomorphism. -/
theorem isIso_of_point_relation_surjective {A B : SurjectiveArrow.{w}}
    (f : A ⟶ B) [Mono f]
    (hPoint : Function.Surjective (fun k : pointArrow ⟶ A => k ≫ f))
    (hRelation : Function.Surjective (fun k : relationArrow ⟶ A => k ≫ f)) :
    IsIso f := by
  have hLeftInjective := left_injective_of_mono f
  have hLeftSurjective : Function.Surjective f.hom.left := by
    intro x
    obtain ⟨k, hk⟩ := hPoint (pointMap B x)
    exact ⟨k.hom.left PUnit.unit,
      congrArg (fun q : pointArrow ⟶ B => q.hom.left PUnit.unit) hk⟩
  have hRightSurjective : Function.Surjective f.hom.right := by
    intro y
    obtain ⟨x, hx⟩ := B.property y
    obtain ⟨a, ha⟩ := hLeftSurjective x
    refine ⟨A.obj.hom a, ?_⟩
    calc
      f.hom.right (A.obj.hom a) = B.obj.hom (f.hom.left a) := (square_apply f a).symm
      _ = B.obj.hom x := congrArg B.obj.hom ha
      _ = y := hx
  have hRightInjective : Function.Injective f.hom.right := by
    intro y₀ y₁ hy
    obtain ⟨x₀, rfl⟩ := A.property y₀
    obtain ⟨x₁, rfl⟩ := A.property y₁
    have hFiber : B.obj.hom (f.hom.left x₀) = B.obj.hom (f.hom.left x₁) :=
      (square_apply f x₀).trans (hy.trans (square_apply f x₁).symm)
    obtain ⟨k, hk⟩ := hRelation (relationMap B (f.hom.left x₀) (f.hom.left x₁) hFiber)
    have h₀ : k.hom.left ⟨false⟩ = x₀ := hLeftInjective
      (congrArg (fun q : relationArrow ⟶ B => q.hom.left ⟨false⟩) hk)
    have h₁ : k.hom.left ⟨true⟩ = x₁ := hLeftInjective
      (congrArg (fun q : relationArrow ⟶ B => q.hom.left ⟨true⟩) hk)
    calc
      A.obj.hom x₀ = A.obj.hom (k.hom.left ⟨false⟩) := by rw [h₀]
      _ = k.hom.right PUnit.unit := square_apply k ⟨false⟩
      _ = A.obj.hom (k.hom.left ⟨true⟩) := (square_apply k ⟨true⟩).symm
      _ = A.obj.hom x₁ := by rw [h₁]
  have : IsIso f.hom.left := (isIso_iff_bijective _).mpr
    ⟨hLeftInjective, hLeftSurjective⟩
  have : IsIso f.hom.right := (isIso_iff_bijective _).mpr
    ⟨hRightInjective, hRightSurjective⟩
  exact (ObjectProperty.isIso_hom_iff f).mp
    (Arrow.isIso_of_isIso_left_of_isIso_right f.hom)

/-- The two actual finite arrows, indexed by a working-small type. -/
def finiteGenerator : Bool → SurjectiveArrow.{w}
  | false => pointArrow
  | true => relationArrow

/-- A working-small family detecting domains and fibers. -/
def finiteGenerators : ObjectProperty SurjectiveArrow.{w} :=
  .ofObj finiteGenerator

instance : ObjectProperty.Small.{w} finiteGenerators.{w} := by
  unfold finiteGenerators
  infer_instance

/-- Both actual finite generators are finitely presentable in the original full category. -/
theorem finiteGenerators_presentable :
    finiteGenerators.{w} ≤ isCardinalPresentable SurjectiveArrow.{w} Cardinal.aleph0.{w} := by
  rintro _ ⟨b⟩
  cases b
  · change IsCardinalPresentable pointArrow.{w} Cardinal.aleph0.{w}
    infer_instance
  · change IsCardinalPresentable relationArrow.{w} Cardinal.aleph0.{w}
    infer_instance

/-- Domain elements and fiber relations form a strong generator for the actual category. -/
theorem finiteGenerators_isStrongGenerator : finiteGenerators.{w}.IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, ?_⟩
  · intro A B f g h
    apply hom_ext_left
    ext x
    exact congrArg (fun q : pointArrow ⟶ B => q.hom.left PUnit.unit)
      (h pointArrow (.mk false) (pointMap A x))
  · intro A B f _ h
    exact isIso_of_point_relation_surjective f
      (h pointArrow (.mk false)) (h relationArrow (.mk true))

/-- The actual finite colimit closure supplies the filtered compact presentations. -/
def compactGenerators : ObjectProperty SurjectiveArrow.{w} :=
  finiteGenerators.colimitsCardinalClosure Cardinal.aleph0.{w}

/-- A genuine small compact generating presentation, produced from the two arrows above. -/
theorem compactGenerators_isCardinalFilteredGenerator :
    compactGenerators.{w}.IsCardinalFilteredGenerator Cardinal.aleph0.{w} := by
  unfold compactGenerators
  have := finiteGenerators_isStrongGenerator.isDense_colimitsCardinalClosure_ι
    finiteGenerators_presentable
  exact IsCardinalFilteredGenerator.of_isDense_ι
    (finiteGenerators.{w}.colimitsCardinalClosure Cardinal.aleph0.{w}) Cardinal.aleph0.{w}
    (finiteGenerators.{w}.colimitsCardinalClosure_le_isCardinalPresentable
      finiteGenerators_presentable)

/-- Surjective functions and their original squares form a locally finitely presentable category. -/
instance : IsCardinalLocallyPresentable SurjectiveArrow.{w} Cardinal.aleph0.{w} := by
  exact (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator _ _).mpr
    ⟨finiteGenerators, inferInstance, finiteGenerators_isStrongGenerator,
      finiteGenerators_presentable⟩

/-- The actual regular accessibility rank is `aleph0`. -/
theorem surjectiveArrow_accessible :
    IsAccessibleCategory.{w} SurjectiveArrow.{w} ∧
      Functor.IsAccessible.{w} surjectiveArrows.{w}.ι := by
  constructor
  · exact ⟨Cardinal.aleph0.{w}, inferInstance, inferInstance⟩
  · exact Functor.isAccessible_of_isCardinalAccessible _ Cardinal.aleph0.{w}

end CategoryTheory.Presentable
