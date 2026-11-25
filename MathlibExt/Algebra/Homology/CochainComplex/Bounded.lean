/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Bounded cochain categories

Bounded cochains form the full subcategory of cochains whose terms vanish
outside a finite integer interval. Inclusion and evaluation retain their
objects and maps.

Zero and binary biproducts are bounded, with support given by the union of
the support bounds. Degreewise split monomorphisms, their identities and
composites are defined componentwise.

A zero-preserving functor maps bounded cochains through the
homological-complex functor and full-subcategory lift.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex

variable (C : Type uC) [Category.{vC} C]

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- Original cochain terms have finite integer support. -/
protected def bounded : ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)

/-- The bounded predicate states exactly the original term support. -/
theorem bounded_iff (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔ ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j) :=
  Iff.rfl

instance : (CochainComplex.bounded C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨a, b, hK⟩
    exact ⟨a, b, fun j hj => (hK j hj).of_iso (HomologicalComplex.Hom.isoApp e j).symm⟩

/-- The native full subcategory on the original finite-support cochains. -/
abbrev Bounded := (CochainComplex.bounded C).FullSubcategory

/-- The original zero cochain has literal support in `[0,0]`. -/
theorem bounded_zero [HasZeroObject C] :
    CochainComplex.bounded C (0 : CochainComplex C ℤ) := by
  refine ⟨0, 0, ?_⟩
  intro j _
  exact (HomologicalComplex.eval C (.up ℤ) j).map_isZero
    (isZero_zero (CochainComplex C ℤ))

instance [HasZeroObject C] : (CochainComplex.bounded C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, bounded_zero C⟩

namespace Bounded

/-- Reify the same original complex with its proved original support window. -/
@[simps! obj]
def of (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) : Bounded C :=
  ⟨K, ⟨a, b, hK⟩⟩

/-- The canonical inclusion retains the original cochain object and map. -/
abbrev ι : Bounded C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

/-- The native bounded inclusion is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- Evaluation at an original integer degree after the original inclusion. -/
@[simps! obj map]
def eval (j : ℤ) : Bounded C ⥤ C := ι C ⋙ HomologicalComplex.eval C (.up ℤ) j

/-- The original bounded morphism property is split mono in each actual component. -/
def degreewiseSplitMonomorphisms : MorphismProperty (Bounded C) :=
  fun _ _ f => ∀ j : ℤ, IsSplitMono (f.hom.f j)

/-- Membership tests the literal original cochain map components. -/
theorem degreewiseSplitMonomorphisms_iff {K L : Bounded C} (f : K ⟶ L) :
    degreewiseSplitMonomorphisms C f ↔ ∀ j : ℤ, IsSplitMono (f.hom.f j) := Iff.rfl

/-- The actual identity components are split mono. -/
theorem degreewiseSplitMonomorphisms_id (K : Bounded C) :
    degreewiseSplitMonomorphisms C (𝟙 K) := by
  intro j
  change IsSplitMono (𝟙 (K.obj.X j))
  infer_instance

/-- Composition uses the original component maps and their actual split witnesses. -/
theorem degreewiseSplitMonomorphisms_comp {K L M : Bounded C} (f : K ⟶ L) (g : L ⟶ M)
    (hf : degreewiseSplitMonomorphisms C f) (hg : degreewiseSplitMonomorphisms C g) :
    degreewiseSplitMonomorphisms C (f ≫ g) := by
  intro j
  change IsSplitMono (f.hom.f j ≫ g.hom.f j)
  let _ : IsSplitMono (f.hom.f j) := hf j
  let _ : IsSplitMono (g.hom.f j) := hg j
  infer_instance

instance : (degreewiseSplitMonomorphisms C).IsMultiplicative where
  id_mem := degreewiseSplitMonomorphisms_id C
  comp_mem := degreewiseSplitMonomorphisms_comp C

/-- The admissible monomorphisms of bounded cochains over an abelian category
test monomorphisms on the actual original components. -/
def degreewiseMonomorphisms : MorphismProperty (Bounded C) :=
  fun _ _ f => ∀ j : ℤ, Mono (f.hom.f j)

/-- The component readout retains the original cochain map. -/
theorem degreewiseMonomorphisms_iff {K L : Bounded C} (f : K ⟶ L) :
    degreewiseMonomorphisms C f ↔ ∀ j : ℤ, Mono (f.hom.f j) := Iff.rfl

instance : (degreewiseMonomorphisms C).IsMultiplicative where
  id_mem K := by
    intro j
    change Mono (𝟙 (K.obj.X j))
    infer_instance
  comp_mem f g hf hg := by
    intro j
    change Mono (f.hom.f j ≫ g.hom.f j)
    let _ : Mono (f.hom.f j) := hf j
    let _ : Mono (g.hom.f j) := hg j
    infer_instance

/-- Every actual split component is a monomorphism; the converse is not required. -/
theorem degreewiseMonomorphisms_of_degreewiseSplitMonomorphisms
    {K L : Bounded C} (f : K ⟶ L) (hf : degreewiseSplitMonomorphisms C f) :
    degreewiseMonomorphisms C f := by
  intro j
  let _ : IsSplitMono (f.hom.f j) := hf j
  infer_instance

end Bounded

end ZeroMorphisms

section Preadditive

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The original term biproduct charts give the exact union support window. -/
theorem biprod_isZero_outside (K L : CochainComplex C ℤ) (a b c d : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hL : ∀ j : ℤ, j < c ∨ d < j → IsZero (L.X j)) (j : ℤ)
    (hj : j < min a c ∨ max b d < j) : IsZero ((K ⊞ L).X j) := by
  have hKj : IsZero (K.X j) := by
    apply hK j
    rcases hj with hj | hj
    · exact Or.inl (lt_of_lt_of_le hj (min_le_left a c))
    · exact Or.inr (lt_of_le_of_lt (le_max_left b d) hj)
  have hLj : IsZero (L.X j) := by
    apply hL j
    rcases hj with hj | hj
    · exact Or.inl (lt_of_lt_of_le hj (min_le_right a c))
    · exact Or.inr (lt_of_le_of_lt (le_max_right b d) hj)
  exact ((biprod_isZero_iff (K.X j) (L.X j)).2 ⟨hKj, hLj⟩).of_iso
    (HomologicalComplex.biprodXIso K L j)

/-- The same original raw biproduct remains in the bounded category. -/
theorem bounded_biprod (K L : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (K ⊞ L) := by
  obtain ⟨a, b, hK⟩ := hK
  obtain ⟨c, d, hL⟩ := hL
  exact ⟨min a c, max b d, biprod_isZero_outside C K L a b c d hK hL⟩

namespace Bounded

/-- The bicone has the literal original ambient biproduct as its point
and the original ambient four legs as its bounded morphisms. -/
def biprodBicone (K L : Bounded C) : BinaryBicone K L where
  pt := ⟨K.obj ⊞ L.obj, bounded_biprod C K.obj L.obj K.property L.property⟩
  fst := ObjectProperty.homMk (biprod.fst : K.obj ⊞ L.obj ⟶ K.obj)
  snd := ObjectProperty.homMk (biprod.snd : K.obj ⊞ L.obj ⟶ L.obj)
  inl := ObjectProperty.homMk (biprod.inl : K.obj ⟶ K.obj ⊞ L.obj)
  inr := ObjectProperty.homMk (biprod.inr : L.obj ⟶ K.obj ⊞ L.obj)
  inl_fst := by apply ObjectProperty.hom_ext; simp
  inl_snd := by apply ObjectProperty.hom_ext; simp
  inr_fst := by apply ObjectProperty.hom_ext; simp
  inr_snd := by apply ObjectProperty.hom_ext; simp

instance : HasBinaryBiproducts (Bounded C) where
  has_binary_biproduct K L := hasBinaryBiproduct_of_total (biprodBicone C K L) (by
    dsimp only [biprodBicone]
    apply ObjectProperty.hom_ext
    change (biprod.fst : K.obj ⊞ L.obj ⟶ K.obj) ≫ biprod.inl +
      (biprod.snd : K.obj ⊞ L.obj ⟶ L.obj) ≫ biprod.inr = 𝟙 (K.obj ⊞ L.obj)
    exact IsBilimit.binary_total (BinaryBiproduct.isBilimit K.obj L.obj))

end Bounded

end Preadditive

instance [Preadditive C] : (Bounded.ι C).Additive :=
  Functor.fullSubcategoryInclusion_additive _

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The original functor carries original zero terms to zero terms in the same window. -/
theorem bounded_mapHomologicalComplex_obj (K : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, hK⟩ := hK
  exact ⟨a, b, fun j hj => F.map_isZero (hK j hj)⟩

/-- The original bounded functor is the native full-subcategory lift of
the original homological-complex functor. -/
@[implicit_reducible, simps! obj_obj map_hom]
def mapCochainComplexBounded : CochainComplex.Bounded C ⥤ CochainComplex.Bounded D :=
  ObjectProperty.lift _
    (CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (.up ℤ))
    (fun K => bounded_mapHomologicalComplex_obj F K.obj K.property)

/-- Every mapped bounded term is the literal original functor image. -/
theorem mapCochainComplexBounded_obj_X (K : CochainComplex.Bounded C) (j : ℤ) :
    ((F.mapCochainComplexBounded).obj K).obj.X j = F.obj (K.obj.X j) := rfl

/-- Every mapped component is the literal original functor map. -/
theorem mapCochainComplexBounded_map_f {K L : CochainComplex.Bounded C} (f : K ⟶ L) (j : ℤ) :
    ((F.mapCochainComplexBounded).map f).hom.f j = F.map (f.hom.f j) := rfl

/-- The original mapped functor carries actual degreewise split witnesses
to split witnesses of its literal original component maps. -/
theorem mapCochainComplexBounded_degreewiseSplitMonomorphisms
    {K L : CochainComplex.Bounded C} (f : K ⟶ L)
    (hf : CochainComplex.Bounded.degreewiseSplitMonomorphisms C f) :
    CochainComplex.Bounded.degreewiseSplitMonomorphisms D
      ((F.mapCochainComplexBounded).map f) := by
  intro j
  change IsSplitMono (F.map (f.hom.f j))
  let _ : IsSplitMono (f.hom.f j) := hf j
  infer_instance

end CategoryTheory.Functor

end
