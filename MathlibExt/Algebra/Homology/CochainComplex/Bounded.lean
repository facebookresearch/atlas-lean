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
# Bounded integer cochain complexes

Let C be a category with zero morphisms. A cochain complex is bounded when its terms are zero
outside some finite integer interval [a,b]. These complexes form a full subcategory, with the
ambient cochain maps as morphisms. Evaluation and inclusion retain the terms and maps.

Degreewise split monomorphisms and degreewise monomorphisms are component conditions. With a
zero object and binary biproducts, the zero complex and binary biproducts are bounded; support
intervals combine by [min(a,c),max(b,d)]. A functor preserving zero morphisms maps bounded
complexes to bounded complexes in the same support window and preserves the degreewise split
property.
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

/-- Let C be a category with zero morphisms. An integer cochain complex K is bounded if there
exist a,b ∈ ℤ such that K^j is a zero object whenever j<a or b<j. This is a condition on the
cochain terms, with both endpoint degrees included in the support window. -/
protected def bounded : ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)

/-- For a category C with zero morphisms and an integer cochain complex K, CochainComplex.bounded
C K is equivalent to existence of integers a,b such that IsZero(K^j) for every j<a or j>b. No
homology-support condition is substituted for this termwise condition. -/
theorem bounded_iff (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔ ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j) :=
  Iff.rfl

instance : (CochainComplex.bounded C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨a, b, hK⟩
    exact ⟨a, b, fun j hj => (hK j hj).of_iso (HomologicalComplex.Hom.isoApp e j).symm⟩

/-- Let C be a category with zero morphisms. Define Bounded C as the full subcategory of
CochainComplex C ℤ consisting of complexes whose terms vanish outside some finite integer
interval. Morphisms are the ambient cochain maps; a support witness imposes no additional
morphism condition. -/
abbrev Bounded := (CochainComplex.bounded C).FullSubcategory

/-- If C has zero morphisms and a zero object, its zero integer cochain complex is bounded. Every
term is zero, so the interval [0,0] is a support witness. -/
theorem bounded_zero [HasZeroObject C] :
    CochainComplex.bounded C (0 : CochainComplex C ℤ) := by
  refine ⟨0, 0, ?_⟩
  intro j _
  exact (HomologicalComplex.eval C (.up ℤ) j).map_isZero
    (isZero_zero (CochainComplex C ℤ))

instance [HasZeroObject C] : (CochainComplex.bounded C).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, bounded_zero C⟩

namespace Bounded

/-- Let C have zero morphisms, K be an integer cochain complex, and a,b ∈ ℤ. If K^j is zero for
every j<a or j>b, then K with this support witness defines an object of Bounded C. The
underlying cochain complex remains K. -/
@[simps! obj]
def of (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) : Bounded C :=
  ⟨K, ⟨a, b, hK⟩⟩

/-- For a category C with zero morphisms, the canonical functor Bounded C → CochainComplex C ℤ
sends a bounded object to its underlying cochain complex and a morphism to its underlying
cochain map. -/
abbrev ι : Bounded C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

/-- Let C be a category with zero morphisms. The inclusion Bounded C → CochainComplex C ℤ is fully
faithful, because Bounded C is a full subcategory. In particular, its maps between any two
bounded complexes are exactly the ambient cochain maps. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- For C with zero morphisms and j ∈ ℤ, define evaluation Bounded C → C by K ↦ K^j. On a bounded
cochain morphism f it returns the component f^j of the underlying ambient cochain map. -/
@[simps! obj map]
def eval (j : ℤ) : Bounded C ⥤ C := ι C ⋙ HomologicalComplex.eval C (.up ℤ) j

/-- Let C have zero morphisms. A morphism f : K → L in Bounded C is degreewise split monic when
each component f^j : K^j → L^j is split monic for every j ∈ ℤ. The component retractions need
not assemble into a cochain map; the property is defined separately in each degree. -/
def degreewiseSplitMonomorphisms : MorphismProperty (Bounded C) :=
  fun _ _ f => ∀ j : ℤ, IsSplitMono (f.hom.f j)

/-- For a category C with zero morphisms and f : K → L in Bounded C, membership in
degreewiseSplitMonomorphisms is equivalent to IsSplitMono(f.hom.f j) for every integer j. Thus
the condition is tested on the underlying cochain-map components. -/
theorem degreewiseSplitMonomorphisms_iff {K L : Bounded C} (f : K ⟶ L) :
    degreewiseSplitMonomorphisms C f ↔ ∀ j : ℤ, IsSplitMono (f.hom.f j) := Iff.rfl

/-- Let C have zero morphisms and K be a bounded integer cochain complex. The identity morphism of
K is degreewise split monic: in each integer degree its component and its retraction are the
identity. -/
theorem degreewiseSplitMonomorphisms_id (K : Bounded C) :
    degreewiseSplitMonomorphisms C (𝟙 K) := by
  intro j
  change IsSplitMono (𝟙 (K.obj.X j))
  infer_instance

/-- For a category C with zero morphisms and bounded cochain maps f : K → L, g : L → M, if every
f^j and g^j is split monic then every component of f≫g is split monic. Component retractions
compose in the reverse order, giving the degreewise split property. -/
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

/-- Let C be a category with zero morphisms. Define degreewiseMonomorphisms on Bounded C by
requiring Mono(f^j) for every integer j. It is a condition on the components of the underlying
cochain map and does not assume an abelian structure on C. -/
def degreewiseMonomorphisms : MorphismProperty (Bounded C) :=
  fun _ _ f => ∀ j : ℤ, Mono (f.hom.f j)

/-- For C with zero morphisms and f : K → L in Bounded C, degreewiseMonomorphisms C f holds if and
only if Mono(f.hom.f j) for every j ∈ ℤ. -/
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

/-- Let C have zero morphisms and f : K → L be a bounded cochain map. If each component f^j is
split monic, then each f^j is monic, so f belongs to degreewiseMonomorphisms. -/
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

/-- Let C be preadditive with binary biproducts. Suppose integer cochain complexes K,L vanish
outside [a,b] and [c,d], respectively. Then (K⊞L)^j is zero whenever j<min(a,c) or max(b,d)<j.
In such a degree both component terms are zero, and the term of the cochain biproduct is their
biproduct. -/
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

/-- In a preadditive category C with binary biproducts, if integer cochain complexes K and L are
bounded, their ambient cochain biproduct K⊞L is bounded. Support windows [a,b] and [c,d] give
the window [min(a,c),max(b,d)]. -/
theorem bounded_biprod (K L : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (K ⊞ L) := by
  obtain ⟨a, b, hK⟩ := hK
  obtain ⟨c, d, hL⟩ := hL
  exact ⟨min a c, max b d, biprod_isZero_outside C K L a b c d hK hL⟩

namespace Bounded

/-- Let C be preadditive with binary biproducts and K,L objects of Bounded C. Define the binary
bicone with point the bounded object underlying K.obj⊞L.obj and four legs the ambient
biproduct projections and inclusions. Boundedness of the point follows from the union of
support windows, and the bicone equations are inherited from the ambient cochain biproduct. -/
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

/-- Let C,D be categories with zero morphisms and F : C → D preserve zero morphisms. If K is a
bounded integer cochain complex, its degreewise image under F is bounded. A support interval
for K is also a support interval for F(K), because F carries zero terms to zero objects. -/
theorem bounded_mapHomologicalComplex_obj (K : CochainComplex C ℤ)
    (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, hK⟩ := hK
  exact ⟨a, b, fun j hj => F.map_isZero (hK j hj)⟩

/-- For categories C,D with zero morphisms and F : C → D preserving them, the degreewise cochain
functor restricts to Bounded C → Bounded D. It sends K^j to F(K^j), its differentials to
F(d_K), and its morphism components to their F-images. The category object and morphism
universes may be independent. -/
@[implicit_reducible, simps! obj_obj map_hom]
def mapCochainComplexBounded : CochainComplex.Bounded C ⥤ CochainComplex.Bounded D :=
  ObjectProperty.lift _
    (CochainComplex.Bounded.ι C ⋙ F.mapHomologicalComplex (.up ℤ))
    (fun K => bounded_mapHomologicalComplex_obj F K.obj K.property)

/-- Let F : C → D preserve zero morphisms between categories with zero morphisms, K ∈ Bounded C,
and j ∈ ℤ. The jth term of the mapped bounded complex is exactly F(K^j). -/
theorem mapCochainComplexBounded_obj_X (K : CochainComplex.Bounded C) (j : ℤ) :
    ((F.mapCochainComplexBounded).obj K).obj.X j = F.obj (K.obj.X j) := rfl

/-- For a zero-preserving functor F : C → D, a bounded cochain map f : K → L, and j ∈ ℤ, the jth
component of the induced bounded map equals F(f^j). -/
theorem mapCochainComplexBounded_map_f {K L : CochainComplex.Bounded C} (f : K ⟶ L) (j : ℤ) :
    ((F.mapCochainComplexBounded).map f).hom.f j = F.map (f.hom.f j) := rfl

/-- Let C,D have zero morphisms and F : C → D preserve zero morphisms. If f : K → L in Bounded C
is split monic in every integer degree, then its image in Bounded D is also split monic in
every degree. Applying F to each component retraction preserves the splitting equation. -/
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
