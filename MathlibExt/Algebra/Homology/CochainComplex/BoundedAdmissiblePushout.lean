/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Admissible pushouts of bounded cochain complexes

Let E be a preadditive exact category with a zero object and binary biproducts.
A bounded complex is an integer-indexed cochain complex whose terms vanish
outside some finite interval. A map is degreewise admissible when every
component is an admissible monomorphism in E.

For a span B ← A → C whose map A → B is degreewise admissible, its pushout
exists both among bounded complexes and among all integer-indexed cochain
complexes, and evaluation in any degree gives the corresponding pushout in E.
If B and C are supported in [aB,bB] and [aC,bC], the pushout is supported in
[min(aB,aC),max(bB,bC)]. The induced map C → B ⨿ₐ C is degreewise admissible.
An additive exact functor between such exact categories preserves these maps
and pushout squares. The object and morphism universes of the two categories
are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uD vD

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- In a preadditive exact category E with a zero object and binary biproducts,
the morphism property on bounded integer-indexed cochain complexes that holds
for i:A → B exactly when every component iⱼ:Aʲ → Bʲ is an admissible
monomorphism in E. -/
def degreewiseAdmissibleMonomorphisms : MorphismProperty (Bounded E) :=
  fun _ _ i => ∀ j : ℤ, IsAdmissibleMono (i.hom.f j)

/-- For bounded integer-indexed cochain complexes A and B in a preadditive
exact category E with a zero object and binary biproducts, a map i:A → B belongs
to the degreewise admissible morphism property if and only if iⱼ:Aʲ → Bʲ is
an admissible monomorphism for every integer j. -/
theorem degreewiseAdmissibleMonomorphisms_iff {A B : Bounded E} (i : A ⟶ B) :
    degreewiseAdmissibleMonomorphisms E i ↔ ∀ j : ℤ, IsAdmissibleMono (i.hom.f j) := Iff.rfl

instance degreewiseAdmissibleMonomorphisms_isMultiplicative :
    (degreewiseAdmissibleMonomorphisms E).IsMultiplicative where
  id_mem A := by
    intro j
    change IsAdmissibleMono (𝟙 (A.obj.X j))
    exact IsAdmissibleMono.id _
  comp_mem i f hi hf := by
    intro j
    change IsAdmissibleMono (i.hom.f j ≫ f.hom.f j)
    exact admissibleMono_comp.comp_mem _ _ (hi j) (hf j)

instance degreewiseAdmissibleMonomorphisms_respectsIso :
    (degreewiseAdmissibleMonomorphisms E).RespectsIso := by
  apply MorphismProperty.respectsIso_of_isStableUnderComposition
  intro A B f hf
  let _ : IsIso f := hf
  intro j
  change IsAdmissibleMono ((eval E j).map f)
  exact IsAdmissibleMono.of_isIso _

private theorem hasColimit_span_eval {A B C : Bounded E} (i : A ⟶ B) (f : A ⟶ C)
    (hi : degreewiseAdmissibleMonomorphisms E i) (j : ℤ) :
    HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) := by
  obtain ⟨P, inC, inB, hP, _⟩ := ExactCategory.admissibleMono_pushout
    (A.obj.X j) (B.obj.X j) (i.hom.f j) (hi j) (C.obj.X j) (f.hom.f j)
  let _ : HasPushout (i.hom.f j) (f.hom.f j) := hP.flip.hasPushout
  let e : span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j ≅
      span (i.hom.f j) (f.hom.f j) :=
    diagramIsoSpan (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j)
  exact hasColimit_of_iso e

/-- Let E be a preadditive exact category with a zero object and binary
biproducts. For bounded cochain complexes A, B, C and a span B ← A → C with
maps i and f, if every iⱼ is an admissible monomorphism, then the pushout of
the underlying maps exists in the category of all integer-indexed cochain
complexes in E. -/
theorem hasPushout_hom_of_degreewiseAdmissibleMonomorphisms
    {A B C : Bounded E} (i : A ⟶ B) (f : A ⟶ C)
    (hi : degreewiseAdmissibleMonomorphisms E i) : HasPushout i.hom f.hom := by
  letI : ∀ j : ℤ, HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) :=
    hasColimit_span_eval E i f hi
  change HasColimit (span i.hom f.hom)
  infer_instance

/-- Let E be a preadditive exact category with a zero object and binary
biproducts, and let i:A → B and f:A → C be maps of bounded cochain complexes
with i degreewise admissible. Suppose Bʲ is zero for j<aB or bB<j, and Cʲ
is zero for j<aC or bC<j. Then the underlying cochain pushout B ⨿ₐ C has
zero j-th term whenever j<min(aB,aC) or max(bB,bC)<j. -/
theorem pushout_unionSupport {A B C : Bounded E} (i : A ⟶ B) (f : A ⟶ C)
    (hi : degreewiseAdmissibleMonomorphisms E i)
    (aB bB aC bC : ℤ)
    (hB : ∀ j : ℤ, j < aB ∨ bB < j → IsZero (B.obj.X j))
    (hC : ∀ j : ℤ, j < aC ∨ bC < j → IsZero (C.obj.X j)) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
    ∀ j : ℤ, j < min aB aC ∨ max bB bC < j → IsZero ((pushout i.hom f.hom).X j) := by
  letI : ∀ j : ℤ, HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) :=
    hasColimit_span_eval E i f hi
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
  intro j hj
  have hBj : IsZero (B.obj.X j) := by
    apply hB j
    rcases hj with hj | hj
    · exact Or.inl (lt_of_lt_of_le hj (min_le_left aB aC))
    · exact Or.inr (lt_of_le_of_lt (le_max_left bB bC) hj)
  have hCj : IsZero (C.obj.X j) := by
    apply hC j
    rcases hj with hj | hj
    · exact Or.inl (lt_of_lt_of_le hj (min_le_right aB aC))
    · exact Or.inr (lt_of_le_of_lt (le_max_right bB bC) hj)
  have hPj := (IsPushout.of_hasPushout i.hom f.hom).map
    (HomologicalComplex.eval E (.up ℤ) j)
  apply (IsZero.iff_id_eq_zero _).2
  apply hPj.hom_ext
  · exact hBj.eq_of_src _ _
  · exact hCj.eq_of_src _ _

/-- Let E be a preadditive exact category with a zero object and binary
biproducts. A span i:A → B, f:A → C of bounded integer-indexed cochain
complexes with i degreewise admissible has a bounded pushout P with maps
inB:B → P and inC:C → P. The square is a pushout in the bounded category,
in the category of all cochain complexes, and in E in every degree.
The map inC is degreewise admissible, and P has the underlying complex
B ⨿ₐ C. -/
theorem exists_boundedAdmissiblePushout {A B C : Bounded E} (i : A ⟶ B) (f : A ⟶ C)
    (hi : degreewiseAdmissibleMonomorphisms E i) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
    ∃ (P : Bounded E) (inB : B ⟶ P) (inC : C ⟶ P),
      IsPushout i f inB inC ∧ IsPushout i.hom f.hom inB.hom inC.hom ∧
      (∀ j : ℤ, IsPushout (i.hom.f j) (f.hom.f j) (inB.hom.f j) (inC.hom.f j)) ∧
      degreewiseAdmissibleMonomorphisms E inC ∧ P.obj = pushout i.hom f.hom := by
  letI : ∀ j : ℤ, HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) :=
    hasColimit_span_eval E i f hi
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
  obtain ⟨aB, bB, hB⟩ := B.property
  obtain ⟨aC, bC, hC⟩ := C.property
  let T : CochainComplex E ℤ := pushout i.hom f.hom
  have hRaw := IsPushout.of_hasPushout i.hom f.hom
  let P : Bounded E := of E T (min aB aC) (max bB bC)
    (pushout_unionSupport E i f hi aB bB aC bC hB hC)
  let inB : B ⟶ P := ObjectProperty.homMk (pushout.inl i.hom f.hom)
  let inC : C ⟶ P := ObjectProperty.homMk (pushout.inr i.hom f.hom)
  have hBounded : IsPushout i f inB inC := IsPushout.of_map_of_faithful (ι E) hRaw
  have hTerms : ∀ j : ℤ, IsPushout (i.hom.f j) (f.hom.f j) (inB.hom.f j) (inC.hom.f j) :=
    fun j => hRaw.map (HomologicalComplex.eval E (.up ℤ) j)
  have hAdmissible : degreewiseAdmissibleMonomorphisms E inC := by
    intro j
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (P := admissibleMonosOf E IsAdmissibleExact) (hTerms j).flip (hi j)
  exact ⟨P, inB, inC, hBounded, hRaw, hTerms, hAdmissible, rfl⟩

/-- Let E be a preadditive exact category with a zero object and binary
biproducts. For a pushout square of bounded cochain complexes with maps
i:A → B, f:A → C, inB:B → P and inC:C → P, if i is degreewise admissible,
then the square of underlying integer-indexed cochain complexes is also a
pushout. -/
theorem admissiblePushout_raw {A B C P : Bounded E}
    {i : A ⟶ B} {f : A ⟶ C} {inB : B ⟶ P} {inC : C ⟶ P}
    (hi : degreewiseAdmissibleMonomorphisms E i) (hP : IsPushout i f inB inC) :
    IsPushout i.hom f.hom inB.hom inC.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
  obtain ⟨P₀, inB₀, inC₀, hP₀, hRaw₀, _, _, _⟩ := exists_boundedAdmissiblePushout E i f hi
  let _ : PreservesColimit (span i f) (ι E) :=
    (hP₀.preservesColimit_span_iff (F := ι E)).2 hRaw₀
  exact hP.map (ι E)

/-- Let E be a preadditive exact category with a zero object and binary
biproducts. Given a pushout square of bounded cochain complexes along a
degreewise admissible map i:A → B, evaluation at each integer j yields
the pushout square with maps iⱼ, fⱼ, inBⱼ and inCⱼ in E. -/
theorem admissiblePushout_term {A B C P : Bounded E}
    {i : A ⟶ B} {f : A ⟶ C} {inB : B ⟶ P} {inC : C ⟶ P}
    (hi : degreewiseAdmissibleMonomorphisms E i) (hP : IsPushout i f inB inC) (j : ℤ) :
    IsPushout (i.hom.f j) (f.hom.f j) (inB.hom.f j) (inC.hom.f j) := by
  letI : ∀ j : ℤ, HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) :=
    hasColimit_span_eval E i f hi
  exact (admissiblePushout_raw E hi hP).map (HomologicalComplex.eval E (.up ℤ) j)

end CochainComplex.Bounded

namespace CategoryTheory.Functor

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : E ⥤ D) [F.Additive] [F.IsExact]

/-- Let E and D be preadditive exact categories with zero objects and binary
biproducts, and let F:E → D be an additive exact functor. If i:A → B is a
map of bounded integer-indexed cochain complexes whose components are
admissible monomorphisms, then the components F(iⱼ) of the induced bounded
cochain map are also admissible monomorphisms. -/
theorem mapCochainComplexBounded_degreewiseAdmissibleMonomorphisms
    {A B : CochainComplex.Bounded E} (i : A ⟶ B)
    (hi : CochainComplex.Bounded.degreewiseAdmissibleMonomorphisms E i) :
    CochainComplex.Bounded.degreewiseAdmissibleMonomorphisms D
      (F.mapCochainComplexBounded.map i) := by
  intro j
  obtain ⟨Q, p, w, hS⟩ := hi j
  have wF : F.map (i.hom.f j) ≫ F.map p = 0 := by
    rw [← F.map_comp, w, F.map_zero]
  refine ⟨F.obj Q, F.map p, wF, ?_⟩
  exact F.map_admissibleExact (ShortComplex.mk (i.hom.f j) p w) hS

/-- Let F:E → D be an additive exact functor between preadditive exact
categories with zero objects and binary biproducts. If a square of bounded
cochain complexes is a pushout along a degreewise admissible map, then
applying F to every term and map gives a pushout square in the category of
bounded cochain complexes in D. -/
theorem mapCochainComplexBounded_isPushout_of_degreewiseAdmissibleMono
    {A B C P : CochainComplex.Bounded E}
    {i : A ⟶ B} {f : A ⟶ C} {inB : B ⟶ P} {inC : C ⟶ P}
    (hi : CochainComplex.Bounded.degreewiseAdmissibleMonomorphisms E i)
    (hP : IsPushout i f inB inC) :
    IsPushout (F.mapCochainComplexBounded.map i) (F.mapCochainComplexBounded.map f)
      (F.mapCochainComplexBounded.map inB) (F.mapCochainComplexBounded.map inC) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hRaw := CochainComplex.Bounded.admissiblePushout_raw E hi hP
  have w : G.map i.hom ≫ G.map inB.hom = G.map f.hom ≫ G.map inC.hom := by
    rw [← G.map_comp, hRaw.w, G.map_comp]
  let s : PushoutCocone (G.map i.hom) (G.map f.hom) :=
    PushoutCocone.mk (G.map inB.hom) (G.map inC.hom) w
  have hTerms : ∀ j : ℤ, IsPushout (F.map (i.hom.f j)) (F.map (f.hom.f j))
      (F.map (inB.hom.f j)) (F.map (inC.hom.f j)) := by
    intro j
    exact (F.map_isPushout_of_isAdmissibleMono
      (CochainComplex.Bounded.admissiblePushout_term E hi hP j).flip (hi j)).flip
  have hs : IsColimit s := HomologicalComplex.isColimitOfEval _ s (fun j =>
    (PushoutCocone.isColimitMapCoconeEquiv s (HomologicalComplex.eval D (.up ℤ) j)).symm
      (hTerms j).isColimit)
  have hTarget : IsPushout (G.map i.hom) (G.map f.hom)
      (G.map inB.hom) (G.map inC.hom) := IsPushout.of_isColimit hs
  exact IsPushout.of_map_of_faithful (CochainComplex.Bounded.ι D) hTarget

end CategoryTheory.Functor

end
