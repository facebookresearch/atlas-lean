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

A span whose distinguished map is degreewise admissible has a pushout
computed in each degree of the exact category. The underlying cochain
pushout is supported in the union of the target support windows.

The induced leg is degreewise admissible, and exact functors preserve
these bounded pushouts.
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

/-- Admissibility of a bounded cochain map is tested degreewise. -/
def degreewiseAdmissibleMonomorphisms : MorphismProperty (Bounded E) :=
  fun _ _ i => ∀ j : ℤ, IsAdmissibleMono (i.hom.f j)

/-- Criterion for degreewise admissibility of the underlying cochain map. -/
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

/-- An admissible bounded span has a pushout in the underlying cochain category. -/
theorem hasPushout_hom_of_degreewiseAdmissibleMonomorphisms
    {A B C : Bounded E} (i : A ⟶ B) (f : A ⟶ C)
    (hi : degreewiseAdmissibleMonomorphisms E i) : HasPushout i.hom f.hom := by
  letI : ∀ j : ℤ, HasColimit (span i.hom f.hom ⋙ HomologicalComplex.eval E (.up ℤ) j) :=
    hasColimit_span_eval E i f hi
  change HasColimit (span i.hom f.hom)
  infer_instance

/-- The pushout is supported in the union of the target support windows. -/
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

/-- Pushout of an admissible span in the category of bounded cochain complexes. -/
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

/-- The bounded pushout realizes the underlying cochain pushout. -/
theorem admissiblePushout_raw {A B C P : Bounded E}
    {i : A ⟶ B} {f : A ⟶ C} {inB : B ⟶ P} {inC : C ⟶ P}
    (hi : degreewiseAdmissibleMonomorphisms E i) (hP : IsPushout i f inB inC) :
    IsPushout i.hom f.hom inB.hom inC.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i f hi
  obtain ⟨P₀, inB₀, inC₀, hP₀, hRaw₀, _, _, _⟩ := exists_boundedAdmissiblePushout E i f hi
  let _ : PreservesColimit (span i f) (ι E) :=
    (hP₀.preservesColimit_span_iff (F := ι E)).2 hRaw₀
  exact hP.map (ι E)

/-- Evaluation in each degree realizes a pushout of components. -/
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

/-- Exact functors preserve degreewise admissibility. -/
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

/-- Exact functors preserve admissible pushouts of bounded cochain complexes. -/
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
