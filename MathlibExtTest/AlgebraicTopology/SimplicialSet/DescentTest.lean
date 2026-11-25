/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Descent

/-!
# Tests for descent for inner fibrations

Consumer checks for the public declarations of
`MathlibExt/AlgebraicTopology/SimplicialSet/Descent.lean`: the
descent predicates of Stevenson Definition 4.1 and their identity
and composition closure, Stevenson Lemma 4.2 (surjective base
change), pre-fibrancy of descent targets and of pullbacks (Remark
3.4 as used in §4), and the reduction of the Remark 3.7
mapping-space criterion for vertex-surjective (in particular
vertex-bijective) maps to full faithfulness on naive mapping
spaces. Factorization through full subcomplexes is tested in
`FullSubcomplexTest`, and injectivity of the induced
mapping-space maps for full-subcomplex inclusions in
`JoinSliceTest`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.DescentTest

variable {S T X Y : SSet.{u}}

/-! ### Descent predicates (Stevenson Definition 4.1) -/

example (p : X ⟶ S) (f : S ⟶ T) : Prop := SSet.SatisfiesDescent p f

example (p : X ⟶ S) (f : S ⟶ T) : Prop :=
  SSet.SatisfiesInnerAnodyneDescent p f

/-- Every inner fibration satisfies descent along the identity. -/
example (p : X ⟶ S) [SSet.InnerFibration p] :
    SSet.SatisfiesDescent p (𝟙 S) :=
  SSet.satisfiesDescent_id p

/-- Every inner fibration satisfies inner anodyne descent along the
identity. -/
example (p : X ⟶ S) [SSet.InnerFibration p] :
    SSet.SatisfiesInnerAnodyneDescent p (𝟙 S) :=
  SSet.satisfiesInnerAnodyneDescent_id p

/-- Concretely: a full-subcomplex inclusion, which is an inner
fibration, satisfies descent along the identity. -/
example (V : Set (X _⦋0⦌)) :
    SSet.SatisfiesInnerAnodyneDescent (SSet.Subcomplex.full V).ι (𝟙 X) :=
  SSet.satisfiesInnerAnodyneDescent_id _

/-- Inner anodyne descent implies descent. -/
example (p : X ⟶ S) (f : S ⟶ T)
    (h : SSet.SatisfiesInnerAnodyneDescent p f) :
    SSet.SatisfiesDescent p f :=
  h.satisfiesDescent

/-- A map satisfying descent is an inner fibration. -/
example (p : X ⟶ S) (f : S ⟶ T) (h : SSet.SatisfiesDescent p f) :
    SSet.InnerFibration p :=
  h.innerFibration

/-- A pullback square over an inner fibration exhibits descent and
makes the pulled-back map an inner fibration. -/
example (p : X ⟶ S) (f : S ⟶ T) (q : Y ⟶ T) (g : X ⟶ Y)
    [SSet.InnerFibration q] (sq : IsPullback g p q f) :
    SSet.SatisfiesDescent p f ∧ SSet.InnerFibration p :=
  ⟨SSet.SatisfiesDescent.of_isPullback inferInstance sq,
    SSet.innerFibration_of_isPullback sq⟩

/-- Descent composes along identity base maps. -/
example (p : X ⟶ S) [SSet.InnerFibration p] :
    SSet.SatisfiesDescent p (𝟙 S ≫ 𝟙 S) := by
  refine (SSet.satisfiesDescent_id p).comp ?_
  intro Z q hq hsq
  obtain ⟨g, hg⟩ := hsq
  have := hq
  exact SSet.satisfiesDescent_id q

/-! ### Surjective base change (Stevenson Lemma 4.2) -/

/-- Lemma 4.2, abstract form. -/
example (p : X ⟶ S) (f : T ⟶ S) (q : Y ⟶ T) (u : Y ⟶ X)
    (sq : IsPullback u q p f)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [SSet.InnerFibration q] : SSet.InnerFibration p :=
  SSet.innerFibration_of_surjective_isPullback sq hf

/-- Lemma 4.2 recovers `p` itself along the identity surjection and
the identity pullback square. -/
example (p : X ⟶ S) [SSet.InnerFibration p] : SSet.InnerFibration p :=
  SSet.innerFibration_of_surjective_isPullback
    (p := p) (f := 𝟙 S) (q := p) (u := 𝟙 X) IsPullback.of_id_fst
    (fun n y => ⟨y, by simp⟩)

/-- Lemma 4.2 for the chosen pullback, abstract form. -/
example (p : X ⟶ S) (f : T ⟶ S)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [SSet.InnerFibration (pullback.fst f p)] : SSet.InnerFibration p :=
  SSet.innerFibration_of_surjective_pullback_fst p f hf

/-- The horn-lifting form of Lemma 4.2. -/
example (p : X ⟶ S) (f : T ⟶ S) (q : Y ⟶ T) (u : Y ⟶ X)
    (sq : IsPullback u q p f)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [SSet.InnerFibration q] :
    HasLiftingProperty Λ[2, (1 : Fin 3)].ι p :=
  SSet.hasLiftingProperty_horn_of_surjective_isPullback sq hf
    (by decide) (by decide)

/-! ### Pre-fibrant descent targets (Remark 3.4) -/

/-- Standard simplices are pre-fibrant (they are quasicategories). -/
example : SSet.IsPreFibrant (Δ[2] : SSet.{u}) := inferInstance

/-- Descent over a pre-fibrant base has a pre-fibrant target. -/
example (p : X ⟶ S) (f : S ⟶ Δ[2])
    (h : SSet.SatisfiesDescent p f) :
    ∃ (Y : SSet.{u}) (q : Y ⟶ Δ[2]) (g : X ⟶ Y),
      SSet.InnerFibration q ∧ IsPullback g p q f ∧ SSet.IsPreFibrant Y :=
  h.exists_isPreFibrant_target

/-- Inner anodyne descent over a pre-fibrant base has a pre-fibrant
target reached by an inner anodyne map. -/
example (p : X ⟶ S) (f : S ⟶ Δ[2])
    (h : SSet.SatisfiesInnerAnodyneDescent p f) :
    ∃ (Y : SSet.{u}) (q : Y ⟶ Δ[2]) (g : X ⟶ Y),
      SSet.InnerFibration q ∧ IsPullback g p q f ∧
        SSet.innerAnodyneExtensions g ∧ SSet.IsPreFibrant Y :=
  h.exists_isPreFibrant_target

/-- An inner fibration pulled back to a standard simplex has
pre-fibrant total object. -/
example (p : X ⟶ S) [SSet.InnerFibration p] (f : Δ[1] ⟶ S) :
    SSet.IsPreFibrant (pullback p f) :=
  inferInstance

/-! ### Mapping-space criteria (Stevenson Remark 3.7) -/

/-- A map surjective on vertices is essentially surjective. -/
example (f : X ⟶ Y) (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    SSet.dwyerKanEssentiallySurjective f :=
  SSet.dwyerKanEssentiallySurjective_of_surjective_app_zero hf

/-- A map bijective on vertices is essentially surjective. -/
example (f : X ⟶ Y) (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    SSet.dwyerKanEssentiallySurjective f :=
  SSet.dwyerKanEssentiallySurjective_of_bijective_app_zero hf

/-- The identity is bijective on vertices, hence essentially
surjective. -/
example : SSet.dwyerKanEssentiallySurjective (𝟙 X) := by
  apply SSet.dwyerKanEssentiallySurjective_of_bijective_app_zero
  exact Function.bijective_id

/-- For a vertex-surjective map between pre-fibrant simplicial
sets, being a Dwyer–Kan equivalence is exactly full faithfulness
on mapping spaces (right-handed landed predicate). -/
example (f : X ⟶ Y) [SSet.IsPreFibrant X] [SSet.IsPreFibrant Y]
    (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    SSet.isDwyerKanEquivalence f ↔ SSet.dwyerKanFullyFaithful f :=
  SSet.isDwyerKanEquivalence_iff_of_surjective_app_zero hf

/-- For a vertex-bijective map between pre-fibrant simplicial sets,
being a Dwyer–Kan equivalence is exactly full faithfulness on
mapping spaces (right-handed landed predicate). -/
example (f : X ⟶ Y) [SSet.IsPreFibrant X] [SSet.IsPreFibrant Y]
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    SSet.isDwyerKanEquivalence f ↔ SSet.dwyerKanFullyFaithful f :=
  SSet.isDwyerKanEquivalence_iff_of_bijective_app_zero hf

/-- The left-handed form, matching Remark 3.7's `Homᴸ`: for a
vertex-surjective map between pre-fibrant simplicial sets,
essential surjectivity plus full faithfulness on left mapping
spaces is exactly full faithfulness on left mapping spaces. -/
example (f : X ⟶ Y) [SSet.IsPreFibrant X] [SSet.IsPreFibrant Y]
    (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    (SSet.dwyerKanEssentiallySurjective f ∧
      SSet.dwyerKanFullyFaithfulLeft f) ↔
      SSet.dwyerKanFullyFaithfulLeft f :=
  SSet.dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero hf

/-- The left-handed form, matching Remark 3.7's `Homᴸ`: for a
vertex-bijective map between pre-fibrant simplicial sets, essential
surjectivity plus full faithfulness on left mapping spaces is
exactly full faithfulness on left mapping spaces. -/
example (f : X ⟶ Y) [SSet.IsPreFibrant X] [SSet.IsPreFibrant Y]
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    (SSet.dwyerKanEssentiallySurjective f ∧
      SSet.dwyerKanFullyFaithfulLeft f) ↔
      SSet.dwyerKanFullyFaithfulLeft f :=
  SSet.dwyerKanFullyFaithfulLeft_iff_of_bijective_app_zero hf

/-- Full faithfulness on left mapping spaces, at element vertices:
the induced maps are realization weak equivalences, matching the
landed right-handed predicate. -/
example (f : X ⟶ Y) (h : SSet.dwyerKanFullyFaithfulLeft f)
    (x y : X _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.mappingSpaceLeft.map X (SSet.const x) (SSet.const y) f) :=
  h.vertex x y

/-- The identity is fully faithful on left mapping spaces,
unconditionally: no Kan hypothesis on the mapping spaces is
needed. -/
example : SSet.dwyerKanFullyFaithfulLeft (𝟙 X) :=
  SSet.dwyerKanFullyFaithfulLeft_id

/-- Pointwise `KanComplex.W` weak equivalences give full
faithfulness on left mapping spaces, with no separate Kan
hypotheses (each `KanComplex.W` value carries them). -/
example (f : X ⟶ Y)
    (hW : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex.W (SSet.mappingSpaceLeft.map X a b f)) :
    SSet.dwyerKanFullyFaithfulLeft f :=
  SSet.dwyerKanFullyFaithfulLeft.of_kanComplexW hW

/-- Under Kan hypotheses on the left mapping spaces, full
faithfulness on left mapping spaces gives pointwise
`KanComplex.W` weak equivalences. -/
example (f : X ⟶ Y) (h : SSet.dwyerKanFullyFaithfulLeft f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceLeft X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceLeft Y (a ≫ f) (b ≫ f)))
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    SSet.KanComplex.W (SSet.mappingSpaceLeft.map X a b f) :=
  h.kanComplexW hKanX hKanY a b

/-- Full faithfulness on left mapping spaces composes. -/
example (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : SSet.dwyerKanFullyFaithfulLeft f)
    (hg : SSet.dwyerKanFullyFaithfulLeft g) :
    SSet.dwyerKanFullyFaithfulLeft (f ≫ g) :=
  hf.comp hg

/- No axioms beyond Lean's standard ones are used by the main
results. -/
#print axioms SSet.innerFibration_of_surjective_isPullback
#print axioms SSet.hasLiftingProperty_horn_of_surjective_isPullback
#print axioms SSet.dwyerKanEssentiallySurjective_of_surjective_app_zero
#print axioms SSet.dwyerKanEssentiallySurjective_of_bijective_app_zero

end MathlibExtTest.AlgebraicTopology.SimplicialSet.DescentTest

end
