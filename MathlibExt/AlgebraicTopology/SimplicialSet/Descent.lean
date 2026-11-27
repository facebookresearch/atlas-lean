/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PreFibrant
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Descent of inner fibrations and mapping-space criteria

An inner fibration over `S` satisfies descent along `S → T` when it is the base
change of an inner fibration over `T`. Inner-anodyne descent additionally requires
the induced map of total objects to be inner anodyne. Pullback pasting gives composition
under the stated witness hypotheses, and degreewise surjective base change reflects
inner fibrations.

Descent over a prefibrant base has a prefibrant total target. Separately, surjectivity
on vertices gives essential surjectivity on homotopy categories. Full faithfulness on
left mapping spaces means realization weak equivalence on every map `Homᴸ_X(a,b)`;
with Kan mapping spaces this is the corresponding Kan weak-equivalence condition.
The right-mapping-space Dwyer–Kan criterion and the left-mapping-space predicate
are kept explicit in their respective statements.

See Stevenson, Notes on the Joyal model structure, arXiv:1810.05233v1, §§2.4, 3, 4,
and Lurie, Higher Topos Theory, §§1.2.2, 1.2.9, and 2.2.5.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T U X Y Z : SSet.{u}}

/-!
## Descent diagrams and pullback pasting

A descent diagram exhibits `X → S` as the pullback of an inner fibration `Y → T`
along `S → T`. Requiring `X → Y` to be inner anodyne gives inner-anodyne descent.
Such diagrams compose when each possible intermediate witness has the required
further descent. See Stevenson, Definition 4.1.
-/

/--
The condition that `p : X → S` is the base change along `f : S → T` of some
inner fibration `q : Y → T`, through a pullback square with top map `X → Y`.
-/
def SatisfiesDescent {X S T : SSet.{u}} (p : X ⟶ S) (f : S ⟶ T) : Prop :=
  ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
    InnerFibration q ∧ IsPullback g p q f

/--
The condition that `p : X → S` is the base change along `f : S → T` of an inner
fibration `q : Y → T`, with the top map `X → Y` in the pullback square inner anodyne.
-/
def SatisfiesInnerAnodyneDescent {X S T : SSet.{u}} (p : X ⟶ S)
    (f : S ⟶ T) : Prop :=
  ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
    InnerFibration q ∧ IsPullback g p q f ∧ innerAnodyneExtensions g

/--
An inner fibration over `T` and a pullback square over `f : S → T` provide a
descent datum for the pulled-back map over `S`.
-/
theorem SatisfiesDescent.of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (hq : InnerFibration q)
    (sq : IsPullback g p q f) : SatisfiesDescent p f :=
  ⟨Y, q, g, hq, sq⟩

/--
A pullback square with descended inner fibration over `T` and inner-anodyne top
map provides inner-anodyne descent along `f : S → T`.
-/
theorem SatisfiesInnerAnodyneDescent.of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (hq : InnerFibration q)
    (sq : IsPullback g p q f) (hg : innerAnodyneExtensions g) :
    SatisfiesInnerAnodyneDescent p f :=
  ⟨Y, q, g, hq, sq, hg⟩

/--
Forgetting the inner-anodyne requirement on the top map of a descent square gives
a descent datum.
-/
theorem SatisfiesInnerAnodyneDescent.satisfiesDescent {p : X ⟶ S}
    {f : S ⟶ T} (h : SatisfiesInnerAnodyneDescent p f) :
    SatisfiesDescent p f := by
  obtain ⟨Y, q, g, hq, sq, -⟩ := h
  exact ⟨Y, q, g, hq, sq⟩

/--
Every inner fibration satisfies descent along the identity of its base.
-/
theorem satisfiesDescent_id (p : X ⟶ S) [InnerFibration p] :
    SatisfiesDescent p (𝟙 S) :=
  ⟨X, p, 𝟙 X, inferInstance, IsPullback.of_id_fst⟩

/--
Every inner fibration satisfies inner-anodyne descent along the identity of its base,
using the identity as the top map of the pullback square.
-/
theorem satisfiesInnerAnodyneDescent_id (p : X ⟶ S)
    [InnerFibration p] : SatisfiesInnerAnodyneDescent p (𝟙 S) :=
  ⟨X, p, 𝟙 X, inferInstance, IsPullback.of_id_fst,
    innerAnodyneExtensions.id_mem X⟩

/--
The base change of an inner fibration in a pullback square is an inner fibration.
-/
theorem innerFibration_of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    [InnerFibration q] : InnerFibration p :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    InnerFibration.mem⟩

/--
A simplicial map satisfying descent is an inner fibration, since it is a base change
of the inner fibration in a descent datum.
-/
theorem SatisfiesDescent.innerFibration {p : X ⟶ S} {f : S ⟶ T}
    (h : SatisfiesDescent p f) : InnerFibration p := by
  obtain ⟨Y, q, g, hq, sq⟩ := h
  have := hq
  exact innerFibration_of_isPullback sq

/--
If `p` descends along `f` and every inner fibration witnessing that descent descends
along `k`, then `p` descends along `f ≫ k`, by pasting the corresponding pullback
squares.
-/
theorem SatisfiesDescent.comp {p : X ⟶ S} {f : S ⟶ T} {k : T ⟶ U}
    (hpf : SatisfiesDescent p f)
    (hk : ∀ (Y : SSet.{u}) (q : Y ⟶ T), InnerFibration q →
      (∃ g : X ⟶ Y, IsPullback g p q f) → SatisfiesDescent q k) :
    SatisfiesDescent p (f ≫ k) := by
  obtain ⟨Y, q, g, hq, sq⟩ := hpf
  obtain ⟨Z, r, g', hr, sq'⟩ := hk Y q hq ⟨g, sq⟩
  exact ⟨Z, r, g ≫ g', hr, sq.paste_horiz sq'⟩

/--
If `p` has inner-anodyne descent along `f` and every witness of that descent has
inner-anodyne descent along `k`, then `p` has inner-anodyne descent along `f ≫ k`.
-/
theorem SatisfiesInnerAnodyneDescent.comp {p : X ⟶ S} {f : S ⟶ T}
    {k : T ⟶ U} (hpf : SatisfiesInnerAnodyneDescent p f)
    (hk : ∀ (Y : SSet.{u}) (q : Y ⟶ T), InnerFibration q →
      (∃ g : X ⟶ Y, IsPullback g p q f ∧ innerAnodyneExtensions g) →
        SatisfiesInnerAnodyneDescent q k) :
    SatisfiesInnerAnodyneDescent p (f ≫ k) := by
  obtain ⟨Y, q, g, hq, sq, hg⟩ := hpf
  obtain ⟨Z, r, g', hr, sq', hg'⟩ := hk Y q hq ⟨g, sq, hg⟩
  exact ⟨Z, r, g ≫ g', hr, sq.paste_horiz sq',
    innerAnodyneExtensions.comp_mem _ _ hg hg'⟩

/-!
## Reflection of inner fibrations by surjective base change

If `T → S` is surjective on simplices in every degree and its base change of
`X → S` is an inner fibration, then `X → S` is an inner fibration. The surjectivity
allows each bottom simplex of an inner-horn problem to lift to `T`. See Stevenson,
Lemma 4.2.
-/

/--
If `f : T → S` is surjective in every simplicial degree and the base change of
`p : X → S` along `f` is an inner fibration, then every inner horn inclusion lifts
against `p`.
-/
theorem hasLiftingProperty_horn_of_surjective_isPullback
    {p : X ⟶ S} {f : T ⟶ S} {q : Y ⟶ T} {u : Y ⟶ X}
    (sq : IsPullback u q p f)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [InnerFibration q] {n : ℕ} {i : Fin (n + 3)} (h0 : 0 < i)
    (hn : i < Fin.last (n + 2)) :
    HasLiftingProperty Λ[n + 2, i].ι p where
  sq_hasLift {top bottom} hsq := by
    obtain ⟨t, ht⟩ := hf (n + 2) (yonedaEquiv bottom)
    let v : Δ[n + 2] ⟶ T := yonedaEquiv.symm t
    have hv : v ≫ f = bottom := by
      simp only [v, yonedaEquiv_symm_comp, ht, Equiv.symm_apply_apply]
    have hw : top ≫ p = (Λ[n + 2, i].ι ≫ v) ≫ f := by
      rw [Category.assoc, hv]
      exact hsq.w
    let topY : (Λ[n + 2, i] : SSet.{u}) ⟶ Y :=
      sq.lift top (Λ[n + 2, i].ι ≫ v) hw
    have htopY_u : topY ≫ u = top := sq.lift_fst _ _ _
    have htopY_q : topY ≫ q = Λ[n + 2, i].ι ≫ v := sq.lift_snd _ _ _
    have : HasLiftingProperty Λ[n + 2, i].ι q :=
      InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
    let sqY : CommSq topY Λ[n + 2, i].ι q v := CommSq.mk htopY_q
    refine CommSq.HasLift.mk' ⟨sqY.lift ≫ u, ?_, ?_⟩
    · rw [← Category.assoc, sqY.fac_left, htopY_u]
    · rw [Category.assoc, sq.w, ← Category.assoc, sqY.fac_right, hv]

/--
If a simplicial map `f : T → S` is degreewise surjective and a pullback of
`p : X → S` along `f` is an inner fibration, then `p` is an inner fibration.
-/
theorem innerFibration_of_surjective_isPullback {p : X ⟶ S}
    {f : T ⟶ S} {q : Y ⟶ T} {u : Y ⟶ X} (sq : IsPullback u q p f)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [InnerFibration q] : InnerFibration p where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_of_surjective_isPullback sq hf h0 hn

/--
For a degreewise surjective base map `f : T → S`, if the projection
`pullback f p → T` is an inner fibration, then `p : X → S` is an inner fibration.
-/
theorem innerFibration_of_surjective_pullback_fst (p : X ⟶ S)
    (f : T ⟶ S) (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [InnerFibration (pullback.fst f p)] : InnerFibration p :=
  innerFibration_of_surjective_isPullback
    (IsPullback.of_hasPullback f p).flip hf

/-!
## Prefibrant total objects in descent diagrams

An inner fibration with prefibrant base has prefibrant total object. This applies
to the target of a descent diagram and to the total object of a pullback over a
prefibrant simplicial set. See Stevenson, Remark 3.4.
-/

/--
A descent datum over a prefibrant base `T` can be chosen with a prefibrant total
object `Y`, since its map `Y → T` is an inner fibration.
-/
theorem SatisfiesDescent.exists_isPreFibrant_target {p : X ⟶ S}
    {f : S ⟶ T} (h : SatisfiesDescent p f) [IsPreFibrant T] :
    ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
      InnerFibration q ∧ IsPullback g p q f ∧ IsPreFibrant Y := by
  obtain ⟨Y, q, g, hq, sq⟩ := h
  have := hq
  exact ⟨Y, q, g, hq, sq, isPreFibrant_of_innerFibration q⟩

/--
For inner-anodyne descent over a prefibrant base `T`, there is a descent target `Y`
that is prefibrant, with the same inner-fibration, pullback, and inner-anodyne top-map
properties.
-/
theorem SatisfiesInnerAnodyneDescent.exists_isPreFibrant_target
    {p : X ⟶ S} {f : S ⟶ T} (h : SatisfiesInnerAnodyneDescent p f)
    [IsPreFibrant T] :
    ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
      InnerFibration q ∧ IsPullback g p q f ∧
        innerAnodyneExtensions g ∧ IsPreFibrant Y := by
  obtain ⟨Y, q, g, hq, sq, hg⟩ := h
  have := hq
  exact ⟨Y, q, g, hq, sq, hg, isPreFibrant_of_innerFibration q⟩

/--
The pullback of an inner fibration over a prefibrant simplicial set has a prefibrant
total simplicial set.
-/
instance isPreFibrant_pullback_snd (p : X ⟶ S) (f : T ⟶ S)
    [InnerFibration p] [IsPreFibrant T] :
    IsPreFibrant (pullback p f) := by
  have : InnerFibration (pullback.snd p f) :=
    innerFibration_of_isPullback (IsPullback.of_hasPullback p f)
  exact isPreFibrant_of_innerFibration (pullback.snd p f)

/-!
## Essential surjectivity and left mapping-space full faithfulness

A vertex-surjective map is essentially surjective on homotopy categories. Full
faithfulness on left mapping spaces is the condition of realization weak equivalence
on all `Homᴸ` maps; for Kan mapping spaces it agrees with the Kan weak-equivalence
condition. These statements use the indicated left or right mapping-space predicates
without identifying them. See Stevenson, Definition 2.16 and Remark 3.7.
-/

/--
A simplicial map surjective on vertices is essentially surjective on homotopy
categories.
-/
theorem dwyerKanEssentiallySurjective_of_surjective_app_zero
    {f : X ⟶ Y} (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    dwyerKanEssentiallySurjective f := by
  have hEss : (mapHomotopyCategory f).EssSurj := ⟨fun a => by
    obtain ⟨y, rfl⟩ : ∃ y, HomotopyCategory.mk y = a :=
      ⟨_, HomotopyCategory.objEquiv.left_inv a⟩
    obtain ⟨x, hx⟩ := hf y
    refine ⟨HomotopyCategory.mk x, ⟨?_⟩⟩
    rw [mapHomotopyCategory_obj_mk, hx]⟩
  exact hEss

/--
A simplicial map bijective on vertices is essentially surjective on homotopy
categories.
-/
theorem dwyerKanEssentiallySurjective_of_bijective_app_zero
    {f : X ⟶ Y} (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    dwyerKanEssentiallySurjective f :=
  dwyerKanEssentiallySurjective_of_surjective_app_zero hf.2

/--
For a map surjective on vertices, Dwyer–Kan equivalence is equivalent to full
faithfulness on the right mapping spaces, since essential surjectivity is automatic.
-/
theorem isDwyerKanEquivalence_iff_of_surjective_app_zero {f : X ⟶ Y}
    (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    isDwyerKanEquivalence f ↔ dwyerKanFullyFaithful f :=
  ⟨fun h => h.dwyerKanFullyFaithful,
    fun h => ⟨dwyerKanEssentiallySurjective_of_surjective_app_zero hf, h⟩⟩

/--
For a map bijective on vertices, Dwyer–Kan equivalence is equivalent to full
faithfulness on the right mapping spaces.
-/
theorem isDwyerKanEquivalence_iff_of_bijective_app_zero {f : X ⟶ Y}
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    isDwyerKanEquivalence f ↔ dwyerKanFullyFaithful f :=
  isDwyerKanEquivalence_iff_of_surjective_app_zero hf.2

/--
The condition that every map `Homᴸ_X(a,b) → Homᴸ_Y(fa,fb)` on left mapping spaces
is a realization weak equivalence, for all vertices `a,b` of `X`.
-/
def dwyerKanFullyFaithfulLeft (f : X ⟶ Y) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    realizationWeakEquivalences (mappingSpaceLeft.map X a b f)

/--
Full faithfulness on left mapping spaces gives a realization weak equivalence on
the mapping-space map at any pair of vertices given as zero-simplices.
-/
theorem dwyerKanFullyFaithfulLeft.vertex {f : X ⟶ Y}
    (h : dwyerKanFullyFaithfulLeft f) (x y : X _⦋0⦌) :
    realizationWeakEquivalences
      (mappingSpaceLeft.map X (const x) (const y) f) :=
  h (const x) (const y)

/--
The identity of a simplicial set is fully faithful on left mapping spaces.
-/
theorem dwyerKanFullyFaithfulLeft_id :
    dwyerKanFullyFaithfulLeft (𝟙 X) := by
  intro a b
  rw [mappingSpaceLeft.map_id]
  exact realizationWeakEquivalences.id_mem _

/--
The composite of two maps fully faithful on left mapping spaces is fully faithful
on left mapping spaces.
-/
theorem dwyerKanFullyFaithfulLeft.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : dwyerKanFullyFaithfulLeft f) (hg : dwyerKanFullyFaithfulLeft g) :
    dwyerKanFullyFaithfulLeft (f ≫ g) := by
  intro a b
  rw [mappingSpaceLeft.map_comp]
  exact realizationWeakEquivalences.comp_mem _ _ (hf a b)
    (hg (a ≫ f) (b ≫ f))

/--
If every induced map on left mapping spaces is a weak equivalence in the category
of Kan complexes, the simplicial map is fully faithful on left mapping spaces.
-/
theorem dwyerKanFullyFaithfulLeft.of_kanComplexW {f : X ⟶ Y}
    (hW : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex.W (mappingSpaceLeft.map X a b f)) :
    dwyerKanFullyFaithfulLeft f := by
  intro a b
  have : KanComplex (mappingSpaceLeft X a b) :=
    (hW a b).kanComplex_source
  have : KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)) :=
    (hW a b).kanComplex_target
  exact (KanComplex.W_iff_realizationWeakEquivalence
    (mappingSpaceLeft.map X a b f)).mp (hW a b)

/--
For a map fully faithful on left mapping spaces, each induced mapping-space map
is a Kan-complex weak equivalence when the source mapping spaces and target
mapping spaces at the image vertices are Kan complexes.
-/
theorem dwyerKanFullyFaithfulLeft.kanComplexW {f : X ⟶ Y}
    (h : dwyerKanFullyFaithfulLeft f)
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceLeft X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)))
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex.W (mappingSpaceLeft.map X a b f) := by
  have : KanComplex (mappingSpaceLeft X a b) := hKanX a b
  have : KanComplex (mappingSpaceLeft Y (a ≫ f) (b ≫ f)) :=
    hKanY a b
  exact (KanComplex.W_iff_realizationWeakEquivalence
    (mappingSpaceLeft.map X a b f)).mpr (h a b)

/--
For a map surjective on vertices, essential surjectivity together with full
faithfulness on left mapping spaces is equivalent to left full faithfulness alone.
-/
theorem dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero
    {f : X ⟶ Y} (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    (dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f) ↔
      dwyerKanFullyFaithfulLeft f :=
  ⟨fun h => h.2,
    fun h => ⟨dwyerKanEssentiallySurjective_of_surjective_app_zero hf, h⟩⟩

/--
For a map bijective on vertices, essential surjectivity together with full
faithfulness on left mapping spaces is equivalent to left full faithfulness alone.
-/
theorem dwyerKanFullyFaithfulLeft_iff_of_bijective_app_zero
    {f : X ⟶ Y} (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    (dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f) ↔
      dwyerKanFullyFaithfulLeft f :=
  dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero hf.2

end SSet

end
