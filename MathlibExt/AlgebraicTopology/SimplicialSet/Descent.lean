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
# Descent for inner fibrations and pre-fibrant simplicial sets

In Stevenson's §4, "4.2" is a *Lemma* (surjective base change, below),
not a Proposition; the section's main descent result is Proposition
4.12. Both are quoted verbatim below. Likewise Proposition 3.5(2) is
a mapping-space *preservation* statement for a specific replacement
map, not a categorical-equivalence criterion; the criterion is Remark
3.7, also quoted below.

Stevenson's Definition 3.1 of pre-fibrant is purely a horn-filling
condition, and the landed predicate `SSet.IsPreFibrant` therefore
uses **no** mapping-space model at all: it is neither stated with the
exponential (path-object) slices of `Slice.lean`
(`SSet.pathMappingSpaceLeft` etc.) nor with the join slices; see the
header of `PreFibrant.lean`. Where mapping spaces do
occur in Stevenson's §3 consequences (Remark 3.3, Proposition 3.5(2),
Remark 3.7) they are the *naive* (join-slice) ones of his §2.4:
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T U X Y Z : SSet.{u}}

/-!
### Descent (Stevenson Definition 4.1)
-/

/-- Stevenson's Definition 4.1: an inner fibration `p : X ⟶ S`
*satisfies descent* relative to `f : S ⟶ T` if there is an inner
fibration `q : Y ⟶ T` and a map `g : X ⟶ Y` forming a pullback
square `IsPullback g p q f`. Following the letter of the definition,
`InnerFibration p` is not part of the predicate; it follows from the
pullback square (`SSet.SatisfiesDescent.innerFibration`). -/
def SatisfiesDescent {X S T : SSet.{u}} (p : X ⟶ S) (f : S ⟶ T) : Prop :=
  ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
    InnerFibration q ∧ IsPullback g p q f

/-- Stevenson's inner anodyne descent (Definition 4.1, second part):
`p` satisfies descent relative to `f` by a pullback square whose top
map `g` is inner anodyne. Stevenson only uses this when `f` itself
is inner anodyne; that hypothesis is kept separate here. -/
def SatisfiesInnerAnodyneDescent {X S T : SSet.{u}} (p : X ⟶ S)
    (f : S ⟶ T) : Prop :=
  ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
    InnerFibration q ∧ IsPullback g p q f ∧ innerAnodyneExtensions g

/-- A pullback square over an inner fibration exhibits descent. -/
theorem SatisfiesDescent.of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (hq : InnerFibration q)
    (sq : IsPullback g p q f) : SatisfiesDescent p f :=
  ⟨Y, q, g, hq, sq⟩

/-- A pullback square over an inner fibration with inner anodyne top
map exhibits inner anodyne descent. -/
theorem SatisfiesInnerAnodyneDescent.of_isPullback {p : X ⟶ S}
    {f : S ⟶ T} {q : Y ⟶ T} {g : X ⟶ Y} (hq : InnerFibration q)
    (sq : IsPullback g p q f) (hg : innerAnodyneExtensions g) :
    SatisfiesInnerAnodyneDescent p f :=
  ⟨Y, q, g, hq, sq, hg⟩

/-- Inner anodyne descent implies descent. -/
theorem SatisfiesInnerAnodyneDescent.satisfiesDescent {p : X ⟶ S}
    {f : S ⟶ T} (h : SatisfiesInnerAnodyneDescent p f) :
    SatisfiesDescent p f := by
  obtain ⟨Y, q, g, hq, sq, -⟩ := h
  exact ⟨Y, q, g, hq, sq⟩

/-- Every inner fibration satisfies descent along the identity, by
the identity pullback square. -/
theorem satisfiesDescent_id (p : X ⟶ S) [InnerFibration p] :
    SatisfiesDescent p (𝟙 S) :=
  ⟨X, p, 𝟙 X, inferInstance, IsPullback.of_id_fst⟩

/-- Every inner fibration satisfies inner anodyne descent along the
identity: the top map of the identity pullback square is `𝟙 X`,
which is inner anodyne. -/
theorem satisfiesInnerAnodyneDescent_id (p : X ⟶ S)
    [InnerFibration p] : SatisfiesInnerAnodyneDescent p (𝟙 S) :=
  ⟨X, p, 𝟙 X, inferInstance, IsPullback.of_id_fst,
    innerAnodyneExtensions.id_mem X⟩

/-- If `p` is the pullback of an inner fibration `q`, then `p` is an
inner fibration: stability of inner fibrations under base change. -/
theorem innerFibration_of_isPullback {p : X ⟶ S} {f : S ⟶ T}
    {q : Y ⟶ T} {g : X ⟶ Y} (sq : IsPullback g p q f)
    [InnerFibration q] : InnerFibration p :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    InnerFibration.mem⟩

/-- A map satisfying descent is an inner fibration, as in the
hypotheses of Stevenson's Definition 4.1. -/
theorem SatisfiesDescent.innerFibration {p : X ⟶ S} {f : S ⟶ T}
    (h : SatisfiesDescent p f) : InnerFibration p := by
  obtain ⟨Y, q, g, hq, sq⟩ := h
  have := hq
  exact innerFibration_of_isPullback sq

/-- Descent composes: if `p` satisfies descent along `f`, and every
inner fibration exhibiting that descent satisfies descent along `k`,
then `p` satisfies descent along `f ≫ k`, by pasting pullback
squares. The universally quantified second hypothesis is needed
because the descent target of `p` along `f` is not canonical. -/
theorem SatisfiesDescent.comp {p : X ⟶ S} {f : S ⟶ T} {k : T ⟶ U}
    (hpf : SatisfiesDescent p f)
    (hk : ∀ (Y : SSet.{u}) (q : Y ⟶ T), InnerFibration q →
      (∃ g : X ⟶ Y, IsPullback g p q f) → SatisfiesDescent q k) :
    SatisfiesDescent p (f ≫ k) := by
  obtain ⟨Y, q, g, hq, sq⟩ := hpf
  obtain ⟨Z, r, g', hr, sq'⟩ := hk Y q hq ⟨g, sq⟩
  exact ⟨Z, r, g ≫ g', hr, sq.paste_horiz sq'⟩

/-- Inner anodyne descent composes: as in
`SSet.SatisfiesDescent.comp`, with the composite top map inner
anodyne by stability of inner anodyne extensions under
composition. -/
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
### Surjective base change (Stevenson Lemma 4.2)
-/

/-- Inner horn inclusions lift against `p` when `p` is the pullback
of an inner fibration `q` along a map `f` surjective on simplices in
every degree: the bottom simplex of a lifting problem factors
through `f`, the horn map then factors through the pullback, and the
filler for `q` induces a filler for `p`. This is the proof of
Stevenson's Lemma 4.2. -/
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

/-- **Stevenson Lemma 4.2**: suppose `f : T ⟶ S` is surjective on
simplices in every degree and there is a pullback square exhibiting
`p : X ⟶ S` as the pullback of an inner fibration `q : Y ⟶ T` along
`f`. Then `p` is an inner fibration. -/
theorem innerFibration_of_surjective_isPullback {p : X ⟶ S}
    {f : T ⟶ S} {q : Y ⟶ T} {u : Y ⟶ X} (sq : IsPullback u q p f)
    (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [InnerFibration q] : InnerFibration p where
  mem := by
    intro _ _ g hg
    obtain ⟨i, h0, hn⟩ := hg
    exact hasLiftingProperty_horn_of_surjective_isPullback sq hf h0 hn

/-- Stevenson Lemma 4.2 for the chosen pullback: if `f : T ⟶ S` is
surjective on simplices in every degree and the base change of
`p : X ⟶ S` along `f` (the first projection of `pullback f p`) is an
inner fibration, then `p` is an inner fibration. -/
theorem innerFibration_of_surjective_pullback_fst (p : X ⟶ S)
    (f : T ⟶ S) (hf : ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))
    [InnerFibration (pullback.fst f p)] : InnerFibration p :=
  innerFibration_of_surjective_isPullback
    (IsPullback.of_hasPullback f p).flip hf

/-!
### Pre-fibrancy in descent diagrams (Remark 3.4 in §4)
-/

/-- The way Remark 3.4 is used in Stevenson's §4–§5: in a descent
diagram over a pre-fibrant base `T`, the descent target `Y` may be
chosen pre-fibrant as well (any target works: an inner fibration to
a pre-fibrant base has pre-fibrant source, by
`SSet.isPreFibrant_of_innerFibration`). -/
theorem SatisfiesDescent.exists_isPreFibrant_target {p : X ⟶ S}
    {f : S ⟶ T} (h : SatisfiesDescent p f) [IsPreFibrant T] :
    ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
      InnerFibration q ∧ IsPullback g p q f ∧ IsPreFibrant Y := by
  obtain ⟨Y, q, g, hq, sq⟩ := h
  have := hq
  exact ⟨Y, q, g, hq, sq, isPreFibrant_of_innerFibration q⟩

/-- The inner-anodyne form of
`SSet.SatisfiesDescent.exists_isPreFibrant_target`: inner anodyne
descent over a pre-fibrant base has a pre-fibrant target. This is
the shape of Stevenson's Proposition 4.12 conclusion ("`T`, and
hence `Y`, is pre-fibrant"); the existence of the descent datum
itself is the additional comparison obligation. -/
theorem SatisfiesInnerAnodyneDescent.exists_isPreFibrant_target
    {p : X ⟶ S} {f : S ⟶ T} (h : SatisfiesInnerAnodyneDescent p f)
    [IsPreFibrant T] :
    ∃ (Y : SSet.{u}) (q : Y ⟶ T) (g : X ⟶ Y),
      InnerFibration q ∧ IsPullback g p q f ∧
        innerAnodyneExtensions g ∧ IsPreFibrant Y := by
  obtain ⟨Y, q, g, hq, sq, hg⟩ := h
  have := hq
  exact ⟨Y, q, g, hq, sq, hg, isPreFibrant_of_innerFibration q⟩

/-- Pulling an inner fibration back to a pre-fibrant simplicial set
`T` has pre-fibrant total object: the second projection
`pullback p f ⟶ T` is an inner fibration (base change of `p`), so
Remark 3.4 applies. -/
instance isPreFibrant_pullback_snd (p : X ⟶ S) (f : T ⟶ S)
    [InnerFibration p] [IsPreFibrant T] :
    IsPreFibrant (pullback p f) := by
  have : InnerFibration (pullback.snd p f) :=
    innerFibration_of_isPullback (IsPullback.of_hasPullback p f)
  exact isPreFibrant_of_innerFibration (pullback.snd p f)

/-!
### Mapping-space criteria (Stevenson Remark 3.7)
-/

/-- A map surjective on vertices is essentially surjective in the
sense of Stevenson Definition 2.16(i): its induced functor on
homotopy categories is surjective on objects, since the objects of
`h(Y)` are the vertices of `Y` and `(h f)(x) = f(x)` on vertices.
Only surjectivity on vertices is needed; injectivity plays no
role. -/
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

/-- A map bijective on vertices is essentially surjective in the
sense of Stevenson Definition 2.16(i): the vertex-bijective case
of `SSet.dwyerKanEssentiallySurjective_of_surjective_app_zero`. -/
theorem dwyerKanEssentiallySurjective_of_bijective_app_zero
    {f : X ⟶ Y} (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    dwyerKanEssentiallySurjective f :=
  dwyerKanEssentiallySurjective_of_surjective_app_zero hf.2

/-- For a map surjective on vertices, being a Dwyer–Kan equivalence
(Stevenson Definition 2.16) is exactly full faithfulness on mapping
spaces: essential surjectivity is automatic from surjectivity on
vertices alone. Stated with the landed right-mapping-space
predicate `SSet.dwyerKanFullyFaithful`; the left-handed analogue is
`SSet.dwyerKanFullyFaithfulLeft` below. Combined with Proposition
2.24 (between ∞-categories) and Proposition 3.5 (reducing
pre-fibrant simplicial sets to ∞-categories without changing naive
mapping spaces), this is the reduction step in the criterion
"surjective on vertices and weak equivalences on naive mapping
spaces iff categorical equivalence" for maps between pre-fibrant
simplicial sets; the Proposition 3.5 input is the additional comparison obligation. -/
theorem isDwyerKanEquivalence_iff_of_surjective_app_zero {f : X ⟶ Y}
    (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    isDwyerKanEquivalence f ↔ dwyerKanFullyFaithful f :=
  ⟨fun h => h.dwyerKanFullyFaithful,
    fun h => ⟨dwyerKanEssentiallySurjective_of_surjective_app_zero hf, h⟩⟩

/-- For a map bijective on vertices, being a Dwyer–Kan equivalence
(Stevenson Definition 2.16) is exactly full faithfulness on mapping
spaces: the vertex-bijective case of
`SSet.isDwyerKanEquivalence_iff_of_surjective_app_zero`. -/
theorem isDwyerKanEquivalence_iff_of_bijective_app_zero {f : X ⟶ Y}
    (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    isDwyerKanEquivalence f ↔ dwyerKanFullyFaithful f :=
  isDwyerKanEquivalence_iff_of_surjective_app_zero hf.2

/-- The fully-faithful half of Stevenson Definition 2.16(ii) and
Remark 3.7, stated with the *left* mapping spaces
`Homᴸ_X(x, y) = SSet.mappingSpaceLeft X x y` of
`JoinSlice.lean`, as in the paper (the landed
`SSet.dwyerKanFullyFaithful` uses right mapping spaces; see
the additional comparison obligation): for all vertex maps `a b : Δ[0] ⟶ X`, the
induced map `mappingSpaceLeft X a b ⟶ mappingSpaceLeft Y (a ≫ f)
(b ≫ f)` is a realization weak equivalence. Like the landed
right-handed predicate, this uses
`SSet.realizationWeakEquivalences`, which is defined on arbitrary
simplicial sets and imposes no Kan hypothesis on the mapping
spaces; when the mapping spaces are Kan complexes it agrees with
`SSet.KanComplex.W` by
`SSet.KanComplex.W_iff_realizationWeakEquivalence` (see
`SSet.dwyerKanFullyFaithfulLeft.of_kanComplexW` and
`SSet.dwyerKanFullyFaithfulLeft.kanComplexW` below). For
pre-fibrant `X, Y`, Kan-ness of the left mapping spaces is the
unproved Remark 3.3 (the additional comparison obligation). -/
def dwyerKanFullyFaithfulLeft (f : X ⟶ Y) : Prop :=
  ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
    realizationWeakEquivalences (mappingSpaceLeft.map X a b f)

/-- The vertex form of `SSet.dwyerKanFullyFaithfulLeft`, for
vertices given as `0`-simplices. -/
theorem dwyerKanFullyFaithfulLeft.vertex {f : X ⟶ Y}
    (h : dwyerKanFullyFaithfulLeft f) (x y : X _⦋0⦌) :
    realizationWeakEquivalences
      (mappingSpaceLeft.map X (const x) (const y) f) :=
  h (const x) (const y)

/-- The identity is fully faithful on left mapping spaces,
unconditionally: realization weak equivalences contain identities
with no Kan hypothesis on the mapping spaces. -/
theorem dwyerKanFullyFaithfulLeft_id :
    dwyerKanFullyFaithfulLeft (𝟙 X) := by
  intro a b
  rw [mappingSpaceLeft.map_id]
  exact realizationWeakEquivalences.id_mem _

/-- Full faithfulness on left mapping spaces is stable under
composition, by `SSet.mappingSpaceLeft.map_comp` and
`SSet.realizationWeakEquivalences.comp_mem`. -/
theorem dwyerKanFullyFaithfulLeft.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : dwyerKanFullyFaithfulLeft f) (hg : dwyerKanFullyFaithfulLeft g) :
    dwyerKanFullyFaithfulLeft (f ≫ g) := by
  intro a b
  rw [mappingSpaceLeft.map_comp]
  exact realizationWeakEquivalences.comp_mem _ _ (hf a b)
    (hg (a ≫ f) (b ≫ f))

/-- Bridge from `SSet.KanComplex.W` to full faithfulness on left
mapping spaces: if every induced map on left mapping spaces is a
`SSet.KanComplex.W` weak equivalence, then `f` is fully faithful
on left mapping spaces. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances extracted from
each `hW a b` by `SSet.KanComplex.W.kanComplex_source` and
`SSet.KanComplex.W.kanComplex_target`; no separate Kan
hypotheses are needed. -/
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

/-- Bridge from full faithfulness on left mapping spaces to
`SSet.KanComplex.W`: if `f` is fully faithful on left mapping
spaces and all source left mapping spaces and all target left
mapping spaces at `f`-image vertices are Kan complexes, then every
induced map on left mapping spaces is a `SSet.KanComplex.W` weak
equivalence. This is
`SSet.KanComplex.W_iff_realizationWeakEquivalence` applied
pointwise, with the `SSet.KanComplex` instances supplied from
`hKanX` and `hKanY`. -/
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

/-- For a map surjective on vertices, essential surjectivity
together with full faithfulness on *left* mapping spaces is
equivalent to full faithfulness on left mapping spaces alone: the
left-handed form of
`SSet.isDwyerKanEquivalence_iff_of_surjective_app_zero`, matching
Remark 3.7's use of `Homᴸ`. Only surjectivity on vertices is
needed. -/
theorem dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero
    {f : X ⟶ Y} (hf : Function.Surjective (f.app (op ⦋0⦌))) :
    (dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f) ↔
      dwyerKanFullyFaithfulLeft f :=
  ⟨fun h => h.2,
    fun h => ⟨dwyerKanEssentiallySurjective_of_surjective_app_zero hf, h⟩⟩

/-- For a map bijective on vertices, essential surjectivity
together with full faithfulness on *left* mapping spaces is
equivalent to full faithfulness on left mapping spaces alone: the
vertex-bijective case of
`SSet.dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero`. -/
theorem dwyerKanFullyFaithfulLeft_iff_of_bijective_app_zero
    {f : X ⟶ Y} (hf : Function.Bijective (f.app (op ⦋0⦌))) :
    (dwyerKanEssentiallySurjective f ∧ dwyerKanFullyFaithfulLeft f) ↔
      dwyerKanFullyFaithfulLeft f :=
  dwyerKanFullyFaithfulLeft_iff_of_surjective_app_zero hf.2

end SSet

end
