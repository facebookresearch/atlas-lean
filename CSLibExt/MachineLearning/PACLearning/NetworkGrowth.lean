/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.VectorGrowth

/-!
# Product, composition, and precomposition bounds for vector growth

Counting lemmas for layered concept classes, after Shalev-Shwartz and
Ben-David, *Understanding Machine Learning: From Theory to
Algorithms*, Chapter 20 (Exercises 20.3 and 20.4 generalized): the
growth function of a finite product of classes over a shared domain,
a composition bound that needs no sample-existence hypothesis on the
intermediate type, and monotonicity of growth under injective
precomposition of the domain. These are the assembly steps toward
the growth bound for sign-activation networks (Theorem 20.6).
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

variable {α α' β γ : Type*} {ι : Type*}

/-- Bound the growth function by a uniform per-sample trace bound. -/
private theorem growthFunctionVec_le_of_traces_le [Fintype β]
    (C : ConceptClass α β) (m B : ℕ)
    (h : ∀ s : Finset α, s.card = m → tracesCard C s ≤ B) :
    growthFunctionVec C m ≤ B := by
  unfold growthFunctionVec
  rcases Set.eq_empty_or_nonempty
    { tracesCard C s | (s : Finset α) (_ : s.card = m) } with hS | hS
  · rw [hS, csSup_empty]
    exact bot_le
  · refine csSup_le hS ?_
    rintro n ⟨s, hs, rfl⟩
    exact h s hs

/-- The product class over a finite index type: a labeling is in the
class when every coordinate function lies in the corresponding factor. -/
def piClass {β : ι → Type*} (C : ∀ i, ConceptClass α (β i)) :
    ConceptClass α (∀ i, β i) :=
  {c | ∀ i, (fun x => c x i) ∈ C i}

/-- Per-sample trace bound for a finite product of classes. -/
private theorem tracesCard_piClass_le [Fintype ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [Fintype (∀ i, β i)]
    (C : ∀ i, ConceptClass α (β i)) (s : Finset α) (m : ℕ)
    (hs : s.card = m) :
    tracesCard (piClass C) s ≤ ∏ i, growthFunctionVec (C i) m := by
  classical
  rw [← traceSetVec_card_eq_tracesCard]
  have hcard : (traceSetVec (piClass C) s).card
      ≤ ∏ i, (traceSetVec (C i) s).card := by
    have h1 : (traceSetVec (piClass C) s).card
        ≤ (Fintype.piFinset fun i => traceSetVec (C i) s).card := by
      refine Finset.card_le_card_of_injOn (fun t i x => t x i) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, mem_traceSetVec] at ht
        obtain ⟨c, hc, htc⟩ := ht
        rw [Finset.mem_coe, Fintype.mem_piFinset]
        intro i
        rw [mem_traceSetVec]
        refine ⟨fun x => c x i, hc i, fun x => ?_⟩
        exact congrArg (fun f => f i) (htc x)
      · apply Function.Injective.injOn
        intro t₁ t₂ h12
        funext x i
        exact congrFun (congrFun h12 i) x
    rw [Fintype.card_piFinset] at h1
    exact h1
  have hgen : ∀ Q : Finset ι, (∀ i ∈ Q, (traceSetVec (C i) s).card
      ≤ growthFunctionVec (C i) m) →
      (∏ i ∈ Q, (traceSetVec (C i) s).card)
      ≤ ∏ i ∈ Q, growthFunctionVec (C i) m := by
    intro Q
    refine Finset.induction_on Q ?_ ?_
    · intro _
      rw [Finset.prod_empty, Finset.prod_empty]
    · intro a Q' haQ' ih hmem
      rw [Finset.prod_insert haQ', Finset.prod_insert haQ']
      apply Nat.mul_le_mul
      · exact hmem a (Finset.mem_insert_self a Q')
      · apply ih
        intro i hi
        exact hmem i (Finset.mem_insert_of_mem hi)
  have hbound : ∀ i ∈ (Finset.univ : Finset ι),
      (traceSetVec (C i) s).card ≤ growthFunctionVec (C i) m := by
    intro i _
    have hle := traceSetVec_card_le_growthFunctionVec (C i) s
    rw [hs] at hle
    exact hle
  have h2 : ∏ i, (traceSetVec (C i) s).card
      ≤ ∏ i, growthFunctionVec (C i) m :=
    hgen Finset.univ hbound
  exact hcard.trans h2

/-- Growth function of a finite product: at most the product of the
factor growth functions. -/
theorem growthFunctionVec_pi_le [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [Fintype (∀ i, β i)] (C : ∀ i, ConceptClass α (β i)) (m : ℕ) :
    growthFunctionVec (piClass C) m ≤ ∏ i, growthFunctionVec (C i) m := by
  apply growthFunctionVec_le_of_traces_le
  intro s hs
  exact tracesCard_piClass_le C s m hs

/-- Per-sample trace bound for composition, with the outer growth
capped by the intermediate type's cardinality. -/
private theorem tracesCard_comp_le_card [Fintype β] [Fintype γ]
    (C₁ : ConceptClass α γ) (C₂ : ConceptClass γ β) (s : Finset α)
    (m : ℕ) (hs : s.card = m) :
    tracesCard (compClass C₁ C₂) s ≤
      growthFunctionVec C₂ (min m (Fintype.card γ)) *
        growthFunctionVec C₁ m := by
  classical
  rw [← traceSetVec_card_eq_tracesCard]
  have hfiber : ∀ u ∈ traceSetVec C₁ s,
      ((traceSetVec (compClass C₁ C₂) s).filter (fun t =>
        ∃ c ∈ compClass C₁ C₂, (∀ x : s, t x = c ↑x) ∧
          ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, (∀ x, c x = c₂ (c₁ x)) ∧
            (∀ x : s, c₁ ↑x = u x))).card
      ≤ growthFunctionVec C₂ (min m (Fintype.card γ)) := by
    intro u hu
    rw [mem_traceSetVec] at hu
    obtain ⟨c₁r, hc₁r, htrr⟩ := hu
    have hScard : (s.image c₁r).card ≤ min m (Fintype.card γ) := by
      apply le_min
      · have h1 : (s.image c₁r).card ≤ s.card := Finset.card_image_le
        rw [hs] at h1
        exact h1
      · exact Finset.card_le_univ _
    have hexγ : ∃ s0 : Finset γ, s0.card = min m (Fintype.card γ) := by
      obtain ⟨t, -, htcard⟩ :=
        Finset.exists_subset_card_eq (s := (Finset.univ : Finset γ))
          (n := min m (Fintype.card γ)) (by
            rw [Finset.card_univ]
            exact min_le_right _ _)
      exact ⟨t, htcard⟩
    have hmono : growthFunctionVec C₂ (s.image c₁r).card
        ≤ growthFunctionVec C₂ (min m (Fintype.card γ)) :=
      growthFunctionVec_mono hScard hexγ
    have hpre : ∀ y : ↥(s.image c₁r), ∃ x : s, c₁r ↑x = ↑y := by
      intro y
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp y.2
      exact ⟨⟨a, ha⟩, hay⟩
    choose g hg using hpre
    have hle : ((traceSetVec (compClass C₁ C₂) s).filter (fun t =>
        ∃ c ∈ compClass C₁ C₂, (∀ x : s, t x = c ↑x) ∧
          ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, (∀ x, c x = c₂ (c₁ x)) ∧
            (∀ x : s, c₁ ↑x = u x))).card
        ≤ (traceSetVec C₂ (s.image c₁r)).card := by
      refine Finset.card_le_card_of_injOn (fun t y => t (g y)) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht
        obtain ⟨ht_mem, c, hc_mem, htc, c₁, hc₁, c₂, hc₂, hcomp,
          hagree⟩ := ht
        rw [Finset.mem_coe, mem_traceSetVec]
        refine ⟨c₂, hc₂, fun y => ?_⟩
        have hinner : c₁ ↑(g y) = ↑y := by
          calc c₁ ↑(g y) = u (g y) := hagree (g y)
            _ = c₁r ↑(g y) := htrr (g y)
            _ = ↑y := hg y
        calc t (g y) = c ↑(g y) := htc (g y)
          _ = c₂ (c₁ ↑(g y)) := hcomp ↑(g y)
          _ = c₂ ↑y := by rw [hinner]
      · intro t₁ ht₁ t₂ ht₂ h12
        rw [Finset.mem_coe, Finset.mem_filter] at ht₁ ht₂
        obtain ⟨ht₁_mem, c', hc'_mem, htc₁, c₁', hc₁', c₂', hc₂',
          hcomp₁, hagree₁⟩ := ht₁
        obtain ⟨ht₂_mem, c'', hc''_mem, htc₂, c₁'', hc₁'', c₂'',
          hc₂'', hcomp₂, hagree₂⟩ := ht₂
        have hvv : ∀ y, t₁ (g y) = t₂ (g y) := fun y => congrFun h12 y
        funext x
        have key : ∀ (t : s → β) (c : α → β) (c₁ : α → γ)
            (c₂ : γ → β) (y₀ : ↥(s.image c₁r)),
            (∀ x : s, t x = c ↑x) → (∀ x, c x = c₂ (c₁ x)) →
            (∀ x : s, c₁ ↑x = u x) → ↑y₀ = c₁r ↑x →
            t x = t (g y₀) := by
          intro t c c₁ c₂ y₀ htc hcomp hagree hy0
          have hgy : c₁r ↑(g y₀) = c₁r ↑x := by rw [hg y₀, hy0]
          have e1 : t x = c₂ (c₁r ↑x) := by
            calc t x = c ↑x := htc x
              _ = c₂ (c₁ ↑x) := hcomp ↑x
              _ = c₂ (u x) := by rw [hagree x]
              _ = c₂ (c₁r ↑x) := by rw [htrr x]
          have e2 : c₂ (c₁r ↑x) = t (g y₀) := by
            calc c₂ (c₁r ↑x) = c₂ (c₁r ↑(g y₀)) := by rw [← hgy]
              _ = c₂ (u (g y₀)) := by rw [← htrr (g y₀)]
              _ = c₂ (c₁ ↑(g y₀)) := by rw [← hagree (g y₀)]
              _ = c ↑(g y₀) := (hcomp _).symm
              _ = t (g y₀) := (htc _).symm
          exact e1.trans e2
        have hy0 : (↑(⟨c₁r ↑x, Finset.mem_image_of_mem c₁r x.2⟩ :
            ↥(s.image c₁r)) = c₁r ↑x) := rfl
        calc t₁ x
            = t₁ (g ⟨c₁r ↑x, Finset.mem_image_of_mem c₁r x.2⟩) :=
              key t₁ c' c₁' c₂' _ htc₁ hcomp₁ hagree₁ hy0
          _ = t₂ (g ⟨c₁r ↑x, Finset.mem_image_of_mem c₁r x.2⟩) :=
              hvv ⟨c₁r ↑x, Finset.mem_image_of_mem c₁r x.2⟩
          _ = t₂ x :=
              (key t₂ c'' c₁'' c₂'' _ htc₂ hcomp₂ hagree₂ hy0).symm
    have hle2 : (traceSetVec C₂ (s.image c₁r)).card
        ≤ growthFunctionVec C₂ (min m (Fintype.card γ)) := by
      have h1 := traceSetVec_card_le_growthFunctionVec C₂ (s.image c₁r)
      exact h1.trans hmono
    exact hle.trans hle2
  have hsub : traceSetVec (compClass C₁ C₂) s ⊆
      (traceSetVec C₁ s).biUnion fun u =>
        (traceSetVec (compClass C₁ C₂) s).filter (fun t =>
          ∃ c ∈ compClass C₁ C₂, (∀ x : s, t x = c ↑x) ∧
            ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, (∀ x, c x = c₂ (c₁ x)) ∧
              (∀ x : s, c₁ ↑x = u x)) := by
    intro t ht
    have ht_mem : t ∈ traceSetVec (compClass C₁ C₂) s := ht
    rw [mem_traceSetVec] at ht
    obtain ⟨c, hc, htc⟩ := ht
    have hc_mem : c ∈ compClass C₁ C₂ := hc
    rw [compClass] at hc
    obtain ⟨c₁, hc₁, c₂, hc₂, hcomp⟩ := hc
    have hcomp' : ∀ x, c x = c₂ (c₁ x) := fun x => by rw [hcomp]
    have hu : (fun x : s => c₁ ↑x) ∈ traceSetVec C₁ s :=
      mem_traceSetVec.mpr ⟨c₁, hc₁, fun x => rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨_, hu, Finset.mem_filter.mpr ⟨ht_mem, c, hc_mem, htc, c₁,
      hc₁, c₂, hc₂, hcomp', fun x => rfl⟩⟩
  have hsum : ∀ Q : Finset (s → γ), Q ⊆ traceSetVec C₁ s →
      (Q.biUnion fun u =>
        (traceSetVec (compClass C₁ C₂) s).filter (fun t =>
          ∃ c ∈ compClass C₁ C₂, (∀ x : s, t x = c ↑x) ∧
            ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, (∀ x, c x = c₂ (c₁ x)) ∧
              (∀ x : s, c₁ ↑x = u x))).card
      ≤ ∑ u ∈ Q, growthFunctionVec C₂ (min m (Fintype.card γ)) := by
    intro Q
    refine Finset.induction_on Q ?_ ?_
    · intro _
      rw [Finset.biUnion_empty, Finset.sum_empty, Finset.card_empty]
    · intro a Q' haQ' ih hsub'
      rw [Finset.biUnion_insert, Finset.sum_insert haQ']
      refine (Finset.card_union_le _ _).trans ?_
      apply Nat.add_le_add
      · apply hfiber
        exact hsub' (Finset.mem_insert_self a Q')
      · apply ih
        intro x hx
        exact hsub' (Finset.mem_insert_of_mem hx)
  have hagg := hsum (traceSetVec C₁ s) (fun x hx => hx)
  have hfin : (traceSetVec (compClass C₁ C₂) s).card
      ≤ ∑ u ∈ traceSetVec C₁ s,
        growthFunctionVec C₂ (min m (Fintype.card γ)) :=
    (Finset.card_le_card hsub).trans hagg
  rw [Finset.sum_const, Nat.nsmul_eq_mul] at hfin
  have hT1 : (traceSetVec C₁ s).card ≤ growthFunctionVec C₁ m := by
    have hle := traceSetVec_card_le_growthFunctionVec C₁ s
    rw [hs] at hle
    exact hle
  calc (traceSetVec (compClass C₁ C₂) s).card
      ≤ (traceSetVec C₁ s).card *
        growthFunctionVec C₂ (min m (Fintype.card γ)) := hfin
    _ = growthFunctionVec C₂ (min m (Fintype.card γ)) *
        (traceSetVec C₁ s).card := mul_comm _ _
    _ ≤ growthFunctionVec C₂ (min m (Fintype.card γ)) *
        growthFunctionVec C₁ m := Nat.mul_le_mul le_rfl hT1

/-- Composition bound with the intermediate growth capped by the
intermediate type's cardinality, so no sample-existence hypothesis
on the intermediate type is needed. When an `m`-element sample of
the intermediate type exists, `min m (Fintype.card γ) = m` and this
is the usual composition bound. -/
theorem growthFunctionVec_comp_le_card [Fintype β] [Fintype γ]
    (C₁ : ConceptClass α γ) (C₂ : ConceptClass γ β) (m : ℕ) :
    growthFunctionVec (compClass C₁ C₂) m ≤
      growthFunctionVec C₂ (min m (Fintype.card γ)) *
        growthFunctionVec C₁ m := by
  apply growthFunctionVec_le_of_traces_le
  intro s hs
  exact tracesCard_comp_le_card C₁ C₂ s m hs

/-- The class obtained by precomposing every concept with a fixed
domain map. -/
def precompClass (f : α' → α) (C : ConceptClass α β) : ConceptClass α' β :=
  {c | ∃ c' ∈ C, c = c' ∘ f}

/-- Per-sample trace bound for precomposition with an injective map. -/
private theorem tracesCard_precomp_le [Fintype β] {f : α' → α}
    (hf : Function.Injective f) (C : ConceptClass α β) (s' : Finset α')
    (m : ℕ) (hs : s'.card = m) :
    tracesCard (precompClass f C) s' ≤ growthFunctionVec C m := by
  classical
  rw [← traceSetVec_card_eq_tracesCard]
  have hcard : (s'.image f).card = m := by
    rw [Finset.card_image_of_injective s' hf, hs]
  have hle : (traceSetVec (precompClass f C) s').card
      ≤ (traceSetVec C (s'.image f)).card := by
    have hpre : ∀ y : ↥(s'.image f), ∃ x : s', f ↑x = ↑y := by
      intro y
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp y.2
      exact ⟨⟨a, ha⟩, hay⟩
    choose g hg using hpre
    refine Finset.card_le_card_of_injOn (fun t' y => t' (g y)) ?_ ?_
    · intro t' ht'
      rw [Finset.mem_coe, mem_traceSetVec] at ht'
      obtain ⟨c, hc, htc⟩ := ht'
      rw [precompClass] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Finset.mem_coe, mem_traceSetVec]
      refine ⟨c', hc', fun y => ?_⟩
      calc t' (g y) = c' (f ↑(g y)) := htc (g y)
        _ = c' ↑y := by rw [hg y]
    · apply Function.Injective.injOn
      intro t₁' t₂' h12
      funext x
      have hgx : ∀ t' : s' → β,
          t' (g ⟨f ↑x, Finset.mem_image_of_mem f x.2⟩) = t' x := by
        intro t'
        have hgy : g ⟨f ↑x, Finset.mem_image_of_mem f x.2⟩ = x := by
          apply Subtype.ext
          apply hf
          exact hg ⟨f ↑x, Finset.mem_image_of_mem f x.2⟩
        rw [hgy]
      calc t₁' x = t₁' (g ⟨f ↑x, Finset.mem_image_of_mem f x.2⟩) :=
            (hgx t₁').symm
        _ = t₂' (g ⟨f ↑x, Finset.mem_image_of_mem f x.2⟩) :=
            congrFun h12 _
        _ = t₂' x := hgx t₂'
  have hle2 : (traceSetVec C (s'.image f)).card
      ≤ growthFunctionVec C m := by
    have h1 := traceSetVec_card_le_growthFunctionVec C (s'.image f)
    rw [hcard] at h1
    exact h1
  exact hle.trans hle2

/-- Precomposition with an injective domain map does not increase
the growth function. -/
theorem growthFunctionVec_precomp_le [Fintype β] {f : α' → α}
    (hf : Function.Injective f) (C : ConceptClass α β) (m : ℕ) :
    growthFunctionVec (precompClass f C) m ≤ growthFunctionVec C m := by
  apply growthFunctionVec_le_of_traces_le
  intro s hs
  exact tracesCard_precomp_le hf C s m hs

end Cslib.MachineLearning.PACLearning
