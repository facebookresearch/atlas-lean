/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Corresponding genomic interactions between two replicates

A chromatin interaction found by a ChIA-PET, HiChIP or Hi-C experiment joins two genomic regions,
its *anchors*. To compare the interactions found by two replicate experiments, IDR2D (Krismer, Guo
and Gifford 2020) pairs each interaction of replicate 1 with the interactions of replicate 2 whose
two anchors both overlap its anchors, or lie within a maximal gap of them (Figure 1C). When several
interactions of replicate 2 correspond to the same interaction of replicate 1, one of them is
chosen by minimizing an *ambiguity-resolution value* (Figure 1D and Eq. (1)): the genomic distance
between the anchor midpoints, the additive inverse of the relative anchor overlap, or the sum of the
two interactions' ranks. The result is a one-to-one correspondence: an interaction of replicate 1
that corresponds to some interaction of replicate 2 is paired with one of minimal value, unless such
a partner is paired with another interaction of replicate 1. The scores of its pairs then enter the
copula mixture model of the irreproducible discovery rate
(`Domains.Biology.Omics.IrreproducibleDiscoveryRate`).

## Conventions

* An anchor is a closed interval `[start, stop]` of base-pair positions on a chromosome, with
  `start ≤ stop`. Two anchors are *within gap `g`* when they lie on the same chromosome and their
  gap `max start₁ start₂ - min stop₁ stop₂ - 1` is at most `g`. For disjoint anchors the gap is the
  number of positions strictly between them, `0` for adjacent ones, and it is negative for
  overlapping ones: `g = -1` asks the anchors to overlap, sharing a position, and `g ≥ -1` is
  IDR2D's maximal gap (its default `-1`, overlap).
* An interaction is a pair of anchors `(A, B)`. Two interactions *correspond* when their first
  anchors are within the gap of each other, and so are their second anchors.
* The interactions of the two replicates form types `ι₁` and `ι₂`, with anchors `x₁ : ι₁ → _` and
  `x₂ : ι₂ → _`. The ambiguity-resolution value is any `f : ι₁ → ι₂ → ℝ`, as the source lets the
  analyst choose among three; lower values are better.

## Main definitions

* `Anchor`: a nonempty closed interval of positions on a chromosome.
* `Anchor.WithinGap g a b`: the anchors `a` and `b` overlap or lie within the gap `g` of each other.
* `Corresponds g I J`: both anchors of the interactions `I` and `J` are within the gap `g`.
* `IsResolvedPartner g x₁ x₂ f i j`: the interaction `j` of replicate 2 corresponds to the
  interaction `i` of replicate 1 and minimizes the ambiguity-resolution value `f i` among those that
  do (Eq. (1)).
* `IsResolvedCorrespondence g x₁ x₂ f P`: `P` is a one-to-one correspondence whose pairs are
  resolved partners and which pairs every interaction of replicate 1 that has a corresponding
  interaction, unless one of its resolved partners is paired with another interaction.

## Main results

* `exists_isResolvedPartner`: an interaction of replicate 1 that corresponds to some interaction of
  a finite replicate 2 has a resolved partner.
* `IsResolvedPartner.unique`: the resolved partner is unique when `f i` takes distinct values.
* `exists_isResolvedCorrespondence`: when replicate 2 is finite, a resolved correspondence exists.

## References

* K. Krismer, Y. Guo and D. K. Gifford, "IDR2D identifies reproducible genomic interactions",
  Nucleic Acids Res. 48 (2020), e31, <https://doi.org/10.1093/nar/gkaa030>: Figure 1C–D and
  Eq. (1).
-/

@[expose] public section

namespace Domains.Biology.Omics.InteractionCorrespondence

/-- A genomic **anchor**: the nonempty closed interval `[start, stop]` of base-pair positions on
the chromosome `chrom`. -/
structure Anchor (Chrom : Type*) where
  /-- The chromosome the anchor lies on. -/
  chrom : Chrom
  /-- The first base-pair position of the anchor. -/
  start : ℤ
  /-- The last base-pair position of the anchor. -/
  stop : ℤ
  /-- The anchor is nonempty. -/
  start_le_stop : start ≤ stop

variable {Chrom : Type*}

/-- Two anchors are **within gap `g`** of each other when they lie on the same chromosome and their
gap `max a.start b.start - min a.stop b.stop - 1` is at most `g`. For disjoint anchors the gap is
the number of base-pair positions strictly between them, `0` for adjacent anchors; for overlapping
anchors it is negative. So `g = -1` says that the anchors overlap, sharing a position, `g = 0` also
admits adjacent anchors, and for `g ≥ -1` this is IDR2D's maximal gap between anchors. -/
def Anchor.WithinGap (g : ℤ) (a b : Anchor Chrom) : Prop :=
  a.chrom = b.chrom ∧ max a.start b.start - min a.stop b.stop - 1 ≤ g

/-- Two interactions, each given by its two anchors, **correspond** within the gap `g` when their
first anchors are within the gap of each other and so are their second anchors (IDR2D,
Figure 1C). -/
def Corresponds (g : ℤ) (I J : Anchor Chrom × Anchor Chrom) : Prop :=
  I.1.WithinGap g J.1 ∧ I.2.WithinGap g J.2

variable {ι₁ ι₂ : Type*}

/-- **Ambiguity resolution** (IDR2D, Eq. (1)). The interaction `j` of replicate 2 is the resolved
partner of the interaction `i` of replicate 1 when it corresponds to `i` within the gap `g` and its
ambiguity-resolution value `f i j` is minimal among the interactions of replicate 2 that
correspond to `i`:

  `j ∈ argmin_{j' ∈ O(i)} f i j'`, where `O(i) = {j' | Corresponds g (x₁ i) (x₂ j')}`.

Here `x₁` and `x₂` give the anchors of the interactions of the two replicates. The source's three
choices of `f` are the genomic distance between the anchor midpoints, the additive inverse of the
relative anchor overlap, and the sum of the ranks of the two interactions. -/
def IsResolvedPartner (g : ℤ) (x₁ : ι₁ → Anchor Chrom × Anchor Chrom)
    (x₂ : ι₂ → Anchor Chrom × Anchor Chrom) (f : ι₁ → ι₂ → ℝ) (i : ι₁) (j : ι₂) : Prop :=
  Corresponds g (x₁ i) (x₂ j) ∧ ∀ j', Corresponds g (x₁ i) (x₂ j') → f i j ≤ f i j'

/-- A **resolved correspondence** between the interactions of two replicates (IDR2D, Figure 1C–D
and Eq. (1)): a set `P` of pairs `(i, j)` such that

* each `j` is a resolved partner of its `i` (`IsResolvedPartner`);
* `P` is one-to-one: no interaction of either replicate is in two pairs;
* every interaction `i` of replicate 1 that corresponds to some interaction of replicate 2 is in a
  pair, unless one of its resolved partners is paired with another interaction of replicate 1, as
  happens when two interactions of replicate 1 compete for the same partner.

The paired scores of its pairs enter the copula mixture model. -/
def IsResolvedCorrespondence (g : ℤ) (x₁ : ι₁ → Anchor Chrom × Anchor Chrom)
    (x₂ : ι₂ → Anchor Chrom × Anchor Chrom) (f : ι₁ → ι₂ → ℝ) (P : Set (ι₁ × ι₂)) : Prop :=
  (∀ p ∈ P, IsResolvedPartner g x₁ x₂ f p.1 p.2) ∧
    (∀ p ∈ P, ∀ q ∈ P, (p.1 = q.1 ↔ p.2 = q.2)) ∧
    ∀ i, (∃ j, Corresponds g (x₁ i) (x₂ j)) →
      (∃ j, (i, j) ∈ P) ∨ ∃ j, IsResolvedPartner g x₁ x₂ f i j ∧ ∃ i', (i', j) ∈ P

/-- An interaction of replicate 1 that corresponds to some interaction of a finite replicate 2 has
a resolved partner. -/
theorem exists_isResolvedPartner [Finite ι₂] {g : ℤ} {x₁ : ι₁ → Anchor Chrom × Anchor Chrom}
    {x₂ : ι₂ → Anchor Chrom × Anchor Chrom} (f : ι₁ → ι₂ → ℝ) {i : ι₁}
    (h : ∃ j, Corresponds g (x₁ i) (x₂ j)) : ∃ j, IsResolvedPartner g x₁ x₂ f i j := by
  obtain ⟨j, hjO, hj⟩ := Set.exists_min_image {j | Corresponds g (x₁ i) (x₂ j)} (f i)
    (Set.toFinite _) h
  exact ⟨j, hjO, fun j' hj' => hj j' hj'⟩

/-- When the ambiguity-resolution values `f i j` of the interactions of replicate 2 are distinct,
an interaction of replicate 1 has at most one resolved partner. -/
theorem IsResolvedPartner.unique {g : ℤ} {x₁ : ι₁ → Anchor Chrom × Anchor Chrom}
    {x₂ : ι₂ → Anchor Chrom × Anchor Chrom} {f : ι₁ → ι₂ → ℝ} {i : ι₁} {j j' : ι₂}
    (hf : Function.Injective (f i)) (hj : IsResolvedPartner g x₁ x₂ f i j)
    (hj' : IsResolvedPartner g x₁ x₂ f i j') : j = j' :=
  hf (le_antisymm (hj.2 j' hj'.1) (hj'.2 j hj.1))

/-- When replicate 2 is finite, a resolved correspondence exists: give each interaction of
replicate 1 that has a corresponding interaction one of its resolved partners, and keep, for each
interaction of replicate 2 chosen in this way, one of the interactions of replicate 1 that chose
it. -/
theorem exists_isResolvedCorrespondence [Finite ι₂] (g : ℤ)
    (x₁ : ι₁ → Anchor Chrom × Anchor Chrom) (x₂ : ι₂ → Anchor Chrom × Anchor Chrom)
    (f : ι₁ → ι₂ → ℝ) : ∃ P, IsResolvedCorrespondence g x₁ x₂ f P := by
  classical
  rcases isEmpty_or_nonempty ι₂ with h₂ | h₂
  · exact ⟨∅, by simp, by simp, fun _ ⟨j, _⟩ => isEmptyElim j⟩
  rcases isEmpty_or_nonempty ι₁ with h₁ | h₁
  · exact ⟨∅, by simp, by simp, fun i => isEmptyElim i⟩
  let M : Set ι₁ := {i | ∃ j, Corresponds g (x₁ i) (x₂ j)}
  have hp : ∀ i ∈ M, ∃ j, IsResolvedPartner g x₁ x₂ f i j := fun i hi =>
    exists_isResolvedPartner f hi
  choose! p hp using hp
  have hc : ∀ j, (∃ i ∈ M, p i = j) → ∃ i ∈ M, p i = j := fun _ h => h
  choose! c hcM hcp using hc
  refine ⟨{q | q.1 ∈ M ∧ p q.1 = q.2 ∧ c q.2 = q.1}, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨hi, hpj, -⟩
    dsimp only at hi hpj ⊢
    rw [← hpj]
    exact hp i hi
  · rintro ⟨i, j⟩ ⟨-, hpj, hci⟩ ⟨i', j'⟩ ⟨-, hpj', hci'⟩
    dsimp only at hpj hci hpj' hci' ⊢
    constructor
    · rintro rfl
      rw [← hpj, ← hpj']
    · rintro rfl
      rw [← hci, ← hci']
  · intro i hi
    by_cases h : c (p i) = i
    · exact Or.inl ⟨p i, hi, rfl, h⟩
    · exact Or.inr ⟨p i, hp i hi, c (p i), hcM (p i) ⟨i, hi, rfl⟩, hcp (p i) ⟨i, hi, rfl⟩, rfl⟩

end Domains.Biology.Omics.InteractionCorrespondence
