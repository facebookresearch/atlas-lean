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
two interactions' ranks. The scores of the pairs of the resulting one-to-one correspondence then
enter the copula mixture model of the irreproducible discovery rate
(`Domains.Biology.Omics.IrreproducibleDiscoveryRate`).

## Conventions

* An anchor is a closed interval `[start, stop]` of base-pair positions on a chromosome. Two anchors
  are *within gap `g`* when they lie on the same chromosome and
  `max start₁ start₂ - min stop₁ stop₂ ≤ g`: for `g = 0` this says that they share a position, and
  for `g > 0` that they overlap or that the later one starts at most `g` positions after the
  earlier one ends.
* An interaction is a pair of anchors `(A, B)`. Two interactions *correspond* when their first
  anchors are within the gap of each other, and so are their second anchors.
* The interactions of the two replicates form types `ι₁` and `ι₂`, with anchors `x₁ : ι₁ → _` and
  `x₂ : ι₂ → _`. The ambiguity-resolution value is any `f : ι₁ → ι₂ → ℝ`, as the source lets the
  analyst choose among three; lower values are better.

## Main definitions

* `Anchor`: a closed interval of positions on a chromosome.
* `Anchor.WithinGap g a b`: the anchors `a` and `b` overlap or lie within the gap `g` of each other.
* `Corresponds g I J`: both anchors of the interactions `I` and `J` are within the gap `g`.
* `IsResolvedPartner g x₁ x₂ f i j`: the interaction `j` of replicate 2 corresponds to the
  interaction `i` of replicate 1 and minimizes the ambiguity-resolution value `f i` among those that
  do (Eq. (1)).
* `IsResolvedCorrespondence g x₁ x₂ f P`: `P` is a one-to-one correspondence whose pairs are
  resolved partners.

## Main results

* `exists_isResolvedPartner`: an interaction of replicate 1 that corresponds to some interaction of
  a finite replicate 2 has a resolved partner.
* `IsResolvedPartner.unique`: the resolved partner is unique when `f i` takes distinct values.

## References

* K. Krismer, Y. Guo and D. K. Gifford, "IDR2D identifies reproducible genomic interactions",
  Nucleic Acids Res. 48 (2020), e31, <https://doi.org/10.1093/nar/gkaa030>: Figure 1C–D and
  Eq. (1).
-/

@[expose] public section

namespace Domains.Biology.Omics.InteractionCorrespondence

/-- A genomic **anchor**: the closed interval `[start, stop]` of base-pair positions on the
chromosome `chrom`. -/
structure Anchor (Chrom : Type*) where
  /-- The chromosome the anchor lies on. -/
  chrom : Chrom
  /-- The first base-pair position of the anchor. -/
  start : ℤ
  /-- The last base-pair position of the anchor. -/
  stop : ℤ

variable {Chrom : Type*}

/-- Two anchors are **within gap `g`** of each other when they lie on the same chromosome and
`max a.start b.start - min a.stop b.stop ≤ g`. For `g = 0` this says that the anchors overlap,
sharing a base-pair position; for `g > 0`, that they overlap or that the start of the later one
lies at most `g` positions after the end of the earlier one. -/
def Anchor.WithinGap (g : ℤ) (a b : Anchor Chrom) : Prop :=
  a.chrom = b.chrom ∧ max a.start b.start - min a.stop b.stop ≤ g

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

/-- A **resolved correspondence** between the interactions of two replicates: a set `P` of pairs
`(i, j)` that is one-to-one (no interaction of either replicate is in two pairs) and in which each
`j` is a resolved partner of `i` (`IsResolvedPartner`). The paired scores of its pairs enter the
copula mixture model. -/
def IsResolvedCorrespondence (g : ℤ) (x₁ : ι₁ → Anchor Chrom × Anchor Chrom)
    (x₂ : ι₂ → Anchor Chrom × Anchor Chrom) (f : ι₁ → ι₂ → ℝ) (P : Set (ι₁ × ι₂)) : Prop :=
  (∀ p ∈ P, IsResolvedPartner g x₁ x₂ f p.1 p.2) ∧
    ∀ p ∈ P, ∀ q ∈ P, (p.1 = q.1 ↔ p.2 = q.2)

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

end Domains.Biology.Omics.InteractionCorrespondence
