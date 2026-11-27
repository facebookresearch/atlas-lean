/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingBall
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.HammingSpherePacking

/-- **Hamming bound.** Let $\alpha$ be a finite alphabet with $q \ge 2$ letters, and let $n$ and
$t$ be natural numbers. If $C$ is a set of words of length $n$ over $\alpha$ in which any two
distinct words are at Hamming distance at least $2t + 1$, then

$$|C| \sum_{i=0}^{t} \binom{n}{i} (q - 1)^i \le q^n.$$

The proof packs disjoint radius-$t$ Hamming balls around the codewords into the ambient space:
the distance hypothesis forces the balls apart (any overlap would give a triangle-inequality
contradiction), and each ball contains exactly $\sum_{i=0}^{t} \binom{n}{i} (q - 1)^i$ words.

This is the $q$-ary generalization of Hamming's binary sphere-packing bound. The original paper
assumes binary words and derives the $2^n$ form; the same disjoint-ball counting argument gives
the formula stated here for an arbitrary finite alphabet.

Binary source: R. W. Hamming, "Error Detecting and Error Correcting Codes",
Bell System Technical Journal 29 (1950), 147–160,
DOI 10.1002/j.1538-7305.1950.tb00463.x. -/
public theorem hamming_sphere_packing_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    {n t : ℕ}
    (C : Finset (Fin n → α))
    (hα : 2 ≤ Fintype.card α)
    (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
      2 * t + 1 ≤ hammingDist c₁ c₂) :
    C.card * (∑ i ∈ Finset.range (t + 1),
      n.choose i * (Fintype.card α - 1) ^ i) ≤ (Fintype.card α) ^ n := by
  -- The alphabet-size hypothesis records the conventional nontrivial-alphabet
  -- domain of the q-ary statement; the counting argument itself needs no lower bound on `q`.
  have _ := hα
  -- Radius-`t` balls around distinct codewords are disjoint.
  have hDisj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
      Disjoint (Hamming.ball c₁ t) (Hamming.ball c₂ t) := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [Hamming.mem_ball] at hy1 hy2
    have htri := hammingDist_triangle c₁ y c₂
    rw [hammingDist_comm y c₂] at htri
    have hge := hDist c₁ hc₁ c₂ hc₂ hne
    omega
  have hPair : ((↑C : Set (Fin n → α))).PairwiseDisjoint
      (fun c => Hamming.ball c t) := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Finset.mem_coe] at hc₁ hc₂
    exact hDisj c₁ hc₁ c₂ hc₂ hne
  have hUnion : (C.biUnion fun c => Hamming.ball c t).card =
      ∑ c ∈ C, (Hamming.ball c t).card :=
    Finset.card_biUnion hPair
  -- Every ball has the same volume.
  have hEach : ∀ c ∈ C, (Hamming.ball c t).card =
      ∑ i ∈ Finset.range (t + 1),
        n.choose i * (Fintype.card α - 1) ^ i := by
    intro c _
    rw [Hamming.card_ball]
    simp only [Fintype.card_fin]
  have hSum : ∑ c ∈ C, (Hamming.ball c t).card =
      C.card * (∑ i ∈ Finset.range (t + 1),
        n.choose i * (Fintype.card α - 1) ^ i) := by
    have hcongr : (∑ c ∈ C, (Hamming.ball c t).card)
        = ∑ _x ∈ C, (∑ i ∈ Finset.range (t + 1),
          n.choose i * (Fintype.card α - 1) ^ i) :=
      Finset.sum_congr rfl hEach
    rw [hcongr, Finset.sum_const, smul_eq_mul]
  have hUniv : (Finset.univ : Finset (Fin n → α)).card =
      (Fintype.card α) ^ n := by
    rw [Finset.card_univ]
    simp [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc C.card * (∑ i ∈ Finset.range (t + 1),
        n.choose i * (Fintype.card α - 1) ^ i)
      = ∑ c ∈ C, (Hamming.ball c t).card := hSum.symm
    _ = (C.biUnion fun c => Hamming.ball c t).card := hUnion.symm
    _ ≤ (Finset.univ : Finset (Fin n → α)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card α) ^ n := hUniv

end MathlibExt.Combinatorics.Coding.HammingSpherePacking
