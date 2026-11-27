/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.Hamming
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.SingletonBound

/-- **Singleton bound.** Let $\alpha$ be a nonempty finite alphabet with $q$ letters, and let $n$
and $d$ be natural numbers with $1 \le d \le n$. If $C$ is a set of words of length $n$ over
$\alpha$ in which any two distinct words are at Hamming distance at least $d$, then $C$ has at
most $q^{n - d + 1}$ elements.

The proof punctures the code to its first $n - d + 1$ coordinates: two codewords agreeing on all
retained coordinates can differ in at most the $d - 1$ deleted coordinates, contradicting the
minimum-distance hypothesis, so puncturing is injective on the code and the bound follows by
counting the punctured words.

Source: R. C. Singleton, "Maximum distance q-nary codes",
IEEE Transactions on Information Theory 10(2) (1964), 116–118,
DOI 10.1109/TIT.1964.1053661. -/
public theorem singleton_bound
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n d : ℕ}
    (C : Finset (Fin n → α))
    (hd1 : 1 ≤ d)
    (hd2 : d ≤ n)
    (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
      d ≤ hammingDist c₁ c₂) :
    C.card ≤ (Fintype.card α) ^ (n - d + 1) := by
  have hle : n - d + 1 ≤ n := by omega
  -- Retain the first `n - d + 1` coordinates.
  let emb : Fin (n - d + 1) → Fin n :=
    fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hle⟩
  have hemb : Function.Injective emb := by
    intro a b h
    simp only [emb, Fin.mk.injEq] at h
    exact Fin.ext h
  -- Puncturing map: restrict a word to the retained coordinates.
  let punch : (Fin n → α) → (Fin (n - d + 1) → α) := fun c i => c (emb i)
  -- Puncturing is injective on the code.
  have hinj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, punch c₁ = punch c₂ → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ hagree
    by_contra hne
    have hagree : ∀ i, c₁ (emb i) = c₂ (emb i) := fun i => congrFun hagree i
    -- Words agreeing on the retained coordinates differ only outside them.
    have hsub : Finset.univ.filter (fun j => c₁ j ≠ c₂ j) ⊆
        Finset.univ \ Finset.image emb Finset.univ := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ j, ?_⟩
      rw [Finset.mem_image]
      rintro ⟨i, -, rfl⟩
      exact hj.2 (hagree i)
    -- There are exactly `d - 1` deleted coordinates.
    have hcompl : (Finset.univ \ Finset.image emb Finset.univ).card = d - 1 := by
      have h1 : (Finset.univ : Finset (Fin n)).card = n := by
        simp [Finset.card_univ, Fintype.card_fin]
      have h2 : (Finset.image emb Finset.univ).card = n - d + 1 := by
        rw [Finset.card_image_of_injective _ hemb]
        simp [Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), h1, h2]
      omega
    have hdist : hammingDist c₁ c₂ ≤ d - 1 :=
      hcompl ▸ Finset.card_le_card hsub
    have hge : d ≤ hammingDist c₁ c₂ := hDist c₁ hc₁ c₂ hc₂ hne
    omega
  -- Hence the code embeds in the type of punctured words; count them.
  let g : C ↪ (Fin (n - d + 1) → α) :=
    ⟨fun c => punch c.val,
      fun a b h => Subtype.ext (hinj _ a.property _ b.property h)⟩
  have hcard : C.card ≤ Fintype.card (Fin (n - d + 1) → α) := by
    have h := Fintype.card_le_of_embedding g
    rwa [Fintype.card_coe] at h
  have hcount : Fintype.card (Fin (n - d + 1) → α) =
      (Fintype.card α) ^ (n - d + 1) := by
    simp [Fintype.card_pi]
  rwa [hcount] at hcard

end MathlibExt.Combinatorics.Coding.SingletonBound
