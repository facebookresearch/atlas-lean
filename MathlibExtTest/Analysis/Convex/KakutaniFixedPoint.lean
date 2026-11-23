/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KakutaniFixedPoint

/-! The single-valued correspondence `x ↦ {1 - x}` on `[0, 1]` has a fixed point by Kakutani's
theorem. Convex values are needed: the best-response-style correspondence jumping from `{1}` to
`{0}` at `1/2`, with value `{0, 1}` there, has a closed graph and nonempty values but no fixed
point. -/

@[expose] public section

open MathlibExt.Analysis.Convex.KakutaniFixedPoint

namespace MathlibExtTest.Analysis.Convex.KakutaniFixedPoint

-- Example 1: singleton correspondence x ↦ {1 - x} has a fixed point via Kakutani
example (hB : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc 0 1) →
    Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc (0 : ℝ) 1, g x = x) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, x ∈ ({1 - x} : Set ℝ) := by
  classical
  have hKc : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hKcv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  have hΦne : ∀ x ∈ Set.Icc (0 : ℝ) 1, (({1 - x} : Set ℝ)).Nonempty := by
    intro x _
    exact ⟨1 - x, rfl⟩
  have hΦcv : ∀ x ∈ Set.Icc (0 : ℝ) 1, Convex ℝ (({1 - x} : Set ℝ)) := by
    intro x _
    exact convex_singleton (1 - x)
  have hΦK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ({1 - x} : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [hy]
    have hxb := Set.mem_Icc.mp hx
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hΦgraph : IsClosed {q : ℝ × ℝ | q.1 ∈ Set.Icc 0 1 ∧ q.2 ∈ ({1 - q.1} : Set ℝ)} := by
    have h_eq : {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ ({1 - q.1} : Set ℝ)} =
        {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1} ∩ {q : ℝ × ℝ | q.2 = 1 - q.1} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
    rw [h_eq]
    apply IsClosed.inter
    · exact isClosed_Icc.preimage continuous_fst
    · exact isClosed_eq continuous_snd (continuous_const.sub continuous_fst)
  exact exists_mem_self_of_brouwer hKc hKcv hKne hB hΦne hΦcv hΦK hΦgraph

-- Example 2: convex values are needed (counterexample with nonconvex value at 1/2)
example : IsClosed {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ (if q.1 < 1 / 2 then ({1} : Set ℝ) else if 1 / 2 < q.1 then ({0} : Set ℝ)
        else ({0, 1} : Set ℝ))} ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      (if x < 1 / 2 then ({1} : Set ℝ) else if 1 / 2 < x then ({0} : Set ℝ)
        else ({0, 1} : Set ℝ)).Nonempty) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      (if x < 1 / 2 then ({1} : Set ℝ) else if 1 / 2 < x then ({0} : Set ℝ)
        else ({0, 1} : Set ℝ)) ⊆
        Set.Icc (0 : ℝ) 1) ∧
    ¬ ∃ x ∈ Set.Icc (0 : ℝ) 1,
      x ∈ (if x < 1 / 2 then ({1} : Set ℝ) else if 1 / 2 < x then ({0} : Set ℝ)
        else ({0, 1} : Set ℝ)) := by
  classical
  constructor
  · -- closed graph: union of [0,1/2]×{1} and [1/2,1]×{0}
    have h_eq : {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
          q.2 ∈ (if q.1 < 1 / 2 then ({1} : Set ℝ) else if 1 / 2 < q.1 then ({0} : Set ℝ)
            else ({0, 1} : Set ℝ))} =
        (Set.Icc (0 : ℝ) (1 / 2) ×ˢ ({1} : Set ℝ)) ∪ (Set.Icc (1 / 2 : ℝ) 1 ×ˢ ({0} : Set ℝ)) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod, Set.mem_Icc,
        Set.mem_singleton_iff]
      constructor
      · intro h
        obtain ⟨⟨hx0, hx1⟩, hmem⟩ := h
        split_ifs at hmem with h1 h2
        · left
          exact ⟨⟨hx0, le_of_lt h1⟩, hmem⟩
        · right
          exact ⟨⟨le_of_lt h2, hx1⟩, hmem⟩
        · have hx_eq : q.1 = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          have hmem' : q.2 = 0 ∨ q.2 = 1 := by simpa using hmem
          rcases hmem' with h0 | h1'
          · right
            have h1_le : (1 / 2 : ℝ) ≤ q.1 := by rw [hx_eq]
            have hle1 : q.1 ≤ 1 := by rw [hx_eq]; norm_num
            exact ⟨⟨h1_le, hle1⟩, h0⟩
          · left
            have h0_le : (0 : ℝ) ≤ q.1 := by rw [hx_eq]; norm_num
            have hle_half : q.1 ≤ 1 / 2 := by rw [hx_eq]
            exact ⟨⟨h0_le, hle_half⟩, h1'⟩
      · intro h
        rcases h with ⟨⟨hx0, hx_half⟩, hy1⟩ | ⟨⟨hx_half, hx1⟩, hy0⟩
        · have hy1_eq : q.2 = 1 := hy1
          rw [hy1_eq]
          have hx1' : q.1 ≤ 1 := le_trans hx_half (by norm_num)
          refine ⟨⟨hx0, hx1'⟩, ?_⟩
          split_ifs with h1 h2
          · rfl
          · have hlt : (1 / 2 : ℝ) < 1 / 2 := lt_of_lt_of_le h2 hx_half
            exact absurd hlt (lt_irrefl _)
          · simp
        · have hy0_eq : q.2 = 0 := hy0
          rw [hy0_eq]
          have hx0' : (0 : ℝ) ≤ q.1 := le_trans (by norm_num) hx_half
          refine ⟨⟨hx0', hx1⟩, ?_⟩
          split_ifs with h1 h2
          · have hlt : (1 / 2 : ℝ) < 1 / 2 := lt_of_le_of_lt hx_half h1
            exact absurd hlt (lt_irrefl _)
          · rfl
          · simp
    rw [h_eq]
    exact IsClosed.union (isClosed_Icc.prod isClosed_singleton)
      (isClosed_Icc.prod isClosed_singleton)
  · constructor
    · intro x _
      split_ifs with h1 h2
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, by simp⟩
    · constructor
      · intro x _ y hy
        have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨le_refl _, zero_le_one⟩
        have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨zero_le_one, le_refl _⟩
        split_ifs at hy with h1 h2
        · rw [hy]
          exact h1mem
        · rw [hy]
          exact h0
        · have hy' : y = 0 ∨ y = 1 := by simpa using hy
          rcases hy' with rfl | rfl
          · exact h0
          · exact h1mem
      · intro hex
        obtain ⟨x, hxK, hxmem⟩ := hex
        split_ifs at hxmem with h1 h2
        · rw [hxmem] at h1
          norm_num at h1
        · rw [hxmem] at h2
          norm_num at h2
        · have hx_eq : x = 1 / 2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          rw [hx_eq] at hxmem
          have hx' : (1 / 2 : ℝ) = 0 ∨ (1 / 2 : ℝ) = 1 := by simpa using hxmem
          rcases hx' with h | h
          · norm_num at h
          · norm_num at h

-- Unconditional Kakutani: `x ↦ {1 - x}` on `[0, 1]` via `exists_mem_self`.
example : ∃ x ∈ Set.Icc (0 : ℝ) 1, x ∈ ({1 - x} : Set ℝ) := by
  have hKne : (Set.Icc (0 : ℝ) 1).Nonempty :=
    Set.nonempty_Icc.mpr (by norm_num)
  have hΦne : ∀ x ∈ Set.Icc (0 : ℝ) 1, (({1 - x} : Set ℝ)).Nonempty :=
    fun x _ => Set.singleton_nonempty (1 - x)
  have hΦcv : ∀ x ∈ Set.Icc (0 : ℝ) 1, Convex ℝ (({1 - x} : Set ℝ)) :=
    fun x _ => convex_singleton (1 - x)
  have hΦK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ({1 - x} : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rw [Set.singleton_subset_iff]
    obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hΦgraph :
      IsClosed {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ ({1 - q.1} : Set ℝ)} := by
    have hf : Continuous (Prod.fst : ℝ × ℝ → ℝ) := continuous_fst
    have h1 : IsClosed ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) :=
      IsClosed.preimage hf isClosed_Icc
    have hcont : Continuous (fun q : ℝ × ℝ => 1 - q.1) := by fun_prop
    have h2 : IsClosed {q : ℝ × ℝ | q.2 = 1 - q.1} :=
      isClosed_eq continuous_snd hcont
    have hset : {q : ℝ × ℝ | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ ({1 - q.1} : Set ℝ)}
        = ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1)
          ∩ {q : ℝ × ℝ | q.2 = 1 - q.1} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_singleton_iff]
    rw [hset]
    exact h1.inter h2
  exact exists_mem_self isCompact_Icc (convex_Icc (0 : ℝ) 1) hKne hΦne hΦcv hΦK hΦgraph

end MathlibExtTest.Analysis.Convex.KakutaniFixedPoint
