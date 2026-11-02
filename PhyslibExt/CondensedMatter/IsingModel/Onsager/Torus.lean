/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib

/-!

# The square-lattice torus

The nearest-neighbor graph on `ℤ_L × ℤ_L` for `L > 2`, its degrees and its number of edges.

## i. Overview

For `L > 2` the `L × L` torus graph `onsTorusGraph L` joins each site of `ℤ_L × ℤ_L` to its four
nearest neighbors. It is the circulant graph of `ℤ_L × ℤ_L` with jumps `(1, 0)` and `(0, 1)`, it is
`4`-regular, and it has `L²` vertices and `2 L²` edges. The condition `L > 2` keeps the four
neighbors distinct; for `L ≤ 2` the periodic square lattice has multiple edges, which a simple graph
cannot represent.

## ii. Key results

- `onsTorusGraph` : the `L × L` torus graph
- `onsTorusGraph_eq_circulantGraph` : it is Mathlib's circulant graph with jumps `(1, 0)` and
  `(0, 1)`
- `onsTorus_degree` : every vertex has degree `4`
- `onsTorus_card_edges` : the torus has `2 L²` edges

## iii. Table of contents

- A. The torus graph
- B. Counting vertices and edges
- C. Comparison with circulant graphs

## iv. References

- None; the material is standard.

-/

@[expose] public section

namespace StatMech.Onsager

/-! ## A. The torus graph -/

/-- Nearest-neighbor adjacency on `ℤ_L × ℤ_L`: the two sites differ by `±1` in exactly one
coordinate. -/
def onsTorusAdj (L : ℕ) (u v : ZMod L × ZMod L) : Prop :=
  (u.1 = v.1 ∧ (u.2 = v.2 + 1 ∨ u.2 = v.2 - 1)) ∨ (u.2 = v.2 ∧ (u.1 = v.1 + 1 ∨ u.1 = v.1 - 1))

/-- Decidability of torus adjacency. -/
instance (L : ℕ) : DecidableRel (onsTorusAdj L) := by
  intro u v; unfold onsTorusAdj; infer_instance

/-- The `L × L` square-lattice torus as a simple graph on `ℤ_L × ℤ_L`, for `L > 2`. -/
def onsTorusGraph (L : ℕ) [Fact (2 < L)] : SimpleGraph (ZMod L × ZMod L) where
  Adj := onsTorusAdj L
  symm := by
    refine ⟨?_⟩
    rintro u v (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
    · exact Or.inl ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inl ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
  loopless := by
    have hne1 : (1 : ZMod L) ≠ 0 := by
      have : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
      exact one_ne_zero
    have hnem1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr hne1
    refine ⟨?_⟩
    rintro v (⟨_, h2 | h2⟩ | ⟨_, h2 | h2⟩)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)

/-- `L ≠ 0` whenever `2 < L`. -/
instance instNeZeroOfFact (L : ℕ) [Fact (2 < L)] : NeZero L :=
  ⟨by have := (Fact.out : 2 < L); omega⟩

/-- Decidable adjacency of the torus graph. -/
instance (L : ℕ) [Fact (2 < L)] : DecidableRel (onsTorusGraph L).Adj :=
  inferInstanceAs (DecidableRel (onsTorusAdj L))

/-! ## B. Counting vertices and edges -/

lemma onsTorus_card_verts (L : ℕ) [NeZero L] :
    Fintype.card (ZMod L × ZMod L) = L ^ 2 := by
  rw [Fintype.card_prod, ZMod.card]; ring

lemma onsTorus_degree (L : ℕ) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    (onsTorusGraph L).degree v = 4 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_one, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L); omega
  have h2 : (2 : ZMod L) ≠ 0 := by
    have : ((2 : ℕ) : ZMod L) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := (Fact.out : 2 < L); omega
    simpa using this
  set A : ZMod L × ZMod L := (v.1, v.2 - 1) with hA_def
  set B : ZMod L × ZMod L := (v.1, v.2 + 1) with hB_def
  set C : ZMod L × ZMod L := (v.1 - 1, v.2) with hC_def
  set D : ZMod L × ZMod L := (v.1 + 1, v.2) with hD_def
  have hAB : A ≠ B := by
    intro h; rw [Prod.ext_iff] at h; exact h2 (by linear_combination -h.2)
  have hAC : A ≠ C := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination h.1)
  have hAD : A ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination -h.1)
  have hBC : B ≠ C := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination h.1)
  have hBD : B ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination -h.1)
  have hCD : C ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h2 (by linear_combination -h.1)
  have hset : (onsTorusGraph L).neighborFinset v = {A, B, C, D} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton, hA_def, hB_def, hC_def, hD_def]
    constructor
    · rintro (⟨g1, g2 | g2⟩ | ⟨g1, g2 | g2⟩)
      · exact Or.inl (Prod.ext_iff.mpr ⟨g1.symm, by linear_combination -g2⟩)
      · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨g1.symm, by linear_combination -g2⟩))
      · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨by linear_combination -g2, g1.symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr ⟨by linear_combination -g2, g1.symm⟩)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl ⟨rfl, Or.inl (by ring)⟩
      · exact Or.inl ⟨rfl, Or.inr (by ring)⟩
      · exact Or.inr ⟨rfl, Or.inl (by ring)⟩
      · exact Or.inr ⟨rfl, Or.inr (by ring)⟩
  change Finset.card ((onsTorusGraph L).neighborFinset v) = 4
  rw [hset]
  rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hAB, hAC, hAD⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hBC, hBD⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hCD),
      Finset.card_singleton]

lemma onsTorus_card_edges (L : ℕ) [Fact (2 < L)] :
    (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 := by
  have hsum := (onsTorusGraph L).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, (onsTorusGraph L).degree v = 4 := onsTorus_degree L
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [onsTorus_card_verts] at hsum
  omega

/-! ## C. Comparison with circulant graphs -/

/-- The torus graph is the circulant graph of `ℤ_L × ℤ_L` with jumps `(1, 0)` and `(0, 1)`. -/
lemma onsTorusGraph_eq_circulantGraph (L : ℕ) [Fact (2 < L)] :
    onsTorusGraph L = SimpleGraph.circulantGraph {((1 : ZMod L), (0 : ZMod L)), (0, 1)} := by
  ext u v
  constructor
  · intro h
    refine ⟨(onsTorusGraph L).ne_of_adj h, ?_⟩
    rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;>
      simp [Prod.ext_iff, h1, h2, sub_eq_iff_eq_add, add_comm]
  · rintro ⟨-, h⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff,
      sub_eq_iff_eq_add, Prod.fst_add, Prod.snd_add, zero_add] at h
    change onsTorusAdj L u v
    unfold onsTorusAdj
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨h2, Or.inl (by rw [h1]; ring)⟩
    · exact Or.inl ⟨h1, Or.inl (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h2.symm, Or.inr (by rw [h1]; ring)⟩
    · exact Or.inl ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩

end StatMech.Onsager
