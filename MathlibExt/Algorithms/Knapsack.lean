/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Profit scaling for 0/1 knapsack

Items are indexed by `Fin n`, with natural weights `w`, profits `p` and a
capacity `W`; `optVal w p W` is the largest total profit of a set of items of
total weight at most `W`.

`knapsack_scaling_loss` is the rounding step of the knapsack FPTAS. For a
scaling factor `K ≥ 1`, each profit is rounded down to `p i / K`
(natural-number division, i.e. `⌊p i / K⌋`), and `S` is a feasible set that is
optimal for the rounded profits. Since `K * (p i / K) ≤ p i < K * (p i / K) + K`,
rounding loses less than `K` per item, hence at most `n * K` on any set of
items; the theorem states the additive bound
`optVal w p W ≤ ∑ i ∈ S, p i + n * K`, whose constant is `n * K` for the number
`n` of items. The FPTAS chooses `K = ε P / n` for the largest profit `P` to
turn this into a factor `1 - ε`; that choice (which needs a real-valued `K`)
and the dynamic program solving the rounded instance are not formalized here.

## References

* V. V. Vazirani, *Approximation Algorithms*, Springer, 2001, Chapter 8
  (Knapsack), Section 8.2: the FPTAS for knapsack, which rounds profits down
  to `⌊profit / K⌋` and bounds the rounding loss by `n K`.
* D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*, Cambridge University Press, 2011, Section 3.1 (The knapsack
  problem).
-/

@[expose] public section

/-- Knapsack value: items are indexed by `Fin n`, with weights
`w` and profits `p`; `optVal w p W` is the maximum total profit
over subsets whose total weight is at most `W`. -/
noncomputable def optVal {n : ℕ} (w p : Fin n → ℕ) (W : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun S => ∑ i ∈ S, w i ≤ W)).sup
    (fun S => ∑ i ∈ S, p i)

/-- Profit scaling loses at most `n * K`: if every scaled profit
`p i / K` (integer division, `K ≥ 1`) is used, then for the true
profits, any feasible set's profit is at most the profit of a
scaled-optimal feasible set plus `n * K`. Equivalently: there is
a feasible set `S` with `∑ p ≥ optVal w p W - n * K` that is
optimal for the scaled profits. The pinned form: some feasible
set is scaled-optimal and within `n * K` of the true optimum. -/
theorem knapsack_scaling_loss {n : ℕ} (w p : Fin n → ℕ) (W K : ℕ)
    (hK : 0 < K) :
    ∃ S : Finset (Fin n), (∑ i ∈ S, w i) ≤ W ∧
      (∀ T : Finset (Fin n), (∑ i ∈ T, w i) ≤ W →
        ∑ i ∈ T, (p i / K) ≤ ∑ i ∈ S, (p i / K)) ∧
      optVal w p W ≤ (∑ i ∈ S, p i) + n * K := by
  set 𝒮 : Finset (Finset (Fin n)) :=
    Finset.univ.powerset.filter (fun S => ∑ i ∈ S, w i ≤ W) with h𝒮
  have hmem : ∀ T : Finset (Fin n), T ∈ 𝒮 ↔ (∑ i ∈ T, w i) ≤ W := by
    intro T
    simp only [h𝒮, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
  have hne : 𝒮.Nonempty := ⟨∅, (hmem ∅).mpr (by simp)⟩
  have himg : (𝒮.image fun S => ∑ i ∈ S, p i / K).Nonempty :=
    hne.image _
  have hMmem := Finset.max'_mem _ himg
  obtain ⟨S, hSmem, hgS⟩ := Finset.mem_image.mp hMmem
  have hSmax : ∀ T ∈ 𝒮, (∑ i ∈ T, p i / K) ≤ ∑ i ∈ S, p i / K := by
    intro T hT
    have hmem' : (fun S => ∑ i ∈ S, p i / K) T
        ∈ 𝒮.image fun S => ∑ i ∈ S, p i / K :=
      Finset.mem_image.mpr ⟨T, hT, rfl⟩
    have hle : (∑ i ∈ T, p i / K)
        ≤ (𝒮.image fun S => ∑ i ∈ S, p i / K).max' himg :=
      Finset.le_max' _ _ hmem'
    rw [← hgS] at hle
    exact hle
  have hSw : (∑ i ∈ S, w i) ≤ W := (hmem S).mp hSmem
  refine ⟨S, hSw, ?_, ?_⟩
  · intro T hTw
    exact hSmax T ((hmem T).mpr hTw)
  · have hpt : ∀ i : Fin n, p i ≤ K * (p i / K) + K := by
      intro i
      have h1 := Nat.div_add_mod (p i) K
      have h2 := Nat.mod_lt (p i) hK
      omega
    have hsplit : ∀ T : Finset (Fin n),
        (∑ i ∈ T, (K * (p i / K) + K))
          = K * (∑ i ∈ T, p i / K) + T.card * K := by
      intro T
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      simp [Finset.sum_const]
    have hsum : ∀ T : Finset (Fin n),
        (∑ i ∈ T, p i) ≤ K * (∑ i ∈ T, p i / K) + T.card * K := by
      intro T
      calc (∑ i ∈ T, p i) ≤ ∑ i ∈ T, (K * (p i / K) + K) :=
              Finset.sum_le_sum (fun i _ => hpt i)
        _ = K * (∑ i ∈ T, p i / K) + T.card * K := hsplit T
    have hcard : ∀ T : Finset (Fin n), T.card * K ≤ n * K := by
      intro T
      have h1 := Finset.card_le_univ T
      rw [Fintype.card_fin] at h1
      exact mul_le_mul_left h1 K
    have hKS : K * (∑ i ∈ S, p i / K) ≤ ∑ i ∈ S, p i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => Nat.mul_div_le (p i) K)
    have hopt : optVal w p W = 𝒮.sup (fun S => ∑ i ∈ S, p i) := rfl
    rw [hopt]
    refine Finset.sup_le ?_
    intro T hT
    calc (∑ i ∈ T, p i) ≤ K * (∑ i ∈ T, p i / K) + T.card * K := hsum T
      _ ≤ K * (∑ i ∈ S, p i / K) + n * K :=
          add_le_add (mul_le_mul_right (hSmax T hT) K) (hcard T)
      _ ≤ (∑ i ∈ S, p i) + n * K := add_le_add hKS le_rfl
