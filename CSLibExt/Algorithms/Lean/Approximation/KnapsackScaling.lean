/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack
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

The rounding step of the knapsack FPTAS: for a scaling factor `K ≥ 1`, each
profit is rounded down to `p i / K` (natural-number division, i.e.
`⌊p i / K⌋`). Since `K * (p i / K) ≤ p i < K * (p i / K) + K`, rounding loses
less than `K` per item, hence at most `n * K` on any set of items. So every
feasible set `S` that is optimal for the rounded profits satisfies the additive
bound `optVal w p W ≤ ∑ i ∈ S, p i + n * K`, whose constant is `n * K` for the
number `n` of items (`optVal_le_add_of_scaledOpt`; the proof only uses that no
feasible set has a larger rounded profit than `S`). This holds for whichever
rounded-optimal set an algorithm returns, also when rounding creates ties;
`knapsack_scaling_loss` adds that such a set exists.

`totalValue_le_add_of_scaledOpt` states the bound for the item lists of the
verified dynamic program in `CSLibExt.Algorithms.Lean.DynamicProgramming.Knapsack`,
with its `Feasible` and `totalValue`.

The FPTAS first discards the items heavier than `W` and chooses `K = ε P / n`
for the largest remaining profit `P`. That item alone is feasible, so
`P ≤ optVal w p W` and the additive loss `n * K = ε P` is at most
`ε * optVal w p W`, a factor `1 - ε`. The discarding step, the choice of `K`
(which needs a real-valued `K`), and running the dynamic program on the rounded
instance are not formalized here.

## References

* V. V. Vazirani, *Approximation Algorithms*, Springer, 2001, Chapter 8
  (Knapsack), Section 8.2: the FPTAS for knapsack, which rounds profits down
  to `⌊profit / K⌋` and bounds the rounding loss by `n K`.
* D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*, Cambridge University Press, 2011, Section 3.1 (The knapsack
  problem).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM.Knapsack

/-- Knapsack value: items are indexed by `Fin n`, with weights
`w` and profits `p`; `optVal w p W` is the maximum total profit
over subsets whose total weight is at most `W`. -/
noncomputable def optVal {n : ℕ} (w p : Fin n → ℕ) (W : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun S => ∑ i ∈ S, w i ≤ W)).sup
    (fun S => ∑ i ∈ S, p i)

/-- The profit of every feasible set is at most `optVal`. -/
theorem le_optVal {n : ℕ} (w p : Fin n → ℕ) (W : ℕ) {T : Finset (Fin n)}
    (hT : (∑ i ∈ T, w i) ≤ W) : (∑ i ∈ T, p i) ≤ optVal w p W :=
  Finset.le_sup (f := fun S => ∑ i ∈ S, p i)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ T), hT⟩)

/-- Profit scaling loses at most `n * K`: if no feasible set has a larger
rounded profit (`p i / K`, natural-number division, `K ≥ 1`) than `S`, as for a
feasible set `S` that is optimal for the rounded profits, then the true optimum
exceeds the true profit of `S` by at most `n * K`. The bound does not need `S`
itself to be feasible. -/
theorem optVal_le_add_of_scaledOpt {n : ℕ} (w p : Fin n → ℕ) (W K : ℕ)
    (hK : 0 < K) {S : Finset (Fin n)}
    (hSmax : ∀ T : Finset (Fin n), (∑ i ∈ T, w i) ≤ W →
      ∑ i ∈ T, (p i / K) ≤ ∑ i ∈ S, (p i / K)) :
    optVal w p W ≤ (∑ i ∈ S, p i) + n * K := by
  have hpt : ∀ i : Fin n, p i ≤ K * (p i / K) + K := by
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
  refine Finset.sup_le ?_
  intro T hT
  have hTw : (∑ i ∈ T, w i) ≤ W := (Finset.mem_filter.mp hT).2
  calc (∑ i ∈ T, p i) ≤ K * (∑ i ∈ T, p i / K) + T.card * K := hsum T
    _ ≤ K * (∑ i ∈ S, p i / K) + n * K :=
        add_le_add (mul_le_mul_right (hSmax T hTw) K) (hcard T)
    _ ≤ (∑ i ∈ S, p i) + n * K := add_le_add hKS le_rfl

/-- Some feasible set is optimal for the rounded profits `p i / K`
(natural-number division, `K ≥ 1`), and by `optVal_le_add_of_scaledOpt` every
such set is within `n * K` of the true optimum. -/
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
  have hSmax : ∀ T : Finset (Fin n), (∑ i ∈ T, w i) ≤ W →
      (∑ i ∈ T, p i / K) ≤ ∑ i ∈ S, p i / K := by
    intro T hTw
    have hmem' : (fun S => ∑ i ∈ S, p i / K) T
        ∈ 𝒮.image fun S => ∑ i ∈ S, p i / K :=
      Finset.mem_image.mpr ⟨T, (hmem T).mpr hTw, rfl⟩
    have hle : (∑ i ∈ T, p i / K)
        ≤ (𝒮.image fun S => ∑ i ∈ S, p i / K).max' himg :=
      Finset.le_max' _ _ hmem'
    rw [← hgS] at hle
    exact hle
  have hSw : (∑ i ∈ S, w i) ≤ W := (hmem S).mp hSmem
  exact ⟨S, hSw, hSmax, optVal_le_add_of_scaledOpt w p W K hK hSmax⟩

/-- The scaling bound for the item lists of the verified dynamic program: if
no feasible set has a larger value rounded down to `value / K` (`K ≥ 1`) than
`S`, as for a feasible set that is optimal for the rounded values, then every
feasible `T` has true value at most the true value of `S` plus
`items.length * K`. -/
theorem totalValue_le_add_of_scaledOpt (items : List Item) (capacity K : ℕ)
    (hK : 0 < K) {S : Finset (Fin items.length)}
    (hSmax : ∀ T : Finset (Fin items.length), Feasible items capacity T →
      ∑ i ∈ T, (items.get i).value / K ≤ ∑ i ∈ S, (items.get i).value / K)
    {T : Finset (Fin items.length)} (hT : Feasible items capacity T) :
    totalValue items T ≤ totalValue items S + items.length * K :=
  (le_optVal (fun i => (items.get i).weight) (fun i => (items.get i).value) capacity
    hT).trans
    (optVal_le_add_of_scaledOpt (fun i => (items.get i).weight)
      (fun i => (items.get i).value) capacity K hK hSmax)

end Cslib.Algorithms.Lean.TimeM.Knapsack
