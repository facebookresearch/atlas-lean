/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Div
public import MathlibExt.Combinatorics.Additive.WeightedDavenport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic

/-!
# Long weighted zero-sum free sequences in groups of rank two

The sequence consists of two blocks of coordinate generators. In each block, the sum of
the selected weights is strictly below the order of the generator.
-/

namespace MetaMathlibExt

namespace exists_weightedZeroSumFree_zmod_prod

private theorem weights_eq_zero {l α n : ℕ} (w : Fin l → ℕ) (hw : ∀ i, w i ≤ α)
    (hlt : l * α < n) (hz : ∑ i, (w i : ZMod n) = 0) : ∀ i, w i = 0 := by
  rw [← Nat.cast_sum, ZMod.natCast_eq_zero_iff] at hz
  have hsum : ∑ i, w i < n := calc
    ∑ i, w i ≤ ∑ _ : Fin l, α := Finset.sum_le_sum fun i _ => hw i
    _ = l * α := by simp
    _ < n := hlt
  apply congrFun
  exact (Fintype.sum_eq_zero_iff_of_nonneg (fun i => Nat.zero_le (w i))).mp
    (Nat.eq_zero_of_dvd_of_lt hz hsum)

end exists_weightedZeroSumFree_zmod_prod

/-- **Long weighted zero-sum free sequences in groups of rank two.** Let $m, n \ge 2$ be natural
numbers with $m \mid n$, let $k \ge 1$ and put $\alpha = \lceil n/(m-1) \rceil - 1$. Then there is
a sequence $s$ over $\mathbb{Z}/n\mathbb{Z} \oplus \mathbb{Z}/kn\mathbb{Z}$ of length
$m + \lceil kn/\alpha \rceil - 2$ that is $\{1, \dots, \alpha\}$-weighted zero-sum free: for every
non-empty set $I$ of positions and all weights $a_i \in \{1, \dots, \alpha\}$, the weighted sum
$\sum_{i \in I} a_i s_i$ is non-zero.

In particular the $\{1, \dots, \alpha\}$-weighted Davenport constant of
$\mathbb{Z}/n\mathbb{Z} \oplus \mathbb{Z}/kn\mathbb{Z}$ is at least
$m + \lceil kn/\alpha \rceil - 1$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Lemma 2 (`integers-2026-A89-lem-2`). -/
public theorem exists_weightedZeroSumFree_zmod_prod (m n k : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (hdvd : m ∣ n) (hk : 1 ≤ k) :
    ∃ s : List (ZMod n × ZMod (k * n)),
      s.length = m + (k * n) ⌈/⌉ (n ⌈/⌉ (m - 1) - 1) - 2 ∧
        IsWeightedZeroSumFree (Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) s := by
  let p := m - 1
  let α := n ⌈/⌉ p - 1
  let q := (k * n) ⌈/⌉ α - 1
  have hp : 0 < p := by dsimp [p]; omega
  have hpn : p < n := by
    have := Nat.le_of_dvd (by omega : 0 < n) hdvd
    dsimp [p]
    omega
  have hceil : 1 < n ⌈/⌉ p := (gc_mul_ceilDiv hp).lt_iff_lt.mpr (by simpa using hpn)
  have hα : 0 < α := by dsimp [α]; omega
  have hkn : 0 < k * n := Nat.mul_pos hk (by omega)
  have hceil' : 0 < (k * n) ⌈/⌉ α := (gc_mul_ceilDiv hα).lt_iff_lt.mpr (by simpa using hkn)
  have hleft : p * α < n := (gc_mul_ceilDiv hp).lt_iff_lt.mp (by dsimp [α]; omega)
  have hright : q * α < k * n := by
    rw [Nat.mul_comm]
    exact (gc_mul_ceilDiv hα).lt_iff_lt.mp (by dsimp [q]; omega)
  let e : Fin (p + q) → ZMod n × ZMod (k * n) :=
    Fin.append (fun _ : Fin p => (1, 0)) (fun _ : Fin q => (0, 1))
  refine ⟨List.ofFn e, ?_, ?_⟩
  · rw [List.length_ofFn]
    change p + q = m + (k * n) ⌈/⌉ α - 2
    dsimp [p, q]
    omega
  unfold IsWeightedZeroSumFree
  simp only [List.get_ofFn]
  -- Index the list by the sum of the two block lengths.
  generalize_proofs hlen
  generalize (List.ofFn e).length = L at hlen ⊢
  subst L
  intro I hI a ha hsum
  -- Extend the selected weights by zero so that the full sum splits at the block boundary.
  let w (i : Fin (p + q)) := if i ∈ I then a i else 0
  have hw (i) : w i ≤ α := by
    by_cases hi : i ∈ I
    · simpa [w, hi] using (Finset.mem_Icc.mp (ha i hi)).2
    · simp [w, hi]
  have hz : ∑ i, w i • e i = 0 := by
    simpa [w, ite_smul, Finset.sum_ite_mem_eq] using hsum
  rw [Fin.sum_univ_add] at hz
  have hw0 : ∀ i, w i = 0 := Fin.addCases
    (exists_weightedZeroSumFree_zmod_prod.weights_eq_zero _ (fun i => hw (i.castAdd q)) hleft
      (by simpa [e, Prod.fst_sum, nsmul_eq_mul] using congrArg Prod.fst hz))
    (exists_weightedZeroSumFree_zmod_prod.weights_eq_zero _ (fun i => hw (i.natAdd p)) hright
      (by simpa [e, Prod.snd_sum, nsmul_eq_mul] using congrArg Prod.snd hz))
  obtain ⟨i, hi⟩ := hI
  exact (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp (ha i hi)).1)
    (by simpa [w, hi] using hw0 i)

end MetaMathlibExt
