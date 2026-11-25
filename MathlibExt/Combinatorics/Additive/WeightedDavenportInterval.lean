/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Additive.WeightedDavenport
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Initial-interval weights for the weighted Davenport constant

For a divisor `m ≥ 2` of `n ≥ 2`, the weights from `1` to `⌈n/(m-1)⌉ - 1` give
weighted Davenport constant `m` on `ZMod n`.
-/

namespace MetaMathlibExt

namespace weightedDavenport_zmod_Icc_of_dvd

private theorem not_free_of_factor_mem {m n q : ℕ} {A : Finset ℕ} (hm : 0 < m)
    (hn : 0 < n) (hqm : q * m = n) (hq : q ∈ A) (s : List (ZMod n)) (hs : s.length = m) :
    ¬ IsWeightedZeroSumFree A s := by
  subst m
  have : NeZero s.length := ⟨hm.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  -- Find a block whose sum of representatives is divisible by the sequence length.
  have hblock := (consecutive_constant_eq_card (ZMod s.length)).1.2
  rw [ZMod.card] at hblock
  obtain ⟨u, v, huv, w, hw, hz⟩ := hblock (fun i => ((s.get i).val : ZMod s.length))
  let I := Finset.Icc u v
  have hdvd : s.length ∣ ∑ i ∈ I, (s.get i).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sum]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans hz
    rw [show w i = 1 from hw i hi, one_zsmul]
  -- Weighting every term in the block by `q` makes the sum divisible by `n`.
  intro hfree
  apply hfree I ⟨u, Finset.left_mem_Icc.mpr huv⟩ (fun _ => q) (fun _ _ => hq)
  have hnSum : n ∣ q * ∑ i ∈ I, (s.get i).val := by
    simpa only [hqm] using Nat.mul_dvd_mul_left q hdvd
  simpa [nsmul_eq_mul, Finset.mul_sum] using (ZMod.natCast_eq_zero_iff _ _).mpr hnSum

private theorem replicate_one_free {l r n : ℕ} (hlt : l * r < n) :
    IsWeightedZeroSumFree (Finset.Icc 1 r) (List.replicate l (1 : ZMod n)) := by
  intro I hI a ha hz
  have hpos : 0 < ∑ i ∈ I, a i :=
    Finset.sum_pos (fun i hi => (Finset.mem_Icc.mp (ha i hi)).1) hI
  have hcard : I.card ≤ l := by simpa using I.card_le_univ
  have hsum : ∑ i ∈ I, a i < n := calc
    ∑ i ∈ I, a i ≤ ∑ _ ∈ I, r := Finset.sum_le_sum fun i hi => (Finset.mem_Icc.mp (ha i hi)).2
    _ ≤ l * r := by simpa using Nat.mul_le_mul_right r hcard
    _ < n := hlt
  have hdvd : n ∣ ∑ i ∈ I, a i := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simpa [List.get_eq_getElem, nsmul_eq_mul] using hz)
  exact (Nat.le_of_dvd hpos hdvd).not_gt hsum

end weightedDavenport_zmod_Icc_of_dvd

open weightedDavenport_zmod_Icc_of_dvd in
/-- **Initial-interval weights with weighted Davenport constant $m$.** Let $m, n \ge 2$ be
natural numbers with $m \mid n$ and put $r = \lceil n/(m-1) \rceil - 1$. Then the
$\{1, \dots, r\}$-weighted Davenport constant of $\mathbb{Z}/n\mathbb{Z}$ is
$D_{\{1, \dots, r\}}(\mathbb{Z}/n\mathbb{Z}) = m$.

Source: Md Ibrahim Molla, *New Families of Weight Sets Yielding Prescribed Weighted Zero-Sum
Constants*, INTEGERS 26 (2026), Article A89, Corollary 1, second part (`integers-2026-A89-cor-1`).
-/
public theorem weightedDavenport_zmod_Icc_of_dvd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdvd : m ∣ n) :
    weightedDavenport (Finset.Icc 1 (n ⌈/⌉ (m - 1) - 1)) (ZMod n) = ((m : ℕ) : ℕ∞) := by
  obtain ⟨q, hnq⟩ := hdvd
  have hnpos : 0 < n := by omega
  have hq : 0 < q := Nat.pos_of_mul_pos_left (hnq ▸ hnpos)
  have hp : 0 < m - 1 := by omega
  have hqceil : q < n ⌈/⌉ (m - 1) := (gc_mul_ceilDiv hp).lt_iff_lt.mpr (by
    rw [hnq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hq)
  have hr : (m - 1) * (n ⌈/⌉ (m - 1) - 1) < n :=
    (gc_mul_ceilDiv hp).lt_iff_lt.mp (by omega)
  apply le_antisymm
  · apply weightedDavenport_le
    exact not_free_of_factor_mem (by omega) hnpos ((Nat.mul_comm q m).trans hnq.symm)
      (Finset.mem_Icc.mpr ⟨hq, by omega⟩)
  · have h := Order.add_one_le_of_lt (lt_weightedDavenport (replicate_one_free hr))
    simpa only [List.length_replicate, ← Nat.cast_succ, Nat.succ_eq_add_one,
      Nat.sub_add_cancel (by omega : 1 ≤ m)] using h

end MetaMathlibExt
