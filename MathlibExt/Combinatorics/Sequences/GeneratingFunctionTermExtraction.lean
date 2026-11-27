/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Term extraction from generating function values
-/

/--
**Recovering a sequence term from its generating function.** Let $t_0, t_1, t_2, \dots$ be
natural numbers and let $c$, $m$, $N$ be natural numbers with $c \ge 2$ and $2 \le m \le N$.
Suppose that the real series $\sum_{k \ge 0} t_k \, (c^{-N})^k$ is summable and that
$t_j < c^{j-2}$ for every $j \ge m$. Then

$$t_N = \Bigl\lfloor c^{N^2} \sum_{k \ge 0} t_k \, (c^{-N})^k \Bigr\rfloor \bmod c^N.$$

Source: M. Prunescu and J. M. Shunia, "On Modular Representations of
C-Recursive Integer Sequences", Journal of Integer Sequences 28 (2025),
Article 25.5.3, Theorem `ThmExtraction1`, source lines 169–173,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.tex>.
The paper attributes the result to Prunescu and Sauras-Altuzarra.
Only the first representation (for `N ≥ m ≥ 2` with `t j < c ^ (j - 2)`)
is recorded, not the `c ≥ 8` variant for all `n ≥ 1`.

Proves `Wanted` entry `generating_function_term_extraction`.
-/
theorem generating_function_term_extraction
    (t : ℕ → ℕ) (c m N : ℕ)
    (hc : 2 ≤ c) (hm : 2 ≤ m) (hmN : m ≤ N)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ N)⁻¹) ^ k))
    (hbound : ∀ j, m ≤ j → t j < c ^ (j - 2)) :
    t N = Nat.floor ((c : ℝ) ^ (N ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ N)⁻¹) ^ k)) % c ^ N := by
  have hN : 2 ≤ N := le_trans hm hmN
  have hcR : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
  have hBNne : ((c : ℝ) ^ N) ≠ 0 := pow_ne_zero N hcne
  have hBpos : (0 : ℝ) < ((c : ℝ) ^ N) := pow_pos hcpos N
  have hC : (c : ℝ) ^ (N ^ 2) = (((c : ℝ) ^ N)) ^ N := by
    rw [pow_two, pow_mul]
  have hg : Summable (fun k => (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k)) :=
    hconv.mul_left _
  have htsum : (c : ℝ) ^ (N ^ 2) * (∑' k, (t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k)
      = ∑' k, (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k) :=
    (Summable.tsum_mul_left _ hconv).symm
  have hhead : ∀ k : ℕ, k ≤ N →
      (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k)
        = ((((t k * (c ^ N) ^ (N - k) : ℕ))) : ℝ) := by
    intro k hk
    have hsplit : ((((c : ℝ) ^ N)) : ℝ) ^ N
        = ((((c : ℝ) ^ N)) : ℝ) ^ (N - k) * ((((c : ℝ) ^ N)) : ℝ) ^ k := by
      rw [← pow_add]
      congr 1
      omega
    have hinv : ((((c : ℝ) ^ N) : ℝ)⁻¹) ^ k = (((((c : ℝ) ^ N) : ℝ) ^ k))⁻¹ :=
      inv_pow _ _
    have hkne : ((((c : ℝ) ^ N) : ℝ) ^ k) ≠ 0 := pow_ne_zero k hBNne
    have hcast : ((((c ^ N) ^ (N - k) : ℕ)) : ℝ) = ((((c : ℝ) ^ N)) : ℝ) ^ (N - k) := by
      rw [Nat.cast_pow, Nat.cast_pow]
    rw [hC, hsplit, hinv, Nat.cast_mul, hcast]
    field_simp
  have htail : ∀ i : ℕ,
      (c : ℝ) ^ (N ^ 2) * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))
        = (t (i + (N + 1)) : ℝ) * (((((c : ℝ) ^ N) ^ (1 + i))))⁻¹ := by
    intro i
    have hsplit : ((((c : ℝ) ^ N)) : ℝ) ^ (i + (N + 1))
        = ((((c : ℝ) ^ N)) : ℝ) ^ N * ((((c : ℝ) ^ N)) : ℝ) ^ (1 + i) := by
      rw [← pow_add]
      congr 1
      omega
    have hinv : ((((c : ℝ) ^ N) : ℝ)⁻¹) ^ (i + (N + 1))
        = (((((c : ℝ) ^ N) : ℝ) ^ (i + (N + 1))))⁻¹ := inv_pow _ _
    have hXne : ((((c : ℝ) ^ N)) : ℝ) ^ (1 + i) ≠ 0 := pow_ne_zero _ hBNne
    have hNne : ((((c : ℝ) ^ N)) : ℝ) ^ N ≠ 0 := pow_ne_zero _ hBNne
    have hprod : ((((c : ℝ) ^ N)) : ℝ) ^ N * ((((c : ℝ) ^ N)) : ℝ) ^ (1 + i) ≠ 0 :=
      mul_ne_zero hNne hXne
    rw [hC, hinv, hsplit]
    field_simp
  have htail_bound : ∀ i : ℕ,
      (c : ℝ) ^ (N ^ 2) * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))
        < (1 / 2 : ℝ) ^ (1 + i) := by
    intro i
    rw [htail i]
    have hjm : m ≤ i + (N + 1) := by omega
    have hnb : t (i + (N + 1)) < c ^ (N + i - 1) := by
      have h1 := hbound (i + (N + 1)) hjm
      have h2 : i + (N + 1) - 2 = N + i - 1 := by omega
      rwa [h2] at h1
    have hreal : ((t (i + (N + 1)) : ℕ) : ℝ) < (c : ℝ) ^ (N + i - 1) := by
      have hcast : ((((c ^ (N + i - 1) : ℕ))) : ℝ) = (c : ℝ) ^ (N + i - 1) := by
        rw [Nat.cast_pow]
      rw [← hcast]
      exact_mod_cast hnb
    have hXpos : (0 : ℝ) < (((c : ℝ) ^ N)) ^ (1 + i) := pow_pos hBpos _
    have hdiv : (t (i + (N + 1)) : ℝ) * (((((c : ℝ) ^ N) ^ (1 + i))))⁻¹
        < (c : ℝ) ^ (N + i - 1) / (((c : ℝ) ^ N)) ^ (1 + i) := by
      rw [div_eq_mul_inv]
      exact mul_lt_mul_of_pos_right hreal (inv_pos.mpr hXpos)
    refine lt_of_lt_of_le hdiv ?_
    have hexp : (N + i - 1) + (1 + i * (N - 1)) = N * (1 + i) := by
      have hmul : i * (N - 1) = i * N - i := Nat.mul_sub_one i N
      rw [hmul]
      have hiN : i ≤ i * N := by
        calc i = i * 1 := (mul_one i).symm
          _ ≤ i * N := Nat.mul_le_mul le_rfl (by omega)
      have h2 : (N + i - 1) + (1 + (i * N - i)) = (N + i) + (i * N - i) := by omega
      have h3 : (N + i) + (i * N - i) = N + i * N := by omega
      rw [h2, h3]
      ring
    have hXeq : ((((c : ℝ) ^ N)) : ℝ) ^ (1 + i)
        = (c : ℝ) ^ (N + i - 1) * (c : ℝ) ^ (1 + i * (N - 1)) := by
      rw [← pow_add, hexp, pow_mul]
    have hc1 : (c : ℝ) ^ (N + i - 1) ≠ 0 := pow_ne_zero _ hcne
    have hc2 : (c : ℝ) ^ (1 + i * (N - 1)) ≠ 0 := pow_ne_zero _ hcne
    have heq : (c : ℝ) ^ (N + i - 1) / ((((c : ℝ) ^ N)) : ℝ) ^ (1 + i)
        = 1 / (c : ℝ) ^ (1 + i * (N - 1)) := by
      rw [hXeq, div_eq_div_iff (mul_ne_zero hc1 hc2) hc2, one_mul]
    have hNm1 : 1 ≤ N - 1 := by omega
    have hi0 : i * 1 ≤ i * (N - 1) := Nat.mul_le_mul le_rfl hNm1
    have hi : i ≤ i * (N - 1) := by rwa [mul_one] at hi0
    have hexple : 1 + i ≤ 1 + i * (N - 1) := Nat.add_le_add_left hi 1
    have hpow1 : (2 : ℝ) ^ (1 + i) ≤ (c : ℝ) ^ (1 + i) := pow_le_pow_left₀ (by norm_num) hcR _
    have hpow2 : (c : ℝ) ^ (1 + i) ≤ (c : ℝ) ^ (1 + i * (N - 1)) :=
      pow_le_pow_right₀ (by linarith) hexple
    have hpow : (2 : ℝ) ^ (1 + i) ≤ (c : ℝ) ^ (1 + i * (N - 1)) := le_trans hpow1 hpow2
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (1 + i) := pow_pos (by norm_num) _
    have hle : (1 : ℝ) / (c : ℝ) ^ (1 + i * (N - 1)) ≤ 1 / (2 : ℝ) ^ (1 + i) :=
      one_div_le_one_div_of_le h2pos hpow
    rw [heq]
    calc (1 : ℝ) / (c : ℝ) ^ (1 + i * (N - 1)) ≤ 1 / (2 : ℝ) ^ (1 + i) := hle
      _ = (1 / 2 : ℝ) ^ (1 + i) := by rw [div_pow, one_pow]
  have hsplit_sum : (∑ k ∈ Finset.range (N + 1),
        (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k))
        + (∑' i, (c : ℝ) ^ (N ^ 2) * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1))))
      = ∑' k, (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k) :=
    Summable.sum_add_tsum_nat_add (N + 1) hg
  have hfin_cast : (∑ k ∈ Finset.range (N + 1),
        (c : ℝ) ^ (N ^ 2) * ((t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k))
      = (((∑ k ∈ Finset.range (N + 1), t k * (c ^ N) ^ (N - k) : ℕ)) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k < N + 1 := Finset.mem_range.mp hk
    exact hhead k (by omega)
  have hfin_split : (∑ k ∈ Finset.range (N + 1), t k * (c ^ N) ^ (N - k))
      = (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k)) + t N := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
  have hfactor : (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k))
      = c ^ N * (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have hexp : N - k = (N - k - 1) + 1 := by omega
    have e1 : (c ^ N) ^ (N - k) = (c ^ N) * (c ^ N) ^ (N - k - 1) := by
      conv_lhs => rw [hexp, pow_succ']
    rw [e1]
    ring
  have hUbsum : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (1 + i)) := by
    have hbase := summable_geometric_two.mul_left (1 / 2 : ℝ)
    apply hbase.congr
    intro i
    rw [add_comm (1 : ℕ) i, pow_succ']
  have hUbval : (∑' i, (1 / 2 : ℝ) ^ (1 + i)) = 1 := by
    have hcongr : ∀ i : ℕ, (1 / 2 : ℝ) ^ (1 + i) = (1 / 2) * (1 / 2) ^ i := by
      intro i
      rw [add_comm (1 : ℕ) i, pow_succ']
    calc (∑' i, (1 / 2 : ℝ) ^ (1 + i)) = ∑' i, ((1 / 2) * (1 / 2) ^ i) :=
          tsum_congr hcongr
      _ = (1 / 2) * (∑' i, (1 / 2 : ℝ) ^ i) :=
          Summable.tsum_mul_left _ summable_geometric_two
      _ = 1 := by rw [tsum_geometric_two]; norm_num
  have hTnonneg : 0 ≤ (∑' i, (c : ℝ) ^ (N ^ 2)
      * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))) := by
    apply tsum_nonneg
    intro i
    rw [htail i]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact inv_nonneg.mpr (pow_nonneg (le_of_lt hBpos) _)
  have hTlt : (∑' i, (c : ℝ) ^ (N ^ 2)
      * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))) < 1 := by
    have hle : ∀ i, (c : ℝ) ^ (N ^ 2)
          * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))
          ≤ (1 / 2 : ℝ) ^ (1 + i) := fun i => le_of_lt (htail_bound i)
    have hlt := Summable.tsum_lt_tsum_of_nonneg
      (fun i => by
        rw [htail i]
        apply mul_nonneg (Nat.cast_nonneg _)
        exact inv_nonneg.mpr (pow_nonneg (le_of_lt hBpos) _)) hle (htail_bound 0) hUbsum
    rwa [hUbval] at hlt
  have htotal : (c : ℝ) ^ (N ^ 2) * (∑' k, (t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k)
      = ((((c ^ N * (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k - 1)) + t N : ℕ))) : ℝ)
        + (∑' i, (c : ℝ) ^ (N ^ 2)
          * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))) := by
    rw [htsum, ← hsplit_sum, hfin_cast, hfin_split, hfactor]
  have hfloor : Nat.floor ((c : ℝ) ^ (N ^ 2)
      * (∑' k, (t k : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ k))
      = c ^ N * (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k - 1)) + t N := by
    rw [htotal]
    have hT0 : Nat.floor (∑' i, (c : ℝ) ^ (N ^ 2)
        * ((t (i + (N + 1)) : ℝ) * ((((c : ℝ) ^ N))⁻¹) ^ (i + (N + 1)))) = 0 :=
      Nat.floor_eq_zero.mpr hTlt
    have hadd := Nat.floor_add_natCast hTnonneg
      (c ^ N * (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k - 1)) + t N)
    rw [add_comm
        ((((c ^ N * (∑ k ∈ Finset.range N, t k * (c ^ N) ^ (N - k - 1)) + t N : ℕ)) : ℝ)) _,
      hadd, hT0, zero_add]
  have htNlt : t N < c ^ N := by
    have h1 : t N < c ^ (N - 2) := hbound N hmN
    have h2 : c ^ (N - 2) ≤ c ^ N := Nat.pow_le_pow_right (by omega) (by omega)
    exact lt_of_lt_of_le h1 h2
  rw [hfloor, add_comm (c ^ N * _) (t N), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt htNlt]

end MetaMathlibExt
