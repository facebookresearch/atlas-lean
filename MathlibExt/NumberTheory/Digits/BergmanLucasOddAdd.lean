/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.BasePhiRepresentations
public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution
import MathlibExt.NumberTheory.Digits.BasePhiConjugate
import all MathlibExt.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval
import all MathlibExt.NumberTheory.Digits.BergmanLucasEvenAdd

/-!
# Recursive structure of Bergman expansions in odd Lucas intervals

For natural numbers $n \ge 2$ and $k$, compare Bergman expansions $S$ and $T$ in three cases:

* For $1 \le k \le L_{2n-2}-1$, $S$ represents $L_{2n-1}+k$. The first case takes $T$ of value
  $L_{2n+1}+k$, and the second takes $T$ of value $L_{2n+1}+L_{2n-1}+k$.
* For $k \le L_{2n-3}$, $S$ represents $L_{2n-2}+k$ and $T$ represents $L_{2n+1}+L_{2n-2}+k$.

In each case the theorem describes $T$ by replacing the least and greatest digits of $S$ and
leaving the interior digits unchanged. This encodes the source's word formulas: removing `10`
from the left and `01` from the right removes precisely the greatest and least positions of `1`.
The proof bounds both end positions, checks the spacing and value of the replacement, and uses
uniqueness. For the first case, the conjugate sum rules out a digit two positions above the least.

## References

* Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, The Fibonacci Quarterly
  62 (2024), no. 2, 112–124, Theorem 5.2 II and Proposition 5.1(b).
* F. Michel Dekking, *How to Add Two Natural Numbers in Base Phi*, The Fibonacci Quarterly
  59 (2021), no. 1, 19–22, Recursive Structure Theorem, Part II.
* Reuses `bergman_value_lt`, `value_pow_le_of_mem`, `bergman_eq_of_value_eq`, `pow_add_prev` and
  `pair_value` from `MathlibExt.NumberTheory.Digits.BergmanLucasEvenAdd`, and
  `bergman_lowest_position_lucasInterval` and its Lucas power bounds from
  `MathlibExt.NumberTheory.Digits.BasePhiRepresentationsBergmanLowestPositionLucasInterval`.
  The conjugate estimate is `BasePhiConjugate.conj_factor_gt` from
  `MathlibExt.NumberTheory.Digits.BasePhiConjugate`.
-/

open scoped goldenRatio

namespace MetaMathlibExt

open bergman_lucas_even_add (pow_add_prev pair_value)

namespace bergman_lucas_odd_add

open BasePhiConjugate
open bergman_lucas_even_add (bergman_value_lt value_pow_le_of_mem bergman_eq_of_value_eq)
open bergman_lowest_position_lucasInterval (lucas_even_gt lucas_odd_lt lucas_odd_add_one_gt
  lucas_even_sub_one_lt)

private theorem greatest_eq_of_value_bounds {S : Finset ℤ} (hS : IsBergmanExpansion S)
    {t j : ℤ} (ht : IsGreatest (S : Set ℤ) t)
    (hlo : φ ^ j ≤ basePhiValue S) (hhi : basePhiValue S < φ ^ (j + 1)) : t = j := by
  have htop := value_pow_le_of_mem (Finset.mem_coe.mp ht.1)
  have hbound := bergman_value_lt hS (k := t + 1) fun i hi =>
    Int.lt_add_one_iff.mpr (ht.2 (Finset.mem_coe.mpr hi))
  have h₁ := (zpow_lt_zpow_iff_right₀ Real.one_lt_goldenRatio).mp (htop.trans_lt hhi)
  have h₂ := (zpow_lt_zpow_iff_right₀ Real.one_lt_goldenRatio).mp (hlo.trans_lt hbound)
  omega

private theorem odd_endpoints {m k : ℕ} {S : Finset ℤ} (hS : IsBergmanExpansion S)
    (hSN : basePhiValue S = (lucasNumber (2 * m + 1) + k : ℕ))
    (hk : 1 ≤ k) (hk' : k ≤ lucasNumber (2 * m) - 1)
    {a t : ℤ} (ha : IsLeast (S : Set ℤ) a) (ht : IsGreatest (S : Set ℤ) t) :
    a = -(2 * (m : ℤ) + 2) ∧ t = 2 * (m : ℤ) + 1 ∧ a + 2 ∉ S := by
  have hrec := cb_lucas_add_two (2 * m)
  have hhi : lucasNumber (2 * m + 1) + k + 1 ≤ lucasNumber (2 * m + 2) := by omega
  have hlo : lucasNumber (2 * m + 1) + 1 ≤ lucasNumber (2 * m + 1) + k := by omega
  have hI : lucasNumber (2 * m + 1) + k ∈
      Set.Icc (lucasNumber (2 * m + 1) + 1) (lucasNumber (2 * m + 2) - 1) :=
    ⟨hlo, by omega⟩
  have ha' : a = -(2 * (m : ℤ) + 2) := by
    have := (bergman_lowest_position_lucasInterval _ m hS hSN ha).2 hI
    omega
  have hloR : (lucasNumber (2 * m + 1) : ℝ) + 1 ≤
      ((lucasNumber (2 * m + 1) + k : ℕ) : ℝ) := by exact_mod_cast hlo
  have hlow := (lucas_odd_add_one_gt m).trans_le hloR
  have hhigh := (show ((lucasNumber (2 * m + 1) + k : ℕ) : ℝ) ≤
      (lucasNumber (2 * m + 2) : ℝ) - 1 by
    have h : ((lucasNumber (2 * m + 1) + k : ℕ) : ℝ) + 1 ≤
        (lucasNumber (2 * m + 2) : ℝ) := by exact_mod_cast hhi
    linarith).trans_lt (lucas_even_sub_one_lt m)
  have ht' : t = 2 * (m : ℤ) + 1 := by
    apply greatest_eq_of_value_bounds hS ht <;> rw [hSN]
    · push_cast at hlow ⊢
      exact hlow.le
    · push_cast at hhigh ⊢
      simpa only [add_assoc, one_add_one_eq_two] using hhigh
  refine ⟨ha', ht', ?_⟩
  intro hm
  have haS : a ∈ S := Finset.mem_coe.mp ha.1
  have ha₁ := hS a haS
  have hmin : ∀ i ∈ S.erase a, a + 2 ≤ i := by
    intro i hi
    obtain ⟨hia, hiS⟩ := Finset.mem_erase.mp hi
    have hle := ha.2 (Finset.mem_coe.mpr hiS)
    have hin : i ≠ a + 1 := fun e => ha₁ (e ▸ hiS)
    omega
  have hnorm := conj_factor_gt (S := S.erase a)
    (fun i hi hj => hS i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj))
    (Finset.mem_erase.mpr ⟨by omega, hm⟩) hmin
  have hev : Even a := ⟨-(m : ℤ) - 1, by omega⟩
  have hev₂ : Even (a + 2) := hev.add ⟨1, by decide⟩
  have htail : (0 : ℝ) < ∑ i ∈ S.erase a, ψ ^ i := by
    calc
      0 < ψ ^ (a + 2) * ∑ i ∈ S.erase a, ψ ^ (i - (a + 2)) := by
        rw [even_pow_eq hev₂]
        have hpos := (neg_pos.mpr Real.goldenConj_neg).trans hnorm
        exact mul_pos (zpow_pos Real.goldenRatio_pos _) hpos
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← zpow_add₀ Real.goldenConj_ne_zero, show a + 2 + (i - (a + 2)) = i by omega]
  have hc := Finset.sum_erase_add S (fun i : ℤ => ψ ^ i) haS
  rw [conj_sum_eq hSN, even_pow_eq hev] at hc
  have hpow : φ ^ (-a) = φ ^ ((2 * m + 2 : ℕ) : ℤ) := by
    congr 1
    push_cast
    omega
  rw [hpow] at hc
  linarith

private theorem even_endpoints {m k : ℕ} (hm : 1 ≤ m) {S : Finset ℤ} (hS : IsBergmanExpansion S)
    (hSN : basePhiValue S = (lucasNumber (2 * m) + k : ℕ)) (hk : k ≤ lucasNumber (2 * m - 1))
    {a t : ℤ} (ha : IsLeast (S : Set ℤ) a) (ht : IsGreatest (S : Set ℤ) t) :
    a = -(2 * (m : ℤ)) ∧ t = 2 * (m : ℤ) := by
  have hrec := cb_lucas_add_two (2 * m - 1)
  rw [show 2 * m - 1 + 2 = 2 * m + 1 by omega, show 2 * m - 1 + 1 = 2 * m by omega] at hrec
  have hlo : lucasNumber (2 * m) ≤ lucasNumber (2 * m) + k := by omega
  have hhi : lucasNumber (2 * m) + k ≤ lucasNumber (2 * m + 1) := by omega
  refine ⟨?_, ?_⟩
  · have := (bergman_lowest_position_lucasInterval _ m hS hSN ha).1 ⟨hlo, hhi⟩
    omega
  · apply greatest_eq_of_value_bounds hS ht <;> rw [hSN]
    · have hloR : (lucasNumber (2 * m) : ℝ) ≤
          ((lucasNumber (2 * m) + k : ℕ) : ℝ) := by exact_mod_cast hlo
      have h := (lucas_even_gt m).trans_le hloR
      push_cast at h ⊢
      exact h.le
    · have h := (show ((lucasNumber (2 * m) + k : ℕ) : ℝ) ≤
          (lucasNumber (2 * m + 1) : ℝ) by exact_mod_cast hhi).trans_lt (lucas_odd_lt m)
      push_cast at h ⊢
      exact h

private theorem odd_lucas_value (m : ℕ) :
    φ ^ (2 * (m : ℤ) + 1) - φ ^ (-(2 * (m : ℤ) + 1)) = (lucasNumber (2 * m + 1) : ℝ) := by
  have he : ((2 * m + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by push_cast; ring
  have ho : Odd (2 * (m : ℤ) + 1) := ⟨m, rfl⟩
  have hψ : ψ = -φ⁻¹ := by rw [Real.inv_goldenRatio, neg_neg]
  rw [← cb_lucas_binet, ← zpow_natCast φ, ← zpow_natCast ψ, he, hψ, ho.neg_zpow, inv_zpow,
    ← zpow_neg, sub_eq_add_neg]

private theorem interior_bounds {S : Finset ℤ} (hS : IsBergmanExpansion S) {a t : ℤ}
    (ha : IsLeast (S : Set ℤ) a) (ht : IsGreatest (S : Set ℤ) t) {i : ℤ}
    (hi : i ∈ (S.erase a).erase t) : a + 2 ≤ i ∧ i + 2 ≤ t := by
  simp only [Finset.mem_erase] at hi
  obtain ⟨hit, hia, hiS⟩ := hi
  have hlo := ha.2 (Finset.mem_coe.mpr hiS)
  have hhi := ht.2 (Finset.mem_coe.mpr hiS)
  have hleft : i ≠ a + 1 := fun e => hS a (Finset.mem_coe.mp ha.1) (e ▸ hiS)
  have hright : i + 1 ≠ t := fun e => hS i hiS (e.symm ▸ Finset.mem_coe.mp ht.1)
  omega

private theorem eq_splice {S E T : Finset ℤ} {a t : ℤ} (ha : a ∈ S) (ht : t ∈ S) (hat : a ≠ t)
    (hS : IsBergmanExpansion S) (hE : IsBergmanExpansion E) (hT : IsBergmanExpansion T)
    (hsep : ∀ x ∈ E, ∀ y ∈ (S.erase a).erase t, x + 2 ≤ y ∨ y + 2 ≤ x)
    (hv : basePhiValue E + basePhiValue S = basePhiValue T + (φ ^ a + φ ^ t)) :
    T = E ∪ (S.erase a).erase t := by
  let I := (S.erase a).erase t
  have hsub : I ⊆ S := fun _ hi => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
  have hd : Disjoint E I := Finset.disjoint_left.mpr fun i hi hj => by
    rcases hsep i hi i hj with h | h <;> omega
  have hb : IsBergmanExpansion (E ∪ I) := by
    intro i hi hj
    rcases Finset.mem_union.mp hi with hi | hi <;> rcases Finset.mem_union.mp hj with hj | hj
    · exact hE i hi hj
    · rcases hsep i hi (i + 1) hj with h | h <;> omega
    · rcases hsep (i + 1) hj i hi with h | h <;> omega
    · exact hS i (hsub hi) (hsub hj)
  have hsplit : basePhiValue I + φ ^ t + φ ^ a = basePhiValue S := by
    unfold I basePhiValue
    rw [Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hat.symm, ht⟩),
      Finset.sum_erase_add _ _ ha]
  apply bergman_eq_of_value_eq hT hb
  change basePhiValue T = ∑ i ∈ E ∪ I, φ ^ i
  rw [Finset.sum_union hd]
  change basePhiValue T = basePhiValue E + basePhiValue I
  linarith

end bergman_lucas_odd_add

open bergman_lucas_odd_add

/-- **Recursive structure of Bergman expansions, odd Lucas case.** Let $n \ge 2$, let $k$ be a
natural number, and write $L_m$ for the $m$-th Lucas number. Call a finite set of integers with no
two consecutive elements a Bergman expansion. Let $S$ and $T$ be Bergman expansions, let $a$ and
$t$ be the least and the greatest element of $S$, let $S' = S \setminus \{a, t\}$, and for an
integer $c$ write $S' + c = \{x + c : x \in S'\}$.

(i) If $1 \le k \le L_{2n-2} - 1$, the base phi value of $S$ is $L_{2n-1} + k$ and that of $T$
is $L_{2n+1} + k$, then there is an integer $b$ with
$T = \{b, b + 3, b + (t - a) + 4\} \cup (S' + (b - a + 2))$.

(ii) If $1 \le k \le L_{2n-2} - 1$, the base phi value of $S$ is $L_{2n-1} + k$ and that of $T$
is $L_{2n+1} + L_{2n-1} + k$, then there is an integer $b$ with
$T = \{b, b + (t - a) + 2, b + (t - a) + 4\} \cup (S' + (b - a + 2))$.

(iii) If $k \le L_{2n-3}$, the base phi value of $S$ is $L_{2n-2} + k$ and that of $T$ is
$L_{2n+1} + L_{2n-2} + k$, then there is an integer $b$ with
$T = \{b, b + 3, b + (t - a) + 4, b + (t - a) + 7\} \cup (S' + (b - a + 4))$.

Source: Michel Dekking and Ad van Loon, *Counting Base Phi Representations*,
Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 5.2 II,
quoting F. Michel Dekking, *How to Add Two Natural Numbers in Base Phi*
(`fq-2024-dekking11102023-thm-5.2`). -/
public theorem bergman_lucas_odd_add (n : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ lucasNumber (2 * n - 2) - 1 →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 1) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 1) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + (t - a) + 2, b + (t - a) + 4} ∪
          ((S.erase a).erase t).image (· + (b - a + 2))) ∧
    (∀ k : ℕ, k ≤ lucasNumber (2 * n - 3) →
      ∀ S T : Finset ℤ, ∀ a t : ℤ, IsBergmanExpansion S →
        basePhiValue S = (lucasNumber (2 * n - 2) + k : ℕ) →
        IsLeast (S : Set ℤ) a → IsGreatest (S : Set ℤ) t → IsBergmanExpansion T →
        basePhiValue T = (lucasNumber (2 * n + 1) + lucasNumber (2 * n - 2) + k : ℕ) →
        ∃ b : ℤ, T = {b, b + 3, b + (t - a) + 4, b + (t - a) + 7} ∪
          ((S.erase a).erase t).image (· + (b - a + 4))) := by
  let m := n - 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hm₀ : 2 * m = 2 * n - 2 := by dsimp [m]; omega
  have hm₁ : 2 * m + 1 = 2 * n - 1 := by dsimp [m]; omega
  have hm₃ : 2 * m + 3 = 2 * n + 1 := by dsimp [m]; omega
  have hm' : 2 * m - 1 = 2 * n - 3 := by dsimp [m]; omega
  rw [← hm₀, ← hm₁, ← hm₃, ← hm']
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hk' S T a t hS hSN ha ht hT hTN
    obtain ⟨ha', ht', hgap⟩ := odd_endpoints hS hSN hk hk' ha ht
    have hat : a + 4 ≤ t := by omega
    refine ⟨a - 2, ?_⟩
    simp only [show a - 2 + 3 = a + 1 by omega, show a - 2 + (t - a) + 4 = t + 2 by omega,
      show a - 2 - a + 2 = 0 by omega, add_zero, Finset.image_id']
    refine eq_splice (Finset.mem_coe.mp ha.1) (Finset.mem_coe.mp ht.1) (by omega) hS ?_ hT ?_ ?_
    · intro i hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      omega
    · intro x hx y hy
      have hy' := interior_bounds hS ha ht hy
      have hyS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hne : y ≠ a + 2 := fun e => hgap (e ▸ hyS)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · rw [hSN, hTN]
      push_cast
      unfold basePhiValue
      rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_pair (by omega)]
      have hlo := pow_add_prev (a - 1)
      have hlo' := pow_add_prev a
      have hhi := pow_add_prev (t + 1)
      rw [show a - 1 - 1 = a - 2 by omega, sub_add_cancel] at hlo
      rw [add_sub_cancel_right, show t + 1 + 1 = t + 2 by omega] at hhi
      have hval := pair_value (m + 1)
      rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hval
      push_cast at hval
      rw [show 2 * ((m : ℤ) + 1) = t + 1 by omega,
        show -(t + 1) = a by omega] at hval
      have hrec : lucasNumber (2 * m + 3) =
          lucasNumber (2 * m + 2) + lucasNumber (2 * m + 1) := cb_lucas_add_two (2 * m + 1)
      rw [hrec, Nat.cast_add]
      linarith
  · intro k hk hk' S T a t hS hSN ha ht hT hTN
    obtain ⟨ha', ht', _⟩ := odd_endpoints hS hSN hk hk' ha ht
    have hat : a + 4 ≤ t := by omega
    refine ⟨a - 2, ?_⟩
    simp only [show a - 2 + (t - a) + 2 = t by omega, show a - 2 + (t - a) + 4 = t + 2 by omega,
      show a - 2 - a + 2 = 0 by omega, add_zero, Finset.image_id']
    refine eq_splice (Finset.mem_coe.mp ha.1) (Finset.mem_coe.mp ht.1) (by omega) hS ?_ hT ?_ ?_
    · intro i hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      omega
    · intro x hx y hy
      have hy' := interior_bounds hS ha ht hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · rw [hSN, hTN]
      push_cast
      unfold basePhiValue
      rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_pair (by omega)]
      have hlo := pow_add_prev (a - 1)
      rw [show a - 1 - 1 = a - 2 by omega, sub_add_cancel] at hlo
      have hval := odd_lucas_value (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] at hval
      push_cast at hval
      rw [show 2 * ((m : ℤ) + 1) + 1 = t + 2 by omega, show -(t + 2) = a - 1 by omega] at hval
      linarith
  · intro k hk S T a t hS hSN ha ht hT hTN
    obtain ⟨ha', ht'⟩ := even_endpoints hm hS hSN hk ha ht
    have hat : a + 4 ≤ t := by omega
    refine ⟨a - 4, ?_⟩
    simp only [show a - 4 + 3 = a - 1 by omega, show a - 4 + (t - a) + 4 = t by omega,
      show a - 4 + (t - a) + 7 = t + 3 by omega, show a - 4 - a + 4 = 0 by omega,
      add_zero, Finset.image_id']
    refine eq_splice (Finset.mem_coe.mp ha.1) (Finset.mem_coe.mp ht.1) (by omega) hS ?_ hT ?_ ?_
    · intro i hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      omega
    · intro x hx y hy
      have hy' := interior_bounds hS ha ht hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · rw [hSN, hTN]
      push_cast
      unfold basePhiValue
      rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.sum_pair (by omega)]
      have hlo := pow_add_prev (a - 1)
      have hlo' := pow_add_prev (a - 2)
      have hlo'' := pow_add_prev (a - 3)
      rw [show a - 1 - 1 = a - 2 by omega, sub_add_cancel] at hlo
      rw [show a - 2 - 1 = a - 3 by omega, show a - 2 + 1 = a - 1 by omega] at hlo'
      rw [show a - 3 - 1 = a - 4 by omega, show a - 3 + 1 = a - 2 by omega] at hlo''
      have hval := odd_lucas_value (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] at hval
      push_cast at hval
      rw [show 2 * ((m : ℤ) + 1) + 1 = t + 3 by omega, show -(t + 3) = a - 3 by omega] at hval
      linarith

end MetaMathlibExt
