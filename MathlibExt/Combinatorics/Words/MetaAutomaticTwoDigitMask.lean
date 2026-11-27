/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.Words.MetaAutomaticTwo
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The binary digit mask for the second meta-automatic sequence

Grouping binary digits in threes gives a base-eight recurrence: the top bit of
an octal digit is ignored, and the lower two contribute their parity. Grouping
in pairs instead gives the radix-four description of the same mask.

## References

* John M. Campbell and Benoît Cloitre, [*Meta-Automatic Sequences*](https://cs.uwaterloo.ca/journals/JIS/VOL29/Cloitre/cloitre20.pdf),
  Journal of Integer Sequences 29 (2026), Article 26.4.1, pp. 1–23,
  Lemma 19 and Theorem 26.
-/

namespace MetaMathlibExt

private def twoBitParity (r : ℕ) : Bool :=
  xor (decide (r / 2 = 1)) (decide (r % 2 = 1))

private theorem metaAutomaticTwo_odd (n : ℕ) :
    metaAutomaticTwo (2 * n + 1) = !metaAutomaticTwo (2 * n) :=
  (metaAutomaticTwo_recover n).2.trans
    (congrArg Bool.not (metaAutomaticTwo_recover n).1.symm)

private theorem metaAutomaticTwo_four (n r : ℕ) (hr : r < 4) :
    metaAutomaticTwo (4 * n + r) =
      xor (xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n))) (twoBitParity r) := by
  have h₀ : metaAutomaticTwo (4 * n) = xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) := by
    by_cases hn : n = 0
    · simp [hn, metaAutomaticTwo]
    · rw [(metaAutomaticTwo_rec n).1 (by omega), (metaAutomaticTwo_recover n).1,
        ← Bool.xor_assoc]
      simp
  have h₁ : metaAutomaticTwo (4 * n + 1) = !metaAutomaticTwo (4 * n) := by
    simpa only [show 2 * (2 * n) = 4 * n by omega] using metaAutomaticTwo_odd (2 * n)
  have h₂ : metaAutomaticTwo (4 * n + 2) = !metaAutomaticTwo (4 * n) := by
    rw [(metaAutomaticTwo_rec n).2.2.1, h₀]
    cases metaAutomaticTwo n <;> simp [metaAutomaticTwo_odd]
  have h₃ := (metaAutomaticTwo_rec n).2.2.2
  obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  · simp [twoBitParity, h₀]
  · simp [twoBitParity, h₁, h₀]
  · simp [twoBitParity, h₂, h₀]
  · simp [twoBitParity, h₃, h₂, h₀]

private theorem metaAutomaticTwo_eight (n r : ℕ) (hr : r < 8) :
    metaAutomaticTwo (8 * n + r) = xor (metaAutomaticTwo n) (twoBitParity (r % 4)) := by
  have h₀ : metaAutomaticTwo (4 * n) = xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) := by
    simpa only [Nat.add_zero, show twoBitParity 0 = false from rfl, Bool.xor_false] using
      metaAutomaticTwo_four n 0 (by decide)
  have h₂ :
      metaAutomaticTwo (4 * n + 2) = !xor (metaAutomaticTwo n) (metaAutomaticTwo (2 * n)) := by
    simpa only [show twoBitParity 2 = true from rfl, Bool.xor_true] using
      metaAutomaticTwo_four n 2 (by decide)
  rw [show 8 * n + r = 4 * (2 * n + r / 4) + r % 4 by omega,
    metaAutomaticTwo_four _ _ (Nat.mod_lt _ (by decide))]
  obtain h | h : r / 4 = 0 ∨ r / 4 = 1 := by omega
  · rw [h, Nat.add_zero, show 2 * (2 * n) = 4 * n by omega, h₀]
    cases metaAutomaticTwo n <;> cases metaAutomaticTwo (2 * n) <;> rfl
  · rw [h, metaAutomaticTwo_odd, show 2 * (2 * n + 1) = 4 * n + 2 by omega, h₂]
    cases metaAutomaticTwo n <;> cases metaAutomaticTwo (2 * n) <;> rfl

private theorem thueMorse_two (n r : ℕ) (hr : r < 2) :
    thueMorse (2 * n + r) = xor (thueMorse n) (decide (r = 1)) := by
  by_cases h : 2 * n + r = 0
  · have hn : n = 0 := by omega
    have h₀ : r = 0 := by omega
    simp [hn, h₀, thueMorse]
  have hd : Nat.digits 2 (2 * n + r) = r :: Nat.digits 2 n := by
    rw [Nat.add_comm (2 * n) r, Nat.digits_add 2 (by decide) r n hr (by omega)]
  unfold thueMorse
  rw [hd]
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · simp
  · rw [List.count_cons_self, show decide ((1 : ℕ) = 1) = true by decide, Bool.xor_true]
    by_cases hp : (Nat.digits 2 n).count 1 % 2 = 1 <;>
      simp [hp, show ((Nat.digits 2 n).count 1 + 1) % 2 = 1 ↔
        (Nat.digits 2 n).count 1 % 2 ≠ 1 by omega]

private theorem thueMorse_eight (n r : ℕ) (hr : r < 4) :
    thueMorse (8 * n + r) = xor (thueMorse n) (twoBitParity r) := by
  rw [show 8 * n + r = 2 * (2 * (2 * n + 0) + r / 2) + r % 2 by omega,
    thueMorse_two _ _ (by omega), thueMorse_two _ _ (by omega), thueMorse_two n 0 (by decide)]
  simp [twoBitParity]

private def maskTerm (n i : ℕ) : ℕ :=
  if i % 3 = 2 then 0 else n / 2 ^ i % 2 * 2 ^ i

private def maskSum (n len : ℕ) : ℕ := ∑ i ∈ Finset.range len, maskTerm n i

-- There are no nonzero digits beyond any length strictly larger than the index itself.
private theorem maskSum_extend (n len : ℕ) (h : n + 1 ≤ len) :
    maskSum n len = maskSum n (n + 1) := by
  unfold maskSum
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  have hni : n < i := Nat.lt_of_succ_le (by simpa using hi)
  have hpow : n < 2 ^ i := hni.trans Nat.lt_two_pow_self
  simp [maskTerm, Nat.div_eq_of_lt hpow]

private theorem maskTerm_add_three (n r : ℕ) (hr : r < 8) (i : ℕ) :
    maskTerm (8 * n + r) (3 + i) = 8 * maskTerm n i := by
  have hd : (8 * n + r) / 8 = n := by omega
  have hm : (3 + i) % 3 = i % 3 := by omega
  simp only [maskTerm, hm, pow_add, show 2 ^ 3 = 8 by decide, ← Nat.div_div_eq_div_mul, hd]
  split <;> simp [Nat.mul_left_comm]

private theorem maskSum_eight (n len r : ℕ) (hr : r < 8) :
    maskSum (8 * n + r) (3 + len) = 8 * maskSum n len + r % 4 := by
  have h₃ : maskSum (8 * n + r) 3 = r % 4 := by
    simp only [maskSum, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, maskTerm]
    simp only [show (0 : ℕ) % 3 ≠ 2 by decide, show (1 : ℕ) % 3 ≠ 2 by decide,
      ite_false, ite_true, pow_zero, pow_one, Nat.div_one, Nat.mul_one, Nat.add_zero]
    omega
  rw [maskSum, Finset.sum_range_add]
  change maskSum (8 * n + r) 3 + _ = _
  simp_rw [h₃, Nat.add_comm (r % 4), maskTerm_add_three n r hr]
  rw [maskSum, Finset.mul_sum]

private theorem metaAutomaticTwo_eq_maskSum (n : ℕ) :
    metaAutomaticTwo n = thueMorse (maskSum n (n + 1)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · simp [hn, maskSum, maskTerm, thueMorse, metaAutomaticTwo, Nat.digits_zero]
    let m := n / 8
    let r := n % 8
    have hm : m < n := Nat.div_lt_self (by omega) (by decide)
    have hr : r < 8 := Nat.mod_lt _ (by decide)
    have he : n = 8 * m + r := by dsimp [m, r]; omega
    have hmask : maskSum n (n + 1) = 8 * maskSum m (m + 1) + r % 4 := calc
      maskSum n (n + 1) = maskSum n (3 + (n + 1)) := (maskSum_extend n _ (by omega)).symm
      _ = maskSum (8 * m + r) (3 + (n + 1)) := congrArg (fun k => maskSum k (3 + (n + 1))) he
      _ = 8 * maskSum m (n + 1) + r % 4 := maskSum_eight m (n + 1) r hr
      _ = 8 * maskSum m (m + 1) + r % 4 := by rw [maskSum_extend m (n + 1) (by omega)]
    calc
      metaAutomaticTwo n = metaAutomaticTwo (8 * m + r) := congrArg metaAutomaticTwo he
      _ = xor (metaAutomaticTwo m) (twoBitParity (r % 4)) := metaAutomaticTwo_eight m r hr
      _ = thueMorse (maskSum n (n + 1)) := by
        rw [hmask, thueMorse_eight _ _ (Nat.mod_lt _ (by decide)), ih m hm]

private theorem sum_range_pairs (f : ℕ → ℕ) (len : ℕ) :
    (∑ i ∈ Finset.range (2 * len), f i) =
      ∑ k ∈ Finset.range len, (f (2 * k) + f (2 * k + 1)) := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [show 2 * (len + 1) = (2 * len + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.add_assoc]

private theorem maskTerm_pair (n k : ℕ) :
    maskTerm n (2 * k) + maskTerm n (2 * k + 1) =
      (if k % 3 = 0 then n / 4 ^ k % 4
        else if k % 3 = 1 then 2 * (n / 4 ^ k % 4 / 2) else n / 4 ^ k % 4 % 2) * 4 ^ k := by
  have hp : (2 : ℕ) ^ (2 * k) = 4 ^ k := by rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by decide]
  have hp' : (2 : ℕ) ^ (2 * k + 1) = 4 ^ k * 2 := by rw [pow_succ, hp]
  have hlo : n / 4 ^ k % 2 = n / 4 ^ k % 4 % 2 := by omega
  have hhi : n / 4 ^ k / 2 % 2 = n / 4 ^ k % 4 / 2 := by omega
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · have he : (2 * k) % 3 ≠ 2 := by omega
    have ho : (2 * k + 1) % 3 ≠ 2 := by omega
    simp only [maskTerm, hp, hp', ← Nat.div_div_eq_div_mul, he, ho, ite_false, h, ite_true]
    rw [Nat.mul_comm (4 ^ k) 2, ← Nat.mul_assoc, ← Nat.add_mul]
    congr 1
    omega
  · have he : (2 * k) % 3 = 2 := by omega
    have ho : (2 * k + 1) % 3 ≠ 2 := by omega
    simp only [maskTerm, he, ho, ite_true, ite_false, hp', ← Nat.div_div_eq_div_mul, hhi,
      zero_add, h, show (1 : ℕ) ≠ 0 by decide]
    ac_rfl
  · have he : (2 * k) % 3 ≠ 2 := by omega
    have ho : (2 * k + 1) % 3 = 2 := by omega
    simp only [maskTerm, hp, he, ho, h, ite_true, ite_false, Nat.add_zero, hlo,
      show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide]

/-- **$\mathcal{M}_2$ is the Thue–Morse sequence along a binary digit mask.** For a natural
number $m$ with binary digits $b_i = \lfloor m / 2^i \rfloor \bmod 2$, let $q(m)$ be the sum of
$b_i 2^i$ over the $i \le m$ with $i \not\equiv 2 \pmod 3$, that is, the number obtained from $m$
by setting its binary digits in the positions $i \equiv 2 \pmod 3$ to zero. Then for every natural
number $n$, the meta-automatic sequence $\mathcal{M}_2$ and the Thue–Morse sequence $t$ satisfy
$\mathcal{M}_2(n) = t(q(n))$. Moreover, writing the base-$4$ digits of $n$ as
$d_k = \lfloor n / 4^k \rfloor \bmod 4 = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$, we have
$q(n) = \sum_{k=0}^{n} d'_k 4^k$, where $d'_k = d_k$ if $k \equiv 0 \pmod 3$, $d'_k = 2 j_k$ if
$k \equiv 1 \pmod 3$, and $d'_k = i_k$ if $k \equiv 2 \pmod 3$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Theorem 26 (`jis-2026-26.4.1-thm-26`). -/
public theorem metaAutomaticTwo_eq_thueMorse_mask (q : ℕ → ℕ)
    (hq : ∀ m, q m = ∑ i ∈ (Finset.range (m + 1)).filter (fun i => i % 3 ≠ 2),
      m / 2 ^ i % 2 * 2 ^ i) (n : ℕ) :
    metaAutomaticTwo n = thueMorse (q n) ∧
      q n = ∑ k ∈ Finset.range (n + 1),
        (if k % 3 = 0 then n / 4 ^ k % 4
          else if k % 3 = 1 then 2 * (n / 4 ^ k % 4 / 2) else n / 4 ^ k % 4 % 2) * 4 ^ k := by
  have hqn : q n = maskSum n (n + 1) := by
    rw [hq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i % 3 = 2 <;> simp [maskTerm, h]
  rw [hqn]
  refine ⟨metaAutomaticTwo_eq_maskSum n, ?_⟩
  rw [← maskSum_extend n (2 * (n + 1)) (by omega), maskSum, sum_range_pairs]
  exact Finset.sum_congr rfl fun k _ => maskTerm_pair n k

end MetaMathlibExt
