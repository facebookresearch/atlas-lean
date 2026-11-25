/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse

/-!
# The Thue–Morse quarto sequence

At each positive index, the quarto bit is the XOR of the Thue–Morse bit and the parity of the
index of the leading binary digit (counting from zero).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Thue–Morse quarto sequence.** The Thue–Morse quarto sequence
$\mathcal{Q} : \mathbb{N} \to \{0, 1\}$ (OEIS A298952, with $\mathcal{Q}(0) = 0$) is given by
$\mathcal{Q}(0) = 0$, $\mathcal{Q}(1) = 1$ and, for every $m \ge 2$, writing $m = 4n + r$ with
$n \ge 0$ and $0 \le r \le 3$: $\mathcal{Q}(m) = \mathcal{Q}(n)$ if $r = 0$,
$\mathcal{Q}(m) = 1 - \mathcal{Q}(n)$ if $r = 1$, $\mathcal{Q}(m) = \mathcal{Q}(2n)$ if $r = 2$,
and $\mathcal{Q}(m) = 1 - \mathcal{Q}(2n)$ if $r = 3$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2 (definition of `𝒬`). -/
public def thueMorseQuarto : ℕ → Bool
  | 0 => false
  | 1 => true
  | n + 2 =>
    match (n + 2) % 4 with
    | 0 => thueMorseQuarto ((n + 2) / 4)
    | 1 => !thueMorseQuarto ((n + 2) / 4)
    | 2 => thueMorseQuarto (2 * ((n + 2) / 4))
    | _ => !thueMorseQuarto (2 * ((n + 2) / 4))
termination_by n => n
decreasing_by all_goals omega

/-- **First sixteen terms of the Thue–Morse quarto sequence.** The values
$\mathcal{Q}(0), \mathcal{Q}(1), \ldots, \mathcal{Q}(15)$ of the Thue–Morse quarto sequence
$\mathcal{Q}$ are $0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1$, in this order.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_small : (List.range 16).map thueMorseQuarto =
    [false, true, false, true, true, false, false, true, false, true, true, false, true,
      false, false, true] := by
  simp [List.range_succ, thueMorseQuarto]

/-- **Recurrences of the Thue–Morse quarto sequence.** The Thue–Morse quarto sequence
$\mathcal{Q}$ satisfies $\mathcal{Q}(4n) = \mathcal{Q}(n)$ and
$\mathcal{Q}(4n+1) = 1 - \mathcal{Q}(n)$ for every $n \ge 1$, and
$\mathcal{Q}(4n+2) = \mathcal{Q}(2n)$ and $\mathcal{Q}(4n+3) = 1 - \mathcal{Q}(2n)$ for every
$n \ge 0$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Section 2.2. -/
public theorem thueMorseQuarto_rec (n : ℕ) :
    (1 ≤ n → thueMorseQuarto (4 * n) = thueMorseQuarto n) ∧
      (1 ≤ n → thueMorseQuarto (4 * n + 1) = !thueMorseQuarto n) ∧
      thueMorseQuarto (4 * n + 2) = thueMorseQuarto (2 * n) ∧
      thueMorseQuarto (4 * n + 3) = !thueMorseQuarto (2 * n) := by
  refine ⟨fun hn => ?_, fun hn => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n = k + 2 := ⟨4 * n - 2, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 0 by omega, show (k + 2) / 4 = n by omega]
  · obtain ⟨k, hk⟩ : ∃ k, 4 * n + 1 = k + 2 := ⟨4 * n - 1, by omega⟩
    rw [hk, thueMorseQuarto]
    simp only [show (k + 2) % 4 = 1 by omega, show (k + 2) / 4 = n by omega]
  · rw [show 4 * n + 2 = 4 * n + 2 from rfl, thueMorseQuarto]
    simp only [show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 2) / 4 = n by omega]
  · rw [show 4 * n + 3 = (4 * n + 1) + 2 by omega, thueMorseQuarto]
    simp only [show (4 * n + 1 + 2) % 4 = 3 by omega, show (4 * n + 1 + 2) / 4 = n by omega]

/-- **Thue–Morse quarto sequence from the Thue–Morse sequence.** Let $\mathcal{Q}$ be the
Thue–Morse quarto sequence and $t$ the Thue–Morse sequence, and let $d(0) = 0$ and
$d(n) = \lfloor \log_2 n \rfloor \bmod 2$ for $n \ge 1$. Then for every $n \ge 0$,
$\mathcal{Q}(n) = t(n) \oplus d(n)$, where $\oplus$ is addition modulo $2$.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Proposition 8 (`jis-2026-26.4.1-prop-8`). -/
public theorem thueMorseQuarto_eq_xor (n : ℕ) :
    thueMorseQuarto n = xor (thueMorse n) (decide (Nat.log 2 n % 2 = 1)) := by
  let f (m : ℕ) := xor (thueMorse m) (decide (Nat.log 2 m % 2 = 1))
  -- Appending either bit flips the log parity. Only a one flips the Thue–Morse bit.
  have step (m : ℕ) (hm : 0 < m) : f (2 * m) = !f m ∧ f (2 * m + 1) = f m := by
    have flip (k : ℕ) : decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
      simp only [← decide_not, decide_eq_decide]
      omega
    have digits (b : Bool) : Nat.digits 2 (Nat.bit b m) = b.toNat :: Nat.digits 2 m := by
      rw [Nat.bit_val, Nat.add_comm, Nat.digits_add 2 (by decide) _ _ b.toNat_lt (Or.inr hm.ne')]
    change f (Nat.bit false m) = !f m ∧ f (Nat.bit true m) = f m
    simp only [f, thueMorse, digits, Nat.log_two_bit hm.ne']
    simp [flip]
  change thueMorseQuarto n = f n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n < 4
    · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      all_goals decide +kernel
    let k := n / 4
    have hk : 0 < k := by omega
    obtain ⟨q₀, q₁, q₂, q₃⟩ := thueMorseQuarto_rec k
    obtain ⟨even, odd⟩ := step k hk
    obtain ⟨even₀, odd₀⟩ := step (2 * k) (by omega)
    obtain ⟨even₁, odd₁⟩ := step (2 * k + 1) (by omega)
    have ih₁ := ih k (by omega)
    have ih₂ := ih (2 * k) (by omega)
    obtain h | h | h | h : n = 4 * k ∨ n = 4 * k + 1 ∨ n = 4 * k + 2 ∨ n = 4 * k + 3 := by
      omega
    · rw [h, q₀ hk, ih₁, show 4 * k = 2 * (2 * k) by omega, even₀, even, Bool.not_not]
    · rw [h, q₁ hk, ih₁, show 4 * k = 2 * (2 * k) by omega, odd₀, even]
    · rw [h, q₂, ih₂, show 4 * k + 2 = 2 * (2 * k + 1) by omega, even₁, odd, even]
    · rw [h, q₃, ih₂, show 4 * k + 3 = 2 * (2 * k + 1) + 1 by omega, odd₁, odd, even,
        Bool.not_not]

end

end MetaMathlibExt
