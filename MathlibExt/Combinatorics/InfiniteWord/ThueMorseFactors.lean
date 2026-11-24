/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.InfiniteWord.Factor
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Complementation of Thue–Morse factors -/

namespace MetaMathlibExt

@[expose] public section

-- Adding a new leading binary one changes the parity of the number of ones.
private theorem thueMorse_add_two_pow {x k : ℕ} (hx : x < 2 ^ k) :
    thueMorse (x + 2 ^ k) = !thueMorse x := by
  let d := (Nat.digits 2 x).length
  have hd : d ≤ k := (Nat.digits_length_le_iff (by decide) x).2 hx
  have hdigits := Nat.digits_append_zeroes_append_digits
    (b := 2) (k := k - d) (m := 1) (n := x) (by decide) (by decide)
  rw [show (Nat.digits 2 x).length + (k - d) = k from Nat.add_sub_of_le hd, Nat.mul_one]
    at hdigits
  have hc : (Nat.digits 2 (x + 2 ^ k)).count 1 = (Nat.digits 2 x).count 1 + 1 := by
    rw [← hdigits]
    simp [List.count_append, List.count_replicate]
  have hparity : ((Nat.digits 2 x).count 1 + 1) % 2 = 1 ↔
      ¬ (Nat.digits 2 x).count 1 % 2 = 1 := by omega
  simp only [thueMorse, hc, hparity]
  by_cases h : (Nat.digits 2 x).count 1 % 2 = 1 <;> simp [h]

/-- **Factors of the Thue–Morse word are closed under complement.** For every natural number
$n$, if a binary word $v$ of length $n$ is a factor of the Thue–Morse sequence, then so is the
word obtained from $v$ by exchanging $0$ and $1$ in every position.

Source: John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.1, Lemma 29 (`jis-2026-26.4.1-lem-29`). -/
public theorem thueMorse_factor_complement (n : ℕ) (v : Fin n → Bool)
    (hv : v ∈ InfiniteWord.factorSet thueMorse n) :
    (fun i => !v i) ∈ InfiniteWord.factorSet thueMorse n := by
  obtain ⟨s, rfl⟩ := InfiniteWord.mem_factorSet.mp hv
  let k := (Nat.digits 2 (s + n)).length
  have hk : s + n < 2 ^ k := Nat.lt_base_pow_length_digits (by decide)
  apply InfiniteWord.mem_factorSet.mpr
  refine ⟨s + 2 ^ k, ?_⟩
  funext j
  simp only [InfiniteWord.factor_apply, Nat.add_right_comm s (2 ^ k) (j : ℕ)]
  exact thueMorse_add_two_pow ((Nat.add_lt_add_left j.isLt s).trans hk)

end

end MetaMathlibExt
