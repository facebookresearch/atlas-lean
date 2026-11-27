/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# A two-sequence gibonacci identity with a Fibonacci factor

A gibonacci sequence is a function `G : ℤ → ℝ` with `G (j + 2) = G (j + 1) + G j` for every
integer `j`; its seeds `G 0` and `G 1` are arbitrary. Write `F_m` for the signed Fibonacci
number `Int.fib m`. For gibonacci sequences `G`, `H` and integers `r`, `s`, `k`,
`gibonacci_mul_add_neg_one_pow_eq_fib_mul` proves

`H_s G_(k+r) + (-1)^(r-1) H_(s-r) G_k = F_r (G_0 H_(k+s-1) + G_1 H_(k+s))`.

## Proof outline

* Two gibonacci sequences that agree at `0` and `1` agree everywhere, by induction upwards and
  downwards from `0`.
* Hence the addition formula `G_(m+n) = F_(n-1) G_m + F_n G_(m+1)` holds for all integers `m`,
  `n` (both sides are gibonacci sequences in `n`), and
  `(-1)^(r-1) H_(s-r) = F_r H_(s-1) - F_(r-1) H_s` holds for all integers `r`, `s` (both sides
  are gibonacci sequences in `r`).
* With `G_(k+r) = F_(r-1) G_k + F_r G_(k+1)`, the left side becomes
  `F_r (G_k H_(s-1) + G_(k+1) H_s)`. Expanding `H_(k+s-1)`, `H_(k+s)`, `G_k` and `G_(k+1)` by the
  addition formula shows that `G_0 H_(k+s-1) + G_1 H_(k+s)` is the same sum
  `G_k H_(s-1) + G_(k+1) H_s`.

## References

* Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27
  (2024), Article 24.6.2. The identity is Proposition 28 of the preprint `arXiv:2311.06287v4`,
  where it is derived from Binet-type identities obtained from Fibonacci functions.
-/

@[expose] public section

namespace MetaMathlibExt

namespace gibonacci_mul_add_neg_one_pow_eq_fib_mul

/-- Two sequences with the gibonacci recurrence that agree at `0` and `1` agree everywhere. -/
private theorem eq_of_eq_zero_of_eq_one {u v : ℤ → ℝ}
    (hu : ∀ j : ℤ, u (j + 2) = u (j + 1) + u j) (hv : ∀ j : ℤ, v (j + 2) = v (j + 1) + v j)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (n : ℤ) : u n = v n := by
  have key : ∀ n : ℤ, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [show (i : ℤ) + 1 + 1 = i + 2 by ring, hu, hv, ih.1, ih.2]
    | pred i ih =>
      refine ⟨?_, by simpa using ih.1⟩
      have hu' := hu (-(i : ℤ) - 1)
      have hv' := hv (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 2 = -(i : ℤ) + 1 by ring,
        show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at hu' hv'
      linarith [ih.1, ih.2]
  exact (key n).1

/-- The recurrence `F_(n+1) = F_n + F_(n-1)`, written with the indices `n + 2 - 1` and
`n + 1 - 1` that occur when `n ↦ F_(n-1)` is shifted. -/
private theorem fib_add_two_sub_one (n : ℤ) :
    Int.fib (n + 2 - 1) = Int.fib (n + 1 - 1) + Int.fib (n - 1) := by
  have h := Int.fib_add_two (n - 1)
  rw [show n - 1 + 2 = n + 2 - 1 by ring, show n - 1 + 1 = n + 1 - 1 by ring] at h
  rw [h, add_comm]

/-- The addition formula `G_(m+n) = F_(n-1) G_m + F_n G_(m+1)` for a gibonacci sequence. -/
private theorem add_eq {G : ℤ → ℝ} (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (m n : ℤ) :
    G (m + n) = (Int.fib (n - 1) : ℝ) * G m + (Int.fib n : ℝ) * G (m + 1) := by
  refine eq_of_eq_zero_of_eq_one (u := fun n => G (m + n))
    (v := fun n => (Int.fib (n - 1) : ℝ) * G m + (Int.fib n : ℝ) * G (m + 1)) ?_ ?_ ?_ ?_ n
  · intro j
    rw [show m + (j + 2) = m + j + 2 by ring, show m + (j + 1) = m + j + 1 by ring]
    exact hG (m + j)
  · intro j
    rw [fib_add_two_sub_one, Int.fib_add_two]
    push_cast
    ring
  · simp
  · simp

/-- The negative shift `(-1)^(r-1) H_(s-r) = F_r H_(s-1) - F_(r-1) H_s` for a gibonacci
sequence. -/
private theorem neg_one_zpow_mul_sub {H : ℤ → ℝ} (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (s r : ℤ) :
    (-1 : ℝ) ^ (r - 1) * H (s - r) =
      (Int.fib r : ℝ) * H (s - 1) - (Int.fib (r - 1) : ℝ) * H s := by
  refine eq_of_eq_zero_of_eq_one (u := fun r => (-1 : ℝ) ^ (r - 1) * H (s - r))
    (v := fun r => (Int.fib r : ℝ) * H (s - 1) - (Int.fib (r - 1) : ℝ) * H s) ?_ ?_ ?_ ?_ r
  · intro j
    have hrec := hH (s - (j + 2))
    rw [show s - (j + 2) + 2 = s - j by ring, show s - (j + 2) + 1 = s - (j + 1) by ring]
      at hrec
    have e2 : (-1 : ℝ) ^ (j + 2 - 1) = (-1) ^ (j - 1) := by
      rw [show j + 2 - 1 = (j - 1) + 2 by ring, zpow_add₀ (by norm_num)]
      norm_num
    have e1 : (-1 : ℝ) ^ (j + 1 - 1) = -(-1) ^ (j - 1) := by
      rw [show j + 1 - 1 = (j - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]
      ring
    rw [e2, e1]
    linear_combination -((-1 : ℝ) ^ (j - 1)) * hrec
  · intro j
    rw [fib_add_two_sub_one, Int.fib_add_two]
    push_cast
    ring
  · simp
  · simp

end gibonacci_mul_add_neg_one_pow_eq_fib_mul

open gibonacci_mul_add_neg_one_pow_eq_fib_mul in
/-- **Addition formula for gibonacci sequences.** Let $F_m$ denote the Fibonacci numbers,
extended to all integers $m$ by $F_{-m} = (-1)^{m+1} F_m$. If $G : \mathbb{Z} \to \mathbb{R}$
satisfies $G_{j+2} = G_{j+1} + G_j$ for every integer $j$, then
$F_{k+1} G_{s+1} + F_k G_s = G_{k+s+1}$ for all integers $k$ and $s$.

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 20
(`jis-2024-24.6.2-prop-20`). -/
theorem fib_mul_gibonacci_add_eq_gibonacci
    (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) (k s : ℤ) :
    (Int.fib (k + 1) : ℝ) * G (s + 1) + (Int.fib k : ℝ) * G s = G (k + s + 1) := by
  rw [add_comm (_ * _) (_ * _), ← add_comm s k, add_assoc]
  simpa using (add_eq hG s (k + 1)).symm

open gibonacci_mul_add_neg_one_pow_eq_fib_mul in
/-- **Two-sequence gibonacci identity with a Fibonacci factor.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$, and let $F_m$ be
the Fibonacci numbers, extended to negative indices by $F_{-m} = (-1)^{m+1} F_m$. Then for all
integers $r$, $s$ and $k$,
$$
H_s G_{k+r} + (-1)^{r-1} H_{s-r} G_k = F_r (G_0 H_{k+s-1} + G_1 H_{k+s}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 35
(`jis-2024-24.6.2-prop-35`). -/
theorem gibonacci_mul_add_neg_one_pow_eq_fib_mul
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r s k : ℤ) :
    H s * G (k + r) + (-1 : ℝ) ^ (r - 1) * H (s - r) * G k =
      (Int.fib r : ℝ) * (G 0 * H (k + s - 1) + G 1 * H (k + s)) := by
  -- `G_(k+r) = F_(r-1) G_k + F_r G_(k+1)` and `(-1)^(r-1) H_(s-r) = F_r H_(s-1) - F_(r-1) H_s`.
  have hGkr := add_eq hG k r
  have hHsr := neg_one_zpow_mul_sub hH s r
  -- Expansions of `H_(k+s-1)`, `H_(k+s)`, `G_k` and `G_(k+1)` from the indices `s` and `0`.
  have hH1 : H (k + s - 1) = (Int.fib (k - 1) : ℝ) * H (s - 1) + (Int.fib k : ℝ) * H s := by
    have h := add_eq hH (s - 1) k
    rwa [show s - 1 + k = k + s - 1 by ring, sub_add_cancel] at h
  have hH2 : H (k + s) = (Int.fib (k - 1) : ℝ) * H s + (Int.fib k : ℝ) * H (s + 1) := by
    rw [add_comm]
    exact add_eq hH s k
  have hH3 : H (s + 1) = H s + H (s - 1) := by
    have h := hH (s - 1)
    rwa [show s - 1 + 2 = s + 1 by ring, sub_add_cancel] at h
  have hG1 : G k = (Int.fib (k - 1) : ℝ) * G 0 + (Int.fib k : ℝ) * G 1 := by
    have h := add_eq hG 0 k
    rwa [zero_add, zero_add] at h
  have hG2 := (fib_mul_gibonacci_add_eq_gibonacci G hG k 0).symm
  simp only [zero_add, add_zero] at hG2
  have hF : (Int.fib (k + 1) : ℝ) = Int.fib k + Int.fib (k - 1) := by
    have h := Int.fib_add_two (k - 1)
    rw [show k - 1 + 2 = k + 1 by ring, sub_add_cancel] at h
    rw [h]
    push_cast
    ring
  rw [hGkr, hH1, hH2]
  linear_combination G k * hHsr + H s * Int.fib r * hG2 + Int.fib r * H (s - 1) * hG1 -
    Int.fib r * G 1 * Int.fib k * hH3 + Int.fib r * G 1 * H s * hF

/-- **A sum of two gibonacci products in terms of the seeds.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all
integers $k$ and $s$,
$$
H_{k+1} G_{s+1} + H_k G_s = G_0 H_{k+s} + G_1 H_{k+s+1}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 21
(`jis-2024-24.6.2-prop-21`). -/
theorem gibonacci_mul_gibonacci_add_eq_seed_combination
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (k s : ℤ) :
    H (k + 1) * G (s + 1) + H k * G s = G 0 * H (k + s) + G 1 * H (k + s + 1) := by
  simpa [show s + (k + 1) = k + s + 1 by ring] using
    gibonacci_mul_add_neg_one_pow_eq_fib_mul G H hG hH 1 (k + 1) s

end MetaMathlibExt
