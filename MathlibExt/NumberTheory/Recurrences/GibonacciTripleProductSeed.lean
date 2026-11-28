/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.GibonacciFibonacciFactorIdentity

/-!
# Seed expansion of a triple gibonacci product

A gibonacci sequence is a function `G : ℤ → ℝ` with `G (j + 2) = G (j + 1) + G j` for every
integer `j`. For gibonacci sequences `G`, `H`, `I` and integers `k`, `r`, `s`,
`gibonacci_triple_product_seed_identity` proves

`G_0 H_0 I_(k+r+s-2) + (G_0 H_1 + G_1 H_0) I_(k+r+s-1) + G_1 H_1 I_(k+r+s)
  = G_(s+1) H_(r+1) I_(k+1) + G_s H_r I_k - G_(s-1) H_(r-1) I_(k-1)`.

## Proof outline

Write `X_n = G_0 H_n + G_1 H_(n+1)`; it is again a gibonacci sequence. By Adegoke's
Proposition 21 (`gibonacci_mul_gibonacci_add_eq_seed_combination`) applied to `G` and `H`,
`G_(s+1) H_(r+1) + G_s H_r = X_(r+s)` and `G_s H_r + G_(s-1) H_(r-1) = X_(r+s-2)`. Replacing
`I_(k+1)` by `I_k + I_(k-1)` turns the right side into `X_(r+s) I_k + X_(r+s-1) I_(k-1)`, and
Proposition 21 applied to `X` and `I` turns this into `X_0 I_(k+r+s-2) + X_1 I_(k+r+s-1)`, which
is the left side after replacing `I_(k+r+s)` by `I_(k+r+s-1) + I_(k+r+s-2)`.

## References

* Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27
  (2024), Article 24.6.2, Propositions 21 and 27.
-/

namespace MetaMathlibExt

/-- **Seed expansion of a triple gibonacci product.** Let $G, H, I \colon \mathbb{Z} \to \mathbb{R}$
satisfy $G_{j+2} = G_{j+1} + G_j$, $H_{j+2} = H_{j+1} + H_j$ and $I_{j+2} = I_{j+1} + I_j$ for
every integer $j$. Then for all integers $k$, $r$, $s$,
$$G_0 H_0 I_{k+r+s-2} + (G_0 H_1 + G_1 H_0) I_{k+r+s-1} + G_1 H_1 I_{k+r+s}
= G_{s+1} H_{r+1} I_{k+1} + G_s H_r I_k - G_{s-1} H_{r-1} I_{k-1}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 27
(`jis-2024-24.6.2-prop-27`). -/
public theorem gibonacci_triple_product_seed_identity
    (G H I : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j) (k r s : ℤ) :
    G 0 * H 0 * I (k + r + s - 2) + (G 0 * H 1 + G 1 * H 0) * I (k + r + s - 1) +
        G 1 * H 1 * I (k + r + s) =
      G (s + 1) * H (r + 1) * I (k + 1) + G s * H r * I k - G (s - 1) * H (r - 1) * I (k - 1) := by
  -- Proposition 21 for `G` and `H`, at `(r, s)` and at `(r - 1, s - 1)`.
  have hA := gibonacci_mul_gibonacci_add_eq_seed_combination G H hG hH r s
  have hC := gibonacci_mul_gibonacci_add_eq_seed_combination G H hG hH (r - 1) (s - 1)
  rw [sub_add_cancel, sub_add_cancel, show r - 1 + (s - 1) = r + s - 2 by ring,
    show r + s - 2 + 1 = r + s - 1 by ring] at hC
  -- `n ↦ G 0 * H n + G 1 * H (n + 1)` is a gibonacci sequence; Proposition 21 for it and `I`.
  have hX : ∀ j : ℤ, G 0 * H (j + 2) + G 1 * H (j + 2 + 1) =
      (G 0 * H (j + 1) + G 1 * H (j + 1 + 1)) + (G 0 * H j + G 1 * H (j + 1)) := by
    intro j
    rw [show j + 2 + 1 = j + 1 + 2 by ring, hH (j + 1), show j + 1 + 1 = j + 2 by ring]
    linear_combination G 0 * hH j
  have hXI := gibonacci_mul_gibonacci_add_eq_seed_combination
    (fun n => G 0 * H n + G 1 * H (n + 1)) I hX hI (k - 1) (r + s - 1)
  simp only [sub_add_cancel, zero_add] at hXI
  rw [show k - 1 + (r + s - 1) = k + r + s - 2 by ring,
    show k + r + s - 2 + 1 = k + r + s - 1 by ring, show (1 : ℤ) + 1 = 2 by norm_num] at hXI
  -- The recurrences used to shift indices.
  have hIk : I (k + 1) = I k + I (k - 1) := by
    have h := hI (k - 1)
    rwa [show k - 1 + 2 = k + 1 by ring, sub_add_cancel] at h
  have hIn : I (k + r + s) = I (k + r + s - 1) + I (k + r + s - 2) := by
    have h := hI (k + r + s - 2)
    rwa [show k + r + s - 2 + 2 = k + r + s by ring,
      show k + r + s - 2 + 1 = k + r + s - 1 by ring] at h
  have hH2 : H 2 = H 1 + H 0 := by simpa using hH 0
  have hHa : H (r + s) = H (r + s - 1) + H (r + s - 2) := by
    have h := hH (r + s - 2)
    rwa [show r + s - 2 + 2 = r + s by ring, show r + s - 2 + 1 = r + s - 1 by ring] at h
  have hHb : H (r + s + 1) = H (r + s) + H (r + s - 1) := by
    have h := hH (r + s - 1)
    rwa [show r + s - 1 + 2 = r + s + 1 by ring, sub_add_cancel] at h
  linear_combination -hXI + G 1 * H 1 * hIn - G 1 * I (k + r + s - 1) * hH2 -
    (I k + I (k - 1)) * hA + I (k - 1) * hC - I (k - 1) * (G 0 * hHa + G 1 * hHb) -
    G (s + 1) * H (r + 1) * hIk

end MetaMathlibExt
