/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Candido-type identities for gibonacci sequences

The recurrence expresses the third value of each sequence in terms of its preceding two,
reducing both identities to polynomial identities in the initial pairs.
-/

namespace MetaMathlibExt

/-- **Two-sequence Candido-type identity for gibonacci sequences.** Let $G$ and $H$ be gibonacci
sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with $X_{j+2} = X_{j+1} + X_j$
for every integer $j$. Then for all integers $r$ and $k$,

$$
2 (H_r G_k^3 + H_{r+1} G_{k+1}^3 + H_{r+2} G_{k+2}^3) =
(G_k^2 + G_{k+1}^2 + G_{k+2}^2)(H_r G_k + H_{r+1} G_{k+1} + H_{r+2} G_{k+2}).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 37
(`jis-2024-24.6.2-prop-37`). -/
public theorem gibonacci_candido_two_sequence
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (r k : ℤ) :
    2 * (H r * G k ^ 3 + H (r + 1) * G (k + 1) ^ 3 + H (r + 2) * G (k + 2) ^ 3) =
      (G k ^ 2 + G (k + 1) ^ 2 + G (k + 2) ^ 2) *
        (H r * G k + H (r + 1) * G (k + 1) + H (r + 2) * G (k + 2)) := by
  rw [hG k, hH r]
  ring

/-- **Four-sequence Candido-type identity for gibonacci sequences.** Let $G$, $H$, $M$, $N$ be
gibonacci sequences, that is, functions $X : \mathbb{Z} \to \mathbb{R}$ with
$X_{j+2} = X_{j+1} + X_j$ for every integer $j$. For two such sequences $X$, $Y$ and integers
$x$, $y$ write $T(X, x; Y, y) = X_x Y_y + X_{x+1} Y_{y+1} + X_{x+2} Y_{y+2}$. Then for all
integers $k$, $r$, $s$, $t$,

$$
6 (G_k H_r M_s N_t + G_{k+1} H_{r+1} M_{s+1} N_{t+1} + G_{k+2} H_{r+2} M_{s+2} N_{t+2}) =
T(G, k; M, s) \, T(H, r; N, t) + T(G, k; H, r) \, T(M, s; N, t) +
T(G, k; N, t) \, T(H, r; M, s).
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 38
(`jis-2024-24.6.2-prop-38`). -/
public theorem gibonacci_candido_four_sequence
    (G H M N : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hM : ∀ j : ℤ, M (j + 2) = M (j + 1) + M j)
    (hN : ∀ j : ℤ, N (j + 2) = N (j + 1) + N j) (k r s t : ℤ) :
    6 * (G k * H r * M s * N t + G (k + 1) * H (r + 1) * M (s + 1) * N (t + 1) +
        G (k + 2) * H (r + 2) * M (s + 2) * N (t + 2)) =
      (G k * M s + G (k + 1) * M (s + 1) + G (k + 2) * M (s + 2)) *
          (H r * N t + H (r + 1) * N (t + 1) + H (r + 2) * N (t + 2)) +
        (G k * H r + G (k + 1) * H (r + 1) + G (k + 2) * H (r + 2)) *
          (M s * N t + M (s + 1) * N (t + 1) + M (s + 2) * N (t + 2)) +
        (G k * N t + G (k + 1) * N (t + 1) + G (k + 2) * N (t + 2)) *
          (H r * M s + H (r + 1) * M (s + 1) + H (r + 2) * M (s + 2)) := by
  rw [hG k, hH r, hM s, hN t]
  ring

end MetaMathlibExt
