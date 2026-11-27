/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Shifted products of two gibonacci sequences -/

namespace MetaMathlibExt

/-- **Shifted product identity for two gibonacci sequences.** Let
$G, H : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$ and $j \mapsto H_j$, satisfy
$G_{j+2} = G_{j+1} + G_j$ and $H_{j+2} = H_{j+1} + H_j$ for every integer $j$. Then for all
integers $s$ and $k$,
$$
G_{k+1} H_{s+1} + G_{k-2} H_{s-2} = 2 G_k H_s + 2 G_{k-1} H_{s-1}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 24
(`jis-2024-24.6.2-prop-24`). -/
public theorem gibonacci_product_shift_identity
    (G H : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j) (s k : ℤ) :
    G (k + 1) * H (s + 1) + G (k - 2) * H (s - 2) = 2 * G k * H s + 2 * G (k - 1) * H (s - 1) := by
  -- Express both outer terms in the two middle terms of each sequence.
  have shifts (X : ℤ → ℝ) (hX : ∀ j : ℤ, X (j + 2) = X (j + 1) + X j) (j : ℤ) :
      X (j + 1) = X j + X (j - 1) ∧ X (j - 2) = X j - X (j - 1) := by
    constructor
    · simpa only [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega]
        using hX (j - 1)
    · have hmid : X j = X (j - 1) + X (j - 2) := by
        simpa only [show j - 2 + 2 = j by omega, show j - 2 + 1 = j - 1 by omega]
          using hX (j - 2)
      rw [hmid, add_sub_cancel_left]
  obtain ⟨gNext, gPrev⟩ := shifts G hG k
  obtain ⟨hNext, hPrev⟩ := shifts H hH s
  rw [gNext, gPrev, hNext, hPrev]
  ring

end MetaMathlibExt
