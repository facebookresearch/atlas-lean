/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Product recurrence for three gibonacci sequences -/

namespace MetaMathlibExt

-- Express three consecutive values using the two preceding values.
private theorem gibonacci_window (X : ℤ → ℝ) (hX : ∀ j : ℤ, X (j + 2) = X (j + 1) + X j)
    (j : ℤ) :
    X (j - 1) = X (j - 3) + X (j - 2) ∧
      X j = X (j - 3) + 2 * X (j - 2) ∧
      X (j + 1) = 2 * X (j - 3) + 3 * X (j - 2) := by
  have hprev : X (j - 1) = X (j - 2) + X (j - 3) := by
    simpa only [show j - 3 + 2 = j - 1 by omega, show j - 3 + 1 = j - 2 by omega]
      using hX (j - 3)
  have hmid : X j = X (j - 1) + X (j - 2) := by
    simpa only [show j - 2 + 2 = j by omega, show j - 2 + 1 = j - 1 by omega]
      using hX (j - 2)
  have hnext : X (j + 1) = X j + X (j - 1) := by
    simpa only [show j - 1 + 2 = j + 1 by omega, show j - 1 + 1 = j by omega]
      using hX (j - 1)
  refine ⟨hprev.trans (add_comm _ _), ?_, ?_⟩
  · rw [hmid, hprev]
    ring
  · rw [hnext, hmid, hprev]
    ring

/-- **Product recurrence for three gibonacci sequences.** Let
$G, H, I : \mathbb{Z} \to \mathbb{R}$, written $j \mapsto G_j$, $j \mapsto H_j$ and
$j \mapsto I_j$, satisfy $G_{j+2} = G_{j+1} + G_j$, $H_{j+2} = H_{j+1} + H_j$ and
$I_{j+2} = I_{j+1} + I_j$ for every integer $j$. Then for all integers $k$, $r$ and $s$,
$$
G_{k+1} H_{r+1} I_{s+1} = 3 G_k H_r I_s + 6 G_{k-1} H_{r-1} I_{s-1} -
3 G_{k-2} H_{r-2} I_{s-2} - G_{k-3} H_{r-3} I_{s-3}.
$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 25
(`jis-2024-24.6.2-prop-25`). -/
public theorem gibonacci_triple_product_recurrence
    (G H I : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
    (hH : ∀ j : ℤ, H (j + 2) = H (j + 1) + H j)
    (hI : ∀ j : ℤ, I (j + 2) = I (j + 1) + I j) (k r s : ℤ) :
    G (k + 1) * H (r + 1) * I (s + 1) =
      3 * G k * H r * I s + 6 * G (k - 1) * H (r - 1) * I (s - 1) -
        3 * G (k - 2) * H (r - 2) * I (s - 2) - G (k - 3) * H (r - 3) * I (s - 3) := by
  obtain ⟨g₁, g₂, g₃⟩ := gibonacci_window G hG k
  obtain ⟨h₁, h₂, h₃⟩ := gibonacci_window H hH r
  obtain ⟨i₁, i₂, i₃⟩ := gibonacci_window I hI s
  rw [g₁, g₂, g₃, h₁, h₂, h₃, i₁, i₂, i₃]
  ring

end MetaMathlibExt
