/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The arithmetic of de Jong's lower bound for the self-intersection of `ω`

R. de Jong, *Arakelov invariants of Riemann surfaces*, Doc. Math. 10 (2005), 311–329, proves in
Proposition 5.6 (p. 323) a lower bound for the Arakelov self-intersection `(ω, ω)` of the relative
dualizing sheaf of a semistable arithmetic surface of genus `g ≥ 2`. The proof combines the
identity `½ g(g + 1)(ω, ω) = (𝒲, ω) + (2g - 2) A` with the bound `(𝒲, ω) ≥ ¼ (g + 1)(ω, ω)`;
this file proves the resulting real inequality, `DeJong.le_of_half_mul_eq_add_of_le`.
-/

@[expose] public section

namespace DeJong

/-- **The arithmetic of de Jong's lower bound.** Let `g ≥ 1` be an integer and `e, w, A` real
numbers with `½ g(g + 1) e = w + (2g - 2) A` and `w ≥ ¼ (g + 1) e`. Then
`e ≥ 8(g - 1) A / ((2g - 1)(g + 1))`.
The source has `g ≥ 2`; `g ≥ 1` suffices. It fails for `g = 0`: `e = -1`, `w = A = 0` satisfy
both hypotheses but not the conclusion `e ≥ 0`.

R. de Jong, *Arakelov invariants of Riemann surfaces*, Doc. Math. 10 (2005), proof of
Proposition 5.6, p. 323 ("Using this in the first equality gives the required lower bound"), with
`e = (ω, ω)`, `w = (𝒲, ω)` and `A = ∑ₛ log R(𝒳ₛ) + ∑_σ log R(𝒳_σ) + deg det p_* ω`. -/
theorem le_of_half_mul_eq_add_of_le (g : ℕ) (hg : 1 ≤ g) (e w A : ℝ)
    (heq : 1 / 2 * g * (g + 1) * e = w + (2 * g - 2) * A) (hw : 1 / 4 * (g + 1) * e ≤ w) :
    8 * ((g : ℝ) - 1) * A / ((2 * g - 1) * (g + 1)) ≤ e := by
  have hG : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hpos : 0 < (2 * (g : ℝ) - 1) * (g + 1) := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith

end DeJong
