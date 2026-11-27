/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander

@[expose] public section

open MathlibExt.Combinatorics.SpectralExpander

namespace MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander

/-- Non-vacuity: the complete graph `K₄` is a `3`-regular spectral expander with `λ = 1 / 3`. -/
theorem k4 : IsSpectralExpander (⊤ : SimpleGraph (Fin 4)) 3 (1 / 3) := by
  have h := isSpectralExpander_top (V := Fin 4) (by simp)
  simp only [Fintype.card_fin] at h
  norm_num at h ⊢
  exact h

/-- The expander mixing lemma applied to `K₄`, with `S = {0, 1}` and `T = {2, 3}`. -/
example :
    |((⊤ : SimpleGraph (Fin 4)).interedges {0, 1} {2, 3}).card / (Fintype.card (Fin 4) * 3 : ℝ) -
        ({0, 1} : Finset (Fin 4)).card / Fintype.card (Fin 4) *
          (({2, 3} : Finset (Fin 4)).card / Fintype.card (Fin 4))| ≤
      1 / 3 * √(({0, 1} : Finset (Fin 4)).card / Fintype.card (Fin 4) *
          (1 - ({0, 1} : Finset (Fin 4)).card / Fintype.card (Fin 4)) *
        (({2, 3} : Finset (Fin 4)).card / Fintype.card (Fin 4) *
          (1 - ({2, 3} : Finset (Fin 4)).card / Fintype.card (Fin 4)))) :=
  expander_mixing_lemma k4 (by norm_num) _ _

/-- The elementary lower bound `d (N - d) ≤ (d λ)² (N - 1)` is an equality for `K₄`
(`3 · 1 = 1 · 3`). -/
example : (3 : ℝ) * (4 - 3) = (3 * (1 / 3)) ^ 2 * (4 - 1) := by norm_num

example : (3 : ℝ) * (Fintype.card (Fin 4) - 3) ≤ (3 * (1 / 3)) ^ 2 * (Fintype.card (Fin 4) - 1) :=
  by exact_mod_cast mul_sub_le_sq_mul_of_isSpectralExpander k4 (by simp)

/-- Random-walk probabilities on `K₄` have total mass one. -/
example (t : ℕ) : walkProb (⊤ : SimpleGraph (Fin 4)) 3 k4.1 (by norm_num) t (fun _ => True) = 1 :=
  walkProb_true k4.1 (by norm_num) t

/-! The walk probabilities need a `d`-regular graph with `d ≥ 1`: for the edgeless graph with
`d = 0`, under which every event would have probability `0`, the proof of `0 < d` cannot be
given. -/

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ :=
  walkProb (⊥ : SimpleGraph (Fin 2)) 0 (fun v => by simp) (by norm_num) 1 fun _ => True

end MathlibExtTest.Combinatorics.SimpleGraph.SpectralExpander
