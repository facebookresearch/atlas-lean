/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring

/-!
# Seed expansion of a triple gibonacci product

A gibonacci sequence is a function `G : ℤ → ℝ` with `G (j + 2) = G (j + 1) + G j` for every
integer `j`. For gibonacci sequences `G`, `H`, `I` and integers `k`, `r`, `s`,
`gibonacci_triple_product_seed_identity` proves

`G_0 H_0 I_(k+r+s-2) + (G_0 H_1 + G_1 H_0) I_(k+r+s-1) + G_1 H_1 I_(k+r+s)
  = G_(s+1) H_(r+1) I_(k+1) + G_s H_r I_k - G_(s-1) H_(r-1) I_(k-1)`.

## Proof outline

Both sides, read as functions of any one of `k`, `r`, `s` with the other two fixed, satisfy the
gibonacci recurrence, since each is a linear combination of shifts of one gibonacci sequence. A
gibonacci sequence vanishing at `0` and `1` vanishes everywhere, so it suffices to check the
identity for `k`, `r`, `s ∈ {0, 1}`, where every value reduces to the seeds.

## References

* Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of Integer Sequences 27
  (2024), Article 24.6.2, Proposition 27.
-/

namespace MetaMathlibExt

namespace gibonacci_triple_product_seed_identity

/-- The gibonacci recurrence at indices `a`, `b = a + 1`, `c = a + 2`, written in any form. -/
private theorem rec_at {X : ℤ → ℝ} (hX : ∀ j : ℤ, X (j + 2) = X (j + 1) + X j)
    (a b c : ℤ) (hb : b = a + 1) (hc : c = a + 2) : X c = X b + X a := by
  subst hb hc
  exact hX a

/-- A sequence with the gibonacci recurrence that vanishes at `0` and `1` vanishes everywhere. -/
private theorem eq_zero {u : ℤ → ℝ} (hu : ∀ j : ℤ, u (j + 2) = u (j + 1) + u j)
    (h0 : u 0 = 0) (h1 : u 1 = 0) (n : ℤ) : u n = 0 := by
  have key : ∀ n : ℤ, u n = 0 ∧ u (n + 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      rw [show (i : ℤ) + 1 + 1 = i + 2 by ring, hu, ih.1, ih.2, add_zero]
    | pred i ih =>
      refine ⟨?_, by simpa using ih.1⟩
      have hu' := hu (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 2 = -(i : ℤ) + 1 by ring,
        show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at hu'
      linarith [ih.1, ih.2]
  exact (key n).1

/-- The values of a gibonacci sequence at `-2`, `-1`, `2` and `3` in terms of its seeds. -/
private theorem seed_values {X : ℤ → ℝ} (hX : ∀ j : ℤ, X (j + 2) = X (j + 1) + X j) :
    X (-2) = 2 * X 0 - X 1 ∧ X (-1) = X 1 - X 0 ∧ X 2 = X 0 + X 1 ∧ X 3 = X 0 + 2 * X 1 := by
  have e₁ := rec_at hX (-2) (-1) 0 (by norm_num) (by norm_num)
  have e₂ := rec_at hX (-1) 0 1 (by norm_num) (by norm_num)
  have e₃ := rec_at hX 0 1 2 (by norm_num) (by norm_num)
  have e₄ := rec_at hX 1 2 3 (by norm_num) (by norm_num)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end gibonacci_triple_product_seed_identity

open gibonacci_triple_product_seed_identity in
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
  -- The difference of the two sides.
  set D : ℤ → ℤ → ℤ → ℝ := fun k r s =>
    G 0 * H 0 * I (k + r + s - 2) + (G 0 * H 1 + G 1 * H 0) * I (k + r + s - 1) +
        G 1 * H 1 * I (k + r + s) -
      (G (s + 1) * H (r + 1) * I (k + 1) + G s * H r * I k -
        G (s - 1) * H (r - 1) * I (k - 1)) with hD
  -- `D` satisfies the gibonacci recurrence in each variable.
  have hk : ∀ r s k : ℤ, D (k + 2) r s = D (k + 1) r s + D k r s := by
    intro r s k
    simp only [hD]
    linear_combination
      G 0 * H 0 * rec_at hI (k + r + s - 2) (k + 1 + r + s - 2) (k + 2 + r + s - 2)
          (by ring) (by ring) +
        (G 0 * H 1 + G 1 * H 0) *
          rec_at hI (k + r + s - 1) (k + 1 + r + s - 1) (k + 2 + r + s - 1) (by ring) (by ring) +
        G 1 * H 1 * rec_at hI (k + r + s) (k + 1 + r + s) (k + 2 + r + s) (by ring) (by ring) -
        G (s + 1) * H (r + 1) * rec_at hI (k + 1) (k + 1 + 1) (k + 2 + 1) (by ring) (by ring) -
        G s * H r * rec_at hI k (k + 1) (k + 2) (by ring) (by ring) +
        G (s - 1) * H (r - 1) * rec_at hI (k - 1) (k + 1 - 1) (k + 2 - 1) (by ring) (by ring)
  have hr : ∀ k s r : ℤ, D k (r + 2) s = D k (r + 1) s + D k r s := by
    intro k s r
    simp only [hD]
    linear_combination
      G 0 * H 0 * rec_at hI (k + r + s - 2) (k + (r + 1) + s - 2) (k + (r + 2) + s - 2)
          (by ring) (by ring) +
        (G 0 * H 1 + G 1 * H 0) *
          rec_at hI (k + r + s - 1) (k + (r + 1) + s - 1) (k + (r + 2) + s - 1)
            (by ring) (by ring) +
        G 1 * H 1 * rec_at hI (k + r + s) (k + (r + 1) + s) (k + (r + 2) + s) (by ring) (by ring) -
        G (s + 1) * I (k + 1) * rec_at hH (r + 1) (r + 1 + 1) (r + 2 + 1) (by ring) (by ring) -
        G s * I k * rec_at hH r (r + 1) (r + 2) (by ring) (by ring) +
        G (s - 1) * I (k - 1) * rec_at hH (r - 1) (r + 1 - 1) (r + 2 - 1) (by ring) (by ring)
  have hs : ∀ k r s : ℤ, D k r (s + 2) = D k r (s + 1) + D k r s := by
    intro k r s
    simp only [hD]
    linear_combination
      G 0 * H 0 * rec_at hI (k + r + s - 2) (k + r + (s + 1) - 2) (k + r + (s + 2) - 2)
          (by ring) (by ring) +
        (G 0 * H 1 + G 1 * H 0) *
          rec_at hI (k + r + s - 1) (k + r + (s + 1) - 1) (k + r + (s + 2) - 1)
            (by ring) (by ring) +
        G 1 * H 1 * rec_at hI (k + r + s) (k + r + (s + 1)) (k + r + (s + 2)) (by ring) (by ring) -
        H (r + 1) * I (k + 1) * rec_at hG (s + 1) (s + 1 + 1) (s + 2 + 1) (by ring) (by ring) -
        H r * I k * rec_at hG s (s + 1) (s + 2) (by ring) (by ring) +
        H (r - 1) * I (k - 1) * rec_at hG (s - 1) (s + 1 - 1) (s + 2 - 1) (by ring) (by ring)
  -- `D` vanishes when `k`, `r`, `s ∈ {0, 1}`.
  obtain ⟨g₁, g₂, g₃, g₄⟩ := seed_values hG
  obtain ⟨h₁, h₂, h₃, h₄⟩ := seed_values hH
  obtain ⟨i₁, i₂, i₃, i₄⟩ := seed_values hI
  have base : ∀ k ∈ ({0, 1} : Set ℤ), ∀ r ∈ ({0, 1} : Set ℤ), ∀ s ∈ ({0, 1} : Set ℤ),
      D k r s = 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro k (rfl | rfl) r (rfl | rfl) s (rfl | rfl) <;>
      · simp only [hD]
        norm_num [g₁, g₂, g₃, g₄, h₁, h₂, h₃, h₄, i₁, i₂, i₃, i₄]
        ring
  -- Propagate from `{0, 1}³` to all of `ℤ³`, one variable at a time.
  have hD0 : D k r s = 0 := by
    refine eq_zero (u := fun s => D k r s) (hs k r) ?_ ?_ s <;>
    · refine eq_zero (u := fun r => D k r _) (fun r => hr k _ r) ?_ ?_ r <;>
      · refine eq_zero (u := fun k => D k _ _) (fun k => hk _ _ k) ?_ ?_ k <;>
        · exact base _ (by simp) _ (by simp) _ (by simp)
  simp only [hD] at hD0
  linarith

end MetaMathlibExt
