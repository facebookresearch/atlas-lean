/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Finance.FiniteTreeError

/-!
# Tests for the finite-tree backward-induction error bound

Boundary instantiations of `finite_tree_error_bound` (unit discount,
horizon zero, probability endpoints, zero residual, expanding discount),
an independently computed one-step numeric pin, and the native `snell`
corollary exercised at the root.
-/

open Cslib.Algorithms.Lean.Finance.FiniteTreeError

/-- `disc = 1`: the geometric sum is `N`, so the bound is `ε * N`. -/
example (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (1 * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (1 * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (N : ℕ) (s : List Bool) : |E N s - V N s| ≤ ε * N := by
  have h := finite_tree_error_bound p 1 ε hp0 hp1 (by norm_num) hε g E V hE0
    hEsucc hV0 hVerr N s
  have h1 : ∑ j ∈ Finset.range N, (1:ℝ) ^ j = N := by simp
  rw [h1] at h
  exact h

/-- `N = 0`: the bound is `0`. -/
example (p disc ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hdisc : 0 < disc)
    (hε : 0 ≤ ε) (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ)
    (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))|
      ≤ ε)
    (s : List Bool) : |E 0 s - V 0 s| ≤ 0 := by
  have h := finite_tree_error_bound p disc ε hp0 hp1 hdisc hε g E V hE0 hEsucc
    hV0 hVerr 0 s
  simpa using h

/-- `p = 0` endpoint: only the down branch matters; bound shape unchanged. -/
example (disc ε : ℝ) (hdisc : 0 < disc) (hε : 0 ≤ ε)
    (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (0 * E k (true :: s) + (1 - 0) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (0 * V k (true :: s) + (1 - 0) * V k (false :: s)))|
      ≤ ε)
    (N : ℕ) (s : List Bool) :
    |E N s - V N s| ≤ ε * ∑ j ∈ Finset.range N, disc ^ j :=
  finite_tree_error_bound 0 disc ε (le_refl 0) (by norm_num) hdisc hε g E V hE0
    hEsucc hV0 hVerr N s

/-- `p = 1` endpoint: only the up branch matters; bound shape unchanged. -/
example (disc ε : ℝ) (hdisc : 0 < disc) (hε : 0 ≤ ε)
    (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (1 * E k (true :: s) + (1 - 1) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (1 * V k (true :: s) + (1 - 1) * V k (false :: s)))|
      ≤ ε)
    (N : ℕ) (s : List Bool) :
    |E N s - V N s| ≤ ε * ∑ j ∈ Finset.range N, disc ^ j :=
  finite_tree_error_bound 1 disc ε (by norm_num) (le_refl 1) hdisc hε g E V hE0
    hEsucc hV0 hVerr N s

/-- `ε = 0`: exactness. -/
example (p disc : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hdisc : 0 < disc)
    (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (disc * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))|
      ≤ 0)
    (N : ℕ) (s : List Bool) : E N s = V N s := by
  have h := finite_tree_error_bound p disc 0 hp0 hp1 hdisc (le_refl 0) g E V hE0
    hEsucc hV0 hVerr N s
  simp only [zero_mul] at h
  have h0 : |E N s - V N s| = 0 := le_antisymm h (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp h0)

/-- `disc = 2 > 1`, `N = 3`: geometric growth, bound `ε * 7`. -/
example (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (g : List Bool → ℝ) (E V : ℕ → List Bool → ℝ) (hE0 : E 0 = g)
    (hEsucc : ∀ k s, E (k + 1) s =
      max (g s) (2 * (p * E k (true :: s) + (1 - p) * E k (false :: s))))
    (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (2 * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (s : List Bool) : |E 3 s - V 3 s| ≤ ε * 7 := by
  have h := finite_tree_error_bound p 2 ε hp0 hp1 (by norm_num) hε g E V hE0
    hEsucc hV0 hVerr 3 s
  have h7 : ∑ j ∈ Finset.range 3, (2:ℝ) ^ j = 7 := by
    norm_num [Finset.sum_range_succ]
  rw [h7] at h
  exact h

/-- Explicit one-step tree: exact values are all `0` (`g ≡ 0`). -/
private noncomputable def Epin : ℕ → List Bool → ℝ
  | 0 => fun _ => 0
  | _ + 1 => fun _ => 0

/-- Explicit one-step tree: computed values err by `1/10` off the terminal. -/
private noncomputable def Vpin : ℕ → List Bool → ℝ
  | 0 => fun _ => 0
  | _ + 1 => fun _ => 1 / 10

private theorem Epin_all_zero (k : ℕ) (s : List Bool) : Epin k s = 0 := by
  cases k with
  | zero => rfl
  | succ n => rfl

private theorem hE0pin : Epin 0 = (fun _ : List Bool => (0:ℝ)) := rfl

private theorem hEsuccpin : ∀ k s, Epin (k + 1) s =
    max ((fun _ : List Bool => (0:ℝ)) s)
      ((1:ℝ) * ((1/2 : ℝ) * Epin k (true :: s)
        + (1 - 1/2) * Epin k (false :: s))) := by
  intro k s
  have h0 : Epin (k + 1) s = 0 := rfl
  have h1 : Epin k (true :: s) = 0 := Epin_all_zero _ _
  have h2 : Epin k (false :: s) = 0 := Epin_all_zero _ _
  rw [h0, h1, h2]
  simp only [mul_zero, add_zero, max_self]

private theorem hV0pin : Vpin 0 = (fun _ : List Bool => (0:ℝ)) := rfl

private theorem hVerrpin : ∀ k s, |Vpin (k + 1) s -
    max ((fun _ : List Bool => (0:ℝ)) s)
      ((1:ℝ) * ((1/2 : ℝ) * Vpin k (true :: s)
        + (1 - 1/2) * Vpin k (false :: s)))| ≤ (1/10 : ℝ) := by
  intro k s
  have hV : Vpin (k + 1) s = 1 / 10 := rfl
  rw [hV]
  cases k with
  | zero =>
      have h1 : Vpin 0 (true :: s) = 0 := rfl
      have h2 : Vpin 0 (false :: s) = 0 := rfl
      rw [h1, h2]
      simp only [mul_zero, add_zero, max_self]
      norm_num
  | succ j =>
      have h1 : Vpin (j + 1) (true :: s) = 1 / 10 := rfl
      have h2 : Vpin (j + 1) (false :: s) = 1 / 10 := rfl
      rw [h1, h2]
      have hinner : (1:ℝ) * ((1/2 : ℝ) * (1/10) + (1 - 1/2) * (1/10))
          = 1 / 10 := by norm_num
      rw [hinner]
      simp only [max_eq_right (by norm_num : (0:ℝ) ≤ 1 / 10)]
      norm_num

/-- Pin (a): the theorem applies to the explicit one-step tree. -/
example : |Epin 1 [] - Vpin 1 []|
    ≤ (1/10 : ℝ) * ∑ j ∈ Finset.range 1, (1:ℝ) ^ j :=
  finite_tree_error_bound (1/2) 1 (1/10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun _ => 0) Epin Vpin hE0pin hEsuccpin hV0pin
    hVerrpin 1 []

/-- Pin (b): both sides evaluate independently; the bound is tight. -/
example : |Epin 1 [] - Vpin 1 []| = 1 / 10 ∧
    (1/10 : ℝ) * ∑ j ∈ Finset.range 1, (1:ℝ) ^ j = 1 / 10 := by
  constructor
  · have hE : Epin 1 [] = 0 := rfl
    have hV : Vpin 1 [] = 1 / 10 := rfl
    rw [hE, hV]
    norm_num
  · norm_num [Finset.sum_range_succ]

/-- Importing-client check: the native `snell` corollary at the root. -/
example (p disc ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hdisc : 0 < disc)
    (hε : 0 ≤ ε) (g : List Bool → ℝ) (V : ℕ → List Bool → ℝ) (hV0 : V 0 = g)
    (hVerr : ∀ k s, |V (k + 1) s -
      max (g s) (disc * (p * V k (true :: s) + (1 - p) * V k (false :: s)))| ≤ ε)
    (N : ℕ) :
    |MathlibExt.Economics.Finance.BinomialOptimalStopping.snell p disc g N []
      - V N []| ≤ ε * ∑ j ∈ Finset.range N, disc ^ j :=
  snell_computed_abs_le p disc ε hp0 hp1 hdisc hε g V hV0 hVerr N []
