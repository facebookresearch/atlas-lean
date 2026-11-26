/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An interval and a later progression

Kumar, Mohan, and Pandey study unions of the interval $I_n = \{0, 1, \dots, n - 1\}$ and a
finite arithmetic progression $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$ of real numbers.
With `realIntervalSet`, `realAPSet` and `IsMSTDSet` from
`MathlibExt.Combinatorics.Additive.IrrationalStepProgressions`, this file shows that
$I_n \cup J(x, m, d)$ is not an MSTD set for natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and
$x > n - 1$.

Write $A = I_n \cup J$. Then $A + A = (A + I_n) \cup (J + J)$, the set $A - I_n$ is a translate
of $A + I_n$, and $|J + J| \le 2m + 1$. The set $A - I_n$ lies in $[-(n - 1), \infty)$, while
the $2m + 1$ differences $0 - (x + id)$ for $0 \le i \le m$ and $1 - (x + id)$ for
$1 \le i \le m$ lie below $-(n - 1)$ and are distinct because $d > 1$. The argument uses only
$n \ge 2$ and real numbers $x > n - 1$ and $d > 1$.

For natural $x$ and $d$ this is a case of the source's Theorem 1, which its Lemmas 1 and 2 prove
for $x \ge n + 1$; its Lemma 3 treats $x \notin \mathbb{N}$.

## Main results

- `not_isMSTDSet_intervalAP_nat_of_lt`: for natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and
  $x > n - 1$, the set $I_n \cup J(x, m, d)$ is not an MSTD set.
-/

namespace MetaMathlibExt

open Pointwise

/-- The interval $I_n$ with $n \ge 2$ and a progression $J(x, m, d)$ of reals with $x > n - 1$
and $d > 1$ form no MSTD set. -/
private theorem not_isMSTDSet_intervalAP_of_lt {n m : ℕ} {x d : ℝ} (hn : 2 ≤ n)
    (hx : (n : ℝ) - 1 < x) (hd : 1 < d) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d) := by
  set I := realIntervalSet n
  set J := realAPSet x m d
  set A := I ∪ J
  have hI {y : ℝ} : y ∈ I ↔ ∃ i : ℕ, i < n ∧ (i : ℝ) = y := by
    simp [I, realIntervalSet]
  have hJ {y : ℝ} : y ∈ J ↔ ∃ i : ℕ, i < m + 1 ∧ x + i * d = y := by
    simp [J, realAPSet]
  have hd₀ : 0 < d := by linarith
  have hx₀ : 0 < x := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- Sums: `A + A = (A + I) ∪ (J + J)`, and `J + J` has at most `2m + 1` elements.
  have hsum : A + A ⊆ (A + I) ∪ (J + J) := by
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.mem_union_left _ (Finset.add_mem_add ha hb)
    rcases Finset.mem_union.mp ha with ha | ha
    · rw [add_comm a b]
      exact Finset.mem_union_left _ (Finset.add_mem_add (Finset.mem_union_right _ hb) ha)
    · exact Finset.mem_union_right _ (Finset.add_mem_add ha hb)
  have hJJ : (J + J).card ≤ 2 * m + 1 := by
    refine (Finset.card_le_card (t := (Finset.range (2 * m + 1)).image
      fun k : ℕ => 2 * x + k * d) ?_).trans (Finset.card_image_le.trans (by simp))
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨i, hi, rfl⟩ := hJ.mp ha
    obtain ⟨j, hj, rfl⟩ := hJ.mp hb
    refine Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), ?_⟩
    push_cast
    ring
  -- Translating by `-(n - 1)` maps `A + I` into `A - I`.
  have hshift : (A + I).card ≤ (A - I).card := by
    refine Finset.card_le_card_of_injOn (fun s => s - (n - 1)) ?_ fun s _ t _ h => by simpa using h
    intro s hs
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨i, hi, rfl⟩ := hI.mp hb
    refine Finset.mem_sub.mpr ⟨a, ha, ((n - 1 - i : ℕ) : ℝ), hI.mpr ⟨n - 1 - i, by omega, rfl⟩, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  -- `2m + 1` further differences lie below `-(n - 1)`, hence outside `A - I`.
  set N₀ := (Finset.range (m + 1)).image fun i : ℕ => 0 - (x + i * d)
  set N₁ := (Finset.Icc 1 m).image fun i : ℕ => 1 - (x + i * d)
  have hinj (c : ℝ) : Function.Injective fun i : ℕ => c - (x + i * d) := by
    intro i j h
    have : (i : ℝ) * d = j * d := by simpa using h
    exact_mod_cast mul_right_cancel₀ hd₀.ne' this
  have hN₀ : N₀.card = m + 1 := by
    rw [Finset.card_image_of_injective _ (hinj 0), Finset.card_range]
  have hN₁ : N₁.card = m := by
    rw [Finset.card_image_of_injective _ (hinj 1), Nat.card_Icc]
    omega
  have h0 : (0 : ℝ) ∈ I := hI.mpr ⟨0, by omega, by simp⟩
  have h1 : (1 : ℝ) ∈ I := hI.mpr ⟨1, by omega, by simp⟩
  have hlow : ∀ y ∈ A - I, 1 - (n : ℝ) ≤ y := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hy
    obtain ⟨i, hi, rfl⟩ := hI.mp hb
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have ha₀ : 0 ≤ a := by
      rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨j, -, rfl⟩ := hI.mp ha
        positivity
      · obtain ⟨j, -, rfl⟩ := hJ.mp ha
        positivity
    linarith
  have hdisj : Disjoint (A - I) (N₀ ∪ N₁) := by
    refine Finset.disjoint_left.mpr fun y hy hN => ?_
    have := hlow y hy
    rcases Finset.mem_union.mp hN with hN | hN
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hN
      have : 0 ≤ (i : ℝ) * d := by positivity
      linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hN
      have : d ≤ (i : ℝ) * d :=
        le_mul_of_one_le_left hd₀.le (by exact_mod_cast (Finset.mem_Icc.mp hi).1)
      linarith
  have hdisj' : Disjoint N₀ N₁ := by
    refine Finset.disjoint_left.mpr fun y hy₀ hy₁ => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy₀
    obtain ⟨j, -, h⟩ := Finset.mem_image.mp hy₁
    have h : (j : ℝ) * d - i * d = 1 := by linarith
    rcases lt_or_ge i j with hij | hij
    · have hij : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have hij : (j : ℝ) ≤ i := by exact_mod_cast hij
      nlinarith
  have hsub : (A - I) ∪ (N₀ ∪ N₁) ⊆ A - A := by
    refine Finset.union_subset (Finset.sub_subset_sub_left Finset.subset_union_left)
      (Finset.union_subset ?_ ?_)
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.sub_mem_sub (Finset.mem_union_left _ h0)
        (Finset.mem_union_right _ (hJ.mpr ⟨i, Finset.mem_range.mp hi, rfl⟩))
    · intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.sub_mem_sub (Finset.mem_union_left _ h1)
        (Finset.mem_union_right _
          (hJ.mpr ⟨i, by have := (Finset.mem_Icc.mp hi).2; omega, rfl⟩))
  have hA : (A + A).card ≤ (A - A).card := by
    calc (A + A).card ≤ (A + I).card + (J + J).card :=
          (Finset.card_le_card hsum).trans (Finset.card_union_le _ _)
      _ ≤ (A - I).card + (N₀.card + N₁.card) := by omega
      _ = ((A - I) ∪ (N₀ ∪ N₁)).card := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hdisj']
      _ ≤ (A - A).card := Finset.card_le_card hsub
  exact not_lt.mpr hA

-- The proof does not need `hm`; the argument keeps the wanted statement's signature.
set_option linter.unusedVariables false in
/-- **Interval plus integer progression starting after the interval is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x > n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Theorem 1
(`integers-2026-A58-thm-1`), the case of natural $x$ and $d$ (Section 3.1); Lemmas 1 and 2
(`integers-2026-A58-lem-1`, `integers-2026-A58-lem-2`) treat $x \ge n + 1$, and the case $x = n$
is not treated separately. -/
public theorem not_isMSTDSet_intervalAP_nat_of_lt (n m d x : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hd : 2 ≤ d)
    (hx : n - 1 < x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
  have hnx : (n : ℝ) ≤ x := by exact_mod_cast (by omega : n ≤ x)
  exact not_isMSTDSet_intervalAP_of_lt (by omega) (by linarith)
    (by exact_mod_cast (by omega : 1 < d))

end MetaMathlibExt
