/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Repetitions under iterated affine expansion

Klarner's theorem for Erdős Problem 481 gives a repeated entry at some depth of affine
expansion when the sum of the reciprocal slopes exceeds one. The proof assigns a summable
weight to the natural numbers whose total over the list grows with each expansion.

Source: T. F. Bloom, Erdős Problems, Problem #481, https://www.erdosproblems.com/481 (status PROVED
(LEAN)). UnsolvedMath record UM-30006892 (`EP-481`), dataset ulamai/UnsolvedMath v1.8.0.

`∑ 1/aᵢ > 1` presupposes `aᵢ ≥ 1`. Sequences are lists of natural numbers (all entries stay in `ℕ`),
`A_k = T^[k - 1] (1)`; the order of entries in `T(A)` does not affect repetitions. Compared with the
formal-conjectures statement `ErdosProblems/481.lean` (equivalent; no code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481Wanted

/-- **Affine expansion of a sequence.** For $r \in \mathbb{N}$, maps
$a, b : \{0, \dots, r - 1\} \to \mathbb{N}$ and a finite sequence $A = (x_1, \dots, x_n)$ of
natural numbers, $T(A)$ is the sequence of length $rn$ obtained by listing the blocks
$(a_i x_1 + b_i, \dots, a_i x_n + b_i)$ one after another for $i = 0, 1, \dots, r - 1$.

The order of the entries does not affect whether an entry repeats. -/
def affineExpand {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap fun i => A.map fun x => a i * x + b i

/-- **Erdős Problem 481: repetitions under affine expansion.** The statement that for every
$r \in \mathbb{N}$ and all maps $a, b : \{0, \dots, r - 1\} \to \mathbb{N}$ with $a_i \ge 1$ for
every $i$ and $\sum_{i < r} 1 / a_i > 1$, if $T$ is the affine expansion of $a$ and $b$, sending a
finite sequence $(x_1, \dots, x_n)$ of natural numbers to the sequence of all $a_i x_j + b_i$,
listed in blocks for $i = 0, 1, \dots, r - 1$ (the order does not affect whether an entry repeats),
then, starting from $A_1 = (1)$ with $A_{k+1} = T(A_k)$, some $A_k$ has a repeated entry. -/
def affineIterateHasRepetition : Prop :=
  ∀ (r : ℕ) (a b : Fin r → ℕ), (∀ i, 0 < a i) → 1 < ∑ i, (1 : ℝ) / a i →
    ∃ k : ℕ, ¬ ((affineExpand a b)^[k] [1]).Nodup

private lemma exists_growth_parameter {r : ℕ} {a : Fin r → ℕ} (ha : ∀ i, 0 < a i)
    (hs : 1 < ∑ i, (1 : ℝ) / a i) :
    ∃ t : ℝ, 0 < t ∧ 1 < ∑ i, ((a i : ℝ) + t) ^ (-1 - t) := by
  let q (t : ℝ) := ∑ i, ((a i : ℝ) + t) ^ (-1 - t)
  have hq : ContinuousAt q 0 := by
    apply tendsto_finsetSum
    intro i _
    apply ContinuousAt.rpow (f := fun t : ℝ ↦ (a i : ℝ) + t) (g := fun t : ℝ ↦ -1 - t)
      (by fun_prop) (by fun_prop)
    exact Or.inl (by simpa using (Nat.cast_ne_zero.mpr (ha i).ne' : (a i : ℝ) ≠ 0))
  have h₀ : 1 < q 0 := by simpa [q, one_div, Real.rpow_neg_one] using hs
  exact (hq.tendsto.eventually_const_lt h₀).exists_gt

-- Sum the pointwise weight estimate over each block, then over the affine maps.
private lemma mul_sum_le_expand {r : ℕ} {a b : Fin r → ℕ} {w : ℕ → ℝ} {c : Fin r → ℝ}
    (h : ∀ i x, c i * w x ≤ w (a i * x + b i)) (A : List ℕ) :
    (∑ i, c i) * (A.map w).sum ≤ ((affineExpand a b A).map w).sum := by
  rw [affineExpand, List.map_flatMap]
  simp only [List.flatMap_def, List.sum_flatten, List.map_map,
    Function.comp_def, ← Fin.sum_univ_def, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum fun x _ ↦ h i x

/--
**Klarner's theorem (Erdős Problem 481).** For every $r \in \mathbb{N}$ and all maps
$a, b : \{0, \dots, r - 1\} \to \mathbb{N}$ with $a_i \ge 1$ for every $i$ and
$\sum_{i < r} 1 / a_i > 1$, let $T$ send a finite sequence $(x_1, \dots, x_n)$ of natural numbers
to the sequence of all $a_i x_j + b_i$, listed in blocks for $i = 0, 1, \dots, r - 1$. Then,
starting from $A_1 = (1)$ with $A_{k+1} = T(A_k)$, some $A_k$ has a repeated entry.

This was first shown by Klarner and generalized by Kolpakov and Talambutsa.

Source: T. F. Bloom, Erdős Problems,
Problem #481, https://www.erdosproblems.com/481 (status PROVED (LEAN)); resolution: D. A. Klarner, A
sufficient condition for certain semigroups to be free, J. Algebra (1982), 140-148; A. Kolpakov and
A. Talambutsa, On free semigroups of affine maps on the real line, Proc. Amer. Math. Soc. (2022),
2301-2307, erdosproblems.com/481: true, first shown by Klarner; generalized by Kolpakov and
Talambutsa, https://www.erdosproblems.com/481.
-/
theorem affineIterateHasRepetition_holds : affineIterateHasRepetition := by
  intro r a b ha hs
  obtain ⟨t, ht, hq⟩ := exists_growth_parameter ha hs
  let c (i : Fin r) := ((a i : ℝ) + t) ^ (-1 - t)
  let q := ∑ i, c i
  change 1 < q at hq
  -- A large shift absorbs every translation, including those belonging to slopes of one.
  obtain ⟨N, hN⟩ := exists_nat_gt ((∑ i, (b i : ℝ)) / t)
  have hB := (div_lt_iff₀ ht).mp hN
  have hNpos : 0 < (N : ℝ) := by
    exact lt_of_le_of_lt (div_nonneg (Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg (b j)) ht.le) hN
  let w (x : ℕ) := ((x : ℝ) + N) ^ (-1 - t)
  have hw (x : ℕ) : 0 < w x := Real.rpow_pos_of_pos (by positivity) _
  have hstep (i : Fin r) (x : ℕ) : c i * w x ≤ w (a i * x + b i) := by
    have ha₁ : (1 : ℝ) ≤ a i := by exact_mod_cast ha i
    have hb : (b i : ℝ) ≤ ∑ j, (b j : ℝ) :=
      Finset.single_le_sum (fun j _ ↦ Nat.cast_nonneg (b j)) (Finset.mem_univ i)
    dsimp [c, w]
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    push_cast
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr ha₁) hNpos.le, mul_nonneg ht.le (Nat.cast_nonneg x)]
  let A (k : ℕ) := (affineExpand a b)^[k] [1]
  have hgrow (k : ℕ) : q ^ k * w 1 ≤ ((A k).map w).sum := by
    induction k with
    | zero => simp [A]
    | succ k ih =>
      rw [pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ q)).trans
        (by simpa [A, Function.iterate_succ_apply'] using mul_sum_le_expand hstep (A k))
  -- With distinct entries the list contributes at most the entire shifted p-series.
  have hsum : Summable w := by
    simpa [w] using (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-1 - t)) N).2
      (Real.summable_nat_rpow.mpr (by linarith))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((∑' x, w x) / w 1) hq
  refine ⟨k, fun hdup ↦ ?_⟩
  have hbound := hsum.sum_le_tsum (A k).toFinset (fun x _ ↦ (hw x).le)
  rw [List.sum_toFinset w hdup] at hbound
  exact ((div_lt_iff₀ (hw 1)).mp hk).not_ge ((hgrow k).trans hbound)

end MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481Wanted
