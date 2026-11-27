/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/818.lean` (Formal Conjectures), for the conjecture statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import MathlibExt.Combinatorics.SolymosiSumProduct

/-!
# Erdős Problem 818

`conjecture_holds` gives a lower bound for the size of the product set of a finite set of
integers with small additive doubling. The proof uses Solymosi's multiplicative energy bound.
-/

@[expose] public section

open scoped Pointwise
open Finset

namespace MathlibExt.NumberTheory.ErdosProblem818Wanted

/-- **Erdős Problem 818.** The statement that for every real $K > 0$ there are reals $C > 0$ and
$c > 0$ such that every finite set $A$ of integers with $|A| \ge 2$ and $|A + A| \le K|A|$
satisfies $c|A|^2 / (\log |A|)^C \le |A \cdot A|$. Here $A + A = \{a + b : a, b \in A\}$,
$A \cdot A = \{ab : a, b \in A\}$ and $\log$ is the natural logarithm. -/
def conjecture : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
      c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C ≤ ((A * A).card : ℝ)

/--
**Erdős Problem 818 is true.** For every real $K > 0$ there are reals $C > 0$ and $c > 0$ such
that every finite set $A$ of integers with $|A| \ge 2$ and $|A + A| \le K|A|$ satisfies
$c|A|^2 / (\log |A|)^C \le |A \cdot A|$. Here $A + A = \{a + b : a, b \in A\}$,
$A \cdot A = \{ab : a, b \in A\}$ and $\log$ is the natural logarithm.

József Solymosi proved a stronger bound, with a single logarithm in the denominator.

Source: József Solymosi, Bounding multiplicative energy by the sumset, Advances
in Mathematics 222 (2009), 402–408, https://doi.org/10.1016/j.aim.2009.04.006. Moved from
`OpenConjectures/NumberTheory/ErdosProblem818`.
-/
theorem conjecture_holds : conjecture := by
  classical
  intro K hK
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1, zero_lt_one, Real.log 2 / (1296 * K ^ 2), by positivity, ?_⟩
  intro A hA hsum
  let f := Int.castRingHom ℝ
  have hcard (S : Finset ℤ) : (S.image f).card = S.card :=
    card_image_of_injective _ Int.cast_injective
  have hbound := MathlibExt.Combinatorics.RealSumProductExponentWanted.solymosi_sum_product
    (A.image f) (by simpa only [hcard] using hA)
  rw [← image_mul f, ← image_add f] at hbound
  simp only [hcard] at hbound
  have hn : 1 < (A.card : ℝ) := by exact_mod_cast (show 1 < A.card from hA)
  have hlog := Real.log_pos hn
  have hsum' : ((A + A).card : ℝ) ^ 2 ≤ (K * A.card) ^ 2 := by gcongr
  have hamb : Real.log 2 * (A.card : ℝ) ^ 4 ≤
      1296 * (A * A).card * (K * A.card) ^ 2 * Real.log A.card := by
    apply hbound.trans
    gcongr
  rw [Real.rpow_one, div_le_iff₀ hlog, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right (a := (A.card : ℝ) ^ 2) _ (by positivity)
  nlinarith only [hamb]

end MathlibExt.NumberTheory.ErdosProblem818Wanted
