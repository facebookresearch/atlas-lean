/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Jakimczuk's lemma on partial sums
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

-- Keep the public argument name `ha` for callers that supply positivity by name.
set_option linter.unusedVariables false in
/-- **Jakimczuk's lemma on sums of asymptotically equivalent terms.** Let $(a_i)_{i \ge 0}$ and
$(b_i)_{i \ge 0}$ be real sequences with $a_i > 0$ and $b_i > 0$ for every $i \ge 1$. If
$a_i \sim b_i$ as $i \to \infty$ and $\sum_{i=1}^{n} b_i \to +\infty$ as $n \to \infty$, then
$$\sum_{i=1}^{n} a_i \sim \sum_{i=1}^{n} b_i \qquad (n \to \infty).$$

The ATLAS wiki attributes this formulation to Rusen Li, *Sums over Primes II*,
Journal of Integer Sequences 27 (2024), Article 24.4.1.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 7 (`jis-2024-24.4.1-lem-7`). -/
public theorem sum_isEquivalent_of_isEquivalent (a b : ℕ → ℝ)
    (ha : ∀ i, 1 ≤ i → 0 < a i) (hb : ∀ i, 1 ≤ i → 0 < b i) (hab : a ~[atTop] b)
    (hdiv : Tendsto (fun n => ∑ i ∈ Icc 1 n, b i) atTop atTop) :
    (fun n => ∑ i ∈ Icc 1 n, a i) ~[atTop] fun n => ∑ i ∈ Icc 1 n, b i := by
  have reindex (f : ℕ → ℝ) (n : ℕ) :
      ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range n, f (i + 1) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simp [Nat.add_comm 1]
  simp_rw [reindex] at hdiv ⊢
  have h : (fun i => a (i + 1) - b (i + 1)) =o[atTop] fun i => b (i + 1) :=
    hab.isLittleO.comp_tendsto (tendsto_add_atTop_nat 1)
  simpa only [IsEquivalent, Pi.sub_def, sum_sub_distrib] using
    h.sum_range (fun i => (hb _ (Nat.succ_pos i)).le) hdiv

end MetaMathlibExt
