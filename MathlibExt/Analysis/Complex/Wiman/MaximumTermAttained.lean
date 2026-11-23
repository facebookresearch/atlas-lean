/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.RadialMajorant
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace Complex

noncomputable section

open Filter Set

/-- **The Taylor terms are bounded above.** Let $f$ be an entire function with Taylor
coefficients $a_n$ at the origin, and let $r$ be real. Then the set of Taylor terms
$\{|a_n|\,|r|^n : n \in \mathbb{N}\}$ is bounded above. -/
theorem bddAbove_range_wimanTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (r : ℝ) :
    BddAbove (range (wimanTerm f r)) := by
  refine ⟨wimanMajorant f r, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact wimanTerm_le_wimanMajorant f hf r n

/-- **Each Taylor term is at most the maximum term.** Let $f$ be an entire function with Taylor
coefficients $a_n$ at the origin and maximum term $\mu(r) = \sup_k |a_k|\,|r|^k$. For every real
$r$ and every $n \in \mathbb{N}$, $|a_n|\,|r|^n \le \mu(r)$. -/
theorem wimanTerm_le_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r : ℝ) (n : ℕ) :
    wimanTerm f r n ≤ wimanMaximumTerm f r := by
  rw [wimanMaximumTerm]
  exact le_csSup (bddAbove_range_wimanTerm f hf r) ⟨n, rfl⟩

/-- **Bounding the maximum term.** Let $f$ be an entire function with Taylor coefficients $a_n$
at the origin and maximum term $\mu(r) = \sup_n |a_n|\,|r|^n$. For all real $r$ and $c$,
$\mu(r) \le c$ if and only if $|a_n|\,|r|^n \le c$ for every $n \in \mathbb{N}$. -/
theorem wimanMaximumTerm_le_iff
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r a : ℝ) :
    wimanMaximumTerm f r ≤ a ↔ ∀ n : ℕ, wimanTerm f r n ≤ a := by
  constructor
  · intro h n
    exact (wimanTerm_le_wimanMaximumTerm f hf r n).trans h
  · intro h
    rw [wimanMaximumTerm]
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨n, rfl⟩
    exact h n

/-- **The maximum term is attained by a Taylor term.** Let $f$ be an entire function with Taylor
coefficients $a_n$ at the origin and maximum term $\mu(r) = \sup_n |a_n|\,|r|^n$. For every real
$r$ there is an $n \in \mathbb{N}$ with $|a_n|\,|r|^n = \mu(r)$. -/
theorem exists_wimanTerm_eq_wimanMaximumTerm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (r : ℝ) :
    ∃ n : ℕ, wimanTerm f r n = wimanMaximumTerm f r := by
  by_cases hzero : ∀ n : ℕ, wimanTerm f r n = 0
  · refine ⟨0, (wimanTerm_le_wimanMaximumTerm f hf r 0).antisymm ?_⟩
    apply (wimanMaximumTerm_le_iff f hf r (wimanTerm f r 0)).2
    intro n
    rw [hzero n, hzero 0]
  · push Not at hzero
    obtain ⟨n₀, hn₀⟩ := hzero
    have hn₀pos : 0 < wimanTerm f r n₀ :=
      lt_of_le_of_ne (wimanTerm_nonneg f r n₀) (Ne.symm hn₀)
    have htail_cocompact :
        ∀ᶠ n in cocompact ℕ, wimanTerm f r n ≤ wimanTerm f r n₀ := by
      rw [Filter.cocompact_eq_cofinite]
      exact ((summable_wimanTerm f hf r).tendsto_cofinite_zero.eventually_lt_const
        hn₀pos).mono fun _ hn ↦ hn.le
    have hcontinuous : Continuous (wimanTerm f r) :=
      continuous_of_discreteTopology
    obtain ⟨n, hn⟩ := hcontinuous.exists_forall_ge' n₀ htail_cocompact
    refine ⟨n, (wimanTerm_le_wimanMaximumTerm f hf r n).antisymm ?_⟩
    exact (wimanMaximumTerm_le_iff f hf r (wimanTerm f r n)).2 hn

end

end Complex
