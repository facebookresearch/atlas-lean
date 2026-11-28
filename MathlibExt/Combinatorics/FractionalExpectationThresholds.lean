/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.Combinatorics.FractionalExpectationThresholds`, submitted by David Ledvinka;
original statement from ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean.
The following notice applies to the adapted portions:
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka

The definitions `IsWeaklySmall`, `p_c`, `q_f` and `l` have been moved here from
`WantedExt.Combinatorics.FractionalExpectationThresholdsWanted`; the choice of constant
and the reduction from the integral estimate are new. lean-eval ships no NOTICE file.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# A constant for fractional expectation-thresholds

Frankston, Kahn, Narayanan and Park, *Thresholds versus fractional expectation-thresholds*,
Theorem 1.1 (https://doi.org/10.4007/annals.2021.194.2.2), assert existence of a universal
constant, not a particular numerical value. We use the explicit **integral** bound of
B. Park and J. Vondrák, *A simple proof of the non-uniform Kahn–Kalai conjecture*,
§2.3, final paragraph of the calculation with `L = 6` (https://arxiv.org/abs/2306.12576).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
namespace FractionalExpectationThresholds

open ProbabilityTheory unitInterval Set
open scoped NNReal

open Classical in
/-- **Weakly $p$-small families.** Let $X$ be a finite set, $p \in [0, 1]$, and $\mathcal F$ a
family of subsets of $X$. Then $\mathcal F$ is weakly $p$-small if there is a function $g$ from
subsets of $X$ to the nonnegative reals such that $\sum_{S \subseteq T} g(S) \ge 1$ for every
$T \in \mathcal F$ and $\sum_{S \subseteq X} g(S)\, p^{|S|} \le 1/2$. -/
def IsWeaklySmall {X : Type*} [Fintype X] (p : I) (𝓕 : Set (Set X)) : Prop :=
  ∃ g : Set X → ℝ≥0, (∀ T ∈ 𝓕, ∑ S with S ⊆ T, g S ≥ 1) ∧ ∑ S, g S * (p : ℝ) ^ S.ncard ≤ 2⁻¹

open Classical in
/-- **The threshold $p_c(\mathcal F)$.** For a set $X$ and $p \in [0, 1]$, let $\mu_p$ be the
$p$-biased product measure on subsets of $X$, under which each element of $X$ lies in the
random subset independently with probability $p$. For a family $\mathcal F$ of subsets of $X$,
$p_c(\mathcal F)$ is some $p \in [0, 1]$ with $\mu_p(\mathcal F) = 1/2$ if such a $p$ exists,
and $0$ otherwise.

When $X$ is finite and $\mathcal F$ is increasing, nonempty and not the family of all subsets
of $X$, such a $p$ exists and is unique; it is the threshold of $\mathcal F$. -/
noncomputable def p_c {X : Type*} (𝓕 : Set (Set X)) : I :=
  if h : ∃ p, setBer(univ, p).real (𝓕 : Set (Set X)) = 2⁻¹ then Classical.choose h else 0

/-- **The fractional expectation-threshold $q_f(\mathcal F)$.** For a family $\mathcal F$ of
subsets of a finite set $X$, $q_f(\mathcal F)$ is the supremum, in $[0, 1]$, of the set of all
$p \in [0, 1]$ such that $\mathcal F$ is weakly $p$-small; it is $0$ if there is no such $p$. -/
noncomputable def q_f {X : Type*} [Fintype X] (𝓕 : Set (Set X)) : I :=
  sSup {p | IsWeaklySmall p 𝓕}

/-- **Size of a largest minimal element, $\ell(\mathcal F)$.** For a family $\mathcal F$ of
subsets of a set $X$, $\ell(\mathcal F)$ is the largest cardinality of a minimal element of
$\mathcal F$ (minimal with respect to inclusion), a natural number.

By convention $\ell(\mathcal F) = 0$ when $\mathcal F$ has no minimal element or when the
cardinalities of its minimal elements are unbounded, and an infinite set counts as having
cardinality $0$. -/
noncomputable def l {X : Type*} (𝓕 : Set (Set X)) : ℕ :=
  ⨆ (A : 𝓕) (_ : IsMin A), (A : Set X).ncard

/-- A universal constant for the Frankston–Kahn–Narayanan–Park bound with the natural logarithm
and largest minimal size $\ell\ge 2$ is $K=12/\ln 2$. Park and Vondrák (§2.3 of
https://arxiv.org/abs/2306.12576) prove $p_c\le 6 q_c\log_2(2\ell)$, with $q_c$ the integral
expectation-threshold. Every integral cover is a fractional cover and $\ln(2\ell)\le 2\ln\ell$
for $\ell\ge 2$. No optimality is asserted. -/
noncomputable def K : ℝ := 12 / Real.log 2

/-- The integral expectation-threshold is the supremum in $[0,1]$ of the parameters
$q\in(0,1)$ for which some family $G$ covers every member of $\mathcal F$ by inclusion and
has $\sum_{S\in G} q^{|S|}\le 1/2$ (Park and Vondrák, Definitions 2 and 3). -/
noncomputable def q_c {X : Type*} [Fintype X] (𝓕 : Set (Set X)) : I :=
  sSup {p | p ∈ Ioo (0 : I) 1 ∧ ∃ G : Finset (Set X),
    (∀ T ∈ 𝓕, ∃ S ∈ G, S ⊆ T) ∧ ∑ S ∈ G, (p : ℝ) ^ S.ncard ≤ 2⁻¹}

/-- The integral expectation-threshold of a finite set family is at most its fractional
expectation-threshold: the indicator of a cover is a feasible fractional weight of the same cost.
This is the first inequality in (3) of Frankston–Kahn–Narayanan–Park. -/
theorem q_c_le_q_f {X : Type*} [Fintype X] (𝓕 : Set (Set X)) : q_c 𝓕 ≤ q_f 𝓕 := by
  classical
  apply sSup_le_sSup
  rintro p ⟨_, G, hG, hcost⟩
  refine ⟨fun S => if S ∈ G then 1 else 0, ?_, ?_⟩
  · intro T hT
    obtain ⟨S, hS, hST⟩ := hG T hT
    exact (show 1 ≤ (if S ∈ G then 1 else 0 : ℝ≥0) by simp [hS]).trans
      (Finset.single_le_sum (f := fun A => if A ∈ G then (1 : ℝ≥0) else 0)
        (fun _ _ => zero_le) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST⟩))
  · simpa [apply_ite, ite_mul, Finset.sum_ite_mem] using hcost

private theorem six_mul_logb_le {r : ℕ} (hr : 2 ≤ r) :
    6 * Real.logb 2 (2 * (r : ℝ)) ≤ K * Real.log r := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr'
  rw [K, Real.logb, Real.log_mul (by norm_num) (by positivity)]
  field_simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  linarith

/-- **Reduction from the uniform integral bound.** Suppose every nonempty $r$-bounded family
$H$ on the finite ground set, with $r\ge1$ and $\varnothing\notin H$, satisfies the uniform
estimate of Park and Vondrák (§2.3): the supremum of $p\in(0,1)$ with
$\mu_p(\langle H\rangle)\le 1/2$ is at most $6q_c(\langle H\rangle)\log_2(2r)$, where
$\langle H\rangle$ is the upward closure. Then every increasing family $\mathcal F$ on the
same ground set with $\ell(\mathcal F)\ge2$ satisfies $p_c\le K q_f\ln\ell(\mathcal F)$. -/
theorem threshold_le_of_integral_bound {X : Type*} [Fintype X]
    (hPV : ∀ (H : Set (Set X)) (r : ℕ), H.Nonempty → ∅ ∉ H → 1 ≤ r →
      (∀ S ∈ H, S.ncard ≤ r) →
      ((sSup {p : I | p ∈ Ioo 0 1 ∧
        setBer(univ, p).real (upperClosure H : Set (Set X)) ≤ 2⁻¹} : I) : ℝ) ≤
        6 * q_c (upperClosure H : Set (Set X)) * Real.logb 2 (2 * (r : ℝ)))
    (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕) :
    (p_c 𝓕 : ℝ) ≤ K * q_f 𝓕 * Real.log (l 𝓕) := by
  classical
  let H : Set (Set X) := Subtype.val '' {A : 𝓕 | IsMin A}
  obtain ⟨A, hm, hsize⟩ : ∃ A : 𝓕, IsMin A ∧ 2 ≤ A.val.ncard := by
    by_contra! h
    have : l 𝓕 ≤ 1 := ciSup_le' fun A => ciSup_le' fun hm => Nat.le_of_lt_succ (h A hm)
    omega
  have hH : H.Nonempty := ⟨_, A, hm, rfl⟩
  have hmin : ∅ ∉ H := by
    rintro ⟨B, _, hb⟩
    have hBA : B ≤ A := show B.val ⊆ A.val by simp [hb]
    have hAB : A = B := le_antisymm (hm hBA) hBA
    simp [hAB, hb] at hsize
  have hbounded : ∀ S ∈ H, Set.ncard S ≤ l 𝓕 := by
    rintro _ ⟨A, hA, rfl⟩
    exact (le_ciSup_of_le (Set.finite_range _).bddAbove A <|
      le_ciSup_of_le (Set.finite_range _).bddAbove hA le_rfl)
  have hgen : (upperClosure H : Set (Set X)) = 𝓕 := by
    ext T
    constructor
    · rintro ⟨_, ⟨A, _, rfl⟩, hAT⟩
      exact h𝓕 hAT A.property
    · intro hT
      obtain ⟨B, hBT, hB, hminB⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ 𝓕) T hT
      exact ⟨B, ⟨⟨B, hB⟩, fun C hCB => hminB C.property hCB, rfl⟩, hBT⟩
  have hbound := hPV H (l 𝓕) hH hmin (by omega) hbounded
  rw [hgen] at hbound
  have h1 : (p_c 𝓕 : ℝ) ≤
      ((sSup {p : I | p ∈ Ioo 0 1 ∧ setBer(univ, p).real 𝓕 ≤ 2⁻¹} : I) : ℝ) := by
    change p_c 𝓕 ≤ _
    unfold p_c
    split_ifs with hex
    · let p := Classical.choose hex
      have hp : setBer(univ, p).real 𝓕 = 2⁻¹ := Classical.choose_spec hex
      change p ≤ _
      rcases eq_or_lt_of_le (bot_le : (0 : I) ≤ p) with h0 | h0
      · rw [← h0]
        exact bot_le
      have hp1 : p < 1 := by
        apply lt_of_le_of_ne (le_top : p ≤ (1 : I))
        intro heq
        rw [heq] at hp
        change setBer(univ, (1 : I)).real 𝓕 = 2⁻¹ at hp
        rw [setBernoulli_one, MeasureTheory.Measure.dirac_real_apply_of_mem
          (h𝓕 (subset_univ _) A.property)] at hp
        norm_num at hp
      exact le_sSup ⟨⟨h0, hp1⟩, hp.le⟩
    · exact bot_le
  have hq : (q_c 𝓕 : ℝ) ≤ q_f 𝓕 := q_c_le_q_f 𝓕
  have log_nonneg : 0 ≤ Real.log (l 𝓕) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ l 𝓕 by omega))
  calc
    (p_c 𝓕 : ℝ) ≤ _ := h1.trans hbound
    _ = q_c 𝓕 * (6 * Real.logb 2 (2 * (l 𝓕 : ℝ))) := by ring
    _ ≤ q_c 𝓕 * (K * Real.log (l 𝓕)) := mul_le_mul_of_nonneg_left (six_mul_logb_le hl) (q_c 𝓕).2.1
    _ ≤ q_f 𝓕 * (K * Real.log (l 𝓕)) := mul_le_mul_of_nonneg_right hq
      (mul_nonneg (by unfold K; positivity) log_nonneg)
    _ = _ := by ring

end FractionalExpectationThresholds
end MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
