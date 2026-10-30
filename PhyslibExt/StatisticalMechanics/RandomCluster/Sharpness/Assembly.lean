/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg
public import CSLibExt.Complexity.BooleanFunctions.SharpnessFK
public import MathlibExt.Probability.OSSS.Integration
public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKQ2Sharp
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent

/-!
# Assembly of the random-cluster sharpness argument

The Poincaré inequality for increasing indicators, the differential inequality, subcritical decay by
integration, and the mean-field lower bound, for the random-cluster model on a finite graph.

## i. Overview

`fk_poincare_indicator` (`θ(1 - θ) ≤ ∑ Cov`, `q ≥ 1`) is unconditional. `fk_differential_inequality`
is conditional on `hbridge`, which says the covariance sum over all pairs equals the sum over edges
of `G`. `fk_subcritical_decay` integrates a supplied differential inequality `hdi` with `θ ≤ 1 - κ`
to get exponential decay. `fk_sharpness_both` adds the mean-field bound from supplied limits `hTβ`,
`hTβ'`, `hmlim`, `hbound`. `fk_q2_crossing_decay_poincare` (`q = 2`) is conditional on `hbridge` and
`hθub` only.

## ii. Key results

- `fk_poincare_indicator`: Poincaré inequality for increasing indicators (unconditional).
- `fk_q2_crossing_decay_poincare`: `θ(a) ≤ exp(-4κ(b - a))` at `q = 2`, conditional on `hbridge` and
  `hθub`.
- `fk_sharpness_both`: decay and mean-field bounds, conditional on the supplied differential
  inequality and limits.

## iii. Table of contents

- A. Poincaré and differential inequalities
- B. Decay and sharpness

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open Finset Real Set Filter Topology


namespace StatMech
namespace OSSS

open StatMech.OSSS.Lindeberg
open StatMech.OSSS.SharpnessFK
open StatMech.FK
open MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A. Poincaré and differential inequalities -/

lemma lind_var_indicator {μ : ConfigSpace (Sym2 V) → ℝ}
    (f : ConfigSpace (Sym2 V) → ℝ) (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
    Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
  unfold Lindeberg.var Lindeberg.cov
  have hsq : Lindeberg.mean μ (fun ω => f ω * f ω) = Lindeberg.mean μ f := by
    unfold Lindeberg.mean
    apply Finset.sum_congr rfl
    intro ω _
    rcases hf ω with h | h <;> simp only [h] <;> ring
  rw [hsq]; ring

/-- Poincaré inequality for increasing indicators (unconditional). -/
theorem fk_poincare_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    fkProbOf G p q A * (1 - fkProbOf G p q A)
      ≤ ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
  classical
  have hvar := Lindeberg.fk_monotonic_poincare G hp hp1 hq
    (f := A.indicator (fun _ => (1 : ℝ)))
    (hA.indicator_monotone)
    (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (fun ω => by rw [Set.indicator_apply]; split_ifs <;> norm_num)
  rwa [lind_var_indicator (A.indicator (fun _ => (1 : ℝ)))
      (fun ω => by
        by_cases h : ω ∈ A
        · right; rw [Set.indicator_of_mem h]
        · left; rw [Set.indicator_of_notMem h])] at hvar

lemma fk_differential_inequality (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (hbridge : ∑ e, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
          = ∑ e ∈ G.edgeFinset, fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)) :
    russoPrefactor p * (fkProbOf G p q A * (1 - fkProbOf G p q A))
      ≤ deriv (fun p => fkProbOf G p q A) p := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpoin := fk_poincare_indicator G hp hp1 hq A hA
  rw [hbridge] at hpoin
  refine le_trans ?_ (FK.russo_bound G hp hp1 hq0 A)
  exact mul_le_mul_of_nonneg_left hpoin (russoPrefactor_pos hp hp1).le

/-! ## B. Decay and sharpness -/

lemma fk_subcritical_decay (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℝ} (hq : 1 ≤ q) (A : Set (ConfigSpace (Sym2 V)))
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hdi : ∀ x ∈ Icc a b,
       russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A))
        ≤ deriv (fun p => fkProbOf G p q A) x)
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
    (rate : ℝ) (hrate : 0 < rate)
    (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ) :
    fkProbOf G a q A ≤ Real.exp (-(rate * (b - a))) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set θn : ℝ → ℝ := fun x => fkProbOf G x q A with hθn
  set θn' : ℝ → ℝ := fun x => deriv (fun p => fkProbOf G p q A) x with hθn'
  have hxbounds : ∀ x ∈ Icc a b, 0 < x ∧ x < 1 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  have hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    change HasDerivAt θn (deriv (fun p => fkProbOf G p q A) x) x
    have hda := FK.hasDerivAt_fkProbOf G hx0 hx1 hq0 A
    rw [hda.deriv]; exact hda
  have hθnn : ∀ x ∈ Icc a b, 0 ≤ θn x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    exact FK.fkProbOf_nonneg G hx0 hx1 hq0 A
  have hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hxbounds x hx
    have hθ := hθnn x hx
    have hfac : θn x * κ ≤ θn x * (1 - θn x) :=
      mul_le_mul_of_nonneg_left (by have := hθub x hx; linarith) hθ
    have hpref_nn : 0 ≤ russoPrefactor x := (russoPrefactor_pos hx0 hx1).le
    calc rate * θn x ≤ (russoPrefactor x * κ) * θn x :=
            mul_le_mul_of_nonneg_right (hrlb x hx) hθ
      _ = russoPrefactor x * (θn x * κ) := by ring
      _ ≤ russoPrefactor x * (θn x * (1 - θn x)) :=
            mul_le_mul_of_nonneg_left hfac hpref_nn
      _ ≤ θn' x := hdi x hx
  have hθa : 0 ≤ θn a := hθnn a (left_mem_Icc.2 hab.le)
  have hθb : θn b ≤ 1 := by have := hθub b (right_mem_Icc.2 hab.le); linarith
  have hfin := subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb
  exact hfin.2.1

lemma fk_q2_crossing_decay_poincare (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A)
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hbridge : ∀ p ∈ Icc a b,
      ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e)
        = ∑ e ∈ G.edgeFinset, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
    (hθub : ∀ p ∈ Icc a b, fkProbOf G p 2 A ≤ 1 - κ) :
    fkProbOf G a 2 A ≤ Real.exp (-(4 * κ * (b - a))) := by
  have hFKcov : ∀ p ∈ Icc a b, ((1 : ℕ) : ℝ) * 1
        * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ 1 * ∑ e ∈ G.edgeFinset,
          fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
    intro p hp
    rw [Set.mem_Icc] at hp
    have hp0 : 0 < p := lt_of_lt_of_le ha0 hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hpoin := fk_poincare_indicator G hp0 hp1 (by norm_num : (1 : ℝ) ≤ 2) A hA
    rw [hbridge p (Set.mem_Icc.2 hp)] at hpoin
    simp only [Nat.cast_one, one_mul]
    exact hpoin
  have hdiff : ∀ p ∈ Icc a b,
      HasDerivAt (fun p => fkProbOf G p 2 A) (deriv (fun p => fkProbOf G p 2 A) p) p := by
    intro p hp
    rw [Set.mem_Icc] at hp
    have hp0 : 0 < p := lt_of_lt_of_le ha0 hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hda := FK.hasDerivAt_fkProbOf G hp0 hp1 (by norm_num : (0 : ℝ) < 2) A
    rw [hda.deriv]; exact hda
  have h := FK.fk_q2_crossing_decay G (n := 1) le_rfl A 1 1 κ one_pos one_pos hκ
    a b hab ha0 hb1 hdiff hFKcov hθub
  have he : (4 * ((1 : ℕ) : ℝ) * 1 * κ / 1 * (b - a)) = 4 * κ * (b - a) := by
    push_cast; ring
  rwa [he] at h

/-- Decay and mean-field bounds, conditional on the supplied differential inequality and limits. -/
theorem fk_sharpness_both (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℝ} (hq : 1 ≤ q) (A : Set (ConfigSpace (Sym2 V)))
    (a b κ : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1) (hκ : 0 < κ)
    (hdi : ∀ x ∈ Icc a b,
       russoPrefactor x * (fkProbOf G x q A * (1 - fkProbOf G x q A))
        ≤ deriv (fun p => fkProbOf G p q A) x)
    (hθub : ∀ x ∈ Icc a b, fkProbOf G x q A ≤ 1 - κ)
    (rate : ℝ) (hrate : 0 < rate)
    (hrlb : ∀ x ∈ Icc a b, rate ≤ russoPrefactor x * κ)
    (T : ℕ → ℝ → ℝ) (mseq : ℕ → ℝ) (β' β fβ fβ' m : ℝ)
    (hββ : β' ≤ β) (hm1 : 1 ≤ m)
    (hTβ : Tendsto (fun n => T n β) atTop (𝓝 fβ))
    (hTβ' : Tendsto (fun n => T n β') atTop (𝓝 fβ'))
    (hmlim : Tendsto mseq atTop (𝓝 m))
    (hbound : ∀ᶠ n in atTop, (β - β') * mseq n ≤ T n β - T n β') :
    (fkProbOf G a q A ≤ Real.exp (-(rate * (b - a))))
      ∧ (β - β' ≤ fβ - fβ') :=
  ⟨fk_subcritical_decay G hq A a b κ hab ha0 hb1 hκ hdi hθub rate hrate hrlb,
   StatMech.OSSS.Integration.meanField_lower T mseq β' β fβ fβ' m hββ hm1 hTβ hTβ' hmlim hbound⟩

end OSSS
end StatMech
