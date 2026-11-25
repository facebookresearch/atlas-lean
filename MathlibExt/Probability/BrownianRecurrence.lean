/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
import MathlibExt.Probability.RandomWalkDichotomy
import MathlibExt.Probability.BrownianOscillation

/-!
# Linear Brownian motion is recurrent

If `B` is a real Brownian motion, then almost surely `limsup_{t → ∞} B t = +∞` and
`liminf_{t → ∞} B t = -∞`, and the path visits every real level: `T_a < ∞` for every `a`
(Le Gall's ENS notes *Intégration, Probabilités et Processus Aléatoires*, Corollaire 14.4.3,
second and third assertions).

The notes derive this from the oscillation at time `0` and Brownian scaling. Here the proof goes
through the repository's random-walk dichotomy: the values `B n` at integer times form a random
walk with independent `N(0, 1)` steps, so one of four alternatives holds almost surely (the walk
is identically zero, drifts to `+∞`, drifts to `-∞`, or oscillates). The first is excluded
because `B 1 ≠ 0` almost surely; the drifts are excluded because `P(B n > 0) = P(B n < 0) = 1/2`
for every `n ≥ 1`, which is incompatible with `B n` being eventually of one sign almost surely.
The walk therefore oscillates, and the intermediate value theorem on a continuous path gives the
hitting times.

## Main results

* `ProbabilityTheory.IsBrownianReal.ae_unbounded_atTop`: almost surely, for every level `A` and
  every `N`, there are integer times `n, m ≥ N` with `B n > A` and `B m < A`.
* `ProbabilityTheory.IsBrownianReal.ae_exists_eq`: almost surely, every real level is hit.

## References

* J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires* (ENS lecture notes),
  Corollaire 14.4.3.
* J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Graduate Texts in
  Mathematics 274, Springer, 2016, Chapter 2.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The increments of `B` between consecutive integer times. -/
private noncomputable def intIncrement (B : ℝ≥0 → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  B ((i : ℝ≥0) + 1) ω - B (i : ℝ≥0) ω

private lemma partialSum_intIncrement (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum
      (intIncrement B) n ω = B n ω - B 0 ω := by
  unfold MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum intIncrement
  have := Finset.sum_range_sub (fun i : ℕ ↦ B (i : ℝ≥0) ω) n
  simpa using this

/-- An event that holds almost surely has probability one, measurable or not. -/
private lemma measure_eq_one_of_ae [IsProbabilityMeasure P] {S : Set Ω}
    (h : ∀ᵐ ω ∂P, ω ∈ S) : P S = 1 := by
  refine le_antisymm prob_le_one ?_
  have hc : P Sᶜ = 0 := h
  calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
    _ = P (S ∪ Sᶜ) := by rw [Set.union_compl_self]
    _ ≤ P S + P Sᶜ := measure_union_le _ _
    _ = P S := by rw [hc, add_zero]

/-- If `P(Y n ∈ A) ≤ 1/2` for every large `n`, then `Y n` cannot be eventually in `A`
almost surely. -/
private lemma not_ae_eventually [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {p : ℝ → Prop}
    (hle : ∀ n, 1 ≤ n → P {ω | p (Y n ω)} ≤ 1 / 2)
    (h : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, p (Y n ω)) : False := by
  set S : ℕ → Set Ω := fun N ↦ {ω | ∀ n ≥ N, p (Y n ω)} with hS
  have hmono : Monotone S := fun a b hab ω hω n hn ↦ hω n (hab.trans hn)
  have hU : P (⋃ N, S N) = 1 := measure_eq_one_of_ae (h.mono fun ω ⟨N, hN⟩ ↦
    Set.mem_iUnion.2 ⟨N, hN⟩)
  rw [hmono.measure_iUnion] at hU
  have hbound : ⨆ N, P (S N) ≤ 1 / 2 := iSup_le fun N ↦
    (measure_mono fun ω (hω : ω ∈ S N) ↦ (hω : ∀ n ≥ N, p (Y n ω)) (N + 1) (Nat.le_succ N)).trans
      (hle (N + 1) (Nat.le_add_left 1 N))
  rw [hU] at hbound
  norm_num at hbound

/-- **Brownian motion is unbounded above and below at infinity.** If `B` is a real Brownian
motion, then almost surely, for every level `A` and every `N`, there are integer times
`n, m ≥ N` with `B n > A` and `B m < A`; in particular `limsup_{t → ∞} B t = +∞` and
`liminf_{t → ∞} B t = -∞` (Le Gall, ENS notes *Intégration, Probabilités et Processus
Aléatoires*, Corollaire 14.4.3, third assertion). -/
theorem IsBrownianReal.ae_unbounded_atTop (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ A : ℝ, ∀ N : ℕ,
      (∃ n ≥ N, A < B n ω) ∧ (∃ n ≥ N, B n ω < A) := by
  have hP : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  set X := intIncrement B with hX
  -- the steps are i.i.d. `N(0, 1)`
  have hlawX : ∀ i, HasLaw (X i) (gaussianReal 0 1) P := by
    intro i
    have h := hB.hasLaw_sub ((i : ℝ≥0) + 1) (i : ℝ≥0)
    convert h using 2
    · rfl
    · apply NNReal.coe_injective
      simp [dist_eq_norm]
  have hindep : iIndepFun X P := by
    have h := hB.hasIndepIncrements.nat (t := fun i : ℕ ↦ (i : ℝ≥0))
      Nat.mono_cast
    convert h using 3
    simp [hX, intIncrement]
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i ↦
    ⟨(hlawX i).aemeasurable, (hlawX 0).aemeasurable, by rw [(hlawX i).map_eq, (hlawX 0).map_eq]⟩
  -- laws of the partial sums
  have hB0 := hB.eval_zero_ae_eq_zero
  have hhalf : ∀ n : ℕ, 1 ≤ n →
      P {ω | 0 < B n ω - B 0 ω} ≤ 1 / 2 ∧ P {ω | B n ω - B 0 ω < 0} ≤ 1 / 2 := by
    intro n hn
    have hne : (nndist ((n : ℝ≥0) : ℝ) ((0 : ℝ≥0) : ℝ)) ≠ 0 := by
      simp only [ne_eq, nndist_eq_zero]
      exact_mod_cast (show n ≠ 0 by omega)
    have hne' : (nndist ((0 : ℝ≥0) : ℝ) ((n : ℝ≥0) : ℝ)) ≠ 0 := by
      rwa [nndist_comm]
    constructor
    · have h := (hB.hasLaw_sub (n : ℝ≥0) 0).measure_eq (p := fun x : ℝ ↦ 0 < x)
        measurableSet_Ioi
      rw [show {x : ℝ | 0 < x} = Set.Ioi 0 from rfl] at h
      exact (h.trans (gaussianReal_Ioi_zero hne)).le
    · have h := (hB.hasLaw_sub 0 (n : ℝ≥0)).measure_eq (p := fun x : ℝ ↦ 0 < x)
        measurableSet_Ioi
      rw [show {x : ℝ | 0 < x} = Set.Ioi 0 from rfl] at h
      have h := h.trans (gaussianReal_Ioi_zero hne')
      refine le_of_eq ?_
      rw [← h]
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, Pi.sub_apply]
      constructor <;> intro h' <;> linarith
  rcases MathlibExt.Probability.RandomWalkDichotomy.random_walk_dichotomy_zero P X hindep hident
    with hzero | htop | hbot | hosc
  · -- the zero walk: `B 1 - B 0 = 0` a.s., impossible for an `N(0, 1)` variable
    exfalso
    have h1 : ∀ᵐ ω ∂P, X 0 ω = 0 := hzero.mono fun ω hω ↦ by
      have := hω 1
      simpa [MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum] using this
    have hm := (hlawX 0).measure_eq (p := fun x : ℝ ↦ x = 0) (measurableSet_singleton 0)
    have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    have h1' : P {ω | X 0 ω = 0} = 1 := measure_eq_one_of_ae h1
    rw [Set.ofPred_eq_eq_singleton, measure_singleton, h1'] at hm
    exact one_ne_zero hm
  · exfalso
    refine not_ae_eventually (Y := fun n ω ↦ B n ω - B 0 ω) (p := fun x ↦ 0 < x)
      (fun n hn ↦ (hhalf n hn).1) ?_
    filter_upwards [htop] with ω hω
    have := hω.eventually_gt_atTop 0
    rw [eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    exact ⟨N, fun n hn ↦ by simpa [hX, partialSum_intIncrement] using hN n hn⟩
  · exfalso
    refine not_ae_eventually (Y := fun n ω ↦ B n ω - B 0 ω) (p := fun x ↦ x < 0)
      (fun n hn ↦ (hhalf n hn).2) ?_
    filter_upwards [hbot] with ω hω
    have := hω.eventually_lt_atBot 0
    rw [eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    exact ⟨N, fun n hn ↦ by simpa [hX, partialSum_intIncrement] using hN n hn⟩
  · filter_upwards [hosc, hB0] with ω ⟨hsup, hinf⟩ h0 A N
    have hS : ∀ n : ℕ, MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum
        X n ω = B n ω := fun n ↦ by rw [hX, partialSum_intIncrement, h0, sub_zero]
    constructor
    · have hfreq : ∃ᶠ n in atTop, ((A : ℝ) : EReal) <
          ((MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum X n ω : ℝ) :
            EReal) := by
        apply frequently_lt_of_lt_limsup (by isBoundedDefault)
        unfold MathlibExt.Probability.RandomWalkDichotomy.randomWalkLimsup at hsup
        rw [hsup]
        exact EReal.coe_lt_top A
      obtain ⟨n, hn, hlt⟩ := frequently_atTop.1 hfreq N
      exact ⟨n, hn, by rw [← hS n]; exact_mod_cast hlt⟩
    · have hfreq : ∃ᶠ n in atTop,
          ((MathlibExt.Probability.RandomWalkTailMeasurability.randomWalkPartialSum X n ω : ℝ) :
            EReal) < ((A : ℝ) : EReal) := by
        apply frequently_lt_of_liminf_lt (by isBoundedDefault)
        unfold MathlibExt.Probability.RandomWalkDichotomy.randomWalkLiminf at hinf
        rw [hinf]
        exact EReal.bot_lt_coe A
      obtain ⟨n, hn, hlt⟩ := frequently_atTop.1 hfreq N
      exact ⟨n, hn, by rw [← hS n]; exact_mod_cast hlt⟩

/-- **Linear Brownian motion hits every level.** If `B` is a real Brownian motion, then almost
surely, for every `a ∈ ℝ`, there is a time `t` with `B t = a`: the hitting time
`T_a = inf {t ≥ 0 : B t = a}` is finite for every `a` (Le Gall, ENS notes *Intégration,
Probabilités et Processus Aléatoires*, Corollaire 14.4.3, second assertion). -/
theorem IsBrownianReal.ae_exists_eq (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, ∃ t, B t ω = a := by
  filter_upwards [hB.ae_unbounded_atTop, hB.cont] with ω hω hc a
  obtain ⟨n, -, hn⟩ := (hω a 0).1
  obtain ⟨m, -, hm⟩ := (hω a 0).2
  have hivt := intermediate_value_uIcc (a := (n : ℝ≥0)) (b := (m : ℝ≥0))
    (f := fun t ↦ B t ω) hc.continuousOn
  obtain ⟨t, -, ht⟩ := hivt (Set.mem_uIcc.2 (Or.inr ⟨hm.le, hn.le⟩))
  exact ⟨t, ht⟩

end ProbabilityTheory
