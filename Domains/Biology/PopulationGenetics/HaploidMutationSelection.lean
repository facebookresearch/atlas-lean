/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mutation–selection balance in a haploid population

The wild type has fitness one and the mutant has fitness `1 - s`. Each generation selection
acts first, then a fraction `u` of the wild type mutates, with no back mutation. We classify
fixed points and limits of this discrete-generation recursion, including the lethal boundary.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §III.4, equations
  (III-13)–(III-18), pp. 146–148, and §III.7, pp. 156–157 (mutational load),
  <https://felsenst.github.io/pgbook/pgbook.pdf>.
-/

open Filter Set
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics

private def haploidMeanFitness (s p : ℝ) : ℝ := 1 - (1 - p) * s

private noncomputable def haploidStep (s u p : ℝ) : ℝ :=
  p * (1 - u) / haploidMeanFitness s p

private theorem haploidMeanFitness_pos_iff {s p : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hp : 0 ≤ p) :
    0 < haploidMeanFitness s p ↔ s < 1 ∨ 0 < p := by
  have hw : haploidMeanFitness s p = (1 - s) + s * p := by unfold haploidMeanFitness; ring
  rw [hw]
  constructor
  · intro h
    by_contra! hn
    have hs' : s = 1 := le_antisymm hs₁ hn.1
    have hp' : p = 0 := le_antisymm hn.2 hp
    rw [hs', hp'] at h
    linarith
  · rintro (h | h)
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr h) (mul_nonneg hs.le hp)
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs₁) (mul_pos hs h)

private theorem haploidStep_mapsTo {s u : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (hu : 0 < u) (hu₁ : u < 1) : MapsTo (haploidStep s u) (Ioc 0 1) (Ioc 0 1) := by
  intro p hp
  have hw := (haploidMeanFitness_pos_iff hs hs₁ hp.1.le).2 (Or.inr hp.1)
  have hwp : p ≤ haploidMeanFitness s p := by
    unfold haploidMeanFitness
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hs₁)]
  exact ⟨div_pos (mul_pos hp.1 (sub_pos.mpr hu₁)) hw,
    (div_le_one hw).2 ((mul_le_of_le_one_right hp.1.le (by linarith)).trans hwp)⟩

private theorem haploidStep_cross {s u p q : ℝ} :
    q * (1 - u) * haploidMeanFitness s p - p * (1 - u) * haploidMeanFitness s q =
      (q - p) * (1 - u) * (1 - s) := by unfold haploidMeanFitness; ring

private theorem haploidStep_mono {s u : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hu₁ : u < 1) :
    MonotoneOn (haploidStep s u) (Ioc 0 1) := by
  intro p hp q hq hpq
  have hwp := (haploidMeanFitness_pos_iff hs hs₁ hp.1.le).2 (Or.inr hp.1)
  have hwq := (haploidMeanFitness_pos_iff hs hs₁ hq.1.le).2 (Or.inr hq.1)
  unfold haploidStep
  rw [div_le_div_iff₀ hwp hwq, ← sub_nonneg, haploidStep_cross]
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hu₁.le)) (sub_nonneg.mpr hs₁)

private theorem haploidStep_strictMono {s u : ℝ} (hs : 0 < s) (hs₁ : s < 1) (hu₁ : u < 1) :
    StrictMonoOn (haploidStep s u) (Icc 0 1) := by
  intro p hp q hq hpq
  have hwp := (haploidMeanFitness_pos_iff hs hs₁.le hp.1).2 (Or.inl hs₁)
  have hwq := (haploidMeanFitness_pos_iff hs hs₁.le hq.1).2 (Or.inl hs₁)
  unfold haploidStep
  rw [div_lt_div_iff₀ hwp hwq, ← sub_pos, haploidStep_cross]
  exact mul_pos (mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hu₁)) (sub_pos.mpr hs₁)

private theorem haploidStep_lethal {u p : ℝ} (hp : 0 < p) : haploidStep 1 u p = 1 - u := by
  have hw : haploidMeanFitness 1 p = p := by unfold haploidMeanFitness; ring
  rw [haploidStep, hw, mul_div_cancel_left₀ _ hp.ne']

private theorem haploidMeanFitness_equilibrium {s u : ℝ} (hs : 0 < s) :
    haploidMeanFitness s (1 - u / s) = 1 - u := by
  unfold haploidMeanFitness
  rw [sub_sub_cancel, div_mul_cancel₀ _ hs.ne']

private theorem haploidMeanFitness_strictMono {s : ℝ} (hs : 0 < s) :
    StrictMono (haploidMeanFitness s) := by
  intro p q hpq
  unfold haploidMeanFitness
  exact sub_lt_sub_left (mul_lt_mul_of_pos_right (sub_lt_sub_left hpq 1) hs) 1

private theorem haploidStep_sign {s u p : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hp : 0 < p) :
    (p < haploidStep s u p ↔ p < 1 - u / s) ∧
      (haploidStep s u p < p ↔ 1 - u / s < p) := by
  have hw := (haploidMeanFitness_pos_iff hs hs₁ hp.le).2 (Or.inr hp)
  have he := haploidMeanFitness_equilibrium (u := u) hs
  have hmono := haploidMeanFitness_strictMono hs
  unfold haploidStep
  constructor
  · rw [lt_div_iff₀ hw, mul_lt_mul_iff_right₀ hp, ← he, hmono.lt_iff_lt]
  · rw [div_lt_iff₀ hw, mul_lt_mul_iff_right₀ hp, ← he, hmono.lt_iff_lt]

private theorem haploidStep_fixed_iff {s u p : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hp : 0 ≤ p) :
    (0 < haploidMeanFitness s p ∧ haploidStep s u p = p) ↔
      (s < 1 ∧ p = 0) ∨ (u < s ∧ p = 1 - u / s) := by
  rcases eq_or_lt_of_le hp with rfl | hp'
  · have hne : u < s → (0 : ℝ) ≠ 1 - u / s := fun hu ↦
      ne_of_lt (sub_pos.mpr ((div_lt_one hs).2 hu))
    by_cases hu : u < s
    · simp [haploidMeanFitness_pos_iff hs hs₁ le_rfl, haploidStep, hne hu]
    · simp [haploidMeanFitness_pos_iff hs hs₁ le_rfl, haploidStep, hu]
  · have hw := (haploidMeanFitness_pos_iff hs hs₁ hp).2 (Or.inr hp')
    have he := haploidMeanFitness_equilibrium (u := u) hs
    have hfix : haploidStep s u p = p ↔ p = 1 - u / s := by
      rw [haploidStep, div_eq_iff hw.ne', mul_right_inj' hp'.ne', ← he, eq_comm]
      exact (haploidMeanFitness_strictMono hs).injective.eq_iff
    constructor
    · rintro ⟨_, h⟩
      have hpe := hfix.1 h
      have hpos : 0 < 1 - u / s := hpe ▸ hp'
      exact Or.inr ⟨(div_lt_one hs).1 (sub_pos.1 hpos), hpe⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact (hp'.ne' h).elim
      · exact ⟨hw, hfix.2 h⟩

private theorem haploidOrbit_mono {f : ℝ → ℝ} {p : ℝ} (hp : p ∈ Ioc 0 1)
    (hf : MapsTo f (Ioc 0 1) (Ioc 0 1)) (hm : MonotoneOn f (Ioc 0 1)) (h : p ≤ f p) :
    Monotone (fun n : ℕ ↦ f^[n] p) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using
      hm ((hf.iterate n) hp) ((hf.iterate (n + 1)) hp) ih

private theorem haploidOrbit_anti {f : ℝ → ℝ} {p : ℝ} (hp : p ∈ Ioc 0 1)
    (hf : MapsTo f (Ioc 0 1) (Ioc 0 1)) (hm : MonotoneOn f (Ioc 0 1)) (h : f p ≤ p) :
    Antitone (fun n : ℕ ↦ f^[n] p) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using
      hm ((hf.iterate (n + 1)) hp) ((hf.iterate n) hp) ih

private theorem haploidOrbit_fixed_of_tendsto {s u p l : ℝ}
    (hl : Tendsto (fun n : ℕ ↦ (haploidStep s u)^[n] p) atTop (𝓝 l))
    (hw : 0 < haploidMeanFitness s l) : haploidStep s u l = l := by
  have hc : ContinuousAt (haploidStep s u) l := by
    unfold haploidStep haploidMeanFitness
    exact (continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.sub ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))
      hw.ne'
  exact isFixedPt_of_tendsto_iterate hl hc

/-- In the two-allele haploid model with `0 < s ≤ 1` and `0 < u < 1`, selection followed by
one-way mutation gives `step p = p * (1 - u) / w p`, where `w p = 1 - (1 - p) * s` is the
mean fitness. This quotient represents a transition only when `w p > 0`, excluding the
all-mutant lethal state `s = 1`, `p = 0` (Lean's zero-denominator value is not a generation).
Positive-frequency orbits remain in `(0, 1]`.

For `s < 1` the map is strictly increasing on `[0, 1]` and zero is a fixed point. For `s = 1`
it is constant `1 - u` on `(0, 1]`. On that positive-frequency interval the sign of `step p - p`
agrees with the sign of `(1 - u / s) - p`. An interior fixed point exists exactly when `u < s`;
it is `pₑ = 1 - u / s`, with mutant frequency `u / s`, mean fitness `1 - u`, and load `u`.
Every positive-frequency orbit converges monotonically to `pₑ` when `u < s`, and decreases to
zero when `s ≤ u`. -/
public theorem haploid_mutation_selection_balance {s u : ℝ}
    (hs : 0 < s) (hs₁ : s ≤ 1) (hu : 0 < u) (hu₁ : u < 1) :
    let w : ℝ → ℝ := fun p ↦ 1 - (1 - p) * s
    let step : ℝ → ℝ := fun p ↦ p * (1 - u) / w p
    let orbit : ℝ → ℕ → ℝ := fun p n ↦ step^[n] p
    let pe := 1 - u / s
    (∀ p ∈ Icc 0 1, 0 < w p ↔ s < 1 ∨ 0 < p) ∧
    (∀ p ∈ Ioc 0 1, ∀ n, orbit p n ∈ Ioc 0 1) ∧
    (∀ p ∈ Icc 0 1, (0 < w p ∧ step p = p) ↔ (s < 1 ∧ p = 0) ∨ (u < s ∧ p = pe)) ∧
    (s < 1 → StrictMonoOn step (Icc 0 1)) ∧
    (s = 1 → ∀ p ∈ Ioc 0 1, step p = 1 - u) ∧
    (∀ p ∈ Ioc 0 1, (p < step p ↔ p < pe) ∧ (step p < p ↔ pe < p)) ∧
    (u < s → pe ∈ Ioo 0 1 ∧ 1 - pe = u / s ∧ w pe = 1 - u ∧ 1 - w pe = u ∧
      ∀ p ∈ Ioc 0 1, Tendsto (orbit p) atTop (𝓝 pe) ∧
        (p ≤ pe → Monotone (orbit p)) ∧ (pe ≤ p → Antitone (orbit p))) ∧
    (s ≤ u → ∀ p ∈ Ioc 0 1, Tendsto (orbit p) atTop (𝓝 0) ∧ StrictAnti (orbit p)) := by
  let pe := 1 - u / s
  let f := haploidStep s u
  have hmaps := haploidStep_mapsTo hs hs₁ hu hu₁
  have hmono := haploidStep_mono hs hs₁ hu₁
  have hsign (p : ℝ) (hp : p ∈ Ioc 0 1) := haploidStep_sign (u := u) hs hs₁ hp.1
  have horbit (p : ℝ) (hp : p ∈ Ioc 0 1) (n : ℕ) : f^[n] p ∈ Ioc 0 1 := (hmaps.iterate n) hp
  refine ⟨fun _ hp ↦ haploidMeanFitness_pos_iff hs hs₁ hp.1, horbit,
    fun _ hp ↦ haploidStep_fixed_iff hs hs₁ hp.1,
    fun h ↦ haploidStep_strictMono hs h hu₁, ?_, hsign, ?_, ?_⟩
  · rintro rfl p hp
    exact haploidStep_lethal hp.1
  · intro hlt
    have he : pe ∈ Ioo 0 1 := ⟨sub_pos.mpr ((div_lt_one hs).2 hlt),
      sub_lt_self _ (div_pos hu hs)⟩
    have hwe := haploidMeanFitness_equilibrium (u := u) hs
    have hfix : f pe = pe :=
      ((haploidStep_fixed_iff hs hs₁ he.1.le).2 (Or.inr ⟨hlt, rfl⟩)).2
    refine ⟨he, sub_sub_cancel _ _, hwe, ?_, ?_⟩
    · change 1 - haploidMeanFitness s pe = u
      rw [hwe, sub_sub_cancel]
    intro p hp
    let a : ℕ → ℝ := fun n ↦ f^[n] p
    have hm (h : p ≤ pe) : Monotone a := haploidOrbit_mono hp hmaps hmono (le_of_not_gt
      (fun hn ↦ not_lt_of_ge h ((hsign p hp).2.1 hn)))
    have ha (h : pe ≤ p) : Antitone a := haploidOrbit_anti hp hmaps hmono (le_of_not_gt
      (fun hn ↦ not_lt_of_ge h ((hsign p hp).1.1 hn)))
    refine ⟨?_, hm, ha⟩
    have hlim : ∃ l : ℝ, 0 < l ∧ Tendsto a atTop (𝓝 l) := by
      rcases le_total p pe with h | h
      · have hb : BddAbove (range a) := ⟨1, by rintro _ ⟨n, rfl⟩; exact (horbit p hp n).2⟩
        have ht := tendsto_atTop_ciSup (hm h) hb
        exact ⟨_, hp.1.trans_le (by
          apply ge_of_tendsto' ht
          intro n
          simpa only [a, Function.iterate_zero_apply] using (hm h) (Nat.zero_le n)), ht⟩
      · have hbound (n : ℕ) : pe ≤ a n := by
          change pe ≤ f^[n] p
          induction n with
          | zero => simpa using h
          | succ n ih =>
            rw [Function.iterate_succ_apply', ← hfix]
            exact hmono ⟨he.1, he.2.le⟩ (horbit p hp n) ih
        have hb : BddBelow (range a) := ⟨pe, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
        have ht := tendsto_atTop_ciInf (ha h) hb
        exact ⟨_, he.1.trans_le (ge_of_tendsto' ht hbound), ht⟩
    obtain ⟨l, hl, ht⟩ := hlim
    have hw := (haploidMeanFitness_pos_iff hs hs₁ hl.le).2 (Or.inr hl)
    have hle : l = pe := by
      rcases (haploidStep_fixed_iff (u := u) hs hs₁ hl.le).1
          ⟨hw, haploidOrbit_fixed_of_tendsto ht hw⟩ with hz | heq
      · exact (hl.ne' hz.2).elim
      · exact heq.2
    change Tendsto a atTop (𝓝 pe)
    rwa [← hle]
  · intro hsu p hp
    have hpe : pe ≤ 0 := sub_nonpos.mpr ((le_div_iff₀ hs).2 (by simpa using hsu))
    have ha : StrictAnti (fun n : ℕ ↦ f^[n] p) := by
      apply strictAnti_nat_of_succ_lt
      intro n
      rw [Function.iterate_succ_apply']
      exact ((hsign _ (horbit p hp n)).2.2 (hpe.trans_lt (horbit p hp n).1))
    refine ⟨?_, ha⟩
    have ht := tendsto_atTop_ciInf ha.antitone
      (show BddBelow (range (fun n : ℕ ↦ f^[n] p)) from
        ⟨0, by rintro _ ⟨n, rfl⟩; exact (horbit p hp n).1.le⟩)
    have hl := ge_of_tendsto' ht (fun n ↦ (horbit p hp n).1.le)
    have hw := (haploidMeanFitness_pos_iff hs hs₁ hl).2 (Or.inl (hsu.trans_lt hu₁))
    rcases (haploidStep_fixed_iff (u := u) hs hs₁ hl).1
        ⟨hw, haploidOrbit_fixed_of_tendsto ht hw⟩ with hz | he
    · exact hz.2 ▸ ht
    · exact (not_lt_of_ge hsu he.1).elim

end MathlibExt.Biology.PopulationGenetics
