/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLEvents
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform

/-!
# The KKL inequality under p-biased measures: reflection and threshold consequences

The map `ω ↦ ¬ω` sends the Bernoulli(`p`) product measure to the Bernoulli(`1 - p`) one and
preserves variance, influences, and maximal influence, so the KKL inequality at `p` is
equivalent to the KKL inequality at `1 - p` (`kpb_kkl_reflect`). The predicate
`kpb_PBiasedHC q` asserts the KKL inequality with constant `2` for all `p ∈ (1/2, q)`; under it,
the sharp-threshold bounds of `KKL.KKLWire` hold. The predicate is not proved in this library
for any `q > 1/2`.

## Main definitions

* `StatMech.Probability.kpb_flipAll`: the coordinatewise complement `ω ↦ ¬ω`.
* `StatMech.Probability.kpb_PBiasedHC`: KKL with constant `2` for all `p ∈ (1/2, q)`.

## Main results

* `StatMech.Probability.kpb_kkl_reflect`: KKL at `p` implies KKL at `1 - p`.
* `StatMech.Probability.kpb_sharpThreshold`, `StatMech.Probability.kpb_sharpThreshold_window`:
  sharp-threshold bounds for increasing events under `kpb_PBiasedHC q`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace StatMech

namespace Probability

open ConfigSpace Function Finset StatMech StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The coordinatewise complement `ω ↦ ¬ω` of a configuration. -/
def kpb_flipAll (ω : ConfigSpace E) : ConfigSpace E := fun e => !(ω e)

omit [Fintype E] [DecidableEq E] in
lemma kpb_flipAll_involutive : Function.Involutive (kpb_flipAll (E := E)) := by
  intro ω; funext e; simp [kpb_flipAll]

omit [DecidableEq E] in
/-- Complementing sends the Bernoulli(`p`) weight to the Bernoulli(`1 - p`) weight. -/
lemma kpb_weight_flip (p : ℝ) (ω : ConfigSpace E) :
    OSSS.weight (OSSS.bernoulliWeight (1 - p)) (kpb_flipAll ω)
      = OSSS.weight (OSSS.bernoulliWeight p) ω := by
  unfold OSSS.weight OSSS.bernoulliWeight kpb_flipAll
  apply Finset.prod_congr rfl
  intro e _
  cases ω e <;> simp

lemma kpb_expect_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.expect (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.expect
  rw [Fintype.sum_bijective (kpb_flipAll) (kpb_flipAll_involutive.bijective)
        (fun ω => OSSS.weight (OSSS.bernoulliWeight p) ω * g (kpb_flipAll ω))
        (fun ω => OSSS.weight (OSSS.bernoulliWeight (1 - p)) ω * g ω)
        (fun ω => by simp only [kpb_weight_flip])]

omit [Fintype E] in
lemma kpb_flipAll_setOpen (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setOpen e ω) = StatMech.setClosed e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

omit [Fintype E] in
lemma kpb_flipAll_setClosed (e : E) (ω : ConfigSpace E) :
    kpb_flipAll (StatMech.setClosed e ω) = StatMech.setOpen e (kpb_flipAll ω) := by
  funext e'; unfold kpb_flipAll StatMech.setOpen StatMech.setClosed
  by_cases h : e' = e
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

lemma kpb_infl_flip (p : ℝ) (g : ConfigSpace E → ℝ) (e : E) :
    OSSS.infl (OSSS.bernoulliWeight (1 - p)) g e
      = OSSS.infl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) e := by
  unfold OSSS.infl
  rw [kpb_expect_flip p]
  apply congrArg
  funext ω
  simp only [kpb_flipAll_setOpen, kpb_flipAll_setClosed]
  rw [abs_sub_comm]

lemma kpb_var_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    OSSS.var (OSSS.bernoulliWeight (1 - p)) g
      = OSSS.var (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold OSSS.var OSSS.cov
  rw [kpb_expect_flip p (fun ω => g ω * g ω), kpb_expect_flip p g]

lemma kpb_totalInfl_flip (p : ℝ) (g : ConfigSpace E → ℝ) :
    totalInfl (OSSS.bernoulliWeight (1 - p)) g
      = totalInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold totalInfl
  exact Finset.sum_congr rfl (fun e _ => kpb_infl_flip p g e)

lemma kpb_maxInfl_flip [Nonempty E] (p : ℝ) (g : ConfigSpace E → ℝ) :
    maxInfl (OSSS.bernoulliWeight (1 - p)) g
      = maxInfl (OSSS.bernoulliWeight p) (fun ω => g (kpb_flipAll ω)) := by
  unfold maxInfl
  apply Finset.sup'_congr _ rfl
  intro e _
  exact kpb_infl_flip p g e

/-- The KKL inequality with constant `2` at `p` implies it at `1 - p`. -/
theorem kpb_kkl_reflect {p : ℝ} (H : KKLHypercontractive p 2) :
    KKLHypercontractive (1 - p) 2 := by
  intro E _ _ _ φ
  have hH := H (E := E) (fun ω => φ (kpb_flipAll ω))
  have he : (fun ω => if φ (kpb_flipAll ω) then (1 : ℝ) else 0)
      = (fun ω => (fun ω => if φ ω then (1 : ℝ) else 0) (kpb_flipAll ω)) := rfl
  rw [he] at hH
  rw [kpb_var_flip p, kpb_maxInfl_flip p, kpb_totalInfl_flip p]
  exact hH

/-- The KKL inequality with constant `2` for every Bernoulli parameter `p ∈ (1/2, q)`. Not proved in
  this library for any `q > 1/2`. -/
def kpb_PBiasedHC (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 2

/-- The KKL inequality with constant `0` holds for every `p`; this is trivial. -/
theorem kpb_residue_c0 {q : ℝ} (hq : q ≤ 1) :
    ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, KKLHypercontractive p 0 := by
  intro p hp
  exact kkl_hypercontractive_zero p (by linarith [hp.1]) (by linarith [hp.2])

/-- `kpb_PBiasedHC q` in the form used by `StatMech.TwoDim.kklw_sharpThreshold`. -/
theorem kpb_Hbkkkl {q : ℝ} (Hpb : kpb_PBiasedHC q) :
    ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), KKLHypercontractive p 2 := by
  intro p hp
  rw [interior_Icc] at hp
  exact Hpb p hp

/-- `StatMech.TwoDim.kklw_sharpThreshold` under `kpb_PBiasedHC q`. -/
theorem kpb_sharpThreshold {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A) :
    1 / 2 + (2 * v₀ * L) * (q - 1 / 2) ≤ StatMech.prob q A := by
  classical
  exact StatMech.TwoDim.kklw_sharpThreshold A hA hq hv0 hL hhalf (kpb_Hbkkkl Hpb) hvar hLL'

/-- `StatMech.TwoDim.kklw_sharpThreshold_window` under `kpb_PBiasedHC q`. -/
theorem kpb_sharpThreshold_window {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q v₀ L ε : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hM : 0 < 2 * v₀ * L)
    (hhalf : StatMech.prob (1 / 2) A = 1 / 2)
    (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (Hpb : kpb_PBiasedHC q)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      v₀ ≤ StatMech.prob p A * (1 - StatMech.prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      L ≤ StatMech.TwoDim.kklw_logMaxInfl p A)
    (hnotyet : StatMech.prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / (2 * v₀ * L) := by
  classical
  exact StatMech.TwoDim.kklw_sharpThreshold_window A hA hq hM hhalf hv0 hL (kpb_Hbkkkl Hpb)
    hvar hLL' hnotyet

end Probability

end StatMech
