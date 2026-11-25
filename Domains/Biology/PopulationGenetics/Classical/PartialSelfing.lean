/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Inbreeding coefficient under partial self-fertilization

The one-generation model partitions offspring by unrelated outcrossing, selfing with two draws of
one parental gene copy, and selfing with draws of distinct parental gene copies.

J. Felsenstein, *Theoretical Evolutionary Genetics* (December 2019), §V.9, pp. 231–232,
equations (V-21)–(V-24), gives the first-step argument for complete selfing. The mixture with
unrelated outcrossing and the formulas with arbitrary initial inbreeding are derived here.
-/

open Filter Set Topology

namespace MathlibExt.Biology.PopulationGenetics.PartialSelfing

private inductive MatingCase where
  | outcross
  | selfSameCopy
  | selfDistinctCopies

private noncomputable def caseWeight (S : ℝ) : MatingCase → ℝ
  | .outcross => 1 - S
  | .selfSameCopy => S * (1 / 2)
  | .selfDistinctCopies => S * (1 / 2)

private noncomputable def ibdGivenCase (F : ℝ) : MatingCase → ℝ
  | .outcross => 0
  | .selfSameCopy => 1
  | .selfDistinctCopies => F

-- Sum the joint IBD probabilities over the three disjoint, exhaustive cases.
-- The assigned conditional probabilities also work when a case has zero weight.
private noncomputable def nextIbd (S F : ℝ) : ℝ :=
  ([MatingCase.outcross, .selfSameCopy, .selfDistinctCopies].map
    fun c => caseWeight S c * ibdGivenCase F c).sum

-- Identity-by-descent probability by generation, starting at `F₀`.
public noncomputable def inbreedingCoeff (S F₀ : ℝ) : ℕ → ℝ
  | 0 => F₀
  | t + 1 => nextIbd S (inbreedingCoeff S F₀ t)

/-- **Inbreeding coefficient under partial self-fertilization.** Each generation is selfed with
probability `S` and otherwise outcrossed to unrelated parents. Given selfing, the two sampled gene
copies come from the same parental copy with probability `1/2` (identity by descent is certain),
and from distinct copies with probability `1/2` (identity by descent has probability `F t`).
Unrelated outcrossing contributes zero. Starting from `F₀ ∈ [0, 1]`, the resulting probabilities
stay in `[0, 1]` and satisfy `F (t + 1) = (S / 2) * (1 + F t)`. For complete selfing, the
complement is `(1 / 2)^t * (1 - F₀)` and the limit is `1`. For `0 ≤ S < 1`, the unique real
fixed point is `S / (2 - S)`; the difference from it is multiplied by `(S / 2)^t` from its
initial value, so the sequence converges to it. -/
public theorem inbreeding_under_partial_selfing (S F₀ : ℝ) (hS : S ∈ Icc 0 1)
    (hF₀ : F₀ ∈ Icc 0 1) :
    let F := inbreedingCoeff S F₀
    F 0 = F₀ ∧
      (∀ t, F t ∈ Icc 0 1) ∧
      (∀ t, F (t + 1) = (S / 2) * (1 + F t)) ∧
      (S = 1 → (∀ t, 1 - F t = (1 / 2 : ℝ) ^ t * (1 - F₀)) ∧ Tendsto F atTop (𝓝 1)) ∧
      (S < 1 →
        let Fstar := S / (2 - S)
        (∀ x : ℝ, (S / 2) * (1 + x) = x ↔ x = Fstar) ∧
          (∀ t, F t - Fstar = (S / 2) ^ t * (F₀ - Fstar)) ∧ Tendsto F atTop (𝓝 Fstar)) := by
  intro F
  have hstep (t : ℕ) : F (t + 1) = (S / 2) * (1 + F t) := by
    change nextIbd S (F t) = _
    simp [nextIbd, caseWeight, ibdGivenCase]
    ring
  have hF (t : ℕ) : F t ∈ Icc 0 1 := by
    induction t with
    | zero => exact hF₀
    | succ t ih =>
      have hhalf : 0 ≤ S / 2 := div_nonneg hS.1 (by norm_num)
      rw [hstep t]
      refine ⟨mul_nonneg hhalf (by linarith [ih.1]), ?_⟩
      calc
        (S / 2) * (1 + F t) ≤ (S / 2) * 2 := by gcongr; linarith [ih.2]
        _ = S := by ring
        _ ≤ 1 := hS.2
  let Fstar := S / (2 - S)
  have hfixed (x : ℝ) : (S / 2) * (1 + x) = x ↔ x = Fstar := by
    have hdenom : 2 - S ≠ 0 := by linarith [hS.2]
    change _ ↔ x = S / (2 - S)
    rw [eq_div_iff hdenom]
    constructor
    · intro hx
      linear_combination -2 * hx
    · intro hx
      linear_combination -(1 / 2) * hx
  have hcenter (t : ℕ) : F t - Fstar = (S / 2) ^ t * (F₀ - Fstar) := by
    have hstar := (hfixed Fstar).2 rfl
    induction t with
    | zero => simp [F, inbreedingCoeff]
    | succ t ih =>
      calc
        F (t + 1) - Fstar = (S / 2) * (F t - Fstar) := by
          rw [hstep]
          linear_combination hstar
        _ = (S / 2) ^ (t + 1) * (F₀ - Fstar) := by rw [ih, pow_succ]; ring
  have hpow : Tendsto (fun t : ℕ => (S / 2) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hS.1]) (by linarith [hS.2])
  have hlim : Tendsto F atTop (𝓝 Fstar) := by
    have heq : F = fun t => (S / 2) ^ t * (F₀ - Fstar) + Fstar := by
      funext t
      linear_combination hcenter t
    rw [heq]
    simpa only [zero_mul, zero_add] using (hpow.mul_const (F₀ - Fstar)).add_const Fstar
  refine ⟨rfl, hF, hstep, ?_, fun _ => ⟨hfixed, hcenter, hlim⟩⟩
  intro h
  have hstar : Fstar = 1 := by norm_num [Fstar, h]
  rw [hstar] at hlim
  refine ⟨fun t => ?_, hlim⟩
  have hc := hcenter t
  rw [hstar, h] at hc
  linear_combination -hc

end MathlibExt.Biology.PopulationGenetics.PartialSelfing
