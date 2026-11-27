/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.TietzeExtension

/-!
# Mazur's Problem 24

We use the Boolean series construction of Labuda and Mauldin
(<https://doi.org/10.4064/cm-48-1-89-91>). For the Borel hypothesis here, Baire category
on the ternary Cantor set suffices: two points of a bounded-value set can be found that
differ by a single late bit.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24Wanted

open Filter Set Topology

private theorem exists_small_large {E : Type*} [NormedAddCommGroup E] (f : E →+ ℝ)
    (hf : ¬ Continuous f) {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ x, ‖x‖ < r ∧ M < ‖f x‖ := by
  have h : ¬ ContinuousAt f 0 := fun h₀ ↦ hf (continuous_of_continuousAt_zero f h₀)
  rw [Metric.continuousAt_iff] at h
  push Not at h
  obtain ⟨ε, hε, h⟩ := h
  obtain ⟨k, hk⟩ := exists_nat_gt (max 0 (M / ε))
  have hk₀ : (0 : ℝ) < k := (le_max_left _ _).trans_lt hk
  obtain ⟨x, hx, hfx⟩ := h (r / k) (div_pos hr hk₀)
  simp only [f.map_zero, dist_zero_right] at hx hfx
  have hx' : ‖k • x‖ < r := by
    calc
      ‖k • x‖ ≤ (k : ℝ) * ‖x‖ := norm_nsmul_le
      _ = ‖x‖ * (k : ℝ) := mul_comm _ _
      _ < r := (lt_div_iff₀ hk₀).1 hx
  refine ⟨k • x, hx', ?_⟩
  rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_of_nonneg hk₀.le]
  exact (div_lt_iff₀ hε |>.1 ((le_max_right _ _).trans_lt hk)).trans_le
    (mul_le_mul_of_nonneg_left hfx hk₀.le)

private noncomputable def cantorSum {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (a : ℕ → Bool) : E := ∑' i, if a i then u i else 0

private theorem summable_cantorTerms {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {u : ℕ → E} (hu : Summable fun i ↦ ‖u i‖) (a : ℕ → Bool) :
    Summable fun i ↦ if a i then u i else 0 :=
  hu.of_norm_bounded fun i ↦ by split <;> simp

private theorem exists_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {u : ℕ → E} (hu : Summable fun i ↦ ‖u i‖) :
    ∃ (e : C(ℕ → Bool, Icc (0 : ℝ) 1)) (c : C(Icc (0 : ℝ) 1, E)),
      ∀ a, c (e a) = cantorSum u a := by
  let e : C(ℕ → Bool, Icc (0 : ℝ) 1) :=
    ⟨inclusion cantorSet_subset_unitInterval ∘ cantorSetHomeomorphNatToBool.symm,
      (continuous_inclusion cantorSet_subset_unitInterval).comp
        cantorSetHomeomorphNatToBool.symm.continuous⟩
  have he : IsClosedEmbedding e := e.continuous.isClosedEmbedding
    ((inclusion_injective cantorSet_subset_unitInterval).comp
      cantorSetHomeomorphNatToBool.symm.injective)
  -- Extend the bit functions with their range still in the unit interval.
  have hcoord (i : ℕ) : ∃ g : C(Icc (0 : ℝ) 1, ℝ),
      (∀ t, g t ∈ Icc (0 : ℝ) 1) ∧ ∀ a, g (e a) = if a i then 1 else 0 := by
    let bit : Bool → ℝ := fun a ↦ if a then 1 else 0
    let b : C(ℕ → Bool, ℝ) :=
      ⟨bit ∘ (fun a ↦ a i), (continuous_of_discreteTopology (f := bit)).comp (continuous_apply i)⟩
    have hb (a : ℕ → Bool) : b a ∈ Icc (0 : ℝ) 1 := by
      change (if a i then 1 else 0) ∈ Icc (0 : ℝ) 1
      split <;> simp
    obtain ⟨g, hg, hge⟩ := b.exists_extension_forall_mem_of_isClosedEmbedding hb
      (nonempty_Icc.2 zero_le_one) he
    exact ⟨g, hg, fun a ↦ congrFun hge a⟩
  choose g hg hge using hcoord
  have hnorm (i : ℕ) (t : Icc (0 : ℝ) 1) : ‖g i t • u i‖ ≤ ‖u i‖ := by
    rw [norm_smul, Real.norm_of_nonneg (hg i t).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hg i t).2
  refine ⟨e, ⟨fun t ↦ ∑' i, g i t • u i,
    continuous_tsum (fun i ↦ (g i).continuous.smul continuous_const) hu hnorm⟩, fun a ↦ ?_⟩
  change (∑' i, g i (e a) • u i) = ∑' i, if a i then u i else 0
  apply tsum_congr
  intro i
  rw [hge]
  split <;> simp

private def flip (n : ℕ) : (ℕ → Bool) ≃ₜ (ℕ → Bool) := by
  let f (a : ℕ → Bool) (i : ℕ) := if i = n then !(a i) else a i
  have hf : Function.Involutive f := by
    intro a
    funext i
    by_cases hi : i = n <;> simp [f, hi]
  have hc : Continuous f := continuous_pi fun i ↦ by
    change Continuous (fun a : ℕ → Bool ↦ if i = n then !(a i) else a i)
    split
    · exact (continuous_of_discreteTopology (f := Bool.not)).comp (continuous_apply i)
    · exact continuous_apply i
  exact ⟨hf.toPerm, hc, hc⟩

private theorem flip_apply (n : ℕ) (a : ℕ → Bool) (i : ℕ) :
    flip n a i = if i = n then !(a i) else a i := rfl

private theorem exists_bounded_flip {g : (ℕ → Bool) → ℝ} (hg : Measurable g) :
    ∃ (N n : ℕ) (a : ℕ → Bool), N ≤ n ∧ ‖g a‖ ≤ N ∧ ‖g (flip n a)‖ ≤ N := by
  let S (N : ℕ) : Set (ℕ → Bool) := {a | ‖g a‖ ≤ N}
  have hS (N : ℕ) : MeasurableSet (S N) :=
    measurableSet_le (continuous_norm.measurable.comp hg) measurable_const
  choose U hU hSU using fun N ↦ (hS N).residualEq_isOpen
  -- Make the open approximations valid at the chosen point and at all its bit flips.
  have hmem : ∀ᶠ a in residual (ℕ → Bool), ∀ N, a ∈ S N ↔ a ∈ U N :=
    eventually_countable_forall.2 fun N ↦ (hSU N).mem_iff
  have hflip : ∀ᶠ a in residual (ℕ → Bool), ∀ n N, flip n a ∈ S N ↔ flip n a ∈ U N :=
    eventually_countable_forall.2 fun n ↦
      (tendsto_residual_of_isOpenMap (flip n).continuous (flip n).isOpenMap).eventually hmem
  obtain ⟨a, ha, haflip⟩ := (dense_of_mem_residual (hmem.and hflip)).nonempty
  obtain ⟨N, hN⟩ := exists_nat_ge ‖g a‖
  have haU : a ∈ U N := (ha N).1 hN
  have hlim : Tendsto (fun n ↦ flip n a) atTop (𝓝 a) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_atTop_of_eventually_const (i₀ := i + 1)
    intro n hn
    simp [flip_apply, (Nat.lt_of_succ_le hn).ne]
  have hlate : ∀ᶠ n in atTop, flip n a ∈ U N := hlim.eventually ((hU N).mem_nhds haU)
  obtain ⟨n, hnU, hn⟩ := (hlate.and (eventually_ge_atTop N)).exists
  exact ⟨N, n, a, hn, hN, (haflip n N).2 hnU⟩

private theorem cantorSum_flip_sub {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {u : ℕ → E} (hu : Summable fun i ↦ ‖u i‖) (n : ℕ) (a : ℕ → Bool) :
    cantorSum u (flip n a) - cantorSum u a = if a n then -u n else u n := by
  unfold cantorSum
  rw [← (summable_cantorTerms hu (flip n a)).tsum_sub (summable_cantorTerms hu a)]
  rw [tsum_eq_single n (fun i hi ↦ by simp [flip_apply, hi])]
  cases h : a n <;> simp [flip_apply, h]

/--
**Mazur's Problem 24: additive functionals measurable along curves are continuous.** Let $E$
be a real Banach space and let $F \colon E \to \mathbb{R}$ be additive, that is,
$F(x + y) = F(x) + F(y)$ for all $x, y \in E$. If for every continuous map
$x \colon [0, 1] \to E$ the function $t \mapsto F(x(t))$ on $[0, 1]$ is Borel measurable,
then $F$ is continuous.

Source: S. Mazur, Problem 24 of the Scottish Book (prize: two small beers).
Solved affirmatively by I. Labuda and R. D. Mauldin, "Problem 24 of the
Scottish Book concerning additive functionals", Colloquium Mathematicum 48,
as quoted in Ger (2016); the proof covers additive operators into a
Hausdorff topological vector space.
-/
theorem additiveFunctionalMeasurableOnCurvesContinuous :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : E → ℝ), (∀ x y, F (x + y) = F x + F y) →
      (∀ (x : C(↥(Set.Icc (0 : ℝ) 1), E)), Measurable fun t => F (x t)) →
      Continuous F := by
  intro E _ _ _ F hadd hcurve
  let f : E →+ ℝ := AddMonoidHom.mk' F hadd
  by_contra hF
  have hex (n : ℕ) : ∃ x, ‖x‖ < (1 / 2 : ℝ) ^ n ∧ 2 * n < ‖f x‖ :=
    exists_small_large f hF (pow_pos (by norm_num) _) (2 * n)
  choose u hu hfu using hex
  have hu' : Summable fun n ↦ ‖u n‖ :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun n ↦ (hu n).le)
  have hg : Measurable fun a : ℕ → Bool ↦ f (cantorSum u a) := by
    obtain ⟨e, c, hce⟩ := exists_curve hu'
    change Measurable fun a : ℕ → Bool ↦ F (cantorSum u a)
    simpa only [Function.comp_def, hce] using (hcurve c).comp e.continuous.measurable
  obtain ⟨N, n, a, hn, ha, hflip⟩ := exists_bounded_flip hg
  have hnorm : ‖f (cantorSum u (flip n a)) - f (cantorSum u a)‖ = ‖f (u n)‖ := by
    rw [← map_sub, cantorSum_flip_sub hu']
    split <;> simp
  have hle : ‖f (u n)‖ ≤ (N : ℝ) + N :=
    hnorm ▸ (norm_sub_le _ _).trans (add_le_add hflip ha)
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  linarith [hfu n]

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook24Wanted
