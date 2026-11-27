/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import MathlibExt.Topology.Homotopy.BorsukUlam
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory
open Metric
open scoped InnerProductSpace MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.HamSandwichWanted

/-- Level sets of a nonzero linear functional (or any level when the offset is
nonzero) are add-Haar-null. -/
private theorem hs_addHaar_setOf_inner_eq_null
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (ν : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure ν]
    (w : E) (c : ℝ) (h : w ≠ 0 ∨ c ≠ 0) :
    ν {x | ⟪w, x⟫_ℝ = c} = 0 := by
  rcases eq_or_ne w 0 with rfl | hw
  · rcases h with h0 | hc
    · exact absurd rfl h0
    · have hempty : {x : E | ⟪(0 : E), x⟫_ℝ = c} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [Set.mem_ofPred_eq, inner_zero_left] at hx
        exact hc hx.symm
      rw [hempty, MeasureTheory.measure_empty]
  · have hnorm2 : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
    set K : Submodule ℝ E := LinearMap.ker (innerₛₗ ℝ w) with hK
    set p : E := (c / ‖w‖ ^ 2) • w with hp
    set s : AffineSubspace ℝ E := AffineSubspace.mk' p K with hs
    have hmem : ∀ x : E, (⟪w, x⟫_ℝ = c) ↔ x ∈ s := by
      intro x
      rw [hs, AffineSubspace.mem_mk', hK, LinearMap.mem_ker, innerₛₗ_apply_apply,
        vsub_eq_sub]
      have key : ⟪w, x - p⟫_ℝ = ⟪w, x⟫_ℝ - c := by
        rw [hp, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
          div_mul_cancel₀ _ hnorm2]
      rw [key]
      constructor
      · intro hxx
        linarith
      · intro hxx
        linarith
    have hset : {x : E | ⟪w, x⟫_ℝ = c} = ↑s := Set.ext fun x => hmem x
    have hdir : K ≠ ⊤ := by
      intro htop
      have hmemK : w ∈ K := by
        rw [htop]
        exact Submodule.mem_top
      rw [hK, LinearMap.mem_ker, innerₛₗ_apply_apply] at hmemK
      exact hw (inner_self_eq_zero.mp hmemK)
    have hstop : s ≠ ⊤ := by
      intro htop
      apply hdir
      have h1 : s.direction = ⊤ := by
        rw [htop]
        exact AffineSubspace.direction_top ℝ E E
      rwa [hs, AffineSubspace.direction_mk'] at h1
    rw [hset]
    exact MeasureTheory.Measure.addHaar_affineSubspace ν s hstop

/-- Closed half-spaces and hyperplanes cut out by a continuous linear functional
are measurable. -/
private theorem hs_measurableSet_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (w : E) (c : ℝ) : MeasurableSet {x | ⟪w, x⟫_ℝ ≤ c} :=
  (isClosed_le (continuous_const.inner continuous_id) continuous_const).measurableSet

private theorem hs_measurableSet_inner_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (w : E) (c : ℝ) : MeasurableSet {x | ⟪w, x⟫_ℝ ≥ c} :=
  (isClosed_le continuous_const (continuous_const.inner continuous_id)).measurableSet

private theorem hs_measurableSet_inner_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (w : E) (c : ℝ) : MeasurableSet {x | ⟪w, x⟫_ℝ = c} :=
  (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet

/-- The two closed half-spaces overlap in the hyperplane and cover everything. -/
private theorem hs_measure_le_add_measure_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) (w : E) (c : ℝ) :
    μ {x | ⟪w, x⟫_ℝ ≤ c} + μ {x | ⟪w, x⟫_ℝ ≥ c} =
      μ Set.univ + μ {x | ⟪w, x⟫_ℝ = c} := by
  have hunion : {x : E | ⟪w, x⟫_ℝ ≤ c} ∪ {x | ⟪w, x⟫_ℝ ≥ c} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    exact le_total _ _
  have hinter : {x : E | ⟪w, x⟫_ℝ ≤ c} ∩ {x | ⟪w, x⟫_ℝ ≥ c} = {x | ⟪w, x⟫_ℝ = c} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  have h := MeasureTheory.measure_union_add_inter (μ := μ) {x : E | ⟪w, x⟫_ℝ ≤ c}
    (hs_measurableSet_inner_ge w c)
  rw [hunion, hinter] at h
  exact h.symm

/-- In `ℝ≥0∞`, `a = b` and `a + b = U` force both to be `U / 2`, with no
finiteness needed. -/
private theorem hs_eq_half_of_add_eq {a b U : ENNReal} (hab : a = b) (hadd : a + b = U) :
    a = U / 2 ∧ b = U / 2 := by
  subst hab
  have h2ne : (2 : ENNReal) ≠ 0 := by norm_num
  have h2top : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hmul : a * 2 = U := by
    rw [mul_comm, two_mul]
    exact hadd
  have ha : a = U / 2 := by
    apply le_antisymm
    · rw [ENNReal.le_div_iff_mul_le (Or.inl h2ne) (Or.inl h2top)]
      exact le_of_eq hmul
    · rw [ENNReal.div_le_iff h2ne h2top]
      exact le_of_eq hmul.symm
  exact ⟨ha, ha⟩

/-- Tail projection `EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n)`,
dropping the `0`-th (head) coordinate. -/
private def hsTail {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j => u (Fin.succ j)

private theorem hs_continuous_tail {n : ℕ} : Continuous (@hsTail n) := by
  unfold hsTail
  fun_prop

private theorem hs_continuous_head {n : ℕ} :
    Continuous fun u : EuclideanSpace ℝ (Fin (n + 1)) => u 0 := by
  fun_prop

private theorem hs_tail_neg {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    hsTail (-u) = -(hsTail u) := by
  ext j
  simp only [hsTail, PiLp.toLp_apply, PiLp.neg_apply]

private theorem hs_head_neg {n : ℕ} (u : EuclideanSpace ℝ (Fin (n + 1))) :
    (-u) 0 = -(u 0) :=
  PiLp.neg_apply (fun _ : Fin (n + 1) => ℝ) u 0

private theorem hs_norm_sq_eq_head_sq_add_tail {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖u‖ ^ 2 = (u 0) ^ 2 + ‖hsTail u‖ ^ 2 := by
  have htail : ∀ j : Fin n, hsTail u j = u (Fin.succ j) := fun j => rfl
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp_rw [htail]

private theorem hs_head_eq_one_or_neg_one_of_tail_eq_zero {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) (h1 : ‖u‖ = 1) (h0 : hsTail u = 0) :
    u 0 = 1 ∨ u 0 = -1 := by
  have hnorm : ‖hsTail u‖ = 0 := by
    rw [h0, norm_zero]
  have h2 : (u 0) ^ 2 = 1 := by
    have h := hs_norm_sq_eq_head_sq_add_tail u
    rw [h1, hnorm] at h
    simpa using h.symm
  exact sq_eq_one_iff.mp h2

private theorem hs_tail_ne_zero_or_head_ne_zero {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) (h1 : ‖u‖ = 1) :
    hsTail u ≠ 0 ∨ u 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h := hs_norm_sq_eq_head_sq_add_tail u
  rw [h1, hcon.1, hcon.2] at h
  simp at h

/-- Off the exceptional hyperplane, membership in the moving half-space is
eventually constant. -/
private theorem hs_eventually_mem_halfspace_iff {n : ℕ}
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : EuclideanSpace ℝ (Fin n))
    (hne : ⟪hsTail u, x⟫_ℝ ≠ u 0) :
    ∀ᶠ u' in nhds u, ((⟪hsTail u', x⟫_ℝ ≤ u' 0) ↔ (⟪hsTail u, x⟫_ℝ ≤ u 0)) := by
  have hcont1 : ContinuousAt
      (fun u' : EuclideanSpace ℝ (Fin (n + 1)) => ⟪hsTail u', x⟫_ℝ) u :=
    (hs_continuous_tail.inner continuous_const).continuousAt
  have hcont2 : ContinuousAt
      (fun u' : EuclideanSpace ℝ (Fin (n + 1)) => u' 0) u :=
    hs_continuous_head.continuousAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hev := hcont1.eventually_lt hcont2 hlt
    exact hev.mono fun u' hu' => ⟨fun _ => hlt.le, fun _ => hu'.le⟩
  · have hev := hcont2.eventually_lt hcont1 hgt
    exact hev.mono fun u' hu' =>
      ⟨fun hle => (not_le_of_gt hu' hle).elim, fun hle => (not_le_of_gt hgt hle).elim⟩

/-- The mass of a moving closed half-space is continuous at any parameter whose
exceptional hyperplane is null. -/
private theorem hs_continuousAt_measure_halfspace {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hZ : μ {x | ⟪hsTail u, x⟫_ℝ = u 0} = 0) :
    ContinuousAt (fun u' => μ {x | ⟪hsTail u', x⟫_ℝ ≤ u' 0}) u := by
  have hmeas : ∀ u' : EuclideanSpace ℝ (Fin (n + 1)),
      MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u', x⟫_ℝ ≤ u' 0} :=
    fun u' => hs_measurableSet_inner_le _ _
  have hae : ∀ᵐ x ∂μ, ∀ᶠ u' in nhds u,
      (x ∈ {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u', x⟫_ℝ ≤ u' 0}) ↔
      (x ∈ {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u, x⟫_ℝ ≤ u 0}) := by
    have hZae := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hZ
    filter_upwards [hZae] with x hx
    have hne : ⟪hsTail u, x⟫_ℝ ≠ u 0 := fun heq => hx heq
    exact hs_eventually_mem_halfspace_iff u x hne
  exact MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (nhds u) (hs_measurableSet_inner_le _ _) hmeas hae

/-- The bisection map from the sphere to `EuclideanSpace ℝ (Fin n)` is
continuous. -/
private theorem hs_continuous_bisectionMap {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n)))
    (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    Continuous (fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
      (WithLp.toLp 2 fun i =>
        ((μ i) {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0}).toReal :
        EuclideanSpace ℝ (Fin n))) := by
  have hcoord : ∀ i : Fin n, Continuous
      (fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        ((μ i) {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0}).toReal) := by
    intro i
    rw [continuous_iff_continuousAt]
    intro u
    have hu1 : ‖(u : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp u.2
    have hZ : μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ =
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0} = 0 := by
      rcases hs_tail_ne_zero_or_head_ne_zero _ hu1 with htail | hhead
      · have hvol : volume {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ =
            (u : EuclideanSpace ℝ (Fin (n + 1))) 0} = 0 :=
          hs_addHaar_setOf_inner_eq_null volume _ _ (Or.inl htail)
        exact (hac i) hvol
      · have hvol : volume {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ =
            (u : EuclideanSpace ℝ (Fin (n + 1))) 0} = 0 :=
          hs_addHaar_setOf_inner_eq_null volume _ _ (Or.inr hhead)
        exact (hac i) hvol
    have hval : ContinuousAt
        (Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
          EuclideanSpace ℝ (Fin (n + 1))) u :=
      continuous_subtype_val.continuousAt
    have hmeas : ContinuousAt
        (fun u' : EuclideanSpace ℝ (Fin (n + 1)) =>
          μ i {x | ⟪hsTail u', x⟫_ℝ ≤ u' 0}) (u : EuclideanSpace ℝ (Fin (n + 1))) :=
      @hs_continuousAt_measure_halfspace _ _ _ (μ i) (hfin i) _ hZ
    have hcomp : ContinuousAt
        (fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
          μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
            (u : EuclideanSpace ℝ (Fin (n + 1))) 0}) u :=
      hmeas.comp hval
    have hfin' : μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0} ≠ ⊤ :=
      @measure_ne_top _ _ (μ i) (hfin i) _
    exact (ENNReal.continuousAt_toReal hfin').comp
      (f := fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
        μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0}) hcomp
  have hpi : Continuous
      (fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 => fun i : Fin n =>
        ((μ i) {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0}).toReal) :=
    continuous_pi fun i => hcoord i
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp hpi

/-- Borsuk–Ulam applied to the bisection map yields a sphere point whose
half-space and opposite half-space have equal mass for every measure. -/
private theorem hs_exists_antipodal_eq {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n)))
    (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ∀ i : Fin n,
      μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0} =
      μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≥
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0} := by
  obtain ⟨u, hu⟩ := MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam
    (fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
      (WithLp.toLp 2 fun i =>
        ((μ i) {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0}).toReal :
        EuclideanSpace ℝ (Fin n)))
    (hs_continuous_bisectionMap μ hfin hac)
  refine ⟨u, fun i => ?_⟩
  have h2 : ((μ i) {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0}).toReal =
      ((μ i) {x | ⟪hsTail ((-u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
        EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
        (((-u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
          EuclideanSpace ℝ (Fin (n + 1)))) 0}).toReal := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hu
    rw [PiLp.toLp_apply, PiLp.toLp_apply] at h
    exact h
  have hne1 : μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
      (u : EuclideanSpace ℝ (Fin (n + 1))) 0} ≠ ⊤ :=
    @measure_ne_top _ _ (μ i) (hfin i) _
  have hne2 : μ i {x | ⟪hsTail ((-u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
      EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
      (((-u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
        EuclideanSpace ℝ (Fin (n + 1)))) 0} ≠ ⊤ :=
    @measure_ne_top _ _ (μ i) (hfin i) _
  have heq := (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp h2
  have hset : {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail ((-u : sphere (0 :
      EuclideanSpace ℝ (Fin (n + 1))) 1) : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≤
      (((-u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
        EuclideanSpace ℝ (Fin (n + 1)))) 0} =
      {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ ≥
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, coe_neg_sphere, hs_tail_neg, hs_head_neg,
      inner_neg_left]
    rw [neg_le_neg_iff]
  rwa [hset] at heq

/-- At a pole (`hsTail u = 0`), the two half-spaces are `univ` and `∅`, so every
measure satisfying the antipodal equation is zero. -/
private theorem hs_measure_univ_eq_zero_of_pole {n : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    (u : EuclideanSpace ℝ (Fin (n + 1))) (h1 : ‖u‖ = 1) (h0 : hsTail u = 0)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (heq : μ {x | ⟪hsTail u, x⟫_ℝ ≤ u 0} = μ {x | ⟪hsTail u, x⟫_ℝ ≥ u 0}) :
    μ Set.univ = 0 := by
  rcases hs_head_eq_one_or_neg_one_of_tail_eq_zero u h1 h0 with hhead | hhead
  · have hle : {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u, x⟫_ℝ ≤ u 0} = Set.univ := by
      rw [h0, hhead]
      exact Set.eq_univ_of_forall fun x => by
        simp only [Set.mem_ofPred_eq, inner_zero_left]
        norm_num
    have hge : {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u, x⟫_ℝ ≥ u 0} = ∅ := by
      rw [h0, hhead]
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Set.mem_ofPred_eq, inner_zero_left] at hx
      norm_num at hx
    rw [hle, hge, MeasureTheory.measure_empty] at heq
    exact heq
  · have hle : {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u, x⟫_ℝ ≤ u 0} = ∅ := by
      rw [h0, hhead]
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      simp only [Set.mem_ofPred_eq, inner_zero_left] at hx
      norm_num at hx
    have hge : {x : EuclideanSpace ℝ (Fin n) | ⟪hsTail u, x⟫_ℝ ≥ u 0} = Set.univ := by
      rw [h0, hhead]
      exact Set.eq_univ_of_forall fun x => by
        simp only [Set.mem_ofPred_eq, inner_zero_left]
        norm_num
    rw [hle, hge, MeasureTheory.measure_empty] at heq
    exact heq.symm

/-- Rescaling a nonzero normal to a unit vector preserves both half-spaces. -/
private theorem hs_norm_inv_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (hw : w ≠ 0) : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 :=
  norm_smul_inv_norm hw

private theorem hs_normalize_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (hw : w ≠ 0) (c : ℝ) :
    {x | ⟪(‖w‖⁻¹ : ℝ) • w, x⟫_ℝ ≤ ‖w‖⁻¹ * c} = {x | ⟪w, x⟫_ℝ ≤ c} := by
  have hpos : (0 : ℝ) < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  ext x
  simp only [Set.mem_ofPred_eq, real_inner_smul_left]
  exact mul_le_mul_iff_of_pos_left hpos

private theorem hs_normalize_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (hw : w ≠ 0) (c : ℝ) :
    {x | ⟪(‖w‖⁻¹ : ℝ) • w, x⟫_ℝ ≥ ‖w‖⁻¹ * c} = {x | ⟪w, x⟫_ℝ ≥ c} := by
  have hpos : (0 : ℝ) < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
  ext x
  simp only [Set.mem_ofPred_eq, real_inner_smul_left]
  exact mul_le_mul_iff_of_pos_left hpos

end MathlibExt.MeasureTheory.Geometry.HamSandwichWanted

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.HamSandwichWanted

/--
**Ham sandwich theorem.** Let $n \ge 1$ and let $\mu_1, \dots, \mu_n$ be finite Borel
measures on the Euclidean space $\mathbb{R}^n$, each absolutely continuous with respect to
Lebesgue measure. Then there exist a unit vector $v \in \mathbb{R}^n$ and a real number $t$
such that for every $i$, both closed half-spaces $\{x : \langle v, x \rangle \le t\}$ and
$\{x : \langle v, x \rangle \ge t\}$ have $\mu_i$-measure equal to $\mu_i(\mathbb{R}^n)/2$.

Proves `Wanted` entry `ham_sandwich`.

Source: A. H. Stone and J. W. Tukey, Duke Math. J. 9 (1942) 356–359 ham
sandwich theorem; J. Matoušek, Using the Borsuk–Ulam Theorem; Lean states measure-theoretic
Euclidean specialization with `μ i ≪ volume` making the bisecting hyperplane null.
-/
public theorem ham_sandwich
    {n : ℕ} (hn : 0 < n)
    [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
    [BorelSpace (EuclideanSpace ℝ (Fin n))]
    (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n)))
    (hfin : ∀ i, IsFiniteMeasure (μ i))
    (hac : ∀ i, μ i ≪ volume) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (t : ℝ), ‖v‖ = 1 ∧
      ∀ i : Fin n, μ i {x | ⟪v, x⟫_ℝ ≤ t} = μ i Set.univ / 2 ∧
        μ i {x | ⟪v, x⟫_ℝ ≥ t} = μ i Set.univ / 2 := by
  obtain ⟨u, hu⟩ := hs_exists_antipodal_eq μ hfin hac
  have hu1 : ‖(u : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp u.2
  by_cases hw : hsTail (u : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · have hzero : ∀ i, μ i Set.univ = 0 := fun i =>
      hs_measure_univ_eq_zero_of_pole _ hu1 hw _ (hu i)
    refine ⟨EuclideanSpace.single ⟨0, hn⟩ 1, 0, ?_, fun i => ?_⟩
    · have hsingle : EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) =
          PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℝ) := rfl
      rw [hsingle, PiLp.norm_single]
      exact norm_one
    · have hkill : ∀ s : Set (EuclideanSpace ℝ (Fin n)), μ i s = 0 := fun s =>
        le_antisymm ((MeasureTheory.measure_mono (Set.subset_univ s)).trans_eq (hzero i))
          zero_le
      simp [hkill]
  · refine ⟨(‖hsTail (u : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ : ℝ) •
        hsTail (u : EuclideanSpace ℝ (Fin (n + 1))),
      ‖hsTail (u : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ *
        (u : EuclideanSpace ℝ (Fin (n + 1))) 0, ?_, fun i => ?_⟩
    · exact hs_norm_inv_smul _ hw
    · have hnull : ∀ i, μ i {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ =
          (u : EuclideanSpace ℝ (Fin (n + 1))) 0} = 0 := fun i => by
        have hvol : volume {x | ⟪hsTail (u : EuclideanSpace ℝ (Fin (n + 1))), x⟫_ℝ =
            (u : EuclideanSpace ℝ (Fin (n + 1))) 0} = 0 :=
          hs_addHaar_setOf_inner_eq_null volume _ _ (Or.inl hw)
        exact (hac i) hvol
      have heq := hu i
      rw [hs_normalize_le _ hw _, hs_normalize_ge _ hw _]
      have hadd := hs_measure_le_add_measure_ge (μ i)
        (hsTail (u : EuclideanSpace ℝ (Fin (n + 1))))
        ((u : EuclideanSpace ℝ (Fin (n + 1))) 0)
      rw [hnull i, add_zero] at hadd
      obtain ⟨h1, h2⟩ := hs_eq_half_of_add_eq heq hadd
      exact ⟨h1, h2⟩

end MathlibExt.MeasureTheory.Geometry.HamSandwichWanted
