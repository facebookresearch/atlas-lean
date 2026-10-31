/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.PartitionOfUnity

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.BartleGravesWanted

open Function Filter Topology

/-- Approximate homogeneous continuous selection: a surjective `T : E →L[ℝ] F` between real Banach
spaces admits a continuous, positively homogeneous `φ : F → E` with `‖φ y‖ ≤ K * ‖y‖` and residual
`‖y - T (φ y)‖ ≤ (1/2) * ‖y‖`. Built from the quantitative open mapping theorem and a partition of
unity subordinate to a cover of the unit sphere. This is the core step of Bartle–Graves. -/
private theorem approx_selection
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (hT : Function.Surjective T) :
    ∃ (φ : F → E) (K : ℝ), 0 ≤ K ∧ Continuous φ ∧
      (∀ (t : ℝ) (y : F), 0 ≤ t → φ (t • y) = t • φ y) ∧
      (∀ y, ‖φ y‖ ≤ K * ‖y‖) ∧
      (∀ y, ‖y - T (φ y)‖ ≤ (1/2) * ‖y‖) := by
  obtain ⟨C, hCpos, hpre⟩ := T.exists_preimage_norm_le hT
  choose xf hTxf hxfle using hpre
  set ι := {y : F // ‖y‖ = 1} with hι
  set U : ι → Set F := fun i => Metric.ball (i.1) (1/2) with hU
  have hUopen : ∀ i, IsOpen (U i) := fun i => Metric.isOpen_ball
  have hSclosed : IsClosed {y : F | ‖y‖ = 1} := isClosed_eq continuous_norm continuous_const
  have hcover : {y : F | ‖y‖ = 1} ⊆ ⋃ i, U i := by
    intro s hs
    refine Set.mem_iUnion.2 ⟨⟨s, hs⟩, ?_⟩
    simp [hU, Metric.mem_ball]
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate hSclosed U hUopen hcover
  set g0 : F → E := fun y => ∑ᶠ i, ρ i y • xf i.1 with hg0
  have hg0cont : Continuous g0 :=
    ρ.continuous_finsum_smul (g := fun i _ => xf i.1) (fun i x _ => continuousAt_const)
  have hfin : ∀ z : F, {i : ι | ρ i z ≠ 0}.Finite := by
    intro z
    have h := ρ.locallyFinite.point_finite z
    simpa [Function.support] using h
  have hg0eq : ∀ z, g0 z = ∑ i ∈ (hfin z).toFinset, ρ i z • xf i.1 := by
    intro z
    rw [hg0]
    apply finsum_eq_finsetSum_of_support_subset
    rw [Set.Finite.coe_toFinset]
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro h0
    exact hi (by rw [h0, zero_smul])
  have hxfleC : ∀ i : ι, ‖xf i.1‖ ≤ C := by
    intro i
    calc ‖xf i.1‖ ≤ C * ‖i.1‖ := hxfle i.1
      _ = C := by rw [i.2, mul_one]
  have hsum_finset : ∀ z, ∑ i ∈ (hfin z).toFinset, ρ i z = ∑ᶠ i, ρ i z := by
    intro z
    rw [finsum_eq_finsetSum_of_support_subset (fun i => ρ i z)]
    rw [Set.Finite.coe_toFinset]
    exact fun i hi => hi
  have hg0bound : ∀ z, ‖g0 z‖ ≤ C := by
    intro z
    rw [hg0eq z]
    calc ‖∑ i ∈ (hfin z).toFinset, ρ i z • xf i.1‖
        ≤ ∑ i ∈ (hfin z).toFinset, ‖ρ i z • xf i.1‖ := norm_sum_le _ _
      _ = ∑ i ∈ (hfin z).toFinset, ρ i z * ‖xf i.1‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i z)]
      _ ≤ ∑ i ∈ (hfin z).toFinset, ρ i z * C := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hxfleC i) (ρ.nonneg i z)
      _ = C * ∑ i ∈ (hfin z).toFinset, ρ i z := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
          rw [hsum_finset z]; exact ρ.sum_le_one z
      _ = C := mul_one C
  have hg0approx : ∀ s : F, ‖s‖ = 1 → ‖s - T (g0 s)‖ ≤ 1/2 := by
    intro s hs
    have hTg0 : T (g0 s) = ∑ i ∈ (hfin s).toFinset, ρ i s • (i.1) := by
      rw [hg0eq s, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hTxf i.1]
    have hsum_one : ∑ i ∈ (hfin s).toFinset, ρ i s = 1 := by
      rw [hsum_finset s]; exact ρ.sum_eq_one hs
    have hsexp : s = ∑ i ∈ (hfin s).toFinset, ρ i s • s := by
      rw [← Finset.sum_smul, hsum_one, one_smul]
    have hdiff : s - T (g0 s) = ∑ i ∈ (hfin s).toFinset, ρ i s • (s - i.1) := by
      have hsplit : ∑ i ∈ (hfin s).toFinset, ρ i s • (s - i.1)
          = (∑ i ∈ (hfin s).toFinset, ρ i s • s) - ∑ i ∈ (hfin s).toFinset, ρ i s • i.1 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_sub]
      rw [hsplit, ← hsexp, ← hTg0]
    rw [hdiff]
    calc ‖∑ i ∈ (hfin s).toFinset, ρ i s • (s - i.1)‖
        ≤ ∑ i ∈ (hfin s).toFinset, ‖ρ i s • (s - i.1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ (hfin s).toFinset, ρ i s * ‖s - i.1‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i s)]
      _ ≤ ∑ i ∈ (hfin s).toFinset, ρ i s * (1/2) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (ρ.nonneg i s)
          have hne : ρ i s ≠ 0 := (Set.Finite.mem_toFinset (hfin s)).1 hi
          have hmem : s ∈ tsupport (ρ i) := subset_tsupport _ (Function.mem_support.2 hne)
          have hball := hρ i hmem
          rw [hU] at hball
          rw [Metric.mem_ball, dist_eq_norm] at hball
          exact le_of_lt hball
      _ = (∑ i ∈ (hfin s).toFinset, ρ i s) * (1/2) := by rw [← Finset.sum_mul]
      _ = 1 * (1/2) := by rw [hsum_one]
      _ = 1/2 := one_mul _
  set φ : F → E := fun y => ‖y‖ • g0 (‖y‖⁻¹ • y) with hφdef
  have hφbound : ∀ y, ‖φ y‖ ≤ C * ‖y‖ := by
    intro y
    rw [hφdef]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y), mul_comm]
    exact mul_le_mul_of_nonneg_right (hg0bound _) (norm_nonneg y)
  have hφapprox : ∀ y, ‖y - T (φ y)‖ ≤ (1/2) * ‖y‖ := by
    intro y
    rcases eq_or_ne y 0 with hy | hy
    · subst hy; simp [hφdef]
    · simp only [hφdef]
      rw [map_smul]
      have hu : ‖(‖y‖⁻¹ • y)‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg y)),
          inv_mul_cancel₀ (norm_ne_zero_iff.2 hy)]
      have key : y - ‖y‖ • T (g0 (‖y‖⁻¹ • y))
          = ‖y‖ • ((‖y‖⁻¹ • y) - T (g0 (‖y‖⁻¹ • y))) := by
        rw [smul_sub]
        congr 1
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hy), one_smul]
      rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y),
        mul_comm ((1:ℝ)/2) ‖y‖]
      exact mul_le_mul_of_nonneg_left (hg0approx _ hu) (norm_nonneg y)
  have hφhom : ∀ (t : ℝ) (y : F), 0 ≤ t → φ (t • y) = t • φ y := by
    intro t y ht
    rcases eq_or_lt_of_le ht with h0 | ht'
    · rw [← h0]; simp [hφdef]
    · rcases eq_or_ne y 0 with hy | hy
      · rw [hy]; simp [hφdef]
      · simp only [hφdef]
        have hnt : ‖t • y‖ = t * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht']
        have hty : ‖t • y‖⁻¹ • (t • y) = ‖y‖⁻¹ • y := by
          rw [smul_smul, hnt]
          congr 1
          rw [mul_inv, mul_right_comm, inv_mul_cancel₀ (ne_of_gt ht'), one_mul]
        rw [hty, hnt, smul_smul]
  have hφcont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro y
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have hφ0 : φ 0 = 0 := by simp [hφdef]
      have htend : Filter.Tendsto φ (𝓝 (0:F)) (𝓝 0) := by
        apply squeeze_zero_norm hφbound
        have h1 : Filter.Tendsto (fun t : F => ‖t‖) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_norm.tendsto (0:F))
        simpa using h1.const_mul C
      rw [ContinuousAt, hφ0]
      exact htend
    · have h2 : ContinuousAt (fun z : F => ‖z‖⁻¹) y :=
        (continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hy)
      have h3 : ContinuousAt (fun z : F => ‖z‖⁻¹ • z) y := h2.smul continuous_id.continuousAt
      have h4 : ContinuousAt (fun z : F => g0 (‖z‖⁻¹ • z)) y := hg0cont.continuousAt.comp h3
      have h5 : ContinuousAt (fun z : F => ‖z‖ • g0 (‖z‖⁻¹ • z)) y :=
        continuous_norm.continuousAt.smul h4
      simpa only [hφdef] using h5
  exact ⟨φ, C, le_of_lt hCpos, hφcont, hφhom, hφbound, hφapprox⟩

/--
**Bartle–Graves theorem.** Let $E$ and $F$ be real Banach spaces and let $T : E \to F$ be a
surjective continuous linear map. Then there are a continuous map $g : F \to E$, in general not
linear, and a constant $C \ge 0$ such that $T(g(y)) = y$ for every $y \in F$, $g(0) = 0$,
$g(t y) = t \, g(y)$ for every real $t \ge 0$ and every $y \in F$, and $\|g(y)\| \le C \|y\|$
for every $y \in F$.

Proves `Wanted` entry `bartle_graves`.

Source:
R. G. Bartle and L. M. Graves, Mappings between function spaces,
Trans. Amer. Math. Soc. 72 (1952), 400–413, DOI 10.1090/S0002-9947-1952-0047910-X;
Michael selection theorem precursor; Lean states real Banach case with continuous right
inverse, positive homogeneity, and linear growth bound.
-/
theorem bartle_graves
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (hT : Function.Surjective T) :
    ∃ (g : F → E) (C : ℝ), 0 ≤ C ∧ Continuous g ∧ (∀ y, T (g y) = y) ∧ g 0 = 0 ∧
      (∀ (t : ℝ) (y : F), 0 ≤ t → g (t • y) = t • g y) ∧
      (∀ y, ‖g y‖ ≤ C * ‖y‖) := by
  obtain ⟨φ, K, hK, hφcont, hφhom, hφbound, hφapprox⟩ := approx_selection T hT
  set Sr : F → F := fun y => y - T (φ y) with hSrdef
  have hSrcont : Continuous Sr := by
    simp only [hSrdef]
    exact continuous_id.sub (T.continuous.comp hφcont)
  have hSrbound : ∀ y, ‖Sr y‖ ≤ (1/2) * ‖y‖ := hφapprox
  have hSrapp : ∀ z, T (φ z) = z - Sr z := by
    intro z; simp only [hSrdef]; abel
  have hSrhom : ∀ (t : ℝ) (y : F), 0 ≤ t → Sr (t • y) = t • Sr y := by
    intro t y ht
    simp only [hSrdef]
    rw [hφhom t y ht, map_smul, smul_sub]
  have hiterbound : ∀ (n : ℕ) (y : F), ‖Sr^[n] y‖ ≤ (1/2)^n * ‖y‖ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [Function.iterate_succ_apply']
      calc ‖Sr (Sr^[k] y)‖ ≤ (1/2) * ‖Sr^[k] y‖ := hSrbound _
        _ ≤ (1/2) * ((1/2)^k * ‖y‖) := mul_le_mul_of_nonneg_left (ih y) (by norm_num)
        _ = (1/2)^(k+1) * ‖y‖ := by rw [pow_succ]; ring
  have hiterhom : ∀ (n : ℕ) (t : ℝ) (y : F), 0 ≤ t → Sr^[n] (t • y) = t • Sr^[n] y := by
    intro n
    induction n with
    | zero => intro t y ht; simp
    | succ k ih =>
      intro t y ht
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hSrhom t y ht, ih t (Sr y) ht]
  have hitercont : ∀ n : ℕ, Continuous (Sr^[n]) := fun n => hSrcont.iterate n
  have hφ0 : φ 0 = 0 := by
    have h := hφbound 0
    rw [norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  have hterm_bound : ∀ (n : ℕ) (y : F), ‖φ (Sr^[n] y)‖ ≤ K * ‖y‖ * (1/2)^n := by
    intro n y
    calc ‖φ (Sr^[n] y)‖ ≤ K * ‖Sr^[n] y‖ := hφbound _
      _ ≤ K * ((1/2)^n * ‖y‖) := mul_le_mul_of_nonneg_left (hiterbound n y) hK
      _ = K * ‖y‖ * (1/2)^n := by ring
  have hsummable : ∀ y : F, Summable (fun n => φ (Sr^[n] y)) := by
    intro y
    exact Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_left (K * ‖y‖))
      (fun n => hterm_bound n y)
  set g : F → E := fun y => ∑' n, φ (Sr^[n] y) with hgdef
  have hg_hasSum : ∀ y, HasSum (fun n => φ (Sr^[n] y)) (g y) := fun y => (hsummable y).hasSum
  have hg0 : g 0 = 0 := by
    simp only [hgdef]
    have hz : ∀ n, φ (Sr^[n] (0:F)) = 0 := by
      intro n
      have h := hiterbound n (0:F)
      rw [norm_zero, mul_zero] at h
      rw [norm_le_zero_iff.1 h, hφ0]
    simp only [hz, tsum_zero]
  have hTg : ∀ y, T (g y) = y := by
    intro y
    have hmap : HasSum (fun n => T (φ (Sr^[n] y))) (T (g y)) := (hg_hasSum y).mapL T
    have hterm : ∀ n, T (φ (Sr^[n] y)) = Sr^[n] y - Sr^[n+1] y := by
      intro n
      rw [Function.iterate_succ_apply']
      exact hSrapp (Sr^[n] y)
    have hmapped : HasSum (fun n => Sr^[n] y - Sr^[n+1] y) (T (g y)) := by
      rwa [funext hterm] at hmap
    have htends := hmapped.tendsto_sum_nat
    have hpart : ∀ n, ∑ i ∈ Finset.range n, (Sr^[i] y - Sr^[i+1] y) = y - Sr^[n] y := by
      intro n
      have h := Finset.sum_range_sub' (fun i => Sr^[i] y) n
      simp only [Function.iterate_zero, id_eq] at h
      exact h
    rw [Filter.tendsto_congr hpart] at htends
    have hSrtends : Filter.Tendsto (fun n => Sr^[n] y) Filter.atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => hiterbound n y)
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const ‖y‖
      simpa using h
    have hy : Filter.Tendsto (fun n => y - Sr^[n] y) Filter.atTop (𝓝 y) := by
      have h := hSrtends.const_sub y
      simpa using h
    exact tendsto_nhds_unique htends hy
  have hghom : ∀ (t : ℝ) (y : F), 0 ≤ t → g (t • y) = t • g y := by
    intro t y ht
    have h1 : HasSum (fun n => φ (Sr^[n] (t • y))) (g (t • y)) := hg_hasSum (t • y)
    have h2 : (fun n => φ (Sr^[n] (t • y))) = (fun n => t • φ (Sr^[n] y)) := by
      funext n
      rw [hiterhom n t y ht, hφhom t (Sr^[n] y) ht]
    rw [h2] at h1
    have h3 : HasSum (fun n => t • φ (Sr^[n] y)) (t • g y) := (hg_hasSum y).const_smul t
    exact HasSum.unique h1 h3
  have hgbound : ∀ y, ‖g y‖ ≤ (2 * K) * ‖y‖ := by
    intro y
    have hnormsummable : Summable (fun n => ‖φ (Sr^[n] y)‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hterm_bound n y)
        ((summable_geometric_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_left
          (K * ‖y‖))
    calc ‖g y‖ = ‖∑' n, φ (Sr^[n] y)‖ := by simp only [hgdef]
      _ ≤ ∑' n, ‖φ (Sr^[n] y)‖ := norm_tsum_le_tsum_norm hnormsummable
      _ ≤ ∑' n, (K * ‖y‖ * (1/2)^n) :=
          Summable.tsum_le_tsum (fun n => hterm_bound n y) hnormsummable
            ((summable_geometric_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_left
              (K * ‖y‖))
      _ = K * ‖y‖ * ∑' n, (1/2:ℝ)^n := by rw [tsum_mul_left]
      _ = K * ‖y‖ * 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ = (2 * K) * ‖y‖ := by ring
  refine ⟨g, 2 * K, mul_nonneg (by norm_num) hK, ?_, hTg, hg0, hghom, hgbound⟩
  rw [continuous_iff_continuousAt]
  intro y
  have hcontOn : ContinuousOn g (Metric.ball (0:F) (‖y‖ + 1)) := by
    simp only [hgdef]
    refine continuousOn_tsum (fun n => (hφcont.comp (hitercont n)).continuousOn)
      ((summable_geometric_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_left
        (K * (‖y‖ + 1))) ?_
    intro n z hz
    have hznorm : ‖z‖ ≤ ‖y‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
      exact le_of_lt hz
    calc ‖φ (Sr^[n] z)‖ ≤ K * ‖z‖ * (1/2)^n := hterm_bound n z
      _ ≤ K * (‖y‖ + 1) * (1/2)^n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hznorm hK) (by positivity)
  have hymem : y ∈ Metric.ball (0:F) (‖y‖ + 1) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  exact hcontOn.continuousAt (Metric.isOpen_ball.mem_nhds hymem)

end MathlibExt.Analysis.FunctionalAnalysis.BartleGravesWanted
