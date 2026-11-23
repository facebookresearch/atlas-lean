/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.LomonosovInvariantSubspaceWanted

/-- Eigenspace of a nonzero compact operator on an infinite-dimensional space is never `⊤`
(N1: a nonzero compact operator is not a scalar). -/
private theorem lomo_eigenspace_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (μ : ℂ) : Module.End.eigenspace (↑K : Module.End ℂ E) μ ≠ ⊤ := by
  intro htop
  have hKe : ∀ x : E, K x = μ • x := by
    intro x
    have hx : x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ := htop ▸ Submodule.mem_top
    simp only [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx
    exact hx
  by_cases hμ : μ = 0
  · subst hμ
    apply hK_ne
    ext x
    simp [hKe x]
  · have hfun : (μ⁻¹ • (K : E → E)) = id := by
      funext x
      simp [hKe x, smul_smul, inv_mul_cancel₀ hμ]
    have hcomp : IsCompactOperator (μ⁻¹ • (K : E → E)) := hK_compact.smul μ⁻¹
    rw [hfun] at hcomp
    exact hInf (FiniteDimensional.of_isCompactOperator_id hcomp)

/-- Eigenspaces are invariant under commuting operators. -/
private theorem lomo_eigenspace_mapsTo_of_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (μ : ℂ) (x : E) (hx : x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ) :
    T x ∈ Module.End.eigenspace (↑K : Module.End ℂ E) μ := by
  simp only [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx ⊢
  have hTK : ∀ z : E, K (T z) = T (K z) := by
    intro z
    have h := congrArg (· z) hComm
    simpa [ContinuousLinearMap.comp_apply] using h.symm
  rw [hTK, hx, map_smul]

/-- Case A: if `K` has an eigenvalue, its eigenspace is the wanted subspace. -/
private theorem lomo_exists_of_hasEigenvalue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  refine ⟨Module.End.eigenspace (↑K : Module.End ℂ E) μ, hμ, ?_, inferInstance, ?_⟩
  · exact lomo_eigenspace_ne_top hInf K hK_compact hK_ne μ
  · intro x hx
    exact lomo_eigenspace_mapsTo_of_commute K T hComm μ x hx

/-- A compact operator with no nonzero eigenvalue is quasinilpotent. -/
private theorem lomo_spectralRadius_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K)
    (hno : ∀ μ : ℂ, μ ≠ 0 → ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ) :
    spectralRadius ℂ K = 0 := by
  rw [spectralRadius_eq_of_unital]
  refine le_antisymm ?_ zero_le
  apply iSup₂_le
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · exact absurd ((hK_compact.hasEigenvalue_iff_mem_spectrum hk0).mpr hk) (hno k hk0)

/-- Powers of a quasinilpotent decay against any geometric constant. -/
private theorem lomo_tendsto_const_pow_mul_norm_pow
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : A) (ha : spectralRadius ℂ a = 0)
    (c : ℝ) (hc : 0 ≤ c) :
    Filter.Tendsto (fun m : ℕ => c ^ m * ‖a ^ m‖) Filter.atTop (nhds 0) := by
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  rw [ha] at hG
  set ε : ℝ := 1 / (2 * (c + 1)) with hε
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have hεpos : (0 : ℝ) < ε := by positivity
  have hlt : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hεpos
  have hev := hG.eventually (Iio_mem_nhds hlt)
  have hev2 : ∀ᶠ m : ℕ in Filter.atTop, ‖a ^ m‖ ^ (1 / (m : ℝ)) < ε := by
    filter_upwards [hev] with m hm
    exact (ENNReal.ofReal_lt_ofReal_iff hεpos).mp hm
  have hce : c * ε ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < 2 * (c + 1) := by positivity
    rw [hε, mul_one_div, div_le_iff₀ hpos]
    have h2 : (1 / 2 : ℝ) * (2 * (c + 1)) = c + 1 := by ring
    linarith
  have hbound : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * ‖a ^ m‖ ≤ (1 / 2) ^ m := by
    filter_upwards [hev2, Filter.eventually_gt_atTop 0] with m hm h1m
    have hm0 : m ≠ 0 := by omega
    have hpow : ‖a ^ m‖ = (‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m := by
      rw [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hm0]
    have hltm : (‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m < ε ^ m :=
      pow_lt_pow_left₀ hm (Real.rpow_nonneg (norm_nonneg _) _) hm0
    calc c ^ m * ‖a ^ m‖
        = c ^ m * ((‖a ^ m‖ ^ (1 / (m : ℝ))) ^ m) := by conv_lhs => rw [hpow]
      _ ≤ c ^ m * ε ^ m :=
          mul_le_mul_of_nonneg_left hltm.le (pow_nonneg hc _)
      _ = (c * ε) ^ m := by rw [mul_pow]
      _ ≤ (1 / 2) ^ m :=
          pow_le_pow_left₀ (mul_nonneg hc (le_of_lt hεpos)) hce _
  have hnonneg : ∀ᶠ m : ℕ in Filter.atTop, (0 : ℝ) ≤ c ^ m * ‖a ^ m‖ :=
    Filter.Eventually.of_forall
      fun m => mul_nonneg (pow_nonneg hc _) (norm_nonneg _)
  have hlim : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact squeeze_zero' hnonneg hbound hlim

/-- Centralizer subalgebra of `K` (N6 notation). -/
private def lomoCentralizer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) : Subalgebra ℂ (E →L[ℂ] E) :=
  Subalgebra.centralizer ℂ {K}

/-- Orbit submodule: operators of the centralizer applied to `y` (N6 notation). -/
private noncomputable def lomoOrb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y : E) : Submodule ℂ E :=
  Submodule.map (↑(ContinuousLinearMap.apply ℂ E y) : (E →L[ℂ] E) →ₗ[ℂ] E)
    (Subalgebra.toSubmodule (lomoCentralizer K))

/-- Closed orbit: topological closure of the orbit (N6 notation). -/
private noncomputable def lomoOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y : E) : Submodule ℂ E :=
  (lomoOrb K y).topologicalClosure

/-- Membership in the orbit submodule. -/
private theorem lomo_mem_orb
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (y z : E) :
    z ∈ lomoOrb K y ↔ ∃ A : E →L[ℂ] E, A ∈ lomoCentralizer K ∧ A y = z := by
  simp [lomoOrb, Submodule.mem_map, Subalgebra.mem_toSubmodule,
    ContinuousLinearMap.apply_apply]

/-- `T` lies in the centralizer of `K`. -/
private theorem lomo_T_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K T : E →L[ℂ] E) (hComm : T.comp K = K.comp T) :
    T ∈ lomoCentralizer K := by
  change T ∈ Subalgebra.centralizer ℂ {K}
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rw [ContinuousLinearMap.mul_def]
  exact hComm.symm

/-- Case B1: a proper nonzero closed orbit is the wanted subspace. -/
private theorem lomo_exists_of_orbit_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T)
    (y : E) (hy : y ≠ 0) (hne : lomoOrbit K y ≠ ⊤) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  have hTmem : T ∈ lomoCentralizer K := lomo_T_mem K T hComm
  have hmaps : Set.MapsTo T (lomoOrb K y : Set E) (lomoOrb K y : Set E) := by
    intro z hz
    have hz' : z ∈ lomoOrb K y := hz
    rw [lomo_mem_orb] at hz'
    obtain ⟨A, hA, rfl⟩ := hz'
    change T (A y) ∈ lomoOrb K y
    rw [lomo_mem_orb]
    refine ⟨T * A, mul_mem hTmem hA, ?_⟩
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  refine ⟨lomoOrbit K y, ?_, hne, Submodule.isClosed_topologicalClosure (lomoOrb K y), ?_⟩
  · rw [Submodule.ne_bot_iff]
    refine ⟨y, ?_, hy⟩
    apply Submodule.le_topologicalClosure
    rw [lomo_mem_orb]
    exact ⟨1, Subalgebra.one_mem _, by simp⟩
  · intro x hx
    have hx' : x ∈ closure (lomoOrb K y : Set E) := by
      have hmem : x ∈ ((lomoOrb K y).topologicalClosure : Set E) := hx
      rwa [Submodule.topologicalClosure_coe] at hmem
    have hTx : T x ∈ closure (lomoOrb K y : Set E) :=
      map_mem_closure T.continuous hx' hmaps
    have hmem2 : T x ∈ ((lomoOrb K y).topologicalClosure : Set E) := by
      rwa [Submodule.topologicalClosure_coe]
    exact hmem2

/-- Setup for Hilden's iteration: a ball mapped by `K` into a compact set away from 0. -/
private theorem lomo_exists_ball_setup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0) :
    ∃ (x0 : E) (r : ℝ), 0 < r ∧ ∃ (S : Set E), IsCompact S ∧ 0 ∉ S ∧
      (∀ x ∈ Metric.closedBall x0 r, K x ∈ S) ∧
      (∀ x ∈ Metric.closedBall x0 r, r ≤ ‖x‖) := by
  obtain ⟨x0, hx0⟩ : ∃ x0, K x0 ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hK_ne
    ext x
    simpa using h x
  have ha : (0 : ℝ) < ‖K x0‖ := norm_pos_iff.mpr hx0
  have hk : (0 : ℝ) < ‖K‖ := norm_pos_iff.mpr hK_ne
  have hKne : (‖K‖ : ℝ) ≠ 0 := ne_of_gt hk
  set r : ℝ := ‖K x0‖ / (2 * ‖K‖) with hr_def
  have h2k : (0 : ℝ) < 2 * ‖K‖ := mul_pos (by norm_num) hk
  have hnpos : (0 : ℝ) < r := by
    rw [hr_def]
    exact div_pos ha h2k
  have hKr : ‖K‖ * r = ‖K x0‖ / 2 := by
    rw [hr_def]
    field_simp
  have hmem : ∀ x ∈ Metric.closedBall x0 r, ‖x - x0‖ ≤ r := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    exact hx
  have hKx : ∀ x ∈ Metric.closedBall x0 r, ‖K x0‖ / 2 ≤ ‖K x‖ := by
    intro x hx
    have hle : ‖K (x - x0)‖ ≤ ‖K‖ * r :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hmem x hx) (le_of_lt hk))
    have heq : K (x - x0) = K x - K x0 := map_sub K x x0
    have htri : ‖K x0‖ - ‖K x‖ ≤ ‖K x - K x0‖ := by
      have h := norm_sub_norm_le (K x0) (K x)
      rwa [norm_sub_rev] at h
    rw [← heq] at htri
    linarith [hle, hKr]
  have hx0ge : 2 * r ≤ ‖x0‖ := by
    by_contra hlt
    have hlt' : ‖x0‖ < 2 * r := lt_of_not_ge hlt
    have h1 : ‖K‖ * ‖x0‖ < ‖K‖ * (2 * r) := mul_lt_mul_of_pos_left hlt' hk
    have h2 : ‖K‖ * (2 * r) = ‖K x0‖ := by linear_combination 2 * hKr
    have h3 : ‖K x0‖ ≤ ‖K‖ * ‖x0‖ := ContinuousLinearMap.le_opNorm _ _
    linarith
  have hxr : ∀ x ∈ Metric.closedBall x0 r, r ≤ ‖x‖ := by
    intro x hx
    have h1 : ‖x0‖ - ‖x‖ ≤ ‖x - x0‖ := by
      have h := norm_sub_norm_le x0 x
      rwa [norm_sub_rev] at h
    linarith [hmem x hx, hx0ge]
  obtain ⟨K', hK'comp, hsub⟩ :=
    hK_compact.image_closedBall_subset_compact (‖x0‖ + r)
  have hxball : ∀ x ∈ Metric.closedBall x0 r,
      x ∈ Metric.closedBall (0 : E) (‖x0‖ + r) := by
    intro x hx
    have htri : ‖x‖ ≤ ‖x0‖ + ‖x - x0‖ := by
      have h := norm_add_le x0 (x - x0)
      rwa [add_sub_cancel] at h
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    linarith [htri, hmem x hx]
  refine ⟨x0, r, hnpos, K' ∩ {y | ‖K x0‖ / 2 ≤ ‖y‖}, ?_, ?_, ?_, hxr⟩
  · exact hK'comp.inter_right (isClosed_le continuous_const continuous_norm)
  · intro h0
    obtain ⟨-, h⟩ := h0
    simp only [Set.mem_ofPred_eq, norm_zero] at h
    linarith
  · intro x hx
    constructor
    · apply hsub
      exact ⟨x, hxball x hx, rfl⟩
    · exact hKx x hx

/-- Finite subcover of a compact set by centralizer preimages of a ball. -/
private theorem lomo_exists_finite_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E)
    (htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤)
    (S : Set E) (hS : IsCompact S) (h0S : (0 : E) ∉ S)
    (x0 : E) (r : ℝ) (hr : 0 < r) :
    ∃ F : Finset (lomoCentralizer K),
      ∀ y ∈ S, ∃ A ∈ F, dist ((A : E →L[ℂ] E) y) x0 < r := by
  have hcover : S ⊆ ⋃ A : lomoCentralizer K, (A : E →L[ℂ] E) ⁻¹' Metric.ball x0 r := by
    intro y hy
    have hyne : y ≠ 0 := fun h => h0S (h ▸ hy)
    have htop : lomoOrbit K y = ⊤ := htrans y hyne
    have hdense : Dense (lomoOrb K y : Set E) := by
      rw [Submodule.dense_iff_topologicalClosure_eq_top]
      exact htop
    obtain ⟨z, hz, hdist⟩ := hdense.exists_dist_lt x0 hr
    have hz' : z ∈ lomoOrb K y := hz
    rw [lomo_mem_orb] at hz'
    obtain ⟨A, hA, rfl⟩ := hz'
    have hmem : y ∈ ((⟨A, hA⟩ : lomoCentralizer K) : E →L[ℂ] E) ⁻¹' Metric.ball x0 r := by
      change A y ∈ Metric.ball x0 r
      rw [Metric.mem_ball, dist_comm]
      exact hdist
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hmem⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun A : lomoCentralizer K => (A : E →L[ℂ] E) ⁻¹' Metric.ball x0 r)
    (fun A => IsOpen.preimage (A : E →L[ℂ] E).continuous Metric.isOpen_ball) hcover
  refine ⟨t, ?_⟩
  intro y hy
  obtain ⟨A, hAt, hAy⟩ := Set.mem_iUnion₂.mp (ht hy)
  have hmem : (A : E →L[ℂ] E) y ∈ Metric.ball x0 r := hAy
  refine ⟨A, hAt, ?_⟩
  rw [Metric.mem_ball] at hmem
  exact hmem

/-- Hilden's iteration: centralizer operators tracking `K^m x0` in the ball. -/
private theorem lomo_iterate_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E)
    (x0 : E) (r : ℝ) (hr : 0 ≤ r) (c : ℝ) (hc : 0 ≤ c)
    (F : Finset (lomoCentralizer K))
    (hFnorm : ∀ A ∈ F, ‖(A : E →L[ℂ] E)‖ ≤ c)
    (hcov : ∀ x ∈ Metric.closedBall x0 r,
      ∃ A ∈ F, ((A : E →L[ℂ] E) (K x)) ∈ Metric.closedBall x0 r) :
    ∀ m : ℕ, ∃ P : E →L[ℂ] E, P ∈ lomoCentralizer K ∧ ‖P‖ ≤ c ^ m ∧
      P ((K ^ m) x0) ∈ Metric.closedBall x0 r := by
  intro m
  induction m with
  | zero =>
    refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
    · rw [pow_zero, ContinuousLinearMap.one_def]
      exact ContinuousLinearMap.norm_id_le
    · have hmem : x0 ∈ Metric.closedBall x0 r :=
        Metric.mem_closedBall.mpr (by simpa using hr)
      have h1 : (1 : E →L[ℂ] E) ((K ^ 0) x0) = x0 := rfl
      rwa [h1]
  | succ m ih =>
    obtain ⟨P, hP, hPnorm, hPmem⟩ := ih
    obtain ⟨A, hAF, hAmem⟩ := hcov _ hPmem
    have hP' : P ∈ Subalgebra.centralizer ℂ {K} := hP
    rw [Subalgebra.mem_centralizer_iff] at hP'
    have hPc : K * P = P * K := hP' K (Set.mem_singleton K)
    have hKP : ∀ w : E, K (P w) = P (K w) := by
      intro w
      have h := congrArg (fun Q : E →L[ℂ] E => Q w) hPc
      simpa [ContinuousLinearMap.mul_def] using h
    have heq : ((A : E →L[ℂ] E) * P) ((K ^ (m + 1)) x0)
        = (A : E →L[ℂ] E) (K (P ((K ^ m) x0))) := by
      rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hKP]
    have h3 : c * c ^ m = c ^ (m + 1) := (pow_succ' c m).symm
    refine ⟨(A : E →L[ℂ] E) * P, mul_mem A.property hP, ?_, ?_⟩
    · rw [← h3]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (hFnorm A hAF) hPnorm (norm_nonneg _) hc)
    · rw [heq]
      exact hAmem

/-- Case B2: transitivity of the centralizer action is impossible. -/
private theorem lomo_false_of_transitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (hno : ∀ μ : ℂ, ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ)
    (htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤) :
    False := by
  have hspec : spectralRadius ℂ K = 0 :=
    lomo_spectralRadius_eq_zero K hK_compact (fun μ _ => hno μ)
  obtain ⟨x0, r, hr, S, hScomp, h0S, hKS, hxr⟩ :=
    lomo_exists_ball_setup K hK_compact hK_ne
  obtain ⟨F, hF⟩ := lomo_exists_finite_cover K htrans S hScomp h0S x0 r hr
  set c : ℝ := 1 + ∑ A ∈ F, ‖(A : E →L[ℂ] E)‖ with hc_def
  have hc : (0 : ℝ) ≤ c := by
    rw [hc_def]
    have hnn : (0 : ℝ) ≤ ∑ A ∈ F, ‖(A : E →L[ℂ] E)‖ :=
      Finset.sum_nonneg (fun A _ => norm_nonneg _)
    linarith
  have hFnorm : ∀ A ∈ F, ‖(A : E →L[ℂ] E)‖ ≤ c := by
    intro A hA
    rw [hc_def]
    exact (Finset.single_le_sum (fun B _ => norm_nonneg _) hA).trans
      (le_add_of_nonneg_left zero_le_one)
  have hcov : ∀ x ∈ Metric.closedBall x0 r,
      ∃ A ∈ F, ((A : E →L[ℂ] E) (K x)) ∈ Metric.closedBall x0 r := by
    intro x hx
    obtain ⟨A, hAF, hdist⟩ := hF (K x) (hKS x hx)
    exact ⟨A, hAF, Metric.ball_subset_closedBall (Metric.mem_ball.mpr hdist)⟩
  have hlim2 : Filter.Tendsto (fun m : ℕ => c ^ m * ‖K ^ m‖ * ‖x0‖) Filter.atTop
      (nhds 0) := by
    simpa using (lomo_tendsto_const_pow_mul_norm_pow K hspec c hc).mul_const ‖x0‖
  have hev : ∀ᶠ m : ℕ in Filter.atTop, c ^ m * ‖K ^ m‖ * ‖x0‖ < r :=
    hlim2.eventually (Iio_mem_nhds hr)
  have hlow : ∀ m : ℕ, r ≤ c ^ m * ‖K ^ m‖ * ‖x0‖ := by
    intro m
    obtain ⟨P, -, hPnorm, hPmem⟩ :=
      lomo_iterate_mem_closedBall K x0 r (le_of_lt hr) c hc F hFnorm hcov m
    have h1 : r ≤ ‖P ((K ^ m) x0)‖ := hxr _ hPmem
    have h2 : ‖P ((K ^ m) x0)‖ ≤ ‖P‖ * (‖K ^ m‖ * ‖x0‖) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    have h3 : ‖P‖ * (‖K ^ m‖ * ‖x0‖) ≤ c ^ m * ‖K ^ m‖ * ‖x0‖ := by
      have h31 : ‖P‖ * ‖K ^ m‖ ≤ c ^ m * ‖K ^ m‖ :=
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      calc ‖P‖ * (‖K ^ m‖ * ‖x0‖) = (‖P‖ * ‖K ^ m‖) * ‖x0‖ := by ring
        _ ≤ (c ^ m * ‖K ^ m‖) * ‖x0‖ := mul_le_mul_of_nonneg_right h31 (norm_nonneg _)
    linarith [h1, h2, h3]
  obtain ⟨m, hm⟩ := (hev.and (Filter.Eventually.of_forall hlow)).exists
  exact absurd hm.2 (not_le_of_gt hm.1)

/--
**Lomonosov's invariant subspace theorem.** Let $E$ be an infinite-dimensional complex Banach
space, let $K$ be a nonzero compact operator on $E$, and let $T$ be a bounded linear operator on
$E$ with $TK = KT$. Then there is a closed linear subspace $M$ of $E$ with $M \ne \{0\}$ and
$M \ne E$ that is invariant under $T$: $T x \in M$ for every $x \in M$.

Proves `Wanted` entry `lomonosov_invariantSubspace`.

Source: V. Lomonosov, Functional Anal. Appl. 7 (1973)
and J. Hilden elementary proof, Bull. Amer. Math. Soc.; Aronszajn-Smith 1954 precursor;
Radjavi-Rosenthal invariant subspace book, 1973; Lean states complex Banach infinite-dimensional
case `K≠0` compact commuting with `T` yields nontrivial closed invariant subspace.
-/
theorem lomonosov_invariantSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK_compact : IsCompactOperator K) (hK_ne : K ≠ 0)
    (T : E →L[ℂ] E) (hComm : T.comp K = K.comp T) :
    ∃ (M : Submodule ℂ E), M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set E) ∧ ∀ x ∈ M, T x ∈ M := by
  by_cases hA : ∃ μ, Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ
  · obtain ⟨μ, hμ⟩ := hA
    exact lomo_exists_of_hasEigenvalue hInf K hK_compact hK_ne T hComm μ hμ
  · have hno : ∀ μ : ℂ, ¬ Module.End.HasEigenvalue (↑K : Module.End ℂ E) μ :=
      fun μ h => hA ⟨μ, h⟩
    by_cases hB : ∃ y : E, y ≠ 0 ∧ lomoOrbit K y ≠ ⊤
    · obtain ⟨y, hy, hne⟩ := hB
      exact lomo_exists_of_orbit_ne_top K T hComm y hy hne
    · have htrans : ∀ y : E, y ≠ 0 → lomoOrbit K y = ⊤ := by
        intro y hy
        by_contra hne
        exact hB ⟨y, hy, hne⟩
      exact False.elim (lomo_false_of_transitive K hK_compact hK_ne hno htrans)

end MathlibExt.Analysis.FunctionalAnalysis.LomonosovInvariantSubspaceWanted
