/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.Ray

@[expose] public section

namespace MathlibExt.Geometry.Manifold.HairyBallWanted

open Metric

open scoped Pointwise

/-- Step 1a: smooth approximation of `f ∘ ν` on `{‖x‖ > 1/2}`.
Produce smooth `g` with `‖g x - f(νx)‖ < m/2` there. -/
private theorem smooth_approx_g
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : sphere (0 : E) 1 → E) (hf : Continuous f)
    (m : ℝ) (hm : 0 < m) :
    ∃ g : E → E, ContDiff ℝ 1 g ∧
      ∀ x : E, ∀ _h : (1 / 2 : ℝ) < ‖x‖,
        ∃ hmem : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1,
          dist (g x) (f ⟨‖x‖⁻¹ • x, hmem⟩) < m / 2 := by
  have mem_sphere_of_half_lt : ∀ x : E, (1 / 2 : ℝ) < ‖x‖ →
      ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h0
      simp [h0] at hx
      linarith
    have hpos : (0 : ℝ) < ‖x‖ := by linarith
    have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    rw [Metric.mem_sphere, dist_zero_right]
    exact hnorm
  set t : E → Set E := fun x =>
    {y | ∀ h : (1 / 2 : ℝ) < ‖x‖,
      dist y (f ⟨‖x‖⁻¹ • x, mem_sphere_of_half_lt x h⟩) < m / 2} with ht
  have ht_conv : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : (1 / 2 : ℝ) < ‖x‖
    · have heq : t x =
          Metric.ball (f ⟨‖x‖⁻¹ • x, mem_sphere_of_half_lt x hx⟩) (m / 2) := by
        ext y
        simp only [ht, Set.mem_ofPred_eq, Metric.mem_ball]
        constructor
        · intro hy
          exact hy hx
        · intro hy h
          have hsub : (⟨‖x‖⁻¹ • x, mem_sphere_of_half_lt x h⟩ :
              sphere (0 : E) 1)
              = ⟨‖x‖⁻¹ • x, mem_sphere_of_half_lt x hx⟩ := by
            congr 1
          rw [hsub]
          exact hy
      rw [heq]
      exact convex_ball _ _
    · have heq : t x = Set.univ := by
        ext y
        simp only [ht, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro h
        exact absurd h hx
      rw [heq]
      exact convex_univ
  have hloc : ∀ x₀ : E, ∃ c : E, ∀ᶠ y in nhds x₀, c ∈ t y := by
    intro x₀
    have hunif := CompactSpace.uniformContinuous_of_continuous hf
    rw [Metric.uniformContinuous_iff] at hunif
    obtain ⟨δ, hδpos, hδ⟩ := hunif (m / 2) (by linarith)
    -- Normalization map E → E, continuous at nonzero points
    have hνcont : ∀ z : E, z ≠ 0 →
        ContinuousAt (fun y : E => ‖y‖⁻¹ • y) z := by
      intro z hz
      apply ContinuousAt.smul
      · apply ContinuousAt.inv₀
        · exact continuous_norm.continuousAt
        · simp [hz]
      · exact continuous_id.continuousAt
    by_cases hx0 : (1 / 2 : ℝ) < ‖x₀‖
    · -- Case ‖x₀‖ > 1/2: constant f(νx₀)
      have hx0ne : x₀ ≠ 0 := by
        intro h0
        simp [h0] at hx0
        linarith
      have hmem0 := mem_sphere_of_half_lt x₀ hx0
      refine ⟨f ⟨‖x₀‖⁻¹ • x₀, hmem0⟩, ?_⟩
      have hUmem : {y : E | (1 / 2 : ℝ) < ‖y‖} ∈ nhds x₀ :=
        IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) hx0
      have hνev : ∀ᶠ y in nhds x₀,
          dist (‖y‖⁻¹ • y) (‖x₀‖⁻¹ • x₀) < δ := by
        have h := (hνcont x₀ hx0ne).eventually
          (Metric.ball_mem_nhds _ hδpos)
        simp only [dist_comm] at h ⊢
        exact h
      filter_upwards [hUmem, hνev] with y hyU hyν
      simp only [ht, Set.mem_ofPred_eq]
      intro h
      -- y ∈ sphere via hyU, x₀ via hx0; uniform continuity gives bound
      have hmem_y := mem_sphere_of_half_lt y hyU
      have hdist_sphere : dist (⟨‖y‖⁻¹ • y, hmem_y⟩ : sphere (0 : E) 1)
          ⟨‖x₀‖⁻¹ • x₀, hmem0⟩ < δ := by
        simpa [Subtype.dist_eq] using hyν
      have hclose := hδ hdist_sphere
      -- Center with h equals center with hyU by proof irrelevance
      have hsub : (⟨‖y‖⁻¹ • y, mem_sphere_of_half_lt y h⟩ : sphere (0 : E) 1)
          = ⟨‖y‖⁻¹ • y, hmem_y⟩ := by
        congr 1
      rw [hsub]
      simpa [dist_comm] using hclose
    · by_cases hx0lt : ‖x₀‖ < 1 / 2
      · -- Case ‖x₀‖ < 1/2: any constant, eventually univ
        refine ⟨0, ?_⟩
        have hUmem : {y : E | ‖y‖ < 1 / 2} ∈ nhds x₀ :=
          IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hx0lt
        filter_upwards [hUmem] with y hyU
        simp only [ht, Set.mem_ofPred_eq]
        intro h
        exact absurd (lt_trans hyU h) (lt_irrefl _)
      · -- Case ‖x₀‖ = 1/2: constant f(νx₀) via x₀ ≠ 0
        have hx0eq : ‖x₀‖ = 1 / 2 :=
          le_antisymm (le_of_not_gt hx0) (le_of_not_gt hx0lt)
        have hx0ne : x₀ ≠ 0 :=
          norm_ne_zero_iff.mp (by rw [hx0eq]; norm_num)
        have hmem_ne : ∀ y : E, y ≠ 0 → ‖y‖⁻¹ • y ∈ sphere (0 : E) 1 := by
          intro y hy
          have hnorm : ‖‖y‖⁻¹ • y‖ = 1 := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0 : ℝ) < ‖y‖⁻¹)]
            field_simp
          rw [Metric.mem_sphere, dist_zero_right]
          exact hnorm
        have hmem0 := hmem_ne x₀ hx0ne
        refine ⟨f ⟨‖x₀‖⁻¹ • x₀, hmem0⟩, ?_⟩
        have hνev : ∀ᶠ y in nhds x₀,
            dist (‖y‖⁻¹ • y) (‖x₀‖⁻¹ • x₀) < δ := by
          have h := (hνcont x₀ hx0ne).eventually
            (Metric.ball_mem_nhds _ hδpos)
          simp only [dist_comm] at h ⊢
          exact h
        filter_upwards [hνev] with y hyν
        simp only [ht, Set.mem_ofPred_eq]
        intro h
        have hyne : y ≠ 0 := by
          intro h0
          simp [h0] at h
          linarith
        have hmem_y := hmem_ne y hyne
        have hdist_sphere : dist (⟨‖y‖⁻¹ • y, hmem_y⟩ : sphere (0 : E) 1)
            ⟨‖x₀‖⁻¹ • x₀, hmem0⟩ < δ := by
          simpa [Subtype.dist_eq] using hyν
        have hclose := hδ hdist_sphere
        have hsub : (⟨‖y‖⁻¹ • y, mem_sphere_of_half_lt y h⟩ : sphere (0 : E) 1)
            = ⟨‖y‖⁻¹ • y, hmem_y⟩ := by
          congr 1
        rw [hsub]
        simpa [dist_comm] using hclose
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
    (modelWithCornersSelf ℝ E) (n := 1) ht_conv hloc
  refine ⟨fun x => g x, ?_, ?_⟩
  · exact g.contMDiff.contDiff
  · intro x hx
    have hmem := mem_sphere_of_half_lt x hx
    have hgt := hg x hx
    exact ⟨hmem, hgt⟩

/-- Step 1: smoothing a nowhere-zero tangent field to a smooth tangent field.
Given continuous `f` on the sphere, orthogonal to the radius and never zero,
produce smooth `h : E → E` tangent on the sphere and never zero there. -/
private theorem smooth_tangent_approx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : sphere (0 : E) 1 → E) (hf : Continuous f)
    (hortho : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (f x) (x : E) = 0)
    (hne : ∀ x : sphere (0 : E) 1, f x ≠ 0) :
    ∃ h : E → E, ContDiff ℝ 1 h ∧
      (∀ x : sphere (0 : E) 1, @inner ℝ E _ (h (x : E)) (x : E) = 0) ∧
      (∀ x : sphere (0 : E) 1, h (x : E) ≠ 0) := by
  by_cases hsphere : Nonempty (sphere (0 : E) 1)
  · -- Minimum m > 0 of ‖f‖ on the compact sphere
    obtain ⟨x0, _, hx0min⟩ := isCompact_univ.exists_isMinOn
      (Set.nonempty_iff_univ_nonempty.mp hsphere) (hf.norm.continuousOn)
    set m : ℝ := ‖f x0‖ with hm
    have hmpos : 0 < m := norm_pos_iff.mpr (hne x0)
    have hmbound : ∀ x : sphere (0 : E) 1, m ≤ ‖f x‖ := by
      intro x
      exact hx0min (Set.mem_univ x)
    obtain ⟨g, hg_smooth, hg_approx⟩ := smooth_approx_g f hf m hmpos
    -- h(x) = g(x) - ⟪g(x), x⟫ • x, smooth
    set h : E → E := fun x => g x - @inner ℝ E _ (g x) x • x with hh
    have hg_inner : ContDiff ℝ 1 (fun x => @inner ℝ E _ (g x) x) :=
      ContDiff.inner ℝ hg_smooth contDiff_id
    have h_smooth : ContDiff ℝ 1 h := by
      simp only [hh]
      exact hg_smooth.sub (hg_inner.smul contDiff_id)
    refine ⟨h, h_smooth, ?_, ?_⟩
    · -- Tangent on sphere: ⟪h(x), x⟫ = 0 using ⟪x, x⟫ = 1
      intro x
      have hx_norm : ‖(x : E)‖ = 1 := by
        have hmem : (x : E) ∈ sphere (0 : E) 1 := x.property
        rw [Metric.mem_sphere, dist_zero_right] at hmem
        exact hmem
      have hxx : @inner ℝ E _ (x : E) (x : E) = 1 := by
        rw [real_inner_self_eq_norm_sq, hx_norm, one_pow]
      simp only [hh]
      rw [inner_sub_left, real_inner_smul_left, hxx, mul_one, sub_self]
    · -- Nonzero on sphere via ‖h - f‖ < m ≤ ‖f‖
      intro x
      have hx_norm : ‖(x : E)‖ = 1 := by
        have hmem : (x : E) ∈ sphere (0 : E) 1 := x.property
        rw [Metric.mem_sphere, dist_zero_right] at hmem
        exact hmem
      have hxx : @inner ℝ E _ (x : E) (x : E) = 1 := by
        rw [real_inner_self_eq_norm_sq, hx_norm, one_pow]
      have hortho_x := hortho x
      -- g approximates f on sphere (‖x‖ = 1 > 1/2, νx = x)
      have hx_half : (1 / 2 : ℝ) < ‖(x : E)‖ := by rw [hx_norm]; norm_num
      obtain ⟨hmem, hdist⟩ := hg_approx (x : E) hx_half
      have hνeq : (⟨‖(x : E)‖⁻¹ • (x : E), hmem⟩ : sphere (0 : E) 1) = x := by
        apply Subtype.ext
        change ‖(x : E)‖⁻¹ • (x : E) = (x : E)
        rw [hx_norm, inv_one, one_smul]
      rw [hνeq] at hdist
      have hgnorm : ‖g (x : E) - f x‖ < m / 2 := by
        rw [← dist_eq_norm]
        simpa [dist_comm] using hdist
      -- h - f = (g - f) - ⟪g - f, x⟫ • x
      have hdecomp : h (x : E) - f x
          = (g (x : E) - f x) - @inner ℝ E _ (g (x : E) - f x) (x : E) • (x : E) := by
        simp only [hh]
        have : @inner ℝ E _ (g (x : E)) (x : E)
            = @inner ℝ E _ (g (x : E) - f x) (x : E) := by
          rw [inner_sub_left, hortho_x, sub_zero]
        rw [this]
        abel
      have hCS : |@inner ℝ E _ (g (x : E) - f x) (x : E)|
          ≤ ‖g (x : E) - f x‖ * ‖(x : E)‖ :=
        abs_real_inner_le_norm _ _
      rw [hx_norm, mul_one] at hCS
      have hinner_norm : ‖@inner ℝ E _ (g (x : E) - f x) (x : E) • (x : E)‖
          ≤ ‖g (x : E) - f x‖ := by
        calc ‖@inner ℝ E _ (g (x : E) - f x) (x : E) • (x : E)‖
            = |@inner ℝ E _ (g (x : E) - f x) (x : E)| * ‖(x : E)‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ = |@inner ℝ E _ (g (x : E) - f x) (x : E)| := by
              rw [hx_norm, mul_one]
          _ ≤ ‖g (x : E) - f x‖ := hCS
      have hnorm_le : ‖h (x : E) - f x‖ < m := by
        calc ‖h (x : E) - f x‖
            = ‖(g (x : E) - f x)
              - @inner ℝ E _ (g (x : E) - f x) (x : E) • (x : E)‖ := by rw [hdecomp]
          _ ≤ ‖g (x : E) - f x‖
              + ‖@inner ℝ E _ (g (x : E) - f x) (x : E) • (x : E)‖ := norm_sub_le _ _
          _ ≤ ‖g (x : E) - f x‖ + ‖g (x : E) - f x‖ := by
              linarith [hinner_norm]
          _ < m := by linarith
      have hmle : m ≤ ‖f x‖ := hmbound x
      intro h0
      have : ‖h (x : E) - f x‖ = ‖f x‖ := by
        rw [h0, zero_sub, norm_neg]
      linarith
  · -- Empty sphere: any h works vacuously
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · exact contDiff_const
    · intro x
      exact absurd ⟨x⟩ hsphere
    · intro x
      exact absurd ⟨x⟩ hsphere

/-- Step 2: homogeneous unit tangent field `V` from smooth `h`.
`V 0 = 0`, `V x = (‖x‖ / ‖h(νx)‖) • h(νx)` for `x ≠ 0`. -/
private noncomputable def VHair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (x : E) : E :=
  letI := Classical.propDecidable (x = 0)
  if x = 0 then 0 else (‖x‖ / ‖h (‖x‖⁻¹ • x)‖) • h (‖x‖⁻¹ • x)

/-- Step 2a: `⟪V x, x⟫ = 0` and `‖V x‖ = ‖x‖`, given `h` tangent and nonzero
on the sphere. -/
private theorem VHair_inner_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E)
    (htan : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (h (x : E)) (x : E) = 0)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (x : E) :
    @inner ℝ E _ (VHair h x) x = 0 ∧ ‖VHair h x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, VHair]
  · -- x ≠ 0: νx ∈ sphere, h(νx) ≠ 0; use opaque ν to avoid rewriting inside h
    set ν : E := ‖x‖⁻¹ • x with hνdef
    have hxnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hνmem : ν ∈ sphere (0 : E) 1 := by
      have hnorm : ‖ν‖ = 1 := by
        have hpos : (0 : ℝ) < ‖x‖⁻¹ :=
          inv_pos.mpr (norm_pos_iff.mpr hx)
        simp only [hνdef, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        field_simp
      rw [Metric.mem_sphere, dist_zero_right]
      exact hnorm
    have hhne : h ν ≠ 0 := hne ⟨ν, hνmem⟩
    have hhnorm_pos : 0 < ‖h ν‖ := norm_pos_iff.mpr hhne
    have hVeq : VHair h x = (‖x‖ / ‖h ν‖) • h ν := by
      simp [VHair, hx, hνdef]
    have hx_eq : x = ‖x‖ • ν := by
      simp only [hνdef, smul_smul, mul_inv_cancel₀ hxnorm_ne, one_smul]
    have htan_ν : @inner ℝ E _ (h ν) ν = 0 := htan ⟨ν, hνmem⟩
    constructor
    · rw [hVeq, real_inner_smul_left, hx_eq, real_inner_smul_right, htan_ν,
        mul_zero, mul_zero]
    · rw [hVeq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
      field_simp

/-- Step 2c: `V` is `C¹` at every `x ≠ 0`. -/
private theorem VHair_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (x : E) (hx : x ≠ 0) : ContDiffAt ℝ 1 (VHair h) x := by
  -- ν(y) = ‖y‖⁻¹ • y is C¹ at x (x ≠ 0)
  have hν : ContDiffAt ℝ 1 (fun y : E => ‖y‖⁻¹ • y) x := by
    apply ContDiffAt.smul
    · apply ContDiffAt.inv
      · exact contDiffAt_norm ℝ hx
      · exact norm_ne_zero_iff.mpr hx
    · exact contDiffAt_id
  -- h ∘ ν is C¹ at x
  have hhν : ContDiffAt ℝ 1 (fun y : E => h (‖y‖⁻¹ • y)) x :=
    hh.comp_contDiffAt x hν
  -- νx ∈ sphere, so h(νx) ≠ 0
  have hνmem : ‖x‖⁻¹ • x ∈ sphere (0 : E) 1 := by
    have hnorm : ‖‖x‖⁻¹ • x‖ = 1 := by
      have hpos : (0 : ℝ) < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      field_simp
    rw [Metric.mem_sphere, dist_zero_right]
    exact hnorm
  have hhne : h (‖x‖⁻¹ • x) ≠ 0 := hne ⟨‖x‖⁻¹ • x, hνmem⟩
  -- ‖h ∘ ν‖ is C¹ and nonzero at x
  have hnorm_hν : ContDiffAt ℝ 1 (fun y : E => ‖h (‖y‖⁻¹ • y)‖) x :=
    ContDiffAt.norm ℝ hhν hhne
  have hnorm_ne : (fun y : E => ‖h (‖y‖⁻¹ • y)‖) x ≠ 0 :=
    norm_ne_zero_iff.mpr hhne
  -- ‖·‖ is C¹ at x
  have hnorm_x : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  -- Scalar ‖y‖ / ‖h(νy)‖ is C¹ at x
  have hscalar : ContDiffAt ℝ 1
      (fun y : E => ‖y‖ / ‖h (‖y‖⁻¹ • y)‖) x :=
    hnorm_x.div hnorm_hν hnorm_ne
  -- Formula (without if) is C¹ at x via smul
  have hformula : ContDiffAt ℝ 1
      (fun y : E => (‖y‖ / ‖h (‖y‖⁻¹ • y)‖) • h (‖y‖⁻¹ • y)) x :=
    hscalar.smul hhν
  -- VHair agrees with formula near x (on {y ≠ 0} ∈ 𝓝 x)
  have heq : (fun y : E => (‖y‖ / ‖h (‖y‖⁻¹ • y)‖) • h (‖y‖⁻¹ • y))
      =ᶠ[nhds x] (VHair h) := by
    have hU : {y : E | y ≠ 0} ∈ nhds x :=
      IsOpen.mem_nhds isOpen_ne hx
    filter_upwards [hU] with y hy
    simp [VHair, hy]
  exact hformula.congr_of_eventuallyEq heq.symm

/-- Step 2c': `V` is `C¹` on the open set `{0}ᶜ`. -/
private theorem VHair_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0) :
    ContDiffOn ℝ 1 (VHair h) {0}ᶜ := by
  rw [isOpen_compl_singleton.contDiffOn_iff]
  intro a ha
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha
  exact VHair_contDiffAt h hh hne a ha

/-- Step 2b: `V (r • x) = r • V x` for `r ≥ 0`. -/
private theorem VHair_homog
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (r : ℝ) (hr : 0 ≤ r) (x : E) :
    VHair h (r • x) = r • VHair h x := by
  by_cases hr0 : r = 0
  · simp [hr0, VHair]
  · by_cases hx : x = 0
    · simp [hx, VHair]
    · -- r ≠ 0, x ≠ 0, r ≥ 0 so r > 0; ν(r•x) = νx, ‖r•x‖ = r‖x‖
      have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have hrx_ne : r • x ≠ 0 := smul_ne_zero hrne hx
      have hnorm_rx : ‖r • x‖ = r * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
      have hνeq : ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
        rw [hnorm_rx, smul_smul]
        have hscal : (r * ‖x‖)⁻¹ * r = ‖x‖⁻¹ := by
          field_simp
        rw [hscal]
      have hVrx : VHair h (r • x)
          = (‖r • x‖ / ‖h (‖r • x‖⁻¹ • (r • x))‖) • h (‖r • x‖⁻¹ • (r • x)) := by
        simp [VHair, hrx_ne]
      have hVx : VHair h x = (‖x‖ / ‖h (‖x‖⁻¹ • x)‖) • h (‖x‖⁻¹ • x) := by
        simp [VHair, hx]
      rw [hVrx, hνeq, hnorm_rx]
      -- (r‖x‖/‖hν‖)•hν = r•((‖x‖/‖hν‖)•hν)
      rw [hVx]
      field_simp
      rw [smul_smul]
      congr 1
      ring

/-- Step 2d-i: `fderiv V` is constant along open rays: `D V (r • x) = D V x`. -/
private theorem VHair_fderiv_homog
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (x : E) (hx : x ≠ 0) (r : ℝ) (hr : 0 < r) :
    fderiv ℝ (VHair h) (r • x) = fderiv ℝ (VHair h) x := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrx : r • x ≠ 0 := smul_ne_zero hr0 hx
  have hdx : DifferentiableAt ℝ (VHair h) x :=
    (VHair_contDiffAt h hh hne x hx).differentiableAt (by simp)
  have hdrx : DifferentiableAt ℝ (VHair h) (r • x) :=
    (VHair_contDiffAt h hh hne _ hrx).differentiableAt (by simp)
  have heq : (fun y : E => VHair h (r • y)) = (fun y : E => r • VHair h y) := by
    funext y
    exact VHair_homog h r hr.le y
  have hfun_eq : (⇑(r • ContinuousLinearMap.id ℝ E) : E → E)
      = (fun y : E => r • y) := by
    funext y
    simp
  have hlin : HasFDerivAt (fun y : E => r • y)
      (r • ContinuousLinearMap.id ℝ E) x := by
    rw [← hfun_eq]
    exact (r • ContinuousLinearMap.id ℝ E).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E => VHair h (r • y))
      ((fderiv ℝ (VHair h) (r • x)).comp (r • ContinuousLinearMap.id ℝ E)) x :=
    hdrx.hasFDerivAt.comp x hlin
  have hsmul : HasFDerivAt (fun y : E => r • VHair h y)
      (r • fderiv ℝ (VHair h) x) x :=
    hdx.hasFDerivAt.const_smul r
  rw [heq] at hcomp
  have hunique := hcomp.unique hsmul
  have hcancel : r • fderiv ℝ (VHair h) (r • x) = r • fderiv ℝ (VHair h) x := by
    have hrewrite : (fderiv ℝ (VHair h) (r • x)).comp
        (r • ContinuousLinearMap.id ℝ E)
        = r • fderiv ℝ (VHair h) (r • x) := by
      ext v
      simp
    rw [hrewrite] at hunique
    exact hunique
  exact (smul_right_injective (E →L[ℝ] E) hr0) hcancel

/-- Step 2d-ii: `‖fderiv V‖` is bounded on the unit sphere. -/
private theorem VHair_fderiv_bound_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0) :
    ∃ C : NNReal, ∀ z ∈ sphere (0 : E) 1, ‖fderiv ℝ (VHair h) z‖₊ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ (VHair h)) {0}ᶜ :=
    (VHair_contDiffOn h hh hne).continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton le_rfl
  have hsub : sphere (0 : E) 1 ⊆ {0}ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hnorm : ‖z‖ = 1 := by
      have hmem := hz
      rw [Metric.mem_sphere, dist_zero_right] at hmem
      exact hmem
    intro h0
    rw [h0, norm_zero] at hnorm
    norm_num at hnorm
  have hcontS : ContinuousOn (fderiv ℝ (VHair h)) (sphere (0 : E) 1) :=
    hcont.mono hsub
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
    hcontS
  refine ⟨⟨max C 0, by positivity⟩, ?_⟩
  intro z hz
  have hle : ‖fderiv ℝ (VHair h) z‖ ≤ max C 0 := le_trans (hC z hz) (le_max_left _ _)
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm]
  exact hle

/-- Step 2d: `V` is globally Lipschitz. Off the segment through `0` use the
mean value inequality on the segment; if `0` lies on the segment, use
`‖V x‖ = ‖x‖` and `‖x - y‖ = ‖x‖ + ‖y‖`. -/
private theorem VHair_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (htan : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (h (x : E)) (x : E) = 0)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0) :
    ∃ L : NNReal, LipschitzWith L (VHair h) := by
  obtain ⟨C, hC⟩ := VHair_fderiv_bound_sphere h hh hne
  refine ⟨max C 1, ?_⟩
  -- Every nonzero point reduces to the sphere along its ray
  have hred : ∀ z : E, z ≠ 0 → ‖fderiv ℝ (VHair h) z‖₊ ≤ max C 1 := by
    intro z hz
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hne_r : ‖z‖ ≠ 0 := ne_of_gt hpos
    have hnorm_u : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      field_simp
    have humem : (‖z‖⁻¹ • z) ∈ sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hnorm_u
    have hu_ne : (‖z‖⁻¹ • z) ≠ 0 := by
      intro hu0
      rw [hu0, norm_zero] at hnorm_u
      norm_num at hnorm_u
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [← mul_smul, mul_inv_cancel₀ hne_r, one_smul]
    have hder : fderiv ℝ (VHair h) z
        = fderiv ℝ (VHair h) (‖z‖⁻¹ • z) := by
      conv_lhs => rw [← hzu]
      exact VHair_fderiv_homog h hh hne _ hu_ne ‖z‖ hpos
    rw [hder]
    exact le_trans (hC _ humem) (le_max_left _ _)
  have hVnorm : ∀ z : E, ‖VHair h z‖ = ‖z‖ :=
    fun z => (VHair_inner_norm h htan hne z).2
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  by_cases h0 : (0 : E) ∈ segment ℝ x y
  · -- `0` on the segment: `‖x - y‖ = ‖x‖ + ‖y‖`
    have hray : SameRay ℝ ((0 : E) - x) (y - 0) :=
      mem_segment_iff_sameRay.mp h0
    have hnorm_eq : ‖x - y‖ = ‖x‖ + ‖y‖ := by
      have hadd := SameRay.norm_add hray
      have h1 : (0 - x) + (y - 0) = y - x := by abel
      have h2 : ‖(0 : E) - x‖ = ‖x‖ := by rw [zero_sub, norm_neg]
      have h3 : ‖y - (0 : E)‖ = ‖y‖ := by rw [sub_zero]
      rw [h1, h2, h3, norm_sub_rev] at hadd
      exact hadd
    have hle : dist (VHair h x) (VHair h y) ≤ dist x y := by
      have hstep : ‖VHair h x - VHair h y‖ ≤ ‖x - y‖ := by
        calc ‖VHair h x - VHair h y‖
            ≤ ‖VHair h x‖ + ‖VHair h y‖ := norm_sub_le _ _
          _ = ‖x‖ + ‖y‖ := by rw [hVnorm x, hVnorm y]
          _ = ‖x - y‖ := hnorm_eq.symm
      simpa only [dist_eq_norm] using hstep
    have h1L : (1 : ℝ) ≤ ((max C 1 : NNReal) : ℝ) := by
      rw [← NNReal.coe_one, NNReal.coe_le_coe]
      exact le_max_right _ _
    calc dist (VHair h x) (VHair h y) ≤ dist x y := hle
      _ = 1 * dist x y := (one_mul _).symm
      _ ≤ ((max C 1 : NNReal) : ℝ) * dist x y := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          exact h1L
  · -- `0` off the segment: mean value inequality on the segment
    have hne_seg : ∀ z ∈ segment ℝ x y, z ≠ 0 := by
      intro z hz hzz
      subst hzz
      exact h0 hz
    have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ (VHair h) z := by
      intro z hz
      exact (VHair_contDiffAt h hh hne z (hne_seg z hz)).differentiableAt
        (by simp)
    have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ (VHair h) z‖₊ ≤ max C 1 := by
      intro z hz
      exact hred z (hne_seg z hz)
    have hlip := (convex_segment x y).lipschitzOnWith_of_nnnorm_fderiv_le
      hdiff hbound
    exact hlip.dist_le_mul _ (left_mem_segment ℝ x y) _ (right_mem_segment ℝ x y)

/-- Step 3a: Pythagoras for `F_t(x) = x + t • V(x)`. -/
private theorem VHair_Ft_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E) (horth : ∀ x, @inner ℝ E _ (V x) x = 0)
    (hnorm : ∀ x, ‖V x‖ = ‖x‖) (t : ℝ) (x : E) :
    ‖x + t • V x‖ ^ 2 = (1 + t ^ 2) * ‖x‖ ^ 2 := by
  have h1 : @inner ℝ E _ x (t • V x) = 0 := by
    rw [real_inner_smul_right, real_inner_comm (V x) x, horth x, mul_zero]
  have h2 : ‖t • V x‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm x]
  rw [norm_add_sq_real, h1, h2]
  ring

/-- Step 3b: `F_t(x) = x + t • V(x)` is bijective when `|t| * L < 1`. -/
private theorem VHair_Ft_bijective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (V : E → E) (L : NNReal) (hlip : LipschitzWith L V)
    (t : ℝ) (ht : |t| * (L : ℝ) < 1) :
    Function.Bijective (fun x => x + t • V x) := by
  set K : NNReal := ‖t‖₊ * L with hK
  have hKcoe : ((K : NNReal) : ℝ) = |t| * (L : ℝ) := by
    rw [hK, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  have hKlt : K < 1 := NNReal.coe_lt_coe.mp (by rwa [hKcoe, NNReal.coe_one])
  have hV : ∀ a b : E, ‖V a - V b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a b
    have h := hlip.dist_le_mul a b
    simpa only [dist_eq_norm] using h
  constructor
  · -- Injectivity from the estimate `‖a - b‖ ≤ (|t| * L) * ‖a - b‖`
    intro a b hab
    simp only at hab
    have heq : a - b = -(t • (V a - V b)) := by
      have h2 : t • V a - t • V b = t • (V a - V b) := (smul_sub _ _ _).symm
      calc a - b
          = (a + t • V a) - (b + t • V b) - (t • V a - t • V b) := by abel
        _ = 0 - (t • V a - t • V b) := by rw [hab, sub_self]
        _ = -(t • (V a - V b)) := by rw [zero_sub, h2]
    have hnorm : ‖a - b‖ ≤ (|t| * (L : ℝ)) * ‖a - b‖ := by
      calc ‖a - b‖ = ‖t • (V a - V b)‖ := by rw [heq, norm_neg]
        _ = |t| * ‖V a - V b‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |t| * ((L : ℝ) * ‖a - b‖) :=
          mul_le_mul_of_nonneg_left (hV a b) (abs_nonneg t)
        _ = (|t| * (L : ℝ)) * ‖a - b‖ := by ring
    have h0 : ‖a - b‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have hlt : (|t| * (L : ℝ)) * ‖a - b‖ < 1 * ‖a - b‖ :=
        mul_lt_mul_of_pos_right ht hpos
      rw [one_mul] at hlt
      linarith
    have hab0 : a - b = 0 := norm_eq_zero.mp h0
    exact sub_eq_zero.mp hab0
  · -- Surjectivity by Banach: `x ↦ y - t • V x` is a contraction
    intro y
    have hGlip : LipschitzWith K (fun x => y - t • V x) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro a b
      have heq : (y - t • V a) - (y - t • V b) = t • (V b - V a) := by
        rw [smul_sub]
        abel
      have hstep : ‖(y - t • V a) - (y - t • V b)‖ ≤ ((K : NNReal) : ℝ) * ‖a - b‖ := by
        calc ‖(y - t • V a) - (y - t • V b)‖
            = ‖t • (V b - V a)‖ := by rw [heq]
          _ = |t| * ‖V b - V a‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = |t| * ‖V a - V b‖ := by rw [norm_sub_rev]
          _ ≤ |t| * ((L : ℝ) * ‖a - b‖) := by gcongr; exact hV a b
          _ = ((K : NNReal) : ℝ) * ‖a - b‖ := by rw [hKcoe]; ring
      simpa only [dist_eq_norm] using hstep
    have hG : ContractingWith K (fun x => y - t • V x) := ⟨hKlt, hGlip⟩
    set pt : E := hG.fixedPoint (fun x => y - t • V x) with hpt
    have hfp_eq : y - t • V pt = pt := hG.fixedPoint_isFixedPt
    have hgoal : pt + t • V pt = y := by
      have hab2 : (pt + t • V pt) - y = -((y - t • V pt) - pt) := by abel
      have hsub : (pt + t • V pt) - y = 0 := by
        rw [hab2, hfp_eq, sub_self, neg_zero]
      exact sub_eq_zero.mp hsub
    exact ⟨pt, hgoal⟩

/-- Step 3c: `F_t` sends the closed annulus `A = {1 ≤ ‖x‖ ≤ 2}` onto
`√(1 + t²) • A`. -/
private theorem VHair_Ft_image_annulus
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E) (horth : ∀ x, @inner ℝ E _ (V x) x = 0)
    (hnorm : ∀ x, ‖V x‖ = ‖x‖) (t : ℝ)
    (hbij : Function.Bijective (fun x => x + t • V x)) :
    (fun x => x + t • V x) '' {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
      = Real.sqrt (1 + t ^ 2) • {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
  have hs_pos : 0 < Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs_ne : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt hs_pos
  have hnormF : ∀ x : E,
      ‖x + t • V x‖ = Real.sqrt (1 + t ^ 2) * ‖x‖ := by
    intro x
    have hsq := VHair_Ft_norm_sq V horth hnorm t x
    have hnn : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
    calc ‖x + t • V x‖ = Real.sqrt (‖x + t • V x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((1 + t ^ 2) * ‖x‖ ^ 2) := by rw [hsq]
      _ = Real.sqrt (1 + t ^ 2) * ‖x‖ := by
          rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg _)]
  apply Set.Subset.antisymm
  · -- Forward: `F x = s • (s⁻¹ • F x)` with `s⁻¹ • F x ∈ A`
    rintro y ⟨x, hx, rfl⟩
    simp only [Set.mem_ofPred_eq] at hx
    have hback : Real.sqrt (1 + t ^ 2)
        • (Real.sqrt (1 + t ^ 2))⁻¹ • (x + t • V x) = x + t • V x := by
      rw [← mul_smul, mul_inv_cancel₀ hs_ne, one_smul]
    have hmem : (Real.sqrt (1 + t ^ 2))⁻¹ • (x + t • V x)
        ∈ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
      have hnorm_eq : ‖(Real.sqrt (1 + t ^ 2))⁻¹ • (x + t • V x)‖ = ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs_pos), hnormF x]
        field_simp
      simp only [Set.mem_ofPred_eq]
      rw [hnorm_eq]
      exact hx
    exact ⟨(Real.sqrt (1 + t ^ 2))⁻¹ • (x + t • V x), hmem, hback⟩
  · -- Backward: preimage has the same norm up to `s`, hence lies in `A`
    rintro y ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq] at hz
    obtain ⟨x, hx⟩ := hbij.2 (Real.sqrt (1 + t ^ 2) • z)
    have hxmem : x ∈ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
      have hFx : ‖x + t • V x‖
          = Real.sqrt (1 + t ^ 2) * ‖z‖ := by
        have h1 : x + t • V x = Real.sqrt (1 + t ^ 2) • z := hx
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_pos.le]
      have hcancel : ‖x‖ = ‖z‖ := by
        have h2 := hnormF x
        rw [hFx] at h2
        exact mul_left_cancel₀ hs_ne h2.symm
      simp only [Set.mem_ofPred_eq]
      rw [hcancel]
      exact hz
    exact ⟨x, hxmem, hx⟩

/-- Step 3d-i: the closed annulus is closed. -/
private theorem VHair_annulus_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsClosed {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
  have h1 : IsClosed {x : E | 1 ≤ ‖x‖} :=
    isClosed_Ici.preimage continuous_norm
  have h2 : IsClosed {x : E | ‖x‖ ≤ 2} :=
    isClosed_Iic.preimage continuous_norm
  have heq : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
      = {x : E | 1 ≤ ‖x‖} ∩ {x : E | ‖x‖ ≤ 2} := rfl
  rw [heq]
  exact h1.inter h2

/-- Step 3d-ii: the annulus has positive finite Haar measure. -/
private theorem VHair_annulus_meas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (x : E) (hx : x ≠ 0) :
    μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≠ 0
      ∧ μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≠ ⊤ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu1 : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    field_simp
  set x₀ : E := (3 / 2 : ℝ) • (‖x‖⁻¹ • x) with hx0
  have hnorm_x0 : ‖x₀‖ = 3 / 2 := by
    rw [hx0, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num), hu1, mul_one]
  have hball : Metric.ball x₀ (1 / 2) ⊆ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hlow : 1 ≤ ‖y‖ := by
      have h := norm_sub_norm_le x₀ y
      rw [norm_sub_rev] at h
      rw [hnorm_x0] at h
      linarith
    have hhigh : ‖y‖ ≤ 2 := by
      calc ‖y‖ = ‖x₀ + (y - x₀)‖ := by congr 1; abel
        _ ≤ ‖x₀‖ + ‖y - x₀‖ := norm_add_le _ _
        _ ≤ 2 := by rw [hnorm_x0]; linarith
    simp only [Set.mem_ofPred_eq]
    exact ⟨hlow, hhigh⟩
  have hpos : 0 < μ (Metric.ball x₀ (1 / 2)) :=
    isOpen_ball.measure_pos μ ⟨x₀, Metric.mem_ball_self (by norm_num)⟩
  have hfin : μ (Metric.closedBall (0 : E) 2) < ⊤ :=
    (isCompact_closedBall (0 : E) 2).measure_lt_top
  have hsub : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ⊆ Metric.closedBall (0 : E) 2 := by
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.2
  constructor
  · exact ne_of_gt (lt_of_lt_of_le hpos (MeasureTheory.measure_mono hball))
  · exact ne_of_lt (lt_of_le_of_lt
      (MeasureTheory.measure_mono hsub) hfin)

/-- Step 3d-iii: Haar measure of the `F_t`-image of the annulus. -/
private theorem VHair_Ft_image_meas
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (V : E → E) (horth : ∀ x, @inner ℝ E _ (V x) x = 0)
    (hnorm : ∀ x, ‖V x‖ = ‖x‖) (t : ℝ)
    (hbij : Function.Bijective (fun x => x + t • V x)) :
    μ ((fun x => x + t • V x) '' {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
      = ENNReal.ofReal (Real.sqrt (1 + t ^ 2) ^ Module.finrank ℝ E)
        * μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
  rw [VHair_Ft_image_annulus V horth hnorm t hbij,
    MeasureTheory.Measure.addHaar_smul_of_nonneg μ (Real.sqrt_nonneg _) _]

/-- Step 4 helper: the annulus sits inside `closedBall 0 2`. -/
private theorem VHair_annulus_subset_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ⊆ Metric.closedBall (0 : E) 2 := by
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hy.2

/-- Step 4a-i: derivative of `F_t` at a nonzero point. -/
private theorem VHair_Ft_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (t : ℝ) (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y => y + t • VHair h y)
      (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x) x := by
  have hV : HasFDerivAt (VHair h) (fderiv ℝ (VHair h) x) x :=
    ((VHair_contDiffAt h hh hne x hx).differentiableAt (by simp)).hasFDerivAt
  have hfun : (⇑(ContinuousLinearMap.id ℝ E) : E → E) = (fun y : E => y) := by
    funext y
    simp
  have hid : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) x := by
    rw [← hfun]
    exact (ContinuousLinearMap.id ℝ E).hasFDerivAt
  have hsmul : HasFDerivAt (fun y => t • VHair h y)
      (t • fderiv ℝ (VHair h) x) x :=
    hV.const_smul t
  exact hid.add hsmul

/-- Step 4a-ii: change of variables on the annulus. -/
private theorem VHair_Ft_lintegral_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (t : ℝ) (hbij : Function.Bijective (fun x => x + t • VHair h x)) :
    (∫⁻ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      ENNReal.ofReal
        |(ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det| ∂μ)
    = μ ((fun x => x + t • VHair h x)
      '' {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}) := by
  refine MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image μ
    VHair_annulus_closed.measurableSet ?_ hbij.1.injOn
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  have hne_x : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    norm_num at hx
  exact (VHair_Ft_hasFDerivAt h hh hne t x hne_x).hasFDerivWithinAt

/-- Step 4 helper: Lipschitz bound controls `‖fderiv V‖` everywhere. -/
private theorem VHair_fderiv_bound_L
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E) (L : NNReal) (hlip : LipschitzWith L V) (z : E) :
    ‖fderiv ℝ V z‖ ≤ (L : ℝ) :=
  norm_fderiv_le_of_lipschitz ℝ hlip

/-- Step 4c: the volume integral is a polynomial in `t`, by Lagrange
interpolation at `finrank + 1` nodes. -/
private theorem VHair_volume_poly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (hpoly : ∀ M : E →L[ℝ] E, ∃ P : Polynomial ℝ,
      P.natDegree ≤ Module.finrank ℝ E ∧ ∀ t : ℝ,
        P.eval t = (ContinuousLinearMap.id ℝ E + t • M).det) :
    ∃ P : Polynomial ℝ, ∀ t : ℝ,
      P.eval t = ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det ∂μ := by
  set n : ℕ := Module.finrank ℝ E with hn
  set nodes : Finset ℕ := Finset.range (n + 1) with hnodes
  set v : ℕ → ℝ := fun j => (j : ℝ) with hv
  have hcard : nodes.card = n + 1 := Finset.card_range _
  have hvs : Set.InjOn v ↑nodes := by
    intro a _ b _ hab
    exact Nat.cast_injective hab
  have hsubA : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ⊆ {0}ᶜ := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hz ⊢
    intro h0
    rw [h0, norm_zero] at hz
    norm_num at hz
  have hAcompact : IsCompact {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset
      VHair_annulus_closed VHair_annulus_subset_ball
  have hDV : ContinuousOn (fun x => fderiv ℝ (VHair h) x)
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    ((VHair_contDiffOn h hh hne).continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton le_rfl).mono hsubA
  have hInt : ∀ j : ℕ, MeasureTheory.IntegrableOn
      (fun x => (ContinuousLinearMap.id ℝ E
        + v j • fderiv ℝ (VHair h) x).det)
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} μ := by
    intro j
    apply ContinuousOn.integrableOn_compact hAcompact
    exact ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add (hDV.const_smul (v j)))
  -- Pointwise identity: interpolation recovers each fiber polynomial
  have hsum : ∀ (x : E) (t : ℝ),
      (∑ j ∈ nodes,
        (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det
          * (Lagrange.basis nodes v j).eval t)
      = (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det := by
    intro x t
    obtain ⟨q, hqdeg, hqeval⟩ := hpoly (fderiv ℝ (VHair h) x)
    have hqlt : q.degree < (((n + 1 : ℕ)) : WithBot ℕ) := by
      have h1 : q.degree ≤ ((q.natDegree : ℕ) : WithBot ℕ) :=
        Polynomial.degree_le_natDegree
      have h3 : q.natDegree < n + 1 :=
        lt_of_le_of_lt hqdeg (Nat.lt_succ_self _)
      calc q.degree ≤ ((q.natDegree : ℕ) : WithBot ℕ) := h1
        _ < (((n + 1 : ℕ)) : WithBot ℕ) := by exact_mod_cast h3
    have hq : q = Lagrange.interpolate nodes v
        (fun j => (ContinuousLinearMap.id ℝ E
          + v j • fderiv ℝ (VHair h) x).det) := by
      refine Lagrange.eq_interpolate_of_eval_eq _ hvs ?_ ?_
      · rw [hcard]
        exact hqlt
      · intro j _
        exact hqeval (v j)
    have h1 : (Lagrange.interpolate nodes v
        (fun j => (ContinuousLinearMap.id ℝ E
          + v j • fderiv ℝ (VHair h) x).det)).eval t
        = (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det := by
      rw [← hq]
      exact hqeval t
    rw [Lagrange.interpolate_apply] at h1
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C] using h1
  refine ⟨Lagrange.interpolate nodes v
    (fun j => ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det ∂μ), ?_⟩
  intro t
  have hPs : (Lagrange.interpolate nodes v
      (fun j => ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det ∂μ)).eval t
      = ∑ j ∈ nodes,
        (∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
          (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det ∂μ)
        * (Lagrange.basis nodes v j).eval t := by
    rw [Lagrange.interpolate_apply]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C]
  calc (Lagrange.interpolate nodes v
        (fun j => ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
          (ContinuousLinearMap.id ℝ E
            + v j • fderiv ℝ (VHair h) x).det ∂μ)).eval t
        = ∑ j ∈ nodes,
          (∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
            (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det ∂μ)
          * (Lagrange.basis nodes v j).eval t := hPs
      _ = ∑ j ∈ nodes,
          ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
            (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det
              * (Lagrange.basis nodes v j).eval t ∂μ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [MeasureTheory.integral_mul_const]
      _ = ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
          ∑ j ∈ nodes,
            (ContinuousLinearMap.id ℝ E + v j • fderiv ℝ (VHair h) x).det
              * (Lagrange.basis nodes v j).eval t ∂μ :=
          (MeasureTheory.integral_finsetSum _
            (fun j _ => (hInt j).mul_const _)).symm
      _ = ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
          (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards
            [MeasureTheory.ae_restrict_mem
              VHair_annulus_closed.measurableSet] with x _
          exact hsum x t

/-- Linear-algebra fact (Step 4b): if `‖M‖ < 1` then `det(id + M) > 0`,
by continuity and the intermediate value theorem along `s ↦ id + s • M`. -/
private theorem det_pos_of_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : E →L[ℝ] E) (hM : ‖M‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + M).det := by
  have hcont : Continuous
      (fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • M).det) :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (ContinuousLinearMap.id ℝ E + s • M).det ≠ 0 := by
    intro s hs
    rw [Set.mem_Icc] at hs
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hker
    obtain ⟨x, hx_mem, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hker
    rw [LinearMap.mem_ker] at hx_mem
    have hco : x + s • M x = 0 := by simpa using hx_mem
    have hx_eq : x = -(s • M x) := by
      calc x = x + s • M x - s • M x := by abel
        _ = 0 - s • M x := by rw [hco]
        _ = -(s • M x) := by abel
    have hnorm : ‖x‖ ≤ s * ‖M‖ * ‖x‖ := by
      calc ‖x‖ = ‖s • M x‖ := by conv_lhs => rw [hx_eq]; rw [norm_neg]
        _ ≤ ‖s‖ * ‖M x‖ := norm_smul_le _ _
        _ ≤ ‖s‖ * (‖M‖ * ‖x‖) := by gcongr; exact M.le_opNorm _
        _ = s * ‖M‖ * ‖x‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hs.1]; ring
    have hsM : s * ‖M‖ < 1 := by
      calc s * ‖M‖ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖M‖ := one_mul _
        _ < 1 := hM
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    have hle : 1 ≤ s * ‖M‖ := by
      have h1 : (1 : ℝ) * ‖x‖ ≤ (s * ‖M‖) * ‖x‖ := by simpa using hnorm
      exact le_of_mul_le_mul_right h1 hxpos
    linarith
  have h0 : (fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • M).det) 0 = 1 := by
    unfold ContinuousLinearMap.det
    simp
  by_contra hneg
  have hle : (ContinuousLinearMap.id ℝ E + M).det ≤ 0 := le_of_not_gt hneg
  have h1eq : (fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • M).det) 1
      = (ContinuousLinearMap.id ℝ E + M).det := by simp
  have hmem : (0 : ℝ) ∈ Set.Icc
      ((fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • M).det) 1)
      ((fun s : ℝ => (ContinuousLinearMap.id ℝ E + s • M).det) 0) := by
    rw [h1eq, h0]
    exact Set.mem_Icc.mpr ⟨hle, zero_le_one⟩
  have hIVT := intermediate_value_Icc' (a := (0 : ℝ)) (b := 1) (by norm_num)
    (hcont.continuousOn)
  obtain ⟨s, hs_mem, hs_eq⟩ := hIVT hmem
  exact hne s hs_mem hs_eq

/-- Linear-algebra fact (Step 4c): for a fixed linear map `M`,
`t ↦ det(id + t • M)` is given by a real polynomial of degree at most `finrank`. -/
private theorem det_poly_ex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : E →L[ℝ] E) : ∃ P : Polynomial ℝ,
      P.natDegree ≤ Module.finrank ℝ E ∧
      ∀ t : ℝ, P.eval t = (ContinuousLinearMap.id ℝ E + t • M).det := by
  refine ⟨Matrix.det ((Polynomial.X : Polynomial ℝ) •
      (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
        (M : E →ₗ[ℝ] E)).map Polynomial.C
      + (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).map
        Polynomial.C), ?_, ?_⟩
  · calc (Matrix.det ((Polynomial.X : Polynomial ℝ) •
        (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
          (M : E →ₗ[ℝ] E)).map Polynomial.C
        + (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).map
          Polynomial.C)).natDegree
        ≤ Fintype.card (Fin (Module.finrank ℝ E)) :=
          Polynomial.natDegree_det_X_add_C_le _ _
      _ = Module.finrank ℝ E := Fintype.card_fin _
  · intro t
    set A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
        (M : E →ₗ[ℝ] E) with hA
    have heval : (Matrix.det ((Polynomial.X : Polynomial ℝ) • A.map Polynomial.C
        + (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).map
          Polynomial.C)).eval t
        = Matrix.det (t • A + 1) := by
      rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, smul_eq_mul]
    have hmat : LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
        ((ContinuousLinearMap.id ℝ E + t • M : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = t • A + 1 := by
      rw [hA]
      simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.coe_id,
        ContinuousLinearMap.toLinearMap_smul, map_add,
        LinearMap.toMatrix_id_eq_basis_toMatrix, Module.Basis.toMatrix_self, map_smul]
      rw [add_comm]
    have hdet := LinearMap.det_toMatrix (Module.finBasis ℝ E)
      ((ContinuousLinearMap.id ℝ E + t • M : E →L[ℝ] E) : E →ₗ[ℝ] E)
    have hgoal : (Matrix.det ((Polynomial.X : Polynomial ℝ) • A.map Polynomial.C
        + (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).map
          Polynomial.C)).eval t
        = (ContinuousLinearMap.id ℝ E + t • M).det := by
      rw [heval, ← hmat]
      exact hdet
    exact hgoal

/-- Polynomial parity fact (Step 5): no real polynomial agrees with
`c * √(1+t²)^n` on an interval when `n` is odd and `c > 0`. -/
private theorem poly_sqrt_odd_contradiction
    {P : Polynomial ℝ} {c : ℝ} {n : ℕ} {δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hodd : Odd n)
    (hP : ∀ t : ℝ, |t| < δ → P.eval t = c * (Real.sqrt (1 + t ^ 2)) ^ n) :
    False := by
  have hsq : ∀ t : ℝ, |t| < δ → (P ^ 2).eval t
      = (Polynomial.C (c ^ 2) * (1 + Polynomial.X ^ 2) ^ n).eval t := by
    intro t ht
    have hPt := hP t ht
    simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, hPt]
    have hnn : (0 : ℝ) ≤ 1 + t ^ 2 := by positivity
    have hsqrt2 : (Real.sqrt (1 + t ^ 2)) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hnn
    calc (c * Real.sqrt (1 + t ^ 2) ^ n) ^ 2
        = c ^ 2 * ((Real.sqrt (1 + t ^ 2)) ^ 2) ^ n := by ring
      _ = c ^ 2 * (1 + t ^ 2) ^ n := by rw [hsqrt2]
  have hIoo_sub : Set.Ioo (-δ) δ
      ⊆ {x | (P ^ 2).eval x
        = (Polynomial.C (c ^ 2) * (1 + Polynomial.X ^ 2) ^ n).eval x} := by
    intro t ht
    exact hsq t (abs_lt.mpr (Set.mem_Ioo.mp ht))
  have hinf : {x | (P ^ 2).eval x
      = (Polynomial.C (c ^ 2) * (1 + Polynomial.X ^ 2) ^ n).eval x}.Infinite := by
    apply Set.Infinite.mono hIoo_sub
    exact Set.Ioo_infinite (by linarith)
  have hpoly_eq : P ^ 2 = Polynomial.C (c ^ 2) * (1 + Polynomial.X ^ 2) ^ n :=
    Polynomial.eq_of_infinite_eval_eq _ _ hinf
  have hP0 : P ≠ 0 := by
    intro h0
    have h00 := hP 0 (by simp [hδ])
    rw [h0] at h00
    simp at h00
    linarith
  have hQ0 : P.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hP0
  have hmap_eq : (P.map (algebraMap ℝ ℂ)) ^ 2
      = Polynomial.C ((algebraMap ℝ ℂ) (c ^ 2)) * (1 + Polynomial.X ^ 2) ^ n := by
    have h := congrArg (Polynomial.map (algebraMap ℝ ℂ)) hpoly_eq
    simpa using h
  have h2 : (Polynomial.C Complex.I : Polynomial ℂ) ^ 2 = -1 := by
    rw [← map_pow]
    simp
  have hfactor : (1 + Polynomial.X ^ 2 : Polynomial ℂ)
      = (Polynomial.X - Polynomial.C Complex.I)
        * (Polynomial.X + Polynomial.C Complex.I) := by
    calc (1 + Polynomial.X ^ 2 : Polynomial ℂ)
        = Polynomial.X ^ 2 - (Polynomial.C Complex.I) ^ 2 := by rw [h2]; ring
      _ = (Polynomial.X - Polynomial.C Complex.I)
          * (Polynomial.X + Polynomial.C Complex.I) := by ring
  have hIne : Complex.I ≠ -Complex.I := by
    intro h
    have him := congrArg Complex.im h
    simp [Complex.I_im] at him
    linarith
  have hc2 : (algebraMap ℝ ℂ) (c ^ 2) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt hc))
  have hC0 : (Polynomial.C ((algebraMap ℝ ℂ) (c ^ 2)) : Polynomial ℂ) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hc2
  have hX1 : (Polynomial.X - Polynomial.C Complex.I : Polynomial ℂ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hplus : (Polynomial.X + Polynomial.C Complex.I : Polynomial ℂ)
      = Polynomial.X - Polynomial.C (-Complex.I) := by simp [sub_neg_eq_add]
  have hX2 : (Polynomial.X - Polynomial.C (-Complex.I) : Polynomial ℂ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  have hLHS : Polynomial.rootMultiplicity Complex.I ((P.map (algebraMap ℝ ℂ)) ^ 2)
      = 2 * Polynomial.rootMultiplicity Complex.I (P.map (algebraMap ℝ ℂ)) := by
    have hQQ : (P.map (algebraMap ℝ ℂ)) * (P.map (algebraMap ℝ ℂ)) ≠ 0 :=
      mul_ne_zero hQ0 hQ0
    have h1 : ((P.map (algebraMap ℝ ℂ)) ^ 2
        = (P.map (algebraMap ℝ ℂ)) * (P.map (algebraMap ℝ ℂ))) := by ring
    rw [h1, Polynomial.rootMultiplicity_mul hQQ, two_mul]
  have hRHS : Polynomial.rootMultiplicity Complex.I
      (Polynomial.C ((algebraMap ℝ ℂ) (c ^ 2)) * (1 + Polynomial.X ^ 2) ^ n) = n := by
    rw [hfactor]
    have hpow : ((Polynomial.X - Polynomial.C Complex.I)
          * (Polynomial.X + Polynomial.C Complex.I) : Polynomial ℂ) ^ n
        = (Polynomial.X - Polynomial.C Complex.I) ^ n
          * (Polynomial.X + Polynomial.C Complex.I) ^ n := mul_pow _ _ _
    rw [hpow, hplus]
    have hne1 : (Polynomial.C ((algebraMap ℝ ℂ) (c ^ 2)) : Polynomial ℂ)
        * ((Polynomial.X - Polynomial.C Complex.I) ^ n
          * (Polynomial.X - Polynomial.C (-Complex.I)) ^ n) ≠ 0 :=
      mul_ne_zero hC0
        (mul_ne_zero (pow_ne_zero n hX1) (pow_ne_zero n hX2))
    rw [Polynomial.rootMultiplicity_mul hne1, Polynomial.rootMultiplicity_C]
    have hne2 : ((Polynomial.X - Polynomial.C Complex.I) ^ n : Polynomial ℂ)
        * (Polynomial.X - Polynomial.C (-Complex.I)) ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero n hX1) (pow_ne_zero n hX2)
    rw [Polynomial.rootMultiplicity_mul hne2,
      Polynomial.rootMultiplicity_X_sub_C_pow]
    have hzero : Polynomial.rootMultiplicity Complex.I
        ((Polynomial.X - Polynomial.C (-Complex.I) : Polynomial ℂ) ^ n) = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      intro hroot
      rw [Polynomial.IsRoot.def] at hroot
      simp only [Polynomial.eval_pow] at hroot
      have heval : ((Polynomial.X - Polynomial.C (-Complex.I) : Polynomial ℂ).eval
          Complex.I) ≠ 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have : Complex.I - (-Complex.I) = 2 * Complex.I := by ring
        rw [this]
        apply mul_ne_zero _ Complex.I_ne_zero
        norm_num
      exact (pow_ne_zero n heval) hroot
    rw [hzero, add_zero, zero_add]
  have heq : 2 * Polynomial.rootMultiplicity Complex.I (P.map (algebraMap ℝ ℂ)) = n := by
    rw [← hLHS, ← hRHS, hmap_eq]
  obtain ⟨m, hm⟩ := hodd
  omega

/-- Step 4 assembly: on `|t| * L < 1` the interpolating polynomial equals
`(μ A).toReal * √(1 + t²) ^ finrank`. -/
private theorem VHair_volume_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (h : E → E) (hh : ContDiff ℝ 1 h)
    (htan : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (h (x : E)) (x : E) = 0)
    (hne : ∀ x : sphere (0 : E) 1, h (x : E) ≠ 0)
    (L : NNReal) (hlip : LipschitzWith L (VHair h))
    (P : Polynomial ℝ)
    (hP : ∀ t : ℝ, P.eval t
      = ∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det ∂μ)
    (t : ℝ) (ht : |t| * (L : ℝ) < 1)
    (hbijt : Function.Bijective (fun x => x + t • VHair h x)) :
    P.eval t = (μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}).toReal
      * Real.sqrt (1 + t ^ 2) ^ Module.finrank ℝ E := by
  have horth : ∀ x, @inner ℝ E _ (VHair h x) x = 0 :=
    fun x => (VHair_inner_norm h htan hne x).1
  have hnorm : ∀ x, ‖VHair h x‖ = ‖x‖ :=
    fun x => (VHair_inner_norm h htan hne x).2
  have hsubA : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ⊆ {0}ᶜ := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hz ⊢
    intro h0
    rw [h0, norm_zero] at hz
    norm_num at hz
  have hDV : ContinuousOn (fun x => fderiv ℝ (VHair h) x)
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    ((VHair_contDiffOn h hh hne).continuousOn_fderiv_of_isOpen
      isOpen_compl_singleton le_rfl).mono hsubA
  have hAcompact : IsCompact {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset
      VHair_annulus_closed VHair_annulus_subset_ball
  have hcont : ContinuousOn
      (fun x => (ContinuousLinearMap.id ℝ E
        + t • fderiv ℝ (VHair h) x).det)
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add (hDV.const_smul t))
  have hInt : MeasureTheory.IntegrableOn
      (fun x => (ContinuousLinearMap.id ℝ E
        + t • fderiv ℝ (VHair h) x).det)
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} μ :=
    hcont.integrableOn_compact hAcompact
  -- Determinants are positive on the annulus here
  have hdet_pos : ∀ x ∈ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      0 < (ContinuousLinearMap.id ℝ E
        + t • fderiv ℝ (VHair h) x).det := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have hbound := VHair_fderiv_bound_L (VHair h) L hlip x
    have hM : ‖t • fderiv ℝ (VHair h) x‖ < 1 := by
      calc ‖t • fderiv ℝ (VHair h) x‖
          = |t| * ‖fderiv ℝ (VHair h) x‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |t| * (L : ℝ) :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg t)
        _ < 1 := ht
    exact det_pos_of_norm_lt_one _ hM
  have hnn : 0 ≤ᵐ[μ.restrict {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}]
      (fun x => (ContinuousLinearMap.id ℝ E
        + t • fderiv ℝ (VHair h) x).det) :=
    (MeasureTheory.ae_restrict_mem
      VHair_annulus_closed.measurableSet).mono
      (fun x hx => (hdet_pos x hx).le)
  have hlin_eq : (∫⁻ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        ENNReal.ofReal
          |(ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det| ∂μ)
      = ∫⁻ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        ENNReal.ofReal
          ((ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det) ∂μ := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem
      VHair_annulus_closed.measurableSet] with x hx
    rw [abs_of_pos (hdet_pos x hx)]
  have hQ : ENNReal.ofReal
        (∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
          (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det ∂μ)
      = ENNReal.ofReal (Real.sqrt (1 + t ^ 2) ^ Module.finrank ℝ E)
        * μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn,
      ← hlin_eq,
      VHair_Ft_lintegral_eq μ h hh hne t hbijt,
      VHair_Ft_image_meas μ (VHair h) horth hnorm t hbijt]
  have hQQ : (∫ x in {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
        (ContinuousLinearMap.id ℝ E + t • fderiv ℝ (VHair h) x).det ∂μ)
      = (μ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}).toReal
        * Real.sqrt (1 + t ^ 2) ^ Module.finrank ℝ E := by
    have hto := congrArg ENNReal.toReal hQ
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg _) _),
      ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg_of_ae hnn)] at hto
    rw [mul_comm] at hto
    exact hto
  rw [hP t, hQQ]

/--
**Hairy ball theorem.** Let $k \in \mathbb{N}$ and let $E$ be a real inner product space of
dimension $2k + 1$, with unit sphere $S = \{x \in E : \|x\| = 1\}$. If $f : S \to E$ is
continuous and $\langle f(x), x \rangle = 0$ for every $x \in S$, then $f(x) = 0$ for some
$x \in S$.

Proves `Wanted` entry `hairyBall_even_sphere_ambient`.

Source: H. Poincaré proved the 2-sphere case in 1885 and L. E. J. Brouwer extended it to
higher even-dimensional spheres in 1912; J. Milnor, Topology from the Differentiable Viewpoint
hairy ball; Guillemin-Pollack, Differential Topology; Lean states even-sphere ambient
finite-dimensional inner-product specialization via `inner = 0`.
-/
theorem hairyBall_even_sphere_ambient
    {k : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hDim : Module.finrank ℝ E = 2 * k + 1)
    (f : sphere (0 : E) 1 → E)
    (hf : Continuous f)
    (hortho : ∀ x : sphere (0 : E) 1, @inner ℝ E _ (f x) (x : E) = 0) :
    ∃ x : sphere (0 : E) 1, f x = 0 := by
  by_contra hcon
  push Not at hcon
  -- Step 1: smooth tangent field without zeros
  obtain ⟨h, hh_smooth, htan, hne⟩ := smooth_tangent_approx f hf hortho hcon
  have hidx : 0 < Module.finrank ℝ E := by omega
  have hne0 : (Module.finBasis ℝ E) ⟨0, hidx⟩ ≠ 0 :=
    (Module.finBasis ℝ E).ne_zero _
  -- Measure setup
  borelize E
  -- Step 2d: global Lipschitz bound
  obtain ⟨L, hlip⟩ := VHair_lipschitz h hh_smooth htan hne
  -- Interval of parameters
  set δ : ℝ := ((L : ℝ) + 1)⁻¹ with hδdef
  have hden : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hmem : ∀ t : ℝ, |t| < δ → |t| * (L : ℝ) < 1 := by
    intro t ht
    have h1 : |t| * (L : ℝ) ≤ δ * (L : ℝ) :=
      mul_le_mul_of_nonneg_right ht.le L.coe_nonneg
    have h2 : δ * (L : ℝ) < 1 := by
      have heq : δ * (L : ℝ) = (L : ℝ) / ((L : ℝ) + 1) := by
        rw [hδdef, div_eq_inv_mul]
      rw [heq]
      exact (div_lt_one hden).mpr (by linarith)
    exact lt_of_le_of_lt h1 h2
  -- Steps 3b, 4c, 4 assembly
  have hbij : ∀ t : ℝ, |t| < δ →
      Function.Bijective (fun x => x + t • VHair h x) := by
    intro t ht
    exact VHair_Ft_bijective (VHair h) L hlip t (hmem t ht)
  obtain ⟨P, hP⟩ := VHair_volume_poly (Module.finBasis ℝ E).addHaar
    h hh_smooth hne det_poly_ex
  obtain ⟨hA0, hAfin⟩ := VHair_annulus_meas (Module.finBasis ℝ E).addHaar
    _ hne0
  have hcpos : 0 < ((Module.finBasis ℝ E).addHaar
      {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}).toReal :=
    ENNReal.toReal_pos hA0 hAfin
  have hodd : Odd (Module.finrank ℝ E) := ⟨k, hDim⟩
  have hPeval : ∀ t : ℝ, |t| < δ →
      P.eval t = ((Module.finBasis ℝ E).addHaar
        {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}).toReal
        * Real.sqrt (1 + t ^ 2) ^ Module.finrank ℝ E := by
    intro t ht
    exact VHair_volume_eq (Module.finBasis ℝ E).addHaar h hh_smooth htan hne
      L hlip P hP t (hmem t ht) (hbij t ht)
  -- Step 5: parity contradiction
  exact poly_sqrt_odd_contradiction hcpos hδ hodd hPeval

end MathlibExt.Geometry.Manifold.HairyBallWanted
