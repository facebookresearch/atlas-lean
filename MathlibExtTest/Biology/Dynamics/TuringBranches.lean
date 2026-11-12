/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringBranches
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Tests for Turing pattern branches: eigenvalues of singular matrices, the Schnakenberg-type
Jacobian `J₀ = [[4/5, 1], [-9/5, -1]]` with `d_u = 1`, `d_v = 9` (unstable on `[0, 11/2]` but
stable on the longer `[0, 7]`, whose band falls in a Neumann gap), neutral diffusions on both
sides of onset, the leading eigenvalue, and an explicit supercritical pitchfork
`G(a, d) = (d - 1) - a²` exercising the branch theorems. -/

open Matrix Filter Topology

namespace MathlibExtTest.Biology.Dynamics.TuringBranches

open MathlibExt.Biology.Dynamics.TuringPatterns MathlibExt.Biology.Dynamics.TuringBranches

/-- The Jacobian `[[4/5, 1], [-9/5, -1]]` (Schnakenberg at `a = 1/10`, `b = 9/10`). -/
local notation "J₀" => !![(4 / 5 : ℝ), 1; -9 / 5, -1]

lemma J₀_trace : (J₀).trace = -1 / 5 := by norm_num [Matrix.trace_fin_two]

lemma J₀_det : (J₀).det = 1 := by norm_num [Matrix.det_fin_two]

lemma J₀_00 : (J₀) 0 0 = 4 / 5 := by simp

lemma J₀_11 : (J₀) 1 1 = -1 := by simp

/-- `h(q) = 9 q² - 31/5 q + 1` for `J₀`, `d_u = 1`, `d_v = 9`. -/
lemma J₀_dispersionDet (q : ℝ) : dispersionDet J₀ 1 9 q = 9 * q ^ 2 - 31 / 5 * q + 1 := by
  rw [dispersionDet, J₀_det, J₀_00, J₀_11]
  ring

/-! ### Eigenvalues of a singular matrix -/

/-- `[[1, 2], [2, 4]]` is singular with trace `5`, so `5` is an eigenvalue. -/
example : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (!![(1 : ℝ), 2; 2, 4]).map (↑) *ᵥ v = (5 : ℂ) • v :=
  (exists_eigenvector_iff_of_det_eq_zero (by norm_num [Matrix.det_fin_two]) 5).2
    (Or.inr (by norm_num [Matrix.trace_fin_two]))

/-- ... and `1` is not. -/
example : ¬ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (!![(1 : ℝ), 2; 2, 4]).map (↑) *ᵥ v = (1 : ℂ) • v := by
  rw [exists_eigenvector_iff_of_det_eq_zero (by norm_num [Matrix.det_fin_two]) 1]
  norm_num [Matrix.trace_fin_two]

/-! ### Continuum versus finite domain -/

lemma J₀_criterion : 2 * Real.sqrt (1 * 9 * (J₀).det) < 9 * (J₀) 0 0 + 1 * (J₀) 1 1 := by
  rw [J₀_det, J₀_00, J₀_11, show (1 * 9 * 1 : ℝ) = 3 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-- Infinitely many real wavenumbers are unstable for `J₀`. -/
example : {k : ℝ | IsUnstableMode J₀ 1 9 k}.Infinite :=
  setOf_isUnstableMode_infinite one_pos (by norm_num) (by rw [J₀_trace]; norm_num) J₀_criterion

/-- The full continuum-versus-Neumann statement for `J₀`. -/
example : {k : ℝ | IsUnstableMode J₀ 1 9 k}.Infinite ∧
    (∀ L, 0 < L → {n : ℕ | IsUnstableMode J₀ 1 9 (neumannWavenumber L n)}.Finite) ∧
    ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ L, 0 < L → L ≤ L₁ →
      (∃ k, IsUnstableMode J₀ 1 9 k) ∧ ¬ IsNeumannUnstable J₀ 1 9 L :=
  continuum_vs_neumann one_pos (by norm_num) (by rw [J₀_trace]; norm_num)
    (by rw [J₀_det]; norm_num) J₀_criterion

/-- On `[0, 11/2]` the first Neumann mode is unstable: `IsNeumannUnstable` is not vacuous. -/
lemma J₀_unstable : IsNeumannUnstable J₀ 1 9 (11 / 2) := by
  rw [isNeumannUnstable_iff]
  refine ⟨1, ?_⟩
  rw [isUnstableMode_iff_dispersionDet_neg (by rw [J₀_trace]; norm_num) zero_le_one
    (by norm_num), J₀_dispersionDet, neumannWavenumber]
  have h1 := Real.pi_gt_three
  have h2 := Real.pi_lt_d2
  set q := ((1 : ℕ) * Real.pi / (11 / 2)) ^ 2 with hq
  have hlo : 36 / 121 < q := by
    rw [hq]
    push_cast
    nlinarith
  have hhi : q < 40 / 121 := by
    rw [hq]
    push_cast
    nlinarith
  nlinarith

/-- `√(61/25)` lies in `(39/25, 391/250)`. -/
lemma sqrt_bounds : 39 / 25 < Real.sqrt (61 / 25) ∧ Real.sqrt (61 / 25) < 391 / 250 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

lemma J₀_bandDiscriminant : bandDiscriminant J₀ 1 9 = 61 / 25 := by
  rw [bandDiscriminant, J₀_det, J₀_00, J₀_11]
  norm_num

/-- On the *longer* interval `[0, 7]` the band falls between `(π/7)²` and `(2π/7)²`, so no
Neumann mode is unstable: instability is not monotone in the domain length. -/
lemma J₀_stable : ¬ IsNeumannUnstable J₀ 1 9 7 := by
  have h1 := Real.pi_gt_three
  have h2 := Real.pi_lt_d2
  obtain ⟨hs1, hs2⟩ := sqrt_bounds
  refine not_isNeumannUnstable_of_gap one_pos (by norm_num) (by rw [J₀_trace]; norm_num)
    (by norm_num) 1 ?_ ?_
  · rw [bandLower, J₀_bandDiscriminant, J₀_00, J₀_11]
    push_cast
    have : (1 * Real.pi / 7) ^ 2 < 1 / 4 := by nlinarith
    have : 1 / 4 < (9 * (4 / 5) + 1 * -1 - Real.sqrt (61 / 25)) / (2 * 1 * 9) := by
      rw [lt_div_iff₀ (by norm_num)]
      linarith
    linarith
  · rw [bandUpper, J₀_bandDiscriminant, J₀_00, J₀_11]
    push_cast
    have : (9 * (4 / 5) + 1 * -1 + Real.sqrt (61 / 25)) / (2 * 1 * 9) < 1 / 2 := by
      rw [div_lt_iff₀ (by norm_num)]
      linarith
    have : (1 : ℝ) / 2 < ((1 + 1) * Real.pi / 7) ^ 2 := by nlinarith
    linarith

/-- Unstable on `[0, 11/2]`, stable on `[0, 7]`. -/
example : IsNeumannUnstable J₀ 1 9 (11 / 2) ∧ ¬ IsNeumannUnstable J₀ 1 9 7 :=
  ⟨J₀_unstable, J₀_stable⟩

/-- A Neumann eigenvalue with positive real part exists on `[0, 11/2]`, realized by a zero-flux
solution of the linearized system. -/
example : ∃ μ : ℂ, 0 < μ.re ∧ ∃ (n : ℕ) (v : Fin 2 → ℂ), v ≠ 0 ∧
    IsLinearizedSolution J₀ 1 9 (fourierMode μ (neumannWavenumber (11 / 2) n) v) := by
  obtain ⟨μ, hμ, hev⟩ := J₀_unstable
  obtain ⟨n, v, hv, hsol, -⟩ := hev.exists_solution (by norm_num)
  exact ⟨μ, hμ, n, v, hv, hsol⟩

/-- Small domains are stable for `J₀`. -/
example : ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ L, 0 < L → L ≤ L₁ → ¬ IsNeumannUnstable J₀ 1 9 L :=
  exists_forall_not_isNeumannUnstable one_pos (by norm_num) (by rw [J₀_trace]; norm_num)
    (by rw [J₀_det]; norm_num)

/-! ### Neutral diffusion and onset -/

/-- The neutral diffusion of `q = (1/2)² = 1/4` is `100/11`. -/
lemma J₀_neutral : neutralDiffusion J₀ 1 ((1 / 2) ^ 2) = 100 / 11 := by
  rw [neutralDiffusion, J₀_det, J₀_00, J₀_11]
  norm_num

lemma J₀_admissible : 0 < (J₀) 0 0 * (1 / 2 : ℝ) ^ 2 - 1 * ((1 / 2 : ℝ) ^ 2) ^ 2 := by
  rw [J₀_00]
  norm_num

/-- Mode `k = 1/2` is unstable at `d = 10 > 100/11` ... -/
example : IsUnstableMode J₀ 1 10 (1 / 2) := by
  rw [isUnstableMode_iff_neutralDiffusion_lt (by rw [J₀_trace]; norm_num) zero_le_one
    (by norm_num) J₀_admissible, J₀_neutral]
  norm_num

/-- ... and stable at `d = 9 < 100/11`. -/
example : ¬ IsUnstableMode J₀ 1 9 (1 / 2) := by
  rw [isUnstableMode_iff_neutralDiffusion_lt (by rw [J₀_trace]; norm_num) zero_le_one
    (by norm_num) J₀_admissible, J₀_neutral]
  norm_num

/-- The inadmissible wavenumber `k = 1` (`f_u - d_u = -1/5 ≤ 0`) is stable even at `d = 100`. -/
example : ¬ IsUnstableMode J₀ 1 100 1 :=
  not_isUnstableMode_of_inadmissible (by rw [J₀_trace]; norm_num) zero_le_one (by norm_num)
    (by rw [J₀_det]; norm_num) (by rw [J₀_11]; norm_num) (by rw [J₀_00]; norm_num)

/-- At the neutral diffusion `100/11` the mode `k = 1/2` has the eigenvalue `0`. -/
example : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
    (modeMatrix J₀ 1 (100 / 11) (1 / 2)).map (↑) *ᵥ v = (0 : ℂ) • v :=
  (exists_eigenvector_modeMatrix_iff_of_neutral J₀_admissible.ne'
    J₀_neutral.symm 0).2 (Or.inl rfl)

/-- The onset criterion on `[0, 11/2]` at `d = 9` (`J₀` is unstable there). -/
example : ∃ n : ℕ,
    0 < (J₀) 0 0 * neumannWavenumber (11 / 2) n ^ 2 - 1 * (neumannWavenumber (11 / 2) n ^ 2) ^ 2 ∧
      neutralDiffusion J₀ 1 (neumannWavenumber (11 / 2) n ^ 2) < 9 :=
  (isNeumannUnstable_iff_exists_neutralDiffusion_lt (by rw [J₀_trace]; norm_num) zero_le_one
    (by norm_num) (by rw [J₀_det]; norm_num) (by rw [J₀_11]; norm_num)).1 J₀_unstable

/-! ### Leading eigenvalue and transversal crossing -/

/-- `leadingEigenvalue (diag (-1, 2)) = 2`. -/
example : leadingEigenvalue !![(-1 : ℝ), 0; 0, 2] = 2 := by
  rw [leadingEigenvalue]
  norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The critical eigenvalue of mode `k = 1/2` crosses zero at `d = 100/11` with positive speed. -/
example : leadingEigenvalue (modeMatrix J₀ 1 (100 / 11) (1 / 2)) = 0 ∧
    0 < (1 * ((1 / 2 : ℝ) ^ 2) ^ 2 - (J₀) 0 0 * (1 / 2) ^ 2) /
      ((J₀).trace - (1 / 2) ^ 2 * (1 + 100 / 11)) := by
  obtain ⟨h0, -, hpos⟩ := leadingEigenvalue_crossing (J := J₀) (du := 1) (d₀ := 100 / 11)
    (k := 1 / 2) (by rw [J₀_trace]; norm_num) J₀_admissible J₀_neutral.symm
  exact ⟨h0, hpos⟩

/-- Non-resonance: at `d = 100/11` on a domain where only mode `1` is neutral. -/
example {L : ℝ} (hn : dispersionDet J₀ 1 (100 / 11) (neumannWavenumber L 1 ^ 2) = 0)
    (hnr : ∀ m, m ≠ 1 → dispersionDet J₀ 1 (100 / 11) (neumannWavenumber L m ^ 2) ≠ 0) :
    {m : ℕ | ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (modeMatrix J₀ 1 (100 / 11) (neumannWavenumber L m)).map (↑) *ᵥ v = (0 : ℂ) • v} = {1} :=
  setOf_neumann_zero_eigen_eq_singleton hn hnr

/-! ### An explicit supercritical pitchfork -/

/-- The reduced map `G(a, d) = (d - 1) - a²` (normal form of a supercritical pitchfork at
`d₀ = 1`) is strictly differentiable at `(0, 1)` with derivative `(a, d) ↦ d`. -/
lemma pitchfork_hasStrictFDerivAt :
    HasStrictFDerivAt (fun p : ℝ × ℝ => p.2 - 1 - p.1 ^ 2) (ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((0 : ℝ), (1 : ℝ)) := by
  have h := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), (1 : ℝ)))).sub_const 1).sub
    ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), (1 : ℝ)))).mul
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), (1 : ℝ)))))
  convert h using 1
  · funext p
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  · ext <;> simp

/-- The pattern branch of the pitchfork exists, and it is `d = 1 + a²` for small `a ≠ 0`. -/
example : ∃ φ : ℝ → ℝ, φ 0 = 1 ∧ ∀ᶠ a in 𝓝[≠] (0 : ℝ), φ a = 1 + a ^ 2 := by
  obtain ⟨φ, hφ0, -, hzero⟩ := exists_patternBranch pitchfork_hasStrictFDerivAt
    (by norm_num) (by simp)
  refine ⟨φ, hφ0, ?_⟩
  have hp : Tendsto (fun a : ℝ => (a, 1 + a ^ 2)) (𝓝[≠] (0 : ℝ)) (𝓝 ((0 : ℝ), (1 : ℝ))) := by
    have : Continuous fun a : ℝ => (a, 1 + a ^ 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hp.eventually hzero, self_mem_nhdsWithin] with a ha ha0
  have := ha.1 (by ring)
  exact (this.resolve_left ha0).symm

/-- The pitchfork branch is supercritical (`φ(a) > 1`) and linearly stable (`λ < 0`): the
coefficient `H = -1` of `a²` is negative. -/
example : ∃ φ : ℝ → ℝ, φ 0 = 1 ∧ ∀ᶠ a in 𝓝[≠] (0 : ℝ), 1 < φ a ∧
    ∃ lam : ℝ, HasDerivAt (fun x => x * (φ a - 1 - x ^ 2)) lam a ∧ lam < 0 := by
  obtain ⟨φ, hφ0, hφd, hzero⟩ := exists_patternBranch pitchfork_hasStrictFDerivAt
    (by norm_num) (by simp)
  have hσ : HasDerivAt (fun d : ℝ => d - 1 - (0 : ℝ) ^ 2) 1 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).sub_const 1
  have h := patternBranch_direction_stability (H := fun _ => -1) (Ha := fun _ => 0) hφ0
    hφd.hasDerivAt.continuousAt hzero (by norm_num) hσ one_pos
    (Eventually.of_forall fun p => by ring) continuousAt_const (by norm_num)
    (Eventually.of_forall fun p => hasDerivAt_const _ _) continuousAt_const
  refine ⟨φ, hφ0, ?_⟩
  filter_upwards [h] with a ⟨hdir, lam, hlam, hneg⟩
  exact ⟨by linarith, lam, hlam, by linarith⟩

/-! ### The Turing branch theorem on a concrete instance

`G(a, d) = leadingEigenvalue (J₀ - (1/2)² D(d)) - a²` with `d_u = 1`, `k = 1/2`, `d₀ = 100/11`:
equal to the critical eigenvalue on the trivial branch and strictly differentiable at `(0, d₀)`
(the discriminant there is `tr² > 0`), so the hypotheses of `turing_patternBranch_stability` hold
together. -/

/-- `G` is `C¹` at `(0, 100/11)`. -/
lemma J₀_G_contDiffAt : ContDiffAt ℝ 1
    (fun p : ℝ × ℝ => leadingEigenvalue (modeMatrix J₀ 1 p.2 (1 / 2)) - p.1 ^ 2)
    ((0 : ℝ), (100 / 11 : ℝ)) := by
  have hfun : (fun p : ℝ × ℝ => leadingEigenvalue (modeMatrix J₀ 1 p.2 (1 / 2)) - p.1 ^ 2) =
      fun p : ℝ × ℝ => ((J₀).trace - (1 / 2) ^ 2 * (1 + p.2) +
        Real.sqrt (((J₀).trace - (1 / 2) ^ 2 * (1 + p.2)) ^ 2 -
          4 * (1 * p.2 * ((1 / 2) ^ 2) ^ 2 - (p.2 * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 +
            (J₀).det))) / 2 - p.1 ^ 2 := by
    funext p
    rw [leadingEigenvalue, trace_modeMatrix, det_modeMatrix, dispersionDet]
  rw [hfun]
  have hD : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ((J₀).trace - (1 / 2) ^ 2 * (1 + p.2)) ^ 2 -
      4 * (1 * p.2 * ((1 / 2) ^ 2) ^ 2 - (p.2 * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 +
        (J₀).det)) ((0 : ℝ), (100 / 11 : ℝ)) := by
    fun_prop
  have hne : ((J₀).trace - (1 / 2) ^ 2 * (1 + (100 / 11 : ℝ))) ^ 2 -
      4 * (1 * (100 / 11 : ℝ) * ((1 / 2) ^ 2) ^ 2 -
        ((100 / 11 : ℝ) * (J₀) 0 0 + 1 * (J₀) 1 1) * (1 / 2) ^ 2 + (J₀).det) ≠ 0 := by
    rw [J₀_trace, J₀_00, J₀_11, J₀_det]
    norm_num
  have hT : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (J₀).trace - (1 / 2) ^ 2 * (1 + p.2))
      ((0 : ℝ), (100 / 11 : ℝ)) := by
    fun_prop
  exact ((hT.add (hD.sqrt hne)).div_const 2).sub (by fun_prop)

/-- **Non-vacuity of `turing_patternBranch_stability`.** For `J₀` at the neutral diffusion
`100/11` of `k = 1/2`, with `G(a, d) = leadingEigenvalue (J₀ - (1/2)² D(d)) - a²` and `H = -1`,
the pattern branch is supercritical (`φ(a) > 100/11`) and linearly stable. -/
example : ∃ φ : ℝ → ℝ, φ 0 = 100 / 11 ∧ ∀ᶠ a in 𝓝[≠] (0 : ℝ), 100 / 11 < φ a ∧
    ∃ lam : ℝ, HasDerivAt
      (fun x => x * (leadingEigenvalue (modeMatrix J₀ 1 (φ a) (1 / 2)) - x ^ 2)) lam a ∧
      lam < 0 := by
  obtain ⟨φ, hφ0, -, -, -, hbr⟩ := turing_patternBranch_stability (J := J₀) (du := 1)
    (k := 1 / 2) (d₀ := 100 / 11) (H := fun _ => -1) (Ha := fun _ => 0)
    (by rw [J₀_trace]; norm_num) J₀_admissible J₀_neutral.symm
    (J₀_G_contDiffAt.hasStrictFDerivAt one_ne_zero)
    (Eventually.of_forall fun d => by simp)
    (Eventually.of_forall fun p => by simp [sub_eq_add_neg])
    continuousAt_const (by norm_num)
    (Eventually.of_forall fun p => hasDerivAt_const _ _) continuousAt_const
  refine ⟨φ, hφ0, ?_⟩
  filter_upwards [hbr] with a ⟨hdir, lam, hlam, hneg⟩
  exact ⟨by linarith, lam, hlam, by linarith⟩

end MathlibExtTest.Biology.Dynamics.TuringBranches
