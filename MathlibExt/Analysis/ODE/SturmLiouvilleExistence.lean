/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import MathlibExt.Analysis.ODE.MaximalSolution

@[expose] public section

namespace MathlibExt.Analysis.ODE.SturmLiouvilleExistence

open MeasureTheory Set Filter Topology
open scoped NNReal

/-!
# Existence for the Sturm–Liouville Dirichlet problem on `[0, 1]`

Given a continuous nonnegative potential `V` and a continuous right-hand side
`f`, there is a `C²` function `u` on `[0, 1]` satisfying `-u'' + V u = f` with
Dirichlet boundary conditions `u 0 = u 1 = 0`.

The proof is by the shooting method. The second-order equation is rewritten as
a first-order system for `(u, u')`, whose globally Lipschitz vector field has
a global solution by the existing API in
`MathlibExt.Analysis.ODE.MaximalSolution`. Two solutions of the system with
initial data `(0, a)` and `(0, 0)` differ by `a` times the solution with initial
data `(0, 1)` for the homogeneous equation: both sides solve the same initial
value problem, so Lipschitz ODE uniqueness identifies them. The homogeneous solution `w` satisfies `w 0 = 0` and `w' 0 = 1`;
an energy argument (integration by parts, using `V ≥ 0`) shows `w 1 ≠ 0`:
otherwise `w` would vanish identically, contradicting `w' 0 = 1`. Choosing
`a = -u₀ 1 / w 1` then gives a solution with `u 1 = 0`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.sturm_liouville_existence` (Theorem, Section on solving the
Dirichlet problem). The v1 formalization of this theorem is left unproved,
so this module gives an original proof. The separate uniqueness theorem
`SpectralTheory.sturm_liouville_uniqueness` is formalized in
`MathlibExt/Analysis/ODE/SturmLiouvilleUniqueness.lean`. The energy argument
below proves the homogeneous uniqueness property needed for shooting.
-/

/-- Clamp a real number into `[0, 1]`, as a point of the subtype. -/
private noncomputable def clamp01 (t : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 t), ⟨le_min zero_le_one (le_max_left 0 t), min_le_left 1 _⟩⟩

private theorem continuous_clamp01 : Continuous clamp01 :=
  Continuous.subtype_mk ((continuous_const.min (continuous_const.max continuous_id))) _

private theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clamp01 t = ⟨t, ht⟩ := by
  apply Subtype.ext
  show min 1 (max 0 t) = t
  rw [max_eq_right ht.1, min_eq_right ht.2]

/-- Extend a continuous function on `[0, 1]` to a continuous function on `ℝ`
by clamping the argument into `[0, 1]`. -/
private noncomputable def ext01 (f : C(Set.Icc (0 : ℝ) 1, ℝ)) : ℝ → ℝ :=
  fun t => f (clamp01 t)

private theorem continuous_ext01 (f : C(Set.Icc (0 : ℝ) 1, ℝ)) : Continuous (ext01 f) :=
  f.continuous.comp continuous_clamp01

private theorem ext01_of_mem (f : C(Set.Icc (0 : ℝ) 1, ℝ)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ext01 f t = f ⟨t, ht⟩ := by
  show f (clamp01 t) = f ⟨t, ht⟩
  rw [clamp01_of_mem ht]

private theorem ext01_nonneg (f : C(Set.Icc (0 : ℝ) 1, ℝ))
    (hf : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ f x) (t : ℝ) : 0 ≤ ext01 f t :=
  hf (clamp01 t)

/-- The second iterated derivative within `[0, 1]` is the derivative of the
derivative within `[0, 1]`. -/
private theorem iteratedDerivWithin_two (u : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    iteratedDerivWithin 2 u s x = derivWithin (derivWithin u s) s x := by
  have h1 : iteratedDerivWithin 2 u s = derivWithin (iteratedDerivWithin 1 u s) s :=
    iteratedDerivWithin_succ
  have h0 : iteratedDerivWithin 1 u s = derivWithin u s := by
    simp [iteratedDerivWithin_succ]
  rw [h1, h0]

/-- The first-order system for the Sturm–Liouville equation `-u'' + V u = c`:
the state `(u, p)` evolves by `(p, V·u - c)`. -/
private noncomputable def sys (Vext c : ℝ → ℝ) : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
  fun t p => (p.2, Vext t * p.1 - c t)

/-- The system is Lipschitz in the state, uniformly in time, with constant
`max 1 MV` where `MV` bounds `|Vext|`. -/
private theorem lipschitz_sys {Vext c : ℝ → ℝ} {MV : ℝ} (hMV : ∀ t, |Vext t| ≤ MV)
    (hMV0 : 0 ≤ MV) {K : ℝ≥0} (hK : (K : ℝ) = max 1 MV) (t : ℝ) :
    LipschitzWith K (sys Vext c t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Prod.dist_eq, Prod.dist_eq]
  show max (dist x.2 y.2) (dist (Vext t * x.1 - c t) (Vext t * y.1 - c t)) ≤
    (K : ℝ) * max (dist x.1 y.1) (dist x.2 y.2)
  have h1 : dist (Vext t * x.1 - c t) (Vext t * y.1 - c t) = |Vext t| * dist x.1 y.1 := by
    rw [dist_eq_norm, dist_eq_norm, ← Real.norm_eq_abs, ← norm_mul]
    congr 1
    ring
  rw [h1]
  apply max_le
  · calc dist x.2 y.2
        ≤ max (dist x.1 y.1) (dist x.2 y.2) := le_max_right _ _
      _ = 1 * max (dist x.1 y.1) (dist x.2 y.2) := (one_mul _).symm
      _ ≤ (K : ℝ) * max (dist x.1 y.1) (dist x.2 y.2) := by
          rw [hK]
          exact mul_le_mul_of_nonneg_right (le_max_left 1 MV)
            (le_max_of_le_left dist_nonneg)
  · calc |Vext t| * dist x.1 y.1
        ≤ MV * max (dist x.1 y.1) (dist x.2 y.2) :=
          mul_le_mul (hMV t) (le_max_left _ _) dist_nonneg hMV0
      _ ≤ (K : ℝ) * max (dist x.1 y.1) (dist x.2 y.2) := by
          rw [hK]
          exact mul_le_mul_of_nonneg_right (le_max_right 1 MV)
            (le_max_of_le_left dist_nonneg)

/-- The system is jointly continuous in `(t, state)`. -/
private theorem continuous_sys_uncurry {Vext c : ℝ → ℝ} (hV : Continuous Vext)
    (hc : Continuous c) :
    Continuous fun p : ℝ × (ℝ × ℝ) => sys Vext c p.1 p.2 := by
  apply Continuous.prodMk (continuous_snd.comp continuous_snd)
  exact ((hV.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).sub
    (hc.comp continuous_fst)

/-- Solutions of the first-order system, with their `C²` regularity and the
second-order equation. The functions `u`, `p` are the two components of the
first-order solution: `u` solves `-u'' + Vext·u = c` in the
`iteratedDerivWithin` sense. -/
private theorem exists_solution {Vext c : ℝ → ℝ} (hV : Continuous Vext) (hc : Continuous c)
    {MV : ℝ} (hMV : ∀ t, |Vext t| ≤ MV) (hMV0 : 0 ≤ MV) (y₀ : ℝ × ℝ) :
    ∃ u p : ℝ → ℝ, Continuous u ∧ Continuous p ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (p t) t) ∧
      (∀ t, HasDerivAt p (Vext t * u t - c t) t) ∧
      u 0 = y₀.1 ∧ p 0 = y₀.2 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        iteratedDerivWithin 2 u (Set.Icc 0 1) t = Vext t * u t - c t) ∧
      ContDiffOn ℝ 2 u (Set.Icc 0 1) := by
  set K : ℝ≥0 := ⟨max 1 MV, by positivity⟩ with hKdef
  have hK : (K : ℝ) = max 1 MV := rfl
  obtain ⟨Y, ⟨hY0, hYder⟩, _⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (sys Vext c) 0 y₀ K (continuous_sys_uncurry hV hc) (lipschitz_sys hMV hMV0 hK)
  have hYcont : Continuous Y :=
    continuous_iff_continuousAt.mpr fun t => (hYder t).continuousAt
  have hInt : ∀ t : ℝ, IntervalIntegrable (fun s => sys Vext c s (Y s)) volume 0 t :=
    fun t => ((continuous_sys_uncurry hV hc).comp
      (continuous_id.prodMk hYcont)).intervalIntegrable 0 t
  have hYeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Y t = y₀ + ∫ s in (0 : ℝ)..t, sys Vext c s (Y s) := by
    intro t _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hYder s) (hInt t)
    rw [hY0] at hFTC
    rw [hFTC, add_comm, sub_add_cancel]
  set u : ℝ → ℝ := fun t => y₀.1 + ∫ s in (0 : ℝ)..t, (Y s).2 with hu_def
  set p : ℝ → ℝ := fun t => y₀.2 + ∫ s in (0 : ℝ)..t, (Vext s * u s - c s) with hp_def
  have hu_cont : Continuous u := by
    rw [hu_def]
    exact Continuous.add continuous_const
      (intervalIntegral.continuous_primitive
        (fun u' w' => (hYcont.snd).intervalIntegrable u' w') 0)
  have hp_cont : Continuous p := by
    rw [hp_def]
    exact Continuous.add continuous_const
      (intervalIntegral.continuous_primitive
        (fun u' w' => ((hV.mul hu_cont).sub hc).intervalIntegrable u' w') 0)
  have hYcomp1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = (Y t).1 := by
    intro t ht
    have hcomp : (∫ s in (0 : ℝ)..t, sys Vext c s (Y s)).1 =
        ∫ s in (0 : ℝ)..t, (Y s).2 := by
      show (ContinuousLinearMap.fst ℝ ℝ ℝ) (∫ s in (0 : ℝ)..t, sys Vext c s (Y s)) = _
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (hInt t)]
      apply intervalIntegral.integral_congr
      intro s _
      show (sys Vext c s (Y s)).1 = (Y s).2
      rfl
    rw [hu_def, hYeq t ht, Prod.fst_add, hcomp]
  have hYcomp2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, p t = (Y t).2 := by
    intro t ht
    have hcomp : (∫ s in (0 : ℝ)..t, sys Vext c s (Y s)).2 =
        ∫ s in (0 : ℝ)..t, (Vext s * (Y s).1 - c s) := by
      show (ContinuousLinearMap.snd ℝ ℝ ℝ) (∫ s in (0 : ℝ)..t, sys Vext c s (Y s)) = _
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.snd ℝ ℝ ℝ) (hInt t)]
      apply intervalIntegral.integral_congr
      intro s _
      show (sys Vext c s (Y s)).2 = Vext s * (Y s).1 - c s
      rfl
    rw [hp_def, hYeq t ht, Prod.snd_add, hcomp]
    show y₀.2 + ∫ s in (0 : ℝ)..t, (Vext s * u s - c s) =
      y₀.2 + ∫ s in (0 : ℝ)..t, Vext s * (Y s).1 - c s
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    show Vext s * u s - c s = Vext s * (Y s).1 - c s
    have hs' : s ∈ Set.Icc (0 : ℝ) t := by rwa [Set.uIcc_of_le ht.1] at hs
    rw [hYcomp1 s ⟨hs'.1, le_trans hs'.2 ht.2⟩]
  have hu_deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (p t) t := by
    intro t ht
    rw [hYcomp2 t ht]
    show HasDerivAt (fun t => y₀.1 + ∫ s in (0 : ℝ)..t, (Y s).2) ((Y t).2) t
    exact (intervalIntegral.integral_hasDerivAt_right
      ((hYcont.snd).intervalIntegrable 0 t)
      ((hYcont.snd).stronglyMeasurableAtFilter volume (𝓝 t))
      (hYcont.snd.continuousAt)).const_add y₀.1
  have hp_deriv : ∀ t, HasDerivAt p (Vext t * u t - c t) t := by
    intro t
    show HasDerivAt (fun t => y₀.2 + ∫ s in (0 : ℝ)..t, (Vext s * u s - c s))
      (Vext t * u t - c t) t
    exact (intervalIntegral.integral_hasDerivAt_right
      (((hV.mul hu_cont).sub hc).intervalIntegrable 0 t)
      (((hV.mul hu_cont).sub hc).stronglyMeasurableAtFilter volume (𝓝 t))
      (((hV.mul hu_cont).sub hc).continuousAt)).const_add y₀.2
  have hdew : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      derivWithin u (Set.Icc (0 : ℝ) 1) x = p x := by
    intro x hx
    exact (hu_deriv x hx).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one x hx)
  have hdewP : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      derivWithin p (Set.Icc (0 : ℝ) 1) x = Vext x * u x - c x := by
    intro x hx
    exact (hp_deriv x).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one x hx)
  have hiter : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      iteratedDerivWithin 2 u (Set.Icc 0 1) t = Vext t * u t - c t := by
    intro t ht
    rw [iteratedDerivWithin_two]
    have hdew2 : derivWithin (derivWithin u (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) t =
        derivWithin p (Set.Icc (0 : ℝ) 1) t :=
      derivWithin_congr (fun x hx => hdew x hx) (hdew t ht)
    rw [hdew2]
    exact (hp_deriv t).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one t ht)
  have hContDiffP : ContDiffOn ℝ 1 p (Set.Icc 0 1) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_derivWithin uniqueDiffOn_Icc_zero_one]
    refine ⟨?_, fun h => by simp at h, ?_⟩
    · intro x hx
      exact (hp_deriv x).hasDerivWithinAt.differentiableWithinAt
    · rw [contDiffOn_zero]
      exact (((hV.mul hu_cont).sub hc).continuousOn).congr
        (fun x hx => hdewP x hx)
  have hcontdiff : ContDiffOn ℝ 2 u (Set.Icc 0 1) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
      contDiffOn_succ_iff_derivWithin uniqueDiffOn_Icc_zero_one]
    refine ⟨?_, fun h => by simp at h, ?_⟩
    · intro x hx
      exact (hu_deriv x hx).hasDerivWithinAt.differentiableWithinAt
    · exact hContDiffP.congr (fun x hx => hdew x hx)
  refine ⟨u, p, hu_cont, hp_cont, hu_deriv, hp_deriv, ?_, ?_, hiter, hcontdiff⟩
  · rw [hu_def]
    simp
  · rw [hp_def]
    simp


/-- **Energy argument.** A solution of the homogeneous equation `-w'' + Vext·w = 0`
with `w 0 = w 1 = 0` vanishes identically, together with its derivative `p`.
Indeed, integration by parts gives `∫₀¹ (Vext·w² + p²) = 0`; both terms are
nonnegative, so `p = 0` on `(0, 1]`, and then `w t = w 0 + ∫₀ᵗ p = 0`; finally
`p 0 = 0` because `w` is identically `0` on `[0, 1]`. -/
private theorem eq_zero_of_homogeneous {Vext : ℝ → ℝ} (hV : ∀ t, 0 ≤ Vext t)
    (hVcont : Continuous Vext) (w p : ℝ → ℝ) (hwcont : Continuous w) (hpcont : Continuous p)
    (hwder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt w (p t) t)
    (hpder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt p (Vext t * w t) t)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, w t = 0 ∧ p t = 0 := by
  have hIBP : ∫ x in (0 : ℝ)..1, (Vext x * w x) * w x + p x * p x = 0 := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub (u := p)
      (u' := fun t => Vext t * w t) (v := w) (v' := p)
      (fun x hx => hpder x (by rwa [Set.uIcc_of_le zero_le_one] at hx))
      (fun x hx => hwder x (by rwa [Set.uIcc_of_le zero_le_one] at hx))
      ((hVcont.mul hwcont).intervalIntegrable 0 1) (hpcont.intervalIntegrable 0 1)
    rw [hw1, hw0] at h
    simpa using h
  set g : ℝ → ℝ := fun t => (Vext t * w t) * w t + p t * p t with hg_def
  have hg_nonneg : ∀ t, 0 ≤ g t := by
    intro t
    have hrew : g t = Vext t * (w t)^2 + (p t)^2 := by rw [hg_def]; ring
    rw [hrew]
    exact add_nonneg (mul_nonneg (hV t) (sq_nonneg _)) (sq_nonneg _)
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact ((hVcont.mul hwcont).mul hwcont).add (hpcont.mul hpcont)
  have hg_int : IntervalIntegrable g volume 0 1 := hg_cont.intervalIntegrable 0 1
  have hae : g =ᵐ[volume.restrict (Set.Ioc 0 1)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
      (Filter.Eventually.of_forall fun t => hg_nonneg t) hg_int).mp hIBP
  have hEqOn : Set.EqOn g 0 (Set.Ioc (0 : ℝ) 1) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae hg_cont.continuousOn continuousOn_const
      (Ioc_subset_closure_interior 0 1)
  have hp0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, p t = 0 := by
    intro t ht
    have hgt : g t = 0 := hEqOn ht
    have hrew : g t = Vext t * (w t)^2 + (p t)^2 := by rw [hg_def]; ring
    rw [hrew] at hgt
    have h1 : 0 ≤ Vext t * (w t)^2 := mul_nonneg (hV t) (sq_nonneg _)
    have h2 : 0 ≤ (p t)^2 := sq_nonneg _
    have hpt : (p t)^2 = 0 := by linarith
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpt
  have hw0' : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t = 0 := by
    intro t ht
    have hFTC : ∫ x in (0 : ℝ)..t, p x = w t - w 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => by
          have hx' : x ∈ Set.Icc (0 : ℝ) t := by rwa [Set.uIcc_of_le ht.1] at hx
          exact hwder x ⟨hx'.1, le_trans hx'.2 ht.2⟩)
        (hpcont.intervalIntegrable 0 t)
    have hInt0 : ∫ x in (0 : ℝ)..t, p x = 0 := by
      have hcongr : ∫ x in (0 : ℝ)..t, p x = ∫ x in (0 : ℝ)..t, (0 : ℝ) :=
        intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => by
          have hx' : x ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.1] at hx
          exact hp0 x ⟨hx'.1, le_trans hx'.2 ht.2⟩))
      rw [hcongr]
      simp
    rw [hInt0, hw0] at hFTC
    linarith
  have hp0end : p 0 = 0 := by
    have h1 : derivWithin w (Set.Icc (0 : ℝ) 1) 0 = p 0 :=
      (hwder 0 (by norm_num)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc_zero_one 0 (by norm_num))
    have hcong : derivWithin w (Set.Icc (0 : ℝ) 1) 0 =
        derivWithin (0 : ℝ → ℝ) (Set.Icc (0 : ℝ) 1) 0 :=
      derivWithin_congr (fun x hx => by simp [hw0' x hx]) (by simp [hw0])
    rw [hcong] at h1
    simp [derivWithin_zero] at h1
    exact h1.symm
  intro t ht
  refine ⟨hw0' t ht, ?_⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]
    exact hp0end
  · rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]
      exact hp0 1 ⟨by norm_num, le_refl 1⟩
    · exact hp0 t ⟨h0, h1.le⟩


/-- **Existence for the Sturm–Liouville Dirichlet problem on the closed unit interval.** Let $V$
and $f$ be continuous real functions on $[0, 1]$ with $V \ge 0$. Then there is a function
$u \colon \mathbb{R} \to \mathbb{R}$ that is $C^2$ on $[0, 1]$, satisfies
$-u''(x) + V(x)\,u(x) = f(x)$ for every $x \in [0, 1]$, with the second derivative taken within
$[0, 1]$, and has $u(0) = u(1) = 0$.

The proof is by the shooting method: let $u_0$ solve the equation with $u_0(0) = u_0'(0) = 0$,
and let $w$ solve the homogeneous equation $-w'' + V w = 0$ with $w(0) = 0$ and $w'(0) = 1$. An
energy argument using $V \ge 0$ shows $w(1) \ne 0$, and $u = u_0 + a w$ with
$a = -u_0(1)/w(1)$ is the required solution.

Source: `SpectralTheory.sturm_liouville_existence` in the v1 formalization, whose formalization
is left unproved there; the proof here is original. -/
theorem sturm_liouville_existence
    (V : C(Set.Icc (0 : ℝ) 1, ℝ)) (hV : ∀ x : Set.Icc (0 : ℝ) 1, 0 ≤ V x)
    (f : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    ∃ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Icc 0 1) ∧
      (∀ x : ℝ, ∀ hx : x ∈ Set.Icc (0 : ℝ) 1, -(iteratedDerivWithin 2 u (Set.Icc 0 1) x) +
        V ⟨x, hx⟩ * u x = f ⟨x, hx⟩) ∧
      u 0 = 0 ∧ u 1 = 0 := by
  set Vext := ext01 V with hVext_def
  set fext := ext01 f with hfext_def
  have hVext : Continuous Vext := continuous_ext01 V
  have hfext : Continuous fext := continuous_ext01 f
  have hVext_nonneg : ∀ t, 0 ≤ Vext t := fun t => ext01_nonneg V hV t
  have hVext_mem : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), Vext t = V ⟨t, ht⟩ :=
    fun t ht => ext01_of_mem V ht
  have hfext_mem : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), fext t = f ⟨t, ht⟩ :=
    fun t ht => ext01_of_mem f ht
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr zero_le_one) (V.continuous.norm.continuousOn)
  set MV : ℝ := ‖V x₀‖ with hMV_def
  have hMV0 : 0 ≤ MV := norm_nonneg _
  have hMV : ∀ t, |Vext t| ≤ MV := by
    intro t
    have h1 : |Vext t| = ‖V (clamp01 t)‖ := by rw [Real.norm_eq_abs]; rfl
    rw [h1]
    exact hmax (clamp01 t).2
  set K : ℝ≥0 := ⟨max 1 MV, by positivity⟩ with hKdef
  have hK : (K : ℝ) = max 1 MV := rfl
  obtain ⟨w, pw, hwcont, hpwcont, hwder, hpwder, hw0, hpw0, hwiter, hwC2⟩ :=
    exists_solution hVext (continuous_const : Continuous (0 : ℝ → ℝ)) hMV hMV0 (0, 1)
  obtain ⟨u₀, pu₀, hu0cont, hpu0cont, hu0der, hpu0der, hu00, hpu00, hu0iter, hu0C2⟩ :=
    exists_solution hVext hfext hMV hMV0 (0, 0)
  have hw1 : w 1 ≠ 0 := by
    intro h
    have hzero := eq_zero_of_homogeneous hVext_nonneg hVext w pw hwcont hpwcont hwder
      (fun t ht => by
        have h' := hpwder t
        change HasDerivAt pw (Vext t * w t - 0) t at h'
        rwa [sub_zero] at h') hw0 h
    have h0 := (hzero 0 (by norm_num)).2
    rw [hpw0] at h0
    exact one_ne_zero h0
  set a : ℝ := -(u₀ 1) / w 1 with ha_def
  obtain ⟨ua, pa, huacont, hpacont, huader, hpader, hua0, hpa0, huaiter, huaC2⟩ :=
    exists_solution hVext hfext hMV hMV0 (0, a)
  set usum : ℝ → ℝ := fun t => u₀ t + a * w t with husum_def
  set psum : ℝ → ℝ := fun t => pu₀ t + a * pw t with hpsum_def
  have husum_der : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt usum (psum t) t := by
    intro t ht
    show HasDerivAt (fun t => u₀ t + a * w t) (pu₀ t + a * pw t) t
    exact (hu0der t ht).add ((hwder t ht).const_mul a)
  have hpsum_der : ∀ t, HasDerivAt psum (Vext t * usum t - fext t) t := by
    intro t
    show HasDerivAt (fun t => pu₀ t + a * pw t) (Vext t * (u₀ t + a * w t) - fext t) t
    have h := (hpu0der t).add ((hpwder t).const_mul a)
    change HasDerivAt (fun y => pu₀ y + a * pw y)
      ((Vext t * u₀ t - fext t) + a * (Vext t * w t - 0)) t at h
    rw [sub_zero] at h
    convert h using 1
    ring
  have hsum0 : usum 0 = (0, a).1 ∧ psum 0 = (0, a).2 := by
    refine ⟨?_, ?_⟩
    · show u₀ 0 + a * w 0 = 0
      rw [hu00, hw0]
      simp
    · show pu₀ 0 + a * pw 0 = a
      rw [hpu00, hpw0]
      simp
  have hY₁cont : ContinuousOn (fun s => (ua s, pa s)) (Set.Icc (0 : ℝ) 1) :=
    (huacont.prodMk hpacont).continuousOn
  have hY₂cont : ContinuousOn (fun s => (usum s, psum s)) (Set.Icc (0 : ℝ) 1) :=
    ((show Continuous (fun t => u₀ t + a * w t) from hu0cont.add (hwcont.const_mul a)).prodMk
      (show Continuous (fun t => pu₀ t + a * pw t) from
        hpu0cont.add (hpwcont.const_mul a))).continuousOn
  have hEq : Set.EqOn (fun s => (ua s, pa s)) (fun s => (usum s, psum s))
      (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := sys Vext fext)
      (s := fun _ => Set.univ) (K := K)
      (fun t _ => (lipschitz_sys hMV hMV0 hK t).lipschitzOnWith)
      hY₁cont
      (fun t ht =>
        (HasDerivAt.prodMk (huader t ⟨ht.1, ht.2.le⟩) (hpader t)).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      hY₂cont
      (fun t ht =>
        (HasDerivAt.prodMk (husum_der t ⟨ht.1, ht.2.le⟩) (hpsum_der t)).hasDerivWithinAt)
      (fun _ _ => Set.mem_univ _)
      (Prod.ext (hua0.trans hsum0.1.symm) (hpa0.trans hsum0.2.symm))
  have hua1 : ua 1 = 0 := by
    have h := hEq (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    have h1 : ua 1 = usum 1 := congrArg Prod.fst h
    rw [h1]
    show u₀ 1 + a * w 1 = 0
    rw [ha_def, div_mul_cancel₀ _ hw1]
    ring
  refine ⟨ua, huaC2, ?_, hua0, hua1⟩
  intro x hx
  rw [huaiter x hx, hVext_mem x hx, hfext_mem x hx]
  ring

end MathlibExt.Analysis.ODE.SturmLiouvilleExistence
