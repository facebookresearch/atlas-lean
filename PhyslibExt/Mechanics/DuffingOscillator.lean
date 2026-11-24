/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.LaSalle
public import Mathlib.Analysis.ODE.Basic
import MathlibExt.Analysis.ODE.MaximalSolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Hardening Duffing oscillator: compact energy sublevels and asymptotic stability

The damped hardening Duffing oscillator with mass `m > 0`, viscous damping `c > 0`, linear
stiffness `k > 0` and hardening coefficient `β > 0` is, on the phase plane `(x, v)`,

  `x' = v`,  `m v' = -c v - k x - β x ^ 3`.

Its mechanical energy is `V = m v ^ 2 / 2 + k x ^ 2 / 2 + β x ^ 4 / 4`.

## i. Overview

The energy dominates the quadratic energy `m v ^ 2 / 2 + k x ^ 2 / 2`, vanishes only at the
origin and has compact sublevel sets. Along the flow `V' = -c v ^ 2 ≤ 0`, so every sublevel set
is forward invariant: every initial state has a forward solution on `[0, ∞)` that stays in its
sublevel set (global continuation, through the existing maximal-solution theorem). On
`{V' = 0} = {v = 0}` the only forward-invariant part is the origin, so the existing LaSalle
invariance principle gives convergence of every forward solution to `(0, 0)`; together with the
Lyapunov stability of the origin this is global asymptotic stability. The energy derivative
alone gives no exponential decay rate: `V' = 0` wherever `v = 0`.

The hypotheses matter: with `c = 0` the energy is conserved and a displaced oscillator does not
converge; with `β < 0` the energy is not coercive (its sublevel sets are unbounded) and nonzero
equilibria appear. Parameters and initial data are model inputs.

## ii. Key results

- `quadratic_le_duffingEnergy`, `duffingEnergy_eq_zero_iff`, `isCompact_duffingSublevel`: the
  energy is coercive, vanishes only at the origin and has compact sublevel sets.
- `hasFDerivAt_duffingEnergy`, `duffingEnergy_orbital`, `duffingEnergy_antitoneOn`: the energy
  derivative, the orbital rate `V' = -c v ^ 2`, and monotone energy along forward solutions.
- `not_exponential_energy_decay`: no bound `V' ≤ -α V` with `α > 0` holds.
- `isForwardInvariant_duffingSublevel`: every energy sublevel set is forward invariant (global
  continuation).
- `largestForwardInvariantSubset_subset_zero`: the forward-invariant part of `{V' = 0}` is at
  most the origin.
- `tendsto_zero_of_isIntegralCurveOn`: every forward solution tends to the origin.
- `stable_zero`: the origin is Lyapunov stable.

## iii. Table of contents

- A. Model
- B. Coercive energy and compact sublevels
- C. Energy derivative
- D. Global continuation in a sublevel
- E. LaSalle convergence and asymptotic stability

## iv. References

- A. H. Nayfeh and D. T. Mook, *Nonlinear Oscillations*, Wiley (1979), Chapter 4 (the Duffing
  equation).
- H. K. Khalil, *Nonlinear Systems*, 3rd edition, Prentice Hall (2002), Section 4.1
  (Theorem 4.1, Lyapunov stability) and Section 4.2 (Theorem 4.4, LaSalle's invariance
  principle).
- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, AMS (2012), Sections 2.4
  and 2.5 (maximal solutions and the exit from compact sets).
- `MathlibExt.Analysis.ODE.LaSalle`: LaSalle's invariance principle.
- `MathlibExt.Analysis.ODE.MaximalSolution`: maximal solutions eventually leave every compact
  set.
-/

@[expose] public section

namespace Mechanics.DuffingOscillator

open Filter Set Topology
open MathlibExt.Analysis.ODE (IsForwardInvariant largestForwardInvariantSubset)

/-! ## A. Model -/

/-- The hardening Duffing field on the phase plane: `(x, v) ↦ (v, -(c v + k x + β x ^ 3) / m)`.
With `u / 0 = 0` the second component is `0` at `m = 0`. -/
noncomputable def duffingField (m c k β : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, -(c * p.2 + k * p.1 + β * p.1 ^ 3) / m)

/-- The mechanical energy `m v ^ 2 / 2 + k x ^ 2 / 2 + β x ^ 4 / 4`. -/
noncomputable def duffingEnergy (m k β : ℝ) (p : ℝ × ℝ) : ℝ :=
  m * p.2 ^ 2 / 2 + k * p.1 ^ 2 / 2 + β * p.1 ^ 4 / 4

/-- The derivative of the energy at `p`: `(δx, δv) ↦ (k x + β x ^ 3) δx + m v δv`. -/
noncomputable def duffingEnergyDeriv (m k β : ℝ) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (k * p.1 + β * p.1 ^ 3) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (m * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ

/-! ## B. Coercive energy and compact sublevels -/

/-- The hardening quartic only adds energy: for `β > 0` the energy dominates
`m v ^ 2 / 2 + k x ^ 2 / 2`. -/
lemma quadratic_le_duffingEnergy {m k β : ℝ} (hβ : 0 < β) (p : ℝ × ℝ) :
    m * p.2 ^ 2 / 2 + k * p.1 ^ 2 / 2 ≤ duffingEnergy m k β p := by
  unfold duffingEnergy
  have : 0 ≤ β * p.1 ^ 4 / 4 := by positivity
  linarith

/-- For `m, k, β > 0` the energy vanishes only at the origin. -/
lemma duffingEnergy_eq_zero_iff {m k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β)
    (p : ℝ × ℝ) : duffingEnergy m k β p = 0 ↔ p = 0 := by
  constructor
  · intro h
    unfold duffingEnergy at h
    have a1 : 0 ≤ m * p.2 ^ 2 / 2 := by positivity
    have a2 : 0 ≤ k * p.1 ^ 2 / 2 := by positivity
    have a3 : 0 ≤ β * p.1 ^ 4 / 4 := by positivity
    have hv : p.2 = 0 := by
      have h2 : p.2 ^ 2 = 0 :=
        (mul_eq_zero.mp (show m * p.2 ^ 2 = 0 by linarith)).resolve_left hm.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    have hx : p.1 = 0 := by
      have h2 : p.1 ^ 2 = 0 :=
        (mul_eq_zero.mp (show k * p.1 ^ 2 = 0 by linarith)).resolve_left hk.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    exact Prod.ext hx hv
  · rintro rfl
    simp [duffingEnergy]

/-- For `m, k, β > 0` every energy sublevel set is compact. -/
lemma isCompact_duffingSublevel {m k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β) (r : ℝ) :
    IsCompact {p : ℝ × ℝ | duffingEnergy m k β p ≤ r} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by unfold duffingEnergy; fun_prop) continuous_const
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨2 * |r| / k + 2 * |r| / m + 1, fun p hp => ?_⟩
    have hp' : duffingEnergy m k β p ≤ r := hp
    have hq := quadratic_le_duffingEnergy (m := m) (k := k) hβ p
    have a1 : 0 ≤ m * p.2 ^ 2 / 2 := by positivity
    have a2 : 0 ≤ k * p.1 ^ 2 / 2 := by positivity
    have hr : r ≤ |r| := le_abs_self r
    have hx2 : p.1 ^ 2 ≤ 2 * |r| / k := by
      rw [le_div_iff₀ hk]
      nlinarith
    have hv2 : p.2 ^ 2 ≤ 2 * |r| / m := by
      rw [le_div_iff₀ hm]
      nlinarith
    have habs : ∀ a : ℝ, |a| ≤ a ^ 2 + 1 := fun a => by
      nlinarith [abs_nonneg a, sq_abs a, sq_nonneg (|a| - 1)]
    have e1 : 0 ≤ 2 * |r| / m := by positivity
    have e2 : 0 ≤ 2 * |r| / k := by positivity
    have h1 : |p.1| ≤ 2 * |r| / k + 2 * |r| / m + 1 := by
      have := habs p.1
      linarith
    have h2 : |p.2| ≤ 2 * |r| / k + 2 * |r| / m + 1 := by
      have := habs p.2
      linarith
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_le h1 h2

/-! ## C. Energy derivative -/

/-- The energy has derivative `duffingEnergyDeriv` at every state. -/
lemma hasFDerivAt_duffingEnergy (m k β : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (duffingEnergy m k β) (duffingEnergyDeriv m k β p) p := by
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hv : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have a1 : HasFDerivAt (fun q : ℝ × ℝ => q.2 ^ 2) _ p := hv.pow 2
  have a2 : HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 2) _ p := hx.pow 2
  have a3 : HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 4) _ p := hx.pow 4
  have b1 : HasFDerivAt (fun q : ℝ × ℝ => m / 2 * q.2 ^ 2) _ p := a1.const_mul (m / 2)
  have b2 : HasFDerivAt (fun q : ℝ × ℝ => k / 2 * q.1 ^ 2) _ p := a2.const_mul (k / 2)
  have b3 : HasFDerivAt (fun q : ℝ × ℝ => β / 4 * q.1 ^ 4) _ p := a3.const_mul (β / 4)
  have h : HasFDerivAt (fun q : ℝ × ℝ => m / 2 * q.2 ^ 2 + k / 2 * q.1 ^ 2 + β / 4 * q.1 ^ 4)
      _ p := (b1.add b2).add b3
  have hfun : duffingEnergy m k β =
      fun q : ℝ × ℝ => m / 2 * q.2 ^ 2 + k / 2 * q.1 ^ 2 + β / 4 * q.1 ^ 4 := by
    funext q
    unfold duffingEnergy
    ring
  rw [hfun]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [duffingEnergyDeriv]
  ring

/-- For `m > 0`, along the field the energy changes at the rate `V' = -c v ^ 2`. -/
lemma duffingEnergy_orbital {m : ℝ} (hm : 0 < m) (c k β : ℝ) (p : ℝ × ℝ) :
    duffingEnergyDeriv m k β p (duffingField m c k β p) = -c * p.2 ^ 2 := by
  simp [duffingEnergyDeriv, duffingField]
  field_simp
  ring

/-- For `m > 0` and `c ≥ 0` the energy is nonincreasing along every forward solution. -/
lemma duffingEnergy_antitoneOn {m c k β : ℝ} (hm : 0 < m) (hc : 0 ≤ c) {γ : ℝ → ℝ × ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ => duffingField m c k β) (Ici 0)) :
    AntitoneOn (fun t => duffingEnergy m k β (γ t)) (Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => duffingEnergyDeriv m k β (γ t) (duffingField m c k β (γ t))) (convex_Ici 0)
    (fun t ht => (hasFDerivAt_duffingEnergy m k β (γ t)).continuousAt.comp_continuousWithinAt
      (hγ.continuousWithinAt ht)) (fun t ht => ?_) (fun t _ => ?_)
  · rw [interior_Ici] at ht
    exact ((hasFDerivAt_duffingEnergy m k β (γ t)).comp_hasDerivWithinAt t
      (hγ t (Set.mem_Ici.mpr (le_of_lt ht)))).mono interior_subset
  · rw [duffingEnergy_orbital hm]
    nlinarith [sq_nonneg (γ t).2]

/-- The energy derivative gives no exponential decay rate: for `m, k, β > 0`, no `α > 0` has
`V' ≤ -α V` everywhere (at `v = 0`, `x ≠ 0` the left side is `0` and the right side negative). -/
lemma not_exponential_energy_decay {m k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β) (c : ℝ) :
    ¬ ∃ α > 0, ∀ p : ℝ × ℝ,
      duffingEnergyDeriv m k β p (duffingField m c k β p) ≤ -α * duffingEnergy m k β p := by
  rintro ⟨α, hα, h⟩
  have h1 := h (1, 0)
  rw [duffingEnergy_orbital hm] at h1
  simp [duffingEnergy] at h1
  nlinarith [mul_pos hα hk, mul_pos hα hβ]

/-! ## D. Global continuation in a sublevel -/

/-- For `m, k, β > 0` and `c ≥ 0` every energy sublevel set is forward invariant: through each of
its points there is a forward solution on `[0, ∞)` that stays in it. -/
lemma isForwardInvariant_duffingSublevel {m c k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β)
    (hc : 0 ≤ c) (r : ℝ) :
    IsForwardInvariant (duffingField m c k β) {p : ℝ × ℝ | duffingEnergy m k β p ≤ r} := by
  intro p hp
  have hp' : duffingEnergy m k β p ≤ r := hp
  have hfC : ContDiff ℝ 1 (duffingField m c k β) := by
    unfold duffingField
    fun_prop
  have hlip : ∀ q ∈ (Set.univ : Set (ℝ × (ℝ × ℝ))), ∃ C : NNReal, ∃ s ∈ 𝓝 q,
      ∀ t : ℝ, ∀ x y : ℝ × ℝ, (t, x) ∈ s ∩ Set.univ → (t, y) ∈ s ∩ Set.univ →
        dist (duffingField m c k β (t, x).2) (duffingField m c k β (t, y).2) ≤ C * dist x y := by
    intro q _
    obtain ⟨C, s, hs, hC⟩ := hfC.locallyLipschitz q.2
    refine ⟨C, Prod.snd ⁻¹' s, continuous_snd.continuousAt.preimage_mem_nhds hs, ?_⟩
    intro t x y hx hy
    exact hC.dist_le_mul x hx.1 y hy.1
  obtain ⟨I, x, hx0, -, h0I, hIcc, hsol, hexit⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_maximal_solution_exit_compact
      Set.univ (fun q => duffingField m c k β q.2) 0 p isOpen_univ (Set.mem_univ _)
      (hfC.continuous.comp continuous_snd).continuousOn hlip
  have hderiv : ∀ t ∈ I, HasDerivAt x (duffingField m c k β (x t)) t := fun t ht => (hsol t ht).2
  have hen : ∀ t ∈ I, 0 ≤ t → duffingEnergy m k β (x t) ≤ duffingEnergy m k β p := by
    intro t ht ht0
    have hsub : Set.Icc 0 t ⊆ I := hIcc 0 h0I t ht
    have hanti : AntitoneOn (fun s => duffingEnergy m k β (x s)) (Set.Icc 0 t) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun s => duffingEnergyDeriv m k β (x s) (duffingField m c k β (x s)))
        (convex_Icc 0 t) (fun s hs => ?_) (fun s hs => ?_) (fun s _ => ?_)
      · exact ((hasFDerivAt_duffingEnergy m k β (x s)).comp_hasDerivAt s
          (hderiv s (hsub hs))).continuousAt.continuousWithinAt
      · exact ((hasFDerivAt_duffingEnergy m k β (x s)).comp_hasDerivAt s
          (hderiv s (hsub (interior_subset hs)))).hasDerivWithinAt
      · rw [duffingEnergy_orbital hm]
        nlinarith [sq_nonneg (x s).2]
    have := hanti ⟨le_refl 0, ht0⟩ ⟨ht0, le_refl t⟩ ht0
    simpa [hx0] using this
  have hS : IsCompact {q : ℝ × ℝ | duffingEnergy m k β q ≤ r} :=
    isCompact_duffingSublevel hm hk hβ r
  have hall : ∀ T, 0 ≤ T → T ∈ I := by
    intro T hT
    by_contra hTI
    have hlt : ∀ t ∈ I, t < T := by
      intro t ht
      by_contra hle
      exact hTI (hIcc 0 h0I t ht ⟨hT, not_lt.mp hle⟩)
    obtain ⟨⟨c₀, hc₀I, hc₀⟩, -⟩ := hexit (Set.Icc 0 T ×ˢ {q | duffingEnergy m k β q ≤ r})
      (isCompact_Icc.prod hS) (Set.subset_univ _)
    have htI : max c₀ 0 ∈ I := by
      rcases le_total c₀ 0 with h | h
      · rw [max_eq_right h]
        exact h0I
      · rw [max_eq_left h]
        exact hc₀I
    apply hc₀ (max c₀ 0) htI (le_max_left _ _)
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨⟨le_max_right _ _, (hlt _ htI).le⟩, (hen _ htI (le_max_right _ _)).trans hp'⟩
  exact ⟨x, fun t ht => (hderiv t (hall t ht)).hasDerivWithinAt, hx0,
    fun t ht => (hen t (hall t ht) ht).trans hp'⟩

/-! ## E. LaSalle convergence and asymptotic stability -/

/-- For `m, k, β, c > 0`, on `{V' = 0}` (that is `v = 0`) the largest forward-invariant subset is
at most the origin, inside any set `K`. -/
lemma largestForwardInvariantSubset_subset_zero {m c k β : ℝ} (hm : 0 < m) (hk : 0 < k)
    (hβ : 0 < β) (hc : 0 < c) (K : Set (ℝ × ℝ)) :
    largestForwardInvariantSubset (duffingField m c k β)
        {p | p ∈ K ∧ duffingEnergyDeriv m k β p (duffingField m c k β p) = 0} ⊆ {0} := by
  intro y hy
  simp only [largestForwardInvariantSubset, Set.mem_sUnion, Set.mem_ofPred_eq] at hy
  obtain ⟨A, ⟨hAZ, hAinv⟩, hyA⟩ := hy
  obtain ⟨φ, hφ, hφ0, hφA⟩ := hAinv y hyA
  have hv : ∀ t, 0 ≤ t → (φ t).2 = 0 := by
    intro t ht
    have h := (hAZ (hφA t ht)).2
    rw [duffingEnergy_orbital hm] at h
    have h2 : (φ t).2 ^ 2 = 0 :=
      (mul_eq_zero.mp (show c * (φ t).2 ^ 2 = 0 by linarith)).resolve_left hc.ne'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hsnd : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (φ 0) :=
    hasFDerivAt_snd
  have hd : HasDerivWithinAt (fun t => (φ t).2) (duffingField m c k β (φ 0)).2 (Ici 0) 0 :=
    hsnd.comp_hasDerivWithinAt 0 (hφ 0 (Set.mem_Ici.mpr (le_refl 0)))
  have hd0 : HasDerivWithinAt (fun t => (φ t).2) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Ici 0) (0 : ℝ)).congr (fun t ht => hv t ht) (hv 0 le_rfl)
  have heq := (uniqueDiffWithinAt_Ici 0).eq_deriv _ hd hd0
  have hy2 : y.2 = 0 := by
    rw [← hφ0]
    exact hv 0 le_rfl
  simp only [duffingField] at heq
  rw [hφ0, hy2] at heq
  have hnum : -(c * 0 + k * y.1 + β * y.1 ^ 3) = 0 :=
    (div_eq_zero_iff.mp heq).resolve_right hm.ne'
  have h2 : y.1 * (k + β * y.1 ^ 2) = 0 := by linear_combination -hnum
  have hx : y.1 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · nlinarith [sq_nonneg y.1, mul_nonneg hβ.le (sq_nonneg y.1)]
  exact Prod.ext hx hy2

/-- LaSalle convergence: for `m, k, β, c > 0`, every forward solution tends to the origin. -/
lemma tendsto_zero_of_isIntegralCurveOn {m c k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β)
    (hc : 0 < c) {γ : ℝ → ℝ × ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ => duffingField m c k β) (Ici 0)) :
    Tendsto γ atTop (𝓝 0) := by
  set K := {q : ℝ × ℝ | duffingEnergy m k β q ≤ duffingEnergy m k β (γ 0)} with hK
  have hKc : IsCompact K := isCompact_duffingSublevel hm hk hβ _
  have hfC : ContDiff ℝ 1 (duffingField m c k β) := by
    unfold duffingField
    fun_prop
  obtain ⟨L, hL⟩ := hfC.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hKc
  have hinv := isForwardInvariant_duffingSublevel hm hk hβ hc.le (duffingEnergy m k β (γ 0))
  have hanti := duffingEnergy_antitoneOn hm hc.le hγ
  have hγK : ∀ t, 0 ≤ t → γ t ∈ K := fun t ht =>
    hanti (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
  exact MathlibExt.Analysis.ODE.tendsto_of_lasalle hKc hL hinv hγ hγK
    (fun q _ => hasFDerivAt_duffingEnergy m k β q)
    (fun q _ => by rw [duffingEnergy_orbital hm]; nlinarith [sq_nonneg q.2])
    (largestForwardInvariantSubset_subset_zero hm hk hβ hc K)

/-- Lyapunov stability of the origin: for `m, k, β > 0` and `c ≥ 0`, forward solutions starting
close to the origin stay close to it (in the max norm of `ℝ × ℝ`). -/
lemma stable_zero {m c k β : ℝ} (hm : 0 < m) (hk : 0 < k) (hβ : 0 < β) (hc : 0 ≤ c) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ γ : ℝ → ℝ × ℝ, IsIntegralCurveOn γ (fun _ => duffingField m c k β) (Ici 0) →
      ‖γ 0‖ < δ → ∀ t, 0 ≤ t → ‖γ t‖ < ε := by
  have hapos : 0 < min m k / 2 := by
    have := lt_min hm hk
    positivity
  set a := min m k / 2 with ha
  have hcoer : ∀ q : ℝ × ℝ, a * ‖q‖ ^ 2 ≤ duffingEnergy m k β q := by
    intro q
    have hq := quadratic_le_duffingEnergy (m := m) (k := k) hβ q
    have hn : ‖q‖ = max |q.1| |q.2| := by
      rw [Prod.norm_def]
      simp [Real.norm_eq_abs]
    have hmk1 : min m k ≤ m := min_le_left _ _
    have hmk2 : min m k ≤ k := min_le_right _ _
    rcases le_total |q.1| |q.2| with h | h
    · rw [hn, max_eq_right h, sq_abs, ha]
      nlinarith [sq_nonneg q.1, sq_nonneg q.2, mul_le_mul_of_nonneg_right hmk1 (sq_nonneg q.2),
        mul_nonneg hk.le (sq_nonneg q.1)]
    · rw [hn, max_eq_left h, sq_abs, ha]
      nlinarith [sq_nonneg q.1, sq_nonneg q.2, mul_le_mul_of_nonneg_right hmk2 (sq_nonneg q.1),
        mul_nonneg hm.le (sq_nonneg q.2)]
  have hVc : Continuous (duffingEnergy m k β) := by
    unfold duffingEnergy
    fun_prop
  have hV0 : duffingEnergy m k β 0 = 0 := by simp [duffingEnergy]
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousAt_iff.mp hVc.continuousAt (a * ε ^ 2) (by positivity)
  refine ⟨δ, hδ, fun γ hγ hγ0 t ht => ?_⟩
  have hanti := duffingEnergy_antitoneOn hm hc hγ
  have h1 : duffingEnergy m k β (γ t) ≤ duffingEnergy m k β (γ 0) :=
    hanti (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr ht) ht
  have h2 : duffingEnergy m k β (γ 0) < a * ε ^ 2 := by
    have := hδV (show dist (γ 0) 0 < δ by rwa [dist_zero_right])
    rw [hV0, Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have h3 := hcoer (γ t)
  have h4 : ‖γ t‖ ^ 2 < ε ^ 2 := by
    have : a * ‖γ t‖ ^ 2 < a * ε ^ 2 := by linarith
    exact lt_of_mul_lt_mul_left this hapos.le
  nlinarith [norm_nonneg (γ t)]

end Mechanics.DuffingOscillator
