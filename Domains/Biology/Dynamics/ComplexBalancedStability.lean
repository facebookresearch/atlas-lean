/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.ComplexBalanced
import MathlibExt.Analysis.ODE.MaximalSolution
import MathlibExt.Dynamics.PolynomialNetworks.MassAction
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Local stability of complex-balanced mass-action systems

A reaction network has finite species `S` and reactions `ρ`, positive rate constants `k`,
and a positive complex-balanced point `cstar`. Its mass-action vector field acts on `S → ℝ`,
with the sup norm; reaction vectors span its stoichiometric subspace.

For every positive equilibrium `xstar`, `exists_solution_of_near` gives global forward
solutions from sufficiently nearby initial states in its stoichiometric compatibility class.
The theorem `stable` gives Lyapunov stability, and `attractive` gives convergence to `xstar`
for sufficiently nearby solutions in that class. Solutions have two-sided derivatives at
all nonnegative times, including zero.

Existence and stability also hold without the class restriction
(`exists_solution_of_near_all_classes`, `stable_all_classes`); attractivity to the fixed
equilibrium needs that restriction. These are local results: global convergence from arbitrary
positive initial states is not claimed.

Global existence applies `MaximalSolutionWanted.ode_global_exists_of_global_lipschitz` to the
field clipped to a closed ball of positive states; the pseudo-Helmholtz energy keeps solutions
that start near the equilibrium inside that ball, where the clipped field is the original one.

## References

* M. Feinberg (1987), Chem. Eng. Sci. 42, 2229–2268: Section 5.2 defines asymptotic stability
  relative to a stoichiometric compatibility class; see also Theorem 6.1.1(iii).
* F. Horn and R. Jackson (1972), Arch. Rational Mech. Anal. 47, 81–116.
-/

public section

open MathlibExt.Biology.Dynamics.ComplexBalanced
open ReactionNetwork
open Finset Set Filter
open scoped Topology NNReal

namespace Domains.Biology.Dynamics.ComplexBalancedStability

private noncomputable def energy {S : Type*} [Fintype S] (a z : S → ℝ) : ℝ :=
  pseudoHelmholtz a z - pseudoHelmholtz a a

private theorem energy_self {S : Type*} [Fintype S] (a : S → ℝ) : energy a a = 0 :=
  sub_self _

private theorem energy_eq_sum {S : Type*} [Fintype S] (a z : S → ℝ) :
    energy a z = ∑ s, (z s * (Real.log (z s) - Real.log (a s) - 1) + a s) := by
  simp only [energy, pseudoHelmholtz, sub_self, zero_sub, mul_neg, mul_one,
    Finset.sum_neg_distrib, sub_neg_eq_add, Finset.sum_add_distrib]

private theorem scalar_energy_nonneg {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    0 ≤ z * (Real.log z - Real.log a - 1) + a := by
  have h := Real.self_sub_one_le_mul_log (x := z / a) (by positivity)
  rw [Real.log_div hz.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  field_simp at hm
  nlinarith

private theorem scalar_energy_pos {a z : ℝ} (ha : 0 < a) (hz : 0 < z) (hne : z ≠ a) :
    0 < z * (Real.log z - Real.log a - 1) + a := by
  have hn : z / a ≠ 1 := by
    intro h
    apply hne
    exact (div_eq_one_iff_eq ha.ne').mp h
  have h := Real.self_sub_one_lt_mul_log (x := z / a) (by positivity) hn
  rw [Real.log_div hz.ne' ha.ne'] at h
  have hm := mul_lt_mul_of_pos_left h ha
  field_simp at hm
  nlinarith

private theorem energy_nonneg {S : Type*} [Fintype S] {a z : S → ℝ}
    (ha : ∀ s, 0 < a s) (hz : ∀ s, 0 < z s) : 0 ≤ energy a z := by
  rw [energy_eq_sum]
  exact Finset.sum_nonneg fun s _ => scalar_energy_nonneg (ha s) (hz s)

private theorem energy_pos {S : Type*} [Fintype S] {a z : S → ℝ}
    (ha : ∀ s, 0 < a s) (hz : ∀ s, 0 < z s) (hne : z ≠ a) : 0 < energy a z := by
  classical
  obtain ⟨s, hs⟩ : ∃ s, z s ≠ a s := by
    by_contra h
    apply hne
    exact funext fun s => by simpa using not_exists.mp h s
  rw [energy_eq_sum]
  exact Finset.sum_pos' (fun s _ => scalar_energy_nonneg (ha s) (hz s))
    ⟨s, Finset.mem_univ s, scalar_energy_pos (ha s) (hz s) hs⟩

private theorem solution_sub_mem {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) {x : ℝ → S → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
    {t : ℝ} (ht : 0 ≤ t) : x t - x 0 ∈ N.stoichiometricSubspace := by
  let W := N.stoichiometricSubspace
  let : NormedAddCommGroup ((S → ℝ) ⧸ W) :=
    Submodule.Quotient.normedAddCommGroup (S := W) (hS := W.isClosed_of_finiteDimensional)
  let q := W.mkQ.toContinuousLinearMap
  have hd (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt (fun v => q (x v)) (q (N.massActionField k (x u))) u :=
    q.hasFDerivAt.comp_hasDerivAt u (hx u hu)
  have hz (u : ℝ) : q (N.massActionField k (x u)) = 0 := by
    change W.mkQ (N.massActionField k (x u)) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact N.massActionField_mem k (x u)
  have hd0 (u : ℝ) (hu : 0 ≤ u) := (hd u hu).congr_deriv (hz u)
  have he : q (x t) = q (x 0) :=
    eq_of_has_deriv_right_eq
      (fun u hu => (hd0 u hu.1).hasDerivWithinAt)
      (fun u _ => (hasDerivAt_const u (q (x 0))).hasDerivWithinAt)
      (fun u hu => (hd0 u hu.1).continuousAt.continuousWithinAt)
      continuousOn_const rfl t ⟨ht, le_rfl⟩
  have hz : W.mkQ (x t - x 0) = 0 := by
    change q (x t - x 0) = 0
    rw [map_sub, he, sub_self]
  rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz

private theorem positive_closedBall {S : Type*} [Fintype S] {a : S → ℝ}
    (ha : ∀ s, 0 < a s) :
    ∃ r > 0, ∀ z : S → ℝ, ‖z - a‖ ≤ r → ∀ s, 0 < z s := by
  let r := 1 / (1 + ∑ s, 1 / a s)
  have hsum : 0 ≤ ∑ s, 1 / a s :=
    Finset.sum_nonneg fun s _ => (one_div_pos.mpr (ha s)).le
  have hr : 0 < r := by dsimp [r]; positivity
  have hra : ∀ s, r ≤ a s := by
    intro s
    have h1 : 1 / a s ≤ ∑ s, 1 / a s :=
      Finset.single_le_sum (f := fun s => 1 / a s)
        (fun s _ => (one_div_pos.mpr (ha s)).le) (Finset.mem_univ s)
    dsimp [r]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (ha s)] at h1
    nlinarith
  refine ⟨r / 2, by positivity, fun z hz s => ?_⟩
  have hc := (norm_le_pi_norm (z - a) s).trans hz
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_le] at hc
  have := hra s
  nlinarith

private theorem energy_continuousAt {S : Type*} [Fintype S] (a : S → ℝ) {z : S → ℝ}
    (hz : ∀ s, 0 < z s) : ContinuousAt (energy a) z := by
  have hc (s : S) : ContinuousAt (fun w : S → ℝ => w s) z :=
    (continuous_apply s).continuousAt
  have hg : ContinuousAt (fun w : S → ℝ =>
      ∑ s, w s * (Real.log (w s) - Real.log (a s) - 1)) z :=
    tendsto_finsetSum Finset.univ fun s _ =>
      (hc s).mul (((hc s).log (hz s).ne').sub continuousAt_const |>.sub continuousAt_const)
  exact hg.sub continuousAt_const

private theorem energy_boundary_lower {S : Type*} [Fintype S] {a : S → ℝ}
    (ha : ∀ s, 0 < a s) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ r → ∀ s, 0 < z s) :
    ∃ b > 0, ∀ z : S → ℝ, ‖z - a‖ = r → b ≤ energy a z := by
  classical
  by_cases hn : (Metric.sphere a r).Nonempty
  · obtain ⟨z, hz, hm⟩ := (isCompact_sphere a r).exists_isMinOn hn
      (fun z hz => (energy_continuousAt a (hpos z (by
        exact (show ‖z - a‖ = r by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz).le))).continuousWithinAt)
    have hnorm : ‖z - a‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hne : z ≠ a := by
      intro h
      subst z
      simp only [sub_self, norm_zero] at hnorm
      linarith
    exact ⟨energy a z, energy_pos ha (hpos z hnorm.le) hne,
      fun w hw => hm (by simpa [Metric.mem_sphere, dist_eq_norm] using hw)⟩
  · exact ⟨1, zero_lt_one, fun z hz => False.elim
      (hn ⟨z, by simpa [Metric.mem_sphere, dist_eq_norm] using hz⟩)⟩

private theorem energy_trapping_of_continuousOn {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    {r b : ℝ}
    (hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ r → ∀ s, 0 < z s)
    (hboundary : ∀ z : S → ℝ, ‖z - a‖ = r → b ≤ energy a z)
    {x : ℝ → S → ℝ}
    (hxc : ContinuousOn x (Ici 0))
    (hx : ∀ t, 0 ≤ t → ‖x t - a‖ ≤ r → HasDerivAt x (N.massActionField k (x t)) t)
    (hnear : ‖x 0 - a‖ < r) (hsmall : energy a (x 0) < b) :
    ∀ t, 0 ≤ t → ‖x t - a‖ < r := by
  intro T hT
  by_contra hbad
  have hlarge : r ≤ ‖x T - a‖ := le_of_not_gt hbad
  let f : ℝ → ℝ := fun t => ‖x t - a‖
  have hcont : ContinuousOn f (Icc 0 T) := fun t ht =>
    ((hxc t ht.1).sub continuousWithinAt_const).norm.mono (Icc_subset_Ici_self)
  obtain ⟨u, hu, hueq⟩ := intermediate_value_Icc hT hcont ⟨hnear.le, hlarge⟩
  let K := Icc 0 T ∩ f ⁻¹' {r}
  have hK : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨τ, hτ, hmin⟩ := hK.exists_isMinOn ⟨u, hu, hueq⟩ continuousOn_id
  have hτ0 : 0 ≤ τ := hτ.1.1
  have hτT : τ ≤ T := hτ.1.2
  have hτr : f τ = r := hτ.2
  have hbefore : ∀ v, 0 ≤ v → v < τ → f v < r := by
    intro v hv hvτ
    by_contra hvbad
    have hvT : v ≤ T := hvτ.le.trans hτT
    obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc hv
      (hcont.mono (Icc_subset_Icc le_rfl hvT)) ⟨hnear.le, le_of_not_gt hvbad⟩
    have hm : τ ≤ w := hmin ⟨⟨hw.1, hw.2.trans hvT⟩, hweq⟩
    linarith [hw.2]
  have hnorm : ∀ v ∈ Icc 0 τ, ‖x v - a‖ ≤ r := by
    intro v hv
    rcases lt_or_eq_of_le hv.2 with hlt | rfl
    · exact (hbefore v hv.1 hlt).le
    · exact hτr.le
  have hd : ∀ v ∈ Icc 0 τ,
      HasDerivAt (fun t => energy a (x t)) (N.helmholtzRate k a (x v)) v := by
    intro v hv
    exact (N.hasDerivAt_pseudoHelmholtz a (hx v hv.1 (hnorm v hv))
      (hpos (x v) (hnorm v hv))).sub_const _
  have hmono : AntitoneOn (fun t => energy a (x t)) (Icc 0 τ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 τ)
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
    · exact fun v hv => (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      have hmem : v ∈ Icc 0 τ := interior_subset hv
      rw [(hd v hmem).deriv]
      exact N.helmholtzRate_nonpos hk ha hcb (hpos (x v) (hnorm v hmem))
  have hle := hmono ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0
  have hb := hboundary (x τ) hτr
  linarith

private theorem energy_trapping {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    {r b : ℝ}
    (hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ r → ∀ s, 0 < z s)
    (hboundary : ∀ z : S → ℝ, ‖z - a‖ = r → b ≤ energy a z)
    {x : ℝ → S → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
    (hnear : ‖x 0 - a‖ < r) (hsmall : energy a (x 0) < b) :
    ∀ t, 0 ≤ t → ‖x t - a‖ < r :=
  energy_trapping_of_continuousOn N hk ha hcb hpos hboundary
    (fun t ht => (hx t ht).continuousAt.continuousWithinAt)
    (fun t ht _ => hx t ht) hnear hsmall

/-- **Lyapunov stability across stoichiometric classes.** Let `a` be a positive complex-balanced
point, hence an equilibrium, of a mass-action system with positive rate constants. For every
`ε > 0` there is `η > 0` such that every solution on `[0, ∞)` that starts within `η` of `a`, in
any stoichiometric compatibility class, stays within `ε` of `a` for all `t ≥ 0`. Distances are
sup-norm distances on `S → ℝ`, and solutions have two-sided derivatives at every `t ≥ 0`. -/
theorem stable_all_classes {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ x : ℝ → S → ℝ,
      (∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t) →
      ‖x 0 - a‖ < η → ∀ t, 0 ≤ t → ‖x t - a‖ < ε := by
  obtain ⟨R, hR, hposR⟩ := positive_closedBall ha
  let r := min (ε / 2) R
  have hr : 0 < r := lt_min (by positivity) hR
  have hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ r → ∀ s, 0 < z s :=
    fun z hz => hposR z (hz.trans (min_le_right _ _))
  obtain ⟨b, hb, hboundary⟩ := energy_boundary_lower ha hr hpos
  have hevent : ∀ᶠ z in nhds a, energy a z < b :=
    (energy_continuousAt a ha).eventually_lt continuousAt_const (by simpa [energy_self] using hb)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min r δ, lt_min hr hδ, fun x hx hnear t ht => ?_⟩
  have htr := energy_trapping N hk ha hcb hpos hboundary hx
    (hnear.trans_le (min_le_left _ _))
    (hsmall (by simpa [dist_eq_norm] using hnear.trans_le (min_le_right r δ))) t ht
  exact htr.trans_le ((min_le_left _ _).trans (by linarith : ε / 2 ≤ ε))

/-- **Lyapunov stability of a positive equilibrium.** Let a mass-action system with positive
rate constants have a positive complex-balanced point `cstar`, and let `xstar` be a positive
equilibrium. For every `ε > 0` there is `η > 0` such that every solution on `[0, ∞)` that starts
in the stoichiometric compatibility class of `xstar`, within `η` of it, stays within `ε` of it
for all `t ≥ 0`. Distances are sup-norm distances on `S → ℝ`, and solutions have two-sided
derivatives at every `t ≥ 0`. The class hypothesis is not needed: stability holds across
classes (`stable_all_classes`). -/
theorem stable {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 < k r)
    (cstar : S → ℝ) (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    (xstar : S → ℝ) (hxstar : ∀ s, 0 < xstar s) (heq : N.massActionField k xstar = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ (x : ℝ → S → ℝ)
      (_hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
      (_hclass : x 0 - xstar ∈ N.stoichiometricSubspace) (_hnear : ‖x 0 - xstar‖ < η),
      ∀ t, 0 ≤ t → ‖x t - xstar‖ < ε := by
  have hcbstar := N.isComplexBalanced_of_massActionField_eq_zero hk hcstar hcb hxstar heq
  obtain ⟨η, hη, hstable⟩ := stable_all_classes N hk hxstar hcbstar hε
  exact ⟨η, hη, fun x hx _hclass hnear => hstable x hx hnear⟩

private theorem equilibrium_eq_of_class {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    (heq : N.massActionField k a = 0) {z : S → ℝ} (hz : ∀ s, 0 < z s)
    (hclass : z - a ∈ N.stoichiometricSubspace) (hzeq : N.massActionField k z = 0) :
    z = a := by
  have h := N.existsUnique_equilibrium_of_isComplexBalanced hk ha hcb ha
  exact h.unique ⟨hz, hclass, hzeq⟩ ⟨ha, by simp, heq⟩

private theorem helmholtzRate_continuousAt {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (a : S → ℝ) {z : S → ℝ}
    (hz : ∀ s, 0 < z s) : ContinuousAt (N.helmholtzRate k a) z := by
  have hc (s : S) : ContinuousAt (fun w : S → ℝ => w s) z :=
    (continuous_apply s).continuousAt
  have hf (s : S) : ContinuousAt (fun w : S → ℝ => N.massActionField k w s) z :=
    (continuous_apply s).continuousAt.comp (N.massActionField_contDiff k).continuous.continuousAt
  exact tendsto_finsetSum Finset.univ fun s _ =>
    (((hc s).log (hz s).ne').sub continuousAt_const).mul (hf s)

private theorem uniform_dissipation {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    (heq : N.massActionField k a = 0) {R δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ R → ∀ s, 0 < z s) :
    ∃ d > 0, ∀ z : S → ℝ, ‖z - a‖ ≤ R →
      z - a ∈ N.stoichiometricSubspace → δ ≤ ‖z - a‖ →
      N.helmholtzRate k a z ≤ -d := by
  classical
  let K := Metric.closedBall a R ∩
    (fun z : S → ℝ => z - a) ⁻¹' (N.stoichiometricSubspace : Set (S → ℝ)) ∩
    (fun z : S → ℝ => ‖z - a‖) ⁻¹' Ici δ
  have hclosedW : IsClosed (N.stoichiometricSubspace : Set (S → ℝ)) :=
    N.stoichiometricSubspace.isClosed_of_finiteDimensional
  have hK : IsCompact K :=
    ((isCompact_closedBall a R).inter_right
      (hclosedW.preimage (continuous_id.sub continuous_const))).inter_right
      (isClosed_Ici.preimage (continuous_id.sub continuous_const).norm)
  have hmem : ∀ z ∈ K, ‖z - a‖ ≤ R ∧ z - a ∈ N.stoichiometricSubspace ∧ δ ≤ ‖z - a‖ :=
    fun z hz => ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1.1, hz.1.2, hz.2⟩
  have hlt : ∀ z ∈ K, N.helmholtzRate k a z < 0 := by
    intro z hz
    obtain ⟨hR, hW, hn⟩ := hmem z hz
    have hzp := hpos z hR
    have hne : z ≠ a := by intro h; subst z; simp only [sub_self, norm_zero] at hn; linarith
    have hnot : N.helmholtzRate k a z ≠ 0 := by
      intro h0
      exact hne (equilibrium_eq_of_class N hk ha hcb heq hzp hW
        ((N.helmholtzRate_eq_zero_iff hk ha hcb hzp).mp h0))
    exact lt_of_le_of_ne (N.helmholtzRate_nonpos hk ha hcb hzp) hnot
  by_cases hn : K.Nonempty
  · obtain ⟨z, hz, hm⟩ := hK.exists_isMinOn hn
      (fun z hz => (helmholtzRate_continuousAt N k a (hpos z (hmem z hz).1)).neg.continuousWithinAt)
    refine ⟨-N.helmholtzRate k a z, by linarith [hlt z hz], fun w hwR hwW hwn => ?_⟩
    have hw : w ∈ K := ⟨⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hwR, hwW⟩, hwn⟩
    have hm' : -N.helmholtzRate k a z ≤ -N.helmholtzRate k a w := hm hw
    linarith
  · exact ⟨1, zero_lt_one, fun z hz hW hδz => False.elim
      (hn ⟨z, ⟨⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, hW⟩, hδz⟩⟩)⟩

private theorem exists_entry {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a)
    (heq : N.massActionField k a = 0) {R δ : ℝ} (hδ : 0 < δ)
    (hpos : ∀ z : S → ℝ, ‖z - a‖ ≤ R → ∀ s, 0 < z s)
    {x : ℝ → S → ℝ}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
    (hbounded : ∀ t, 0 ≤ t → ‖x t - a‖ ≤ R)
    (hclass : ∀ t, 0 ≤ t → x t - a ∈ N.stoichiometricSubspace) :
    ∃ t, 0 ≤ t ∧ ‖x t - a‖ < δ := by
  obtain ⟨d, hd, hbound⟩ := uniform_dissipation N hk ha hcb heq hδ hpos
  by_contra hbad
  have hfar : ∀ t, 0 ≤ t → δ ≤ ‖x t - a‖ := by
    simpa only [not_exists, not_and, not_lt] using hbad
  have hxp : ∀ t, 0 ≤ t → ∀ s, 0 < x t s := fun t ht => hpos (x t) (hbounded t ht)
  let T := (energy a (x 0) + 1) / d
  have hT : 0 ≤ T := by
    have hE := energy_nonneg ha (hxp 0 le_rfl)
    dsimp [T]
    positivity
  have hder : ∀ t, 0 ≤ t →
      HasDerivAt (fun u => energy a (x u) + d * u) (N.helmholtzRate k a (x t) + d) t := by
    intro t ht
    exact ((N.hasDerivAt_pseudoHelmholtz a (hx t ht) (hxp t ht)).sub_const _).add
      (hasDerivAt_const_mul d)
  have hmono : AntitoneOn (fun t => energy a (x t) + d * t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun t ht => (hder t ht.1).continuousAt.continuousWithinAt)
    · exact fun t ht => (hder t (interior_subset ht).1).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (interior_subset ht).1
      rw [(hder t ht0).deriv]
      have := hbound (x t) (hbounded t ht0) (hclass t ht0) (hfar t ht0)
      linarith
  have hle := hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  have hnonneg := energy_nonneg ha (hxp T hT)
  have hmul : d * T = energy a (x 0) + 1 := by dsimp [T]; field_simp
  change energy a (x T) + d * T ≤ energy a (x 0) + d * 0 at hle
  rw [hmul, mul_zero, add_zero] at hle
  linarith

/-- **Local attraction within the compatibility class.** Let a mass-action system with
positive rate constants have a positive complex-balanced point `cstar`, and let `xstar` be a
positive equilibrium. There is `η > 0` such that every solution on `[0, ∞)` that starts in the
stoichiometric compatibility class of `xstar`, within `η` of it, converges to `xstar` as
`t → ∞`. Distances are sup-norm distances on `S → ℝ`, and solutions have two-sided derivatives
at every `t ≥ 0`. The convergence is local and relative to the class, and the class hypothesis
cannot be dropped: equilibria of other classes can lie arbitrarily close to `xstar` (for
`A ⇌ B` with equal rates, every `(c, c)` with `c > 0` is one), and they are constant
solutions. -/
theorem attractive {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 < k r)
    (cstar : S → ℝ) (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    (xstar : S → ℝ) (hxstar : ∀ s, 0 < xstar s) (heq : N.massActionField k xstar = 0) :
    ∃ η > 0, ∀ (x : ℝ → S → ℝ)
      (_hx : ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t)
      (_hclass : x 0 - xstar ∈ N.stoichiometricSubspace) (_hnear : ‖x 0 - xstar‖ < η),
      Filter.Tendsto x Filter.atTop (nhds xstar) := by
  have hcbstar := N.isComplexBalanced_of_massActionField_eq_zero hk hcstar hcb hxstar heq
  obtain ⟨R, hR, hpos⟩ := positive_closedBall hxstar
  obtain ⟨η, hη, hstableR⟩ := stable_all_classes N hk hxstar hcbstar hR
  refine ⟨η, hη, fun x hx hclass hnear => ?_⟩
  have hbounded : ∀ t, 0 ≤ t → ‖x t - xstar‖ ≤ R :=
    fun t ht => (hstableR x hx hnear t ht).le
  have hclasses : ∀ t, 0 ≤ t → x t - xstar ∈ N.stoichiometricSubspace := by
    intro t ht
    simpa using N.stoichiometricSubspace.add_mem (solution_sub_mem N k hx ht) hclass
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hstableε⟩ := stable_all_classes N hk hxstar hcbstar hε
  obtain ⟨u, hu, hentry⟩ := exists_entry N hk hxstar hcbstar heq hδ hpos hx hbounded hclasses
  let y : ℝ → S → ℝ := fun t => x (t + u)
  have hy : ∀ t, 0 ≤ t → HasDerivAt y (N.massActionField k (y t)) t := by
    intro t ht
    have h := (hx (t + u) (by linarith)).scomp t ((hasDerivAt_id t).add_const u)
    simpa [y, Function.comp_def] using h
  have hynear : ‖y 0 - xstar‖ < δ := by simpa [y] using hentry
  refine ⟨u, fun t ht => ?_⟩
  have hnorm := hstableε y hy hynear (t - u) (by linarith)
  simpa [y, sub_add_cancel, dist_eq_norm] using hnorm

private noncomputable def clip {S : Type*} (a : S → ℝ) (R : ℝ) (z : S → ℝ) : S → ℝ :=
  fun s => max (a s - R) (min (a s + R) (z s))

private theorem clip_mem_closedBall {S : Type*} [Fintype S] (a : S → ℝ) {R : ℝ}
    (hR : 0 ≤ R) (z : S → ℝ) : ‖clip a R z - a‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro s
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
  have hL : a s - R ≤ clip a R z s := le_max_left _ _
  have hU : clip a R z s ≤ a s + R :=
    max_le (by linarith) (min_le_left _ _)
  constructor <;> linarith

private theorem clip_eq_self {S : Type*} [Fintype S] (a z : S → ℝ) {R : ℝ}
    (hz : ‖z - a‖ ≤ R) : clip a R z = z := by
  ext s
  have hc := (norm_le_pi_norm (z - a) s).trans hz
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_le] at hc
  dsimp [clip]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

private theorem clip_lipschitz {S : Type*} [Fintype S] (a : S → ℝ) (R : ℝ) :
    LipschitzWith 1 (clip a R) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (z - w))).mpr
  intro s
  have heval : LipschitzWith 1 (fun z : S → ℝ => z s) := LipschitzWith.eval s
  have h := (heval.const_min (a s + R)).const_max (a s - R)
  simpa [clip] using h.norm_sub_le z w

private theorem lipschitz_extension {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (a : S → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ g : (S → ℝ) → S → ℝ, ∃ K : ℝ≥0,
      LipschitzWith K g ∧ ∀ z, ‖z - a‖ ≤ R → g z = N.massActionField k z := by
  let f := N.massActionField k
  have hf := N.massActionField_contDiff k
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall a R) (isCompact_closedBall a R)
  let g := f ∘ clip a R
  have hclip (z : S → ℝ) : clip a R z ∈ Metric.closedBall a R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using clip_mem_closedBall a hR z
  refine ⟨g, K, ?_, ?_⟩
  · have h := hK.comp (clip_lipschitz a R).lipschitzOnWith (s := Set.univ)
      (fun z _ => hclip z)
    simpa only [mul_one, lipschitzOnWith_univ] using h
  · intro z hz
    dsimp [g]
    rw [clip_eq_self a z hz]

/-- **Forward solutions near a complex-balanced point, in every class.** Let `a` be a positive
complex-balanced point, hence an equilibrium, of a mass-action system with positive rate
constants. There is `η > 0` such that every state within `η` of `a`, in any stoichiometric
compatibility class, is the initial value of a solution defined for all `t ≥ 0`, with two-sided
derivatives at every `t ≥ 0`, including `0`. Distances are sup-norm distances on `S → ℝ`. -/
theorem exists_solution_of_near_all_classes {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {a : S → ℝ} (ha : ∀ s, 0 < a s) (hcb : N.IsComplexBalanced k a) :
    ∃ η > 0, ∀ z : S → ℝ, ‖z - a‖ < η →
      ∃ x : ℝ → S → ℝ, x 0 = z ∧
        ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t := by
  obtain ⟨R, hR, hpos⟩ := positive_closedBall ha
  obtain ⟨b, hb, hboundary⟩ := energy_boundary_lower ha hR hpos
  have hevent : ∀ᶠ z in nhds a, energy a z < b :=
    (energy_continuousAt a ha).eventually_lt continuousAt_const
      (by simpa [energy_self] using hb)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨g, K, hK, hagree⟩ := lipschitz_extension N k a hR.le
  refine ⟨min R δ, lt_min hR hδ, fun z hnear => ?_⟩
  obtain ⟨x, ⟨hx0, hx⟩, -⟩ :=
    MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun _ => g) 0 z K (hK.continuous.comp continuous_snd) fun _ => hK
  have htr : ∀ t, 0 ≤ t → ‖x t - a‖ < R :=
    energy_trapping_of_continuousOn N hk ha hcb hpos hboundary
      (fun t _ => (hx t).continuousAt.continuousWithinAt)
      (fun t _ ht => by simpa only [hagree (x t) ht] using hx t)
      (by simpa only [hx0] using hnear.trans_le (min_le_left R δ))
      (by rw [hx0]; exact hsmall (by
        simpa [dist_eq_norm] using hnear.trans_le (min_le_right R δ)))
  exact ⟨x, hx0, fun t ht => by simpa only [hagree (x t) (htr t ht).le] using hx t⟩

/-- **Forward solutions near a positive equilibrium.** Let a mass-action system with positive
rate constants have a positive complex-balanced point `cstar`, and let `xstar` be a positive
equilibrium. There is `η > 0` such that every state `z` of the stoichiometric compatibility
class of `xstar` within `η` of it is the initial value of a solution defined for all `t ≥ 0`,
with two-sided derivatives at every `t ≥ 0`, including `0`. Distances are sup-norm distances on
`S → ℝ`. The class hypothesis is not needed: `exists_solution_of_near_all_classes` gives such
solutions from every nearby state. -/
theorem exists_solution_of_near {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : ReactionNetwork S ρ) (k : ρ → ℝ) (hk : ∀ r, 0 < k r)
    (cstar : S → ℝ) (hcstar : ∀ s, 0 < cstar s) (hcb : N.IsComplexBalanced k cstar)
    (xstar : S → ℝ) (hxstar : ∀ s, 0 < xstar s) (heq : N.massActionField k xstar = 0) :
    ∃ η > 0, ∀ (z : S → ℝ)
      (_hclass : z - xstar ∈ N.stoichiometricSubspace) (_hnear : ‖z - xstar‖ < η),
      ∃ x : ℝ → S → ℝ, x 0 = z ∧
        ∀ t, 0 ≤ t → HasDerivAt x (N.massActionField k (x t)) t := by
  have hcbstar := N.isComplexBalanced_of_massActionField_eq_zero hk hcstar hcb hxstar heq
  obtain ⟨η, hη, hexists⟩ := exists_solution_of_near_all_classes N hk hxstar hcbstar
  exact ⟨η, hη, fun z _hclass hnear => hexists z hnear⟩

end Domains.Biology.Dynamics.ComplexBalancedStability
