/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SelfishRouting
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! # Existence of Wardrop equilibria

Beckmann, McGuire and Winsten showed that a nonatomic routing instance with continuous
latencies has a Wardrop equilibrium for every nonnegative demand: the feasible flows form a
nonempty compact polytope, the *Beckmann potential* `Φ(f) = ∑ₑ ∫₀^{fₑ} ℓₑ(x) dx` is continuous
on it and so attains its minimum, and at a minimiser no traffic can be shifted from a path to a
cheaper path of the same commodity, because the derivative of `Φ` in that direction is the
difference of the two path latencies.

Only continuity of the latencies on `[0, ∞)` is used; monotonicity, which Roughgarden and
Tardos also assume, gives uniqueness of the equilibrium cost instead
(`RoutingInstance.IsWardrop.cost_eq`).

## Main results

* `RoutingInstance.exists_isWardrop`: if every commodity has a path and the demands are
  nonnegative, some feasible flow is a Wardrop equilibrium.

## References

* M. Beckmann, C. B. McGuire and C. B. Winsten, *Studies in the Economics of
  Transportation*, Yale University Press, 1956.
* T. Roughgarden and É. Tardos, "How bad is selfish routing?", J. ACM 49(2) (2002),
  236–259, Lemma 2.9 (§2.4) and §2.3.
-/

namespace MathlibExt.GameTheory.SelfishRouting

open Finset

namespace RoutingInstance

variable {E ι P : Type*} [Fintype E] [Fintype P] [DecidableEq E] [DecidableEq ι]
variable (N : RoutingInstance E ι P)

/-- The latency of edge `e` extended to negative loads by its value at `0`. -/
private noncomputable def clampedLatency (e : E) (x : ℝ) : ℝ :=
  N.latency e (max x 0)

/-- The Beckmann potential `∑ₑ ∫₀^{fₑ} ℓₑ`, written with the clamped latencies so that it is
defined and differentiable for every path flow; it agrees with the Beckmann potential on
nonnegative flows. -/
private noncomputable def potential (f : P → ℝ) : ℝ :=
  ∑ e, ∫ x in (0 : ℝ)..N.edgeFlow f e, N.clampedLatency e x

omit [Fintype E] [Fintype P] [DecidableEq E] [DecidableEq ι] in
private theorem continuous_clampedLatency (hℓ : ∀ e, ContinuousOn (N.latency e) (Set.Ici 0))
    (e : E) : Continuous (N.clampedLatency e) :=
  (hℓ e).comp_continuous (continuous_id.max continuous_const) fun x => le_max_right x 0

omit [Fintype E] [DecidableEq ι] in
private theorem continuous_edgeFlow (e : E) : Continuous fun f : P → ℝ => N.edgeFlow f e :=
  continuous_finsetSum _ fun p _ => continuous_apply p

omit [DecidableEq ι] in
private theorem continuous_potential (hℓ : ∀ e, ContinuousOn (N.latency e) (Set.Ici 0)) :
    Continuous N.potential := by
  refine continuous_finsetSum _ fun e _ => ?_
  have hF : Continuous fun y => ∫ x in (0 : ℝ)..y, N.clampedLatency e x :=
    continuous_iff_continuousAt.2 fun y =>
      ((N.continuous_clampedLatency hℓ e).integral_hasStrictDerivAt 0 y).hasDerivAt.continuousAt
  exact hF.comp (N.continuous_edgeFlow e)

omit [Fintype E] [DecidableEq ι] in
private theorem edgeFlow_add_smul (f v : P → ℝ) (δ : ℝ) (e : E) :
    N.edgeFlow (f + δ • v) e = N.edgeFlow f e + δ * N.edgeFlow v e := by
  simp [edgeFlow, sum_add_distrib, mul_sum]

omit [Fintype E] [DecidableEq E] in
private theorem isCompact_feasible {r : ι → ℝ} : IsCompact {f : P → ℝ | N.IsFeasible r f} := by
  have hclosed : IsClosed {f : P → ℝ | N.IsFeasible r f} := by
    have : {f : P → ℝ | N.IsFeasible r f} =
        (⋂ p, {f : P → ℝ | 0 ≤ f p}) ∩
          ⋂ i, {f : P → ℝ | ∑ p with N.commodity p = i, f p = r i} := by
      ext f; simp [IsFeasible]
    rw [this]
    exact (isClosed_iInter fun p => isClosed_le continuous_const (continuous_apply p)).inter
      (isClosed_iInter fun i =>
        isClosed_eq (continuous_finsetSum _ fun p _ => continuous_apply p) continuous_const)
  refine (isCompact_univ_pi fun p => isCompact_Icc (a := (0 : ℝ))
    (b := r (N.commodity p))).of_isClosed_subset hclosed fun f hf p _ => ⟨hf.1 p, ?_⟩
  rw [← hf.2 (N.commodity p)]
  exact single_le_sum (fun q _ => hf.1 q) (by simp)

omit [Fintype E] in
/-- **Existence of Wardrop equilibria** (Beckmann, McGuire and Winsten 1956; Roughgarden–Tardos
2002, Lemma 2.9). If every latency is continuous on `[0, ∞)`, every commodity has at least
one path and every demand is nonnegative, then some flow feasible for the demands is a Wardrop
equilibrium. The proof minimises the Beckmann potential `∑ₑ ∫₀^{fₑ} ℓₑ` over the compact set of
feasible flows. -/
theorem exists_isWardrop [Finite E] (hℓ : ∀ e, ContinuousOn (N.latency e) (Set.Ici 0)) {r : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hpath : ∀ i, ∃ p, N.commodity p = i) :
    ∃ f, N.IsFeasible r f ∧ N.IsWardrop f := by
  classical
  cases nonempty_fintype E
  choose pth hpth using hpath
  set K := {f : P → ℝ | N.IsFeasible r f}
  have hne : K.Nonempty := by
    refine ⟨fun p => if pth (N.commodity p) = p then r (N.commodity p) else 0,
      fun p => by dsimp only; split_ifs <;> simp [hr], fun i => ?_⟩
    have h : ∀ p ∈ univ.filter (fun p => N.commodity p = i),
        (if pth (N.commodity p) = p then r (N.commodity p) else 0) =
          if pth i = p then r i else 0 := by
      intro p hp; rw [(mem_filter.1 hp).2]
    dsimp only
    rw [sum_congr rfl h, sum_ite_eq]
    simp [hpth]
  obtain ⟨f, hfK, hmin⟩ := N.isCompact_feasible.exists_isMinOn hne
    (N.continuous_potential hℓ).continuousOn
  refine ⟨f, hfK, fun p q hpq hfp => ?_⟩
  by_contra hlt
  push Not at hlt
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hlt
  set v : P → ℝ := Pi.single q 1 - Pi.single p 1
  set g : ℝ → ℝ := fun δ => N.potential (f + δ • v)
  -- moving `δ ∈ [0, f p]` units from `p` to `q` keeps the flow feasible
  have hmem : ∀ δ ∈ Set.Icc (0 : ℝ) (f p), f + δ • v ∈ K := by
    rintro δ ⟨hδ0, hδ⟩
    refine ⟨fun x => ?_, fun i => ?_⟩
    · by_cases hxq : x = q
      · subst hxq
        simp [v, hpq', hfK.1 x, hδ0, add_nonneg]
      · by_cases hxp : x = p
        · subst hxp; simp [v, hxq]; linarith
        · simp [v, hxq, hxp, hfK.1 x]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
      rw [hfK.2 i]
      have : ∑ x with N.commodity x = i, v x = 0 := by
        simp only [v, Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_filter, mem_univ,
          true_and, hpq]
        simp
      rw [this, mul_zero, add_zero]
  have hlocmin : IsLocalMinOn g (Set.Icc 0 (f p)) 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => by
      simpa [g] using hmin (hmem δ hδ)
  -- the derivative of the potential in the direction `v`
  set d := ∑ e, N.clampedLatency e (N.edgeFlow f e) * N.edgeFlow v e
  have hderiv : HasDerivAt g d 0 := by
    have : g = fun δ => ∑ e, ∫ x in (0 : ℝ)..(N.edgeFlow f e + δ * N.edgeFlow v e),
        N.clampedLatency e x := by
      funext δ; simp only [g, potential, edgeFlow_add_smul]
    rw [this]
    refine HasDerivAt.fun_sum fun e _ => ?_
    have hF := ((N.continuous_clampedLatency hℓ e).integral_hasStrictDerivAt 0
      (N.edgeFlow f e + 0 * N.edgeFlow v e)).hasDerivAt
    have hin : HasDerivAt (fun δ : ℝ => N.edgeFlow f e + δ * N.edgeFlow v e)
        (1 * N.edgeFlow v e) 0 :=
      HasDerivAt.const_add (N.edgeFlow f e)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (N.edgeFlow v e))
    have := hF.comp 0 hin
    simpa [Function.comp_def] using this
  have hd : 0 ≤ d := by
    have hseg : segment ℝ (0 : ℝ) (0 + f p) ⊆ Set.Icc 0 (f p) := by
      rw [zero_add, segment_eq_Icc hfp.le]
    have := hlocmin.hasFDerivWithinAt_nonneg hderiv.hasFDerivAt.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hfp
  have hdeq : d = N.pathLatency f q - N.pathLatency f p := by
    have hclamp : ∀ e, N.clampedLatency e (N.edgeFlow f e) = N.latency e (N.edgeFlow f e) :=
      fun e => by simp [clampedLatency, max_eq_left (edgeFlow_nonneg hfK.1 e)]
    simp only [d, hclamp]
    rw [← sum_pathLatency_mul]
    simp [v, mul_sub, sum_sub_distrib, Pi.single_apply]
  linarith

end RoutingInstance

end MathlibExt.GameTheory.SelfishRouting
