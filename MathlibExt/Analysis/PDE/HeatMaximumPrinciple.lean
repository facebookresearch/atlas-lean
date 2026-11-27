/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

/-!
# Weak maximum principle and uniqueness for the heat equation

Let `U` be a bounded open subset of a finite-dimensional real inner product space and `T ≥ 0`.
The parabolic cylinder is `(0, T] × U`; its parabolic boundary is
`({0} × closure U) ∪ ([0, T] × ∂U)`, which does not contain the points `(T, x)` with `x ∈ U`.
A function continuous on `[0, T] × closure U`, `C²` in space on the cylinder, with a left time
derivative `uₜ` satisfying `uₜ - Δ u ≤ 0` there, attains its maximum over `[0, T] × closure U` on
the parabolic boundary. Consequently the initial-boundary value problem for `uₜ - Δ u = f` has at
most one solution.

The proof is the perturbation argument: `u - ε t` satisfies `(u - ε t)ₜ - Δ (u - ε t) ≤ -ε < 0`,
while at an interior maximum (including at time `T`) the left time derivative is nonnegative and
the Laplacian is nonpositive.

## Main results

* `parabolicBoundary`: the parabolic boundary of `(0, T] × U`.
* `exists_mem_parabolicBoundary_isMaxOn`: weak maximum principle for subsolutions.
* `eqOn_of_heat_equation`: uniqueness for the initial-boundary value problem.

## References

* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 4 (Heat equation),
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf: §4.4, Theorem
  4.9 (weak maximum principle) and Theorem 4.10 (uniqueness).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19
  (2010), Chapter 2 (maximum principle and uniqueness for the heat equation on bounded domains).
  The book was not available to this formalization; theorem numbers are not cited from it.
-/

@[expose] public section

open InnerProductSpace Filter Topology Set Laplacian

namespace MathlibExt.Analysis.PDE.HeatMaximumPrinciple

open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Parabolic boundary of a space-time cylinder.** For `U` and `T`, the set
`({0} × closure U) ∪ ([0, T] × ∂U)` of pairs `(t, x)`. For open `U` and `T > 0` it is the closure
of the cylinder `(0, T] × U` minus the cylinder itself, as defined in §4.4 of M. Schmidt, *Partial
Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, Chapter 4 (written `∂Ω_T`
there); for `T = 0` the cylinder is empty and the set is `{0} × closure U`, the initial time
slice. -/
def parabolicBoundary (U : Set E) (T : ℝ) : Set (ℝ × E) :=
  ({0} ×ˢ closure U) ∪ (Icc 0 T ×ˢ frontier U)

/-- A left derivative at a maximum over `[0, t]` is nonnegative. -/
private theorem nonneg_of_isMaxOn_Icc {g : ℝ → ℝ} {g' t : ℝ} (ht : 0 < t)
    (hmax : IsMaxOn g (Icc 0 t) t) (hg : HasDerivWithinAt g g' (Icc 0 t) t) : 0 ≤ g' := by
  have hloc : IsLocalMaxOn g (Icc 0 t) t := hmax.isLocalMaxOn
  have hseg : segment ℝ t 0 ⊆ Icc 0 t := by
    rw [segment_symm]
    exact (convex_Icc 0 t).segment_subset (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le)
  have hy := sub_mem_posTangentConeAt_of_segment_subset hseg
  have := hloc.hasFDerivWithinAt_nonpos hg.hasFDerivWithinAt hy
  simp at this
  nlinarith

variable [FiniteDimensional ℝ E]

/-- **Weak maximum principle for the heat equation.** Let `U` be a nonempty bounded open subset of
a finite-dimensional real inner product space and `T ≥ 0`. If `u` is continuous on
`[0, T] × closure U`, `u t` is `C²` at every `x ∈ U` for `t ∈ (0, T]`, `s ↦ u s x` has left
derivative `uₜ t x` at such `t`, and `uₜ - Δ u ≤ 0` on `(0, T] × U`, then `u` attains its maximum
over `[0, T] × closure U` at a point of the parabolic boundary.

This is Theorem 4.9 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 4, stated there for solutions of the heat equation; here for
subsolutions, with only a left time derivative. -/
theorem exists_mem_parabolicBoundary_isMaxOn {U : Set E} {T : ℝ} (hT : 0 ≤ T)
    (hUb : Bornology.IsBounded U) (hU : IsOpen U) (hne : U.Nonempty)
    {u ut : ℝ → E → ℝ}
    (hc : ContinuousOn (fun p : ℝ × E => u p.1 p.2) (Icc 0 T ×ˢ closure U))
    (hx : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ContDiffAt ℝ 2 (u t) x)
    (ht : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, HasDerivWithinAt (fun s => u s x) (ut t x) (Iic t) t)
    (hsub : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ut t x - Δ (u t) x ≤ 0) :
    ∃ p ∈ parabolicBoundary U T,
      IsMaxOn (fun p : ℝ × E => u p.1 p.2) (Icc 0 T ×ˢ closure U) p := by
  set K := Icc 0 T ×ˢ closure U with hK
  have hKc : IsCompact K := isCompact_Icc.prod hUb.isCompact_closure
  have hΓsub : parabolicBoundary U T ⊆ K := by
    rintro ⟨t, x⟩ (⟨ht0, hx0⟩ | ⟨ht0, hx0⟩)
    · simp only [mem_singleton_iff] at ht0
      exact ⟨by rw [ht0]; exact left_mem_Icc.mpr hT, hx0⟩
    · exact ⟨ht0, frontier_subset_closure hx0⟩
  have hΓc : IsCompact (parabolicBoundary U T) :=
    (isCompact_singleton.prod hUb.isCompact_closure).union
      (isCompact_Icc.prod (Metric.isCompact_of_isClosed_isBounded isClosed_frontier
        (hUb.closure.subset frontier_subset_closure)))
  have hΓne : (parabolicBoundary U T).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(0, x), Or.inl ⟨rfl, subset_closure hx⟩⟩
  obtain ⟨p, hp, hpmax⟩ := hΓc.exists_isMaxOn hΓne (hc.mono hΓsub)
  refine ⟨p, hp, fun q hq => ?_⟩
  simp only [mem_ofPred_eq]
  by_contra hlt
  push Not at hlt
  set δ := u q.1 q.2 - u p.1 p.2 with hδ
  have hδpos : 0 < δ := by linarith
  set ε := δ / (2 * (T + 1)) with hε
  have hεpos : 0 < ε := by positivity
  set v : ℝ × E → ℝ := fun r => u r.1 r.2 - ε * r.1 with hv
  have hvc : ContinuousOn v K := hc.sub (continuousOn_const.mul continuous_fst.continuousOn)
  obtain ⟨r, hr, hrmax⟩ := hKc.exists_isMaxOn ⟨q, hq⟩ hvc
  have hεT : ε * T < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  -- the maximum of `v` is not on the parabolic boundary
  have hrΓ : r ∉ parabolicBoundary U T := by
    intro hrΓ
    have h1 : v q ≤ v r := hrmax hq
    have h2 : u r.1 r.2 ≤ u p.1 p.2 := hpmax hrΓ
    have h3 : 0 ≤ r.1 := hr.1.1
    have h4 : q.1 ≤ T := hq.1.2
    simp only [hv] at h1
    nlinarith [mul_le_mul_of_nonneg_left h4 hεpos.le, mul_nonneg hεpos.le h3]
  obtain ⟨⟨hr0, hrT⟩, hrU'⟩ := hr
  have hr0' : 0 < r.1 := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exact absurd (Or.inl ⟨by simp [← h], hrU'⟩) hrΓ
  have hrU : r.2 ∈ U := by
    by_contra hn
    refine hrΓ (Or.inr ⟨⟨hr0, hrT⟩, ?_⟩)
    rw [frontier, hU.interior_eq]
    exact ⟨hrU', hn⟩
  have hmem : r.1 ∈ Ioc 0 T := ⟨hr0', hrT⟩
  -- space: `u r.1` has a local maximum at `r.2`
  have hspace : IsLocalMax (u r.1) r.2 := by
    filter_upwards [hU.mem_nhds hrU] with y hy
    have := hrmax (show (r.1, y) ∈ K from ⟨⟨hr0, hrT⟩, subset_closure hy⟩)
    simp only [hv, mem_ofPred_eq] at this
    linarith
  have hΔ := laplacian_nonpos_of_isLocalMax (hx r.1 hmem r.2 hrU) hspace
  -- time: `s ↦ u s r.2 - ε s` has a maximum over `[0, r.1]` at `r.1`
  have htime : IsMaxOn (fun s => u s r.2 - ε * s) (Icc 0 r.1) r.1 := by
    intro s hs
    exact hrmax (show (s, r.2) ∈ K from ⟨⟨hs.1, hs.2.trans hrT⟩, hrU'⟩)
  have hder : HasDerivWithinAt (fun s => u s r.2 - ε * s) (ut r.1 r.2 - ε) (Icc 0 r.1) r.1 :=
    ((ht r.1 hmem r.2 hrU).mono Icc_subset_Iic_self).sub
      ((hasDerivAt_id r.1).const_mul ε |>.hasDerivWithinAt.congr_deriv (by simp))
  have hnn := nonneg_of_isMaxOn_Icc hr0' htime hder
  have := hsub r.1 hmem r.2 hrU
  linarith

/-- **Uniqueness for the heat equation on a bounded domain.** Let `U` be a bounded open subset of
a finite-dimensional real inner product space and `T ≥ 0`. Two functions that are continuous on
`[0, T] × closure U`, `C²` in space and left-differentiable in time on `(0, T] × U`, solve
`uₜ - Δ u = f` there and agree on the parabolic boundary, agree on `[0, T] × closure U`
(Theorem 4.10 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 4; Evans, *Partial Differential Equations*, 2nd ed., Chapter 2). -/
theorem eqOn_of_heat_equation {U : Set E} {T : ℝ} (hT : 0 ≤ T)
    (hUb : Bornology.IsBounded U) (hU : IsOpen U)
    {u₁ u₂ ut₁ ut₂ f : ℝ → E → ℝ}
    (hc₁ : ContinuousOn (fun p : ℝ × E => u₁ p.1 p.2) (Icc 0 T ×ˢ closure U))
    (hc₂ : ContinuousOn (fun p : ℝ × E => u₂ p.1 p.2) (Icc 0 T ×ˢ closure U))
    (hx₁ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ContDiffAt ℝ 2 (u₁ t) x)
    (hx₂ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ContDiffAt ℝ 2 (u₂ t) x)
    (ht₁ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, HasDerivWithinAt (fun s => u₁ s x) (ut₁ t x) (Iic t) t)
    (ht₂ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, HasDerivWithinAt (fun s => u₂ s x) (ut₂ t x) (Iic t) t)
    (heq₁ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ut₁ t x - Δ (u₁ t) x = f t x)
    (heq₂ : ∀ t ∈ Ioc 0 T, ∀ x ∈ U, ut₂ t x - Δ (u₂ t) x = f t x)
    (hb : ∀ p ∈ parabolicBoundary U T, u₁ p.1 p.2 = u₂ p.1 p.2) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ closure U, u₁ t x = u₂ t x := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · simp
  have key : ∀ {w₁ w₂ wt₁ wt₂ : ℝ → E → ℝ},
      ContinuousOn (fun p : ℝ × E => w₁ p.1 p.2) (Icc 0 T ×ˢ closure U) →
      ContinuousOn (fun p : ℝ × E => w₂ p.1 p.2) (Icc 0 T ×ˢ closure U) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, ContDiffAt ℝ 2 (w₁ t) x) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, ContDiffAt ℝ 2 (w₂ t) x) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, HasDerivWithinAt (fun s => w₁ s x) (wt₁ t x) (Iic t) t) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, HasDerivWithinAt (fun s => w₂ s x) (wt₂ t x) (Iic t) t) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, wt₁ t x - Δ (w₁ t) x = f t x) →
      (∀ t ∈ Ioc 0 T, ∀ x ∈ U, wt₂ t x - Δ (w₂ t) x = f t x) →
      (∀ p ∈ parabolicBoundary U T, w₁ p.1 p.2 = w₂ p.1 p.2) →
      ∀ t ∈ Icc 0 T, ∀ x ∈ closure U, w₁ t x ≤ w₂ t x := by
    intro w₁ w₂ wt₁ wt₂ hc₁ hc₂ hx₁ hx₂ ht₁ ht₂ heq₁ heq₂ hb t ht x hx
    obtain ⟨p, hp, hmax⟩ := exists_mem_parabolicBoundary_isMaxOn (u := fun s y => w₁ s y - w₂ s y)
      (ut := fun s y => wt₁ s y - wt₂ s y) hT hUb hU hne (hc₁.sub hc₂)
      (fun s hs y hy => (hx₁ s hs y hy).sub (hx₂ s hs y hy))
      (fun s hs y hy => (ht₁ s hs y hy).sub (ht₂ s hs y hy))
      (fun s hs y hy => by
        have hl : Δ (fun y => w₁ s y - w₂ s y) y = Δ (w₁ s) y - Δ (w₂ s) y :=
          (hx₁ s hs y hy).laplacian_sub (hx₂ s hs y hy)
        rw [hl]
        linarith [heq₁ s hs y hy, heq₂ s hs y hy])
    have := hmax (show (t, x) ∈ Icc 0 T ×ˢ closure U from ⟨ht, hx⟩)
    simp only [mem_ofPred_eq] at this
    linarith [hb p hp]
  intro t ht x hx
  exact le_antisymm (key hc₁ hc₂ hx₁ hx₂ ht₁ ht₂ heq₁ heq₂ hb t ht x hx)
    (key hc₂ hc₁ hx₂ hx₁ ht₂ ht₁ heq₂ heq₁ (fun p hp => (hb p hp).symm) t ht x hx)

end MathlibExt.Analysis.PDE.HeatMaximumPrinciple
