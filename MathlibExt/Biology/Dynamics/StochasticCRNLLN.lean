/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
public import MathlibExt.Biology.Epidemiology.StochasticSIRKurtz
import MathlibExt.Analysis.ODE.GronwallIntegral

/-!
# Kurtz's law of large numbers for density-dependent stochastic reaction networks

A stochastic chemical reaction network (`StochasticCRNNonExplosion.StochasticCRN`) on finitely
many species `S` with finitely many reactions `ρ` is the continuous-time Markov chain on count
vectors `X : S → ℕ` in which reaction `r` fires at rate `λ_r(X)` and moves the state by the
reaction vector `ζ_r = prod r - src r`. A family `C N` of such networks indexed by a system size
`N` (volume times Avogadro's number) is *density dependent* (Kurtz 1970) if the propensities are
asymptotically of the form `λ^N_r(z) = N β_r(z / N)`. Kurtz's theorem says that the concentration
process `X^N(t) / N` then converges, uniformly on compact time intervals and in probability, to
the solution of the **mean-field** (deterministic reaction-rate) equation

  `x' = ∑_r β_r(x) ζ_r`.

For mass-action kinetics `β_r(x) = κ_r ∏_s x_s ^ (src r s)` this is the deterministic
mass-action system `ComplexBalanced.ReactionNetwork.massActionField`.

## The chain

As in `MathlibExt.Biology.Epidemiology.StochasticSIRKurtz`, the chain is given by Kurtz's random
time-change representation (Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)): with unit-rate
Poisson processes `Y_r`, one per reaction,

  `X(t) = X(0) + ∑_r Y_r(∫₀ᵗ λ_r(X(s)) ds) ζ_r`.

`IsChainPath C y X` states this equation for one sample path, with measurable coordinates and
locally integrable propensities along the path.

## Main results

* `IsChainPath.deviation_le`: Kurtz's pathwise estimate, localized to a tube around the
  deterministic trajectory. If on the `δ`-tube (in `ℓ¹`) the scaled propensities are within
  `e + L · distance` of `β_r` along the trajectory and bounded by `B`, and the scaled clocks satisfy
  `|y(N a) / N - a| ≤ η` on `[0, (B + 1) T]`, then as long as the resulting bound stays inside the
  tube, the `ℓ¹` deviation of `X / N` from `x` on `[0, T]` is at most
  `(initial deviation + Z (η + e T)) e^{L Z t}`, with `Z = ∑_r ‖ζ_r‖₁`. The proof does not use
  right-continuity of the paths: the clock bound itself limits the size of a jump.
* `tendsto_measure_deviation`: **Kurtz's theorem.** If each `β_r` is locally Lipschitz, the scaled
  propensities converge to `β_r` uniformly on bounded sets, and the scaled initial state converges
  in probability, then for every `T` and `ε > 0`
  `P(∃ t ∈ [0, T], ‖X^N(t) / N - x(t)‖₁ ≥ ε) → 0`.
* `tendsto_measure_iSup_deviation`: the same for the supremum over `[0, T]`.
* `tendsto_measure_deviation_of_eq`: the exactly density-dependent case
  `λ^N_r(z) = N β_r(z / N)`.
* `tendsto_measure_deviation_zero_of_initial`: the initial-condition hypothesis for deterministic
  initial counts with `X^N(0) / N → x(0)`.
* `tendsto_measure_deviation_massAction`: **mass-action kinetics.** For the stochastic mass-action
  propensities `massActionPropensity` (falling factorials over `N^{|src r|}`), the limit is the
  deterministic mass-action system `x' = massActionField κ x`; the propensity error is `O(1 / N)`
  on bounded sets (`abs_massActionPropensity_div_sub_le`).

## Scope

* The chain is taken as given through its time-change representation, almost surely. That the
  jump–hold path `StochasticCRN.path` of `MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion`
  has such a representation is not proved here (for SIR it is
  `MathlibExt.Biology.Epidemiology.StochasticSIRChain`).
* No growth or non-explosion condition is needed: the estimate is localized to a neighbourhood of
  the deterministic trajectory on `[0, T]`, which is compact.
* Independence of the clocks `Y_r` is not used, so it is not assumed.
* Only the law of large numbers is proved; the diffusion (central limit) correction is not treated.
* The events over `[0, T]` are not assumed measurable; their probabilities are outer measures.

## References

* T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump Markov
  processes*, J. Appl. Probab. 7 (1970) 49–58.
* T. G. Kurtz, *The relationship between stochastic and deterministic models for chemical
  reactions*, J. Chem. Phys. 57 (1972) 2976–2978.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 6, §4 and ch. 11, §2 (Theorem 2.1).
* D. F. Anderson and T. G. Kurtz, *Stochastic Analysis of Biochemical Systems*, Springer (2015).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExt.Biology.Dynamics.StochasticCRNLLN

open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
open MathlibExt.Biology.Dynamics.ComplexBalanced
open MathlibExt.Biology.Epidemiology.StochasticSIR (tendsto_measure_poissonClock)

variable {S ρ : Type*}

/-! ### Reaction vectors, norms and the mean-field equation -/

/-- The reaction vector `ζ_r = prod r - src r` of reaction `r`, as a real vector. -/
def reactionVector (G : ReactionNetwork S ρ) (r : ρ) (i : S) : ℝ :=
  (G.prod r i : ℝ) - G.src r i

/-- The scaled state (concentration) `z / N` of a count vector `z`. -/
noncomputable def scaled (N : ℕ) (z : S → ℕ) : S → ℝ := fun i => (z i : ℝ) / N

section Fintype

variable [Fintype S]

/-- The `ℓ¹` norm `∑_i |u_i|` of a real vector. -/
noncomputable def l1Norm (u : S → ℝ) : ℝ := ∑ i, |u i|

theorem l1Norm_nonneg (u : S → ℝ) : 0 ≤ l1Norm u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The sup norm is at most the `ℓ¹` norm. -/
theorem norm_le_l1Norm (u : S → ℝ) : ‖u‖ ≤ l1Norm u :=
  (pi_norm_le_iff_of_nonneg (l1Norm_nonneg u)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |u j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)

/-- The sum `Z = ∑_r ‖ζ_r‖₁` of the `ℓ¹` norms of the reaction vectors. -/
noncomputable def stoichNorm [Fintype ρ] (G : ReactionNetwork S ρ) : ℝ :=
  ∑ r, l1Norm (reactionVector G r)

theorem stoichNorm_nonneg [Fintype ρ] (G : ReactionNetwork S ρ) : 0 ≤ stoichNorm G :=
  Finset.sum_nonneg fun _ _ => l1Norm_nonneg _

/-- The `ℓ¹` distance at time `t` between the scaled chain `X / N` and a deterministic path `x`. -/
noncomputable def deviation (N : ℕ) (X : ℝ → S → ℕ) (x : ℝ → S → ℝ) (t : ℝ) : ℝ :=
  l1Norm (scaled N (X t) - x t)

theorem deviation_nonneg (N : ℕ) (X : ℝ → S → ℕ) (x : ℝ → S → ℝ) (t : ℝ) :
    0 ≤ deviation N X x t :=
  l1Norm_nonneg _

end Fintype

variable [Fintype ρ]

/-- The internal clock of reaction `r` at time `t`: the integrated propensity
`∫₀ᵗ λ_r(X(s)) ds`, truncated at `0` so it can index a counting process. -/
noncomputable def clock (C : StochasticCRN S ρ) (r : ρ) (X : ℝ → S → ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (∫ s in (0 : ℝ)..t, C.propensity r (X s))

/-- The scaled clock `(1 / N) ∫₀ᵗ λ_r(X(s)) ds` of reaction `r`. -/
noncomputable def scaledClock (N : ℕ) (C : StochasticCRN S ρ) (X : ℝ → S → ℕ) (r : ρ) (t : ℝ) :
    ℝ :=
  (∫ s in (0 : ℝ)..t, C.propensity r (X s)) / N

/-- **One sample path of a stochastic reaction network** in Kurtz's random time-change
representation (Ethier–Kurtz 1986, ch. 6, (4.1); Anderson–Kurtz 2015): given paths `y r`
of the driving unit-rate counting processes, one per reaction, the counts satisfy, for `t ≥ 0`,

  `X(t) = X(0) + ∑_r y_r(∫₀ᵗ λ_r(X(s)) ds) (prod r - src r)`.

When the `y r` are independent unit-rate Poisson processes, this is the Markov chain in which
reaction `r` fires at rate `λ_r(X)`. The coordinates are required to be measurable (a càdlàg path
is) and the propensities locally integrable along the path (they are locally bounded along a
non-explosive path), so that the clocks are genuine Lebesgue integrals. -/
structure IsChainPath (C : StochasticCRN S ρ) (y : ρ → ℝ≥0 → ℕ) (X : ℝ → S → ℕ) : Prop where
  /-- Each coordinate of the path is measurable. -/
  measurable_coord : ∀ i, Measurable fun t => X t i
  /-- The propensities are integrable along the path on every `[0, t]`. -/
  intervalIntegrable_propensity : ∀ r t,
    IntervalIntegrable (fun s => C.propensity r (X s)) volume 0 t
  /-- The random time-change equation. -/
  coord_eq : ∀ t, 0 ≤ t → ∀ i,
    (X t i : ℝ) = X 0 i + ∑ r, (y r (clock C r X t) : ℝ) * reactionVector C.network r i

/-- `x` solves the **mean-field equation** `x' = ∑_r β_r(x) ζ_r` of the network `G` with
macroscopic rate functions `β` on `t ≥ 0`. -/
structure IsSolution (G : ReactionNetwork S ρ) (β : ρ → (S → ℝ) → ℝ) (x : ℝ → S → ℝ) :
    Prop where
  /-- Each coordinate has the mean-field derivative. -/
  hasDerivAt : ∀ t, 0 ≤ t → ∀ i,
    HasDerivAt (fun τ => x τ i) (∑ r, β r (x t) * reactionVector G r i) t

namespace IsSolution

variable {G : ReactionNetwork S ρ} {β : ρ → (S → ℝ) → ℝ} {x : ℝ → S → ℝ}

theorem continuousOn (h : IsSolution G β x) : ContinuousOn x (Ici 0) :=
  continuousOn_pi.2 fun i t ht => (h.hasDerivAt t ht i).continuousAt.continuousWithinAt

/-- The integral form of the mean-field equation. -/
theorem eq_add_integral (h : IsSolution G β x) {t : ℝ} (ht : 0 ≤ t)
    (hβx : ∀ r, ContinuousOn (fun s => β r (x s)) (Icc 0 t)) (i : S) :
    x t i = x 0 i + ∑ r, (∫ s in (0 : ℝ)..t, β r (x s)) * reactionVector G r i := by
  have hii : ∀ r, IntervalIntegrable (fun s => β r (x s)) volume 0 t := fun r =>
    (hβx r).intervalIntegrable_of_Icc ht
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := fun τ => x τ i) (f' := fun s => ∑ r, β r (x s) * reactionVector G r i)
    (fun s hs => h.hasDerivAt s (by rw [uIcc_of_le ht] at hs; exact hs.1) i)
    (ContinuousOn.intervalIntegrable_of_Icc ht
      (continuousOn_finsetSum _ fun r _ => (hβx r).mul continuousOn_const))
  rw [intervalIntegral.integral_finsetSum (fun r _ => (hii r).mul_const _)] at this
  simp only [intervalIntegral.integral_mul_const] at this
  linarith

end IsSolution

/-! ### Kurtz's pathwise estimate -/

private theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

namespace IsChainPath

variable {C : StochasticCRN S ρ} {y : ρ → ℝ≥0 → ℕ} {X : ℝ → S → ℕ}
  {β : ρ → (S → ℝ) → ℝ} {x : ℝ → S → ℝ} {N : ℕ}

/-- The time-change equation in scaled form:
`X(t) / N = X(0) / N + ∑_r (y_r(N Λ_r(t)) / N) ζ_r` with `Λ_r` the scaled clock. -/
theorem scaled_coord_eq (h : IsChainPath C y X) (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) (i : S) :
    (X t i : ℝ) / N = (X 0 i : ℝ) / N + ∑ r,
      (y r (Real.toNNReal (N * scaledClock N C X r t)) : ℝ) / N * reactionVector C.network r i := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [h.coord_eq t ht i, add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  have : (N : ℝ) * scaledClock N C X r t = ∫ s in (0 : ℝ)..t, C.propensity r (X s) := by
    unfold scaledClock
    field_simp
  rw [this, clock, div_mul_eq_mul_div]

omit [Fintype ρ] in
theorem scaledClock_nonneg (r : ρ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ scaledClock N C X r t :=
  div_nonneg (intervalIntegral.integral_nonneg ht fun _ _ => C.propensity_nonneg r _)
    (Nat.cast_nonneg _)

/-- If the scaled propensities along the path are at most `B` on `(0, t)`, then the scaled clock
at `t` is at most `B t`. -/
theorem scaledClock_le (h : IsChainPath C y X) (hN : 0 < N) (r : ρ) {t B : ℝ} (ht : 0 ≤ t)
    (hB : ∀ s ∈ Ioo 0 t, C.propensity r (X s) / N ≤ B) : scaledClock N C X r t ≤ B * t := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hle : (∫ s in (0 : ℝ)..t, C.propensity r (X s)) ≤ ∫ s in (0 : ℝ)..t, (N * B : ℝ) :=
    intervalIntegral.integral_mono_on_of_le_Ioo ht (h.intervalIntegrable_propensity r t)
      intervalIntegrable_const fun s hs => by
        have := hB s hs
        rw [div_le_iff₀ hNr] at this
        linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  unfold scaledClock
  rw [div_le_iff₀ hNr]
  linarith

variable [Fintype S] {T δ L e B η : ℝ}

/-- **The integral inequality.** At a time `t ∈ [0, T]` before which the scaled path stays in the
`δ`-tube around `x`, the deviation satisfies
`dev(t) ≤ dev(0) + Z (η + e T) + L Z ∫₀ᵗ dev`. -/
theorem deviation_le_add_integral (h : IsChainPath C y X) (hN : 0 < N)
    (hode : IsSolution C.network β x) (he : 0 ≤ e) (hB : 0 ≤ B) {t : ℝ}
    (ht : t ∈ Icc 0 T)
    (hβx : ∀ r, ContinuousOn (fun s => β r (x s)) (Icc 0 T))
    (hrate : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      |C.propensity r z / N - β r (x s)| ≤ e + L * l1Norm (scaled N z - x s))
    (hbound : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      C.propensity r z / N ≤ B)
    (hclock : ∀ r, ∀ a ∈ Icc 0 ((B + 1) * T), |(y r (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η)
    (htube : ∀ s ∈ Ico 0 t, deviation N X x s < δ)
    (hint : IntervalIntegrable (deviation N X x) volume 0 t) :
    deviation N X x t ≤ deviation N X x 0 + stoichNorm C.network * (η + e * T) +
      L * stoichNorm C.network * ∫ s in (0 : ℝ)..t, deviation N X x s := by
  obtain ⟨ht0, htT⟩ := ht
  have hT : 0 ≤ T := ht0.trans htT
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hβii : ∀ r, IntervalIntegrable (fun s => β r (x s)) volume 0 t := fun r =>
    ((hβx r).mono (Icc_subset_Icc_right htT)).intervalIntegrable_of_Icc ht0
  -- the clocks stay in the range where the clock bound applies
  have hΛ : ∀ r, scaledClock N C X r t ∈ Icc 0 ((B + 1) * T) := fun r =>
    ⟨scaledClock_nonneg r ht0, (h.scaledClock_le hN r ht0 fun s hs =>
      hbound r s ⟨hs.1.le, hs.2.le.trans htT⟩ (X s) (htube s ⟨hs.1.le, hs.2⟩)).trans
        (by nlinarith)⟩
  -- the drift error
  have hdrift : ∀ r, |scaledClock N C X r t - ∫ s in (0 : ℝ)..t, β r (x s)| ≤
      e * t + L * ∫ s in (0 : ℝ)..t, deviation N X x s := by
    intro r
    have hsub : scaledClock N C X r t - ∫ s in (0 : ℝ)..t, β r (x s) =
        ∫ s in (0 : ℝ)..t, (C.propensity r (X s) / N - β r (x s)) := by
      rw [intervalIntegral.integral_sub ((h.intervalIntegrable_propensity r t).div_const _)
        (hβii r), intervalIntegral.integral_div]
      rfl
    have hg : IntervalIntegrable (fun s => e + L * deviation N X x s) volume 0 t :=
      intervalIntegrable_const.add (hint.const_mul L)
    rw [hsub, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le ht0 ?_ hg).trans (le_of_eq ?_)
    · filter_upwards [Measure.ae_ne volume t] with s hst hs
      have hs' : s ∈ Ico 0 t := ⟨hs.1.le, lt_of_le_of_ne hs.2 hst⟩
      rw [Real.norm_eq_abs]
      exact hrate r s ⟨hs'.1, hs'.2.le.trans htT⟩ (X s) (htube s hs')
    · rw [intervalIntegral.integral_add intervalIntegrable_const (hint.const_mul L),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul,
        sub_zero, mul_comm t e]
  -- the total error per reaction
  set U := ∫ s in (0 : ℝ)..t, deviation N X x s with hU
  set Er : ρ → ℝ := fun r => (y r (Real.toNNReal (N * scaledClock N C X r t)) : ℝ) / N -
    ∫ s in (0 : ℝ)..t, β r (x s) with hEr
  have hE : ∀ r, |Er r| ≤ η + e * T + L * U := by
    intro r
    have h1 := hclock r _ (hΛ r)
    have h2 := hdrift r
    have h3 : e * t ≤ e * T := mul_le_mul_of_nonneg_left htT he
    calc |Er r| ≤ |(y r (Real.toNNReal (N * scaledClock N C X r t)) : ℝ) / N -
          scaledClock N C X r t| + |scaledClock N C X r t - ∫ s in (0 : ℝ)..t, β r (x s)| :=
          abs_sub_le _ _ _
      _ ≤ η + e * T + L * U := by linarith
  -- coordinates
  have hcoord : ∀ i, (X t i : ℝ) / N - x t i =
      ((X 0 i : ℝ) / N - x 0 i) + ∑ r, Er r * reactionVector C.network r i := by
    intro i
    rw [h.scaled_coord_eq hN ht0 i,
      hode.eq_add_integral ht0 (fun r => (hβx r).mono (Icc_subset_Icc_right htT)) i]
    simp only [hEr, sub_mul, Finset.sum_sub_distrib]
    ring
  calc deviation N X x t = ∑ i, |(X t i : ℝ) / N - x t i| := rfl
    _ = ∑ i, |((X 0 i : ℝ) / N - x 0 i) + ∑ r, Er r * reactionVector C.network r i| :=
        Finset.sum_congr rfl fun i _ => by rw [hcoord i]
    _ ≤ ∑ i, (|(X 0 i : ℝ) / N - x 0 i| + ∑ r, |Er r| * |reactionVector C.network r i|) := by
        refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans (add_le_add_right ?_ _)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun r _ => abs_mul _ _
    _ = deviation N X x 0 + ∑ r, |Er r| * l1Norm (reactionVector C.network r) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rfl
    _ ≤ deviation N X x 0 + ∑ r, (η + e * T + L * U) * l1Norm (reactionVector C.network r) := by
        gcongr with r
        · exact l1Norm_nonneg _
        · exact hE r
    _ = _ := by
        rw [← Finset.mul_sum]
        unfold stoichNorm
        ring

/-- **Gronwall inside the tube.** If the scaled path stays in the `δ`-tube before `t₁ ≤ T`, then
`dev(t) ≤ (dev(0) + Z (η + e T)) e^{L Z t}` on `[0, t₁]`. -/
theorem deviation_le_of_tube (h : IsChainPath C y X) (hN : 0 < N)
    (hode : IsSolution C.network β x) (hL : 0 ≤ L) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hβx : ∀ r, ContinuousOn (fun s => β r (x s)) (Icc 0 T))
    (hrate : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      |C.propensity r z / N - β r (x s)| ≤ e + L * l1Norm (scaled N z - x s))
    (hbound : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      C.propensity r z / N ≤ B)
    (hclock : ∀ r, ∀ a ∈ Icc 0 ((B + 1) * T), |(y r (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc 0 T) (htube : ∀ s ∈ Ico 0 t₁, deviation N X x s < δ) :
    ∀ t ∈ Icc 0 t₁, deviation N X x t ≤
      (deviation N X x 0 + stoichNorm C.network * (η + e * T)) *
        exp (L * stoichNorm C.network * t) := by
  have hxc := hode.continuousOn
  have hmeas : AEStronglyMeasurable (deviation N X x) (volume.restrict (Icc 0 t₁)) := by
    have : deviation N X x = fun s => ∑ i, |(X s i : ℝ) / N - x s i| := rfl
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    refine continuous_abs.comp_aestronglyMeasurable (AEStronglyMeasurable.sub ?_ ?_)
    · exact ((measurable_from_nat.comp (h.measurable_coord i)).div_const _).aestronglyMeasurable
    · exact ((continuous_apply i).comp_continuousOn
        (hxc.mono fun s hs => hs.1)).aestronglyMeasurable measurableSet_Icc
  have hbd : ∀ s ∈ Icc 0 t₁, ‖deviation N X x s‖ ≤ max δ (deviation N X x t₁) := by
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (deviation_nonneg _ _ _ _)]
    rcases eq_or_lt_of_le hs.2 with hst | hst
    · rw [hst]; exact le_max_right _ _
    · exact (htube s ⟨hs.1, hst⟩).le.trans (le_max_left _ _)
  have hInt : IntegrableOn (deviation N X x) (Icc 0 t₁) :=
    IntegrableOn.of_bound measure_Icc_lt_top hmeas _
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hbd))
  refine MathlibExt.Analysis.ODE.le_mul_exp_of_le_add_integral
    (mul_nonneg hL (stoichNorm_nonneg _)) hInt (fun t _ => deviation_nonneg _ _ _ _) ?_
  intro t ht
  exact h.deviation_le_add_integral hN hode he hB ⟨ht.1, ht.2.trans ht₁.2⟩ hβx hrate hbound
    hclock (fun s hs => htube s ⟨hs.1, hs.2.trans_le ht.2⟩)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      (hInt.mono_set (Icc_subset_Icc_right ht.2)))

/-- **Leaving the tube needs a jump the clocks forbid.** If the deviation is at most `A` on
`[0, t₀]` with `t₀ < T` and `A + 2 η Z < δ`, then the path stays in the `δ`-tube on
`[t₀, t₀ + ε)` for some `ε > 0`. Each jump of `y_r(N ·) / N` is at most `2 η` by the clock bound,
and the clocks and `x` are continuous. -/
theorem exists_tube_right (h : IsChainPath C y X) (hN : 0 < N)
    (hode : IsSolution C.network β x) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hbound : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      C.propensity r z / N ≤ B)
    (hclock : ∀ r, ∀ a ∈ Icc 0 ((B + 1) * T), |(y r (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η)
    {A t₀ : ℝ} (ht₀ : t₀ ∈ Ico 0 T) (hdev : ∀ s ∈ Icc 0 t₀, deviation N X x s ≤ A)
    (hsmall : A + 2 * η * stoichNorm C.network < δ) :
    ∃ ε > 0, ∀ s ∈ Ico t₀ (t₀ + ε), deviation N X x s < δ := by
  obtain ⟨ht₀0, ht₀T⟩ := ht₀
  have hZ := stoichNorm_nonneg C.network
  have hAδ : A < δ := by nlinarith
  set ζ := reactionVector C.network with hζ
  have hii : ∀ r a b, IntervalIntegrable (fun s => C.propensity r (X s)) volume a b :=
    fun r a b => (h.intervalIntegrable_propensity r a).symm.trans
      (h.intervalIntegrable_propensity r b)
  have hΛc : ∀ r, Continuous (scaledClock N C X r) := fun r =>
    (intervalIntegral.continuous_primitive (hii r) 0).div_const _
  have hΛt₀ : ∀ r, scaledClock N C X r t₀ < (B + 1) * T := by
    intro r
    have := h.scaledClock_le hN r ht₀0 fun s hs =>
      hbound r s ⟨hs.1.le, hs.2.le.trans ht₀T.le⟩ (X s)
        ((hdev s ⟨hs.1.le, hs.2.le⟩).trans_lt hAδ)
    nlinarith
  -- the modulus of continuity at `t₀`
  set g : ℝ → ℝ := fun t => l1Norm (x t - x t₀) +
    ∑ r, |scaledClock N C X r t - scaledClock N C X r t₀| * l1Norm (ζ r) with hg
  have hgt : Tendsto g (𝓝 t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t => l1Norm (x t - x t₀)) (𝓝 t₀) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset S) fun i _ =>
        ((hode.hasDerivAt t₀ ht₀0 i).continuousAt.tendsto.sub_const (x t₀ i)).abs
      simpa [l1Norm] using this
    have h2 : Tendsto (fun t => ∑ r, |scaledClock N C X r t - scaledClock N C X r t₀| *
        l1Norm (ζ r)) (𝓝 t₀) (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ρ) fun r _ =>
        ((((hΛc r).tendsto t₀).sub_const (scaledClock N C X r t₀)).abs.mul_const
          (l1Norm (ζ r)))
      simpa using this
    simpa using h1.add h2
  have hgap : 0 < δ - A - 2 * η * stoichNorm C.network := by linarith
  have hev : ∀ᶠ t in 𝓝 t₀, g t < δ - A - 2 * η * stoichNorm C.network ∧
      ∀ r, scaledClock N C X r t < (B + 1) * T :=
    (hgt.eventually (gt_mem_nhds hgap)).and (eventually_all.2 fun r =>
      ((hΛc r).tendsto t₀).eventually (gt_mem_nhds (hΛt₀ r)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hs0 : 0 ≤ s := ht₀0.trans hs.1
  have hdist : dist s t₀ < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
    linarith [hs.2]
  obtain ⟨hgs, hΛs⟩ := hball hdist
  -- the jump of each scaled clock path between `t₀` and `s`
  set Yt : ρ → ℝ → ℝ := fun r t => (y r (Real.toNNReal (N * scaledClock N C X r t)) : ℝ) / N
    with hYt
  have hjump : ∀ r, |Yt r s - Yt r t₀| ≤
      |scaledClock N C X r s - scaledClock N C X r t₀| + 2 * η := by
    intro r
    have h1 := hclock r _ ⟨scaledClock_nonneg r hs0, (hΛs r).le⟩
    have h2 := hclock r _ ⟨scaledClock_nonneg r ht₀0, (hΛt₀ r).le⟩
    have h3 := le_abs_self (scaledClock N C X r s - scaledClock N C X r t₀)
    have h4 := neg_abs_le (scaledClock N C X r s - scaledClock N C X r t₀)
    simp only [hYt]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hcoord : ∀ i, (X s i : ℝ) / N - x s i = ((X t₀ i : ℝ) / N - x t₀ i) -
      (x s i - x t₀ i) + ∑ r, (Yt r s - Yt r t₀) * ζ r i := by
    intro i
    rw [h.scaled_coord_eq hN hs0 i, h.scaled_coord_eq hN ht₀0 i]
    simp only [hYt, hζ, sub_mul, Finset.sum_sub_distrib]
    ring
  calc deviation N X x s = ∑ i, |(X s i : ℝ) / N - x s i| := rfl
    _ = ∑ i, |((X t₀ i : ℝ) / N - x t₀ i) - (x s i - x t₀ i) +
          ∑ r, (Yt r s - Yt r t₀) * ζ r i| := Finset.sum_congr rfl fun i _ => by rw [hcoord i]
    _ ≤ ∑ i, (|(X t₀ i : ℝ) / N - x t₀ i| + |x s i - x t₀ i| +
          ∑ r, |Yt r s - Yt r t₀| * |ζ r i|) := by
        refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans
          (add_le_add (abs_sub_le_abs_add_abs _ _) ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun r _ => abs_mul _ _
    _ = deviation N X x t₀ + l1Norm (x s - x t₀) + ∑ r, |Yt r s - Yt r t₀| * l1Norm (ζ r) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rfl
    _ ≤ deviation N X x t₀ + l1Norm (x s - x t₀) +
          ∑ r, (|scaledClock N C X r s - scaledClock N C X r t₀| + 2 * η) * l1Norm (ζ r) := by
        gcongr with r
        · exact l1Norm_nonneg _
        · exact hjump r
    _ = deviation N X x t₀ + g s + 2 * η * stoichNorm C.network := by
        simp only [hg, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, stoichNorm, hζ]
        ring
    _ < δ := by
        have := hdev t₀ ⟨ht₀0, le_rfl⟩
        linarith

/-- **Kurtz's pathwise estimate** (Kurtz 1970; Ethier–Kurtz 1986, ch. 11, proof of Thm 2.1),
localized to the `δ`-tube around the deterministic trajectory. Let `X` be a chain path of a
network with propensities `λ_r` and `x` a solution of the mean-field equation `x' = ∑_r β_r(x) ζ_r`.
Suppose that on the `δ`-tube around `x` over `[0, T]`

* the scaled propensities are close to `β` along the trajectory,
  `|λ_r(z) / N - β_r(x(s))| ≤ e + L ‖z / N - x(s)‖₁`, and bounded by `B`, and
* the scaled clocks are within `η` of the identity on `[0, (B + 1) T]`,
  `|y_r(N a) / N - a| ≤ η`.

With `Z = ∑_r ‖ζ_r‖₁` and `A = dev(0) + Z (η + e T)`, if `A e^{L Z T} + 2 η Z < δ` then

  `‖X(t) / N - x(t)‖₁ ≤ A e^{L Z t}` for all `t ∈ [0, T]`.

Proof: let `t₀` be the supremum of the times before which the path stays in the tube. Gronwall's
inequality bounds the deviation by `A e^{L Z t}` on `[0, t₀]`; if `t₀ < T`, the bounded jumps and
continuity of the clocks keep the path in the tube a little longer, a contradiction. -/
theorem deviation_le (h : IsChainPath C y X) (hN : 0 < N) (hode : IsSolution C.network β x)
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hη : 0 ≤ η) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hβx : ∀ r, ContinuousOn (fun s => β r (x s)) (Icc 0 T))
    (hrate : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      |C.propensity r z / N - β r (x s)| ≤ e + L * l1Norm (scaled N z - x s))
    (hbound : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
      C.propensity r z / N ≤ B)
    (hclock : ∀ r, ∀ a ∈ Icc 0 ((B + 1) * T), |(y r (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η)
    (hsmall : (deviation N X x 0 + stoichNorm C.network * (η + e * T)) *
      exp (L * stoichNorm C.network * T) + 2 * η * stoichNorm C.network < δ) :
    ∀ t ∈ Icc 0 T, deviation N X x t ≤
      (deviation N X x 0 + stoichNorm C.network * (η + e * T)) *
        exp (L * stoichNorm C.network * t) := by
  have hZ := stoichNorm_nonneg C.network
  set A := deviation N X x 0 + stoichNorm C.network * (η + e * T) with hA
  have hA0 : 0 ≤ A := add_nonneg (deviation_nonneg _ _ _ _)
    (mul_nonneg hZ (add_nonneg hη (mul_nonneg he hT)))
  set G : Set ℝ := {t | t ∈ Icc 0 T ∧ ∀ s ∈ Ico 0 t, deviation N X x s < δ} with hG
  have hG0 : (0 : ℝ) ∈ G := ⟨⟨le_rfl, hT⟩, fun s hs => absurd hs.2 (not_lt.2 hs.1)⟩
  have hGbdd : BddAbove G := ⟨T, fun t ht => ht.1.2⟩
  have ht₀T : sSup G ≤ T := csSup_le ⟨0, hG0⟩ fun t ht => ht.1.2
  have ht₀0 : 0 ≤ sSup G := le_csSup hGbdd hG0
  have htube : ∀ s ∈ Ico 0 (sSup G), deviation N X x s < δ := fun s hs => by
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup ⟨0, hG0⟩ hs.2
    exact ht.2 s ⟨hs.1, hst⟩
  have hgr := h.deviation_le_of_tube hN hode hL he hB hβx hrate hbound hclock
    ⟨ht₀0, ht₀T⟩ htube
  rcases eq_or_lt_of_le ht₀T with heq | hlt
  · intro t ht
    exact hgr t (heq ▸ ht)
  · exfalso
    have hexp : ∀ s ∈ Icc 0 (sSup G), deviation N X x s ≤
        A * exp (L * stoichNorm C.network * T) := fun s hs =>
      (hgr s hs).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2
        (mul_le_mul_of_nonneg_left (hs.2.trans ht₀T) (mul_nonneg hL hZ))) hA0)
    obtain ⟨ε, hε, hright⟩ := h.exists_tube_right hN hode hB hη hbound hclock
      ⟨ht₀0, hlt⟩ hexp hsmall
    set t' := sSup G + min (ε / 2) ((T - sSup G) / 2) with ht'
    have hm1 : 0 < min (ε / 2) ((T - sSup G) / 2) := lt_min (half_pos hε) (by linarith)
    have hm2 : min (ε / 2) ((T - sSup G) / 2) ≤ ε / 2 := min_le_left _ _
    have hm3 : min (ε / 2) ((T - sSup G) / 2) ≤ (T - sSup G) / 2 := min_le_right _ _
    have ht'G : t' ∈ G := by
      refine ⟨⟨by linarith, by linarith⟩, fun s hs => ?_⟩
      rcases lt_or_ge s (sSup G) with hs' | hs'
      · exact htube s ⟨hs.1, hs'⟩
      · exact hright s ⟨hs', by linarith [hs.2]⟩
    have := le_csSup hGbdd ht'G
    linarith

end IsChainPath

/-! ### Kurtz's theorem -/

section Kurtz

variable [Fintype S] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {G : ReactionNetwork S ρ} {C : ℕ → StochasticCRN S ρ}
  {β : ρ → (S → ℝ) → ℝ} {Y : ℕ → ρ → ℝ≥0 → Ω → ℕ} {X : ℕ → Ω → ℝ → S → ℕ}
  {x : ℝ → S → ℝ}

/-- **Kurtz's law of large numbers for density-dependent stochastic reaction networks**
(Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1). Let `C N` be stochastic reaction
networks on the reaction network `G`, indexed by the system size `N`, and `β_r` locally Lipschitz
macroscopic rate functions such that the scaled propensities converge uniformly on bounded sets,

  `sup_{‖z / N‖ ≤ R} |λ^N_r(z) / N - β_r(z / N)| → 0`  for every `R`.

For each `N` let `X N` be the chain driven by unit-rate Poisson processes `Y N r`, i.e. almost
every sample path solves the random time-change equations of `IsChainPath`. Let `x` solve the
mean-field equation `x' = ∑_r β_r(x) ζ_r`. If the scaled initial state converges to `x(0)` in
probability, then the scaled chain converges to `x` in probability, uniformly on every `[0, T]`:

  `P(∃ t ∈ [0, T], ‖X^N(t) / N - x(t)‖₁ ≥ ε) → 0`  as `N → ∞`.

The event is not assumed measurable; `μ` is applied as an outer measure. -/
theorem tendsto_measure_deviation (hnet : ∀ N, (C N).network = G)
    (hβ : ∀ r, LocallyLipschitz (β r))
    (happrox : ∀ R : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ r (z : S → ℕ),
      ‖scaled N z‖ ≤ R → |(C N).propensity r z / N - β r (scaled N z)| ≤ e N)
    (hY : ∀ N r, IsPoissonProcess (Y N r) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath (C N) (fun r u => Y N r u ω) (X N ω))
    (hode : IsSolution G β x)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | δ ≤ deviation N (X N ω) x 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (X N ω) x t}) atTop (𝓝 0) := by
  rcases lt_or_ge T 0 with hT | hT
  · have hempty : ∀ N : ℕ, {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (X N ω) x t} = ∅ := fun N => by
      ext ω
      simp [Icc_eq_empty (not_le.2 hT)]
    simp only [hempty, measure_empty]
    exact tendsto_const_nhds
  -- the trajectory on `[0, T]` lies in a ball of radius `R₀`
  have hxc : ContinuousOn x (Icc 0 T) := hode.continuousOn.mono fun t ht => ht.1
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hxc
  have hR₀0 : 0 ≤ R₀ := (norm_nonneg _).trans (hR₀ 0 ⟨le_rfl, hT⟩)
  set R : ℝ := R₀ + 1 with hR
  have hR0 : 0 ≤ R := by linarith
  have htubeR : ∀ s ∈ Icc 0 T, ∀ u : S → ℝ, l1Norm (u - x s) < 1 →
      u ∈ Metric.closedBall (0 : S → ℝ) R := by
    intro s hs u hu
    rw [mem_closedBall_zero_iff]
    calc ‖u‖ = ‖x s + (u - x s)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x s‖ + ‖u - x s‖ := norm_add_le _ _
      _ ≤ R₀ + 1 := add_le_add (hR₀ s hs) ((norm_le_l1Norm _).trans hu.le)
  have hxR : ∀ s ∈ Icc 0 T, x s ∈ Metric.closedBall (0 : S → ℝ) R := fun s hs =>
    htubeR s hs (x s) (by simp [l1Norm])
  have h0R : (0 : S → ℝ) ∈ Metric.closedBall (0 : S → ℝ) R := Metric.mem_closedBall_self hR0
  -- Lipschitz constants and bounds on the ball
  have hK : ∀ r, ∃ K, LipschitzOnWith K (β r) (Metric.closedBall (0 : S → ℝ) R) := fun r =>
    (hβ r).locallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall _ _)
  choose K hK using hK
  set L : ℝ := ∑ r, (K r : ℝ) with hLdef
  have hL : 0 ≤ L := Finset.sum_nonneg fun r _ => (K r).2
  have hKL : ∀ r, (K r : ℝ) ≤ L := fun r =>
    Finset.single_le_sum (f := fun r => (K r : ℝ)) (fun r _ => (K r).2) (Finset.mem_univ r)
  have hLip : ∀ r, ∀ u ∈ Metric.closedBall (0 : S → ℝ) R,
      ∀ v ∈ Metric.closedBall (0 : S → ℝ) R, |β r u - β r v| ≤ L * l1Norm (u - v) := by
    intro r u hu v hv
    have := (hK r).dist_le_mul u hu v hv
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul (hKL r) (norm_le_l1Norm _) (norm_nonneg _) hL)
  set Bβ : ℝ := ∑ r, |β r 0| + L * R with hBβ
  have hBβ0 : 0 ≤ Bβ := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg hL hR0)
  have hβbd : ∀ r, ∀ u ∈ Metric.closedBall (0 : S → ℝ) R, β r u ≤ Bβ := by
    intro r u hu
    have h1 := (hK r).dist_le_mul u hu 0 h0R
    rw [Real.dist_eq, dist_zero_right] at h1
    have h2 : ‖u‖ ≤ R := mem_closedBall_zero_iff.1 hu
    have h3 : |β r 0| ≤ ∑ r, |β r 0| := Finset.single_le_sum (f := fun r => |β r 0|)
      (fun r _ => abs_nonneg _) (Finset.mem_univ r)
    have h4 : (K r : ℝ) * ‖u‖ ≤ L * R := mul_le_mul (hKL r) h2 (norm_nonneg _) hL
    have h5 := le_abs_self (β r u - β r 0)
    have h6 := le_abs_self (β r 0)
    linarith
  have hβx : ∀ r, ContinuousOn (fun s => β r (x s)) (Icc 0 T) := fun r =>
    (hK r).continuousOn.comp hxc fun s hs => hxR s hs
  -- the propensity error on the ball
  obtain ⟨e₀, he₀, he₀bd⟩ := happrox R
  set e : ℕ → ℝ := fun N => max (e₀ N) 0 with hedef
  have he : Tendsto e atTop (𝓝 0) := by
    simpa using he₀.max (tendsto_const_nhds (x := (0 : ℝ)))
  -- the constants
  set Z : ℝ := stoichNorm G with hZdef
  have hZ : 0 ≤ Z := stoichNorm_nonneg G
  set B : ℝ := Bβ + 1 with hBdef
  have hB : 0 ≤ B := by linarith
  set E : ℝ := exp (L * Z * T) with hEdef
  have hE : 0 < E := exp_pos _
  set δ : ℝ := min 1 ε with hδdef
  have hδ : 0 < δ := lt_min one_pos hε
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  set δ₀ : ℝ := δ / (4 * E) with hδ₀def
  have hδ₀ : 0 < δ₀ := div_pos hδ (by linarith)
  have hden : 0 < 4 * (Z * E + 2 * Z + 1) := by nlinarith [mul_nonneg hZ hE.le]
  set η : ℝ := δ / (4 * (Z * E + 2 * Z + 1)) with hηdef
  have hη : 0 < η := div_pos hδ hden
  have hηZ : η * (Z * E + 2 * Z) ≤ δ / 4 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
    nlinarith [mul_nonneg hZ hE.le]
  have hZe : Tendsto (fun N => Z * e N * T * E) atTop (𝓝 0) := by
    simpa using ((he.const_mul Z).mul_const T).mul_const E
  -- the bad events
  set Bad₀ : ℕ → Set Ω := fun N => {ω | ¬ IsChainPath (C N) (fun r u => Y N r u ω) (X N ω)}
    with hBad₀def
  set Bad₁ : ℕ → Set Ω := fun N => {ω | δ₀ ≤ deviation N (X N ω) x 0} with hBad₁def
  set Bad₂ : ℕ → ρ → Set Ω := fun N r =>
    {ω | ∃ a ∈ Icc 0 ((B + 1) * T), η < |(Y N r (Real.toNNReal (N * a)) ω : ℝ) / N - a|}
    with hBad₂def
  have hBad₀ : ∀ N, μ (Bad₀ N) = 0 := fun N => ae_iff.1 (hchain N)
  have hsub : ∀ N, 0 < N → e N < 1 → Z * e N * T * E < δ / 4 →
      (∀ r (z : S → ℕ), ‖scaled N z‖ ≤ R → |(C N).propensity r z / N - β r (scaled N z)| ≤ e₀ N) →
      {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (X N ω) x t} ⊆ (Bad₀ N ∪ Bad₁ N) ∪ ⋃ r, Bad₂ N r := by
    intro N hN heN1 heN hbdN ω ⟨t, ht, hle⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists, Bad₀, Bad₁, Bad₂, mem_ofPred_eq,
      not_not, not_le, not_and, not_lt] at hcon
    obtain ⟨⟨hpath, hdev0⟩, hcl⟩ := hcon
    have he0 : 0 ≤ e N := le_max_right _ _
    have hodeN : IsSolution (C N).network β x := by rw [hnet N]; exact hode
    have hZN : stoichNorm (C N).network = Z := by rw [hnet N]
    have hrate : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
        |(C N).propensity r z / N - β r (x s)| ≤ e N + L * l1Norm (scaled N z - x s) := by
      intro r s hs z hz
      have hzR := htubeR s hs _ (hz.trans_le hδ1)
      have h1 : |(C N).propensity r z / N - β r (scaled N z)| ≤ e N :=
        (hbdN r z (mem_closedBall_zero_iff.1 hzR)).trans (le_max_left _ _)
      have h2 := hLip r _ hzR _ (hxR s hs)
      calc |(C N).propensity r z / N - β r (x s)|
          ≤ |(C N).propensity r z / N - β r (scaled N z)| + |β r (scaled N z) - β r (x s)| :=
            abs_sub_le _ _ _
        _ ≤ e N + L * l1Norm (scaled N z - x s) := add_le_add h1 h2
    have hbound : ∀ r, ∀ s ∈ Icc 0 T, ∀ z : S → ℕ, l1Norm (scaled N z - x s) < δ →
        (C N).propensity r z / N ≤ B := by
      intro r s hs z hz
      have hzR := htubeR s hs _ (hz.trans_le hδ1)
      have h1 := hbdN r z (mem_closedBall_zero_iff.1 hzR)
      have h2 := hβbd r _ hzR
      have h3 := le_abs_self ((C N).propensity r z / N - β r (scaled N z))
      have h4 : e₀ N ≤ e N := le_max_left _ _
      linarith
    have hsmall : (deviation N (X N ω) x 0 + stoichNorm (C N).network * (η + e N * T)) *
        exp (L * stoichNorm (C N).network * T) + 2 * η * stoichNorm (C N).network < δ := by
      rw [hZN]
      have hd0 : deviation N (X N ω) x 0 * (4 * E) < δ := (lt_div_iff₀ (by linarith)).1 hdev0
      have hexp : (deviation N (X N ω) x 0 + Z * (η + e N * T)) * E + 2 * η * Z =
          deviation N (X N ω) x 0 * E + η * (Z * E + 2 * Z) + Z * e N * T * E := by ring
      rw [hexp]
      linarith
    have hbnd := hpath.deviation_le hN hodeN hT hL hη.le he0 hB hβx hrate hbound hcl hsmall t ht
    rw [hZN] at hbnd hsmall
    have hA0 : 0 ≤ deviation N (X N ω) x 0 + Z * (η + e N * T) :=
      add_nonneg (deviation_nonneg _ _ _ _) (mul_nonneg hZ (add_nonneg hη.le
        (mul_nonneg he0 hT)))
    have hexpt : exp (L * Z * t) ≤ E :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hL hZ))
    have := mul_le_mul_of_nonneg_left hexpt hA0
    have hηZ0 : 0 ≤ 2 * η * Z := by positivity
    linarith
  have hlim : Tendsto (fun N => (μ (Bad₀ N) + μ (Bad₁ N)) + ∑ r, μ (Bad₂ N r)) atTop
      (𝓝 ((0 + 0) + ∑ _r : ρ, (0 : ℝ≥0∞))) := by
    refine (Tendsto.add ?_ (hinit δ₀ hδ₀)).add (tendsto_finsetSum _ fun r _ => ?_)
    · simp only [hBad₀]
      exact tendsto_const_nhds
    · exact tendsto_measure_poissonClock (fun N => hY N r) ((B + 1) * T) hη
  simp only [add_zero, Finset.sum_const_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0, he.eventually (gt_mem_nhds one_pos),
    hZe.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ / 4)), he₀bd] with N hN he1 heZ hbdN
  refine (measure_mono (hsub N hN he1 heZ hbdN)).trans ((measure_union_le _ _).trans ?_)
  gcongr
  · exact measure_union_le _ _
  · exact measure_iUnion_fintype_le _ _

/-- **Kurtz's theorem, supremum form.** Under the hypotheses of `tendsto_measure_deviation`, the
supremum over `[0, T]` of the `ℓ¹` deviation between the scaled chain and the mean-field solution
is at least `ε` with probability tending to `0`. The supremum is taken in `ℝ≥0∞`, so it exists
for every path and need not be attained. -/
theorem tendsto_measure_iSup_deviation (hnet : ∀ N, (C N).network = G)
    (hβ : ∀ r, LocallyLipschitz (β r))
    (happrox : ∀ R : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ N in atTop, ∀ r (z : S → ℕ),
      ‖scaled N z‖ ≤ R → |(C N).propensity r z / N - β r (scaled N z)| ≤ e N)
    (hY : ∀ N r, IsPoissonProcess (Y N r) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath (C N) (fun r u => Y N r u ω) (X N ω))
    (hode : IsSolution G β x)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | δ ≤ deviation N (X N ω) x 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ENNReal.ofReal ε ≤
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (X N ω) x t)}) atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_deviation hnet hβ happrox hY hchain hode hinit T hε2)
    (fun _ => bot_le) (fun N => measure_mono fun ω hω => ?_)
  simp only [mem_ofPred_eq] at hω ⊢
  have hlt : ENNReal.ofReal (ε / 2) <
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (X N ω) x t) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)) hω
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
  obtain ⟨htT, hdev⟩ := lt_iSup_iff.1 ht
  exact ⟨t, htT, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε2.le).1 hdev).le⟩

/-- **Kurtz's theorem for exactly density-dependent propensities** `λ^N_r(z) = N β_r(z / N)`
(Kurtz 1970): the uniform-approximation hypothesis of `tendsto_measure_deviation` holds with no
error for `N ≥ 1`. -/
theorem tendsto_measure_deviation_of_eq (hnet : ∀ N, (C N).network = G)
    (hβ : ∀ r, LocallyLipschitz (β r))
    (hprop : ∀ N, 0 < N → ∀ r (z : S → ℕ), (C N).propensity r z = N * β r (scaled N z))
    (hY : ∀ N r, IsPoissonProcess (Y N r) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath (C N) (fun r u => Y N r u ω) (X N ω))
    (hode : IsSolution G β x)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | δ ≤ deviation N (X N ω) x 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (X N ω) x t}) atTop (𝓝 0) := by
  refine tendsto_measure_deviation hnet hβ (fun R => ⟨fun _ => 0, tendsto_const_nhds, ?_⟩) hY
    hchain hode hinit T hε
  filter_upwards [eventually_gt_atTop 0] with N hN r z _
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [hprop N hN r z, mul_div_cancel_left₀ _ hNr, sub_self, abs_zero]

omit [IsProbabilityMeasure μ] in
/-- Deterministic initial counts: if almost surely `X N 0 = z₀ N` and `z₀ N / N → x(0)`, then the
scaled initial state converges to `x(0)` in probability (the hypothesis `hinit` of
`tendsto_measure_deviation`). -/
theorem tendsto_measure_deviation_zero_of_initial {z₀ : ℕ → S → ℕ}
    (hX₀ : ∀ N, ∀ᵐ ω ∂μ, X N ω 0 = z₀ N)
    (hz₀ : Tendsto (fun N => scaled N (z₀ N)) atTop (𝓝 (x 0))) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N => μ {ω | δ ≤ deviation N (X N ω) x 0}) atTop (𝓝 0) := by
  have hdet : Tendsto (fun N => l1Norm (scaled N (z₀ N) - x 0)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset S) fun i _ =>
      ((tendsto_pi_nhds.1 hz₀ i).sub_const (x 0 i)).abs
    simpa [l1Norm] using this
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hdet.eventually (gt_mem_nhds hδ)] with N hN
  symm
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hX₀ N))
  simp only [mem_ofPred_eq] at hω ⊢
  intro h0
  unfold deviation at hω
  rw [h0] at hω
  linarith

end Kurtz

/-! ### Mass-action kinetics -/

section MassAction

/-- `|∏ a - ∏ b| ≤ M ^ |s| ∑ |a_i - b_i|` when all factors are bounded by `M ≥ 1`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} {M : ℝ}
    (hM : 1 ≤ M) (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ M ^ s.card * ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hM0 : 0 ≤ M := by linarith
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have haj := ha j (Finset.mem_insert_self j s)
    have hB : |∏ i ∈ s, b i| ≤ M ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |b i| ≤ ∏ _i ∈ s, M :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
              (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        _ = M ^ s.card := Finset.prod_const M
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj,
      Finset.card_insert_of_notMem hj]
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i| := by
          congr 1; ring
      _ ≤ |a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| + |(a j - b j) * ∏ i ∈ s, b i| :=
          abs_add_le _ _
      _ ≤ M * (M ^ s.card * ∑ i ∈ s, |a i - b i|) + |a j - b j| * M ^ s.card := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul haj ih' (abs_nonneg _) hM0)
            (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      _ ≤ M ^ (s.card + 1) * (|a j - b j| + ∑ i ∈ s, |a i - b i|) := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (a j - b j)) (pow_nonneg hM0 s.card))
            (sub_nonneg.2 hM)]

/-- The falling factorial `n (n - 1) ⋯ (n - k + 1)` as a real product (it vanishes for `n < k`). -/
theorem cast_descFactorial_eq_prod (n k : ℕ) :
    (n.descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((n : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul]
    rcases le_or_gt k n with hk | hk
    · rw [Nat.cast_sub hk, ih, mul_comm]
    · have h0 : (n.descFactorial k : ℝ) = 0 := by
        rw [Nat.descFactorial_eq_zero_iff_lt.2 hk, Nat.cast_zero]
      rw [h0, ← ih, h0, mul_zero, zero_mul]

variable [Fintype S]

/-- The **stochastic mass-action propensity** at system size `N` (Kurtz 1972):
with `k = src r`,

  `λ^N_r(z) = N κ_r ∏_s z_s (z_s - 1) ⋯ (z_s - k_s + 1) / N^{k_s}`,

the number of ordered choices of the reactant molecules, scaled by the volume. -/
noncomputable def massActionPropensity (G : ReactionNetwork S ρ) (κ : ρ → ℝ) (N : ℕ) (r : ρ)
    (z : S → ℕ) : ℝ :=
  N * κ r * ∏ s, ((z s).descFactorial (G.src r s) : ℝ) / (N : ℝ) ^ G.src r s

/-- The stochastic reaction network with mass-action propensities at system size `N`. -/
noncomputable def massAction (G : ReactionNetwork S ρ) (κ : ρ → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (N : ℕ) : StochasticCRN S ρ where
  network := G
  propensity := massActionPropensity G κ N
  propensity_nonneg r z := by
    unfold massActionPropensity
    have := hκ r
    positivity
  propensity_eq_zero r z h := by
    obtain ⟨s, hs⟩ : ∃ s, z s < G.src r s := by
      by_contra hcon
      exact h fun s => not_lt.1 fun hs => hcon ⟨s, hs⟩
    unfold massActionPropensity
    rw [Finset.prod_eq_zero (Finset.mem_univ s)
      (by rw [Nat.descFactorial_eq_zero_iff_lt.2 hs]; simp), mul_zero]

omit [Fintype ρ] in
/-- The scaled mass-action propensities converge to the deterministic mass-action rates
`κ_r ∏_s u_s ^ (src r s)` uniformly on bounded sets, at rate `O(1 / N)`. -/
theorem abs_massActionPropensity_div_sub_le (G : ReactionNetwork S ρ) (κ : ρ → ℝ) (r : ρ)
    (R : ℝ) : ∃ c : ℝ, ∀ N : ℕ, 0 < N → ∀ z : S → ℕ, ‖scaled N z‖ ≤ R →
      |massActionPropensity G κ N r z / N - G.rate κ (scaled N z) r| ≤ c / N := by
  classical
  set K : ℕ := ∑ s, G.src r s with hKdef
  have hK : ∀ s, G.src r s ≤ K := fun s =>
    Finset.single_le_sum (f := fun s => G.src r s) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  set M : ℝ := max R 0 + K + 1 with hMdef
  have hM : 1 ≤ M := by linarith [le_max_right R 0]
  have hM0 : 0 ≤ M := by linarith
  set M' : ℝ := M ^ K with hM'def
  have hM' : 1 ≤ M' := one_le_pow₀ hM
  refine ⟨|κ r| * (M' ^ Fintype.card S * (Fintype.card S * (M' * (K * K)))),
    fun N hN z hz => ?_⟩
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  set u := scaled N z with hudef
  have hu : ∀ s, |u s| ≤ max R 0 := fun s => by
    have := norm_le_pi_norm u s
    rw [Real.norm_eq_abs] at this
    exact this.trans (hz.trans (le_max_left _ _))
  set a : S → ℝ := fun s => ∏ i ∈ Finset.range (G.src r s), (u s - i / N) with hadef
  set b : S → ℝ := fun s => u s ^ G.src r s with hbdef
  have hfac : ∀ s, ((z s).descFactorial (G.src r s) : ℝ) / (N : ℝ) ^ G.src r s = a s := by
    intro s
    simp only [hadef, hudef, scaled]
    rw [cast_descFactorial_eq_prod]
    simp_rw [← sub_div]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  have hdiv : massActionPropensity G κ N r z / N = κ r * ∏ s, a s := by
    unfold massActionPropensity
    simp only [hfac]
    field_simp
  have hrate : G.rate κ u r = κ r * ∏ s, b s := rfl
  have hai : ∀ s, ∀ i ∈ Finset.range (G.src r s), |u s - i / N| ≤ M := by
    intro s i hi
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast ((Finset.mem_range.1 hi).le.trans (hK s))
    have hiN : (i : ℝ) / N ≤ i := div_le_self (Nat.cast_nonneg _) hN1
    have hi0 : 0 ≤ (i : ℝ) / N := by positivity
    calc |u s - i / N| ≤ |u s| + |(i : ℝ) / N| := abs_sub_le_abs_add_abs _ _
      _ ≤ M := by rw [abs_of_nonneg hi0]; linarith [hu s]
  have hbi : ∀ s, |u s| ≤ M := fun s => by linarith [hu s]
  have hapow : ∀ s, |a s| ≤ M' := by
    intro s
    simp only [hadef]
    rw [Finset.abs_prod]
    calc ∏ i ∈ Finset.range (G.src r s), |u s - i / N| ≤ ∏ _i ∈ Finset.range (G.src r s), M :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (hai s)
      _ = M ^ G.src r s := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ M' := pow_le_pow_right₀ hM (hK s)
  have hbpow : ∀ s, |b s| ≤ M' := by
    intro s
    simp only [hbdef]
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hbi s) _).trans (pow_le_pow_right₀ hM (hK s))
  have hab : ∀ s, |a s - b s| ≤ M' * (K * K / N) := by
    intro s
    have hb' : b s = ∏ _i ∈ Finset.range (G.src r s), u s := by
      simp only [hbdef, Finset.prod_const, Finset.card_range]
    rw [hb']
    simp only [hadef]
    refine (abs_prod_sub_prod_le _ hM (hai s) (fun _ _ => hbi s)).trans ?_
    rw [Finset.card_range]
    have hsum : ∑ i ∈ Finset.range (G.src r s), |u s - i / N - u s| ≤ K * K / N := by
      calc ∑ i ∈ Finset.range (G.src r s), |u s - i / N - u s|
          ≤ ∑ _i ∈ Finset.range (G.src r s), (K : ℝ) / N := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : (i : ℝ) ≤ K := by
              exact_mod_cast ((Finset.mem_range.1 hi).le.trans (hK s))
            rw [show u s - i / N - u s = -((i : ℝ) / N) by ring, abs_neg,
              abs_of_nonneg (by positivity)]
            exact div_le_div_of_nonneg_right hi' hNr.le
        _ = G.src r s * (K / N) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ K * (K / N) := by
            gcongr
            exact_mod_cast hK s
        _ = K * K / N := by ring
    exact mul_le_mul (pow_le_pow_right₀ hM (hK s)) hsum
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by linarith)
  have houter : |∏ s, a s - ∏ s, b s| ≤
      M' ^ Fintype.card S * (Fintype.card S * (M' * (K * K / N))) := by
    refine (abs_prod_sub_prod_le _ hM' (fun s _ => hapow s) (fun s _ => hbpow s)).trans ?_
    rw [Finset.card_univ]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
    calc ∑ s, |a s - b s| ≤ ∑ _s : S, M' * (K * K / N) := Finset.sum_le_sum fun s _ => hab s
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hdiv, hrate, ← mul_sub, abs_mul]
  calc |κ r| * |∏ s, a s - ∏ s, b s|
      ≤ |κ r| * (M' ^ Fintype.card S * (Fintype.card S * (M' * (K * K / N)))) :=
        mul_le_mul_of_nonneg_left houter (abs_nonneg _)
    _ = _ := by ring

omit [Fintype ρ] in
/-- The deterministic mass-action rate `u ↦ κ_r ∏_s u_s ^ (src r s)` is locally Lipschitz. -/
theorem locallyLipschitz_rate (G : ReactionNetwork S ρ) (κ : ρ → ℝ) (r : ρ) :
    LocallyLipschitz fun u : S → ℝ => G.rate κ u r := by
  have : ContDiff ℝ 1 fun u : S → ℝ => κ r * ∏ s, u s ^ G.src r s :=
    contDiff_const.mul (contDiff_prod fun s _ => (contDiff_apply ℝ (fun _ : S => ℝ) s).pow _)
  exact this.locallyLipschitz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : ℕ → ρ → ℝ≥0 → Ω → ℕ} {X : ℕ → Ω → ℝ → S → ℕ} {x : ℝ → S → ℝ}

/-- **Kurtz's law of large numbers for mass-action stochastic reaction networks** (Kurtz 1972;
Ethier–Kurtz 1986, ch. 11, §2). Let `X N` be the chain of the network `G` with mass-action
propensities `λ^N_r(z) = N κ_r ∏_s (z_s)_{(src r s)} / N^{src r s}` at system size `N`, and `x` a
solution of the deterministic mass-action system `x' = massActionField κ x`. If the scaled initial
state converges to `x(0)` in probability, then for every `T` and `ε > 0`

  `P(∃ t ∈ [0, T], ‖X^N(t) / N - x(t)‖₁ ≥ ε) → 0`  as `N → ∞`. -/
theorem tendsto_measure_deviation_massAction (G : ReactionNetwork S ρ) {κ : ρ → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) (hY : ∀ N r, IsPoissonProcess (Y N r) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath (massAction G κ hκ N) (fun r u => Y N r u ω) (X N ω))
    (hode : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun τ => x τ i) (G.massActionField κ (x t) i) t)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N => μ {ω | δ ≤ deviation N (X N ω) x 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (X N ω) x t}) atTop (𝓝 0) := by
  refine tendsto_measure_deviation (C := massAction G κ hκ) (β := fun r u => G.rate κ u r)
    (fun _ => rfl) (locallyLipschitz_rate G κ) (fun R => ?_) hY hchain
    ⟨fun t ht i => hode t ht i⟩ hinit T hε
  choose c hc using fun r => abs_massActionPropensity_div_sub_le G κ r R
  refine ⟨fun N => (∑ r, |c r|) / N, tendsto_const_div_atTop_nhds_zero_nat _, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with N hN r z hz
  exact (hc r N hN z hz).trans (div_le_div_of_nonneg_right ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun r => |c r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ r)))
    (Nat.cast_nonneg _))

end MassAction

end MathlibExt.Biology.Dynamics.StochasticCRNLLN
