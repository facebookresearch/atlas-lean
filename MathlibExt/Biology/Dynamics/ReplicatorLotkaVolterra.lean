/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Replicator
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Orbital equivalence of replicator and Lotka–Volterra dynamics

A symmetric matrix game with strategies `Option ι` and payoff matrix
`A : Matrix (Option ι) (Option ι) ℝ` has linear fitness `x ↦ A *ᵥ x`; its replicator equation
is `MathlibExt.Biology.Dynamics.Replicator.IsSolution (fun z => A *ᵥ z)`. The strategy `none`
is the reference strategy. The generalized Lotka–Volterra equation for species `ι`, with
intrinsic growth rates `r` and interaction matrix `B`, is

  `y_i' = y_i (r_i + ∑_j B_ij y_j)`   (`lvField r B`).

**Hofbauer's theorem** (Hofbauer 1981; Hofbauer–Sigmund 1998, §7.5): with
`r_i = A_{i,none} - A_{none,none}` (`lvGrowth A`) and `B_ij = A_{ij} - A_{none,j}`
(`lvInteraction A`), the map `x ↦ (x_i / x_none)_i` (`toLV`), with inverse
`y ↦ (1, y) / (1 + ∑ y_j)` (`ofLV`) on the simplex (`toLV_ofLV`, `ofLV_toLV`), sends orbits of
the replicator equation to orbits of the Lotka–Volterra equation, preserving their orientation.
The two directions are proved separately; that mapping a replicator trajectory to its
Lotka–Volterra trajectory and back recovers the original trajectory (up to the time changes) is
not proved here.

**Time is not preserved.** Only the oriented orbits correspond. Along a replicator solution
`x(t)`, the image `toLV (x t)` runs through a Lotka–Volterra orbit at the speed
`x_none(t)`, so the Lotka–Volterra time is `τ(t) = ∫₀ᵗ x_none(s) ds` (`timeChange`); in the
other direction the replicator time is `t(τ) = ∫₀^τ (1 + ∑ y_j(σ)) dσ` (`repTimeChange`).
Both time changes are `C¹` with positive derivative (orientation preserving); because the speed
is clamped at time `0` (see below), the extensions to `ℝ` are in general not `C²` (the
derivative has a corner at `0`), and smoothness on `(0, ∞)` is not claimed. Neither is the
identity: on the interior of the simplex with at least two strategies, `τ(t) < t` and
`t(τ) > τ` for all positive times (`timeChange_lt_self`, `lt_repTimeChange_self`). In
particular a replicator solution defined for all `t ≥ 0` may correspond to a Lotka–Volterra
solution defined only on a bounded interval `[0, ∫₀^∞ x_none)` (finite-time blow-up; see the
test file for an explicit example).

**Domain.** All results are on the common positive domain: every strategy frequency
`x_k > 0` (interior of the simplex) and every species density `y_i > 0` (open positive
orthant). The boundary, where some coordinate vanishes, is excluded.

Solutions in `Replicator.IsSolution` are only specified for `t ≥ 0`. The time changes are
defined by integrating the speed clamped at time `0` (`x (max s 0)`), which extends them to
strictly increasing `C¹` functions on all of `ℝ` without changing them on `[0, ∞)`; the new
trajectories (`lvTrajectory`, `repTrajectory`) are obtained by composing with
`Function.invFun` of the time change.

## Main definitions

* `lvField r B`: the generalized Lotka–Volterra vector field; for two species with
  `r = ![α, -γ]`, `B = !![0, -β; δ, 0]` it is the predator–prey field of
  `MathlibExt.Biology.Dynamics.LotkaVolterra` (`lvField_predatorPrey`).
* `lvGrowth A`, `lvInteraction A`, `lvGame r B`: the Lotka–Volterra parameters of a game, and a
  game realizing given parameters.
* `toLV`, `ofLV`: the coordinate changes.
* `timeChange`, `lvTrajectory`: replicator to Lotka–Volterra.
* `repTimeChange`, `repTrajectory`: Lotka–Volterra to replicator.

## Main results

* `hasDerivAt_toLV_mulVec`: along a replicator solution,
  `d/dt toLV (x t) = x_none(t) • lvField (lvGrowth A) (lvInteraction A) (toLV (x t))`.
* `hasDerivAt_ofLV`: along a positive Lotka–Volterra solution,
  `d/dτ ofLV (y τ) = (1 + ∑ y_j(τ)) • (replicator field at ofLV (y τ))`.
* `replicator_orbitEquiv_lotkaVolterra`: a replicator solution starting in the interior of the
  simplex is mapped, after the explicit positive time change `timeChange`, to a positive
  Lotka–Volterra trajectory, and `timeChange x t < t` for `t > 0`.
* `lotkaVolterra_orbitEquiv_replicator`: a positive Lotka–Volterra solution on `[0, ∞)` is
  mapped, after the explicit positive time change `repTimeChange`, to a replicator solution
  (`Replicator.IsSolution`) in the interior of the simplex, and `τ < repTimeChange y τ` for
  `τ > 0`.

The two directions do not chain. The reverse direction covers only Lotka–Volterra solutions
that exist for all `τ ≥ 0`; it does not handle solutions that blow up in finite time, such as
the trajectory `eᵘ / (2 - eᵘ)` produced from the logistic replicator solution in the tests
(there `t(τ) → ∞` as `τ` approaches the blow-up time, so such a solution should still give a
replicator solution for all time, but this is not proved here).

## Source receipt

Statement source: J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*
(1998), §7.5, Theorem 7.5.1 (theorem number not checked against the book; paraphrased, not
quoted): there is a differentiable, invertible map from `{x ∈ S_n : x_n > 0}` onto
`ℝ^{n-1}_+` sending orbits of the replicator equation of the `n × n` game `(a_ij)` to orbits of
the Lotka–Volterra equation with `r_i = a_in - a_nn` and interaction matrix `a_ij - a_nj`; the
proof uses `y_i = x_i / x_n` and the time change `dτ = x_n dt`. Here the reference strategy
`n` is `none`, and the domain is restricted further to all coordinates positive.
Reuse search (2026-11-11): the repo's replicator dynamics (`Replicator.IsSolution`,
`Replicator.meanFitness`, `IsSolution.sum_eq_one`, `IsSolution.pos_of_pos`) are reused; the
only Lotka–Volterra model in the repo is the two-species predator–prey system (no vector field
definition), which `lvField` specializes to. No existing time-reparametrization API for ODE
solutions was found in pinned Mathlib or `MathlibExt`.

## References

* J. Hofbauer, *On the occurrence of limit cycles in the Volterra–Lotka equation*, Nonlinear
  Anal. 5 (1981) 1003–1007.
* J. Hofbauer and K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge
  University Press (1998), §7.5.
-/

@[expose] public section

open Set Finset Function Matrix
open scoped Topology

namespace MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra

open Replicator

variable {ι : Type*} [Fintype ι]

/-! ### Definitions -/

/-- The generalized Lotka–Volterra vector field `y_i (r_i + ∑_j B_ij y_j)` with intrinsic
growth rates `r` and interaction matrix `B`. -/
def lvField (r : ι → ℝ) (B : Matrix ι ι ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun i => y i * (r i + ∑ j, B i j * y j)

/-- The Lotka–Volterra growth rates `r_i = A_{i,none} - A_{none,none}` of the game `A`. -/
def lvGrowth (A : Matrix (Option ι) (Option ι) ℝ) : ι → ℝ :=
  fun i => A (some i) none - A none none

/-- The Lotka–Volterra interaction matrix `B_ij = A_{ij} - A_{none,j}` of the game `A`. -/
def lvInteraction (A : Matrix (Option ι) (Option ι) ℝ) : Matrix ι ι ℝ :=
  fun i j => A (some i) (some j) - A none (some j)

/-- A game realizing the Lotka–Volterra parameters `r`, `B`: payoff `B_ij` against `j`,
`r_i` against the reference strategy, and a zero payoff row for the reference strategy. -/
def lvGame (r : ι → ℝ) (B : Matrix ι ι ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  fun k l => match k, l with
    | some i, some j => B i j
    | some i, none => r i
    | none, _ => 0

/-- Replicator to Lotka–Volterra coordinates: `y_i = x_i / x_none`. Meaningful for
`x_none > 0`. -/
noncomputable def toLV (x : Option ι → ℝ) : ι → ℝ :=
  fun i => x (some i) / x none

/-- Lotka–Volterra to replicator coordinates: `x_none = 1 / (1 + ∑ y_j)`,
`x_i = y_i / (1 + ∑ y_j)`. Meaningful for `1 + ∑ y_j ≠ 0`; it lands in the simplex. -/
noncomputable def ofLV (y : ι → ℝ) : Option ι → ℝ :=
  fun k => k.elim 1 y / (1 + ∑ j, y j)

/-- The Lotka–Volterra time along a replicator solution `x`: `τ(t) = ∫₀ᵗ x_none(s) ds` for
`t ≥ 0`. The speed is clamped at time `0` (`x (max s 0)`), which leaves `τ` unchanged on
`[0, ∞)` and makes it a `C¹` function on `ℝ`. -/
noncomputable def timeChange (x : ℝ → Option ι → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, x (max s 0) none

/-- The Lotka–Volterra trajectory of a replicator solution `x`, in Lotka–Volterra time `u`:
`toLV (x (τ⁻¹ u))` with `τ = timeChange x`. -/
noncomputable def lvTrajectory (x : ℝ → Option ι → ℝ) (u : ℝ) : ι → ℝ :=
  toLV (x (invFun (timeChange x) u))

/-- The replicator time along a Lotka–Volterra solution `y`: `t(τ) = ∫₀^τ (1 + ∑ y_j(σ)) dσ`
for `τ ≥ 0`, with the integrand clamped at time `0` as in `timeChange`. -/
noncomputable def repTimeChange (y : ℝ → ι → ℝ) (τ : ℝ) : ℝ :=
  ∫ σ in (0 : ℝ)..τ, (1 + ∑ j, y (max σ 0) j)

/-- The replicator trajectory of a Lotka–Volterra solution `y`, in replicator time `t`:
`ofLV (y (t⁻¹ t))` with `t(·) = repTimeChange y`. -/
noncomputable def repTrajectory (y : ℝ → ι → ℝ) (t : ℝ) : Option ι → ℝ :=
  ofLV (y (invFun (repTimeChange y) t))

/-! ### Algebra of the coordinate changes -/

/-- **Two-species case.** With `r = ![α, -γ]` and `B = !![0, -β; δ, 0]`, `lvField` is the
predator–prey field `x' = α x - β x y`, `y' = δ x y - γ y` of
`MathlibExt.Biology.Dynamics.LotkaVolterra`. -/
theorem lvField_predatorPrey (α β γ δ x y : ℝ) :
    lvField ![α, -γ] !![0, -β; δ, 0] ![x, y] = ![α * x - β * x * y, δ * x * y - γ * y] := by
  ext i
  fin_cases i <;> simp [lvField, Fin.sum_univ_two] <;> ring

omit [Fintype ι] in
@[simp]
theorem lvGrowth_lvGame (r : ι → ℝ) (B : Matrix ι ι ℝ) : lvGrowth (lvGame r B) = r := by
  ext i
  simp [lvGrowth, lvGame]

omit [Fintype ι] in
@[simp]
theorem lvInteraction_lvGame (r : ι → ℝ) (B : Matrix ι ι ℝ) :
    lvInteraction (lvGame r B) = B := by
  ext i j
  simp [lvInteraction, lvGame]

@[simp]
theorem ofLV_none (y : ι → ℝ) : ofLV y none = 1 / (1 + ∑ j, y j) := rfl

@[simp]
theorem ofLV_some (y : ι → ℝ) (i : ι) : ofLV y (some i) = y i / (1 + ∑ j, y j) := rfl

/-- `ofLV` lands in the hyperplane `∑ x_k = 1`. -/
theorem sum_ofLV {y : ι → ℝ} (hy : 1 + ∑ j, y j ≠ 0) : ∑ k, ofLV y k = 1 := by
  rw [Fintype.sum_option, ofLV_none]
  simp only [ofLV_some, ← Finset.sum_div]
  field_simp

/-- `ofLV` inverts `toLV` on the hyperplane `∑ x_k = 1` (where `x_none ≠ 0`). -/
theorem ofLV_toLV {x : Option ι → ℝ} (h0 : x none ≠ 0) (h1 : ∑ k, x k = 1) :
    ofLV (toLV x) = x := by
  have hS : 1 + ∑ j, toLV x j = 1 / x none := by
    rw [Fintype.sum_option] at h1
    simp only [toLV, ← Finset.sum_div]
    field_simp
    linarith
  ext k
  cases k with
  | none => simp [hS]
  | some i =>
    rw [ofLV_some, hS]
    simp only [toLV]
    field_simp

/-- `toLV` inverts `ofLV`. -/
theorem toLV_ofLV {y : ι → ℝ} (hy : 1 + ∑ j, y j ≠ 0) : toLV (ofLV y) = y := by
  ext i
  simp only [toLV, ofLV_some, ofLV_none]
  field_simp

/-- `ofLV` maps the open positive orthant into the interior of the simplex. -/
theorem ofLV_pos {y : ι → ℝ} (hy : ∀ j, 0 < y j) (k : Option ι) : 0 < ofLV y k := by
  have hS : 0 < 1 + ∑ j, y j := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hy j).le
    linarith
  cases k with
  | none => simpa using hS
  | some i => simpa using div_pos (hy i) hS

omit [Fintype ι] in
/-- `toLV` maps the interior of the simplex (indeed any positive vector) into the open
positive orthant. -/
theorem toLV_pos {x : Option ι → ℝ} (hx : ∀ k, 0 < x k) (i : ι) : 0 < toLV x i :=
  div_pos (hx _) (hx _)

/-- **Fitness differences are Lotka–Volterra rates.** For the game `A` and `x_none ≠ 0`,
`(A x)_i - (A x)_none = x_none (r_i + ∑_j B_ij y_j)` with `y = toLV x`. -/
theorem mulVec_some_sub_mulVec_none (A : Matrix (Option ι) (Option ι) ℝ)
    {x : Option ι → ℝ} (hx : x none ≠ 0) (i : ι) :
    (A *ᵥ x) (some i) - (A *ᵥ x) none =
      x none * (lvGrowth A i + ∑ j, lvInteraction A i j * toLV x j) := by
  have h : ∀ j, x none * (lvInteraction A i j * toLV x j) =
      A (some i) (some j) * x (some j) - A none (some j) * x (some j) := fun j => by
    simp only [lvInteraction, toLV]
    field_simp
  simp only [mulVec, dotProduct, Fintype.sum_option, mul_add, Finset.mul_sum, h,
    Finset.sum_sub_distrib, lvGrowth]
  ring

/-- On the hyperplane `∑ x_k = 1`, `f̄(x) - f_none(x) = ∑_i x_i (f_i(x) - f_none(x))`. -/
theorem meanFitness_sub_none (f : (Option ι → ℝ) → Option ι → ℝ) {x : Option ι → ℝ}
    (hx : ∑ k, x k = 1) :
    meanFitness f x - f x none = ∑ i, x (some i) * (f x (some i) - f x none) := by
  rw [Fintype.sum_option] at hx
  simp only [meanFitness, Fintype.sum_option, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  rw [show x none = 1 - ∑ i, x (some i) by linarith]
  ring

/-! ### The vector fields are positive multiples of each other -/

/-- Along any replicator solution with `x_none(t) ≠ 0`,
`d/dt (x_i / x_none) = (x_i / x_none) (f_i - f_none)`: the mean fitness cancels. -/
theorem hasDerivAt_toLV {f : (Option ι → ℝ) → Option ι → ℝ} {x : ℝ → Option ι → ℝ} {t : ℝ}
    (hx : ∀ k, HasDerivAt (fun s => x s k) (x t k * (f (x t) k - meanFitness f (x t))) t)
    (h0 : x t none ≠ 0) (i : ι) :
    HasDerivAt (fun s => toLV (x s) i)
      (toLV (x t) i * (f (x t) (some i) - f (x t) none)) t := by
  have h := (hx (some i)).fun_div (hx none) h0
  simp only [toLV]
  convert h using 1
  field_simp
  ring

/-- **Replicator to Lotka–Volterra, infinitesimally.** Along a solution of the replicator
equation of the game `A` with `x_none(t) ≠ 0`, `toLV (x t)` moves with velocity
`x_none(t) • lvField (lvGrowth A) (lvInteraction A) (toLV (x t))`. -/
theorem hasDerivAt_toLV_mulVec {A : Matrix (Option ι) (Option ι) ℝ} {x : ℝ → Option ι → ℝ}
    {t : ℝ}
    (hx : ∀ k, HasDerivAt (fun s => x s k)
      (x t k * ((A *ᵥ x t) k - meanFitness (fun z => A *ᵥ z) (x t))) t)
    (h0 : x t none ≠ 0) (i : ι) :
    HasDerivAt (fun s => toLV (x s) i)
      (x t none * lvField (lvGrowth A) (lvInteraction A) (toLV (x t)) i) t := by
  convert hasDerivAt_toLV (f := fun z => A *ᵥ z) hx h0 i using 1
  simp only [mulVec_some_sub_mulVec_none A h0, lvField]
  ring

/-- **Lotka–Volterra to replicator, infinitesimally.** Along a solution of
`y' = lvField (lvGrowth A) (lvInteraction A) y` with `1 + ∑ y_j(τ) ≠ 0`, `ofLV (y τ)` moves
with velocity `(1 + ∑ y_j(τ))` times the replicator field of the game `A` at `ofLV (y τ)`. -/
theorem hasDerivAt_ofLV {A : Matrix (Option ι) (Option ι) ℝ} {y : ℝ → ι → ℝ} {τ : ℝ}
    (hy : ∀ i, HasDerivAt (fun σ => y σ i) (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hS : 1 + ∑ j, y τ j ≠ 0) (k : Option ι) :
    HasDerivAt (fun σ => ofLV (y σ) k) ((1 + ∑ j, y τ j) * (ofLV (y τ) k *
      ((A *ᵥ ofLV (y τ)) k - meanFitness (fun z => A *ᵥ z) (ofLV (y τ))))) τ := by
  have hw0 : ofLV (y τ) none ≠ 0 := by simp [hS]
  have hdiff : ∀ i, (A *ᵥ ofLV (y τ)) (some i) - (A *ᵥ ofLV (y τ)) none =
      (lvGrowth A i + ∑ j, lvInteraction A i j * y τ j) / (1 + ∑ j, y τ j) := by
    intro i
    rw [mulVec_some_sub_mulVec_none A hw0, toLV_ofLV hS, ofLV_none]
    field_simp
  have hmean : meanFitness (fun z => A *ᵥ z) (ofLV (y τ)) - (A *ᵥ ofLV (y τ)) none =
      (∑ i, lvField (lvGrowth A) (lvInteraction A) (y τ) i) / (1 + ∑ j, y τ j) ^ 2 := by
    rw [meanFitness_sub_none _ (sum_ofLV hS), Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hdiff, ofLV_some, lvField]
    field_simp
  have hSd : HasDerivAt (fun σ => 1 + ∑ j, y σ j)
      (∑ j, lvField (lvGrowth A) (lvInteraction A) (y τ) j) τ := by
    simpa using (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hy j).const_add 1
  cases k with
  | none =>
    have h := (hasDerivAt_const τ (1 : ℝ)).fun_div hSd hS
    have hk : (A *ᵥ ofLV (y τ)) none - meanFitness (fun z => A *ᵥ z) (ofLV (y τ)) =
        -((∑ i, lvField (lvGrowth A) (lvInteraction A) (y τ) i) / (1 + ∑ j, y τ j) ^ 2) := by
      rw [← hmean]
      ring
    simp only [ofLV_none]
    convert h using 1
    rw [hk]
    field_simp
    ring
  | some i =>
    have h := (hy i).fun_div hSd hS
    have hk : (A *ᵥ ofLV (y τ)) (some i) - meanFitness (fun z => A *ᵥ z) (ofLV (y τ)) =
        (lvGrowth A i + ∑ j, lvInteraction A i j * y τ j) / (1 + ∑ j, y τ j) -
          (∑ i, lvField (lvGrowth A) (lvInteraction A) (y τ) i) / (1 + ∑ j, y τ j) ^ 2 := by
      rw [← hmean, ← hdiff]
      ring
    simp only [ofLV_some]
    convert h using 1
    rw [hk]
    simp only [lvField]
    field_simp

/-! ### Reparametrization by an increasing `C¹` time change -/

/-- **Reparametrization.** Let `θ : ℝ → ℝ` have positive derivative `θ'` everywhere. If a curve
`c` satisfies `c'(s) = θ'(s) v` at `s`, then `c ∘ θ⁻¹` has derivative `v` at `θ(s)`. -/
theorem hasDerivAt_comp_invFun {θ θ' c : ℝ → ℝ} (hθ : ∀ s, HasDerivAt θ (θ' s) s)
    (hpos : ∀ s, 0 < θ' s) {s v : ℝ} (hc : HasDerivAt c (θ' s * v) s) :
    HasDerivAt (fun u => c (invFun θ u)) v (θ s) := by
  have hmono : StrictMono θ := strictMono_of_deriv_pos fun s => (hθ s).deriv ▸ hpos s
  have hcont : Continuous θ := continuous_iff_continuousAt.2 fun s => (hθ s).continuousAt
  have hleft : ∀ p, invFun θ (θ p) = p := leftInverse_invFun hmono.injective
  have hsub : Ioo (θ (s - 1)) (θ (s + 1)) ⊆ θ '' Ioo (s - 1) (s + 1) :=
    intermediate_value_Ioo (by linarith) hcont.continuousOn
  have hnhds : Ioo (θ (s - 1)) (θ (s + 1)) ∈ 𝓝 (θ s) :=
    Ioo_mem_nhds (hmono (by linarith)) (hmono (by linarith))
  have hg_cont : ContinuousAt (invFun θ) (θ s) := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := θ '' Ioo (s - 1) (s + 1)) ?_
      (Filter.mem_of_superset hnhds hsub) ?_
    · rintro _ ⟨p, -, rfl⟩ _ ⟨q, -, rfl⟩ hpq
      rw [hleft p, hleft q]
      exact hmono.le_iff_le.1 hpq
    · rw [image_image, show (fun p => invFun θ (θ p)) = id from funext hleft, image_id,
        hleft s]
      exact Ioo_mem_nhds (by linarith) (by linarith)
  have hev : ∀ᶠ u in 𝓝 (θ s), θ (invFun θ u) = u := by
    filter_upwards [hnhds] with u hu
    obtain ⟨p, -, rfl⟩ := hsub hu
    rw [hleft p]
  have hg : HasDerivAt (invFun θ) (θ' s)⁻¹ (θ s) :=
    HasDerivAt.of_local_left_inverse hg_cont (by rw [hleft s]; exact hθ s) (hpos s).ne' hev
  have hc' : HasDerivAt c (θ' s * v) (invFun θ (θ s)) := by
    rw [hleft s]
    exact hc
  convert hc'.comp (θ s) hg using 1
  · rfl
  · rw [mul_right_comm, mul_inv_cancel₀ (hpos s).ne', one_mul]

/-- A function continuous at every `t ≥ 0`, clamped at `0`, is continuous. -/
private theorem continuous_clamp {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → ContinuousAt g t) :
    Continuous fun s => g (max s 0) :=
  continuous_iff_continuousAt.2 fun s =>
    ContinuousAt.comp (g := g) (f := fun s : ℝ => max s 0) (hg _ (le_max_right s 0))
      (continuous_id.max continuous_const).continuousAt

/-! ### Replicator to Lotka–Volterra -/

section ReplicatorToLV

variable {f : (Option ι → ℝ) → Option ι → ℝ} {x : ℝ → Option ι → ℝ}

omit [Fintype ι] in
theorem timeChange_zero (x : ℝ → Option ι → ℝ) : timeChange x 0 = 0 :=
  intervalIntegral.integral_same

/-- The derivative of the Lotka–Volterra time is the reference frequency: `τ'(t) = x_none(t)`
for `t ≥ 0` (clamped at `0` for `t < 0`). -/
theorem hasDerivAt_timeChange (hx : IsSolution f x) (t : ℝ) :
    HasDerivAt (timeChange x) (x (max t 0) none) t :=
  ((continuous_clamp fun s hs => (hx.hasDerivAt none s hs).continuousAt).integral_hasStrictDerivAt
    0 t).hasDerivAt

/-- The Lotka–Volterra time is `C¹`. -/
theorem contDiff_timeChange (hx : IsSolution f x) : ContDiff ℝ 1 (timeChange x) :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_timeChange hx t).differentiableAt, by
    simpa only [funext fun t => (hasDerivAt_timeChange hx t).deriv] using
      continuous_clamp fun s hs => (hx.hasDerivAt none s hs).continuousAt⟩

/-- The Lotka–Volterra time increases at a positive rate. -/
theorem timeChange_deriv_pos (hx : IsSolution f x) (hf : Continuous f) (h0 : 0 < x 0 none)
    (t : ℝ) : 0 < x (max t 0) none :=
  hx.pos_of_pos hf h0 (le_max_right t 0)

theorem strictMono_timeChange (hx : IsSolution f x) (hf : Continuous f) (h0 : 0 < x 0 none) :
    StrictMono (timeChange x) :=
  strictMono_of_deriv_pos fun t =>
    (hasDerivAt_timeChange hx t).deriv ▸ timeChange_deriv_pos hx hf h0 t

/-- The Lotka–Volterra trajectory at time `τ(t)` is the image `toLV (x t)` of the replicator
state at time `t`. -/
theorem lvTrajectory_timeChange (hx : IsSolution f x) (hf : Continuous f) (h0 : 0 < x 0 none)
    (t : ℝ) : lvTrajectory x (timeChange x t) = toLV (x t) := by
  rw [lvTrajectory, leftInverse_invFun (strictMono_timeChange hx hf h0).injective t]

/-- **The Lotka–Volterra trajectory solves the Lotka–Volterra equation** at every time
`τ(t)`, `t ≥ 0`, in the image of `[0, ∞)` under the time change. -/
theorem hasDerivAt_lvTrajectory {A : Matrix (Option ι) (Option ι) ℝ}
    (hx : IsSolution (fun z => A *ᵥ z) x) (h0 : 0 < x 0 none) {t : ℝ} (ht : 0 ≤ t) (i : ι) :
    HasDerivAt (fun u => lvTrajectory x u i)
      (lvField (lvGrowth A) (lvInteraction A) (lvTrajectory x (timeChange x t)) i)
      (timeChange x t) := by
  have hf : Continuous fun z : Option ι → ℝ => A *ᵥ z := continuous_const.matrix_mulVec
    continuous_id
  rw [lvTrajectory_timeChange hx hf h0]
  have hc := hasDerivAt_toLV_mulVec (fun k => hx.hasDerivAt k t ht)
    (hx.pos_of_pos hf h0 ht).ne' i
  have hc' : HasDerivAt (fun s => toLV (x s) i)
      (x (max t 0) none * lvField (lvGrowth A) (lvInteraction A) (toLV (x t)) i) t := by
    rw [max_eq_left ht]
    exact hc
  exact hasDerivAt_comp_invFun (c := fun s => toLV (x s) i) (hasDerivAt_timeChange hx)
    (timeChange_deriv_pos hx hf h0) hc'

/-- **Time is not preserved.** For a replicator solution starting in the interior of the
simplex, with at least two strategies, the Lotka–Volterra time runs strictly slower:
`τ(t) < t` for every `t > 0`. -/
theorem timeChange_lt_self [Nonempty ι] (hx : IsSolution f x) (hf : Continuous f)
    (h0 : ∀ k, 0 < x 0 k) (h1 : ∑ k, x 0 k = 1) {t : ℝ} (ht : 0 < t) : timeChange x t < t := by
  have hd : ∀ s, HasDerivAt (fun s => s - timeChange x s) (1 - x (max s 0) none) s :=
    fun s => (hasDerivAt_id s).sub (hasDerivAt_timeChange hx s)
  have hpos : ∀ s, 0 < 1 - x (max s 0) none := by
    intro s
    have hs := hx.sum_eq_one hf h1 (le_max_right s 0)
    rw [Fintype.sum_option] at hs
    have : 0 < ∑ i, x (max s 0) (some i) :=
      Finset.sum_pos (fun i _ => hx.pos_of_pos hf (h0 _) (le_max_right s 0))
        Finset.univ_nonempty
    linarith
  have hmono : StrictMono fun s => s - timeChange x s :=
    strictMono_of_deriv_pos fun s => (hd s).deriv ▸ hpos s
  have := hmono ht
  simp only [timeChange_zero, sub_zero] at this
  linarith

/-- **Orbital equivalence, replicator to Lotka–Volterra** (Hofbauer–Sigmund 1998,
§7.5). Let `x` solve the replicator equation of the game `A` with initial state in the
interior of the simplex. The explicit time change `τ = timeChange x`, `τ(t) = ∫₀ᵗ x_none`, is
`C¹` with positive derivative `x_none` (orientation preserving) and `τ(0) = 0`; the curve
`lvTrajectory x` is positive and solves the Lotka–Volterra equation with
`r = lvGrowth A`, `B = lvInteraction A` at each time `τ(t)`, `t ≥ 0`, where it equals
`(x_i(t) / x_none(t))_i`. The original times are **not** identified: `τ(t) < t` for `t > 0`
whenever there are at least two strategies. Boundary states are excluded. -/
theorem replicator_orbitEquiv_lotkaVolterra [Nonempty ι] {A : Matrix (Option ι) (Option ι) ℝ}
    (hx : IsSolution (fun z => A *ᵥ z) x) (h0 : ∀ k, 0 < x 0 k) (h1 : ∑ k, x 0 k = 1) :
    timeChange x 0 = 0 ∧ ContDiff ℝ 1 (timeChange x) ∧
    (∀ t, HasDerivAt (timeChange x) (x (max t 0) none) t ∧ 0 < x (max t 0) none) ∧
    (∀ t, 0 ≤ t → ∀ i,
      lvTrajectory x (timeChange x t) i = x t (some i) / x t none ∧
      0 < lvTrajectory x (timeChange x t) i ∧
      HasDerivAt (fun u => lvTrajectory x u i)
        (lvField (lvGrowth A) (lvInteraction A) (lvTrajectory x (timeChange x t)) i)
        (timeChange x t)) ∧
    ∀ t, 0 < t → timeChange x t < t := by
  have hf : Continuous fun z : Option ι → ℝ => A *ᵥ z := continuous_const.matrix_mulVec
    continuous_id
  refine ⟨timeChange_zero x, contDiff_timeChange hx, fun t => ⟨hasDerivAt_timeChange hx t,
    timeChange_deriv_pos hx hf (h0 none) t⟩, fun t ht i => ⟨?_, ?_,
    hasDerivAt_lvTrajectory hx (h0 none) ht i⟩, fun t ht => timeChange_lt_self hx hf h0 h1 ht⟩
  · rw [lvTrajectory_timeChange hx hf (h0 none)]
    rfl
  · rw [lvTrajectory_timeChange hx hf (h0 none)]
    exact toLV_pos (fun k => hx.pos_of_pos hf (h0 k) ht) i

end ReplicatorToLV

/-! ### Lotka–Volterra to replicator -/

section LVToReplicator

variable {A : Matrix (Option ι) (Option ι) ℝ} {y : ℝ → ι → ℝ}

theorem repTimeChange_zero (y : ℝ → ι → ℝ) : repTimeChange y 0 = 0 :=
  intervalIntegral.integral_same

/-- The derivative of the replicator time is `1 + ∑ y_j(τ)` for `τ ≥ 0` (clamped at `0` for
`τ < 0`). -/
theorem hasDerivAt_repTimeChange
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ) (τ : ℝ) :
    HasDerivAt (repTimeChange y) (1 + ∑ j, y (max τ 0) j) τ := by
  have hc : Continuous fun σ => 1 + ∑ j, y (max σ 0) j :=
    continuous_const.add (continuous_finsetSum _ fun j _ =>
      continuous_clamp fun s hs => (hy j s hs).continuousAt)
  exact (hc.integral_hasStrictDerivAt 0 τ).hasDerivAt

/-- The replicator time is `C¹`. -/
theorem contDiff_repTimeChange
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ) : ContDiff ℝ 1 (repTimeChange y) :=
  contDiff_one_iff_deriv.2 ⟨fun τ => (hasDerivAt_repTimeChange hy τ).differentiableAt, by
    rw [funext fun τ => (hasDerivAt_repTimeChange hy τ).deriv]
    exact continuous_const.add (continuous_finsetSum _ fun j _ =>
      continuous_clamp fun s hs => (hy j s hs).continuousAt)⟩

private theorem one_le_repTimeChange_deriv (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) (τ : ℝ) :
    1 ≤ 1 + ∑ j, y (max τ 0) j := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hpos _ (le_max_right τ 0) j).le
  linarith

theorem strictMono_repTimeChange
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) : StrictMono (repTimeChange y) :=
  strictMono_of_deriv_pos fun τ => (hasDerivAt_repTimeChange hy τ).deriv ▸
    zero_lt_one.trans_le (one_le_repTimeChange_deriv hpos τ)

/-- The replicator trajectory at time `t(τ)` is `ofLV (y τ)`. -/
theorem repTrajectory_repTimeChange
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) (τ : ℝ) :
    repTrajectory y (repTimeChange y τ) = ofLV (y τ) := by
  rw [repTrajectory, leftInverse_invFun (strictMono_repTimeChange hy hpos).injective τ]

/-- The replicator time runs at least as fast as the Lotka–Volterra time:
`τ ≤ t(τ)` for `τ ≥ 0`. -/
theorem le_repTimeChange_self
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) {τ : ℝ} (hτ : 0 ≤ τ) : τ ≤ repTimeChange y τ := by
  have hd : ∀ s, HasDerivAt (fun s => repTimeChange y s - s) (∑ j, y (max s 0) j) s :=
    fun s => ((hasDerivAt_repTimeChange hy s).sub (hasDerivAt_id s)).congr_deriv (by ring)
  have hmono : Monotone fun s => repTimeChange y s - s :=
    monotone_of_deriv_nonneg (fun s => (hd s).differentiableAt) fun s =>
      (hd s).deriv ▸ Finset.sum_nonneg fun j _ => (hpos _ (le_max_right s 0) j).le
  have := hmono hτ
  simp only [repTimeChange_zero, sub_zero] at this
  linarith

/-- **Time is not preserved.** With at least one species, the replicator time runs strictly
faster: `τ < t(τ)` for every `τ > 0`. -/
theorem lt_repTimeChange_self [Nonempty ι]
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) {τ : ℝ} (hτ : 0 < τ) : τ < repTimeChange y τ := by
  have hd : ∀ s, HasDerivAt (fun s => repTimeChange y s - s) (∑ j, y (max s 0) j) s :=
    fun s => ((hasDerivAt_repTimeChange hy s).sub (hasDerivAt_id s)).congr_deriv (by ring)
  have hmono : StrictMono fun s => repTimeChange y s - s :=
    strictMono_of_deriv_pos fun s => (hd s).deriv ▸
      Finset.sum_pos (fun j _ => hpos _ (le_max_right s 0) j) Finset.univ_nonempty
  have := hmono hτ
  simp only [repTimeChange_zero, sub_zero] at this
  linarith

/-- Every replicator time `t ≥ 0` is reached: `t = t(τ)` for some `τ ∈ [0, t]`. -/
theorem exists_repTimeChange_eq
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) {t : ℝ} (ht : 0 ≤ t) :
    ∃ τ ∈ Icc 0 t, repTimeChange y τ = t := by
  have hcont : Continuous (repTimeChange y) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_repTimeChange hy s).continuousAt
  have hmem : t ∈ Icc (repTimeChange y 0) (repTimeChange y t) :=
    ⟨(repTimeChange_zero y).symm ▸ ht, le_repTimeChange_self hy hpos ht⟩
  exact intermediate_value_Icc ht hcont.continuousOn hmem

/-- **The replicator trajectory solves the replicator equation** of the game `A` for all
times `t ≥ 0`. -/
theorem isSolution_repTrajectory
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) :
    IsSolution (fun z => A *ᵥ z) (repTrajectory y) where
  hasDerivAt k t ht := by
    obtain ⟨τ, hτ, rfl⟩ := exists_repTimeChange_eq hy hpos ht
    rw [repTrajectory_repTimeChange hy hpos]
    have hS : 0 < 1 + ∑ j, y τ j := by
      simpa [max_eq_left hτ.1] using
        zero_lt_one.trans_le (one_le_repTimeChange_deriv hpos τ)
    have hc := hasDerivAt_ofLV (A := A) (fun i => hy i τ hτ.1) hS.ne' k
    rw [show (1 + ∑ j, y τ j) = 1 + ∑ j, y (max τ 0) j by rw [max_eq_left hτ.1]] at hc
    exact hasDerivAt_comp_invFun (c := fun σ => ofLV (y σ) k) (hasDerivAt_repTimeChange hy)
      (fun s => zero_lt_one.trans_le (one_le_repTimeChange_deriv hpos s)) hc

/-- **Orbital equivalence, Lotka–Volterra to replicator** (Hofbauer–Sigmund 1998,
§7.5). Let `y` be a positive solution on `[0, ∞)` of the Lotka–Volterra equation with
`r = lvGrowth A`, `B = lvInteraction A` (every `r`, `B` arises this way, from `lvGame r B`).
The explicit time change `t = repTimeChange y`, `t(τ) = ∫₀^τ (1 + ∑ y_j)`, is `C¹` with
derivative `≥ 1` (orientation preserving) and `t(0) = 0`; the curve `repTrajectory y` solves
the replicator equation of the game `A` for all `t ≥ 0`, stays in the interior of the simplex,
and equals `ofLV (y τ)` at time `t(τ)`. The original times are **not** identified:
`τ < t(τ)` for `τ > 0` whenever there is at least one species. Boundary states are
excluded. Only Lotka–Volterra solutions existing for all `τ ≥ 0` are covered; solutions that
blow up in finite time (such as those produced by `replicator_orbitEquiv_lotkaVolterra` when
`∫₀^∞ x_none < ∞`) are not. -/
theorem lotkaVolterra_orbitEquiv_replicator [Nonempty ι]
    (hy : ∀ i τ, 0 ≤ τ → HasDerivAt (fun σ => y σ i)
      (lvField (lvGrowth A) (lvInteraction A) (y τ) i) τ)
    (hpos : ∀ τ, 0 ≤ τ → ∀ i, 0 < y τ i) :
    repTimeChange y 0 = 0 ∧ ContDiff ℝ 1 (repTimeChange y) ∧
    (∀ τ, HasDerivAt (repTimeChange y) (1 + ∑ j, y (max τ 0) j) τ ∧
      1 ≤ 1 + ∑ j, y (max τ 0) j) ∧
    IsSolution (fun z => A *ᵥ z) (repTrajectory y) ∧
    (∀ τ, 0 ≤ τ → repTrajectory y (repTimeChange y τ) = ofLV (y τ)) ∧
    (∀ t, 0 ≤ t → (∀ k, 0 < repTrajectory y t k) ∧ ∑ k, repTrajectory y t k = 1) ∧
    ∀ τ, 0 < τ → τ < repTimeChange y τ := by
  refine ⟨repTimeChange_zero y, contDiff_repTimeChange hy, fun τ => ⟨hasDerivAt_repTimeChange hy τ,
    one_le_repTimeChange_deriv hpos τ⟩, isSolution_repTrajectory hy hpos,
    fun τ _ => repTrajectory_repTimeChange hy hpos τ, fun t ht => ?_,
    fun τ hτ => lt_repTimeChange_self hy hpos hτ⟩
  obtain ⟨τ, hτ, rfl⟩ := exists_repTimeChange_eq hy hpos ht
  rw [repTrajectory_repTimeChange hy hpos]
  have hyτ := hpos τ hτ.1
  refine ⟨ofLV_pos hyτ, sum_ofLV ?_⟩
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => (hyτ j).le
  linarith

end LVToReplicator

end MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra
