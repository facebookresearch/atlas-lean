/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.OrderClosed
public import Physlib.Thermodynamics.IdealGas.Basic

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!

# Equilibrium postulates and the fundamental relation

The entropy fundamental relation of a simple system, after Callen: entropy as a
differentiable, concave, first-order homogeneous function of the equilibrium state that
increases with the internal energy, with temperature, pressure and chemical potentials
defined as its partial derivatives.

## i. Overview

An equilibrium state of a simple system with `k` species is a triple `(U, V, N)` of
internal energy, volume and amounts `N : Fin k → ℝ`, all strictly positive
(`thermoDomain`). All quantities are plain reals; no unit system is used. The sign
convention is work done ON the system positive, `dU = dQ + dW`. Amounts are treated
as continuous.

The physics postulates (LAW) are fields of the structure `FundamentalRelation`, never
global Lean axioms. On the open domain, `S` is Fréchet differentiable (`h_diff`), concave
(`h_concave`, the stability condition), positively homogeneous of degree 1 (`h_homog`)
and has `∂S/∂U > 0` (`h_pos`). The fields constrain `S` only on the domain. Everything
else is proved from them (MC): the chain rule along curves of states
(`hasDerivAt_comp_curve`, from `h_diff`), strict monotonicity in `U`, the first law, the
Euler relation, Gibbs-Duhem, the equilibrium and heat-flow results, and the ideal-gas
equations. The ideal gas is a `FundamentalRelation` (`idealGas`), so the postulates are
consistent and the generic results apply to it.

Partial derivatives are single-variable `deriv` slices, uniformly: `dSdU` varies `U`,
`dSdV` varies `V`, `dSdN i` varies `N i` through `Function.update`. Where `S` is
differentiable they are the Fréchet derivative applied to the coordinate directions
(`dSdU_eq_fderiv`, `dSdV_eq_fderiv`, `dSdN_eq_fderiv`). Temperature, pressure and
chemical potentials are defined from them (`temp`, `press`, `chemPot`), not postulated.
These definitions are total: where a slice is not differentiable, `deriv` is Lean's junk
value `0`, and where `∂S/∂U = 0` the temperature is the junk value `1 / 0 = 0`. Neither
happens on the domain of a `FundamentalRelation`. Differentiability along a curve is
always stated with explicit `HasDerivAt` hypotheses on the curve components.

Model boundary: the third law and `S ≥ 0` are NOT implied and not assumed.
Nondifferentiable fundamental relations (subgradients) are not treated. Homogeneity
excludes small systems and long-range forces; `N` is continuous. This module is kept
distinct from statistical ensembles.

## ii. Key results

- `FundamentalRelation` : the postulate bundle (entropy plus LAW hypotheses).
- `temp`, `press`, `chemPot` : `T`, `p`, `μᵢ` as partial derivatives of `S`.
- `dSdU_eq_fderiv`, `dSdV_eq_fderiv`, `dSdN_eq_fderiv` : the slice partials are the
  Fréchet partials.
- `hasDerivAt_comp_curve` : the chain rule along a curve of states, from `h_diff`.
- `temp_pos` : `T > 0` on the domain.
- `FundamentalRelation.strictMonoOn_energy` : `S` is strictly increasing in `U`.
- `firstLaw`, `firstLaw_value` : `dU = T dS - p dV + ∑ μᵢ dNᵢ` along a curve.
- `euler_homogeneous_function`, `euler_relation` : `U = TS - pV + ∑ μᵢNᵢ`.
- `gibbsDuhem` : `S dT - V dp + ∑ Nᵢ dμᵢ = 0` in derivative form along a curve.
- `entropyMax_temperature_eq` : equal temperatures at an interior entropy maximum.
- `entropyFlow_sign` : hot-to-cold flow increases total entropy (derivative sign).
- `Sideal`, `SidealGen` : the ideal-gas entropy model (MOD).
- `sideal_eq_entropy` : `Sideal` is Physlib's ideal-gas `entropy` with `c = 3/2`.
- `sideal_differentiableOn` : the ideal-gas entropy is Fréchet differentiable.
- `idealGas` : the ideal gas as a `FundamentalRelation 1`, every postulate proved.
- `sideal_pV`, `sideal_U` : `pV = NkT` and `U = (3/2)NkT`.
- `sideal_euler`, `sideal_gibbsDuhem` : Euler and Gibbs-Duhem for the ideal gas.
- `concave_perspLog`, `sideal_concave`, `sideal_concave_gen` : concavity of the
  perspective of `log` and of the ideal-gas entropy.
- `sideal_dSdU_at_N_zero`, `sideal_EOS_fails_at_N_zero` : boundary countermodel.

## iii. Table of contents

- A. Equilibrium states and the fundamental relation
- B. The first law and the Euler relation
- C. Gibbs-Duhem
- D. Entropy maximum and heat flow
- E. The ideal gas

## iv. References

- H. B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed.,
  Wiley, 1985: the postulates and the fundamental relation (Ch. 1), equal
  temperatures and the direction of heat flow (Ch. 2), the Euler and Gibbs-Duhem
  relations and the simple ideal gas (Ch. 3), stability and concavity (Ch. 8).
- MIT OpenCourseWare, 5.60 *Thermodynamics & Kinetics*: state functions,
  reversible changes, the ideal gas.
- IUPAC Green Book: quantity language for `U`, `V`, `N`, `S`, `T`, `p`, `μ`.

-/

@[expose] public section

namespace Chemistry.Thermodynamics

open scoped BigOperators Topology

/-!

## A. Equilibrium states and the fundamental relation

-/

/-- Equilibrium state space of a simple system with `k` species: internal energy,
volume and species amounts. -/
abbrev ThermoState (k : ℕ) : Type := ℝ × ℝ × (Fin k → ℝ)

/-- The physical domain: `U > 0`, `V > 0` and every `N i > 0`. -/
def thermoDomain (k : ℕ) : Set (ThermoState k) :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ∧ ∀ i, 0 < x.2.2 i}

/-- The physical domain is open. -/
lemma isOpen_thermoDomain (k : ℕ) : IsOpen (thermoDomain k) := by
  have h1 : IsOpen {x : ThermoState k | 0 < x.1} :=
    isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {x : ThermoState k | 0 < x.2.1} :=
    isOpen_lt continuous_const (continuous_fst.comp continuous_snd)
  have h3 : ∀ i : Fin k, IsOpen {x : ThermoState k | 0 < x.2.2 i} := fun i =>
    isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hN : IsOpen (⋂ i, {x : ThermoState k | 0 < x.2.2 i}) :=
    isOpen_iInter_of_finite h3
  have hdecomp : thermoDomain k =
      {x : ThermoState k | 0 < x.1} ∩ {x : ThermoState k | 0 < x.2.1} ∩
        ⋂ i, {x : ThermoState k | 0 < x.2.2 i} := by
    ext x
    simp [thermoDomain, and_assoc]
  rw [hdecomp]
  exact (h1.inter h2).inter hN

/-- Partial derivative of `S` with respect to `U`: the `deriv` of the
single-variable slice varying `U` at fixed `V`, `N`. Where the slice is not
differentiable, this is Lean's junk value `0`. -/
noncomputable def dSdU {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k) : ℝ :=
  deriv (fun u => S (u, x.2.1, x.2.2)) x.1

/-- Partial derivative of `S` with respect to `V`: the `deriv` of the
single-variable slice varying `V` at fixed `U`, `N`. Where the slice is not
differentiable, this is Lean's junk value `0`. -/
noncomputable def dSdV {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k) : ℝ :=
  deriv (fun v => S (x.1, v, x.2.2)) x.2.1

/-- Partial derivative of `S` with respect to `N i`: the `deriv` of the
single-variable slice varying `N i` through `Function.update` at fixed `U`, `V`
and the other amounts. Where the slice is not differentiable, this is Lean's junk
value `0`. -/
noncomputable def dSdN {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k)
    (i : Fin k) : ℝ :=
  deriv (fun n => S (x.1, x.2.1, Function.update x.2.2 i n)) (x.2.2 i)

/-- Absolute temperature as a partial derivative of entropy: `T = 1 / (∂S/∂U)`.
Physically meaningful where `∂S/∂U > 0`, as on the domain of a
`FundamentalRelation`; where `∂S/∂U = 0` the value is Lean's junk `1 / 0 = 0`. -/
noncomputable def temp {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k) : ℝ :=
  1 / dSdU S x

/-- Pressure as a partial derivative of entropy: `p = T * (∂S/∂V)`. Physically
meaningful on the domain of a `FundamentalRelation`; elsewhere it inherits the junk
values of `temp` and `dSdV`. -/
noncomputable def press {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k) : ℝ :=
  temp S x * dSdV S x

/-- Chemical potential of species `i` as a partial derivative of entropy:
`μᵢ = -T * (∂S/∂Nᵢ)`. Physically meaningful on the domain of a
`FundamentalRelation`; elsewhere it inherits the junk values of `temp` and `dSdN`. -/
noncomputable def chemPot {k : ℕ} (S : ThermoState k → ℝ) (x : ThermoState k)
    (i : Fin k) : ℝ :=
  -temp S x * dSdN S x i

/-- The equilibrium postulates for the entropy of a simple system with `k` species,
carried as structure hypotheses (LAW), not global axioms. On the open domain
`thermoDomain k`, `S` is Fréchet differentiable, concave, positively homogeneous of
degree 1, and has `∂S/∂U > 0`; the fields constrain `S` only on the domain. The chain
rule along curves, the Euler relation, Gibbs-Duhem and the equations of state are
proved below, never assumed here. -/
structure FundamentalRelation (k : ℕ) where
  /-- The entropy function on equilibrium states. -/
  S : ThermoState k → ℝ
  /-- `S` is Fréchet differentiable on the open domain. -/
  h_diff : DifferentiableOn ℝ S (thermoDomain k)
  /-- Entropy is concave on the domain (the stability condition). -/
  h_concave : ConcaveOn ℝ (thermoDomain k) S
  /-- Entropy is positively homogeneous of degree 1. -/
  h_homog : ∀ x ∈ thermoDomain k, ∀ t : ℝ, 0 < t →
    S (t * x.1, t * x.2.1, t • x.2.2) = t * S x
  /-- Entropy increases with `U`: `∂S/∂U > 0` on the domain. Strict monotonicity in
  `U` follows (`FundamentalRelation.strictMonoOn_energy`). -/
  h_pos : ∀ x ∈ thermoDomain k, 0 < dSdU S x

/-- `S` is Fréchet differentiable at every state of the open domain. -/
lemma FundamentalRelation.differentiableAt {k : ℕ} (F : FundamentalRelation k)
    {x : ThermoState k} (hx : x ∈ thermoDomain k) : DifferentiableAt ℝ F.S x :=
  F.h_diff.differentiableAt ((isOpen_thermoDomain k).mem_nhds hx)

/-- Where `S` is differentiable, the `U`-slice partial `dSdU` is the Fréchet
derivative of `S` in the direction `(1, 0, 0)`. -/
lemma dSdU_eq_fderiv {k : ℕ} {S : ThermoState k → ℝ} {x : ThermoState k}
    (hS : DifferentiableAt ℝ S x) : dSdU S x = fderiv ℝ S x (1, 0, 0) := by
  have hγ : HasDerivAt (fun u : ℝ => ((u, x.2.1, x.2.2) : ThermoState k))
      ((1, 0, 0) : ThermoState k) x.1 :=
    (hasDerivAt_id x.1).prodMk
      ((hasDerivAt_const x.1 x.2.1).prodMk (hasDerivAt_const x.1 x.2.2))
  exact (hS.hasFDerivAt.comp_hasDerivAt x.1 hγ).deriv

/-- Where `S` is differentiable, the `V`-slice partial `dSdV` is the Fréchet
derivative of `S` in the direction `(0, 1, 0)`. -/
lemma dSdV_eq_fderiv {k : ℕ} {S : ThermoState k → ℝ} {x : ThermoState k}
    (hS : DifferentiableAt ℝ S x) : dSdV S x = fderiv ℝ S x (0, 1, 0) := by
  have hγ : HasDerivAt (fun v : ℝ => ((x.1, v, x.2.2) : ThermoState k))
      ((0, 1, 0) : ThermoState k) x.2.1 :=
    (hasDerivAt_const x.2.1 x.1).prodMk
      ((hasDerivAt_id x.2.1).prodMk (hasDerivAt_const x.2.1 x.2.2))
  exact (hS.hasFDerivAt.comp_hasDerivAt x.2.1 hγ).deriv

/-- Where `S` is differentiable, the `N i`-slice partial `dSdN` is the Fréchet
derivative of `S` in the direction `(0, 0, Pi.single i 1)`. -/
lemma dSdN_eq_fderiv {k : ℕ} {S : ThermoState k → ℝ} {x : ThermoState k}
    (hS : DifferentiableAt ℝ S x) (i : Fin k) :
    dSdN S x i = fderiv ℝ S x (0, 0, Pi.single i 1) := by
  have hγ : HasDerivAt
      (fun n : ℝ => ((x.1, x.2.1, Function.update x.2.2 i n) : ThermoState k))
      ((0, 0, Pi.single i 1) : ThermoState k) (x.2.2 i) :=
    (hasDerivAt_const _ x.1).prodMk
      ((hasDerivAt_const _ x.2.1).prodMk (hasDerivAt_update x.2.2 i (x.2.2 i)))
  have hS' : HasFDerivAt S (fderiv ℝ S x)
      ((x.1, x.2.1, Function.update x.2.2 i (x.2.2 i)) : ThermoState k) := by
    rw [Function.update_eq_self]
    exact hS.hasFDerivAt
  exact (hS'.comp_hasDerivAt (x.2.2 i) hγ).deriv

/-- Chain rule along a curve of states: if the curve components have derivatives
`U'`, `V'`, `N' i` at `t0` and `S` is differentiable at the state
`(γU t0, γV t0, γN t0)`, then `S` along the curve has derivative
`∂S/∂U * U' + ∂S/∂V * V' + ∑ ∂S/∂Nᵢ * N'ᵢ` at `t0`. Proved from the Fréchet
derivative by decomposing `(U', V', N')` along the coordinate directions. For a
`FundamentalRelation`, `FundamentalRelation.differentiableAt` supplies `hS` from
`h_diff`. -/
lemma hasDerivAt_comp_curve {k : ℕ} {S : ThermoState k → ℝ} {γU γV : ℝ → ℝ}
    {γN : ℝ → Fin k → ℝ} {U' V' : ℝ} {N' : Fin k → ℝ} {t0 : ℝ}
    (hU : HasDerivAt γU U' t0) (hV : HasDerivAt γV V' t0)
    (hN : ∀ i, HasDerivAt (fun t => γN t i) (N' i) t0)
    (hS : DifferentiableAt ℝ S (γU t0, γV t0, γN t0)) :
    HasDerivAt (fun t => S (γU t, γV t, γN t))
      (dSdU S (γU t0, γV t0, γN t0) * U' + dSdV S (γU t0, γV t0, γN t0) * V' +
        ∑ i, dSdN S (γU t0, γV t0, γN t0) i * N' i) t0 := by
  have hγ : HasDerivAt (fun t => ((γU t, γV t, γN t) : ThermoState k))
      ((U', V', N') : ThermoState k) t0 :=
    hU.prodMk (hV.prodMk (hasDerivAt_pi.2 hN))
  have hdecomp : ((U', V', N') : ThermoState k) =
      U' • ((1, 0, 0) : ThermoState k) + V' • ((0, 1, 0) : ThermoState k) +
        ∑ i, N' i • ((0, 0, Pi.single i 1) : ThermoState k) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Prod.fst_sum]
    · ext j
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hval : fderiv ℝ S (γU t0, γV t0, γN t0) ((U', V', N') : ThermoState k) =
      dSdU S (γU t0, γV t0, γN t0) * U' + dSdV S (γU t0, γV t0, γN t0) * V' +
        ∑ i, dSdN S (γU t0, γV t0, γN t0) i * N' i := by
    rw [hdecomp, map_add, map_add, map_sum, map_smul, map_smul,
      dSdU_eq_fderiv hS, dSdV_eq_fderiv hS, smul_eq_mul, smul_eq_mul,
      mul_comm U', mul_comm V']
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, dSdN_eq_fderiv hS, mul_comm]
  rw [← hval]
  exact hS.hasFDerivAt.comp_hasDerivAt t0 hγ

/-- Temperature is positive on the domain. -/
lemma temp_pos {k : ℕ} (F : FundamentalRelation k) (x : ThermoState k)
    (hx : x ∈ thermoDomain k) : 0 < temp F.S x :=
  one_div_pos.mpr (F.h_pos x hx)

/-- Entropy is strictly increasing in `U` at fixed positive `V` and `N`: a
consequence of `∂S/∂U > 0` and differentiability. -/
lemma FundamentalRelation.strictMonoOn_energy {k : ℕ} (F : FundamentalRelation k)
    {V : ℝ} {N : Fin k → ℝ} (hV : 0 < V) (hN : ∀ i, 0 < N i) :
    StrictMonoOn (fun u => F.S (u, V, N)) (Set.Ioi 0) := by
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u => F.S (u, V, N)) (dSdU F.S (u, V, N)) u := by
    intro u hu
    simpa using hasDerivAt_comp_curve (hasDerivAt_id' u) (hasDerivAt_const u V)
      (fun i => hasDerivAt_const u (N i)) (F.differentiableAt ⟨hu, hV, hN⟩)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun u hu => (hderiv u hu).continuousAt.continuousWithinAt) fun u hu => ?_
  rw [interior_Ioi] at hu
  rw [(hderiv u hu).deriv]
  exact F.h_pos _ ⟨hu, hV, hN⟩

/-!

## B. The first law and the Euler relation

-/

/-- Pure-algebra core of the first-law identity: with `T = 1/SU`, `p = T*SV` and
`μᵢ = -T*SNᵢ`, the rate `U'` equals `T` times the total differential minus the
`p dV` term plus the chemical terms. -/
lemma firstLaw_algebra {k : ℕ} (SU SV U' V' T p : ℝ) (SN N' mu : Fin k → ℝ)
    (hSU : SU ≠ 0) (hT : T = 1 / SU) (hp : p = T * SV)
    (hmu : ∀ i, mu i = -T * SN i) :
    U' = T * (SU * U' + SV * V' + ∑ i, SN i * N' i) - p * V' +
      ∑ i, mu i * N' i := by
  simp only [hT, hp, hmu]
  have hsum : (∑ i, (-(1 / SU) * SN i) * N' i) =
      -(1 / SU) * (∑ i, SN i * N' i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  set c := 1 / SU with hc
  have h1 : SU * c = 1 := by
    rw [hc, one_div]
    exact mul_inv_cancel₀ hSU
  linear_combination -U' * h1

/-- Pure-algebra core of the Euler relation: with `T = 1/SU`, `p = T*SV` and
`μᵢ = -T*SNᵢ`, the homogeneous-function identity `SU*U + SV*V + ∑ SNᵢNᵢ = S`
rearranges to `U = TS - pV + ∑ μᵢNᵢ`. -/
lemma euler_algebra {k : ℕ} (SU SV Sx U V T p : ℝ) (SN N mu : Fin k → ℝ)
    (hSU : SU ≠ 0) (hT : T = 1 / SU) (hp : p = T * SV)
    (hmu : ∀ i, mu i = -T * SN i)
    (he : SU * U + SV * V + ∑ i, SN i * N i = Sx) :
    U = T * Sx - p * V + ∑ i, mu i * N i := by
  simp only [hT, hp, hmu]
  have hsum : (∑ i, (-(1 / SU) * SN i) * N i) =
      -(1 / SU) * (∑ i, SN i * N i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum]
  set c := 1 / SU with hc
  have h1 : SU * c = 1 := by
    rw [hc, one_div]
    exact mul_inv_cancel₀ hSU
  linear_combination c * he - U * h1

/-- First-law identity in total-differential-value form: `U'` equals `T` times
the total differential of `S` (the derivative along a curve given by
`hasDerivAt_comp_curve`) minus `p V'` plus the chemical terms. -/
lemma firstLaw_value {k : ℕ} (F : FundamentalRelation k) (x : ThermoState k)
    (U' V' : ℝ) (N' : Fin k → ℝ) (hx : x ∈ thermoDomain k) :
    U' = temp F.S x *
        (dSdU F.S x * U' + dSdV F.S x * V' + ∑ i, dSdN F.S x i * N' i) -
        press F.S x * V' + ∑ i, chemPot F.S x i * N' i :=
  firstLaw_algebra (dSdU F.S x) (dSdV F.S x) U' V' (temp F.S x) (press F.S x)
    (dSdN F.S x) N' (chemPot F.S x) (ne_of_gt (F.h_pos x hx)) rfl rfl
    (fun _ => rfl)

/-- First law along a differentiable curve of states: `dU/dt = T dS/dt - p dV/dt +
∑ μᵢ dNᵢ/dt`, where `dS/dt` is the `deriv` of `S` along the curve, identified with
the total differential by the chain rule `hasDerivAt_comp_curve`. -/
lemma firstLaw {k : ℕ} (F : FundamentalRelation k) (γU γV : ℝ → ℝ)
    (γN : ℝ → Fin k → ℝ) (U' V' : ℝ) (N' : Fin k → ℝ) (t0 : ℝ)
    (hU : HasDerivAt γU U' t0) (hV : HasDerivAt γV V' t0)
    (hN : ∀ i, HasDerivAt (fun t => γN t i) (N' i) t0)
    (hx : (γU t0, γV t0, γN t0) ∈ thermoDomain k) :
    U' = temp F.S (γU t0, γV t0, γN t0) *
        deriv (fun t => F.S (γU t, γV t, γN t)) t0 -
        press F.S (γU t0, γV t0, γN t0) * V' +
        ∑ i, chemPot F.S (γU t0, γV t0, γN t0) i * N' i := by
  rw [(hasDerivAt_comp_curve hU hV hN (F.differentiableAt hx)).deriv]
  exact firstLaw_value F (γU t0, γV t0, γN t0) U' V' N' hx

/-- Euler homogeneous-function identity (differential form): differentiating
`S(tU, tV, tN) = t * S(U, V, N)` at `t = 1` gives
`SU*U + SV*V + ∑ SNᵢNᵢ = S`. Uses homogeneity `h_homog` and the chain rule
`hasDerivAt_comp_curve` along the ray. -/
lemma euler_homogeneous_function {k : ℕ} (F : FundamentalRelation k)
    (x : ThermoState k) (hx : x ∈ thermoDomain k) :
    dSdU F.S x * x.1 + dSdV F.S x * x.2.1 +
      ∑ i, dSdN F.S x i * x.2.2 i = F.S x := by
  have hU : HasDerivAt (fun t : ℝ => t * x.1) x.1 1 := by
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const x.1
  have hV : HasDerivAt (fun t : ℝ => t * x.2.1) x.2.1 1 := by
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const x.2.1
  have hN : ∀ i : Fin k, HasDerivAt (fun t : ℝ => (t • x.2.2) i) (x.2.2 i)
      1 := by
    intro i
    change HasDerivAt (fun t : ℝ => t * x.2.2 i) (x.2.2 i) 1
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const (x.2.2 i)
  have hpt : ((fun s : ℝ => s * x.1) 1, (fun s : ℝ => s * x.2.1) 1,
      (fun s : ℝ => s • x.2.2) 1) = x := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have hS : DifferentiableAt ℝ F.S ((fun s : ℝ => s * x.1) 1,
      (fun s : ℝ => s * x.2.1) 1, (fun s : ℝ => s • x.2.2) 1) := by
    rw [hpt]
    exact F.differentiableAt hx
  have hchain := hasDerivAt_comp_curve (γU := fun s : ℝ => s * x.1)
    (γV := fun s : ℝ => s * x.2.1) (γN := fun s : ℝ => s • x.2.2) hU hV hN hS
  have heq : (fun t : ℝ => F.S ((fun s : ℝ => s * x.1) t,
      (fun s : ℝ => s * x.2.1) t, (fun s : ℝ => s • x.2.2) t)) =ᶠ[𝓝 (1 : ℝ)]
      (fun t : ℝ => t * F.S x) :=
    (eventually_gt_nhds zero_lt_one).mono fun t ht => F.h_homog x hx t ht
  have hRHS : HasDerivAt (fun t : ℝ => t * F.S x) (F.S x) 1 := by
    simpa using (hasDerivAt_id' (1 : ℝ)).mul_const (F.S x)
  have hLHS : HasDerivAt (fun t : ℝ => F.S ((fun s : ℝ => s * x.1) t,
      (fun s : ℝ => s * x.2.1) t, (fun s : ℝ => s • x.2.2) t)) (F.S x) 1 :=
    hRHS.congr_of_eventuallyEq heq
  rw [hpt] at hchain
  exact hchain.unique hLHS

/-- Euler relation: `U = T*S - p*V + ∑ μᵢ*Nᵢ`, from homogeneity via
`euler_homogeneous_function`. -/
lemma euler_relation {k : ℕ} (F : FundamentalRelation k) (x : ThermoState k)
    (hx : x ∈ thermoDomain k) :
    x.1 = temp F.S x * F.S x - press F.S x * x.2.1 +
      ∑ i, chemPot F.S x i * x.2.2 i :=
  euler_algebra (dSdU F.S x) (dSdV F.S x) (F.S x) x.1 x.2.1 (temp F.S x)
    (press F.S x) (dSdN F.S x) x.2.2 (chemPot F.S x)
    (ne_of_gt (F.h_pos x hx)) rfl rfl (fun _ => rfl)
    (euler_homogeneous_function F x hx)

/-!

## C. Gibbs-Duhem

-/

/-- Gibbs-Duhem relation in derivative form along a curve: if `T`, `p` and the
`μᵢ` have derivatives `T'`, `p'`, `μ'` along the curve at `t0`, then
`S*T' - V*p' + ∑ Nᵢ*μ'ᵢ = 0`. Proved by differentiating the Euler relation
along the curve and subtracting the first-law identity; `hev` (the curve stays in
the domain near `t0`) is what lets the Euler relation be differentiated. The
differentiability of `T`, `p`, `μ` along the curve is an explicit hypothesis, not a
consequence of the first-order postulates. -/
lemma gibbsDuhem {k : ℕ} (F : FundamentalRelation k) (γU γV : ℝ → ℝ)
    (γN : ℝ → Fin k → ℝ) (U' V' T' p' : ℝ) (N' mu' : Fin k → ℝ) (t0 : ℝ)
    (hU : HasDerivAt γU U' t0) (hV : HasDerivAt γV V' t0)
    (hN : ∀ i, HasDerivAt (fun t => γN t i) (N' i) t0)
    (hx : (γU t0, γV t0, γN t0) ∈ thermoDomain k)
    (hev : ∀ᶠ t in 𝓝 t0, (γU t, γV t, γN t) ∈ thermoDomain k)
    (hT : HasDerivAt (fun t => temp F.S (γU t, γV t, γN t)) T' t0)
    (hp : HasDerivAt (fun t => press F.S (γU t, γV t, γN t)) p' t0)
    (hmu : ∀ i, HasDerivAt (fun t => chemPot F.S (γU t, γV t, γN t) i)
      (mu' i) t0) :
    F.S (γU t0, γV t0, γN t0) * T' - γV t0 * p' +
      ∑ i, γN t0 i * mu' i = 0 := by
  have hS : HasDerivAt (fun t => F.S (γU t, γV t, γN t))
      (dSdU F.S (γU t0, γV t0, γN t0) * U' +
        dSdV F.S (γU t0, γV t0, γN t0) * V' +
        ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i) t0 :=
    hasDerivAt_comp_curve hU hV hN (F.differentiableAt hx)
  have hTS : HasDerivAt
      (fun t => temp F.S (γU t, γV t, γN t) * F.S (γU t, γV t, γN t))
      (T' * F.S (γU t0, γV t0, γN t0) + temp F.S (γU t0, γV t0, γN t0) *
        (dSdU F.S (γU t0, γV t0, γN t0) * U' +
          dSdV F.S (γU t0, γV t0, γN t0) * V' +
          ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i)) t0 :=
    hT.mul hS
  have hPV : HasDerivAt (fun t => press F.S (γU t, γV t, γN t) * γV t)
      (p' * γV t0 + press F.S (γU t0, γV t0, γN t0) * V') t0 :=
    hp.mul hV
  have hsum : HasDerivAt
      (fun t => ∑ i, chemPot F.S (γU t, γV t, γN t) i * γN t i)
      (∑ i, (mu' i * γN t0 i +
        chemPot F.S (γU t0, γV t0, γN t0) i * N' i)) t0 :=
    HasDerivAt.fun_sum (fun i _ => (hmu i).mul (hN i))
  have hRHS : HasDerivAt
      (fun t => temp F.S (γU t, γV t, γN t) * F.S (γU t, γV t, γN t) -
        press F.S (γU t, γV t, γN t) * γV t +
        ∑ i, chemPot F.S (γU t, γV t, γN t) i * γN t i)
      ((T' * F.S (γU t0, γV t0, γN t0) + temp F.S (γU t0, γV t0, γN t0) *
          (dSdU F.S (γU t0, γV t0, γN t0) * U' +
            dSdV F.S (γU t0, γV t0, γN t0) * V' +
            ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i)) -
        (p' * γV t0 + press F.S (γU t0, γV t0, γN t0) * V') +
        ∑ i, (mu' i * γN t0 i +
          chemPot F.S (γU t0, γV t0, γN t0) i * N' i)) t0 :=
    (hTS.sub hPV).add hsum
  have hevE : γU =ᶠ[𝓝 t0] (fun t =>
      temp F.S (γU t, γV t, γN t) * F.S (γU t, γV t, γN t) -
        press F.S (γU t, γV t, γN t) * γV t +
        ∑ i, chemPot F.S (γU t, γV t, γN t) i * γN t i) :=
    hev.mono fun t ht => euler_relation F (γU t, γV t, γN t) ht
  have hγ : HasDerivAt γU
      ((T' * F.S (γU t0, γV t0, γN t0) + temp F.S (γU t0, γV t0, γN t0) *
          (dSdU F.S (γU t0, γV t0, γN t0) * U' +
            dSdV F.S (γU t0, γV t0, γN t0) * V' +
            ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i)) -
        (p' * γV t0 + press F.S (γU t0, γV t0, γN t0) * V') +
        ∑ i, (mu' i * γN t0 i +
          chemPot F.S (γU t0, γV t0, γN t0) i * N' i)) t0 :=
    hRHS.congr_of_eventuallyEq hevE
  have hUU : (T' * F.S (γU t0, γV t0, γN t0) +
        temp F.S (γU t0, γV t0, γN t0) *
          (dSdU F.S (γU t0, γV t0, γN t0) * U' +
            dSdV F.S (γU t0, γV t0, γN t0) * V' +
            ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i)) -
      (p' * γV t0 + press F.S (γU t0, γV t0, γN t0) * V') +
      (∑ i, mu' i * γN t0 i +
        ∑ i, chemPot F.S (γU t0, γV t0, γN t0) i * N' i) = U' := by
    have huniq := hγ.unique hU
    rwa [Finset.sum_add_distrib] at huniq
  have hfirst : U' = temp F.S (γU t0, γV t0, γN t0) *
        (dSdU F.S (γU t0, γV t0, γN t0) * U' +
          dSdV F.S (γU t0, γV t0, γN t0) * V' +
          ∑ i, dSdN F.S (γU t0, γV t0, γN t0) i * N' i) -
        press F.S (γU t0, γV t0, γN t0) * V' +
        ∑ i, chemPot F.S (γU t0, γV t0, γN t0) i * N' i :=
    firstLaw_value F (γU t0, γV t0, γN t0) U' V' N' hx
  have hcomm : (∑ i, γN t0 i * mu' i) = ∑ i, mu' i * γN t0 i :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hcomm]
  linear_combination hUU + hfirst

/-!

## D. Entropy maximum and heat flow

Two subsystems with the same fundamental relation `F`, fixed volumes and amounts per
subsystem, exchanging energy at fixed total `U₁ + U₂ = Utot`.

-/

/-- Total-entropy derivative along the energy-exchange curve: `dStot/dU₁` is the
difference of the two `∂S/∂U` values, by the chain rule `hasDerivAt_comp_curve` on
each leg. -/
lemma stot_hasDerivAt {k : ℕ} (F : FundamentalRelation k) (V1 V2 Utot Ustar : ℝ)
    (N1 N2 : Fin k → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain k)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain k) :
    HasDerivAt (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2))
      (dSdU F.S (Ustar, V1, N1) + -dSdU F.S (Utot - Ustar, V2, N2))
      Ustar := by
  have hS1 : HasDerivAt (fun t => F.S (t, V1, N1))
      (dSdU F.S (Ustar, V1, N1)) Ustar := by
    simpa using hasDerivAt_comp_curve (γN := fun _ => N1) (hasDerivAt_id' Ustar)
      (hasDerivAt_const Ustar V1) (fun i => hasDerivAt_const Ustar (N1 i))
      (F.differentiableAt hx1)
  have hU2 : HasDerivAt (fun t : ℝ => Utot - t) (-1) Ustar :=
    HasDerivAt.const_sub Utot (hasDerivAt_id' Ustar)
  have hS2 : HasDerivAt (fun t => F.S (Utot - t, V2, N2))
      (-dSdU F.S (Utot - Ustar, V2, N2)) Ustar := by
    simpa using hasDerivAt_comp_curve (γN := fun _ => N2) hU2
      (hasDerivAt_const Ustar V2) (fun i => hasDerivAt_const Ustar (N2 i))
      (F.differentiableAt hx2)
  exact hS1.add hS2

/-- At an interior local maximizer of total entropy, the two subsystem
temperatures agree. No global maximum is claimed: the maximizer hypothesis is
explicit. -/
lemma entropyMax_temperature_eq {k : ℕ} (F : FundamentalRelation k) (V1 V2 Utot Ustar : ℝ)
    (N1 N2 : Fin k → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain k)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain k)
    (hmax : IsLocalMax
      (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2)) Ustar) :
    temp F.S (Ustar, V1, N1) = temp F.S (Utot - Ustar, V2, N2) := by
  have hStot := stot_hasDerivAt F V1 V2 Utot Ustar N1 N2 hx1 hx2
  have h0 := hmax.hasDerivAt_eq_zero hStot
  have hSU : dSdU F.S (Ustar, V1, N1) = dSdU F.S (Utot - Ustar, V2, N2) := by
    linarith
  change 1 / dSdU F.S (Ustar, V1, N1) = 1 / dSdU F.S (Utot - Ustar, V2, N2)
  rw [hSU]

/-- The `deriv` form of the total-entropy rate: `dStot/dU₁ = SU₁ - SU₂`. -/
lemma stot_deriv_eq {k : ℕ} (F : FundamentalRelation k) (V1 V2 Utot Ustar : ℝ)
    (N1 N2 : Fin k → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain k)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain k) :
    deriv (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2)) Ustar =
      dSdU F.S (Ustar, V1, N1) - dSdU F.S (Utot - Ustar, V2, N2) := by
  have hder := (stot_hasDerivAt F V1 V2 Utot Ustar N1 N2 hx1 hx2).deriv
  rwa [sub_eq_add_neg]

/-- Hot-to-cold sign in derivative form: if subsystem 1 is hotter than subsystem
2 (`T₁ > T₂`), then `dStot/dU₁ < 0` at the point, so transferring energy from 1
to 2 (decreasing `U₁`) increases total entropy to first order. -/
lemma entropyFlow_sign {k : ℕ} (F : FundamentalRelation k) (V1 V2 Utot Ustar : ℝ)
    (N1 N2 : Fin k → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain k)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain k)
    (hT : temp F.S (Utot - Ustar, V2, N2) < temp F.S (Ustar, V1, N1)) :
    deriv (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2)) Ustar < 0 := by
  rw [stot_deriv_eq F V1 V2 Utot Ustar N1 N2 hx1 hx2]
  have e1 : dSdU F.S (Ustar, V1, N1) = 1 / temp F.S (Ustar, V1, N1) := by
    unfold temp
    rw [one_div_one_div]
  have e2 : dSdU F.S (Utot - Ustar, V2, N2) =
      1 / temp F.S (Utot - Ustar, V2, N2) := by
    unfold temp
    rw [one_div_one_div]
  rw [e1, e2]
  exact sub_neg.mpr
    (one_div_lt_one_div_of_lt (temp_pos F (Utot - Ustar, V2, N2) hx2) hT)

/-!

## E. The ideal gas

A concrete entropy model (MOD): the Sackur-Tetrode-style fundamental relation
for a monatomic ideal gas with one species. `idealGas` packages it as a
`FundamentalRelation 1` for `kB > 0`, proving every postulate, so the results of
sections A to D apply to it.

-/

/-- Ideal-gas entropy (MOD): `S = N * kB * (log (V/N) + (3/2) * log (U/N) + s0)`
with a symbolic constant `kB` (per-particle Boltzmann constant, energy per
temperature per particle; positive in the lemmas that need it) and dimensionless
reference entropy per particle `s0` (absorbing the thermal-wavelength and
reference-state constants). Physical domain: `U > 0`, `V > 0`, `N > 0`; outside it
the value is junk fixed by Lean's conventions (`Real.log` of a nonpositive argument,
division by zero). -/
noncomputable def Sideal (kB s0 U V N : ℝ) : ℝ :=
  N * kB * (Real.log (V / N) + 3 / 2 * Real.log (U / N) + s0)

/-- On the physical domain `Sideal` is Physlib's monophase ideal-gas entropy
`_root_.entropy c R s0 U0 V0 N0` with `c = 3/2`, `R = kB`, reference entropy `kB * s0` per
particle and the unit reference state `U0 = V0 = N0 = 1`. -/
lemma sideal_eq_entropy (kB s0 U V N : ℝ) (hU : 0 < U) (hV : 0 < V) (hN : 0 < N) :
    Sideal kB s0 U V N = _root_.entropy (3 / 2) kB (kB * s0) 1 1 1 U V N := by
  simp only [Sideal, _root_.entropy, div_one]
  rw [Real.log_div hV.ne' hN.ne', Real.log_div hU.ne' hN.ne']
  ring

/-- The ideal-gas entropy as a function on single-species equilibrium states.
Physically meaningful on `thermoDomain 1`; elsewhere it inherits the junk values of
`Sideal`. -/
noncomputable def SidealGen (kB s0 : ℝ) : ThermoState 1 → ℝ :=
  fun x => Sideal kB s0 x.1 x.2.1 (x.2.2 0)

/-- `U`-slice derivative of the ideal-gas entropy. -/
lemma sideal_dSdU_hasDerivAt (kB s0 U V N : ℝ) (hU : 0 < U) (hN : 0 < N) :
    HasDerivAt (fun u => Sideal kB s0 u V N) (3 * N * kB / (2 * U)) U := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hU0 : U ≠ 0 := ne_of_gt hU
  have hinner : HasDerivAt (fun u : ℝ => u / N) (1 / N) U :=
    (hasDerivAt_id' U).div_const N
  have hlog : HasDerivAt (fun u : ℝ => Real.log (u / N))
      ((1 / N) / (U / N)) U :=
    hinner.log (div_ne_zero hU0 hN0)
  have hfun : (fun u => Sideal kB s0 u V N) = (fun u =>
      N * kB * (Real.log (V / N) + s0) + (N * kB * (3 / 2)) *
        Real.log (u / N)) := by
    funext u
    simp only [Sideal]
    ring
  have hbuilt : HasDerivAt (fun u =>
      N * kB * (Real.log (V / N) + s0) + (N * kB * (3 / 2)) *
        Real.log (u / N)) (0 + (N * kB * (3 / 2)) * ((1 / N) / (U / N)))
      U :=
    (hasDerivAt_const U (N * kB * (Real.log (V / N) + s0))).add
      (hlog.const_mul (N * kB * (3 / 2)))
  have hval : (0 + (N * kB * (3 / 2)) * ((1 / N) / (U / N))) =
      3 * N * kB / (2 * U) := by
    field_simp [hN0, hU0]
    ring
  rw [hfun]
  rw [hval] at hbuilt
  exact hbuilt

/-- The `∂S/∂U` slice partial of the ideal gas. -/
lemma sideal_dSdU (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hN : 0 < x.2.2 0) :
    dSdU (SidealGen kB s0) x = 3 * x.2.2 0 * kB / (2 * x.1) :=
  (sideal_dSdU_hasDerivAt kB s0 x.1 x.2.1 (x.2.2 0) hU hN).deriv

/-- `V`-slice derivative of the ideal-gas entropy. -/
lemma sideal_dSdV_hasDerivAt (kB s0 U V N : ℝ) (hV : 0 < V) (hN : 0 < N) :
    HasDerivAt (fun v => Sideal kB s0 U v N) (N * kB / V) V := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hinner : HasDerivAt (fun v : ℝ => v / N) (1 / N) V :=
    (hasDerivAt_id' V).div_const N
  have hlog : HasDerivAt (fun v : ℝ => Real.log (v / N))
      ((1 / N) / (V / N)) V :=
    hinner.log (div_ne_zero hV0 hN0)
  have hfun : (fun v => Sideal kB s0 U v N) = (fun v =>
      N * kB * (3 / 2 * Real.log (U / N) + s0) + (N * kB) *
        Real.log (v / N)) := by
    funext v
    simp only [Sideal]
    ring
  have hbuilt : HasDerivAt (fun v =>
      N * kB * (3 / 2 * Real.log (U / N) + s0) + (N * kB) *
        Real.log (v / N)) (0 + (N * kB) * ((1 / N) / (V / N))) V :=
    (hasDerivAt_const V (N * kB * (3 / 2 * Real.log (U / N) + s0))).add
      (hlog.const_mul (N * kB))
  have hval : (0 + (N * kB) * ((1 / N) / (V / N))) = N * kB / V := by
    field_simp [hN0, hV0]
    ring
  rw [hfun]
  rw [hval] at hbuilt
  exact hbuilt

/-- The `∂S/∂V` slice partial of the ideal gas. -/
lemma sideal_dSdV (kB s0 : ℝ) (x : ThermoState 1) (hV : 0 < x.2.1)
    (hN : 0 < x.2.2 0) :
    dSdV (SidealGen kB s0) x = x.2.2 0 * kB / x.2.1 :=
  (sideal_dSdV_hasDerivAt kB s0 x.1 x.2.1 (x.2.2 0) hV hN).deriv

/-- `N`-slice derivative of the ideal-gas entropy. -/
lemma sideal_dSdN_hasDerivAt (kB s0 U V N : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hN : 0 < N) :
    HasDerivAt (fun n => Sideal kB s0 U V n)
      (kB * (Real.log (V / N) + 3 / 2 * Real.log (U / N) + s0 - 5 / 2)) N := by
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hU0 : U ≠ 0 := ne_of_gt hU
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hf : HasDerivAt (fun n : ℝ => n * kB) kB N := by
    simpa using (hasDerivAt_id' N).mul_const kB
  have hVd : HasDerivAt (fun n : ℝ => V / n) ((0 * N - V * 1) / N ^ 2) N :=
    (hasDerivAt_const N V).div (hasDerivAt_id' N) hN0
  have hVlog : HasDerivAt (fun n : ℝ => Real.log (V / n))
      (((0 * N - V * 1) / N ^ 2) / (V / N)) N :=
    hVd.log (div_ne_zero hV0 hN0)
  have hUd : HasDerivAt (fun n : ℝ => U / n) ((0 * N - U * 1) / N ^ 2) N :=
    (hasDerivAt_const N U).div (hasDerivAt_id' N) hN0
  have hUlog : HasDerivAt (fun n : ℝ => Real.log (U / n))
      (((0 * N - U * 1) / N ^ 2) / (U / N)) N :=
    hUd.log (div_ne_zero hU0 hN0)
  have hg : HasDerivAt
      (fun n : ℝ => Real.log (V / n) + 3 / 2 * Real.log (U / n) + s0)
      ((((0 * N - V * 1) / N ^ 2) / (V / N)) +
        (3 / 2) * (((0 * N - U * 1) / N ^ 2) / (U / N)) + 0) N :=
    (hVlog.add (hUlog.const_mul (3 / 2))).add (hasDerivAt_const N s0)
  have hfun : (fun n => Sideal kB s0 U V n) = (fun n =>
      (n * kB) * (Real.log (V / n) + 3 / 2 * Real.log (U / n) + s0)) := by
    funext n
    simp only [Sideal]
  have hbuilt : HasDerivAt (fun n =>
      (n * kB) * (Real.log (V / n) + 3 / 2 * Real.log (U / n) + s0))
      (kB * (Real.log (V / N) + 3 / 2 * Real.log (U / N) + s0) + (N * kB) *
        ((((0 * N - V * 1) / N ^ 2) / (V / N)) +
          (3 / 2) * (((0 * N - U * 1) / N ^ 2) / (U / N)) + 0)) N :=
    hf.mul hg
  have hval : (kB * (Real.log (V / N) + 3 / 2 * Real.log (U / N) + s0) +
      (N * kB) * ((((0 * N - V * 1) / N ^ 2) / (V / N)) +
        (3 / 2) * (((0 * N - U * 1) / N ^ 2) / (U / N)) + 0)) =
      kB * (Real.log (V / N) + 3 / 2 * Real.log (U / N) + s0 - 5 / 2) := by
    field_simp [hN0, hU0, hV0]
    ring
  rw [hfun]
  rw [hval] at hbuilt
  exact hbuilt

/-- The `∂S/∂N` slice partial of the ideal gas. -/
lemma sideal_dSdN (kB s0 : ℝ) (x : ThermoState 1) (i : Fin 1)
    (hU : 0 < x.1) (hV : 0 < x.2.1) (hN : 0 < x.2.2 0) :
    dSdN (SidealGen kB s0) x i =
      kB * (Real.log (x.2.1 / x.2.2 0) + 3 / 2 * Real.log (x.1 / x.2.2 0) +
        s0 - 5 / 2) := by
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  have hslice : (fun n => SidealGen kB s0
      (x.1, x.2.1, Function.update x.2.2 0 n)) =
      (fun n => Sideal kB s0 x.1 x.2.1 n) := by
    funext n
    change Sideal kB s0 x.1 x.2.1 ((Function.update x.2.2 0 n) 0) =
      Sideal kB s0 x.1 x.2.1 n
    rw [Function.update_self]
  change deriv (fun n => SidealGen kB s0
    (x.1, x.2.1, Function.update x.2.2 0 n)) (x.2.2 0) = _
  rw [hslice]
  exact (sideal_dSdN_hasDerivAt kB s0 x.1 x.2.1 (x.2.2 0) hU hV hN).deriv

/-- Ideal-gas temperature: `T = 2U / (3NkB)`. -/
lemma sideal_temp (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    temp (SidealGen kB s0) x = 2 * x.1 / (3 * x.2.2 0 * kB) := by
  have hN0 : x.2.2 0 ≠ 0 := ne_of_gt hN
  have hU0 : x.1 ≠ 0 := ne_of_gt hU
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  change 1 / dSdU (SidealGen kB s0) x = _
  rw [sideal_dSdU kB s0 x hU hN]
  field_simp [hN0, hU0, hkB0]

/-- Ideal-gas pressure: `p = 2U / (3V)`. -/
lemma sideal_press (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hV : 0 < x.2.1) (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    press (SidealGen kB s0) x = 2 * x.1 / (3 * x.2.1) := by
  have hN0 : x.2.2 0 ≠ 0 := ne_of_gt hN
  have hU0 : x.1 ≠ 0 := ne_of_gt hU
  have hV0 : x.2.1 ≠ 0 := ne_of_gt hV
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  change temp (SidealGen kB s0) x * dSdV (SidealGen kB s0) x = _
  rw [sideal_temp kB s0 x hU hN hkB, sideal_dSdV kB s0 x hV hN]
  field_simp [hN0, hU0, hV0, hkB0]

/-- Ideal-gas chemical potential. -/
lemma sideal_mu (kB s0 : ℝ) (x : ThermoState 1) (i : Fin 1)
    (hU : 0 < x.1) (hV : 0 < x.2.1) (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    chemPot (SidealGen kB s0) x i =
      -(2 * x.1 / (3 * x.2.2 0)) *
        (Real.log (x.2.1 / x.2.2 0) + 3 / 2 * Real.log (x.1 / x.2.2 0) +
          s0 - 5 / 2) := by
  have hN0 : x.2.2 0 ≠ 0 := ne_of_gt hN
  have hU0 : x.1 ≠ 0 := ne_of_gt hU
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  change -temp (SidealGen kB s0) x * dSdN (SidealGen kB s0) x i = _
  rw [sideal_temp kB s0 x hU hN hkB, sideal_dSdN kB s0 x i hU hV hN]
  field_simp [hN0, hU0, hkB0]

/-- Ideal-gas equation of state: `p * V = N * kB * T`. -/
lemma sideal_pV (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hV : 0 < x.2.1) (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    press (SidealGen kB s0) x * x.2.1 =
      x.2.2 0 * kB * temp (SidealGen kB s0) x := by
  have hN0 : x.2.2 0 ≠ 0 := ne_of_gt hN
  have hU0 : x.1 ≠ 0 := ne_of_gt hU
  have hV0 : x.2.1 ≠ 0 := ne_of_gt hV
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  rw [sideal_press kB s0 x hU hV hN hkB, sideal_temp kB s0 x hU hN hkB]
  field_simp [hN0, hU0, hV0, hkB0]

/-- Ideal-gas caloric equation of state: `U = (3/2) * N * kB * T`. -/
lemma sideal_U (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    x.1 = 3 / 2 * x.2.2 0 * kB * temp (SidealGen kB s0) x := by
  have hN0 : x.2.2 0 ≠ 0 := ne_of_gt hN
  have hU0 : x.1 ≠ 0 := ne_of_gt hU
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  rw [sideal_temp kB s0 x hU hN hkB]
  field_simp [hN0, hU0, hkB0]

/-- The ideal-gas entropy is positively homogeneous of degree 1 (all arguments,
since the ratios `V/N` and `U/N` are scale invariant). -/
lemma sideal_homog (kB s0 : ℝ) (x : ThermoState 1) (t : ℝ) (ht : 0 < t) :
    SidealGen kB s0 (t * x.1, t * x.2.1, t • x.2.2) =
      t * SidealGen kB s0 x := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  change Sideal kB s0 (t * x.1) (t * x.2.1) ((t • x.2.2) 0) =
    t * Sideal kB s0 x.1 x.2.1 (x.2.2 0)
  change Sideal kB s0 (t * x.1) (t * x.2.1) (t * x.2.2 0) =
    t * Sideal kB s0 x.1 x.2.1 (x.2.2 0)
  simp only [Sideal]
  rw [mul_div_mul_left _ _ ht0, mul_div_mul_left _ _ ht0]
  ring

/-- The ideal-gas `∂S/∂U` is positive on the domain. -/
lemma sideal_dSdU_pos (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hN : 0 < x.2.2 0) (hkB : 0 < kB) : 0 < dSdU (SidealGen kB s0) x := by
  rw [sideal_dSdU kB s0 x hU hN]
  exact div_pos (mul_pos (mul_pos (by norm_num) hN) hkB) (by linarith)

/-- The ideal-gas `U`-slice is differentiable. -/
lemma sideal_sliceU_diff (kB s0 U V N : ℝ) (hU : 0 < U) (hN : 0 < N) :
    DifferentiableAt ℝ (fun u => Sideal kB s0 u V N) U :=
  (sideal_dSdU_hasDerivAt kB s0 U V N hU hN).differentiableAt

/-- The ideal-gas `V`-slice is differentiable. -/
lemma sideal_sliceV_diff (kB s0 U V N : ℝ) (hV : 0 < V) (hN : 0 < N) :
    DifferentiableAt ℝ (fun v => Sideal kB s0 U v N) V :=
  (sideal_dSdV_hasDerivAt kB s0 U V N hV hN).differentiableAt

/-- The ideal-gas `N`-slice is differentiable. -/
lemma sideal_sliceN_diff (kB s0 U V N : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hN : 0 < N) : DifferentiableAt ℝ (fun n => Sideal kB s0 U V n) N :=
  (sideal_dSdN_hasDerivAt kB s0 U V N hU hV hN).differentiableAt

/-- The ideal-gas entropy is Fréchet differentiable on the single-species domain
(the differentiability postulate `h_diff`). -/
lemma sideal_differentiableOn (kB s0 : ℝ) :
    DifferentiableOn ℝ (SidealGen kB s0) (thermoDomain 1) := by
  intro x hx
  have hU : x.1 ≠ 0 := hx.1.ne'
  have hV : x.2.1 ≠ 0 := hx.2.1.ne'
  have hN : x.2.2 0 ≠ 0 := (hx.2.2 0).ne'
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold SidealGen Sideal
  fun_prop (disch := first | assumption | exact div_ne_zero hV hN |
    exact div_ne_zero hU hN)

/-- The ideal gas satisfies Gibbs-Duhem in derivative form along a curve,
proved directly from the explicit `T`, `p`, `μ` functions. The curve is
assumed positive near `t0` (the form in which domain membership is used). -/
lemma sideal_gibbsDuhem (kB s0 : ℝ) (γU γV : ℝ → ℝ) (γN : ℝ → Fin 1 → ℝ)
    (U' V' : ℝ) (N' : Fin 1 → ℝ) (t0 : ℝ) (hkB : 0 < kB)
    (hU : HasDerivAt γU U' t0) (hV : HasDerivAt γV V' t0)
    (hN : ∀ i, HasDerivAt (fun t => γN t i) (N' i) t0)
    (hUpos : 0 < γU t0) (hVpos : 0 < γV t0) (hNpos : 0 < γN t0 0)
    (hevU : ∀ᶠ t in 𝓝 t0, 0 < γU t) (hevV : ∀ᶠ t in 𝓝 t0, 0 < γV t)
    (hevN : ∀ᶠ t in 𝓝 t0, 0 < γN t 0) :
    SidealGen kB s0 (γU t0, γV t0, γN t0) *
        deriv (fun t => temp (SidealGen kB s0) (γU t, γV t, γN t)) t0 -
      γV t0 *
        deriv (fun t => press (SidealGen kB s0) (γU t, γV t, γN t)) t0 +
      ∑ i, γN t0 i *
        deriv (fun t => chemPot (SidealGen kB s0) (γU t, γV t, γN t) i)
          t0 = 0 := by
  have hkB0 : kB ≠ 0 := ne_of_gt hkB
  have hU0 : γU t0 ≠ 0 := ne_of_gt hUpos
  have hV0 : γV t0 ≠ 0 := ne_of_gt hVpos
  have hN0 : γN t0 0 ≠ 0 := ne_of_gt hNpos
  have hev := hevU.and (hevV.and hevN)
  have hTnum : HasDerivAt (fun t : ℝ => 2 * γU t) (2 * U') t0 :=
    hU.const_mul 2
  have hTden : HasDerivAt (fun t : ℝ => 3 * γN t 0 * kB) (3 * N' 0 * kB)
      t0 := by
    simpa using ((hN 0).const_mul 3).mul_const kB
  have hTden0 : 3 * γN t0 0 * kB ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) hNpos) hkB)
  have hTexpl : HasDerivAt (fun t : ℝ => 2 * γU t / (3 * γN t 0 * kB))
      ((2 * U' * (3 * γN t0 0 * kB) - 2 * γU t0 * (3 * N' 0 * kB)) /
        (3 * γN t0 0 * kB) ^ 2) t0 :=
    hTnum.div hTden hTden0
  have heqT : (fun t : ℝ => 2 * γU t / (3 * γN t 0 * kB)) =ᶠ[𝓝 t0]
      (fun t => temp (SidealGen kB s0) (γU t, γV t, γN t)) :=
    hev.mono fun t ht =>
      (sideal_temp kB s0 (γU t, γV t, γN t) ht.1 ht.2.2 hkB).symm
  have hT : HasDerivAt (fun t => temp (SidealGen kB s0) (γU t, γV t, γN t))
      ((2 * U' * (3 * γN t0 0 * kB) - 2 * γU t0 * (3 * N' 0 * kB)) /
        (3 * γN t0 0 * kB) ^ 2) t0 :=
    hTexpl.congr_of_eventuallyEq heqT.symm
  have hPnum : HasDerivAt (fun t : ℝ => 2 * γU t) (2 * U') t0 :=
    hU.const_mul 2
  have hPden : HasDerivAt (fun t : ℝ => 3 * γV t) (3 * V') t0 :=
    hV.const_mul 3
  have hPden0 : 3 * γV t0 ≠ 0 := ne_of_gt (by linarith)
  have hPexpl : HasDerivAt (fun t : ℝ => 2 * γU t / (3 * γV t))
      ((2 * U' * (3 * γV t0) - 2 * γU t0 * (3 * V')) /
        (3 * γV t0) ^ 2) t0 :=
    hPnum.div hPden hPden0
  have heqP : (fun t : ℝ => 2 * γU t / (3 * γV t)) =ᶠ[𝓝 t0]
      (fun t => press (SidealGen kB s0) (γU t, γV t, γN t)) :=
    hev.mono fun t ht =>
      (sideal_press kB s0 (γU t, γV t, γN t) ht.1 ht.2.1 ht.2.2 hkB).symm
  have hP : HasDerivAt (fun t => press (SidealGen kB s0) (γU t, γV t, γN t))
      ((2 * U' * (3 * γV t0) - 2 * γU t0 * (3 * V')) /
        (3 * γV t0) ^ 2) t0 :=
    hPexpl.congr_of_eventuallyEq heqP.symm
  have hMnum : HasDerivAt (fun t : ℝ => 2 * γU t) (2 * U') t0 :=
    hU.const_mul 2
  have hMden : HasDerivAt (fun t : ℝ => 3 * γN t 0) (3 * N' 0) t0 :=
    (hN 0).const_mul 3
  have hMden0 : 3 * γN t0 0 ≠ 0 := ne_of_gt (by linarith)
  have hMdiv : HasDerivAt (fun t : ℝ => 2 * γU t / (3 * γN t 0))
      ((2 * U' * (3 * γN t0 0) - 2 * γU t0 * (3 * N' 0)) /
        (3 * γN t0 0) ^ 2) t0 :=
    hMnum.div hMden hMden0
  have hA : HasDerivAt (fun t : ℝ => -(2 * γU t / (3 * γN t 0)))
      (-((2 * U' * (3 * γN t0 0) - 2 * γU t0 * (3 * N' 0)) /
        (3 * γN t0 0) ^ 2)) t0 :=
    hMdiv.neg
  have hVd2 : HasDerivAt (fun t : ℝ => γV t / γN t 0)
      ((V' * γN t0 0 - γV t0 * N' 0) / (γN t0 0) ^ 2) t0 :=
    hV.div (hN 0) hN0
  have hVlog : HasDerivAt (fun t : ℝ => Real.log (γV t / γN t 0))
      (((V' * γN t0 0 - γV t0 * N' 0) / (γN t0 0) ^ 2) /
        (γV t0 / γN t0 0)) t0 :=
    hVd2.log (div_ne_zero hV0 hN0)
  have hUd2 : HasDerivAt (fun t : ℝ => γU t / γN t 0)
      ((U' * γN t0 0 - γU t0 * N' 0) / (γN t0 0) ^ 2) t0 :=
    hU.div (hN 0) hN0
  have hUlog : HasDerivAt (fun t : ℝ => Real.log (γU t / γN t 0))
      (((U' * γN t0 0 - γU t0 * N' 0) / (γN t0 0) ^ 2) /
        (γU t0 / γN t0 0)) t0 :=
    hUd2.log (div_ne_zero hU0 hN0)
  have hB : HasDerivAt (fun t : ℝ => Real.log (γV t / γN t 0) +
      3 / 2 * Real.log (γU t / γN t 0) + s0 - 5 / 2)
      (((((V' * γN t0 0 - γV t0 * N' 0) / (γN t0 0) ^ 2) /
          (γV t0 / γN t0 0)) +
        (3 / 2) * (((U' * γN t0 0 - γU t0 * N' 0) / (γN t0 0) ^ 2) /
          (γU t0 / γN t0 0)) + 0) - 0) t0 :=
    ((hVlog.add (hUlog.const_mul (3 / 2))).add
      (hasDerivAt_const t0 s0)).sub (hasDerivAt_const t0 (5 / 2))
  have hMexpl : HasDerivAt (fun t : ℝ => (-(2 * γU t / (3 * γN t 0))) *
      (Real.log (γV t / γN t 0) + 3 / 2 * Real.log (γU t / γN t 0) +
        s0 - 5 / 2))
      ((-((2 * U' * (3 * γN t0 0) - 2 * γU t0 * (3 * N' 0)) /
          (3 * γN t0 0) ^ 2)) *
        (Real.log (γV t0 / γN t0 0) + 3 / 2 * Real.log (γU t0 / γN t0 0) +
          s0 - 5 / 2) +
        (-(2 * γU t0 / (3 * γN t0 0))) *
          (((((V' * γN t0 0 - γV t0 * N' 0) / (γN t0 0) ^ 2) /
              (γV t0 / γN t0 0)) +
            (3 / 2) * (((U' * γN t0 0 - γU t0 * N' 0) /
              (γN t0 0) ^ 2) / (γU t0 / γN t0 0)) + 0) - 0)) t0 :=
    hA.mul hB
  have heqM : (fun t : ℝ => (-(2 * γU t / (3 * γN t 0))) *
      (Real.log (γV t / γN t 0) + 3 / 2 * Real.log (γU t / γN t 0) +
        s0 - 5 / 2)) =ᶠ[𝓝 t0]
      (fun t => chemPot (SidealGen kB s0) (γU t, γV t, γN t) 0) :=
    hev.mono fun t ht =>
      (sideal_mu kB s0 (γU t, γV t, γN t) 0 ht.1 ht.2.1 ht.2.2 hkB).symm
  have hM : HasDerivAt
      (fun t => chemPot (SidealGen kB s0) (γU t, γV t, γN t) 0)
      ((-((2 * U' * (3 * γN t0 0) - 2 * γU t0 * (3 * N' 0)) /
          (3 * γN t0 0) ^ 2)) *
        (Real.log (γV t0 / γN t0 0) + 3 / 2 * Real.log (γU t0 / γN t0 0) +
          s0 - 5 / 2) +
        (-(2 * γU t0 / (3 * γN t0 0))) *
          (((((V' * γN t0 0 - γV t0 * N' 0) / (γN t0 0) ^ 2) /
              (γV t0 / γN t0 0)) +
            (3 / 2) * (((U' * γN t0 0 - γU t0 * N' 0) /
              (γN t0 0) ^ 2) / (γU t0 / γN t0 0)) + 0) - 0)) t0 :=
    hMexpl.congr_of_eventuallyEq heqM.symm
  rw [Fin.sum_univ_one, hT.deriv, hP.deriv, hM.deriv]
  simp only [SidealGen, Sideal]
  field_simp [hU0, hV0, hN0, hkB0]
  ring

/-- Total-entropy rate for two ideal-gas subsystems exchanging energy at fixed
total: the difference of the two `∂S/∂U` values. -/
lemma sideal_stot_hasDerivAt (kB s0 V1 V2 N1 N2 Utot Ustar : ℝ)
    (hU1 : 0 < Ustar) (hU2 : 0 < Utot - Ustar) (hN1 : 0 < N1)
    (hN2 : 0 < N2) :
    HasDerivAt
      (fun U1 => Sideal kB s0 U1 V1 N1 + Sideal kB s0 (Utot - U1) V2 N2)
      (3 * N1 * kB / (2 * Ustar) +
        (3 * N2 * kB / (2 * (Utot - Ustar))) * -1) Ustar := by
  have h1 : HasDerivAt (fun U1 => Sideal kB s0 U1 V1 N1)
      (3 * N1 * kB / (2 * Ustar)) Ustar :=
    sideal_dSdU_hasDerivAt kB s0 Ustar V1 N1 hU1 hN1
  have hg : HasDerivAt (fun u => Sideal kB s0 u V2 N2)
      (3 * N2 * kB / (2 * (Utot - Ustar))) (Utot - Ustar) :=
    sideal_dSdU_hasDerivAt kB s0 (Utot - Ustar) V2 N2 hU2 hN2
  have hh : HasDerivAt (fun U1 : ℝ => Utot - U1) (-1) Ustar := by
    exact HasDerivAt.const_sub Utot (hasDerivAt_id' Ustar)
  have h2 : HasDerivAt (fun U1 => Sideal kB s0 (Utot - U1) V2 N2)
      ((3 * N2 * kB / (2 * (Utot - Ustar))) * -1) Ustar :=
    hg.comp (h := fun U1 : ℝ => Utot - U1) (x := Ustar) hh
  exact h1.add h2

/-- The perspective of `Real.log`: `(V, N) ↦ N * log (V / N)` is concave on
`V > 0`, `N > 0`, by two-point Jensen for `log`. -/
lemma concave_perspLog : ConcaveOn ℝ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}
    (fun p => p.2 * Real.log (p.1 / p.2)) := by
  have hconv : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
    have h : {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} = Set.Ioi 0 ×ˢ Set.Ioi 0 := by
      ext p
      cases p with
      | mk a b => simp
    rw [h]
    exact (convex_Ioi 0).prod (convex_Ioi 0)
  refine ⟨hconv, fun x hx y hy a b ha hb hab => ?_⟩
  cases x with
  | mk V1 N1 =>
    cases y with
    | mk V2 N2 =>
      change 0 < V1 ∧ 0 < N1 at hx
      change 0 < V2 ∧ 0 < N2 at hy
      have hN10 : N1 ≠ 0 := ne_of_gt hx.2
      have hN20 : N2 ≠ 0 := ne_of_gt hy.2
      have hM : 0 < a * N1 + b * N2 := by
        by_cases ha0 : a = 0
        · subst ha0
          have hb1 : b = 1 := by linarith
          rw [hb1]
          simpa using hy.2
        · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have h1 : 0 < a * N1 := mul_pos ha' hx.2
          have h2 : 0 ≤ b * N2 := mul_nonneg hb (le_of_lt hy.2)
          linarith
      set M := a * N1 + b * N2 with hMdef
      have hM0 : M ≠ 0 := ne_of_gt hM
      have hlog := strictConcaveOn_log_Ioi.concaveOn
      have hJ := hlog.2 (show V1 / N1 ∈ Set.Ioi 0 from div_pos hx.1 hx.2)
        (show V2 / N2 ∈ Set.Ioi 0 from div_pos hy.1 hy.2)
        (show (0 : ℝ) ≤ a * N1 / M from
          div_nonneg (mul_nonneg ha (le_of_lt hx.2)) (le_of_lt hM))
        (show (0 : ℝ) ≤ b * N2 / M from
          div_nonneg (mul_nonneg hb (le_of_lt hy.2)) (le_of_lt hM))
        (show a * N1 / M + b * N2 / M = 1 from by
          rw [← add_div, ← hMdef]
          exact div_self hM0)
      simp only [smul_eq_mul] at hJ
      have hmid : (a * N1 / M) * (V1 / N1) + (b * N2 / M) * (V2 / N2) =
          (a * V1 + b * V2) / M := by
        field_simp [hM0, hN10, hN20]
      rw [hmid] at hJ
      have hscale : M * ((a * N1 / M) * Real.log (V1 / N1) +
          (b * N2 / M) * Real.log (V2 / N2)) ≤
          M * Real.log ((a * V1 + b * V2) / M) :=
        mul_le_mul_of_nonneg_left hJ (le_of_lt hM)
      have hLHS : M * ((a * N1 / M) * Real.log (V1 / N1) +
          (b * N2 / M) * Real.log (V2 / N2)) =
          a * (N1 * Real.log (V1 / N1)) + b * (N2 * Real.log (V2 / N2)) := by
        field_simp [hM0]
      have hRHS : M * Real.log ((a * V1 + b * V2) / M) =
          (fun p : ℝ × ℝ => p.2 * Real.log (p.1 / p.2))
            (a • (V1, N1) + b • (V2, N2)) := by
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        rw [← hMdef]
      have hgoal : a • (N1 * Real.log (V1 / N1)) +
          b • (N2 * Real.log (V2 / N2)) ≤
          (fun p : ℝ × ℝ => p.2 * Real.log (p.1 / p.2))
            (a • (V1, N1) + b • (V2, N2)) := by
        calc a • (N1 * Real.log (V1 / N1)) + b • (N2 * Real.log (V2 / N2))
            = a * (N1 * Real.log (V1 / N1)) +
              b * (N2 * Real.log (V2 / N2)) := by
              rw [smul_eq_mul, smul_eq_mul]
          _ = M * ((a * N1 / M) * Real.log (V1 / N1) +
              (b * N2 / M) * Real.log (V2 / N2)) := hLHS.symm
          _ ≤ M * Real.log ((a * V1 + b * V2) / M) := hscale
          _ = (fun p : ℝ × ℝ => p.2 * Real.log (p.1 / p.2))
              (a • (V1, N1) + b • (V2, N2)) := hRHS.symm
      exact hgoal

/-- Positive orthant in `(U, V, N)` space for the single-species ideal gas. -/
def sidealDomain : Set (ℝ × ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2}

/-- The ideal-gas domain is convex. -/
lemma convex_sidealDomain : Convex ℝ sidealDomain := by
  have h : sidealDomain = Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
    ext p
    cases p with
    | mk a p2 =>
      cases p2 with
      | mk b c => simp [sidealDomain]
  rw [h]
  exact (convex_Ioi 0).prod ((convex_Ioi 0).prod (convex_Ioi 0))

/-- Linear projection `(U, V, N) ↦ (V, N)`. -/
private def sidealProjVN : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
    (((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))))

/-- Linear projection `(U, V, N) ↦ (U, N)`. -/
private def sidealProjUN : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))))

/-- The ideal-gas entropy is concave on the positive orthant (for `0 ≤ kB`):
perspective-of-`log` in `(V, N)` and `(U, N)` plus a linear term, scaled
by `kB`. -/
lemma sideal_concave (kB s0 : ℝ) (hkB : 0 ≤ kB) :
    ConcaveOn ℝ sidealDomain
      (fun x : ℝ × ℝ × ℝ => Sideal kB s0 x.1 x.2.1 x.2.2) := by
  have h1 : ConcaveOn ℝ sidealDomain
      (fun x : ℝ × ℝ × ℝ => x.2.2 * Real.log (x.2.1 / x.2.2)) := by
    have hsub : sidealDomain ⊆
        sidealProjVN ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
      intro x hx
      change 0 < (sidealProjVN x).1 ∧ 0 < (sidealProjVN x).2
      exact ⟨hx.2.1, hx.2.2⟩
    exact (concave_perspLog.comp_linearMap sidealProjVN).subset hsub
      convex_sidealDomain
  have h2 : ConcaveOn ℝ sidealDomain
      (fun x : ℝ × ℝ × ℝ => x.2.2 * Real.log (x.1 / x.2.2)) := by
    have hsub : sidealDomain ⊆
        sidealProjUN ⁻¹' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} := by
      intro x hx
      change 0 < (sidealProjUN x).1 ∧ 0 < (sidealProjUN x).2
      exact ⟨hx.1, hx.2.2⟩
    exact (concave_perspLog.comp_linearMap sidealProjUN).subset hsub
      convex_sidealDomain
  have h2s : ConcaveOn ℝ sidealDomain
      (fun x : ℝ × ℝ × ℝ => (3 / 2) * (x.2.2 * Real.log (x.1 / x.2.2))) :=
    h2.smul (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have h12 : ConcaveOn ℝ sidealDomain (fun x : ℝ × ℝ × ℝ =>
      x.2.2 * Real.log (x.2.1 / x.2.2) +
        (3 / 2) * (x.2.2 * Real.log (x.1 / x.2.2))) :=
    h1.add h2s
  have hlin : ConcaveOn ℝ sidealDomain
      (fun x : ℝ × ℝ × ℝ => s0 * x.2.2) := by
    refine ⟨convex_sidealDomain, fun x _ y _ a b _ _ _ => ?_⟩
    have heq : (a • x + b • y).2.2 = a * x.2.2 + b * y.2.2 := by
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    change a • (s0 * x.2.2) + b • (s0 * y.2.2) ≤ s0 * (a • x + b • y).2.2
    rw [heq, smul_eq_mul, smul_eq_mul]
    exact le_of_eq (by ring)
  have h12l : ConcaveOn ℝ sidealDomain (fun x : ℝ × ℝ × ℝ =>
      (x.2.2 * Real.log (x.2.1 / x.2.2) +
        (3 / 2) * (x.2.2 * Real.log (x.1 / x.2.2))) + s0 * x.2.2) :=
    h12.add hlin
  have hS : ConcaveOn ℝ sidealDomain (fun x : ℝ × ℝ × ℝ => kB *
      ((x.2.2 * Real.log (x.2.1 / x.2.2) +
        (3 / 2) * (x.2.2 * Real.log (x.1 / x.2.2))) + s0 * x.2.2)) :=
    h12l.smul hkB
  have hfun : (fun x : ℝ × ℝ × ℝ => kB *
      ((x.2.2 * Real.log (x.2.1 / x.2.2) +
        (3 / 2) * (x.2.2 * Real.log (x.1 / x.2.2))) + s0 * x.2.2)) =
      (fun x : ℝ × ℝ × ℝ => Sideal kB s0 x.1 x.2.1 x.2.2) := by
    funext x
    simp only [Sideal]
    ring
  rw [← hfun]
  exact hS

/-- The physical single-species domain is convex. -/
lemma convex_thermoDomainOne : Convex ℝ (thermoDomain 1) := by
  have h : thermoDomain 1 =
      Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.pi Set.univ (fun _ => Set.Ioi 0)) := by
    ext x
    cases x with
    | mk U x2 =>
      cases x2 with
      | mk V N => simp [thermoDomain, Set.mem_pi]
  rw [h]
  exact (convex_Ioi 0).prod ((convex_Ioi 0).prod
    (convex_pi fun i _ => convex_Ioi 0))

/-- Linear embedding of single-species states into `(U, V, N)` space. -/
private def sidealEmbed : ThermoState 1 →ₗ[ℝ] (ℝ × ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ (ℝ × (Fin 1 → ℝ))).prod
    ((((LinearMap.fst ℝ ℝ (Fin 1 → ℝ)).comp
      (LinearMap.snd ℝ ℝ (ℝ × (Fin 1 → ℝ))))).prod
      ((((LinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →ₗ[ℝ] ℝ).comp
        (LinearMap.snd ℝ ℝ (Fin 1 → ℝ))).comp
        (LinearMap.snd ℝ ℝ (ℝ × (Fin 1 → ℝ))))))

/-- The ideal-gas entropy satisfies the concavity postulate on single-species
states. -/
lemma sideal_concave_gen (kB s0 : ℝ) (hkB : 0 ≤ kB) :
    ConcaveOn ℝ (thermoDomain 1) (SidealGen kB s0) := by
  have hsub : thermoDomain 1 ⊆ sidealEmbed ⁻¹' sidealDomain := by
    intro x hx
    change 0 < (sidealEmbed x).1 ∧ 0 < (sidealEmbed x).2.1 ∧
      0 < (sidealEmbed x).2.2
    exact ⟨hx.1, hx.2.1, hx.2.2 0⟩
  exact ((sideal_concave kB s0 hkB).comp_linearMap sidealEmbed).subset hsub
    convex_thermoDomainOne

/-- The monatomic ideal gas as a `FundamentalRelation 1` (for `kB > 0`): every
postulate is proved for `SidealGen kB s0`, so the results of sections A to D apply
to it. -/
noncomputable def idealGas (kB s0 : ℝ) (hkB : 0 < kB) : FundamentalRelation 1 where
  S := SidealGen kB s0
  h_diff := sideal_differentiableOn kB s0
  h_concave := sideal_concave_gen kB s0 hkB.le
  h_homog := fun x _ t ht => sideal_homog kB s0 x t ht
  h_pos := fun x hx => sideal_dSdU_pos kB s0 x hx.1 (hx.2.2 0) hkB

/-- The ideal gas satisfies the Euler relation `U = TS - pV + μN`: `euler_relation` for
`idealGas`, stated with componentwise positivity. -/
lemma sideal_euler (kB s0 : ℝ) (x : ThermoState 1) (hU : 0 < x.1)
    (hV : 0 < x.2.1) (hN : 0 < x.2.2 0) (hkB : 0 < kB) :
    x.1 = temp (SidealGen kB s0) x * SidealGen kB s0 x -
      press (SidealGen kB s0) x * x.2.1 +
      ∑ i, chemPot (SidealGen kB s0) x i * x.2.2 i :=
  euler_relation (idealGas kB s0 hkB) x ⟨hU, hV, fun i => by rwa [Fin.fin_one_eq_zero i]⟩

/-- Boundary countermodel, postulate failure: at `N = 0` the ideal-gas `∂S/∂U`
slice is identically zero, so `SidealGen` violates `∂S/∂U > 0` there and
`idealGas` needs the open domain `N > 0`. -/
lemma sideal_dSdU_at_N_zero (kB s0 U V : ℝ) :
    dSdU (SidealGen kB s0) (U, V, fun _ => 0) = 0 := by
  have hslice : (fun u => Sideal kB s0 u V 0) = fun _ => 0 := by
    funext u
    simp [Sideal]
  change deriv (fun u => SidealGen kB s0 (u, V, fun _ => 0)) U = 0
  have heq : (fun u => SidealGen kB s0 (u, V, fun _ => 0)) =
      (fun u => Sideal kB s0 u V 0) := rfl
  rw [heq, hslice]
  exact (hasDerivAt_const U 0).deriv

/-- Boundary countermodel, equation-of-state failure: at `(U, V, N) = (1, 1, 0)` with
`kB = 1`, every hypothesis of `sideal_U` except `0 < N` holds, and its conclusion
`U = (3/2) * N * kB * T` fails, so `0 < N` cannot be dropped from `sideal_U`. -/
lemma sideal_EOS_fails_at_N_zero (s0 : ℝ) :
    ¬ (1 : ℝ) =
      3 / 2 * (0 : ℝ) * 1 * temp (SidealGen 1 s0) (1, 1, fun _ => 0) := by
  have hT : temp (SidealGen 1 s0) (1, 1, fun _ => 0) = 0 := by
    change 1 / dSdU (SidealGen 1 s0) (1, 1, fun _ => 0) = 0
    rw [sideal_dSdU_at_N_zero]
    exact div_zero 1
  intro h
  rw [hT] at h
  norm_num at h

end Chemistry.Thermodynamics
