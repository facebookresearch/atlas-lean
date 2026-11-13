/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jordan boundary of a cubic parameter component

`AMR-052-0019` (Stony Brook (1992), McMullen III.2): for
`f_λ(z) = λ z^2 + z^3`, `∂U` is a Jordan curve, where `U` is the
parameter component with both finite critical points in the immediate
basin of zero.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

namespace MathlibExt.Dynamics.CubicParameterJordanBoundaryWanted

/-! Source: UnsolvedMath record `AMR-052-0019`, numeric id 5300019
(Stony Brook Open Problems in Dynamical Systems, 1992, McMullen III.2).
Source URL: https://www.math.stonybrook.edu/open-problems-dynamical-systems
Status: the source dataset labels it unsolved; since resolved (see the entry metadata). -/

/-- Cubic family f_λ(z) = λ z ^ 2 + z ^ 3. Cites [AMR-052-0019]. -/
def cubicFamily (lam z : ℂ) : ℂ := lam * z ^ 2 + z ^ 3

/-- Finite critical point of f_λ: vanishing complex derivative at c.
Cites [AMR-052-0019]. -/
def IsCriticalPoint (lam c : ℂ) : Prop := HasDerivAt (cubicFamily lam) 0 c

/-- Basin of zero: points whose forward iterates under f_λ tend to 0.
Cites [AMR-052-0019]. -/
def basinOfZero (lam : ℂ) : Set ℂ :=
  {z | Filter.Tendsto (fun n : ℕ => (cubicFamily lam)^[n] z) Filter.atTop (nhds (0 : ℂ))}

/-- Immediate basin of zero: set containing 0, contained in the basin,
connected, and maximal with these properties. Cites [AMR-052-0019]. -/
def IsImmediateBasin (lam : ℂ) (V : Set ℂ) : Prop :=
  (0 : ℂ) ∈ V ∧ V ⊆ basinOfZero lam ∧ IsConnected V ∧
    ∀ W : Set ℂ, (0 : ℂ) ∈ W → W ⊆ basinOfZero lam → IsConnected W → W ⊆ V

/-- Parameter set where both finite critical points lie in one immediate
basin of zero. Cites [AMR-052-0019]. -/
def parameterSet : Set ℂ :=
  {lam | ∃ V : Set ℂ, IsImmediateBasin lam V ∧ ∀ c : ℂ, IsCriticalPoint lam c → c ∈ V}

/-- Parameter component: nonempty maximal connected subset of the parameter
set. Cites [AMR-052-0019]. -/
def IsParameterComponent (U : Set ℂ) : Prop :=
  U.Nonempty ∧ U ⊆ parameterSet ∧ IsConnected U ∧
    ∀ W : Set ℂ, U ⊆ W → W ⊆ parameterSet → IsConnected W → W = U

/-- Jordan curve in ℂ: continuous injective image of the unit circle.
Cites [AMR-052-0019]. -/
def IsJordanCurve (S : Set ℂ) : Prop :=
  ∃ f : ↥(Metric.sphere (0 : ℂ) 1) → ℂ, Continuous f ∧ Function.Injective f ∧ Set.range f = S

/-- Question (open in the source): the boundary of every such parameter component is a
Jordan curve. Cites [AMR-052-0019]. -/
def conjecture : Prop :=
  ∀ U : Set ℂ, IsParameterComponent U → IsJordanCurve (frontier U)

/--
Resolved true: Roesch (Ann. Sci. ENS 2007, arXiv:math/0612172, Theorem 2) proves the boundary of
every component of H = {a : -a in the basin of 0} for z^{d-1}(z + da/(d-1)) is a Jordan curve;
at d = 3 the linear change lambda = 3a/2 carries the central component H0 onto U. Source:
Pascale Roesch, Hyperbolic components of polynomials with a fixed critical point of maximal
order, Ann. Sci. Ecole Norm. Sup. (4) 40 (2007), arXiv:math/0612172,
https://arxiv.org/abs/math/0612172. Moved from
`OpenConjectures/Dynamics/CubicParameterJordanBoundary`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Dynamics.CubicParameterJordanBoundaryWanted
