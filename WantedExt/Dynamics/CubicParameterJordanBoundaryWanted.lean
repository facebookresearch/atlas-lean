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
public import Mathlib.Data.Complex.Basic
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

/-- **Cubic family.** For a parameter $\lambda \in \mathbb{C}$, the cubic polynomial map
$f_\lambda : \mathbb{C} \to \mathbb{C}$ is given by $f_\lambda(z) = \lambda z^2 + z^3$.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def cubicFamily (lam z : ℂ) : ℂ := lam * z ^ 2 + z ^ 3

/-- **Critical points of the cubic family.** For $\lambda \in \mathbb{C}$, a point
$c \in \mathbb{C}$ is a critical point of $f_\lambda(z) = \lambda z^2 + z^3$ when $f_\lambda$ has
complex derivative $0$ at $c$, that is, $f_\lambda'(c) = 0$.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def IsCriticalPoint (lam c : ℂ) : Prop := HasDerivAt (cubicFamily lam) 0 c

/-- **Basin of attraction of zero.** For $\lambda \in \mathbb{C}$, the basin of zero of
$f_\lambda(z) = \lambda z^2 + z^3$ is the set of $z \in \mathbb{C}$ whose forward orbit tends to
$0$, that is, $f_\lambda^{n}(z) \to 0$ as $n \to \infty$, where $f_\lambda^{n}$ denotes the
$n$-th iterate of $f_\lambda$.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def basinOfZero (lam : ℂ) : Set ℂ :=
  {z | Filter.Tendsto (fun n : ℕ => (cubicFamily lam)^[n] z) Filter.atTop (nhds (0 : ℂ))}

/-- **Immediate basin of zero.** For $\lambda \in \mathbb{C}$, a set $V \subseteq \mathbb{C}$ is
the immediate basin of zero of $f_\lambda(z) = \lambda z^2 + z^3$ when $0 \in V$, $V$ is contained
in the basin of zero of $f_\lambda$ (the set of $z$ with $f_\lambda^{n}(z) \to 0$), $V$ is
connected, and every connected set $W \subseteq \mathbb{C}$ with $0 \in W$ that is contained in the
basin of zero of $f_\lambda$ satisfies $W \subseteq V$. Thus $V$ is the connected component of $0$
in the basin of zero.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def IsImmediateBasin (lam : ℂ) (V : Set ℂ) : Prop :=
  (0 : ℂ) ∈ V ∧ V ⊆ basinOfZero lam ∧ IsConnected V ∧
    ∀ W : Set ℂ, (0 : ℂ) ∈ W → W ⊆ basinOfZero lam → IsConnected W → W ⊆ V

/-- **Parameters with both critical points in the immediate basin.** The parameter set is the set
of $\lambda \in \mathbb{C}$ for which some immediate basin of zero $V$ of
$f_\lambda(z) = \lambda z^2 + z^3$ contains every critical point of $f_\lambda$.

Since $f_\lambda'(z) = z(3z + 2\lambda)$, the critical points of $f_\lambda$ are $0$ and
$-2\lambda/3$ (equal when $\lambda = 0$), so this asks that both finite critical points lie in
the immediate basin of zero.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def parameterSet : Set ℂ :=
  {lam | ∃ V : Set ℂ, IsImmediateBasin lam V ∧ ∀ c : ℂ, IsCriticalPoint lam c → c ∈ V}

/-- **Parameter components.** A set $U \subseteq \mathbb{C}$ is a parameter component when it is
a connected component of the parameter set, the set of $\lambda \in \mathbb{C}$ for which every
critical point of $f_\lambda(z) = \lambda z^2 + z^3$ lies in the immediate basin of zero of
$f_\lambda$: $U$ is nonempty, contained in the parameter set and connected, and every connected
set $W \subseteq \mathbb{C}$ with $U \subseteq W$ that is contained in the parameter set equals
$U$.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def IsParameterComponent (U : Set ℂ) : Prop :=
  U.Nonempty ∧ U ⊆ parameterSet ∧ IsConnected U ∧
    ∀ W : Set ℂ, U ⊆ W → W ⊆ parameterSet → IsConnected W → W = U

/-- **Jordan curves in the plane.** A set $S \subseteq \mathbb{C}$ is a Jordan curve when there is
a continuous injective map $f$ from the unit circle $\{z \in \mathbb{C} : |z| = 1\}$ to
$\mathbb{C}$ whose image is exactly $S$.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def IsJordanCurve (S : Set ℂ) : Prop :=
  ∃ f : ↥(Metric.sphere (0 : ℂ) 1) → ℂ, Continuous f ∧ Function.Injective f ∧ Set.range f = S

/-- **McMullen's question on Jordan boundaries of cubic parameter components.** Let
$f_\lambda(z) = \lambda z^2 + z^3$ for $\lambda \in \mathbb{C}$. The statement is that for every
parameter component $U$, that is, every connected component of the set of $\lambda$ for which
every critical point of $f_\lambda$ lies in the immediate basin of zero of $f_\lambda$, the
boundary $\partial U$ of $U$ in $\mathbb{C}$ is a Jordan curve.

The source poses this as an open question.

Source: [AMR-052-0019], Stony Brook open problems (1992), McMullen III.2. -/
def conjecture : Prop :=
  ∀ U : Set ℂ, IsParameterComponent U → IsJordanCurve (frontier U)

/-- **Roesch's theorem on the boundaries of cubic parameter components.** For the cubic family
$f_\lambda(z) = \lambda z^2 + z^3$ with $\lambda \in \mathbb{C}$, the boundary of every parameter
component is a Jordan curve. Here a parameter component is a connected component of the set of
$\lambda$ for which every critical point of $f_\lambda$ lies in the immediate basin of zero of
$f_\lambda$.

Roesch (Theorem 2) proves that the boundary of every component of
$H = \{a : -a \text{ lies in the basin of } 0\}$ for the family $z^{d-1}(z + da/(d-1))$ is a
Jordan curve; at $d = 3$ the linear change $\lambda = 3a/2$ carries the central component $H_0$
onto the parameter component.

Source:
Pascale Roesch, Hyperbolic components of polynomials with a fixed critical point of maximal
order, Ann. Sci. Ecole Norm. Sup. (4) 40 (2007), arXiv:math/0612172,
https://arxiv.org/abs/math/0612172. Moved from
`OpenConjectures/Dynamics/CubicParameterJordanBoundary`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Dynamics.CubicParameterJordanBoundaryWanted
