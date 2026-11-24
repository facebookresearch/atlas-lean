/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multistability of positive feedback loops of monotone input/output systems

A positivity cone `K ⊆ ℝ^n` is a closed convex pointed cone with nonempty interior; it orders
`ℝ^n` by `x₁ ⪰ x₂ ↔ x₁ - x₂ ∈ K`, with `x₁ ≻ x₂` meaning `x₁ ⪰ x₂` and `x₁ ≠ x₂`, and
`x₁ ≫ x₂ ↔ x₁ - x₂ ∈ int K`. A single-input single-output system `ẋ = f(x, u)`, `y = h(x)` has a
state space `X ⊆ ℝ^n` that is the closure of an open set, an input set `U ⊆ ℝ` and an output map
`h : X → ℝ`, with the standard order on inputs and outputs. Inputs are locally essentially
bounded measurable functions `u : [0, ∞) → U`; `f` is differentiable, and the solution
`φ(t, ξ, u)` from `ξ ∈ X` exists for all `t ≥ 0` and stays in `X` (forward completeness and
invariance). The system is monotone if `ξ₁ ⪰ ξ₂` and `u₁ ≥ u₂` almost everywhere imply
`φ(t, ξ₁, u₁) ⪰ φ(t, ξ₂, u₂)` for all `t ≥ 0`, and `h` is monotone. It has a non-degenerate
input-to-state characteristic `k_X : U → X` if for each constant input `u`, `k_X(u)` is the
unique globally asymptotically stable equilibrium of `ẋ = f(x, u)` on `X` and
`det D_x f(k_X(u), u) ≠ 0`; its input/output characteristic is `k_Y = h ∘ k_X`. A map
`k : U → U` has non-degenerate fixed points if at every fixed point `k'(u)` exists and `k'(u) ≠ 1`.

**Theorem (secondresult)** (Angeli–Sontag 2004). Consider a monotone single-input single-output
system with a non-degenerate I/S and I/O static characteristic, and close the loop with the
unitary positive feedback `u = y`. Then the equilibria of the closed loop `ẋ = f(x, h(x))` are
in one-to-one correspondence with the fixed points of `k_Y`. Moreover, if `k_Y` has
non-degenerate fixed points, the closed-loop system is strongly monotone, and all its
trajectories are bounded, then for almost all initial conditions the solutions converge to the
set of equilibria corresponding to inputs `u` with `k_Y'(u) < 1`.

Encoding. Solutions are taken in integral (Carathéodory) form, and the open-loop and closed-loop
solution maps are given as data with their defining properties (existence, invariance of `X`
and uniqueness), as the source assumes. Global asymptotic stability within `X` is Lyapunov
stability together with attraction of every solution from `X`. The correspondence of equilibria
is `u ↦ k_X(u)`; the closed loop requires `h(X) ⊆ U`. "Almost all initial conditions" is
Lebesgue-almost every point of `X`, and convergence to a set is convergence of the distance to
it. Strong monotonicity of the closed loop is a hypothesis of the second part, as in the source.
This is the theorem used by Angeli, Ferrell and Sontag (PNAS 2004) for bistable positive
feedback loops.

Sources: D. Angeli, E. D. Sontag, "Multi-stability in monotone input/output systems", Systems
Control Lett. 51 (2004) 185–202, Sections 2–3, Definitions of monotone systems and static
characteristics, Theorem 2 (arXiv:q-bio/0309002); D. Angeli, J. E. Ferrell Jr., E. D. Sontag,
"Detection of multistability, bifurcations, and hysteresis in a large class of biological
positive-feedback systems", Proc. Natl. Acad. Sci. USA 101 (2004) 1822–1827.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Biophysics.MonotoneFeedbackMultistabilityWanted

open MeasureTheory Filter Topology

variable {n : ℕ}

/-- A positivity cone in `ℝ^n`: a nonempty closed convex cone (closed under nonnegative scaling),
pointed (`K ∩ -K = {0}`), with nonempty interior. -/
structure IsPositivityCone (K : Set (Fin n → ℝ)) : Prop where
  nonempty : K.Nonempty
  closed : IsClosed K
  convex : Convex ℝ K
  smul_mem : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ K, c • x ∈ K
  pointed : ∀ x, x ∈ K → -x ∈ K → x = 0
  interior_nonempty : (interior K).Nonempty

/-- An input: a measurable function `u : ℝ → ℝ`, bounded on every bounded interval of times, with
values in `U` on `[0, ∞)`. -/
def IsInput (U : Set ℝ) (u : ℝ → ℝ) : Prop :=
  Measurable u ∧ (∀ T, ∃ M, ∀ t ∈ Set.Icc 0 T, |u t| ≤ M) ∧ ∀ t, 0 ≤ t → u t ∈ U

/-- `x` is a solution of `ẋ = g(x, t)` on `[0, ∞)` from `ξ`, in integral form:
`x t = ξ + ∫₀ᵗ g (x s) s ds` for all `t ≥ 0`, with `x` continuous. -/
def IsSolution (g : (Fin n → ℝ) → ℝ → Fin n → ℝ) (ξ : Fin n → ℝ) (x : ℝ → Fin n → ℝ) : Prop :=
  Continuous x ∧ ∀ t, 0 ≤ t → x t = ξ + ∫ s in (0 : ℝ)..t, g (x s) s

/-- The jacobian `D_x f(x, u)` of `f` with respect to the state. -/
noncomputable def stateJacobian (f : (Fin n → ℝ) → ℝ → Fin n → ℝ) (x : Fin n → ℝ) (u : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun z => f z u) x (Pi.single j 1) i

/-- A single-input single-output system `ẋ = f(x, u)`, `y = h(x)` with state space `X`, input set
`U`, positivity cone `K` on states and solution map `φ t ξ u`, satisfying the source's standing
assumptions: `X` is the closure of an open set, `f` is differentiable, and for every `ξ ∈ X` and
every input `u` the solution `t ↦ φ t ξ u` exists on `[0, ∞)`, stays in `X`, and is the unique
solution with these properties. -/
structure IOSystem (n : ℕ) where
  /-- The positivity cone ordering the states. -/
  K : Set (Fin n → ℝ)
  /-- The state space. -/
  X : Set (Fin n → ℝ)
  /-- The input set. -/
  U : Set ℝ
  /-- The vector field. -/
  f : (Fin n → ℝ) → ℝ → Fin n → ℝ
  /-- The output map. -/
  h : (Fin n → ℝ) → ℝ
  /-- The solution map `φ t ξ u`. -/
  φ : ℝ → (Fin n → ℝ) → (ℝ → ℝ) → Fin n → ℝ
  cone : IsPositivityCone K
  closure_interior : closure (interior X) = X
  differentiable : Differentiable ℝ fun p : (Fin n → ℝ) × ℝ => f p.1 p.2
  solution : ∀ ξ ∈ X, ∀ u, IsInput U u →
    IsSolution (fun x t => f x (u t)) ξ (fun t => φ t ξ u) ∧ ∀ t, 0 ≤ t → φ t ξ u ∈ X
  unique : ∀ ξ ∈ X, ∀ u, IsInput U u → ∀ x : ℝ → Fin n → ℝ,
    IsSolution (fun x t => f x (u t)) ξ x → (∀ t, 0 ≤ t → x t ∈ X) →
      ∀ t, 0 ≤ t → x t = φ t ξ u

namespace IOSystem

variable (sys : IOSystem n)

/-- The system is monotone: `ξ₁ - ξ₂ ∈ K` and `u₁ ≥ u₂` on `[0, ∞)` imply
`φ t ξ₁ u₁ - φ t ξ₂ u₂ ∈ K` for all `t ≥ 0`; and the output map is monotone on `X`. -/
def IsMonotone : Prop :=
  (∀ ξ₁ ∈ sys.X, ∀ ξ₂ ∈ sys.X, ∀ u₁ u₂, IsInput sys.U u₁ → IsInput sys.U u₂ →
    ξ₁ - ξ₂ ∈ sys.K → (∀ t, 0 ≤ t → u₂ t ≤ u₁ t) →
      ∀ t, 0 ≤ t → sys.φ t ξ₁ u₁ - sys.φ t ξ₂ u₂ ∈ sys.K) ∧
  ∀ x₁ ∈ sys.X, ∀ x₂ ∈ sys.X, x₁ - x₂ ∈ sys.K → sys.h x₂ ≤ sys.h x₁

/-- `kX` is a non-degenerate input-to-state characteristic: for every `u ∈ U`, `kX u ∈ X` is an
equilibrium of `ẋ = f(x, u)` that is Lyapunov stable and attracts every solution from `X` (so it
is the unique globally asymptotically stable equilibrium on `X`), and
`det D_x f(kX u, u) ≠ 0`. -/
def IsNondegenerateCharacteristic (kX : ℝ → Fin n → ℝ) : Prop :=
  ∀ u ∈ sys.U, kX u ∈ sys.X ∧ sys.f (kX u) u = 0 ∧
    (∀ ε > 0, ∃ δ > 0, ∀ ξ ∈ sys.X, dist ξ (kX u) < δ →
      ∀ t, 0 ≤ t → dist (sys.φ t ξ (fun _ => u)) (kX u) < ε) ∧
    (∀ ξ ∈ sys.X, Tendsto (fun t => sys.φ t ξ (fun _ => u)) atTop (𝓝 (kX u))) ∧
    (stateJacobian sys.f (kX u) u).det ≠ 0

end IOSystem

/-- A map `k` has non-degenerate fixed points on `U`: at every `u ∈ U` with `k u = u`, `k` is
differentiable and `k'(u) ≠ 1`. -/
def HasNondegenerateFixedPoints (U : Set ℝ) (k : ℝ → ℝ) : Prop :=
  ∀ u ∈ U, k u = u → DifferentiableAt ℝ k u ∧ deriv k u ≠ 1

/-- **Equilibria of the positive feedback loop** (Angeli–Sontag 2004, Theorem 2, first part).
Let `sys` be a single-input single-output system (positivity cone `K`, state space `X` equal to
the closure of its interior, differentiable `f`, and a solution map `φ` giving, for every `ξ ∈ X`
and every input `u`, the unique solution from `ξ` on `[0, ∞)` that stays in `X`) that is
monotone, with a non-degenerate input-to-state characteristic `kX` on `U` (each constant input
`u ∈ U` has the unique globally asymptotically stable equilibrium `kX u ∈ X`, with
`det D_x f(kX u, u) ≠ 0`), and assume `h(X) ⊆ U`. Then `u ↦ kX u` is a bijection from the fixed
points `u ∈ U` of the input/output characteristic `kY = h ∘ kX` onto the equilibria `x ∈ X` of
the closed loop `ẋ = f(x, h(x))`.

Source: D. Angeli, E. D. Sontag, Systems Control Lett. 51 (2004) 185–202, Theorem 2. -/
theorem_wanted bijOn_fixedPoints_equilibria (sys : IOSystem n) (hmono : sys.IsMonotone)
    {kX : ℝ → Fin n → ℝ} (hk : sys.IsNondegenerateCharacteristic kX)
    (hhU : ∀ x ∈ sys.X, sys.h x ∈ sys.U) :
    Set.BijOn kX {u | u ∈ sys.U ∧ sys.h (kX u) = u} {x | x ∈ sys.X ∧ sys.f x (sys.h x) = 0}

/-- **Generic convergence of the positive feedback loop** (Angeli–Sontag 2004, Theorem 2, second
part). Let `sys` be a single-input single-output system (positivity cone `K`, state space `X`
equal to the closure of its interior, differentiable `f`, and a solution map `φ` giving, for every
`ξ ∈ X` and every input `u`, the unique solution from `ξ` on `[0, ∞)` that stays in `X`) that is
monotone, with a non-degenerate input-to-state characteristic `kX` on `U`; assume `h(X) ⊆ U`, and
let `ψ t ξ` be the solution map of the closed loop `ẋ = f(x, h(x))`: for `ξ ∈ X`, `t ↦ ψ t ξ` is a
solution on `[0, ∞)` that stays in `X`. Suppose the input/output characteristic `kY = h ∘ kX` has
non-degenerate fixed points on `U`, the closed loop is strongly monotone (`ξ₁ - ξ₂ ∈ K` and
`ξ₁ ≠ ξ₂` imply `ψ t ξ₁ - ψ t ξ₂ ∈ int K` for every `t > 0`), and every closed-loop trajectory
from `X` is bounded. Then for Lebesgue-almost every `ξ ∈ X`, the distance from `ψ t ξ` to the set
`{kX u | u ∈ U, kY u = u, kY'(u) < 1}` tends to `0`.

Source: D. Angeli, E. D. Sontag, Systems Control Lett. 51 (2004) 185–202, Theorem 2. -/
theorem_wanted ae_tendsto_infDist_stableEquilibria (sys : IOSystem n) (hmono : sys.IsMonotone)
    {kX : ℝ → Fin n → ℝ} (hk : sys.IsNondegenerateCharacteristic kX)
    (hhU : ∀ x ∈ sys.X, sys.h x ∈ sys.U) (ψ : ℝ → (Fin n → ℝ) → Fin n → ℝ)
    (hψ : ∀ ξ ∈ sys.X, IsSolution (fun x _ => sys.f x (sys.h x)) ξ (fun t => ψ t ξ) ∧
      ∀ t, 0 ≤ t → ψ t ξ ∈ sys.X)
    (hfix : HasNondegenerateFixedPoints sys.U (sys.h ∘ kX))
    (hstrong : ∀ ξ₁ ∈ sys.X, ∀ ξ₂ ∈ sys.X, ξ₁ - ξ₂ ∈ sys.K → ξ₁ ≠ ξ₂ →
      ∀ t, 0 < t → ψ t ξ₁ - ψ t ξ₂ ∈ interior sys.K)
    (hbdd : ∀ ξ ∈ sys.X, Bornology.IsBounded (Set.range fun t : Set.Ici (0 : ℝ) => ψ t ξ)) :
    ∀ᵐ ξ ∂(volume.restrict sys.X), Tendsto
      (fun t => Metric.infDist (ψ t ξ)
        (kX '' {u | u ∈ sys.U ∧ sys.h (kX u) = u ∧ deriv (sys.h ∘ kX) u < 1}))
      atTop (𝓝 0)

end WantedExt.Biology.Biophysics.MonotoneFeedbackMultistabilityWanted
