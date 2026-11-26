/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permanence of replicator systems via an average Lyapunov function

A replicator system `xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` on the simplex `Sₙ` is permanent if there is a
compact subset of the interior of `Sₙ` that every interior orbit eventually enters and never
leaves; equivalently, some `δ > 0` bounds every coordinate of every interior orbit from below
after a transient. Hofbauer and Sigmund (2003, Theorem 5), after Hofbauer (1981) and Jansen
(1987): the replicator equation is permanent if there is `p` in the interior of `Sₙ` with
`pᵀ A b > bᵀ A b` for every rest point `b` on the boundary of `Sₙ`. The average Lyapunov function
is `P(x) = ∏ᵢ xᵢ^{pᵢ}`. Jansen's Lotka–Volterra form needs, in addition, that the system be
dissipative (orbits eventually bounded); without it the condition can hold while orbits blow up
(`y' = y (1 + y)` in dimension one), so only the replicator form, on the compact simplex, is
recorded here.

The replicator equation and its rest points are the library predicates `IsSolution` and
`IsRestPoint` of `MathlibExt.Biology.Dynamics.Replicator` (`MathlibExt.Dynamics.Replicator.Basic`).

Recorded here: the replicator permanence criterion, with permanence stated as a uniform
eventual lower bound `δ` on all coordinates of all interior orbits on `[0, ∞)`. Jansen (1987) was
read only in its abstract.

Sources: J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.)
40 (2003) 479–519, doi:10.1090/S0273-0979-03-00988-1, Theorem 5; W. Jansen, "A permanence theorem
for replicator and Lotka–Volterra systems", J. Math. Biol. 25 (1987) 411–422,
doi:10.1007/BF00277165; J. Hofbauer, "A general cooperation theorem for hypercycles", Monatsh.
Math. 91 (1981) 233–240.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.Replicator.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace WantedExt.Biology.Ecology.ReplicatorPermanenceWanted

open Matrix MathlibExt.Biology.Dynamics.Replicator

/-- `b` is a **rest point on the boundary of the simplex**: `b` is in the simplex (every
`bᵢ ≥ 0`, `∑ bᵢ = 1`), some coordinate vanishes, and `b` is a rest point of the replicator
equation, `IsRestPoint (fun z => A *ᵥ z) b` (`bᵢ ((A b)ᵢ - bᵀ A b) = 0` for every `i`). -/
def IsBoundaryRestPoint {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (b : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧ ∑ i, b i = 1 ∧ (∃ i, b i = 0) ∧ IsRestPoint (fun z => A *ᵥ z) b

/-- The replicator equation of the matrix game `A` is **permanent**: there is `δ > 0` such that
every solution `x` (`IsSolution (fun z => A *ᵥ z) x`) starting in the interior of the simplex
(every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) eventually has every coordinate at least `δ`: some `T` has
`xᵢ(t) ≥ δ` for all `t ≥ T` and all `i`. Here `IsSolution` asks for two-sided derivatives at
every `t ≥ 0`, `t = 0` included: a trajectory given only on `[0, ∞)` must be extended to negative
times with the replicator derivative at `0`. -/
def IsPermanent {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → ι → ℝ, IsSolution (fun z => A *ᵥ z) x → (∀ i, 0 < x 0 i) →
    ∑ i, x 0 i = 1 → ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ i, δ ≤ x t i

/-- **Permanence criterion** (Hofbauer and Sigmund 2003, Theorem 5; Jansen 1987): let `A` be a
real square matrix indexed by a finite type. If there is `p` in the interior of the simplex
(every `pᵢ > 0`, `∑ pᵢ = 1`) such that `pᵀ A b > bᵀ A b` for every rest point `b` of the
replicator equation on the boundary of the simplex, then the replicator equation is permanent.

Sources: Hofbauer and Sigmund (2003), Theorem 5; Jansen (1987). -/
public theorem_wanted isPermanent_of_average_lyapunov {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hp₁ : ∑ i, p i = 1)
    (hlyap : ∀ b, IsBoundaryRestPoint A b → b ⬝ᵥ (A *ᵥ b) < p ⬝ᵥ (A *ᵥ b)) :
    IsPermanent A

end WantedExt.Biology.Ecology.ReplicatorPermanenceWanted
