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
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace WantedExt.Biology.Ecology.ReplicatorPermanenceWanted

open Matrix

/-- `x` solves the **replicator equation** `xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` on `[0, ∞)`. -/
def IsSolution {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivAt x (fun i => x t i * ((A *ᵥ x t) i - x t ⬝ᵥ (A *ᵥ x t))) t

/-- `b` is a **rest point on the boundary of the simplex**: `b` is in the simplex (every
`bᵢ ≥ 0`, `∑ bᵢ = 1`), some coordinate vanishes, and `bᵢ ((A b)ᵢ - bᵀ A b) = 0` for every `i`. -/
def IsBoundaryRestPoint {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (b : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧ ∑ i, b i = 1 ∧ (∃ i, b i = 0) ∧
    ∀ i, b i * ((A *ᵥ b) i - b ⬝ᵥ (A *ᵥ b)) = 0

/-- The replicator equation is **permanent**: there is `δ > 0` such that every solution on
`[0, ∞)` starting in the interior of the simplex (every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) eventually
has every coordinate at least `δ`: some `T` has `xᵢ(t) ≥ δ` for all `t ≥ T` and all `i`. -/
def IsPermanent {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → ι → ℝ, IsSolution A x → (∀ i, 0 < x 0 i) → ∑ i, x 0 i = 1 →
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ i, δ ≤ x t i

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
