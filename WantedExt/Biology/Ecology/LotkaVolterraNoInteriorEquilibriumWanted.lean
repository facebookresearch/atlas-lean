/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lotka–Volterra and replicator systems without an interior equilibrium

For the Lotka–Volterra system `yᵢ' = yᵢ (rᵢ + ∑ⱼ cᵢⱼ yⱼ)` with no equilibrium in the open
positive orthant, no interior orbit has an ω-limit point in the open orthant: the ω-limit set lies
in the boundary or is empty, the orbit going to infinity (Hofbauer and Sigmund 1998, §5.2,
Theorem 5.2.1). For the replicator equation `xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` with no rest point in
the interior of the simplex, every interior orbit converges to the boundary of the simplex
(Hofbauer and Sigmund 2003, §2.5, Theorem 4, last sentence). The two forms are linked by
Hofbauer's orbital equivalence (`Domains.Biology.Dynamics.ReplicatorLotkaVolterra`), whose
Lotka–Volterra field `lvField` is used here. The replicator equation and its rest points are the
library predicates `IsSolution` and `IsRestPoint` of `MathlibExt.Biology.Dynamics.Replicator`
(`MathlibExt.Dynamics.Replicator.Basic`). The argument is a Farkas-type separation followed by
time averaging.

Recorded here: both forms, for solutions on `[0, ∞)` starting in the open orthant, respectively
in the interior of the simplex. "Converges to the boundary" is stated as
`∏ᵢ xᵢ(t) → 0`, which on the simplex is equivalent to the distance to the boundary tending
to `0`.

Sources: J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.)
40 (2003) 479–519, doi:10.1090/S0273-0979-03-00988-1, §2.5, Theorem 4 (p. 485); J. Hofbauer and
K. Sigmund, *Evolutionary Games and Population Dynamics*, Cambridge Univ. Press (1998), §5.2,
Theorem 5.2.1.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.Replicator.Basic
public import Domains.Biology.Dynamics.ReplicatorLotkaVolterra
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Ecology.LotkaVolterraNoInteriorEquilibriumWanted

open Filter Topology Matrix MathlibExt.Biology.Dynamics.Replicator
open MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra (lvField)

/-- **Forward solutions of the Lotka–Volterra system.** `y` solves `yᵢ' = yᵢ (rᵢ + ∑ⱼ Cᵢⱼ yⱼ)`,
with the library's field `lvField r C`, at every time `t ≥ 0`. The derivative is two-sided
(`HasDerivAt`) at `t = 0` too, so a trajectory given only on `[0, ∞)` must be extended to
negative times with that derivative at `0`; one that is only right-differentiable at `0` does
not qualify. A solution on an open interval containing `[0, ∞)` qualifies, and negative times
matter only through the derivative at `0`. This is the convention of `IsSolution` and of the
hypothesis of `lotkaVolterra_orbitEquiv_replicator`. -/
def IsLVSolution {ι : Type*} [Fintype ι] (r : ι → ℝ) (C : Matrix ι ι ℝ) (y : ℝ → ι → ℝ) :
    Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivAt y (lvField r C (y t)) t

/-- `z` is in the **interior of the simplex**: every coordinate positive, coordinates sum to `1`. -/
def InInteriorSimplex {ι : Type*} [Fintype ι] (z : ι → ℝ) : Prop :=
  (∀ i, 0 < z i) ∧ ∑ i, z i = 1

/-- **No interior ω-limit points** (Hofbauer and Sigmund 1998, §5.2, Theorem 5.2.1): let `r` be a
real vector and `C` a real square matrix indexed by a finite type, and suppose the Lotka–Volterra
system has no equilibrium in the open positive orthant: no `z` with every `zᵢ > 0` and
`r + C z = 0`. Then for every solution `y` on `[0, ∞)` with every `yᵢ(0) > 0`, no point `p` with
every `pᵢ > 0` is an ω-limit point of `y`, i.e. `p` is not a cluster point of `y(t)` as `t → ∞`.

Source: Hofbauer and Sigmund (1998), §5.2, Theorem 5.2.1. -/
public theorem_wanted not_mapClusterPt_of_no_interior_eq {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (C : Matrix ι ι ℝ) (hno : ¬ ∃ z : ι → ℝ, (∀ i, 0 < z i) ∧ r + C *ᵥ z = 0)
    (y : ℝ → ι → ℝ) (hy : IsLVSolution r C y) (hy₀ : ∀ i, 0 < y 0 i)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) :
    ¬ MapClusterPt p atTop y

/-- **Convergence to the boundary of the simplex** (Hofbauer and Sigmund 2003, §2.5, Theorem 4):
let `A` be a real square matrix indexed by a finite type, and suppose the replicator equation
`xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` (`IsSolution (fun z => A *ᵥ z)`) has no rest point in the interior
of the simplex: no `z` with every `zᵢ > 0`, `∑ zᵢ = 1` and `IsRestPoint (fun z => A *ᵥ z) z`
(that is, `zᵢ ((A z)ᵢ - zᵀ A z) = 0` for every `i`). Then every solution `x` with `x(0)` in the
interior of the simplex converges to the boundary: `∏ᵢ xᵢ(t) → 0` as `t → ∞`. Here `IsSolution`
asks for two-sided derivatives at every `t ≥ 0`, `t = 0` included: a trajectory given only on
`[0, ∞)` must be extended to negative times with the replicator derivative at `0`.

Source: Hofbauer and Sigmund (2003), §2.5, Theorem 4 (p. 485). -/
public theorem_wanted tendsto_boundary_of_no_interior_rest_point {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ)
    (hno : ¬ ∃ z : ι → ℝ, InInteriorSimplex z ∧ IsRestPoint (fun z => A *ᵥ z) z)
    (x : ℝ → ι → ℝ) (hx : IsSolution (fun z => A *ᵥ z) x) (hx₀ : InInteriorSimplex (x 0)) :
    Tendsto (fun t => ∏ i, x t i) atTop (𝓝 0)

end WantedExt.Biology.Ecology.LotkaVolterraNoInteriorEquilibriumWanted
