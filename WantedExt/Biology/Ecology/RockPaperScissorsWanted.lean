/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rock–paper–scissors replicator dynamics: the trichotomy by the sign of `det A`

The replicator equation `xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` on the simplex `S₃` for the
rock–paper–scissors matrix in Hofbauer and Sigmund's convention
`A = [[0, -a₂, b₃], [b₁, 0, -a₃], [-a₁, b₂, 0]]` with wins `bᵢ > 0` and losses `aᵢ > 0`
has a unique rest point `z` in the interior of `S₃`. After Zeeman (1980), Hofbauer and Sigmund
(2003, Theorem 2) state that the following are equivalent: (a) `z` is asymptotically stable;
(b) `z` is globally stable; (c) `det A > 0`; (d) `zᵀ A z > 0`. If `det A = 0`, every interior
orbit is a closed orbit around `z`; if `det A < 0`, every interior orbit other than `z` has as
ω-limit the heteroclinic cycle through the vertices `e₁, e₂, e₃`, which is the boundary of `S₃`.
Here `det A = b₁ b₂ b₃ - a₁ a₂ a₃`.

Recorded here: the four equivalences, the closed orbits for `det A = 0`, and convergence to the
heteroclinic cycle for `det A < 0`, for solutions on `[0, ∞)` starting in the interior of `S₃`.
Asymptotic stability is relative to the simplex; global stability means Lyapunov stability plus
convergence of every interior solution. Zeeman (1980) and Hofbauer–Sigmund (1998, §7.7) were not
read; the statement follows Hofbauer and Sigmund (2003).

Sources: E. C. Zeeman, "Population dynamics from game theory", in *Global Theory of Dynamical
Systems*, Lecture Notes in Math. 819, Springer (1980); J. Hofbauer and K. Sigmund, "Evolutionary
game dynamics", Bull. Amer. Math. Soc. (N.S.) 40 (2003) 479–519,
doi:10.1090/S0273-0979-03-00988-1, Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Ecology.RockPaperScissorsWanted

open Filter Topology Matrix

/-- The rock–paper–scissors payoff matrix `[[0, -a₂, b₃], [b₁, 0, -a₃], [-a₁, b₂, 0]]` with
losses `aᵢ` and wins `bᵢ` (indices `0, 1, 2` for strategies `1, 2, 3`). -/
def rpsMatrix (a b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -a 1, b 2; b 0, 0, -a 2; -a 0, b 1, 0]

/-- `x` solves the **replicator equation** `xᵢ' = xᵢ ((A x)ᵢ - ∑ⱼ xⱼ (A x)ⱼ)` on `[0, ∞)`,
coordinatewise. This is the condition of the library's replicator-equation predicate
`MathlibExt.Biology.Dynamics.Replicator.IsSolution` (in
`Domains.Biology.Dynamics.Replicator`) for the linear fitness `fun z => A *ᵥ z`, whose mean
fitness is `∑ⱼ xⱼ (A x)ⱼ`; it is restated here because `WantedExt` may not import `Domains`. -/
def IsSolution (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ → Fin 3 → ℝ) : Prop :=
  ∀ i t, 0 ≤ t →
    HasDerivAt (fun s => x s i) (x t i * ((A *ᵥ x t) i - ∑ j, x t j * (A *ᵥ x t) j)) t

/-- `z` is in the **interior of the simplex** `S₃`: every `zᵢ > 0` and `∑ zᵢ = 1`. -/
def InInterior (z : Fin 3 → ℝ) : Prop := (∀ i, 0 < z i) ∧ ∑ i, z i = 1

/-- `z` is in the **boundary of the simplex** `S₃`: every `zᵢ ≥ 0`, `∑ zᵢ = 1`, and some
coordinate vanishes. For `S₃` this is the heteroclinic cycle `e₁ → e₂ → e₃ → e₁`. -/
def InBoundary (z : Fin 3 → ℝ) : Prop := (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1 ∧ ∃ i, z i = 0

/-- `z` is an **interior rest point**: `z` is in the interior of `S₃` and `(A z)ᵢ = zᵀ A z` for
every `i`. -/
def IsInteriorRestPoint (A : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  InInterior z ∧ ∀ i, (A *ᵥ z) i = z ⬝ᵥ (A *ᵥ z)

/-- `z` is **Lyapunov stable** for solutions starting in the simplex: for every `ε > 0` there is
`δ > 0` such that every solution on `[0, ∞)` with `x(0)` in the simplex and `‖x(0) - z‖ < δ` has
`‖x(t) - z‖ < ε` for every `t ≥ 0`. -/
def IsLyapunovStable (A : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → Fin 3 → ℝ, IsSolution A x →
    (∀ i, 0 ≤ x 0 i) → ∑ i, x 0 i = 1 → ‖x 0 - z‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖x t - z‖ < ε

/-- `z` is **asymptotically stable**: Lyapunov stable, and there is `δ₀ > 0` such that every
solution on `[0, ∞)` with `x(0)` in the simplex and `‖x(0) - z‖ < δ₀` converges to `z`. -/
def IsAsymptoticallyStable (A : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  IsLyapunovStable A z ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x : ℝ → Fin 3 → ℝ, IsSolution A x →
    (∀ i, 0 ≤ x 0 i) → ∑ i, x 0 i = 1 → ‖x 0 - z‖ < δ₀ → Tendsto x atTop (𝓝 z)

/-- `z` is **globally stable**: Lyapunov stable, and every solution on `[0, ∞)` with `x(0)` in the
interior of `S₃` converges to `z`. -/
def IsGloballyStable (A : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) : Prop :=
  IsLyapunovStable A z ∧ ∀ x : ℝ → Fin 3 → ℝ, IsSolution A x → InInterior (x 0) →
    Tendsto x atTop (𝓝 z)

/-- **Unique interior rest point** (Hofbauer and Sigmund 2003, §3): for losses `aᵢ > 0` and wins
`bᵢ > 0`, the rock–paper–scissors replicator equation has exactly one rest point in the interior
of `S₃`.

Source: Hofbauer and Sigmund (2003), Theorem 2 and the text before it. -/
public theorem_wanted existsUnique_interiorRestPoint (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) :
    ∃! z, IsInteriorRestPoint (rpsMatrix a b) z

/-- **Zeeman's equivalences** (Hofbauer and Sigmund 2003, Theorem 2): let `aᵢ > 0`, `bᵢ > 0`, and
let `z` be the interior rest point of the rock–paper–scissors replicator equation with matrix
`A`. Then the following are equivalent: (a) `z` is asymptotically stable; (b) `z` is globally
stable; (c) `det A > 0`; (d) `zᵀ A z > 0`.

Sources: Zeeman (1980); Hofbauer and Sigmund (2003), Theorem 2. -/
public theorem_wanted zeeman_tfae (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (z : Fin 3 → ℝ) (hz : IsInteriorRestPoint (rpsMatrix a b) z) :
    (IsAsymptoticallyStable (rpsMatrix a b) z ↔ IsGloballyStable (rpsMatrix a b) z) ∧
      (IsGloballyStable (rpsMatrix a b) z ↔ 0 < (rpsMatrix a b).det) ∧
      (0 < (rpsMatrix a b).det ↔ 0 < z ⬝ᵥ (rpsMatrix a b *ᵥ z))

/-- **Closed orbits when `det A = 0`** (Hofbauer and Sigmund 2003, Theorem 2): let `aᵢ > 0`,
`bᵢ > 0` with `det A = 0`. Then every solution on `[0, ∞)` with `x(0)` in the interior of `S₃` is
periodic: there is `T > 0` with `x(t + T) = x(t)` for every `t ≥ 0`.

Sources: Zeeman (1980); Hofbauer and Sigmund (2003), Theorem 2. -/
public theorem_wanted periodic_of_det_eq_zero (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hdet : (rpsMatrix a b).det = 0) (x : ℝ → Fin 3 → ℝ)
    (hx : IsSolution (rpsMatrix a b) x) (hx₀ : InInterior (x 0)) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 ≤ t → x (t + T) = x t

/-- **Convergence to the heteroclinic cycle when `det A < 0`** (Hofbauer and Sigmund 2003,
Theorem 2): let `aᵢ > 0`, `bᵢ > 0` with `det A < 0`, and let `z` be the interior rest point. Then
every solution `x` on `[0, ∞)` with `x(0)` in the interior of `S₃` and `x(0) ≠ z` has the
boundary of `S₃` (the heteroclinic cycle through `e₁, e₂, e₃`) as ω-limit set: `∏ᵢ xᵢ(t) → 0`, and
every point of the boundary is a cluster point of `x(t)` as `t → ∞`.

Sources: Zeeman (1980); Hofbauer and Sigmund (2003), Theorem 2. -/
public theorem_wanted omegaLimit_heteroclinic_of_det_neg (a b : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hdet : (rpsMatrix a b).det < 0) (z : Fin 3 → ℝ)
    (hz : IsInteriorRestPoint (rpsMatrix a b) z) (x : ℝ → Fin 3 → ℝ)
    (hx : IsSolution (rpsMatrix a b) x) (hx₀ : InInterior (x 0)) (hne : x 0 ≠ z) :
    Tendsto (fun t => ∏ i, x t i) atTop (𝓝 0) ∧
      ∀ q, InBoundary q → MapClusterPt q atTop x

end WantedExt.Biology.Ecology.RockPaperScissorsWanted
