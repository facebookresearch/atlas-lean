/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Every evolutionarily stable state is asymptotically stable for the replicator dynamics

For a symmetric matrix game with payoff matrix `A`, the replicator equation on the simplex
`Δ = {x | x ≥ 0, ∑ x = 1}` is `ẋ_i = x_i ((A x)_i - x · A x)`. Hofbauer, Schuster and Sigmund
(1979) showed that `p ∈ Δ` is an evolutionarily stable state (ESS, in the sense of Maynard Smith
and Price) iff `p · A x > x · A x` for all `x ≠ p` in `Δ` near `p`, so that
`V(x) = ∏ x_i ^ p_i` is a strict local Lyapunov function, and therefore every ESS, interior or on
the boundary of `Δ`, is asymptotically stable. An interior ESS attracts every interior orbit
(Hofbauer and Sigmund 2003, Theorem 7). Taylor and Jonker (1978) proved the stronger linear
statement for a regular ESS. The converse fails: the interior rest point of the four-member
hypercycle is asymptotically stable but not an ESS.

`Domains.Biology.Dynamics.ReplicatorStability` proves asymptotic stability only for an interior
ESS (`IsESS.asymptoticallyStable` with `∀ i, 0 < p i`) and states that boundary ESS are not
covered. `WantedExt` may not import `Domains`, so the replicator vector field, the ESS predicate
and the stability notions are restated here with the same meaning as `Replicator.IsSolution`
and `Replicator.IsESS`.

Sources: J. Hofbauer, P. Schuster and K. Sigmund, "A note on evolutionary stable strategies and
game dynamics", J. Theor. Biol. 81 (1979) 609–612; P. D. Taylor and L. B. Jonker,
"Evolutionarily stable strategies and game dynamics", Math. Biosci. 40 (1978) 145–156, §§2–4;
J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.) 40
(2003) 479–519, §2.6, Theorem 7.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- The simplex of mixed strategies `Δ = {x | ∀ i, 0 ≤ x i, ∑ i, x i = 1}`. -/
def simplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The **replicator vector field** of the matrix game `A`:
`F(x)_i = x_i ((A x)_i - x · A x)`. -/
def replicatorField (A : Matrix ι ι ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => x i * ((A *ᵥ x) i - x ⬝ᵥ A *ᵥ x)

/-- `x` solves the replicator equation `ẋ = F(x)` of `A` for all times `t ≥ 0`. -/
def IsReplicatorSolution (A : Matrix ι ι ℝ) (x : ℝ → ι → ℝ) : Prop :=
  ∀ i t, 0 ≤ t → HasDerivAt (fun s => x s i) (replicatorField A (x t) i) t

/-- `p` is an **evolutionarily stable state** of `A` (Maynard Smith and Price): `p ∈ Δ` and for
every `q ∈ Δ` with `q ≠ p`, either `q · A p < p · A p`, or `q · A p = p · A p` and
`q · A q < p · A q`. -/
def IsESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ q ∈ simplex ι, q ≠ p →
    q ⬝ᵥ A *ᵥ p < p ⬝ᵥ A *ᵥ p ∨ (q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p ∧ q ⬝ᵥ A *ᵥ q < p ⬝ᵥ A *ᵥ q)

/-- `p` is **locally superior**: `p ∈ Δ` and `x · A x < p · A x` for every `x ≠ p` in `Δ`
near `p`. -/
def IsLocallySuperior (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ᶠ x in 𝓝 p, x ∈ simplex ι → x ≠ p → x ⬝ᵥ A *ᵥ x < p ⬝ᵥ A *ᵥ x

/-- `p` is **asymptotically stable** for the replicator dynamics of `A` on `Δ`: every state of
`Δ` has a forward solution; `p` is Lyapunov stable (for every `ε > 0` there is `δ > 0` such
that every solution starting in `Δ` within `δ` of `p` stays within `ε` of `p` for all `t ≥ 0`);
and `p` is locally attracting (there is `δ > 0` such that every solution starting in `Δ` within
`δ` of `p` converges to `p`). -/
def IsAsymptoticallyStable (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  (∀ x₀ ∈ simplex ι, ∃ x : ℝ → ι → ℝ, x 0 = x₀ ∧ IsReplicatorSolution A x) ∧
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x → x 0 ∈ simplex ι →
      ‖x 0 - p‖ < δ → ∀ t, 0 ≤ t → ‖x t - p‖ < ε) ∧
  ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x → x 0 ∈ simplex ι →
    ‖x 0 - p‖ < δ → Tendsto x atTop (𝓝 p)

/-- A **regular ESS** in the sense of Taylor and Jonker (1978): an ESS `p` such that
`(A p)_i < p · A p` for every strategy `i` outside the support of `p`, and `x · A x < 0` for
every nonzero `x` with `∑ x = 0` supported in the support of `p`. -/
def IsRegularESS (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  IsESS A p ∧ (∀ i, p i = 0 → (A *ᵥ p) i < p ⬝ᵥ A *ᵥ p) ∧
    ∀ x : ι → ℝ, x ≠ 0 → ∑ i, x i = 0 → (∀ i, p i = 0 → x i = 0) → x ⬝ᵥ A *ᵥ x < 0

/-- The Jacobian matrix of the replicator vector field of `A` at `p`. -/
noncomputable def replicatorJacobian [DecidableEq ι] (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    Matrix ι ι ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (replicatorField A) p : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- **ESS ⇔ local superiority** (Hofbauer, Schuster and Sigmund 1979). For every payoff matrix
`A` and every `p`, `p` is an ESS of `A` iff `p ∈ Δ` and `x · A x < p · A x` for all `x ≠ p` in
`Δ` near `p`.

Source: Hofbauer, Schuster and Sigmund (1979), pp. 609–611. -/
public theorem_wanted isESS_iff_isLocallySuperior (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    IsESS A p ↔ IsLocallySuperior A p

/-- **Every ESS is asymptotically stable** (Hofbauer, Schuster and Sigmund 1979). For every
payoff matrix `A` and every ESS `p` of `A`, interior or on the boundary of `Δ`, `p` is
asymptotically stable for the replicator dynamics: solutions from `Δ` exist, `p` is Lyapunov
stable on `Δ`, and `p` attracts every solution starting in `Δ` near `p`.

Source: Hofbauer, Schuster and Sigmund (1979), corollary after D4. -/
public theorem_wanted IsESS.isAsymptoticallyStable {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsESS A p) : IsAsymptoticallyStable A p

/-- **An interior ESS attracts every interior orbit** (Hofbauer and Sigmund 2003, Theorem 7).
For every payoff matrix `A` and every ESS `p` of `A` with `p i > 0` for all `i`, every solution
`x` of the replicator equation with `x 0 ∈ Δ` and `x 0 i > 0` for all `i` converges to `p`.

Source: Hofbauer and Sigmund (2003), §2.6, Theorem 7. -/
public theorem_wanted IsESS.tendsto_of_pos {A : Matrix ι ι ℝ} {p : ι → ℝ} (h : IsESS A p)
    (hp : ∀ i, 0 < p i) {x : ℝ → ι → ℝ} (hx : IsReplicatorSolution A x)
    (hx₀ : x 0 ∈ simplex ι) (hx₀pos : ∀ i, 0 < x 0 i) : Tendsto x atTop (𝓝 p)

/-- **A regular ESS is linearly stable** (Taylor and Jonker 1978, §3 Theorem). For every payoff
matrix `A` and every regular ESS `p` of `A`, every complex eigenvalue `μ` of the Jacobian of the
replicator field at `p` with an eigenvector `h ≠ 0` in the tangent space `∑ h = 0` has
`Re μ < 0`.

Source: Taylor and Jonker (1978), §2 (regular ESS, p. 148), §3 Theorem (p. 150). -/
public theorem_wanted IsRegularESS.re_lt_zero [DecidableEq ι] {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsRegularESS A p) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (hμ : (replicatorJacobian A p).map (fun a : ℝ => (a : ℂ)) *ᵥ v = μ • v) : μ.re < 0

/-- The payoff matrix of the **four-member hypercycle** with rates `k`:
`a_{i, i-1} = k_i` (indices mod 4) and all other entries `0`. -/
def hypercycle (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if j = i - 1 then k i else 0

/-- **The converse fails** (Hofbauer, Schuster and Sigmund 1979, hypercycle example). For every
`k` with `k i > 0` for all `i`, the four-member hypercycle has a rest point `p` with `p i > 0`
for all `i` and `∑ p = 1` that is asymptotically stable for the replicator dynamics but is not
an ESS.

Source: Hofbauer, Schuster and Sigmund (1979), p. 611. -/
public theorem_wanted hypercycle_not_isESS (k : Fin 4 → ℝ) (hk : ∀ i, 0 < k i) :
    ∃ p : Fin 4 → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ replicatorField (hypercycle k) p = 0 ∧
      IsAsymptoticallyStable (hypercycle k) p ∧ ¬ IsESS (hypercycle k) p

end WantedExt.Biology.Ecology.BoundaryESSStabilityWanted
