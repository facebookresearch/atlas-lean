/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Goh's theorem: diagonal stability gives global stability of Lotka–Volterra systems

The generalized Lotka–Volterra system is `xᵢ' = xᵢ (bᵢ + ∑ⱼ aᵢⱼ xⱼ)` on the open positive
orthant. Goh (1977) showed: if there is an interior equilibrium `x* > 0` (every coordinate
positive, `b + A x* = 0`) and a positive diagonal matrix `D = diag(d₁, …, dₙ)` such that
`D A + Aᵀ D` is negative definite, then `x*` is globally asymptotically stable in the open
orthant. The Lyapunov function is `V(x) = ∑ᵢ dᵢ (xᵢ - xᵢ* - xᵢ* ln(xᵢ / xᵢ*))`, whose derivative
along solutions is `½ (x - x*)ᵀ (D A + Aᵀ D) (x - x*) < 0` for `x ≠ x*`.

Recorded here: Lyapunov stability and global attractivity of `x*` for solutions on `[0, ∞)`
starting in the open orthant. Only Goh's abstract was read; the statement follows the
presentation of Goh's Lyapunov function in Allesina's lecture notes (§3.3.6), where the
condition `A W + W Aᵀ < 0` for a positive diagonal `W` is equivalent to the condition here with
`D = W⁻¹` (derived).

Sources: B. S. Goh, "Global stability in many-species systems", Am. Nat. 111 (1977) 135–143,
doi:10.1086/283144; B. S. Goh, "Global stability in two species interactions", J. Math. Biol. 3
(1976) 313–318, doi:10.1007/BF00275063; S. Allesina, *Theoretical Community Ecology*, lecture
notes, §3.3.6.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.Ecology.LotkaVolterraNoInteriorEquilibriumWanted
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace WantedExt.Biology.Ecology.GohDiagonalStabilityWanted

open Filter Topology Matrix
open LotkaVolterraNoInteriorEquilibriumWanted (IsLVSolution)

/-- `A` is **diagonally stable with weights `d`**: every `dᵢ > 0` and the symmetric matrix
`D A + Aᵀ D`, with `D = diag(d)`, is negative definite: `vᵀ (D A + Aᵀ D) v < 0` for every
`v ≠ 0`. -/
def IsDiagonallyStable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ ∀ v : Fin n → ℝ, v ≠ 0 → v ⬝ᵥ ((diagonal d * A + Aᵀ * diagonal d) *ᵥ v) < 0

/-- **Goh's global stability theorem** (Goh 1977): let `A` be a real `n × n` matrix and `b` a real
vector, and suppose (1) `x*` is an interior equilibrium: every `xᵢ* > 0` and `b + A x* = 0`; and
(2) there are weights `d` with every `dᵢ > 0` such that `D A + Aᵀ D` is negative definite. Then
(a) `x*` is Lyapunov stable for the solutions on `[0, ∞)` that start in the open positive orthant:
for every `ε > 0` there is `δ > 0` such that every such solution with `‖x(0) - x*‖ < δ` has
`‖x(t) - x*‖ < ε` for all `t ≥ 0`; and (b) every solution on `[0, ∞)` with all `xᵢ(0) > 0`
converges to `x*` as `t → ∞`.

Sources: Goh (1977); Allesina, lecture notes §3.3.6. -/
public theorem_wanted globally_stable {n : ℕ} (b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (xs : Fin n → ℝ) (hxs : ∀ i, 0 < xs i) (heq : b + A *ᵥ xs = 0) (d : Fin n → ℝ)
    (hd : IsDiagonallyStable A d) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ → Fin n → ℝ, IsLVSolution b A x →
        (∀ i, 0 < x 0 i) → ‖x 0 - xs‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖x t - xs‖ < ε) ∧
      ∀ x : ℝ → Fin n → ℝ, IsLVSolution b A x → (∀ i, 0 < x 0 i) → Tendsto x atTop (𝓝 xs)

end WantedExt.Biology.Ecology.GohDiagonalStabilityWanted
