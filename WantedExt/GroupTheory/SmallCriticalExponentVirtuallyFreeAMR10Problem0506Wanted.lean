/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kleinian groups of small critical exponent are virtually free (Bestvina, Q 5.6)

M. Bestvina, Questions in Geometric Group Theory, Q 5.6 (Misha Kapovich), for finitely generated
Kleinian groups `G` in `Isom(ℍⁿ)` as in Q 5.5: is there `ε > 0` so that `δ(G) < ε` implies that `G`
is virtually free?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

namespace MathlibExt.GroupTheory.SmallCriticalExponentVirtuallyFreeAMR10Problem0506Wanted

/-!
Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 5.6 (Misha
Kapovich), https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf. UnsolvedMath record
UM-01100506 (`AMR-010-0506`), dataset ulamai/UnsolvedMath v1.8.0.

`Isom(ℍⁿ)` is `O⁺(n, 1)`: matrices preserving `J = diag(-1, 1, …, 1)` with `A₀₀ > 0`, acting on the
hyperboloid model; a Kleinian group is a discrete subgroup (`DiscreteTopology`, topology of `GL`).
With base point `o = e₀`, `d(o, A o) = arcosh A₀₀`, and `δ(Γ) < ε` is stated as convergence of the
Poincaré series `∑_{γ ∈ Γ} exp(-s d(o, γ o))` for some `s < ε` (equivalent, and free of junk values
of an infimum). Virtually free: some finite-index subgroup is free. The constant depends on `n`, as
in the question.
-/

/-- The Lorentzian form `J = diag(-1, 1, …, 1)` on `ℝ^{n+1}`. -/
def lorentzForm (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else 1

/-- `A ∈ O⁺(n, 1)`: `Aᵀ J A = J` and `A₀₀ > 0`, i.e. `A` is an isometry of the hyperboloid model
`ℍⁿ = {x : -x₀² + x₁² + ⋯ + xₙ² = -1, x₀ > 0}`; these are all the isometries of `ℍⁿ`. -/
def IsHyperbolicIsometry {n : ℕ} (A : GL (Fin (n + 1)) ℝ) : Prop :=
  (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).transpose * lorentzForm n *
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = lorentzForm n ∧
    0 < (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0

/-- The hyperbolic distance `d(o, A o) = arcosh A₀₀` from the base point `o = e₀` of `ℍⁿ`. -/
noncomputable def displacement {n : ℕ} (A : GL (Fin (n + 1)) ℝ) : ℝ :=
  Real.arcosh ((A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) 0 0)

/-- Kapovich's question (Bestvina Q 5.6), answered: for each `n` there is `ε > 0` such that every
finitely generated discrete subgroup `Γ` of `Isom(ℍⁿ)` with critical exponent `δ(Γ) < ε` is
virtually free. `δ(Γ) < ε` is stated as convergence of the Poincaré series
`∑_{γ ∈ Γ} exp(-s d(o, γ o))` for some `s < ε`. -/
def smallCriticalExponentVirtuallyFree : Prop :=
  ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (GL (Fin (n + 1)) ℝ),
    (∀ A ∈ Γ, IsHyperbolicIsometry A) → DiscreteTopology Γ → Γ.FG →
    (∃ s : ℝ, s < ε ∧ Summable fun A : Γ => Real.exp (-s * displacement (A : GL (Fin (n + 1)) ℝ))) →
    ∃ H : Subgroup Γ, H.FiniteIndex ∧ IsFreeGroup H

/--
Resolved true: Liu and Wang proved that for each `n` there is `D(n) ∈ (0, 1/2)` such that every
finitely generated discrete subgroup of `Isom(ℍⁿ)` with critical exponent `δ(Γ) < D(n)` is virtually
free (for torsion-free groups even convex cocompact, Theorem 1.2). Source: M. Bestvina, Questions in
Geometric Group Theory (updated July 2004), Q 5.6 (Misha Kapovich),
https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf; resolution: B. Liu and S. Wang,
Discrete subgroups of small critical exponent, Geom. Topol. 27 (2023), 2347-2381, arXiv:2008.12365,
Corollary 1.6: "For each n, there exists a positive constant D(n) < 1/2 such that, any finitely
generated discrete isometry subgroup Γ < Isom(ℍⁿ) is virtually free if δ(Γ) < D(n)",
https://arxiv.org/abs/2008.12365.
-/
public theorem_wanted smallCriticalExponentVirtuallyFree_holds : smallCriticalExponentVirtuallyFree

end MathlibExt.GroupTheory.SmallCriticalExponentVirtuallyFreeAMR10Problem0506Wanted
