/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Analysis.ODE.PolynomialGlobal
public import MathlibExt.AlgebraicGeometry.PolynomialInequalities

/-!
# Sum-of-squares boundary identities give compact polynomial trapping

An exact identity for the negative Lie derivative as a sum of squares plus
a multiple of the level polynomial proves inwardness on its zero set. With
compactness and regularity, this yields an actual forward global solution.
The multiplier is unrestricted: it vanishes from the inequality on the zero
set. No search algorithm or converse completeness statement is asserted.

This combines polynomial identity soundness with the regular-boundary criterion
of Ghorbal–Sogokon–Platzer, §5.3,
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf, and compact continuation
as in Teschl, *Ordinary Differential Equations and Dynamical Systems*, §2.6,
Corollaries 2.15–2.16, https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf.
-/

@[expose] public section

open Set
namespace MvPolynomial

/-- Let `F` be a real polynomial vector field in finitely many variables and
`p` a polynomial with compact sublevel `{x | eval x p ≤ 0}` and nonzero
evaluated gradient on its entire zero set. If
`-mkDerivation ℝ F p = s₀ + r * p` with `IsSumSq s₀`, then through every
initial point with `eval x₀ p ≤ 0` at any time `a` there is a forward global
solution staying in this sublevel for all `t ≥ a`, with ordinary derivative
equal to the evaluated field, including at `a`. The multiplier `r` has no sign
restriction, and the boundary Lie derivative may be zero. -/
theorem exists_forward_solution_of_sos_boundary_identity {σ : Type*} [Finite σ]
    (F : σ → MvPolynomial σ ℝ) (p s₀ r : MvPolynomial σ ℝ)
    (hs₀ : IsSumSq s₀) (hid : -mkDerivation ℝ F p = s₀ + r * p)
    (hK : IsCompact {x | eval x p ≤ 0})
    (hreg : ∀ x, eval x p = 0 → ∃ i, eval x (pderiv i p) ≠ 0)
    (a : ℝ) {x₀ : σ → ℝ} (h₀ : eval x₀ p ≤ 0) :
    ∃ x : ℝ → σ → ℝ, x a = x₀ ∧ (∀ t ∈ Ici a, eval (x t) p ≤ 0) ∧
      ∀ t ∈ Ici a, HasDerivAt x (fun i => eval (x t) (F i)) t := by
  apply exists_forward_solution_of_compact_sublevel F p hK hreg _ a h₀
  intro x hx
  have hn := eval_nonneg_of_sos_identity (I := (∅ : Finset Unit)) (J := {()})
    (g := fun _ => (0 : MvPolynomial σ ℝ)) (h := fun _ => p)
    (s := fun _ => (0 : MvPolynomial σ ℝ)) (r := fun _ => r)
    hs₀ (by simp) (by simpa using hid)
    (x := x) (by simp [basicClosedSet, hx])
  simpa only [map_neg, neg_nonneg] using hn
end MvPolynomial
