/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wanted: flux balance value function and balancing with total support

Statements complementing `MathlibExt.Biology.Dynamics.SystemsBiology`.

* Flux balance analysis (Orth, Thiele & Palsson 2010). For the linear program
  `max cᵀv` subject to `S v = b`, `l ≤ v ≤ u` (`fbaValue S l u c b`), the optimal value is a
  concave piecewise-linear function of `b` on the feasible right-hand sides: it is the minimum of
  finitely many affine functions `b ↦ y ⬝ᵥ b + κ` (the dual objective at the vertices of the dual
  polyhedron). At an interior feasible `b` with a unique optimal metabolite price vector `y`, the
  optimal value is differentiable with gradient `y` (for a concave function the superdifferential
  at an interior point is a singleton exactly when it is differentiable there; the
  superdifferential is the set of optimal prices by `exists_optimal_dual_iff_supergradient`).
* Symmetric matrix balancing (Csima & Datta 1972). A symmetric nonnegative matrix with total
  support has a positive vector `d` with `diag(d) A diag(d)` doubly stochastic. The converse is
  `hasTotalSupport_of_balancing`.

Sources: J. D. Orth, I. Thiele, B. Ø. Palsson, "What is flux balance analysis?", Nat.
Biotechnol. 28 (2010) 245–248; R. T. Rockafellar, *Convex Analysis*, Princeton (1970),
Thm 19.3 and Thm 25.1; J. Csima and B. N. Datta, "The DAD theorem for symmetric non-negative
matrices", J. Combin. Theory Ser. A 12 (1972) 147–152; R. Sinkhorn and P. Knopp, "Concerning
nonnegative matrices and doubly stochastic matrices", Pacific J. Math. 21 (1967) 343–348.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.Dynamics.SystemsBiology

@[expose] public section

namespace MathlibExt.Biology.Dynamics.SystemsBiology

open Matrix

variable {m n : ℕ}

/-- **The FBA value is piecewise linear.** There are finitely many affine functions
`b ↦ y ⬝ᵥ b + κ` whose minimum is the optimal value at every feasible right-hand side `b`.

Source: Rockafellar (1970), Thm 19.3; Orth, Thiele & Palsson (2010). -/
theorem_wanted exists_finset_isLeast_fbaValue (S : Matrix (Fin m) (Fin n) ℝ)
    (l u c : Fin n → ℝ) :
    ∃ T : Finset ((Fin m → ℝ) × ℝ), ∀ b : Fin m → ℝ, (fbaFeasible S l u b).Nonempty →
      IsLeast ((fun p : (Fin m → ℝ) × ℝ => p.1 ⬝ᵥ b + p.2) '' (T : Set _))
        (fbaValue S l u c b)

/-- **Shadow prices are derivatives when unique.** If `b` is an interior point of the set of
feasible right-hand sides and `y` is the only metabolite price vector of an optimal dual
solution, then the optimal value is differentiable at `b` with derivative `b' ↦ y ⬝ᵥ b'`.

Source: Rockafellar (1970), Thm 25.1; Orth, Thiele & Palsson (2010). -/
theorem_wanted hasFDerivAt_fbaValue_of_unique {S : Matrix (Fin m) (Fin n) ℝ}
    {l u c : Fin n → ℝ} {b : Fin m → ℝ}
    (hb : b ∈ interior {b' : Fin m → ℝ | (fbaFeasible S l u b').Nonempty}) {y : Fin m → ℝ}
    (huniq : ∀ y' : Fin m → ℝ, (∃ α β, fbaDualFeasible S c y' α β ∧
        ∀ y'' α'' β'', fbaDualFeasible S c y'' α'' β'' →
          fbaDualValue l u b y' α β ≤ fbaDualValue l u b y'' α'' β'') ↔ y' = y) :
    HasFDerivAt (fbaValue S l u c)
      (∑ i, y i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) b

/-- **Csima–Datta: sufficiency of total support.** A symmetric nonnegative matrix with total
support has a positive vector `d` with `diag(d) A diag(d)` doubly stochastic.

Source: Csima & Datta (1972); Sinkhorn & Knopp (1967). -/
theorem_wanted exists_symmetric_balancing_of_hasTotalSupport {A : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : A.IsSymm) (hA : ∀ i j, 0 ≤ A i j) (hts : HasTotalSupport A) :
    ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧
      (fun i j => d i * A i j * d j) ∈ doublyStochastic ℝ (Fin n)

end MathlibExt.Biology.Dynamics.SystemsBiology
