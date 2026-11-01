/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of Fisher–KPP traveling fronts at every speed `c ≥ 2 √(r D)`

For the Fisher–KPP equation `∂u/∂t = D ∂²u/∂x² + r u (1 - u)` with `D, r > 0`, a front of speed
`c` is a profile `U` with `D U'' + c U' + r U (1 - U) = 0`, `0 < U < 1`, `U → 1` at `-∞` and
`U → 0` at `+∞` (`IsFront` in `MathlibExt.Biology.Dynamics.FisherKPP`).

**Kolmogorov–Petrovsky–Piskunov theorem (existence part).** For every `c ≥ 2 √(r D)` there is a
front of speed `c`, and it is strictly decreasing. Together with
`MathlibExt.Biology.Dynamics.FisherKPP.not_isFront_of_sq_lt` (no front when `c² < 4 r D`), this
makes `2 √(r D)` the minimal front speed. The classical proof is a phase-plane argument: in the
`(U, U')` plane the saddle `(1, 0)` has an unstable manifold that enters the triangular trapping
region `{0 ≤ U ≤ 1, -μ U ≤ U' ≤ 0}` with `μ = c / (2D)`, which it can leave only through the
stable node (or degenerate node at `c = 2 √(r D)`) `(0, 0)`. Uniqueness of the front up to
translation is also classical and is not stated here.

Sources: A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
croissance de la quantité de matière et son application à un problème biologique*, Bull. Univ.
État Moscou Sér. Int. A 1 (1937), 1–26; R. A. Fisher, *The wave of advance of advantageous genes*,
Ann. Eugenics 7 (1937), 355–369; J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed.,
Springer, 2002, Section 13.2.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.Dynamics.FisherKPP

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Dynamics.FisherKPP

/-- **Kolmogorov–Petrovsky–Piskunov: fronts exist at every speed `c ≥ 2 √(r D)`**, and they are
strictly decreasing. -/
theorem_wanted exists_isFront_of_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) : ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U

end MathlibExt.Biology.Dynamics.FisherKPP
