/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPP
import MathlibExt.Analysis.ODE.PlanarShooting.Lemma
import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion

/-!
# Existence of logistic Fisher–KPP traveling fronts at every speed `c ≥ 2 √(r D)`

This file proves the existence half of the Kolmogorov–Petrovsky–Piskunov theorem for the
logistic reaction `f(u) = r u (1 - u)`, including the minimal speed `c = 2 √(r D)`.

## Front convention (frozen)

This is the convention of `FisherKPP.IsFront` (and of the former Wanted contract
`exists_isFront_of_le`), and every statement here uses it unchanged:

* PDE: `∂u/∂t = D ∂²u/∂x² + r u (1 - u)` with `D > 0`, `r > 0`.
* Traveling coordinate: `u(x, t) = U(z)` with `z = x - c t`, so a positive speed `c` moves the
  front towards `x = +∞`.
* Profile equation: `D U'' + c U' + r U (1 - U) = 0`, encoded as
  `MathlibExt.Biology.Dynamics.FisherKPP.IsWaveProfile D r c U U'`, where the second function
  `U'` is the derivative of `U` and `U'' = (-(c U') - r U (1 - U)) / D`.
* Front: `MathlibExt.Biology.Dynamics.FisherKPP.IsFront D r c U U'`, that is a wave profile with
  `0 < U < 1` everywhere, `U → 1` (the invading stable state) as `z → -∞` and `U → 0` (the
  invaded unstable state) as `z → +∞`.
* Monotone front: `StrictAnti U`, a front that decreases strictly from `1` to `0`.
* Admissible speeds: `2 * √(r * D) ≤ c`. The minimal (critical) speed is `c = 2 √(r D)`, where
  the node `(0, 0)` of the phase plane is degenerate.

## Main results

* `exists_isFront_of_le`: **KPP existence.** For every `c ≥ 2 √(r D)` there is a strictly
  decreasing front of speed `c`. It discharges the former Wanted contract of the same name with
  the same hypotheses and conclusion.
* `exists_isFront_two_mul_sqrt`: the minimal-speed boundary `c = 2 √(r D)` itself.
* `exists_isFront_of_sq_le`: the same existence for nonnegative speeds with `4 r D ≤ c²`.

## Proof

Shooting in the phase plane `(U, U')`. `PlanarShooting.exists_unstableBranch` builds the
unstable branch of the saddle `(1, 0)` on `z < 0` from a convergent power series.
`PlanarShooting.exists_isFront_of_unstableBranch` continues it to a global solution that stays
in the trapping triangle `{0 < U < 1, -c U / (2 D) < U' < 0}`, which is forward invariant for
every `c ≥ 2 √(r D)`, the critical speed included, and shows that the solution converges to the
node `(0, 0)`. This file composes the two. The critical speed needs no limit of supercritical
fronts.

## Scope

Only the logistic reaction is treated. Minimal speeds for general monostable reactions are not
stated. Uniqueness of the front up to translation and the converse (no front for
`0 ≤ c < 2 √(r D)`, see `FisherKPP.not_isFront_of_sq_lt`) are not combined here.

## References

* A. Kolmogorov, I. Petrovsky and N. Piskunov, *Étude de l'équation de la diffusion avec
  croissance de la quantité de matière et son application à un problème biologique*, Bull.
  Univ. État Moscou Sér. Int. A 1 (1937), 1–26.
* R. A. Fisher, *The wave of advance of advantageous genes*, Ann. Eugenics 7 (1937), 355–369.
* J. D. Murray, *Mathematical Biology I: An Introduction*, 3rd ed., Springer, 2002, §13.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Dynamics.FisherKPP

open Real

/-- **Kolmogorov–Petrovsky–Piskunov: fronts exist at every speed `c ≥ 2 √(r D)`**, and they are
strictly decreasing. For `D, r > 0` and `2 √(r D) ≤ c` there is a profile `U` with derivative
`U'` solving `D U'' + c U' + r U (1 - U) = 0`, with `0 < U < 1`, `U → 1` at `-∞`, `U → 0` at
`+∞`, and `U` strictly decreasing. -/
theorem exists_isFront_of_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r)
    (hc : 2 * √(r * D) ≤ c) : ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U := by
  obtain ⟨U, V, hode, hq, hU, hV, -⟩ :=
    MathlibExt.Analysis.ODE.PlanarShooting.exists_unstableBranch hD hr c
  exact MathlibExt.Analysis.ODE.PlanarShooting.exists_isFront_of_unstableBranch hD hr hc
    ⟨U, V, hode, hq, hU, hV⟩

/-- **The minimal-speed front.** At the critical speed `c = 2 √(r D)` a strictly decreasing
front exists. -/
theorem exists_isFront_two_mul_sqrt {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    ∃ U U' : ℝ → ℝ, IsFront D r (2 * √(r * D)) U U' ∧ StrictAnti U :=
  exists_isFront_of_le hD hr le_rfl

/-- **KPP existence, squared form.** For a nonnegative speed with `4 r D ≤ c²` a strictly
decreasing front exists. -/
theorem exists_isFront_of_sq_le {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 ≤ c)
    (hc : 4 * r * D ≤ c ^ 2) : ∃ U U' : ℝ → ℝ, IsFront D r c U U' ∧ StrictAnti U := by
  refine exists_isFront_of_le hD hr ?_
  have h : √(4 * (r * D)) ≤ c := by
    rw [Real.sqrt_le_left hc0]
    linarith
  rwa [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

end MathlibExt.Biology.Dynamics.FisherKPP
