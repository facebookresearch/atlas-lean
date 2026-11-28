/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The Dickman–de Bruijn function

This file defines a reusable predicate characterizing the Dickman–de Bruijn function on `ℝ`.
It records the standard zero extension to negative inputs, its range and continuity on
nonnegative inputs, its normalization on `[0, 1]`, and its delay differential equation above
one. Existence and uniqueness are proved separately in
`MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique`.

## References

* [Ofir Gorodetsky, *Rigidity of Averages over the Two Largest Prime
  Factors*](https://arxiv.org/abs/2608.05191)
* [Jared Duker Lichtman, *An improvement on the largest prime factors of consecutive
  integers*](https://arxiv.org/abs/2607.16032)
-/

@[expose] public section

namespace Real

/-- **Dickman–de Bruijn functions.** A function $\rho : \mathbb{R} \to \mathbb{R}$ is a
Dickman–de Bruijn function if $\rho(u) = 0$ for every real $u < 0$, $\rho$ maps $[0, \infty)$
into $[0, 1]$, $\rho$ is continuous on $[0, \infty)$, $\rho(u) = 1$ for every $u \in [0, 1]$,
and for every real $u > 1$ the function $\rho$ is differentiable at $u$ with
$u \rho'(u) + \rho(u - 1) = 0$.

These conditions describe the Dickman–de Bruijn function, extended by zero to negative inputs.
Continuity is asserted only on the original nonnegative domain, since the total zero extension
is discontinuous at zero. -/
def IsDickmanDeBruijn (ρ : ℝ → ℝ) : Prop :=
  (∀ u, u < 0 → ρ u = 0) ∧
    Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) ∧
    ContinuousOn ρ (Set.Ici (0 : ℝ)) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u, 1 < u → DifferentiableAt ℝ ρ u ∧ u * deriv ρ u + ρ (u - 1) = 0

/-- **The Dickman–de Bruijn function vanishes on the negative reals.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $\rho(u) = 0$ for every
real $u < 0$. -/
lemma IsDickmanDeBruijn.eq_zero_of_neg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : u < 0) : ρ u = 0 :=
  h.1 u hu

/-- **Range of the Dickman–de Bruijn function on the nonnegative reals.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $0 \le \rho(u) \le 1$
for every real $u \ge 0$. -/
lemma IsDickmanDeBruijn.mapsTo_Ici_Icc {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) :
    Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) :=
  h.2.1

/-- **Continuity of the Dickman–de Bruijn function on the nonnegative reals.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $\rho$ is continuous on
$[0, \infty)$. -/
lemma IsDickmanDeBruijn.continuousOn_Ici {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) : ContinuousOn ρ (Set.Ici (0 : ℝ)) :=
  h.2.2.1

/-- **The Dickman–de Bruijn function equals one on the unit interval.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $\rho(u) = 1$ for every
$u \in [0, 1]$. -/
lemma IsDickmanDeBruijn.eq_one_of_mem_Icc {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : ρ u = 1 :=
  h.2.2.2.1 u hu

/-- **Normalization of the Dickman–de Bruijn function, inequality form.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function and $u$ is a real number with
$0 \le u$ and $u \le 1$, then $\rho(u) = 1$. -/
lemma IsDickmanDeBruijn.eq_one_of_nonneg_of_le_one {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : ρ u = 1 :=
  h.eq_one_of_mem_Icc ⟨h0, h1⟩

/-- **Differentiability of the Dickman–de Bruijn function above one.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $\rho$ is differentiable
at every real $u > 1$. -/
lemma IsDickmanDeBruijn.differentiableAt_of_one_lt {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 1 < u) : DifferentiableAt ℝ ρ u :=
  (h.2.2.2.2 u hu).1

/-- **Delay differential equation of the Dickman–de Bruijn function.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then
$u \rho'(u) + \rho(u - 1) = 0$ for every real $u > 1$. -/
lemma IsDickmanDeBruijn.delay_eq {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 1 < u) :
    u * deriv ρ u + ρ (u - 1) = 0 :=
  (h.2.2.2.2 u hu).2

/-- **Nonnegativity of the Dickman–de Bruijn function.** If $\rho : \mathbb{R} \to \mathbb{R}$
is a Dickman–de Bruijn function, then $\rho(u) \ge 0$ for every real $u \ge 0$. -/
lemma IsDickmanDeBruijn.nonneg_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ρ u :=
  (h.mapsTo_Ici_Icc hu).1

/-- **Upper bound one for the Dickman–de Bruijn function on the nonnegative reals.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function, then $\rho(u) \le 1$
for every real $u \ge 0$. -/
lemma IsDickmanDeBruijn.le_one_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : ρ u ≤ 1 :=
  (h.mapsTo_Ici_Icc hu).2

/-- **Pointwise range bound for the Dickman–de Bruijn function.** If
$\rho : \mathbb{R} \to \mathbb{R}$ is a Dickman–de Bruijn function and $u \ge 0$ is real, then
$\rho(u) \in [0, 1]$. -/
lemma IsDickmanDeBruijn.mem_Icc_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : ρ u ∈ Set.Icc (0 : ℝ) 1 :=
  h.mapsTo_Ici_Icc hu

end Real
