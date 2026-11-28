/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Helfrich sphere condition and the Ou-Yang–Helfrich critical pressure

For a closed lipid vesicle with the Helfrich free energy `F = ∫ G_H dA + p ∫ dV`,
`G_H = (k_c/2)(2H + c₀)² - k̄ K + λ` (bending modulus `k_c`, spontaneous curvature `c₀`, surface
tension `λ`, pressure difference `p`, mean curvature `H`, Gaussian curvature `K`), equilibrium
shapes satisfy the shape equation (Ou-Yang and Helfrich 1987)

  `p - 2λH + k_c (2H + c₀)(2H² - c₀ H - 2K) + 2 k_c ∇²H = 0`,

with the orientation in which a round sphere of radius `R` has `H = -1/R` and `K = 1/R²`. A sphere
of radius `R` therefore satisfies it iff `p R² + 2λR - k_c c₀ (2 - c₀ R) = 0`. For a normal
displacement `Ω₃ = ∑_{l,m} a_{lm} Y_{lm}` of such a sphere the second variation is
(Tu and Ou-Yang 2008, after Ou-Yang and Helfrich 1987)

  `δ²F = ∑_{l,m} |a_{lm}|² q_l(p)`,  `q_l(p) = (R/2)[l(l+1) - 2]{2k_c [l(l+1) - c₀R]/R³ - p}`,

from which the critical pressure is `p_c = 2k_c(6 - c₀R)/R³`.

Here the shape equation is recorded through its left-hand side as a function of `H`, `K` and
`∇²H`, and the second variation through its mode formula, both as printed; the perturbations are
finite expansions. The admissible class is linearized volume preservation, `a_{00} = 0`. With
`k_c > 0` and `R > 0`: `δ²F ≥ 0` on the admissible class iff `p ≤ p_c` (the `l = 2` modes are
neutral at `p = p_c`); excluding the `l = 1` modes (rigid translations), `δ²F > 0` on nonzero
admissible perturbations iff `p < p_c`; and the `l = 0` coefficient is `q_0 = R(p + 2k_c c₀/R²)`,
nonnegative iff `p ≥ p_c - 12k_c/R³`, so the source's "for any `a_{lm}`" needs the `l = 0`
restriction. Not recorded here: the derivation of the shape equation as the first variation of
`F` and of the mode formula from the general second variation, which need the calculus of
variations for curvature functionals of closed surfaces in `ℝ³`; and any nonlinear stability.

Sources: Z.-C. Ou-Yang and W. Helfrich, "Instability and deformation of a spherical vesicle by
pressure", Physical Review Letters 59 (1987) 2486–2488, doi:10.1103/PhysRevLett.59.2486;
Z. C. Tu and Z. C. Ou-Yang, "Elastic theory of low-dimensional continua and its applications in
bio- and nano-structures", Journal of Computational and Theoretical Nanoscience 5 (2008) 422–448,
arXiv:0706.0001, the shape equation, the sphere condition, the second
variation on the sphere and the critical pressure.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Biophysics.HelfrichSphereStability
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace WantedExt.Biology.Biophysics.HelfrichSphereStabilityWanted

/-- The left-hand side of the **Helfrich shape equation**
`p - 2λH + k_c (2H + c₀)(2H² - c₀ H - 2K) + 2 k_c ∇²H` at a point with mean curvature `H`,
Gaussian curvature `K` and `∇²H = lapH`. -/
def shapeLHS (p lam kc c₀ H K lapH : ℝ) : ℝ :=
  p - 2 * lam * H + kc * (2 * H + c₀) * (2 * H ^ 2 - c₀ * H - 2 * K) + 2 * kc * lapH

/-- The second variation `δ²F = ∑_{l < L} ∑_{|m| ≤ l} |a_{lm}|² q_l(p)` of the finite expansion
with coefficients `a l m` (`m` ranging over `2l + 1` values). -/
noncomputable def secondVariation (kc c₀ R p : ℝ) (L : ℕ) (a : (l : ℕ) → Fin (2 * l + 1) → ℂ) :
    ℝ :=
  ∑ l ∈ Finset.range L, ∑ m : Fin (2 * l + 1), ‖a l m‖ ^ 2 * modeCoeff kc c₀ R p l

/-- **The sphere condition** (Ou-Yang and Helfrich 1987; Tu and Ou-Yang 2008): for `R > 0`, the
round sphere of radius `R` (`H = -1/R`, `K = 1/R²`, `∇²H = 0`) satisfies the shape equation iff
`p R² + 2λR - k_c c₀ (2 - c₀ R) = 0`.

Source: Tu and Ou-Yang (2008), sphere condition; Ou-Yang and Helfrich (1987). -/
public theorem_wanted shapeLHS_sphere_eq_zero_iff (p lam kc c₀ R : ℝ) (hR : 0 < R) :
    shapeLHS p lam kc c₀ (-1 / R) (1 / R ^ 2) 0 = 0 ↔
      p * R ^ 2 + 2 * lam * R - kc * c₀ * (2 - c₀ * R) = 0

/-- **Semidefinite stability criterion** (Ou-Yang and Helfrich 1987; Tu and Ou-Yang 2008): for
`k_c > 0` and `R > 0`, the second variation is nonnegative on every finite expansion with
`a_{00} = 0` (linearized volume preservation) iff `p ≤ p_c = 2k_c(6 - c₀R)/R³`.

Source: Tu and Ou-Yang (2008), critical pressure; Ou-Yang and Helfrich (1987). -/
public theorem_wanted secondVariation_nonneg_iff (kc c₀ R p : ℝ) (hkc : 0 < kc) (hR : 0 < R) :
    (∀ (L : ℕ) (a : (l : ℕ) → Fin (2 * l + 1) → ℂ), a 0 0 = 0 →
        0 ≤ secondVariation kc c₀ R p L a) ↔ p ≤ criticalPressure kc c₀ R

/-- **Strict stability criterion** (Ou-Yang and Helfrich 1987; Tu and Ou-Yang 2008, with the
translations excluded): for `k_c > 0` and `R > 0`, the second variation is positive on every
finite expansion with `a_{00} = 0`, all `l = 1` coefficients zero, and some coefficient `a_{lm}`
with `l < L` nonzero, iff `p < p_c`.

Source: Tu and Ou-Yang (2008), critical pressure; Ou-Yang and Helfrich (1987). -/
public theorem_wanted secondVariation_pos_iff (kc c₀ R p : ℝ) (hkc : 0 < kc) (hR : 0 < R) :
    (∀ (L : ℕ) (a : (l : ℕ) → Fin (2 * l + 1) → ℂ), a 0 0 = 0 → (∀ m, a 1 m = 0) →
        (∃ l < L, ∃ m, a l m ≠ 0) → 0 < secondVariation kc c₀ R p L a) ↔
      p < criticalPressure kc c₀ R

end WantedExt.Biology.Biophysics.HelfrichSphereStabilityWanted
