/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Convergence stability and evolutionary stability of singular strategies

In adaptive dynamics with one-dimensional strategies, `s x y` is the invasion fitness of a rare
mutant `y` in a resident population `x`, with `s x x = 0` (Geritz, Kisdi, Meszéna and Metz
1998). The local fitness gradient is `D(x) = ∂s/∂y (x, x)`, and `x*` is singular when
`D(x*) = 0`. With second partial derivatives `s_xx, s_xy, s_yy` at `(x*, x*)`: `x*` is
ESS-stable when `s_yy < 0`; convergence-stable when `D'(x*) = s_xy + s_yy < 0` (Eshel 1983),
equivalently `s_xx > s_yy` because `s_xx + 2 s_xy + s_yy = 0` on the diagonal; it can invade
nearby residents when `s_xx > 0`; and nearby strategies on opposite sides are mutually invasible
when `s_xx + s_yy > 0`. A continuously stable strategy (Eshel and Motro 1981; Eshel 1983) is
both ESS-stable and convergence-stable; an evolutionary branching point is convergence-stable
but not ESS-stable. The statements below are the local, generic (strict-inequality) cases,
for invasion fitness of class `C²`.

Sources: S. A. H. Geritz, É. Kisdi, G. Meszéna and J. A. J. Metz, "Evolutionarily singular
strategies and the adaptive growth and branching of the evolutionary tree", Evol. Ecol. 12
(1998) 35–57, eqs. (1)–(11), Table 1; I. Eshel, "Evolutionary and continuous stability",
J. Theor. Biol. 103 (1983) 99–111.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

namespace WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

/-- The **local fitness gradient** `D(x) = ∂s/∂y (x, y)` at `y = x`. -/
noncomputable def fitnessGradient (s : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun y => s x y) x

/-- The second partial derivative `∂²s/∂x²` (resident variable) at `(a, b)`. -/
noncomputable def sxx (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun x => deriv (fun x' => s x' b) x) a

/-- The mixed second partial derivative `∂²s/∂x∂y` at `(a, b)`. -/
noncomputable def sxy (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => s x y) b) a

/-- The second partial derivative `∂²s/∂y²` (mutant variable) at `(a, b)`. -/
noncomputable def syy (s : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun y => deriv (fun y' => s a y') y) b

/-- Standing hypotheses on an **invasion fitness** with a singular strategy `x*`: `s` is `C²` as
a function of `(x, y)`, `s x x = 0` for every `x`, and `D(x*) = 0`. -/
structure IsSingular (s : ℝ → ℝ → ℝ) (xs : ℝ) : Prop where
  contDiff : ContDiff ℝ 2 (fun p : ℝ × ℝ => s p.1 p.2)
  diag : ∀ x, s x x = 0
  gradient_eq_zero : fitnessGradient s xs = 0

/-- **Diagonal identity and the derivative of the fitness gradient** (Geritz et al. 1998,
eq. (7)). For an invasion fitness `s` with singular strategy `x*` (`s` is `C²`, `s x x = 0`,
`D(x*) = 0`): `s_xx + 2 s_xy + s_yy = 0` at `(x*, x*)`, and `D` has derivative `s_xy + s_yy` at
`x*`.

Source: Geritz et al. (1998), eq. (7). -/
public theorem_wanted diagonal_identity_and_hasDerivAt {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (h : IsSingular s xs) :
    sxx s xs xs + 2 * sxy s xs xs + syy s xs xs = 0 ∧
      HasDerivAt (fitnessGradient s) (sxy s xs xs + syy s xs xs) xs

/-- **Convergence stability** (Eshel 1983; Geritz et al. 1998, eq. (8)). For an invasion
fitness `s` with singular strategy `x*`: `s_xy + s_yy < 0` iff `s_yy < s_xx` (all at
`(x*, x*)`), and if `s_xy + s_yy < 0` then there is `δ > 0` such that every resident `x` with
`0 < |x - x*| < δ` has fitness gradient pointing towards `x*`: `(x* - x) D(x) > 0`.

Sources: Eshel (1983); Geritz et al. (1998), eq. (8). -/
public theorem_wanted convergenceStable_iff_and_gradient {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (h : IsSingular s xs) :
    (sxy s xs xs + syy s xs xs < 0 ↔ syy s xs xs < sxx s xs xs) ∧
      (sxy s xs xs + syy s xs xs < 0 →
        ∃ δ > 0, ∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * fitnessGradient s x)

/-- **ESS-stability** (Geritz et al. 1998, eq. (5)). For an invasion fitness `s` with singular
strategy `x*`: if `s_yy < 0` at `(x*, x*)`, there is `δ > 0` with `s x* y < 0` for every mutant
`y` with `0 < |y - x*| < δ`; if `s_yy > 0`, there is `δ > 0` with `s x* y > 0` for every such
`y`.

Source: Geritz et al. (1998), eq. (5). -/
public theorem_wanted isLocalESS_iff {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs) :
    (syy s xs xs < 0 → ∃ δ > 0, ∀ y, 0 < |y - xs| → |y - xs| < δ → s xs y < 0) ∧
      (0 < syy s xs xs → ∃ δ > 0, ∀ y, 0 < |y - xs| → |y - xs| < δ → 0 < s xs y)

/-- **Invasion potential** (Geritz et al. 1998, eq. (9)). For an invasion fitness `s` with
singular strategy `x*`: if `s_xx > 0` at `(x*, x*)`, there is `δ > 0` such that `x*` invades
every resident `x` with `0 < |x - x*| < δ`: `s x x* > 0`.

Source: Geritz et al. (1998), eq. (9). -/
public theorem_wanted invades_nearby_residents {s : ℝ → ℝ → ℝ} {xs : ℝ}
    (h : IsSingular s xs) (hxx : 0 < sxx s xs xs) :
    ∃ δ > 0, ∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < s x xs

/-- **Mutual invasibility** (Geritz et al. 1998, eq. (11)). For an invasion fitness `s` with
singular strategy `x*`: if `s_xx + s_yy > 0` at `(x*, x*)`, there is `δ > 0` such that for
every `h` with `0 < h < δ` the strategies `x* - h` and `x* + h` invade each other; if
`s_xx + s_yy < 0`, there is `δ > 0` such that no two distinct strategies within `δ` of `x*`
invade each other.

Source: Geritz et al. (1998), eq. (11). -/
public theorem_wanted mutual_invasibility {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs) :
    (0 < sxx s xs xs + syy s xs xs → ∃ δ > 0, ∀ e, 0 < e → e < δ →
        0 < s (xs - e) (xs + e) ∧ 0 < s (xs + e) (xs - e)) ∧
      (sxx s xs xs + syy s xs xs < 0 → ∃ δ > 0, ∀ x y, |x - xs| < δ → |y - xs| < δ →
        x ≠ y → ¬ (0 < s x y ∧ 0 < s y x))

/-- **Evolutionary branching point** (Geritz et al. 1998, Table 1). For an invasion fitness `s`
with singular strategy `x*` that is convergence-stable (`s_xy + s_yy < 0`) but not ESS-stable
(`s_yy > 0`): there is `δ > 0` such that every resident `x` with `0 < |x - x*| < δ` has
`(x* - x) D(x) > 0`, every mutant `y` with `0 < |y - x*| < δ` invades `x*` (`s x* y > 0`), and
for every `e` with `0 < e < δ` the strategies `x* - e` and `x* + e` invade each other.

Source: Geritz et al. (1998), Table 1 and Fig. 2. -/
public theorem_wanted branchingPoint {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs)
    (hconv : sxy s xs xs + syy s xs xs < 0) (hyy : 0 < syy s xs xs) :
    ∃ δ > 0, (∀ x, 0 < |x - xs| → |x - xs| < δ → 0 < (xs - x) * fitnessGradient s x) ∧
      (∀ y, 0 < |y - xs| → |y - xs| < δ → 0 < s xs y) ∧
      ∀ e, 0 < e → e < δ → 0 < s (xs - e) (xs + e) ∧ 0 < s (xs + e) (xs - e)

end WantedExt.Biology.Ecology.SingularStrategyClassificationWanted
