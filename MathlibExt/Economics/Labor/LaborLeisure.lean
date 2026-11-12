/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# Labor-leisure: compensated and uncompensated wage effects

A household with time endowment `T` and nonlabor income `N` faces wage `w`; its full income
is `w * T + N`, and Marshallian leisure demand `ℓ w M` depends on the wage (the price of
leisure) and full income. Holding `T` and `N` fixed, leisure along the wage is
`ℓ w (w * T + N)` and labor supply is `T` minus leisure.

Because full income moves with the wage, the uncompensated wage effect has an endowment term.
Given the consumer Slutsky identity for leisure, `s = ∂ℓ/∂w + (∂ℓ/∂M) ℓ` with `s` the
compensated (Hicksian) wage effect, the chain rule gives

* `dℓ/dw = s + L · ∂ℓ/∂M` (`leisureDemand_hasDerivAt`), and
* `dL/dw = -s - L · ∂ℓ/∂M` (`laborSupply_hasDerivAt`),

where `L = T - ℓ` is labor supply. With leisure normal the income effect opposes the
substitution effect, which allows a backward-bending labor-supply curve.

The Slutsky identity is a hypothesis here; it is the conclusion of the consumer Slutsky
equation (Atlas roadmap EC04.T04). Future unification: discharge it with that theorem once it
is on `main`. No interiority, normality, or participation assumption is made.

## Main results

* `MathlibExt.Economics.LaborLeisure.leisureDemand_hasDerivAt`
* `MathlibExt.Economics.LaborLeisure.laborSupply_hasDerivAt`

## References

* H. R. Varian, *Intermediate Microeconomics: A Modern Approach*, Chapter 9, "Buying and
  Selling" (the Slutsky equation with endowment income and labor supply).
* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 3.G (the Slutsky equation and compensated demand).

Atlas roadmap target AP04.T01.
-/

namespace MathlibExt.Economics.LaborLeisure

/-- Full income `w * T + N`: the market value at wage `w` of the time endowment `T`
plus nonlabor income `N`. This is the budget the household spends on consumption and
on leisure priced at the wage. -/
def fullIncome (T N w : ℝ) : ℝ :=
  w * T + N

/-- Marshallian (uncompensated) leisure demand along the wage, holding the time endowment
`T` and nonlabor income `N` fixed. Here `ℓ w M` is leisure demanded at wage (price of
leisure) `w` and full income `M`; because full income itself moves with the wage, the
wage enters twice. -/
def leisureDemand (ℓ : ℝ → ℝ → ℝ) (T N w : ℝ) : ℝ :=
  ℓ w (fullIncome T N w)

/-- Labor supply: the part of the time endowment `T` not consumed as leisure. -/
def laborSupply (ℓ : ℝ → ℝ → ℝ) (T N w : ℝ) : ℝ :=
  T - leisureDemand ℓ T N w

/-- **Labor-leisure Slutsky decomposition (leisure form).** Let `D` be the derivative of
Marshallian leisure demand `(w, M) ↦ ℓ w M` at `(w, fullIncome T N w)`, so `D (1, 0)` is the
own-wage effect at fixed full income and `D (0, 1)` is the full-income effect. Let `s` be the
compensated (Hicksian) wage derivative of leisure, related to `D` by the standard Slutsky
identity `s = D (1, 0) + D (0, 1) * ℓ` (the conclusion of the consumer Slutsky equation for the
good "leisure" at price `w`). Then the total, uncompensated wage effect on leisure, with `T`
and `N` fixed, is the substitution effect `s` plus the endowment-income effect
`(T - ℓ) * D (0, 1) = laborSupply * D (0, 1)`. -/
theorem leisureDemand_hasDerivAt {ℓ : ℝ → ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {T N w s : ℝ}
    (hℓ : HasFDerivAt (fun q : ℝ × ℝ => ℓ q.1 q.2) D (w, fullIncome T N w))
    (hslutsky : s = D (1, 0) + D (0, 1) * leisureDemand ℓ T N w) :
    HasDerivAt (leisureDemand ℓ T N) (s + laborSupply ℓ T N w * D (0, 1)) w := by
  have h1 : HasDerivAt id (1 : ℝ) w := hasDerivAt_id w
  have h2 : HasDerivAt (fun w : ℝ => w * T) (1 * T) w := HasDerivAt.mul_const h1 T
  have h3 : HasDerivAt (fun w : ℝ => w * T + N) (1 * T) w := HasDerivAt.add_const N h2
  have hlin : HasDerivAt (fun w : ℝ => w * T + N) T w := by simpa using h3
  have hlinF : HasFDerivAt (fun w : ℝ => w * T + N)
      (ContinuousLinearMap.toSpanSingleton ℝ T) w :=
    HasDerivAt.hasFDerivAt hlin
  have hid : HasFDerivAt id (ContinuousLinearMap.id ℝ ℝ) w := hasFDerivAt_id w
  have hinner : HasFDerivAt (fun w : ℝ => (w, fullIncome T N w))
      ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ T)) w :=
    HasFDerivAt.prodMk hid hlinF
  have hcomp : HasFDerivAt ((fun q : ℝ × ℝ => ℓ q.1 q.2) ∘ (fun w : ℝ => (w, fullIncome T N w)))
      (D ∘SL ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.toSpanSingleton ℝ T))) w :=
    HasFDerivAt.comp w hℓ hinner
  have hG1 : ((ContinuousLinearMap.id ℝ ℝ).prod
      (ContinuousLinearMap.toSpanSingleton ℝ T)) (1 : ℝ) = (1, T) := by
    simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  have hpair : ((1 : ℝ), T) = (1, 0) + T • ((0 : ℝ), 1) := by ext <;> simp
  have hval : (D ∘SL ((ContinuousLinearMap.id ℝ ℝ).prod
      (ContinuousLinearMap.toSpanSingleton ℝ T))) (1 : ℝ) = D (1, 0) + T * D (0, 1) := by
    have hc : (D ∘SL ((ContinuousLinearMap.id ℝ ℝ).prod
        (ContinuousLinearMap.toSpanSingleton ℝ T))) (1 : ℝ)
        = D (((ContinuousLinearMap.id ℝ ℝ).prod
        (ContinuousLinearMap.toSpanSingleton ℝ T)) (1 : ℝ)) := rfl
    rw [hc, hG1, hpair, map_add, map_smul, smul_eq_mul]
  have hderiv := HasFDerivAt.hasDerivAt hcomp
  rw [hval] at hderiv
  have hfun : (fun q : ℝ × ℝ => ℓ q.1 q.2) ∘ (fun w : ℝ => (w, fullIncome T N w))
      = leisureDemand ℓ T N := rfl
  rw [hfun] at hderiv
  have heq : s + laborSupply ℓ T N w * D (0, 1) = D (1, 0) + T * D (0, 1) := by
    rw [hslutsky]
    unfold laborSupply
    ring
  rw [heq]
  exact hderiv

/-- **Labor-supply Slutsky decomposition.** Under the hypotheses of
`leisureDemand_hasDerivAt`, the uncompensated wage effect on labor supply is the
compensated effect `-s` minus the income effect `laborSupply * D (0, 1)`. With leisure a
normal good (`0 < D (0, 1)`) and positive labor supply, the income effect works against the
substitution effect, which is the source of a backward-bending labor-supply curve. -/
theorem laborSupply_hasDerivAt {ℓ : ℝ → ℝ → ℝ} {D : ℝ × ℝ →L[ℝ] ℝ} {T N w s : ℝ}
    (hℓ : HasFDerivAt (fun q : ℝ × ℝ => ℓ q.1 q.2) D (w, fullIncome T N w))
    (hslutsky : s = D (1, 0) + D (0, 1) * leisureDemand ℓ T N w) :
    HasDerivAt (laborSupply ℓ T N) (-s - laborSupply ℓ T N w * D (0, 1)) w := by
  have hleisure := leisureDemand_hasDerivAt hℓ hslutsky
  have h := HasDerivAt.const_sub T hleisure
  have hfun : (fun x : ℝ => T - leisureDemand ℓ T N x) = laborSupply ℓ T N := rfl
  rw [hfun] at h
  have heq : -s - laborSupply ℓ T N w * D (0, 1)
      = -(s + laborSupply ℓ T N w * D (0, 1)) := by ring
  rw [heq]
  exact h

end MathlibExt.Economics.LaborLeisure
