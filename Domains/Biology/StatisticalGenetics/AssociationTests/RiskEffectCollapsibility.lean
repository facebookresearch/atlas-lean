/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Collapsibility of risk differences and risk ratios

For a nonnegative joint mass function of binary treatment, response and covariate with total
mass $1$, suppose treatment and covariate are independent, every treatment–covariate cell has
positive mass, and the crude control risk is positive. Then each crude risk is the mixture of
its stratum risks with weights from the marginal covariate distribution. The risk ratio
standardized to those weights equals the crude risk ratio. This gives a sufficient condition for
the observed-data equality illustrated in Table 1; it does not assert causal exchangeability.

For a weight $q \in [0,1]$ and real stratum risks $r(x,z)$, a common-weight mixture of the two
strata preserves an additive or multiplicative relation between the treatment and control risks
when that relation holds in both strata.

## References

* Sander Greenland, James M. Robins and Judea Pearl, *Confounding and Collapsibility in Causal
  Inference*, Statistical Science **14** (1), 1999, pp. 29–46, §4.1, pp. 37–38 and Table 1.
-/

public section

namespace WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted

@[expose] section

/-- The marginal mass `P(X = x)` of a joint mass function `p x y z` of binary `X, Y, Z`. -/
def massX (p : Bool → Bool → Bool → ℝ) (x : Bool) : ℝ :=
  ∑ y, ∑ z, p x y z

/-- The marginal mass `P(Z = z)`. -/
def massZ (p : Bool → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  ∑ x, ∑ y, p x y z

/-- The joint mass `P(X = x, Z = z)`. -/
def massXZ (p : Bool → Bool → Bool → ℝ) (x z : Bool) : ℝ :=
  ∑ y, p x y z

/-- The crude risk `P(Y = 1 | X = x)`. It is meaningful when `P(X = x) > 0`; if `P(X = x) = 0`,
Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def crudeRisk (p : Bool → Bool → Bool → ℝ) (x : Bool) : ℝ :=
  (∑ z, p x true z) / massX p x

/-- The stratum risk `P(Y = 1 | X = x, Z = z)`. It is meaningful when `P(X = x, Z = z) > 0`; if that
mass is `0`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def stratumRisk (p : Bool → Bool → Bool → ℝ) (x z : Bool) : ℝ :=
  p x true z / massXZ p x z

end

/-- **Common-weight mixture identity under `X ⊥ Z`** (Greenland, Robins and Pearl 1999, p. 38).
Let `p x y z ≥ 0` be a joint mass function of binary `X, Y, Z` with total mass `1`, with observed
independence `X ⊥ Z` (`P(X = x, Z = z) = P(X = x) P(Z = z)` for all `x, z`) and
`P(X = x, Z = z) > 0` for all `x, z`, and suppose the crude risk for `X = 0` is positive,
`P(Y = 1 | X = 0) > 0`. Then for each `x`,
`P(Y = 1 | X = x) = ∑_z P(Z = z) P(Y = 1 | X = x, Z = z)` (a common-weight mixture over `Z`), and
the risk ratio standardized to `P(Z)`,
`∑_z P(z) P(Y = 1 | 1, z) / ∑_z P(z) P(Y = 1 | 0, z)`, equals the crude risk ratio
`P(Y = 1 | X = 1) / P(Y = 1 | X = 0)` (an observed-data identity; causal exchangeability is not
assumed or implied). By the mixture identity both denominators equal `P(Y = 1 | X = 0)`, so
neither is zero.

Source: Greenland, Robins and Pearl (1999), pp. 37–38. -/
public theorem crudeRisk_eq_mixture (p : Bool → Bool → Bool → ℝ) (hp : ∀ x y z, 0 ≤ p x y z)
    (hsum : ∑ x, ∑ y, ∑ z, p x y z = 1) (hind : ∀ x z, massXZ p x z = massX p x * massZ p z)
    (hpos : ∀ x z, 0 < massXZ p x z) (hrisk : 0 < crudeRisk p false) :
    (∀ x, crudeRisk p x = ∑ z, massZ p z * stratumRisk p x z) ∧
      (∑ z, massZ p z * stratumRisk p true z) / (∑ z, massZ p z * stratumRisk p false z) =
        crudeRisk p true / crudeRisk p false := by
  -- Nonnegativity and normalization make `p` a mass function; `hrisk` makes the ratio meaningful.
  -- The equalities themselves only use the factorization and nonzero cell masses.
  have _ := hp
  have _ := hsum
  have _ := hrisk
  have hmix (x : Bool) : crudeRisk p x = ∑ z, massZ p z * stratumRisk p x z := by
    rw [crudeRisk, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    have hne : massX p x * massZ p z ≠ 0 := hind x z ▸ (hpos x z).ne'
    have hz : massZ p z ≠ 0 := (mul_ne_zero_iff.mp hne).2
    rw [stratumRisk, hind x z, ← div_div, ← mul_div_assoc, mul_div_cancel_left₀ _ hz]
  exact ⟨hmix, by rw [← hmix true, ← hmix false]⟩

/-- **Constant risk differences and risk ratios collapse** (Greenland, Robins and Pearl 1999,
pp. 37–38). Let `q ∈ [0, 1]` be `P(Z = 1)`, let `r x z` be the risk of response given `X = x`
and `Z = z`, and let `m x = q r(x, 1) + (1 - q) r(x, 0)` be the marginal risk (the mixture that
holds when `X` is independent of `Z`). If `r(1, z) - r(0, z) = δ` for both `z`, then
`m 1 - m 0 = δ`; if `r(1, z) = ρ r(0, z)` for both `z`, then `m 1 = ρ m 0`.

Source: Greenland, Robins and Pearl (1999), pp. 37–38, Table 1. -/
public theorem riskDifference_riskRatio_collapse (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (r : Bool → Bool → ℝ) (δ ρ : ℝ) :
    ((∀ z, r true z - r false z = δ) →
        (q * r true true + (1 - q) * r true false) -
          (q * r false true + (1 - q) * r false false) = δ) ∧
      ((∀ z, r true z = ρ * r false z) →
        q * r true true + (1 - q) * r true false =
          ρ * (q * r false true + (1 - q) * r false false)) := by
  -- The bounds describe a mixture weight; the algebraic identities hold without them.
  have _hq : 0 ≤ q ∧ q ≤ 1 := ⟨hq₀, hq₁⟩
  constructor
  · intro h
    linear_combination q * h true + (1 - q) * h false
  · intro h
    rw [h true, h false]
    ring

end WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted
