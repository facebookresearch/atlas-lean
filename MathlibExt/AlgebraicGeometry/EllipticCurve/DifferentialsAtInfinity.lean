/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Kähler differentials of the chart at infinity

Let `W` be a Weierstrass curve over a commutative ring `R`, with chart at infinity
`B_W = R[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`
(`WeierstrassCurve.CoordinateRingAtInfinity`). Write

* `h_z = ∂h/∂z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²` (`WeierstrassCurve.polynomialAtInfinityZ`),
* `h_w = ∂h/∂w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`
  (`WeierstrassCurve.polynomialAtInfinityW`),

and `S = B_W[1 / h_w]` (`WeierstrassCurve.AwayPartialW`), the open part of the chart at infinity
where `h_w` is invertible. This file proves:

* `h_w(0, 0) = 1`, so the point at infinity `z = w = 0` lies in `Spec S`
  (`WeierstrassCurve.eval_zero_polynomialAtInfinityW`,
  `WeierstrassCurve.evalAtInfinity_partialWAtInfinity`);
* in `Ω¹_{B_W/R}`, the relation `h_z dz + h_w dw = 0` holds and `dz, dw` span
  (`WeierstrassCurve.relation_D_atInfinity`, `WeierstrassCurve.span_D_atInfinity`);
* in `Ω¹_{S/R}`, `dw = -(h_z / h_w) dz` (`WeierstrassCurve.D_wAtInfinity_awayPartialW`);
* `Ω¹_{S/R}` is a free `S`-module with basis `dz` (`WeierstrassCurve.basisAwayPartialW`), of
  rank one when `R` is nontrivial (`WeierstrassCurve.finrank_awayPartialW`).

No hypothesis on the discriminant is used, and `R` is any commutative ring (any field in
particular).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §6, p. 211.
* The Stacks project, Lemma 10.131.8, <https://stacks.math.columbia.edu/tag/00RT>.
-/

@[expose] public section

open MvPolynomial KaehlerDifferential

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The partial derivatives of the polynomial at infinity -/

/-- **The partial derivative `h_z`.** Let `W` be a Weierstrass curve over a commutative ring `R`.
This is the polynomial `h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²` in `R[z, w]`, the partial derivative
in `z` of `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`
(`pderiv_zero_polynomialAtInfinity`). Here `z` is the variable `0` and `w` the variable `1`. -/
noncomputable def polynomialAtInfinityZ : MvPolynomial (Fin 2) R :=
  C W.a₁ * X 1 - 3 * X 0 ^ 2 - 2 * C W.a₂ * X 0 * X 1 - C W.a₄ * X 1 ^ 2

/-- **The partial derivative `h_w`.** Let `W` be a Weierstrass curve over a commutative ring `R`.
This is the polynomial `h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²` in `R[z, w]`, the
partial derivative in `w` of `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`
(`pderiv_one_polynomialAtInfinity`). Here `z` is the variable `0` and `w` the variable `1`. -/
noncomputable def polynomialAtInfinityW : MvPolynomial (Fin 2) R :=
  1 + C W.a₁ * X 0 + 2 * C W.a₃ * X 1 - C W.a₂ * X 0 ^ 2 - 2 * C W.a₄ * X 0 * X 1 -
    3 * C W.a₆ * X 1 ^ 2

/-- **`∂h/∂z = h_z`.** Let `W` be a Weierstrass curve over a commutative ring `R`. The partial
derivative in `z` of `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` is
`h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²`. -/
theorem pderiv_zero_polynomialAtInfinity :
    pderiv 0 W.polynomialAtInfinity = W.polynomialAtInfinityZ := by
  simp [polynomialAtInfinity, polynomialAtInfinityZ, pderiv_X]
  ring

/-- **`∂h/∂w = h_w`.** Let `W` be a Weierstrass curve over a commutative ring `R`. The partial
derivative in `w` of `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³` is
`h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`. -/
theorem pderiv_one_polynomialAtInfinity :
    pderiv 1 W.polynomialAtInfinity = W.polynomialAtInfinityW := by
  simp [polynomialAtInfinity, polynomialAtInfinityW, pderiv_X]
  ring

/-- **The point at infinity lies on the chart.** Let `W` be a Weierstrass curve over a
commutative ring `R`. Then `h(0, 0) = 0` for
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. -/
theorem eval_zero_polynomialAtInfinity : eval 0 W.polynomialAtInfinity = 0 := by
  simp [polynomialAtInfinity]

/-- **`h_w` is `1` at the point at infinity.** Let `W` be a Weierstrass curve over a commutative
ring `R`. Then `h_w(0, 0) = 1` for `h_w = ∂h/∂w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`.

No hypothesis on the discriminant is needed. See also
`evalAtInfinity_partialWAtInfinity` for the same statement read in `B_W`. -/
theorem eval_zero_polynomialAtInfinityW : eval 0 W.polynomialAtInfinityW = 1 := by
  simp [polynomialAtInfinityW]

/-- The partial derivative `h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²`, as an element of `B_W`. -/
noncomputable def partialZAtInfinity : W.CoordinateRingAtInfinity :=
  Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) W.polynomialAtInfinityZ

/-- The partial derivative `h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`, as an element
of `B_W`. -/
noncomputable def partialWAtInfinity : W.CoordinateRingAtInfinity :=
  Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) W.polynomialAtInfinityW

/-- **`h_w` takes the value `1` at the point at infinity.** Let `W` be a Weierstrass curve over
a commutative ring `R`. The evaluation `B_W → R` at `z = w = 0` sends
`h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²` to `1`. In particular the point at
infinity `(0 : 1 : 0)` lies in the open set `h_w ≠ 0` of the chart at infinity.

No hypothesis on the discriminant is needed. -/
theorem evalAtInfinity_partialWAtInfinity :
    W.evalAtInfinity W.partialWAtInfinity = 1 := by
  simp [evalAtInfinity, partialWAtInfinity, polynomialAtInfinityW]

/-! ### Differentials of `B_W` -/

/-- A derivation on `R[z, w]` is determined by its values on `z` and `w`, through the partial
derivatives. -/
private lemma derivation_eq_pderiv {M : Type*} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial (Fin 2) R) M] [IsScalarTower R (MvPolynomial (Fin 2) R) M]
    (d : Derivation R (MvPolynomial (Fin 2) R) M) (p : MvPolynomial (Fin 2) R) :
    d p = pderiv 0 p • d (X 0) + pderiv 1 p • d (X 1) := by
  have e : d = (LinearMap.toSpanSingleton _ M (d (X 0))).compDer (pderiv 0) +
      (LinearMap.toSpanSingleton _ M (d (X 1))).compDer (pderiv 1) := by
    refine MvPolynomial.derivation_ext fun i ↦ ?_
    fin_cases i <;> simp [pderiv_X]
  conv_lhs => rw [e]
  rfl

/-- **The differential of a class in `B_W`.** Let `W` be a Weierstrass curve over a commutative
ring `R` and let `p ∈ R[z, w]`. In `Ω¹_{B_W/R}`, the class of `p` in `B_W` has differential

$$d\bar p = \overline{\partial_z p} \, dz + \overline{\partial_w p} \, dw.$$
-/
theorem D_mk_atInfinity (p : MvPolynomial (Fin 2) R) :
    D R W.CoordinateRingAtInfinity (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) p) =
      Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) (pderiv 0 p) •
          D R _ W.zAtInfinity +
        Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) (pderiv 1 p) •
          D R _ W.wAtInfinity := by
  have := derivation_eq_pderiv ((D R W.CoordinateRingAtInfinity).compAlgebraMap
    (MvPolynomial (Fin 2) R)) p
  simp only [Derivation.compAlgebraMap_apply, Ideal.Quotient.algebraMap_eq] at this
  rw [this, ← algebraMap_smul W.CoordinateRingAtInfinity (pderiv 0 p),
    ← algebraMap_smul W.CoordinateRingAtInfinity (pderiv 1 p)]
  rfl

/-- **The relation `h_z dz + h_w dw = 0`.** Let `W` be a Weierstrass curve over a commutative
ring `R`. In `Ω¹_{B_W/R}`,

$$h_z \, dz + h_w \, dw = 0,$$

with `h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²` and
`h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`
read in `B_W`: the differential of the equation `h = 0` of the chart at infinity. -/
theorem relation_D_atInfinity :
    W.partialZAtInfinity • D R _ W.zAtInfinity + W.partialWAtInfinity • D R _ W.wAtInfinity =
      0 := by
  have h : Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) W.polynomialAtInfinity = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have := W.D_mk_atInfinity W.polynomialAtInfinity
  rw [h, map_zero, pderiv_zero_polynomialAtInfinity, pderiv_one_polynomialAtInfinity] at this
  exact this.symm

/-- **`dz` and `dw` span `Ω¹_{B_W/R}`.** Let `W` be a Weierstrass curve over a commutative ring
`R`. The `B_W`-module `Ω¹_{B_W/R}` is spanned by `dz` and `dw`. -/
theorem span_D_atInfinity :
    Submodule.span W.CoordinateRingAtInfinity
      {D R _ W.zAtInfinity, D R _ W.wAtInfinity} = ⊤ := by
  rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [D_mk_atInfinity]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### Differentials of `S = B_W[1 / h_w]` -/

/-- **The chart at infinity where `h_w` is invertible.** Let `W` be a Weierstrass curve over a
commutative ring `R`. This is the localization `S = B_W[1 / h_w]` of the coordinate ring at
infinity `B_W` at `h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`. It contains the point
at infinity `z = w = 0` (`evalAtInfinity_partialWAtInfinity`). -/
abbrev AwayPartialW : Type _ := Localization.Away W.partialWAtInfinity

/-- **The differential of a class in `S`.** Let `W` be a Weierstrass curve over a commutative
ring `R`, let `p ∈ R[z, w]` and let `S = B_W[1 / h_w]`. In `Ω¹_{S/R}`, the image of `p` in `S`
has differential `∂_z p dz + ∂_w p dw`. -/
theorem D_algebraMap_mk_awayPartialW (p : MvPolynomial (Fin 2) R) :
    D R W.AwayPartialW
        (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) p)) =
      algebraMap _ W.AwayPartialW
          (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) (pderiv 0 p)) •
          D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity) +
        algebraMap _ W.AwayPartialW
          (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) (pderiv 1 p)) •
          D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity) := by
  rw [← map_D R R W.CoordinateRingAtInfinity, ← map_D R R W.CoordinateRingAtInfinity,
    ← map_D R R W.CoordinateRingAtInfinity, D_mk_atInfinity, map_add, map_smul, map_smul,
    algebraMap_smul, algebraMap_smul]

/-- **The relation `h_w dw = -h_z dz` in `Ω¹_S`.** Let `W` be a Weierstrass curve over a
commutative ring `R` and let `S = B_W[1 / h_w]`. In `Ω¹_{S/R}`,

$$h_w \, dw = -(h_z \, dz),$$

with `h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²` and
`h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`.

No hypothesis on the discriminant is needed. -/
theorem relation_D_awayPartialW :
    algebraMap _ W.AwayPartialW W.partialWAtInfinity •
        D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity) =
      -(algebraMap _ W.AwayPartialW W.partialZAtInfinity •
        D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity)) := by
  have := congrArg (KaehlerDifferential.map R R W.CoordinateRingAtInfinity W.AwayPartialW)
    W.relation_D_atInfinity
  rw [map_add, map_smul, map_smul, map_zero, map_D, map_D] at this
  rw [algebraMap_smul, algebraMap_smul]
  exact eq_neg_of_add_eq_zero_right this

/-- **`dw = -(h_z / h_w) dz`.** Let `W` be a Weierstrass curve over a commutative ring `R` and let
`S = B_W[1 / h_w]`. In `Ω¹_{S/R}`,

$$dw = -\frac{h_z}{h_w} \, dz,$$

with `h_z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²` and
`h_w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`.

No hypothesis on the discriminant is needed. -/
theorem D_wAtInfinity_awayPartialW :
    D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity) =
      -(algebraMap _ W.AwayPartialW W.partialZAtInfinity *
          IsLocalization.Away.invSelf W.partialWAtInfinity) •
        D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity) := by
  have hu := IsLocalization.Away.mul_invSelf (S := W.AwayPartialW) W.partialWAtInfinity
  calc D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity)
      = IsLocalization.Away.invSelf W.partialWAtInfinity •
          (algebraMap _ W.AwayPartialW W.partialWAtInfinity •
            D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity)) := by
        rw [smul_smul, mul_comm, hu, one_smul]
    _ = _ := by rw [relation_D_awayPartialW, smul_neg, smul_smul, neg_smul, mul_comm]

/-- **`dz` spans `Ω¹_S`.** Let `W` be a Weierstrass curve over a commutative ring `R` and let
`S = B_W[1 / h_w]`. The `S`-module `Ω¹_{S/R}` is spanned by `dz`.

The localization step `S ⊗_{B_W} Ω¹_{B_W/R} = Ω¹_{S/R}` is the Stacks project, Lemma 10.131.8,
<https://stacks.math.columbia.edu/tag/00RT>; here it is proved directly from `dw = -(h_z / h_w) dz`
(`D_wAtInfinity_awayPartialW`) and the Leibniz rule. -/
theorem span_D_zAtInfinity_awayPartialW :
    Submodule.span W.AwayPartialW {D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity)} = ⊤ := by
  set N := Submodule.span W.AwayPartialW {D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity)}
  have hz : D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity) ∈ N :=
    Submodule.subset_span rfl
  have hw : D R _ (algebraMap _ W.AwayPartialW W.wAtInfinity) ∈ N := by
    rw [D_wAtInfinity_awayPartialW]; exact Submodule.smul_mem _ _ hz
  have hB : ∀ b : W.CoordinateRingAtInfinity,
      D R W.AwayPartialW (algebraMap _ W.AwayPartialW b) ∈ N := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [D_algebraMap_mk_awayPartialW]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ hw)
  rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers W.partialWAtInfinity) s
  have e := IsLocalization.mk'_spec W.AwayPartialW x y
  obtain ⟨v, hv⟩ := (IsLocalization.map_units W.AwayPartialW y).exists_right_inv
  have key : algebraMap _ W.AwayPartialW (y : W.CoordinateRingAtInfinity) •
      D R _ (IsLocalization.mk' W.AwayPartialW x y) =
        D R _ (algebraMap _ _ x) - IsLocalization.mk' W.AwayPartialW x y •
          D R _ (algebraMap _ W.AwayPartialW (y : W.CoordinateRingAtInfinity)) := by
    rw [← e, Derivation.leibniz]
    abel
  have : D R _ (IsLocalization.mk' W.AwayPartialW x y) =
      v • (algebraMap _ W.AwayPartialW (y : W.CoordinateRingAtInfinity) •
        D R _ (IsLocalization.mk' W.AwayPartialW x y)) := by
    rw [smul_smul, mul_comm, hv, one_smul]
  rw [this, key]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hB x) (Submodule.smul_mem _ _ (hB _)))

/-! ### The coefficient of `dz` -/

/-- **The derivation `∂/∂z` on `R[z, w]` with values in `S`.** Let `W` be a Weierstrass curve
over a commutative ring `R` and let `S = B_W[1 / h_w]`. This is the `R`-derivation
`R[z, w] → S` sending `z ↦ 1` and `w ↦ -h_z / h_w`. -/
noncomputable def derivationZPoly :
    Derivation R (MvPolynomial (Fin 2) R) W.AwayPartialW :=
  mkDerivation R ![1, -(algebraMap _ W.AwayPartialW W.partialZAtInfinity *
    IsLocalization.Away.invSelf W.partialWAtInfinity)]

private lemma algebraMap_poly_eq (p : MvPolynomial (Fin 2) R) :
    algebraMap (MvPolynomial (Fin 2) R) W.AwayPartialW p =
      algebraMap W.CoordinateRingAtInfinity W.AwayPartialW
        (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) p) := by
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 2) R) W.CoordinateRingAtInfinity,
    Ideal.Quotient.algebraMap_eq]

private lemma derivationZPoly_polynomialAtInfinity :
    W.derivationZPoly W.polynomialAtInfinity = 0 := by
  have hu := IsLocalization.Away.mul_invSelf (S := W.AwayPartialW) W.partialWAtInfinity
  rw [derivation_eq_pderiv, pderiv_zero_polynomialAtInfinity, pderiv_one_polynomialAtInfinity]
  simp only [derivationZPoly, mkDerivation_X, Algebra.smul_def, algebraMap_poly_eq]
  change algebraMap _ _ W.partialZAtInfinity * 1 + algebraMap _ _ W.partialWAtInfinity *
    -(algebraMap _ _ W.partialZAtInfinity * _) = 0
  linear_combination (-(algebraMap _ W.AwayPartialW W.partialZAtInfinity)) * hu

/-- **`∂/∂z` kills the equation.** Let `W` be a Weierstrass curve over a commutative ring `R`.
The derivation `R[z, w] → B_W[1 / h_w]` with `z ↦ 1`, `w ↦ -h_z / h_w` vanishes on the ideal
`(h)`, since `h_z · 1 + h_w · (-h_z / h_w) = 0`. -/
theorem derivationZPoly_mem (a : MvPolynomial (Fin 2) R)
    (ha : a ∈ Ideal.span {W.polynomialAtInfinity}) : W.derivationZPoly a = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have h : Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) W.polynomialAtInfinity = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [Derivation.leibniz, derivationZPoly_polynomialAtInfinity, smul_zero, zero_add,
    Algebra.smul_def, algebraMap_poly_eq, h, map_zero, zero_mul]

/-- **The derivation `∂/∂z` on `B_W` with values in `S`.** Let `W` be a Weierstrass curve over a
commutative ring `R` and let `S = B_W[1 / h_w]`. This is the `R`-derivation `B_W → S` sending
`z ↦ 1` and `w ↦ -h_z / h_w`, induced by `derivationZPoly`. -/
noncomputable def derivationZ : Derivation R W.CoordinateRingAtInfinity W.AwayPartialW :=
  Derivation.mk'
    (((Ideal.span {W.polynomialAtInfinity}).restrictScalars R).liftQ
        W.derivationZPoly.toLinearMap (fun a ha ↦ W.derivationZPoly_mem a ha) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R _).symm.toLinearMap) (by
    intro a b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    change W.derivationZPoly (p * q) = _ • W.derivationZPoly q + _ • W.derivationZPoly p
    rw [Derivation.leibniz, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul])

private lemma derivationZ_mk (p : MvPolynomial (Fin 2) R) :
    W.derivationZ (Ideal.Quotient.mk (Ideal.span {W.polynomialAtInfinity}) p) =
      W.derivationZPoly p :=
  rfl

/-- **The coefficient of `dz`.** Let `W` be a Weierstrass curve over a commutative ring `R` and
let `S = B_W[1 / h_w]`. This is the `S`-linear map `Ω¹_{S/R} → S` sending `dz ↦ 1`
(`coeffDZ_D_zAtInfinity`) and `dw ↦ -h_z / h_w`. It is built from the derivation `derivationZ`
on `B_W` through `S ⊗_{B_W} Ω¹_{B_W/R} ≃ Ω¹_{S/R}`, the Stacks project, Lemma 10.131.8,
<https://stacks.math.columbia.edu/tag/00RT>. -/
noncomputable def coeffDZ :
    (KaehlerDifferential R W.AwayPartialW) →ₗ[W.AwayPartialW] W.AwayPartialW :=
  (W.derivationZ.liftKaehlerDifferential.liftBaseChange W.AwayPartialW) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale R W.CoordinateRingAtInfinity
      W.AwayPartialW).symm.toLinearMap

/-- **The coefficient of `dz` in `dz` is `1`.** Let `W` be a Weierstrass curve over a commutative
ring `R` and let `S = B_W[1 / h_w]`. The map `coeffDZ : Ω¹_{S/R} → S` sends `dz` to `1`. -/
theorem coeffDZ_D_zAtInfinity :
    W.coeffDZ (D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity)) = 1 := by
  simp only [coeffDZ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D, one_smul]
  rw [zAtInfinity, derivationZ_mk]
  simp [derivationZPoly, mkDerivation_X]

/-! ### `Ω¹_S` is free of rank one on `dz` -/

/-- **`Ω¹_S` is free with basis `dz`.** Let `W` be a Weierstrass curve over a commutative ring `R`
and let `S = B_W[1 / h_w]` be the part of the chart at infinity `B_W = R[z, w] / (h)` where
`h_w = ∂h/∂w` is invertible; it contains the point at infinity `z = w = 0`, where `h_w = 1`. Then
`Ω¹_{S/R}` is a free `S`-module with the one-element basis `dz` (`basisAwayPartialW_apply`).

The source works over a field and with `Δ_W ≠ 0`; neither hypothesis is used: `R` is any
commutative ring and `W` any Weierstrass curve. This is the algebraic input to Milne's remark
that the invariant differential is holomorphic at the point at infinity.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §6, p. 211 ("One can check that it also
holomorphic at the point at infinity"); the Stacks project, Lemma 10.131.8,
<https://stacks.math.columbia.edu/tag/00RT>. -/
noncomputable def basisAwayPartialW :
    Module.Basis (Fin 1) W.AwayPartialW (KaehlerDifferential R W.AwayPartialW) :=
  Module.Basis.mk (v := fun _ ↦ D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity))
    (LinearIndependent.of_comp W.coeffDZ (by
      have : W.coeffDZ ∘ (fun _ : Fin 1 ↦ D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity))
          = Module.Basis.singleton (Fin 1) W.AwayPartialW := by
        funext i
        simp [coeffDZ_D_zAtInfinity]
      rw [this]
      exact (Module.Basis.singleton (Fin 1) W.AwayPartialW).linearIndependent))
    (by rw [← W.span_D_zAtInfinity_awayPartialW, Set.range_const])

/-- The basis vector of `basisAwayPartialW` is `dz`. -/
theorem basisAwayPartialW_apply (i : Fin 1) :
    W.basisAwayPartialW i = D R _ (algebraMap _ W.AwayPartialW W.zAtInfinity) := by
  simp [basisAwayPartialW]

/-- `Ω¹_{S/R}` is a free `S`-module, for `S = B_W[1 / h_w]`. -/
instance free_awayPartialW : Module.Free W.AwayPartialW (KaehlerDifferential R W.AwayPartialW) :=
  Module.Free.of_basis W.basisAwayPartialW

/-- **Evaluation of `S` at the point at infinity.** Let `W` be a Weierstrass curve over a
commutative ring `R`. This is the ring map `B_W[1 / h_w] → R` sending `z ↦ 0` and `w ↦ 0`, well
defined since `h_w(0, 0) = 1` (`evalAtInfinity_partialWAtInfinity`). -/
noncomputable def evalAtInfinityAwayPartialW : W.AwayPartialW →+* R :=
  IsLocalization.Away.lift W.partialWAtInfinity (g := W.evalAtInfinity.toRingHom) (by
    simp [evalAtInfinity_partialWAtInfinity])

/-- `S = B_W[1 / h_w]` is nontrivial when `R` is: it maps to `R` by evaluation at the point at
infinity. -/
instance nontrivial_awayPartialW [Nontrivial R] : Nontrivial W.AwayPartialW :=
  W.evalAtInfinityAwayPartialW.domain_nontrivial

/-- **`Ω¹_S` has rank one.** Let `W` be a Weierstrass curve over a nontrivial commutative ring
`R` (for example a field) and let `S = B_W[1 / h_w]`. Then `Ω¹_{S/R}` is a free `S`-module of rank
`1`, with basis `dz` (`basisAwayPartialW`).

No hypothesis on the discriminant is needed. -/
theorem finrank_awayPartialW [Nontrivial R] :
    Module.finrank W.AwayPartialW (KaehlerDifferential R W.AwayPartialW) = 1 := by
  rw [Module.finrank_eq_card_basis W.basisAwayPartialW, Fintype.card_fin]

end WeierstrassCurve
