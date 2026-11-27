/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.AlgebraicGeometry.EllipticCurve.DifferentialsAtInfinity
public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The invariant differential in the chart at infinity

Let `W` be a Weierstrass curve over a field `F` with coefficients `a₁, a₂, a₃, a₄, a₆`, with affine
coordinate ring `A_W = F[x, y] / (g)`, `g = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`, and
coordinate ring at infinity `B_W = F[z, w] / (h)`,
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`, glued along
`A_W[1 / y] ≃ B_W[1 / w]`, `x ↦ z / w`, `y ↦ 1 / w` (`WeierstrassCurve.awayYEquivAwayW`).
Write `P = 2 y + a₁ x + a₃` and `Q = 3 x² + 2 a₂ x + a₄ - a₁ y`, and
`h_z = ∂h / ∂z = a₁ w - 3 z² - 2 a₂ z w - a₄ w²`,
`h_w = ∂h / ∂w = 1 + a₁ z + 2 a₃ w - a₂ z² - 2 a₄ z w - 3 a₆ w²`.

The invariant differential `ω_W` of `A_W` satisfies `P ω_W = dx` and `Q ω_W = dy`. This file works
in the module of Kähler differentials `Ω¹` of the overlap `S = B_W[1 / w]` over `F`, with `x` and
`y` read in `S` through the isomorphism, and proves, when the discriminant is nonzero:

* there is exactly one `θ ∈ Ω¹_{S/F}` with `P θ = dx` and `Q θ = dy`, namely `p dx + q dy` for any
  `p, q` with `p P + q Q = 1` (`WeierstrassCurve.existsUnique_invariantDifferential_atInfinity`);
* every such `θ` satisfies `h_w θ = -dz` and `h_z θ = dw`
  (`WeierstrassCurve.invariantDifferential_atInfinity`).

Here `h_z` and `h_w` are `WeierstrassCurve.partialZAtInfinity` and
`WeierstrassCurve.partialWAtInfinity`, the classes in `B_W` of the partial derivatives of `h`,
mapped to `S`.

The identities `h_w dx = -P dz`, `h_w dy = -Q dz`, `h_z dx = P dw`, `h_z dy = Q dw` behind them hold
for every Weierstrass curve (`WeierstrassCurve.kaehler_identities_atInfinity`).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §6, p. 211.
-/

@[expose] public section

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-! ### The identities in the differentials of the overlap -/

section Identities

variable {S : Type*} [CommRing S] [Algebra F S]

open KaehlerDifferential in
/-- The four identities in `Ω¹_{S/F}` for elements `z, w, v` of an `F`-algebra `S` with
`w v = 1` and `h(z, w) = 0`, with `x = z v` and `y = v`. -/
private theorem kaehler_identities_aux (z w v : S) (hv : w * v = 1)
    (hrel : w + algebraMap F S W.a₁ * z * w + algebraMap F S W.a₃ * w ^ 2 - z ^ 3 -
      algebraMap F S W.a₂ * z ^ 2 * w - algebraMap F S W.a₄ * z * w ^ 2 -
      algebraMap F S W.a₆ * w ^ 3 = 0) :
    let a₁ := algebraMap F S W.a₁
    let a₂ := algebraMap F S W.a₂
    let a₃ := algebraMap F S W.a₃
    let a₄ := algebraMap F S W.a₄
    let a₆ := algebraMap F S W.a₆
    let hz := a₁ * w - 3 * z ^ 2 - 2 * a₂ * z * w - a₄ * w ^ 2
    let hw := 1 + a₁ * z + 2 * a₃ * w - a₂ * z ^ 2 - 2 * a₄ * z * w - 3 * a₆ * w ^ 2
    let x := z * v
    let y := v
    let P := 2 * y + a₁ * x + a₃
    let Q := 3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y
    hw • D F S x = -(P • D F S z) ∧ hw • D F S y = -(Q • D F S z) ∧
      hz • D F S x = P • D F S w ∧ hz • D F S y = Q • D F S w := by
  intro a₁ a₂ a₃ a₄ a₆ hz hw x y P Q
  have hd : hz • D F S z + hw • D F S w = 0 := by
    have h := congrArg (D F S) hrel
    simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow,
      Derivation.map_algebraMap, map_zero, smul_zero, add_zero] at h
    simp only [hz, hw]
    linear_combination (norm := module) h
  have hdv : D F S v = -(v ^ 2 • D F S w) := by
    have h := congrArg (D F S) hv
    simp only [Derivation.leibniz, Derivation.map_one_eq_zero] at h
    linear_combination (norm := module) v • h - hv • D F S v
  have hc : z * v ^ 2 * hz + v * hw + P = 0 := by
    simp only [hz, hw, P, x, y]
    linear_combination 3 * v ^ 2 * hrel -
      ((2 + a₁ * z) * v + a₃ * (1 + v * w) + v * hw) * hv
  have hc₂ : v ^ 2 * hz + Q = 0 := by
    simp only [hz, Q, x, y]
    linear_combination (a₁ * v - 2 * a₂ * z * v - a₄ * (v * w + 1)) * hv
  have hDx : D F S x = z • D F S v + v • D F S z := Derivation.leibniz _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hDx, hdv]
    linear_combination (norm := module) (-(z * v ^ 2)) • hd + hc • D F S z
  · change hw • D F S v = _
    rw [hdv]
    linear_combination (norm := module) (-(v ^ 2)) • hd + hc₂ • D F S z
  · rw [hDx, hdv]
    linear_combination (norm := module) v • hd - hc • D F S w
  · change hz • D F S v = _
    rw [hdv]
    linear_combination (norm := module) -(hc₂ • D F S w)

end Identities

/-! ### The overlap of the two charts -/

/-- The chart map `A_W → B_W[1 / w]`, the composite of `A_W → A_W[1 / y]` and the isomorphism
`A_W[1 / y] ≃ B_W[1 / w]`; it sends `x ↦ z / w` and `y ↦ 1 / w`. -/
noncomputable def affineToOverlap : W.toAffine.CoordinateRing →ₐ[F] W.AtInfinityAwayW :=
  W.awayYEquivAwayW.toAlgHom.comp (IsScalarTower.toAlgHom F _ W.AffineAwayY)

/-- The chart map `A_W → B_W[1 / w]` sends `x` to `z / w`. -/
theorem affineToOverlap_affineX :
    W.affineToOverlap W.affineX =
      algebraMap _ _ W.zAtInfinity * IsLocalization.Away.invSelf W.wAtInfinity :=
  W.awayYEquivAwayW_affineX

/-- The chart map `A_W → B_W[1 / w]` sends `y` to `1 / w`. -/
theorem affineToOverlap_affineY :
    W.affineToOverlap W.affineY = IsLocalization.Away.invSelf W.wAtInfinity :=
  W.awayYEquivAwayW_affineY

private lemma algebraMap_mk_C (c : F) :
    algebraMap W.CoordinateRingAtInfinity W.AtInfinityAwayW
      (Ideal.Quotient.mk _ (MvPolynomial.C c)) = algebraMap F _ c := by
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
    ← IsScalarTower.algebraMap_apply]

private lemma partialZAtInfinity_eq :
    algebraMap _ W.AtInfinityAwayW W.partialZAtInfinity =
      algebraMap F _ W.a₁ * algebraMap _ _ W.wAtInfinity -
        3 * algebraMap _ _ W.zAtInfinity ^ 2 -
        2 * algebraMap F _ W.a₂ * algebraMap _ _ W.zAtInfinity * algebraMap _ _ W.wAtInfinity -
        algebraMap F _ W.a₄ * algebraMap _ _ W.wAtInfinity ^ 2 := by
  rw [partialZAtInfinity, polynomialAtInfinityZ]
  simp only [map_sub, map_mul, map_pow, map_ofNat, algebraMap_mk_C]
  rfl

private lemma partialWAtInfinity_eq :
    algebraMap _ W.AtInfinityAwayW W.partialWAtInfinity =
      1 + algebraMap F _ W.a₁ * algebraMap _ _ W.zAtInfinity +
        2 * algebraMap F _ W.a₃ * algebraMap _ _ W.wAtInfinity -
        algebraMap F _ W.a₂ * algebraMap _ _ W.zAtInfinity ^ 2 -
        2 * algebraMap F _ W.a₄ * algebraMap _ _ W.zAtInfinity * algebraMap _ _ W.wAtInfinity -
        3 * algebraMap F _ W.a₆ * algebraMap _ _ W.wAtInfinity ^ 2 := by
  rw [partialWAtInfinity, polynomialAtInfinityW]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one, algebraMap_mk_C]
  rfl

open KaehlerDifferential in
/-- **The differentials of the chart coordinates on the overlap.** Let `W` be a Weierstrass curve
over a field `F`, let `S = B_W[1 / w]` be the overlap of its two charts, and read
`x = z / w` and `y = 1 / w` in `S` through the chart isomorphism
(`WeierstrassCurve.affineToOverlap`). Let `P = 2 y + a₁ x + a₃`,
`Q = 3 x² + 2 a₂ x + a₄ - a₁ y`, `h_z = ∂h / ∂z` and `h_w = ∂h / ∂w` for
`h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`. Then in the module `Ω¹_{S/F}` of Kähler
differentials,
`h_w dx = -P dz`, `h_w dy = -Q dz`, `h_z dx = P dw` and `h_z dy = Q dw`.

No hypothesis on the discriminant is needed. These are the identities of the source's proof of
`h_w ω_W = -dz` and `h_z ω_W = dw`. -/
theorem kaehler_identities_atInfinity :
    let x := W.affineToOverlap W.affineX
    let y := W.affineToOverlap W.affineY
    let P := 2 * y + algebraMap F _ W.a₁ * x + algebraMap F _ W.a₃
    let Q := 3 * x ^ 2 + 2 * algebraMap F _ W.a₂ * x + algebraMap F _ W.a₄ -
      algebraMap F _ W.a₁ * y
    let z : W.AtInfinityAwayW := algebraMap _ _ W.zAtInfinity
    let w : W.AtInfinityAwayW := algebraMap _ _ W.wAtInfinity
    algebraMap _ W.AtInfinityAwayW W.partialWAtInfinity • D F _ x = -(P • D F _ z) ∧
      algebraMap _ W.AtInfinityAwayW W.partialWAtInfinity • D F _ y = -(Q • D F _ z) ∧
      algebraMap _ W.AtInfinityAwayW W.partialZAtInfinity • D F _ x = P • D F _ w ∧
      algebraMap _ W.AtInfinityAwayW W.partialZAtInfinity • D F _ y = Q • D F _ w := by
  intro x y P Q z w
  have hrel := congrArg (algebraMap W.CoordinateRingAtInfinity W.AtInfinityAwayW)
    W.relation_atInfinity
  simp only [map_sub, map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] at hrel
  have hv := IsLocalization.Away.mul_invSelf (S := W.AtInfinityAwayW) W.wAtInfinity
  have key := W.kaehler_identities_aux z w (IsLocalization.Away.invSelf W.wAtInfinity) hv hrel
  simp only [x, y, affineToOverlap_affineX, affineToOverlap_affineY, partialZAtInfinity_eq,
    partialWAtInfinity_eq, P, Q]
  exact key

/-- The partial derivatives `P = 2 y + a₁ x + a₃` and `Q = 3 x² + 2 a₂ x + a₄ - a₁ y` generate the
unit ideal of the overlap `B_W[1 / w]` when the discriminant is nonzero. -/
private lemma exists_mul_add_mul_eq_one_overlap (hΔ : W.Δ ≠ 0) :
    ∃ p q : W.AtInfinityAwayW,
      p * (2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
          algebraMap F _ W.a₃) +
        q * (3 * W.affineToOverlap W.affineX ^ 2 +
          2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
          algebraMap F _ W.a₁ * W.affineToOverlap W.affineY) = 1 := by
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero W hΔ
  refine ⟨W.affineToOverlap p, W.affineToOverlap q, ?_⟩
  have h := congrArg W.affineToOverlap hpq
  have hC : ∀ c : F, AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (Polynomial.C c)) =
      algebraMap F W.toAffine.CoordinateRing c := fun c ↦ by
    simp [IsScalarTower.algebraMap_apply F (Polynomial F) (AdjoinRoot _),
      AdjoinRoot.algebraMap_eq]
  simp only [Affine.polynomialY, Affine.polynomialX, map_add, map_sub, map_mul, map_neg,
    map_pow, AdjoinRoot.mk_X, hC] at h
  rw [map_one] at h
  have hX : AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) = W.affineX :=
    AdjoinRoot.mk_C _
  have hY : AdjoinRoot.root W.toAffine.polynomial = W.affineY := rfl
  simp only [hX, hY, AlgHom.commutes,
    map_ofNat] at h
  linear_combination h

open KaehlerDifferential in
/-- **The invariant differential in the chart at infinity.** Let `W` be a Weierstrass curve over a
field `F` with discriminant `Δ_W ≠ 0`, let `S = B_W[1 / w]` be the overlap of its two charts, and
read `x = z / w` and `y = 1 / w` in `S` through the chart isomorphism
(`WeierstrassCurve.affineToOverlap`). Let `P = 2 y + a₁ x + a₃`, `Q = 3 x² + 2 a₂ x + a₄ - a₁ y`,
`h_z = ∂h / ∂z` and `h_w = ∂h / ∂w` for `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`.
If `θ ∈ Ω¹_{S/F}` satisfies `P θ = dx` and `Q θ = dy`, then `h_w θ = -dz` and `h_z θ = dw`.

The invariant differential `ω_W` of the affine chart satisfies `P ω_W = dx` and `Q ω_W = dy`, so its
image in `Ω¹_{S/F}` is such a `θ`; by `existsUnique_invariantDifferential_atInfinity` there is
exactly one. This is item 2 of the source's statement, read in `Ω¹_{S/F}`. Item 1, that `Ω¹` of
`(B_W)_{h_w}` is free with basis `dz`, is `WeierstrassCurve.basisAwayPartialW`; the final form
`ω_W = -dz / h_w` on `(B_W)_{w h_w}` is not stated here.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter V, §6, p. 211: `ω = dx / 2y` is holomorphic on
the affine curve, and "One can check that it also holomorphic at the point at infinity"; this is
the algebraic form of that check. -/
theorem invariantDifferential_atInfinity (hΔ : W.Δ ≠ 0)
    (θ : KaehlerDifferential F W.AtInfinityAwayW)
    (hP : (2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
        algebraMap F _ W.a₃) • θ = D F _ (W.affineToOverlap W.affineX))
    (hQ : (3 * W.affineToOverlap W.affineX ^ 2 +
        2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
        algebraMap F _ W.a₁ * W.affineToOverlap W.affineY) • θ =
        D F _ (W.affineToOverlap W.affineY)) :
    algebraMap _ W.AtInfinityAwayW W.partialWAtInfinity • θ =
        -D F _ (algebraMap _ W.AtInfinityAwayW W.zAtInfinity) ∧
      algebraMap _ W.AtInfinityAwayW W.partialZAtInfinity • θ =
        D F _ (algebraMap _ W.AtInfinityAwayW W.wAtInfinity) := by
  obtain ⟨p, q, hpq⟩ := W.exists_mul_add_mul_eq_one_overlap hΔ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := W.kaehler_identities_atInfinity
  set P := 2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
    algebraMap F _ W.a₃
  set Q := 3 * W.affineToOverlap W.affineX ^ 2 +
    2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
    algebraMap F _ W.a₁ * W.affineToOverlap W.affineY
  set hw := algebraMap _ W.AtInfinityAwayW W.partialWAtInfinity
  set hz := algebraMap _ W.AtInfinityAwayW W.partialZAtInfinity
  clear_value P Q
  constructor
  · calc hw • θ = (p * P + q * Q) • (hw • θ) := by rw [hpq, one_smul]
      _ = p • (hw • (P • θ)) + q • (hw • (Q • θ)) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm P, smul_comm Q]
      _ = -((p * P + q * Q) • D F _ (algebraMap _ W.AtInfinityAwayW W.zAtInfinity)) := by
          rw [hP, hQ, h₁, h₂, add_smul, mul_smul, mul_smul, smul_neg, smul_neg, neg_add]
      _ = _ := by rw [hpq, one_smul]
  · calc hz • θ = (p * P + q * Q) • (hz • θ) := by rw [hpq, one_smul]
      _ = p • (hz • (P • θ)) + q • (hz • (Q • θ)) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm P, smul_comm Q]
      _ = (p * P + q * Q) • D F _ (algebraMap _ W.AtInfinityAwayW W.wAtInfinity) := by
          rw [hP, hQ, h₃, h₄, add_smul, mul_smul, mul_smul]
      _ = _ := by rw [hpq, one_smul]

open KaehlerDifferential in
/-- The differential of the affine equation: `P dy = Q dx` for a solution `(x, y)` in an
`F`-algebra `S`. -/
private lemma kaehler_affine_relation_aux {S : Type*} [CommRing S] [Algebra F S] (x y : S)
    (hrel : y ^ 2 + algebraMap F S W.a₁ * x * y + algebraMap F S W.a₃ * y -
      (x ^ 3 + algebraMap F S W.a₂ * x ^ 2 + algebraMap F S W.a₄ * x + algebraMap F S W.a₆) = 0) :
    (2 * y + algebraMap F S W.a₁ * x + algebraMap F S W.a₃) • D F S y =
      (3 * x ^ 2 + 2 * algebraMap F S W.a₂ * x + algebraMap F S W.a₄ -
        algebraMap F S W.a₁ * y) • D F S x := by
  have h := congrArg (D F S) hrel
  simp only [map_sub, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.map_algebraMap, map_zero, smul_zero, add_zero] at h
  linear_combination (norm := module) h

open KaehlerDifferential in
/-- The differential of the affine equation on the overlap: `P dy = Q dx`. -/
private lemma kaehler_affine_relation :
    (2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
        algebraMap F _ W.a₃) • D F _ (W.affineToOverlap W.affineY) =
      (3 * W.affineToOverlap W.affineX ^ 2 +
        2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
        algebraMap F _ W.a₁ * W.affineToOverlap W.affineY) •
        D F _ (W.affineToOverlap W.affineX) := by
  have hrel := congrArg W.affineToOverlap W.relation_affine
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, AlgHom.commutes] at hrel
  exact W.kaehler_affine_relation_aux _ _ hrel

open KaehlerDifferential in
/-- **The invariant differential on the overlap exists and is unique.** Let `W` be a Weierstrass
curve over a field `F` with discriminant `Δ_W ≠ 0`, let `S = B_W[1 / w]` be the overlap of its two
charts, and read `x = z / w` and `y = 1 / w` in `S` through the chart isomorphism. Let
`P = 2 y + a₁ x + a₃` and `Q = 3 x² + 2 a₂ x + a₄ - a₁ y`. Then there is exactly one
`θ ∈ Ω¹_{S/F}` with `P θ = dx` and `Q θ = dy`: for `p, q ∈ S` with `p P + q Q = 1`, it is
`θ = p dx + q dy`. It is the image of the invariant differential `ω_W` of the affine chart. -/
theorem existsUnique_invariantDifferential_atInfinity (hΔ : W.Δ ≠ 0) :
    ∃! θ : KaehlerDifferential F W.AtInfinityAwayW,
      (2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
          algebraMap F _ W.a₃) • θ = D F _ (W.affineToOverlap W.affineX) ∧
        (3 * W.affineToOverlap W.affineX ^ 2 +
          2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
          algebraMap F _ W.a₁ * W.affineToOverlap W.affineY) • θ =
          D F _ (W.affineToOverlap W.affineY) := by
  obtain ⟨p, q, hpq⟩ := W.exists_mul_add_mul_eq_one_overlap hΔ
  have hg := W.kaehler_affine_relation
  set P := 2 * W.affineToOverlap W.affineY + algebraMap F _ W.a₁ * W.affineToOverlap W.affineX +
    algebraMap F _ W.a₃
  set Q := 3 * W.affineToOverlap W.affineX ^ 2 +
    2 * algebraMap F _ W.a₂ * W.affineToOverlap W.affineX + algebraMap F _ W.a₄ -
    algebraMap F _ W.a₁ * W.affineToOverlap W.affineY
  set dx := D F _ (W.affineToOverlap W.affineX)
  set dy := D F _ (W.affineToOverlap W.affineY)
  clear_value P Q dx dy
  refine ⟨p • dx + q • dy, ⟨?_, ?_⟩, ?_⟩
  · calc P • (p • dx + q • dy) = (p * P) • dx + q • (P • dy) := by
          rw [smul_add, smul_smul, smul_comm P q, mul_comm P p]
      _ = (p * P + q * Q) • dx := by rw [hg, ← mul_smul, add_smul]
      _ = dx := by rw [hpq, one_smul]
  · calc Q • (p • dx + q • dy) = p • (Q • dx) + (q * Q) • dy := by
          rw [smul_add, smul_comm Q p, smul_smul, smul_smul, mul_comm Q q]
      _ = (p * P + q * Q) • dy := by rw [← hg, ← mul_smul, add_smul]
      _ = dy := by rw [hpq, one_smul]
  · rintro θ ⟨hP, hQ⟩
    calc θ = (p * P + q * Q) • θ := by rw [hpq, one_smul]
      _ = p • dx + q • dy := by rw [add_smul, mul_smul, mul_smul, hP, hQ]

end WeierstrassCurve
