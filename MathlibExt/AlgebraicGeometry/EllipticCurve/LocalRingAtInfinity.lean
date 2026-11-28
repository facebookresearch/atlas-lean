/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The local ring at the point at infinity of a Weierstrass cubic

Let `W` be a Weierstrass curve over a field `F`, with affine coordinate ring
`A_W = F[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)` and coordinate ring at infinity
`B_W = F[z, w] / (h)`, `h = w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³`, where
`z = X / Y` and `w = Z / Y` (`WeierstrassCurve.CoordinateRingAtInfinity`). The point at infinity
`O = (0 : 1 : 0)` is the point `z = w = 0` of the chart `Y ≠ 0`. This file proves:

* `m = (z, w)` is a maximal ideal of `B_W` (`WeierstrassCurve.maximalIdealAtInfinity`), and in
  the local ring `𝒪 = (B_W)_m` (`WeierstrassCurve.LocalRingAtInfinity`) one has `w = z³ v` for
  the unit `v = (1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²)⁻¹`;
* `A_W` and `B_W` are domains, and `𝒪` is a discrete valuation ring with uniformizer `z`, so
  `ord_O z = 1` and `ord_O w = 3`;
* `B_W` and `𝒪` have the same fraction field as `A_W`, namely Mathlib's
  `WeierstrassCurve.Affine.FunctionField` (through `A_W[1 / y] ≃ B_W[1 / w]`); there
  `x z² = y z³ = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²`, a unit of `𝒪`, so `ord_O x = -2` and
  `ord_O y = -3`;
* an element of `A_W` whose image in the function field lies in `𝒪` is a constant: the regular
  functions on the projective cubic are the constants.

The valuation at `O` is Mathlib's adic valuation of the maximal ideal of `𝒪`
(`WeierstrassCurve.valuationAtInfinity`), with values in `ℤᵐ⁰`; it sends `f` to
`exp (-ord_O f)`.

The sources assume `Δ_W ≠ 0`; nothing here uses it: `W` is any Weierstrass curve over a field.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, pp. 31 and 34, and Chapter II, §1,
  p. 47.
* B. Conrad, *Minimal models for elliptic curves*, notes, 21 November 2015,
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Theorem 2.8, p. 4.
* The Stacks project, Lemma 10.119.7, <https://stacks.math.columbia.edu/tag/00PD>.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The element `u = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²` of the coordinate ring at
infinity `B_W`, for a Weierstrass curve `W` over a commutative ring `R`. It satisfies
`w u = z³` (`wAtInfinity_mul_unitAtInfinity`), and over a field it is a unit of the local ring
at infinity (`isUnit_algebraMap_unitAtInfinity`). -/
noncomputable def unitAtInfinity : W.CoordinateRingAtInfinity :=
  1 + algebraMap R _ W.a₁ * W.zAtInfinity + algebraMap R _ W.a₃ * W.wAtInfinity -
    algebraMap R _ W.a₂ * W.zAtInfinity ^ 2 -
    algebraMap R _ W.a₄ * W.zAtInfinity * W.wAtInfinity - algebraMap R _ W.a₆ * W.wAtInfinity ^ 2

/-- **The relation at infinity, factored.** Let `W` be a Weierstrass curve over a commutative
ring `R`. In `B_W = R[z, w] / (h)` one has `w u = z³`, where
`u = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²` (`unitAtInfinity`): this is the relation
`w + a₁ z w + a₃ w² - z³ - a₂ z² w - a₄ z w² - a₆ w³ = 0` rewritten.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Theorem 2.8, p. 4. -/
theorem wAtInfinity_mul_unitAtInfinity :
    W.wAtInfinity * W.unitAtInfinity = W.zAtInfinity ^ 3 := by
  have h := W.relation_atInfinity
  rw [unitAtInfinity]
  linear_combination h

end CommRing

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-! ### The maximal ideal of the point at infinity -/

/-- The element `u = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²` takes the value `1` at the point
at infinity. -/
theorem evalAtInfinity_unitAtInfinity : W.evalAtInfinity W.unitAtInfinity = 1 := by
  simp [unitAtInfinity, evalAtInfinity_zAtInfinity, evalAtInfinity_wAtInfinity]

/-- The ideal `m` of the point at infinity in `B_W`, for a Weierstrass curve `W` over a field
`F`: the kernel of evaluation at `z = w = 0`. It equals `(z, w)`
(`maximalIdealAtInfinity_eq_span`) and is maximal. -/
noncomputable def maximalIdealAtInfinity : Ideal W.CoordinateRingAtInfinity :=
  RingHom.ker W.evalAtInfinity

/-- The ideal of the point at infinity is maximal, since evaluation `B_W → F` is surjective. -/
instance : W.maximalIdealAtInfinity.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap F _ c, by simp⟩

/-- **The ideal of the point at infinity.** Let `W` be a Weierstrass curve over a field `F`. The
kernel `m` of evaluation `B_W → F` at `z = w = 0` is the ideal `(z, w)` of `B_W`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34 (the local ring at a point `P` of
an affine curve is the localization at the maximal ideal of `P`). The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem maximalIdealAtInfinity_eq_span :
    W.maximalIdealAtInfinity = Ideal.span {W.zAtInfinity, W.wAtInfinity} := by
  apply le_antisymm
  · intro b hb
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hp : MvPolynomial.constantCoeff p = 0 := by
      rwa [maximalIdealAtInfinity, RingHom.mem_ker, evalAtInfinity_mk] at hb
    have hmem : p ∈ Ideal.span (MvPolynomial.X '' Set.univ) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra! h
      have h0 : m = 0 := by
        ext i
        exact h i (Set.mem_univ i)
      subst h0
      exact (MvPolynomial.mem_support_iff.mp hm) (by rwa [MvPolynomial.constantCoeff_eq] at hp)
    have himage : Ideal.map (Ideal.Quotient.mk _) (Ideal.span (MvPolynomial.X '' Set.univ)) =
        Ideal.span {W.zAtInfinity, W.wAtInfinity} := by
      rw [Ideal.map_span]
      congr 1
      ext b
      simp [Fin.exists_fin_two, zAtInfinity, wAtInfinity, eq_comm]
    rw [← himage]
    exact Ideal.mem_map_of_mem _ hmem
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact W.evalAtInfinity_zAtInfinity
    · exact W.evalAtInfinity_wAtInfinity

/-- The element `u = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²` does not lie in the ideal of the
point at infinity. -/
theorem unitAtInfinity_notMem : W.unitAtInfinity ∉ W.maximalIdealAtInfinity := by
  simp [maximalIdealAtInfinity, evalAtInfinity_unitAtInfinity]

/-- **The local ring at the point at infinity.** For a Weierstrass curve `W` over a field `F`,
this is the localization `𝒪 = (B_W)_m` of the coordinate ring at infinity
`B_W = F[z, w] / (h)` at the maximal ideal `m = (z, w)` of the point `O = (0 : 1 : 0)`. -/
abbrev LocalRingAtInfinity : Type _ := Localization.AtPrime W.maximalIdealAtInfinity

/-- The element `u = 1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²` is a unit of the local ring at
infinity. -/
theorem isUnit_algebraMap_unitAtInfinity :
    IsUnit (algebraMap _ W.LocalRingAtInfinity W.unitAtInfinity) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr W.unitAtInfinity_notMem

/-- The unit `v = (1 + a₁ z + a₃ w - a₂ z² - a₄ z w - a₆ w²)⁻¹` of the local ring at infinity. -/
noncomputable def unitInvAtInfinity : W.LocalRingAtInfinityˣ :=
  W.isUnit_algebraMap_unitAtInfinity.unit⁻¹

/-- **`w = z³ v` at infinity.** Let `W` be a Weierstrass curve over a field `F`. In the local
ring `𝒪 = (B_W)_(z, w)` at the point at infinity,

$$w = z^3 v, \qquad v = (1 + a_1 z + a_3 w - a_2 z^2 - a_4 z w - a_6 w^2)^{-1},$$

where `v` (`unitInvAtInfinity`) is a unit of `𝒪`.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Theorem 2.8, p. 4. The
source assumes `Δ_W ≠ 0`, which is not used. -/
theorem algebraMap_wAtInfinity_eq :
    algebraMap _ W.LocalRingAtInfinity W.wAtInfinity =
      algebraMap _ W.LocalRingAtInfinity W.zAtInfinity ^ 3 * ↑W.unitInvAtInfinity := by
  have h := congrArg (algebraMap _ W.LocalRingAtInfinity) W.wAtInfinity_mul_unitAtInfinity
  rw [map_mul, map_pow] at h
  rw [← h, unitInvAtInfinity, mul_assoc, IsUnit.mul_val_inv, mul_one]

/-! ### The coordinate rings are domains -/

/-- The coordinate `y` is nonzero in the affine coordinate ring `A_W` of a Weierstrass curve
over a field. -/
theorem affineY_ne_zero : W.affineY ≠ 0 := by
  intro h
  rw [affineY, ← AdjoinRoot.mk_X, AdjoinRoot.mk_eq_zero] at h
  have := Polynomial.natDegree_le_of_dvd h Polynomial.X_ne_zero
  rw [Affine.natDegree_polynomial, natDegree_X] at this
  omega

/-- The coordinate `x` is nonzero in the affine coordinate ring `A_W` of a Weierstrass curve
over a field. -/
theorem affineX_ne_zero : W.affineX ≠ 0 := by
  intro h
  rw [affineX, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h
  have := Polynomial.natDegree_le_of_dvd h (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)
  rw [Affine.natDegree_polynomial, natDegree_C] at this
  omega

/-- The powers of `y` are nonzerodivisors of `A_W`. -/
theorem powers_affineY_le_nonZeroDivisors :
    Submonoid.powers W.affineY ≤ nonZeroDivisors W.toAffine.CoordinateRing :=
  powers_le_nonZeroDivisors_of_noZeroDivisors W.affineY_ne_zero

/-- `A_W[1 / y]` is a domain. -/
instance : IsDomain W.AffineAwayY :=
  IsLocalization.isDomain_localization W.powers_affineY_le_nonZeroDivisors

/-- `B_W[1 / w]` is a domain, being isomorphic to `A_W[1 / y]`. -/
instance : IsDomain W.AtInfinityAwayW :=
  Function.Injective.isDomain W.awayYEquivAwayW.symm W.awayYEquivAwayW.symm.injective

/-- **`w` is a nonzerodivisor of `B_W`.** Let `W` be a Weierstrass curve over a field `F`. Then
`w` is a nonzerodivisor of `B_W = F[z, w] / (h)`: `w` is prime in `F[z, w]` and does not divide
`h`, since `h ≡ -z³` modulo `w`. -/
theorem wAtInfinity_mem_nonZeroDivisors :
    W.wAtInfinity ∈ nonZeroDivisors W.CoordinateRingAtInfinity := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [wAtInfinity, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨k, hk⟩ := hb
  have hX : Prime (MvPolynomial.X 1 : MvPolynomial (Fin 2) F) := MvPolynomial.prime_X
  have hnd : ¬ (MvPolynomial.X 1 ∣ W.polynomialAtInfinity) := by
    rintro ⟨r, hr⟩
    have h := congrArg (MvPolynomial.aeval (R := F)
      ![(MvPolynomial.X 0 : MvPolynomial (Fin 2) F), 0]) hr
    rw [aeval_polynomialAtInfinity, map_mul] at h
    simp at h
  have hdvd : MvPolynomial.X 1 ∣ k :=
    (hX.dvd_or_dvd ⟨p, by rw [← hk]; ring⟩).resolve_left hnd
  obtain ⟨k', rfl⟩ := hdvd
  refine ⟨k', mul_right_cancel₀ hX.ne_zero ?_⟩
  linear_combination hk

/-- The map `B_W → B_W[1 / w]` is injective. -/
theorem algebraMap_atInfinityAwayW_injective :
    Function.Injective (algebraMap W.CoordinateRingAtInfinity W.AtInfinityAwayW) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr W.wAtInfinity_mem_nonZeroDivisors)

/-- **The coordinate ring at infinity is a domain.** Let `W` be a Weierstrass curve over a field
`F`. Then `B_W = F[z, w] / (h)` is an integral domain: it embeds into `B_W[1 / w]`, which is
isomorphic to the domain `A_W[1 / y]`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34. -/
instance : IsDomain W.CoordinateRingAtInfinity :=
  Function.Injective.isDomain _ W.algebraMap_atInfinityAwayW_injective

/-- The coordinate `z` is nonzero in `B_W`. -/
theorem zAtInfinity_ne_zero : W.zAtInfinity ≠ 0 := by
  intro hz
  have h := W.awayYEquivAwayW_symm_zAtInfinity
  rw [hz, map_zero, map_zero, eq_comm] at h
  have hu : IsUnit (IsLocalization.Away.invSelf (S := W.AffineAwayY) W.affineY) :=
    isUnit_iff_exists_inv.mpr
      ⟨algebraMap _ _ W.affineY, by rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩
  have hx : algebraMap _ W.AffineAwayY W.affineX = 0 := hu.mul_left_eq_zero.mp h
  exact W.affineX_ne_zero (IsLocalization.injective _ W.powers_affineY_le_nonZeroDivisors
    (hx.trans (map_zero _).symm))

/-! ### The local ring at infinity is a discrete valuation ring -/

/-- The map `B_W → 𝒪` to the local ring at infinity is injective. -/
theorem algebraMap_localRingAtInfinity_injective :
    Function.Injective (algebraMap W.CoordinateRingAtInfinity W.LocalRingAtInfinity) :=
  IsLocalization.injective (M := W.maximalIdealAtInfinity.primeCompl) W.LocalRingAtInfinity
    (Ideal.primeCompl_le_nonZeroDivisors _)

/-- The coordinate `z` is nonzero in the local ring at infinity. -/
theorem algebraMap_zAtInfinity_ne_zero :
    algebraMap _ W.LocalRingAtInfinity W.zAtInfinity ≠ 0 :=
  (map_ne_zero_iff _ W.algebraMap_localRingAtInfinity_injective).mpr W.zAtInfinity_ne_zero

/-- **The maximal ideal at infinity is principal.** Let `W` be a Weierstrass curve over a field
`F`. The maximal ideal of the local ring `𝒪 = (B_W)_(z, w)` at the point at infinity is
generated by `z`: it is generated by `z` and `w`, and `w = z³ v` with `v` a unit.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Theorem 2.8, p. 4. The
source assumes `Δ_W ≠ 0`, which is not used. -/
theorem maximalIdeal_localRingAtInfinity :
    maximalIdeal W.LocalRingAtInfinity =
      Ideal.span {algebraMap _ W.LocalRingAtInfinity W.zAtInfinity} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W.maximalIdealAtInfinity,
    congrArg (Ideal.map (algebraMap _ W.LocalRingAtInfinity)) W.maximalIdealAtInfinity_eq_span,
    Ideal.map_span, Set.image_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact Ideal.subset_span rfl
    · rw [SetLike.mem_coe, Ideal.mem_span_singleton, algebraMap_wAtInfinity_eq]
      exact Dvd.intro (algebraMap _ _ W.zAtInfinity ^ 2 * ↑W.unitInvAtInfinity) (by ring)
  · exact Ideal.span_mono (by simp)

/-- **The local ring at infinity is a discrete valuation ring.** Let `W` be a Weierstrass curve
over a field `F`. The local ring `𝒪 = (B_W)_(z, w)` at the point at infinity is a discrete
valuation ring: it is a Noetherian local domain whose maximal ideal is generated by the nonzero
element `z` (`maximalIdeal_localRingAtInfinity`). The source assumes `Δ_W ≠ 0`, which is not
used: the point at infinity is nonsingular on every Weierstrass cubic.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34; B. Conrad, *Minimal models for
elliptic curves*, 2015, <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of
Theorem 2.8, p. 4; the Stacks project, Lemma 10.119.7,
<https://stacks.math.columbia.edu/tag/00PD>. -/
instance : IsDiscreteValuationRing W.LocalRingAtInfinity := by
  have hne : maximalIdeal W.LocalRingAtInfinity ≠ ⊥ := by
    rw [maximalIdeal_localRingAtInfinity, Ne, Ideal.span_singleton_eq_bot]
    exact W.algebraMap_zAtInfinity_ne_zero
  exact ((IsDiscreteValuationRing.TFAE _
    fun h ↦ hne (isField_iff_maximalIdeal_eq.mp h)).out 1 5).mpr
    (⟨⟨_, W.maximalIdeal_localRingAtInfinity⟩⟩ :
      (maximalIdeal W.LocalRingAtInfinity).IsPrincipal)

/-- **`z` is a uniformizer at infinity.** Let `W` be a Weierstrass curve over a field `F`. The
coordinate `z = X / Y` is irreducible, that is a uniformizer, in the discrete valuation ring
`𝒪 = (B_W)_(z, w)` at the point at infinity.

Source: B. Conrad, *Minimal models for elliptic curves*, 2015,
<http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>, proof of Theorem 2.8, p. 4. The
source assumes `Δ_W ≠ 0`, which is not used. -/
theorem irreducible_zAtInfinity :
    Irreducible (algebraMap _ W.LocalRingAtInfinity W.zAtInfinity) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := W.LocalRingAtInfinity) _).mpr
    W.maximalIdeal_localRingAtInfinity

/-- **`ord_O z = 1`.** Let `W` be a Weierstrass curve over a field `F`. The additive valuation
of the discrete valuation ring `𝒪` at the point at infinity takes the value `1` at `z`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem addVal_zAtInfinity :
    IsDiscreteValuationRing.addVal W.LocalRingAtInfinity
      (algebraMap _ _ W.zAtInfinity) = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer W.irreducible_zAtInfinity

/-- **`ord_O w = 3`.** Let `W` be a Weierstrass curve over a field `F`. The additive valuation
of the discrete valuation ring `𝒪` at the point at infinity takes the value `3` at `w`, since
`w = z³ v` with `v` a unit.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem addVal_wAtInfinity :
    IsDiscreteValuationRing.addVal W.LocalRingAtInfinity
      (algebraMap _ _ W.wAtInfinity) = 3 := by
  rw [algebraMap_wAtInfinity_eq, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, addVal_zAtInfinity,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero]
  rfl

/-! ### The common function field -/

/-- The image of `y` in the function field `Frac(A_W)` is a unit. -/
theorem isUnit_algebraMap_affineY :
    IsUnit (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField W.affineY) :=
  isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr W.affineY_ne_zero)

/-- The map `B_W[1 / w] → Frac(A_W)`: the inverse of `A_W[1 / y] ≃ B_W[1 / w]` followed by the
map `A_W[1 / y] → Frac(A_W)`. It sends `z ↦ x / y` and `w ↦ 1 / y`. -/
noncomputable def awayWToFunctionField : W.AtInfinityAwayW →+* W.toAffine.FunctionField :=
  (IsLocalization.Away.lift W.affineY W.isUnit_algebraMap_affineY).comp
    W.awayYEquivAwayW.symm.toRingEquiv.toRingHom

/-- The map `B_W[1 / w] → Frac(A_W)` composed with `A_W → A_W[1 / y] ≃ B_W[1 / w]` is the map
`A_W → Frac(A_W)`. -/
theorem awayWToFunctionField_awayYEquivAwayW_algebraMap (a : W.toAffine.CoordinateRing) :
    W.awayWToFunctionField (W.awayYEquivAwayW (algebraMap _ _ a)) =
      algebraMap _ W.toAffine.FunctionField a := by
  simp only [awayWToFunctionField, RingHom.comp_apply]
  change IsLocalization.Away.lift W.affineY W.isUnit_algebraMap_affineY
    (W.awayYEquivAwayW.symm (W.awayYEquivAwayW (algebraMap _ _ a))) = _
  rw [AlgEquiv.symm_apply_apply, IsLocalization.Away.lift_eq]

/-- The map `B_W[1 / w] → Frac(A_W)` is injective. -/
theorem awayWToFunctionField_injective : Function.Injective W.awayWToFunctionField := by
  have h : Function.Injective (IsLocalization.Away.lift (S := W.AffineAwayY) W.affineY
      W.isUnit_algebraMap_affineY) := by
    unfold IsLocalization.Away.lift
    refine (IsLocalization.lift_injective_iff _).mpr fun a b ↦ ?_
    exact (IsLocalization.injective _ W.powers_affineY_le_nonZeroDivisors).eq_iff.trans
      (IsFractionRing.injective _ _).eq_iff.symm
  intro a b hab
  exact W.awayYEquivAwayW.symm.injective (h hab)

/-- `Frac(A_W)` is a `B_W`-algebra through `B_W → B_W[1 / w] → Frac(A_W)`, `z ↦ x / y`,
`w ↦ 1 / y`. -/
noncomputable instance : Algebra W.CoordinateRingAtInfinity W.toAffine.FunctionField :=
  (W.awayWToFunctionField.comp (algebraMap _ W.AtInfinityAwayW)).toAlgebra

/-- The map `B_W → Frac(A_W)` factors through `B_W[1 / w]`. -/
theorem algebraMap_atInfinity_functionField (b : W.CoordinateRingAtInfinity) :
    algebraMap _ W.toAffine.FunctionField b = W.awayWToFunctionField (algebraMap _ _ b) :=
  rfl

/-- The map `B_W → Frac(A_W)` is injective. -/
theorem algebraMap_atInfinity_functionField_injective :
    Function.Injective (algebraMap W.CoordinateRingAtInfinity W.toAffine.FunctionField) :=
  W.awayWToFunctionField_injective.comp W.algebraMap_atInfinityAwayW_injective

/-- The image of `w` in `Frac(A_W)` is nonzero. -/
theorem algebraMap_wAtInfinity_ne_zero :
    algebraMap _ W.toAffine.FunctionField W.wAtInfinity ≠ 0 :=
  (map_ne_zero_iff _ W.algebraMap_atInfinity_functionField_injective).mpr
    (nonZeroDivisors.ne_zero W.wAtInfinity_mem_nonZeroDivisors)

/-- Every element `a` of `A_W` satisfies `a wⁿ = b` in `Frac(A_W)` for some `b ∈ B_W` and
`n ∈ ℕ`. -/
theorem exists_algebraMap_mul_pow_eq (a : W.toAffine.CoordinateRing) :
    ∃ (b : W.CoordinateRingAtInfinity) (n : ℕ),
      algebraMap _ W.toAffine.FunctionField a *
        algebraMap _ W.toAffine.FunctionField W.wAtInfinity ^ n =
      algebraMap _ W.toAffine.FunctionField b := by
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers W.wAtInfinity)
    (W.awayYEquivAwayW (algebraMap _ W.AffineAwayY a))
  obtain ⟨n, hn⟩ := s.2
  refine ⟨b, n, ?_⟩
  have h := congrArg W.awayWToFunctionField hs
  rw [map_mul, awayWToFunctionField_awayYEquivAwayW_algebraMap] at h
  rw [algebraMap_atInfinity_functionField, algebraMap_atInfinity_functionField, ← map_pow,
    ← map_pow, show W.wAtInfinity ^ n = s from hn]
  exact h

/-- **`A_W` and `B_W` have the same fraction field.** Let `W` be a Weierstrass curve over a
field `F`. The function field `Frac(A_W)` of the affine chart is a fraction field of the
coordinate ring at infinity `B_W`, through `B_W → B_W[1 / w] ≃ A_W[1 / y] → Frac(A_W)`,
`z ↦ x / y`, `w ↦ 1 / y`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34. -/
instance : IsFractionRing W.CoordinateRingAtInfinity W.toAffine.FunctionField := by
  have : FaithfulSMul W.CoordinateRingAtInfinity W.toAffine.FunctionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      W.algebraMap_atInfinity_functionField_injective
  refine IsFractionRing.of_field _ _ fun k ↦ ?_
  obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) k
  obtain ⟨b₁, n₁, h₁⟩ := W.exists_algebraMap_mul_pow_eq a₁
  obtain ⟨b₂, n₂, h₂⟩ := W.exists_algebraMap_mul_pow_eq a₂
  refine ⟨b₁ * W.wAtInfinity ^ n₂, b₂ * W.wAtInfinity ^ n₁, ?_⟩
  have hw := W.algebraMap_wAtInfinity_ne_zero
  have ha : algebraMap _ W.toAffine.FunctionField a₂ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha₂
  rw [map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
  field_simp

/-- The elements of `B_W` outside the ideal of the point at infinity become units in
`Frac(A_W)`. -/
theorem isUnit_algebraMap_functionField_of_mem_primeCompl
    (s : W.maximalIdealAtInfinity.primeCompl) :
    IsUnit (algebraMap W.CoordinateRingAtInfinity W.toAffine.FunctionField s) := by
  refine isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ W.algebraMap_atInfinity_functionField_injective).mpr ?_)
  intro h
  exact s.2 (h ▸ Ideal.zero_mem _)

/-- `Frac(A_W)` is an algebra over the local ring `𝒪` at infinity, through the map
`𝒪 = (B_W)_(z, w) → Frac(A_W)` extending `B_W → Frac(A_W)`. -/
noncomputable instance : Algebra W.LocalRingAtInfinity W.toAffine.FunctionField :=
  (IsLocalization.lift (M := W.maximalIdealAtInfinity.primeCompl) (S := W.LocalRingAtInfinity)
    W.isUnit_algebraMap_functionField_of_mem_primeCompl).toAlgebra

/-- The maps `B_W → 𝒪 → Frac(A_W)` and `B_W → Frac(A_W)` agree. -/
instance : IsScalarTower W.CoordinateRingAtInfinity W.LocalRingAtInfinity
    W.toAffine.FunctionField := by
  refine ⟨fun b o k ↦ ?_⟩
  have h : b • o = algebraMap W.CoordinateRingAtInfinity W.LocalRingAtInfinity b * o :=
    Algebra.smul_def b o
  rw [h, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  congr 1
  exact IsLocalization.lift_eq (M := W.maximalIdealAtInfinity.primeCompl)
    (S := W.LocalRingAtInfinity) W.isUnit_algebraMap_functionField_of_mem_primeCompl b

/-- **The local ring at infinity has fraction field `Frac(A_W)`.** Let `W` be a Weierstrass
curve over a field `F`. The function field `Frac(A_W)` of the affine chart is a fraction field
of the local ring `𝒪 = (B_W)_(z, w)` at the point at infinity. The source assumes `Δ_W ≠ 0`,
which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 34. -/
instance : IsFractionRing W.LocalRingAtInfinity W.toAffine.FunctionField :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization W.maximalIdealAtInfinity.primeCompl
    W.LocalRingAtInfinity W.toAffine.FunctionField

/-- **`x = z / w`.** Let `W` be a Weierstrass curve over a field `F`. In the function field
`Frac(A_W)`, the affine coordinate `x = X / Z` equals `z / w`, for `z = X / Y` and `w = Z / Y`. -/
theorem algebraMap_affineX_eq :
    algebraMap _ W.toAffine.FunctionField W.affineX =
      algebraMap _ W.toAffine.FunctionField W.zAtInfinity /
        algebraMap _ W.toAffine.FunctionField W.wAtInfinity := by
  rw [eq_div_iff W.algebraMap_wAtInfinity_ne_zero,
    ← W.awayWToFunctionField_awayYEquivAwayW_algebraMap, awayYEquivAwayW_affineX,
    algebraMap_atInfinity_functionField, algebraMap_atInfinity_functionField, map_mul, mul_assoc,
    ← map_mul, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf,
    map_one, mul_one]

/-- **`y = 1 / w`.** Let `W` be a Weierstrass curve over a field `F`. In the function field
`Frac(A_W)`, the affine coordinate `y = Y / Z` equals `w⁻¹`, for `w = Z / Y`. -/
theorem algebraMap_affineY_eq :
    algebraMap _ W.toAffine.FunctionField W.affineY =
      (algebraMap _ W.toAffine.FunctionField W.wAtInfinity)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← W.awayWToFunctionField_awayYEquivAwayW_algebraMap, awayYEquivAwayW_affineY,
    algebraMap_atInfinity_functionField, ← map_mul, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, map_one]

/-- **`x z² = u`.** Let `W` be a Weierstrass curve over a field `F`. In the function field
`Frac(A_W)`,

$$x z^2 = 1 + a_1 z + a_3 w - a_2 z^2 - a_4 z w - a_6 w^2,$$

and the right side (`unitAtInfinity`) is a unit of the local ring at infinity
(`isUnit_algebraMap_unitAtInfinity`); so `x = z⁻² · (unit of 𝒪)`, that is `ord_O x = -2`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem algebraMap_affineX_mul_zAtInfinity_pow_two :
    algebraMap _ W.toAffine.FunctionField W.affineX *
        algebraMap _ W.toAffine.FunctionField W.zAtInfinity ^ 2 =
      algebraMap _ W.toAffine.FunctionField W.unitAtInfinity := by
  have h := congrArg (algebraMap _ W.toAffine.FunctionField) W.wAtInfinity_mul_unitAtInfinity
  rw [map_mul, map_pow] at h
  have hw := W.algebraMap_wAtInfinity_ne_zero
  rw [algebraMap_affineX_eq, div_mul_eq_mul_div, div_eq_iff hw, ← pow_succ', ← h, mul_comm]

/-- **`y z³ = u`.** Let `W` be a Weierstrass curve over a field `F`. In the function field
`Frac(A_W)`,

$$y z^3 = 1 + a_1 z + a_3 w - a_2 z^2 - a_4 z w - a_6 w^2,$$

and the right side (`unitAtInfinity`) is a unit of the local ring at infinity
(`isUnit_algebraMap_unitAtInfinity`); so `y = z⁻³ · (unit of 𝒪)`, that is `ord_O y = -3`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem algebraMap_affineY_mul_zAtInfinity_pow_three :
    algebraMap _ W.toAffine.FunctionField W.affineY *
        algebraMap _ W.toAffine.FunctionField W.zAtInfinity ^ 3 =
      algebraMap _ W.toAffine.FunctionField W.unitAtInfinity := by
  have h := congrArg (algebraMap _ W.toAffine.FunctionField) W.wAtInfinity_mul_unitAtInfinity
  rw [map_mul, map_pow] at h
  have hw := W.algebraMap_wAtInfinity_ne_zero
  rw [algebraMap_affineY_eq, ← h, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]

/-! ### The valuation at infinity -/

/-- The point at infinity as a height one prime of the discrete valuation ring `𝒪`: its maximal
ideal, which is nonzero. -/
noncomputable def placeAtInfinity : IsDedekindDomain.HeightOneSpectrum W.LocalRingAtInfinity where
  asIdeal := maximalIdeal _
  isPrime := inferInstance
  ne_bot := by
    rw [maximalIdeal_localRingAtInfinity, Ne, Ideal.span_singleton_eq_bot]
    exact W.algebraMap_zAtInfinity_ne_zero

/-- **The valuation at the point at infinity.** For a Weierstrass curve `W` over a field `F`,
this is the valuation `v_O` of the function field `Frac(A_W)` with values in `ℤᵐ⁰` attached to
the discrete valuation ring `𝒪` at the point at infinity (Mathlib's adic valuation). It is
multiplicative: `v_O f = exp (-ord_O f)`, so `v_O z = exp (-1)`. -/
noncomputable def valuationAtInfinity :
    Valuation W.toAffine.FunctionField (WithZero (Multiplicative ℤ)) :=
  W.placeAtInfinity.valuation W.toAffine.FunctionField

/-- A unit of `𝒪` has valuation `1` at infinity. -/
theorem valuationAtInfinity_algebraMap_localRing_of_isUnit {o : W.LocalRingAtInfinity}
    (ho : IsUnit o) : W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField o) = 1 := by
  rw [valuationAtInfinity, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal.mpr ho

/-- An element of `B_W` not vanishing at the point at infinity has valuation `1` there. -/
theorem valuationAtInfinity_algebraMap_of_notMem {b : W.CoordinateRingAtInfinity}
    (hb : b ∉ W.maximalIdealAtInfinity) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField b) = 1 := by
  rw [IsScalarTower.algebraMap_apply W.CoordinateRingAtInfinity W.LocalRingAtInfinity]
  exact W.valuationAtInfinity_algebraMap_localRing_of_isUnit
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hb)

/-- **`ord_O z = 1`.** Let `W` be a Weierstrass curve over a field `F`. The valuation at the
point at infinity of `z = X / Y` is `exp (-1)`, that is `ord_O z = 1`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem valuationAtInfinity_zAtInfinity :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField W.zAtInfinity) =
      WithZero.exp (-1) := by
  rw [IsScalarTower.algebraMap_apply W.CoordinateRingAtInfinity W.LocalRingAtInfinity,
    valuationAtInfinity, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    W.algebraMap_zAtInfinity_ne_zero W.maximalIdeal_localRingAtInfinity

/-- **`ord_O w = 3`.** Let `W` be a Weierstrass curve over a field `F`. The valuation at the
point at infinity of `w = Z / Y` is `exp (-3)`, that is `ord_O w = 3`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem valuationAtInfinity_wAtInfinity :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField W.wAtInfinity) =
      WithZero.exp (-3) := by
  rw [IsScalarTower.algebraMap_apply W.CoordinateRingAtInfinity W.LocalRingAtInfinity,
    algebraMap_wAtInfinity_eq, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
    ← IsScalarTower.algebraMap_apply, valuationAtInfinity_zAtInfinity,
    W.valuationAtInfinity_algebraMap_localRing_of_isUnit (Units.isUnit _), mul_one,
    ← WithZero.exp_nsmul]
  norm_num

/-- **`ord_O x = -2`.** Let `W` be a Weierstrass curve over a field `F`. The valuation at the
point at infinity of the affine coordinate `x = X / Z` is `exp 2`, that is `x` has a pole of
order `2` at `O`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem valuationAtInfinity_affineX :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField W.affineX) = WithZero.exp 2 := by
  rw [algebraMap_affineX_eq, map_div₀, valuationAtInfinity_zAtInfinity,
    valuationAtInfinity_wAtInfinity, ← WithZero.exp_sub]
  norm_num

/-- **`ord_O y = -3`.** Let `W` be a Weierstrass curve over a field `F`. The valuation at the
point at infinity of the affine coordinate `y = Y / Z` is `exp 3`, that is `y` has a pole of
order `3` at `O`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. The source assumes
`Δ_W ≠ 0`, which is not used. -/
theorem valuationAtInfinity_affineY :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField W.affineY) = WithZero.exp 3 := by
  rw [algebraMap_affineY_eq, map_inv₀, valuationAtInfinity_wAtInfinity, ← WithZero.exp_neg]
  norm_num

/-! ### Regular functions on the projective cubic are constant -/

/-- Let `g : F[X] → K` be a ring map to a field with a valuation `v` in `ℤᵐ⁰`, such that the
nonzero constants have valuation `1` and `v (g X) = exp k` with `k > 0`. Then
`v (g p) = exp (k deg p)` for every nonzero polynomial `p`. -/
private lemma valuation_map_polynomial {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (g : F[X] →+* K)
    (hC : ∀ c : F, c ≠ 0 → v (g (C c)) = 1) {k : ℤ} (hX : v (g X) = WithZero.exp k)
    (hk : 0 < k) {p : F[X]} (hp : p ≠ 0) :
    v (g p) = WithZero.exp (p.natDegree * k) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    have hlead : v (g (C p.leadingCoeff * X ^ p.natDegree)) = WithZero.exp (n * k) := by
      rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
        hC _ (leadingCoeff_ne_zero.mpr hp), one_mul, hX, ← WithZero.exp_nsmul, hn, nsmul_eq_mul]
    conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow]
    by_cases he : p.eraseLead = 0
    · rw [he, zero_add, hlead]
    · have hlt : p.eraseLead.natDegree < n :=
        hn ▸ p.eraseLead_natDegree_lt_or_eraseLead_eq_zero.resolve_right he
      rw [map_add, Valuation.map_add_eq_of_lt_right, hlead]
      rw [hlead, ih _ hlt he rfl, WithZero.exp_lt_exp]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hlt) hk

/-- The constant polynomial `c` in `x` is the constant `c` of `A_W`. -/
private lemma of_C_eq (c : F) :
    AdjoinRoot.of W.toAffine.polynomial (C c) = algebraMap F W.toAffine.CoordinateRing c := by
  simp [IsScalarTower.algebraMap_apply F F[X] (AdjoinRoot _), AdjoinRoot.algebraMap_eq]

/-- A nonzero constant `c ∈ F` has valuation `1` at the point at infinity. -/
theorem valuationAtInfinity_algebraMap_constant {c : F} (hc : c ≠ 0) :
    W.valuationAtInfinity
      (algebraMap _ W.toAffine.FunctionField (algebraMap F W.toAffine.CoordinateRing c)) = 1 := by
  rw [← W.awayWToFunctionField_awayYEquivAwayW_algebraMap,
    ← IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing W.AffineAwayY,
    AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply F W.CoordinateRingAtInfinity W.AtInfinityAwayW,
    ← algebraMap_atInfinity_functionField]
  refine W.valuationAtInfinity_algebraMap_of_notMem ?_
  simpa [maximalIdealAtInfinity] using hc

/-- **Regular functions on a projective Weierstrass cubic are constant.** Let `W` be a
Weierstrass curve over a field `F` and let `f ∈ A_W`. If the valuation at the point at infinity
of `f` is at most `1`, that is `f` has no pole at `O`, then `f` is a constant `c ∈ F`.

Writing `f = p(x) + q(x) y` with `p, q ∈ F[x]`, the two terms have valuations
`exp (2 deg p)` and `exp (2 deg q + 3)` when nonzero; these differ by parity, so `q = 0` and
`deg p = 0`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 31 ("only the constant functions are
without zeros and poles"), and Chapter II, §1, p. 47 (`x` and `y` have poles of order `2` and
`3` at `O` and no other poles). -/
theorem exists_eq_algebraMap_of_valuationAtInfinity_le_one (f : W.toAffine.CoordinateRing)
    (hf : W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField f) ≤ 1) :
    ∃ c : F, f = algebraMap F _ c := by
  obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq f
  set g : F[X] →+* W.toAffine.FunctionField :=
    (algebraMap _ W.toAffine.FunctionField).comp (AdjoinRoot.of W.toAffine.polynomial) with hg
  have hC : ∀ c : F, c ≠ 0 → W.valuationAtInfinity (g (C c)) = 1 := fun c hc ↦ by
    rw [hg, RingHom.comp_apply, W.of_C_eq]
    exact W.valuationAtInfinity_algebraMap_constant hc
  have hX : W.valuationAtInfinity (g X) = WithZero.exp 2 := W.valuationAtInfinity_affineX
  have hsum : algebraMap _ W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • Affine.CoordinateRing.mk W.toAffine X) =
        g p + g q * algebraMap _ W.toAffine.FunctionField W.affineY := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul, AdjoinRoot.algebraMap_eq]
    rfl
  rw [hsum] at hf
  have hy := W.valuationAtInfinity_affineY
  have hq : q = 0 := by
    by_contra hq
    have hvq : W.valuationAtInfinity (g q * algebraMap _ _ W.affineY) =
        WithZero.exp ((q.natDegree : ℤ) * 2 + 3) := by
      rw [Valuation.map_mul, valuation_map_polynomial _ g hC hX (by norm_num) hq, hy,
        ← WithZero.exp_add]
    have hbig : 1 < W.valuationAtInfinity (g q * algebraMap _ _ W.affineY) := by
      rw [hvq, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      positivity
    by_cases hp : p = 0
    · rw [hp, map_zero, zero_add] at hf
      exact absurd hf (not_le.mpr hbig)
    · have hvp := valuation_map_polynomial _ g hC hX (by norm_num) hp
      have hne : W.valuationAtInfinity (g p) ≠
          W.valuationAtInfinity (g q * algebraMap _ _ W.affineY) := by
        rw [hvp, hvq, Ne, WithZero.exp_inj]
        omega
      rw [Valuation.map_add_of_distinct_val _ hne] at hf
      exact absurd (le_trans (le_max_right _ _) hf) (not_le.mpr hbig)
  subst hq
  rw [map_zero, zero_mul, add_zero] at hf
  refine ⟨p.coeff 0, ?_⟩
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one, AdjoinRoot.algebraMap_eq]
  by_cases hp : p = 0
  · simp [hp]
  · have hvp := valuation_map_polynomial _ g hC hX (by norm_num) hp
    rw [hvp, ← WithZero.exp_zero, WithZero.exp_le_exp] at hf
    have hd : p.natDegree = 0 := by omega
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    exact W.of_C_eq _

/-- **Functions on `A_W` regular at infinity are constant.** Let `W` be a Weierstrass curve over
a field `F` and let `f ∈ A_W`. If the image of `f` in the common function field `Frac(A_W)` lies
in the image of the local ring `𝒪` at the point at infinity, then `f` is a constant `c ∈ F`.
The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter I, §4, p. 31 ("only the constant functions are
without zeros and poles"). -/
theorem exists_eq_algebraMap_of_mem_range (f : W.toAffine.CoordinateRing)
    (hf : algebraMap _ W.toAffine.FunctionField f ∈
      Set.range (algebraMap W.LocalRingAtInfinity W.toAffine.FunctionField)) :
    ∃ c : F, f = algebraMap F _ c := by
  obtain ⟨o, ho⟩ := hf
  refine W.exists_eq_algebraMap_of_valuationAtInfinity_le_one f ?_
  rw [← ho, valuationAtInfinity]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _

end WeierstrassCurve
