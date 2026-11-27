/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.LocalRingAtInfinity
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Positivity

/-!
# Functions with a pole of order at most three at infinity

Let `W` be a Weierstrass curve over a field `F`, with affine coordinate ring
`A_W = F[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)`, and let `v_O` be the valuation
of the function field at the point at infinity `O` (`WeierstrassCurve.valuationAtInfinity`, with
values in `ℤᵐ⁰`, so `v_O f = exp (-ord_O f)`). This file proves:

* every `f ∈ A_W` is `p(x) + q(x) y` for unique `p, q ∈ F[x]` (over any commutative ring;
  `WeierstrassCurve.existsUnique_eq_add_mul_affineY`);
* `v_O (p(x) + q(x) y) = max (exp (2 deg p)) (exp (2 deg q + 3))`, a term being `0` when its
  polynomial is `0` (`WeierstrassCurve.valuationAtInfinity_add_mul_affineY`), that is
  `ord_O f = -max (2 deg p, 2 deg q + 3)` for `f ≠ 0`;
* `ord_O f ≥ -2` exactly for `f ∈ F + F x`, and `ord_O f ≥ -3` exactly for
  `f ∈ F + F x + F y`; `ord_O (r + u x) = -2` exactly when `u ≠ 0`, and
  `ord_O (t + s x + u y) = -3` exactly when `u ≠ 0`.

The source assumes `Δ_W ≠ 0`; nothing here uses it.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47 (the bases `{1, x}` and
  `{1, x, y}` of `L(2[O])` and `L(3[O])`), and proof of Theorem 2.1(b), p. 50.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The element `p • 1 + q • y` of `A_W` is `p(x) + q(x) y`. -/
private lemma smul_basis_eq (p q : R[X]) :
    p • (1 : W.toAffine.CoordinateRing) + q • Affine.CoordinateRing.mk W.toAffine X =
      AdjoinRoot.of W.toAffine.polynomial p +
        AdjoinRoot.of W.toAffine.polynomial q * W.affineY := by
  rw [Algebra.smul_def, Algebra.smul_def, mul_one, AdjoinRoot.algebraMap_eq]
  rfl

/-- **The decomposition `f = p(x) + q(x) y`.** Let `W` be a Weierstrass curve over a commutative
ring `R`. Every element `f` of the affine coordinate ring `A_W` is `p(x) + q(x) y` for a unique pair
of polynomials `p, q ∈ R[x]`. This restates Mathlib's basis `{1, y}` of `A_W` over `R[x]`
(`WeierstrassCurve.Affine.CoordinateRing.basis`). The source works over a field with `Δ_W ≠ 0`;
neither is used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. -/
theorem existsUnique_eq_add_mul_affineY (f : W.toAffine.CoordinateRing) :
    ∃! pq : R[X] × R[X], AdjoinRoot.of W.toAffine.polynomial pq.1 +
      AdjoinRoot.of W.toAffine.polynomial pq.2 * W.affineY = f := by
  obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq f
  refine ⟨(p, q), (W.smul_basis_eq p q).symm, fun ⟨p', q'⟩ h ↦ ?_⟩
  dsimp only at h
  rw [← smul_basis_eq, ← sub_eq_zero] at h
  have h' : (p' - p) • (1 : W.toAffine.CoordinateRing) +
      (q' - q) • Affine.CoordinateRing.mk W.toAffine X = 0 := by
    rw [← h, sub_smul, sub_smul]; abel
  obtain ⟨hp, hq⟩ := Affine.CoordinateRing.smul_basis_eq_zero h'
  rw [sub_eq_zero] at hp hq
  rw [hp, hq]

end CommRing

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

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

private lemma of_C_eq (c : F) :
    AdjoinRoot.of W.toAffine.polynomial (C c) = algebraMap F W.toAffine.CoordinateRing c := by
  simp [IsScalarTower.algebraMap_apply F F[X] (AdjoinRoot _), AdjoinRoot.algebraMap_eq]

private lemma of_X_eq : AdjoinRoot.of W.toAffine.polynomial X = W.affineX := rfl

open scoped Classical in
/-- **`ord_O p(x) = -2 deg p`.** Let `W` be a Weierstrass curve over a field `F` and let
`p ∈ F[x]`. The valuation at the point at infinity of `p(x) ∈ A_W` is `0` if `p = 0` and
`exp (2 deg p)` otherwise, since `ord_O x = -2` and nonzero constants have valuation `1`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. -/
theorem valuationAtInfinity_polynomial (p : F[X]) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (AdjoinRoot.of W.toAffine.polynomial p)) =
      if p = 0 then 0 else WithZero.exp (2 * (p.natDegree : ℤ)) := by
  split_ifs with hp
  · simp [hp]
  · rw [← RingHom.comp_apply, valuation_map_polynomial _ _ (fun c hc ↦ ?_) ?_ two_pos hp, mul_comm]
    · exact W.valuationAtInfinity_affineX
    · rw [RingHom.comp_apply, W.of_C_eq]
      exact W.valuationAtInfinity_algebraMap_constant hc

open scoped Classical in
/-- **`ord_O (q(x) y) = -2 deg q - 3`.** Let `W` be a Weierstrass curve over a field `F` and let
`q ∈ F[x]`. The valuation at the point at infinity of `q(x) y ∈ A_W` is `0` if `q = 0` and
`exp (2 deg q + 3)` otherwise, since `ord_O y = -3`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. -/
theorem valuationAtInfinity_polynomial_mul_affineY (q : F[X]) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (AdjoinRoot.of W.toAffine.polynomial q * W.affineY)) =
      if q = 0 then 0 else WithZero.exp (2 * (q.natDegree : ℤ) + 3) := by
  rw [map_mul, Valuation.map_mul, valuationAtInfinity_polynomial, valuationAtInfinity_affineY]
  split_ifs <;> simp [← WithZero.exp_add]

open scoped Classical in
/-- **The pole order of `p(x) + q(x) y` at infinity.** Let `W` be a Weierstrass curve over a field
`F` and let `p, q ∈ F[x]`. The valuation at the point at infinity of `f = p(x) + q(x) y ∈ A_W` is
the maximum of `exp (2 deg p)` (read as `0` when `p = 0`) and `exp (2 deg q + 3)` (read as `0`
when `q = 0`). Since `v_O = exp (-ord_O)`, for `f ≠ 0` this is
`ord_O f = -max (2 deg p, 2 deg q + 3)` with `deg 0 = -∞`: the two terms have orders of different
parity. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. -/
theorem valuationAtInfinity_add_mul_affineY (p q : F[X]) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (AdjoinRoot.of W.toAffine.polynomial p + AdjoinRoot.of W.toAffine.polynomial q * W.affineY)) =
      max (if p = 0 then 0 else WithZero.exp (2 * (p.natDegree : ℤ)))
        (if q = 0 then 0 else WithZero.exp (2 * (q.natDegree : ℤ) + 3)) := by
  rw [← W.valuationAtInfinity_polynomial p, ← W.valuationAtInfinity_polynomial_mul_affineY q,
    map_add]
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  refine Valuation.map_add_of_distinct_val _ ?_
  rw [valuationAtInfinity_polynomial, valuationAtInfinity_polynomial_mul_affineY]
  simp only [hp, hq, ↓reduceIte, Ne, WithZero.exp_inj]
  omega


private lemma ite_le_exp_iff {P : Prop} [Decidable P] {a k : ℤ} :
    (if P then (0 : WithZero (Multiplicative ℤ)) else WithZero.exp a) ≤ WithZero.exp k ↔
      P ∨ a ≤ k := by
  split_ifs with h <;> simp [h, WithZero.exp_le_exp]

/-- **Bounding the pole order of `p(x) + q(x) y`.** Let `W` be a Weierstrass curve over a field
`F`, let `p, q ∈ F[x]` and `k ∈ ℤ`. Then `v_O (p(x) + q(x) y) ≤ exp k`, that is
`ord_O (p(x) + q(x) y) ≥ -k`, if and only if `p = 0` or `2 deg p ≤ k`, and `q = 0` or
`2 deg q + 3 ≤ k`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47. -/
theorem valuationAtInfinity_add_mul_affineY_le_exp_iff (p q : F[X]) (k : ℤ) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (AdjoinRoot.of W.toAffine.polynomial p + AdjoinRoot.of W.toAffine.polynomial q * W.affineY)) ≤
        WithZero.exp k ↔
      (p = 0 ∨ 2 * (p.natDegree : ℤ) ≤ k) ∧ (q = 0 ∨ 2 * (q.natDegree : ℤ) + 3 ≤ k) := by
  classical
  rw [valuationAtInfinity_add_mul_affineY, max_le_iff, ite_le_exp_iff, ite_le_exp_iff]

private lemma of_linear (r u : F) :
    AdjoinRoot.of W.toAffine.polynomial (C u * X + C r) =
      algebraMap F _ r + algebraMap F _ u * W.affineX := by
  rw [map_add, map_mul, of_C_eq, of_C_eq, of_X_eq, add_comm]

private lemma eq_add_zero_mul (a : W.toAffine.CoordinateRing) :
    a = a + AdjoinRoot.of W.toAffine.polynomial 0 * W.affineY := by
  simp

/-- **Functions with a pole of order at most two at infinity.** Let `W` be a Weierstrass curve
over a field `F` and let `f ∈ A_W`. Then `v_O f ≤ exp 2`, that is `ord_O f ≥ -2`, if and only if
`f = r + u x` for some `r, u ∈ F`: the elements of `A_W` with `ord_O ≥ -2` form `F + F x`. The
source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47
(the basis `{1, x}` of `L(2[O])`). -/
theorem valuationAtInfinity_le_exp_two_iff (f : W.toAffine.CoordinateRing) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField f) ≤ WithZero.exp 2 ↔
      ∃ r u : F, f = algebraMap F _ r + algebraMap F _ u * W.affineX := by
  constructor
  · obtain ⟨⟨p, q⟩, rfl, -⟩ := W.existsUnique_eq_add_mul_affineY f
    dsimp only
    rw [valuationAtInfinity_add_mul_affineY_le_exp_iff]
    rintro ⟨hp, hq⟩
    have hq : q = 0 := hq.resolve_right (by omega)
    have hp : p.natDegree ≤ 1 := by
      rcases hp with hp | hp
      · simp [hp]
      · omega
    refine ⟨p.coeff 0, p.coeff 1, ?_⟩
    rw [hq, map_zero, zero_mul, add_zero, ← of_linear, ← eq_X_add_C_of_natDegree_le_one hp]
  · rintro ⟨r, u, rfl⟩
    rw [← of_linear, W.eq_add_zero_mul (AdjoinRoot.of _ (C u * X + C r)),
      valuationAtInfinity_add_mul_affineY_le_exp_iff]
    refine ⟨Or.inr ?_, Or.inl rfl⟩
    have := natDegree_linear_le (a := u) (b := r)
    omega

/-- **Functions with a pole of order at most three at infinity.** Let `W` be a Weierstrass curve
over a field `F` and let `f ∈ A_W`. Then `v_O f ≤ exp 3`, that is `ord_O f ≥ -3`, if and only if
`f = t + s x + u y` for some `t, s, u ∈ F`: the elements of `A_W` with `ord_O ≥ -3` form
`F + F x + F y`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, §1, p. 47
(the basis `{1, x, y}` of `L(3[O])`). -/
theorem valuationAtInfinity_le_exp_three_iff (f : W.toAffine.CoordinateRing) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField f) ≤ WithZero.exp 3 ↔
      ∃ t s u : F,
        f = algebraMap F _ t + algebraMap F _ s * W.affineX + algebraMap F _ u * W.affineY := by
  constructor
  · obtain ⟨⟨p, q⟩, rfl, -⟩ := W.existsUnique_eq_add_mul_affineY f
    dsimp only
    rw [valuationAtInfinity_add_mul_affineY_le_exp_iff]
    rintro ⟨hp, hq⟩
    have hq : q.natDegree = 0 := by
      rcases hq with hq | hq
      · simp [hq]
      · omega
    have hp : p.natDegree ≤ 1 := by
      rcases hp with hp | hp
      · simp [hp]
      · omega
    refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_⟩
    rw [← of_linear, ← eq_X_add_C_of_natDegree_le_one hp, ← of_C_eq,
      ← eq_C_of_natDegree_eq_zero hq]
  · rintro ⟨t, s, u, rfl⟩
    rw [← of_linear, ← of_C_eq, valuationAtInfinity_add_mul_affineY_le_exp_iff]
    refine ⟨Or.inr ?_, Or.inr ?_⟩
    · have := natDegree_linear_le (a := s) (b := t)
      omega
    · simp

/-- **`r + u x` has a pole of order exactly two when `u ≠ 0`.** Let `W` be a Weierstrass curve
over a field `F` and let `r, u ∈ F`. Then `v_O (r + u x) = exp 2`, that is
`ord_O (r + u x) = -2`, if and only if `u ≠ 0`. The source assumes `Δ_W ≠ 0`, which is not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, proof of Theorem 2.1(b), p. 50
("`x ∘ φ = u₁ x' + r`"). -/
theorem valuationAtInfinity_add_mul_affineX_eq_exp_two_iff (r u : F) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (algebraMap F _ r + algebraMap F _ u * W.affineX)) = WithZero.exp 2 ↔ u ≠ 0 := by
  classical
  rw [← of_linear, W.eq_add_zero_mul (AdjoinRoot.of _ (C u * X + C r))]
  by_cases hu : u = 0
  · subst hu
    have h := (W.valuationAtInfinity_add_mul_affineY_le_exp_iff (C 0 * X + C r) 0 0).mpr
      ⟨Or.inr (by simp), Or.inl rfl⟩
    simp only [ne_eq, not_true_eq_false, iff_false]
    intro h'
    rw [h', WithZero.exp_le_exp] at h
    omega
  · have hd : (C u * X + C r).natDegree = 1 := natDegree_linear hu
    have hp : C u * X + C r ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
    rw [valuationAtInfinity_add_mul_affineY]
    simp [hp, hd, hu]

/-- **`t + s x + u y` has a pole of order exactly three when `u ≠ 0`.** Let `W` be a Weierstrass
curve over a field `F` and let `t, s, u ∈ F`. Then `v_O (t + s x + u y) = exp 3`, that is
`ord_O (t + s x + u y) = -3`, if and only if `u ≠ 0`. The source assumes `Δ_W ≠ 0`, which is
not used.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, proof of Theorem 2.1(b), p. 50
("`y ∘ φ = u₂ y' + s x' + t`"). -/
theorem valuationAtInfinity_add_mul_affineX_add_mul_affineY_eq_exp_three_iff (t s u : F) :
    W.valuationAtInfinity (algebraMap _ W.toAffine.FunctionField
      (algebraMap F _ t + algebraMap F _ s * W.affineX + algebraMap F _ u * W.affineY)) =
        WithZero.exp 3 ↔ u ≠ 0 := by
  classical
  rw [← of_linear, ← of_C_eq, valuationAtInfinity_add_mul_affineY]
  have hp : (if C s * X + C t = 0 then (0 : WithZero (Multiplicative ℤ)) else
      WithZero.exp (2 * ((C s * X + C t).natDegree : ℤ))) < WithZero.exp 3 := by
    split_ifs
    · exact WithZero.zero_lt_coe _
    · have := natDegree_linear_le (a := s) (b := t)
      rw [WithZero.exp_lt_exp]
      omega
  by_cases hu : u = 0
  · simp only [hu, map_zero, ↓reduceIte, ne_eq, not_true_eq_false, iff_false]
    rw [max_eq_left zero_le]
    exact hp.ne
  · simp only [map_eq_zero, hu, ↓reduceIte, natDegree_C, CharP.cast_eq_zero, mul_zero, zero_add,
      ne_eq, not_false_eq_true, iff_true]
    exact max_eq_right hp.le

end WeierstrassCurve
