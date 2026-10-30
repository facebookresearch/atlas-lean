/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Multiplicity of a polynomial at a point

The order of vanishing of a multivariate polynomial `F` at a point `v : σ → R` is the order at the
origin (Mathlib's `MvPowerSeries.order`, the least total degree of a monomial with nonzero
coefficient) of its Taylor expansion `F(v + X)`. The multiplicity of `F` at a point `p` of the
projective space `ℙ K (σ → K)` is its order of vanishing at a representative of `p`; for
homogeneous `F` this does not depend on the representative.

Points of `ℙ K (σ → K)` also index the hyperplanes of `ℙ K (σ → K)`, in particular the lines of
the projective plane `ℙ K (Fin 3 → K)`: the point `p` lies on the hyperplane with coordinate vector
`ℓ` exactly when `Projectivization.orthogonal p ℓ`, which Mathlib defines as the vanishing of the
dot product of representatives. Incidence is therefore stated with `Projectivization.orthogonal`
(symmetric by `Projectivization.orthogonal_comm`), and the hyperplane with coordinate vector
`w ≠ 0` is the zero set of the linear form `∑ i, C (w i) * X i`.

## Main definitions

* `MvPolynomial.orderAt F v`: the order of vanishing of `F` at `v`, in `ℕ∞`; it is `⊤` exactly
  when `F = 0` (`MvPolynomial.orderAt_eq_top_iff`).
* `MvPolynomial.multiplicityAt F p`: the multiplicity of `F` at `p : ℙ K (σ → K)`, in `ℕ`, with
  the junk value `0` at `F = 0`.

## Main statements

* `MvPolynomial.one_le_orderAt_iff`: `F` vanishes to order at least one at `v` iff `F(v) = 0`.
* `MvPolynomial.natCast_add_one_le_orderAt_iff`: over a domain of characteristic zero, `F`
  vanishes to order at least `n + 1` at `v` iff `F(v) = 0` and every first partial derivative
  vanishes to order at least `n` at `v`. By induction, the order of vanishing is the least order
  of a partial derivative of `F` not vanishing at `v`; `MvPolynomial.two_le_orderAt_iff`
  characterizes the singular points.
* `MvPolynomial.orderAt_smul`: for homogeneous `F`, rescaling the point by a nonzero scalar does
  not change the order of vanishing, so `MvPolynomial.multiplicityAt_mk` computes the
  multiplicity at any representative.
* `MvPolynomial.orderAt_sum_C_mul_X_of_dotProduct_eq_zero` and
  `MvPolynomial.orderAt_sum_C_mul_X_of_dotProduct_ne_zero`, with their projective forms
  `MvPolynomial.multiplicityAt_sum_C_mul_X_of_orthogonal` and
  `MvPolynomial.multiplicityAt_sum_C_mul_X_of_not_orthogonal`: a hyperplane has multiplicity one
  at its points and zero elsewhere.

## Implementation notes

The order of vanishing is defined through the Taylor expansion rather than through partial
derivatives so that it is correct in every characteristic: over `ZMod 2`, the polynomial `X₀²`
vanishes to order two at the origin although all its partial derivatives vanish identically.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

section Basic

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Rescaling a representative by a nonzero scalar does not change the point. -/
theorem mk_smul_eq {a : K} (ha : a ≠ 0) {v : V} (hv : v ≠ 0) :
    mk K (a • v) (smul_ne_zero ha hv) = mk K v hv :=
  (mk_eq_mk_iff' K _ _ _ hv).2 ⟨a, rfl⟩

end Basic

variable {K m : Type*} [Field K] [Fintype m]

/-- Orthogonality of two points is the vanishing of the dot product of their representatives. -/
theorem orthogonal_iff_rep_dotProduct_rep {v w : ℙ K (m → K)} :
    v.orthogonal w ↔ v.rep ⬝ᵥ w.rep = 0 := by
  conv_lhs => rw [← v.mk_rep, ← w.mk_rep]
  exact orthogonal_mk _ _

end Projectivization

namespace MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- The order of vanishing of `F` at the point `v`: the order at the origin
(`MvPowerSeries.order`, the least total degree of a monomial with nonzero coefficient) of the
Taylor expansion `F(v + X)`. It is `⊤` for `F = 0`. -/
noncomputable def orderAt (F : MvPolynomial σ R) (v : σ → R) : ℕ∞ :=
  ((aeval fun i => (X i + C (v i) : MvPolynomial σ R)) F : MvPowerSeries σ R).order

/-- The constant term of the Taylor expansion `F(v + X)` is `F(v)`. -/
theorem constantCoeff_aeval_X_add_C (F : MvPolynomial σ R) (v : σ → R) :
    constantCoeff (aeval (fun i => X i + C (v i)) F) = eval v F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Partial derivatives commute with Taylor expansion. -/
theorem pderiv_aeval_X_add_C (i : σ) (v : σ → R) (F : MvPolynomial σ R) :
    pderiv i (aeval (fun j => X j + C (v j)) F) = aeval (fun j => X j + C (v j)) (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i
    · subst h
      simp [hp]
    · simp [hp, pderiv_X_of_ne h]

/-- The order of a polynomial, as a power series, is at least `n` iff its coefficients of total
degree less than `n` vanish. -/
private theorem natCast_le_order_coe_iff {G : MvPolynomial σ R} {n : ℕ} :
    (n : ℕ∞) ≤ (G : MvPowerSeries σ R).order ↔ ∀ d : σ →₀ ℕ, d.degree < n → G.coeff d = 0 := by
  refine ⟨fun h d hd => ?_, fun h => MvPowerSeries.nat_le_order fun d hd => ?_⟩
  · rw [← coeff_coe]
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
  · rw [coeff_coe]
    exact h d hd

/-- Two polynomials with the same vanishing coefficients have the same order. -/
private theorem order_coe_eq_of_coeff_eq_zero_iff {G H : MvPolynomial σ R}
    (h : ∀ d, G.coeff d = 0 ↔ H.coeff d = 0) :
    (G : MvPowerSeries σ R).order = (H : MvPowerSeries σ R).order := by
  refine le_antisymm (MvPowerSeries.le_order fun d hd => ?_)
    (MvPowerSeries.le_order fun d hd => ?_)
  · rw [coeff_coe, ← h, ← coeff_coe]
    exact MvPowerSeries.coeff_of_lt_order hd
  · rw [coeff_coe, h, ← coeff_coe]
    exact MvPowerSeries.coeff_of_lt_order hd

/-- A polynomial vanishes to order at least one at `v` iff it vanishes at `v`. -/
theorem one_le_orderAt_iff {F : MvPolynomial σ R} {v : σ → R} :
    1 ≤ F.orderAt v ↔ eval v F = 0 := by
  rw [orderAt, MvPowerSeries.one_le_order_iff_constCoeff_eq_zero,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe, ← constantCoeff_eq,
    constantCoeff_aeval_X_add_C]

/-- A polynomial vanishes to order zero at `v` iff it does not vanish at `v`. -/
theorem orderAt_eq_zero_iff {F : MvPolynomial σ R} {v : σ → R} :
    F.orderAt v = 0 ↔ eval v F ≠ 0 := by
  rw [ne_eq, ← one_le_orderAt_iff, not_le, Order.lt_one_iff]

@[simp]
theorem orderAt_zero (v : σ → R) : (0 : MvPolynomial σ R).orderAt v = ⊤ := by
  simp [orderAt]

/-- A nonzero constant vanishes to order zero everywhere. -/
theorem orderAt_C_of_ne_zero {a : R} (ha : a ≠ 0) (v : σ → R) :
    (C a : MvPolynomial σ R).orderAt v = 0 :=
  orderAt_eq_zero_iff.2 (by simpa using ha)

/-- Evaluating a homogeneous polynomial of degree `d` at a rescaled point multiplies the value by
the `d`-th power of the scalar. The evaluation form is
`FormalizedTextbooks.Hartshorne1977.ClassicalVarieties.isHomogeneous_eval_smul`; this generalized
form is kept private, as an ingredient of `orderAt_smul`. -/
private theorem IsHomogeneous.aeval_smul {S : Type*} [CommSemiring S] [Algebra R S]
    {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) (c : S) (y : σ → S) :
    MvPolynomial.aeval (c • y) F = c ^ d * MvPolynomial.aeval y F := by
  rw [F.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hexp : ∑ i ∈ m.support, m i = d := (hF.degree_eq_sum_deg_support hm).symm
  rw [aeval_monomial, aeval_monomial]
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hexp]
  ring

/-- The coefficients of `G(a X)` are those of `G` multiplied by `a` to the power of the total
degree. -/
private theorem coeff_aeval_C_mul_X (a : R) (G : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (aeval (fun i => C a * X i) G).coeff d = a ^ d.degree * G.coeff d := by
  classical
  have hcomp : ∀ n, aeval (fun i => C a * X i) (homogeneousComponent n G) =
      C (a ^ n) * homogeneousComponent n G := by
    intro n
    have h := (homogeneousComponent_isHomogeneous n G).aeval_smul (C a) X
    rw [aeval_X_left_apply, ← C_pow] at h
    rw [← h]
    rfl
  conv_lhs => rw [← sum_homogeneousComponent G]
  rw [map_sum, coeff_sum]
  simp only [hcomp, coeff_C_mul, coeff_homogeneousComponent, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hd
  · rfl
  · rw [coeff_eq_zero_of_totalDegree_lt, mul_zero]
    rw [Finset.mem_range, not_lt] at hd
    rw [← Finsupp.degree_apply]
    omega

end CommSemiring

section CommRing

variable [CommRing R]

/-- Taylor expansion at `-v` undoes Taylor expansion at `v`. -/
private theorem aeval_X_add_C_neg (v : σ → R) (F : MvPolynomial σ R) :
    aeval (fun i => X i + C (-v i)) (aeval (fun i => X i + C (v i)) F) = F := by
  rw [← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← aeval_X_left_apply F]
  congr 2
  funext i
  simp

/-- The order of vanishing is `⊤` exactly for the zero polynomial. -/
@[simp]
theorem orderAt_eq_top_iff {F : MvPolynomial σ R} {v : σ → R} :
    F.orderAt v = ⊤ ↔ F = 0 := by
  rw [orderAt, MvPowerSeries.order_eq_top_iff, coe_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := aeval_X_add_C_neg v F
  rw [h, map_zero] at this
  exact this.symm

theorem orderAt_ne_top {F : MvPolynomial σ R} (hF : F ≠ 0) (v : σ → R) : F.orderAt v ≠ ⊤ :=
  orderAt_eq_top_iff.not.2 hF

end CommRing

section CharZero

variable [CommRing R] [IsDomain R] [CharZero R]

/-- In characteristic zero, the order of a polynomial is at least `n + 1` iff its constant term
vanishes and every first partial derivative has order at least `n`. -/
private theorem natCast_add_one_le_order_coe_iff {G : MvPolynomial σ R} {n : ℕ} :
    (n : ℕ∞) + 1 ≤ (G : MvPowerSeries σ R).order ↔
      G.coeff 0 = 0 ∧ ∀ i, (n : ℕ∞) ≤ (pderiv i G : MvPowerSeries σ R).order := by
  classical
  rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by push_cast; rfl, natCast_le_order_coe_iff]
  simp_rw [natCast_le_order_coe_iff, coeff_pderiv]
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun i d hd => ?_⟩
    rw [h (d + Finsupp.single i 1) (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]
  · rintro ⟨h0, h⟩ d hd
    obtain rfl | hd0 := eq_or_ne d 0
    · exact h0
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! hcon
      exact hd0 (Finsupp.ext hcon)
    have hsplit : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))
    have hdeg : (d - Finsupp.single i 1).degree < n := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    have h' := h i (d - Finsupp.single i 1) hdeg
    rw [hsplit] at h'
    exact (mul_eq_zero.1 h').resolve_right (Nat.cast_add_one_ne_zero _)

/-- In characteristic zero, `F` vanishes to order at least `n + 1` at `v` iff `F(v) = 0` and
every first partial derivative of `F` vanishes to order at least `n` at `v`. -/
theorem natCast_add_one_le_orderAt_iff {F : MvPolynomial σ R} {v : σ → R} {n : ℕ} :
    (n : ℕ∞) + 1 ≤ F.orderAt v ↔ eval v F = 0 ∧ ∀ i, (n : ℕ∞) ≤ (pderiv i F).orderAt v := by
  simp only [orderAt, natCast_add_one_le_order_coe_iff, ← constantCoeff_eq,
    constantCoeff_aeval_X_add_C, pderiv_aeval_X_add_C]

/-- In characteristic zero, `F` vanishes to order at least two at `v` (`v` is a singular point of
`F = 0`) iff `F` and all its first partial derivatives vanish at `v`. -/
theorem two_le_orderAt_iff {F : MvPolynomial σ R} {v : σ → R} :
    2 ≤ F.orderAt v ↔ eval v F = 0 ∧ ∀ i, eval v (pderiv i F) = 0 := by
  have h := natCast_add_one_le_orderAt_iff (F := F) (v := v) (n := 1)
  simp only [Nat.cast_one, one_add_one_eq_two, one_le_orderAt_iff] at h
  exact h

end CharZero

section Field

variable {K : Type*} [Field K]

/-- For a homogeneous polynomial, rescaling the point by a nonzero scalar does not change the
order of vanishing. -/
theorem orderAt_smul {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d) {c : K}
    (hc : c ≠ 0) (v : σ → K) : F.orderAt (c • v) = F.orderAt v := by
  have key : aeval (fun i => X i + C ((c • v) i)) F =
      C (c ^ d) * aeval (fun i => C c⁻¹ * X i) (aeval (fun i => X i + C (v i)) F) := by
    have hpt : (fun i => X i + C ((c • v) i)) =
        (C c : MvPolynomial σ K) • fun i => (C c⁻¹ * X i + C (v i) : MvPolynomial σ K) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_add, ← mul_assoc, ← C_mul,
        mul_inv_cancel₀ hc, C_1, one_mul]
    have hfun : (fun i => (aeval fun i => (C c⁻¹ * X i : MvPolynomial σ K)) (X i + C (v i))) =
        fun i => C c⁻¹ * X i + C (v i) := by
      funext i
      simp
    rw [hpt, hF.aeval_smul, ← C_pow, ← AlgHom.comp_apply, comp_aeval, hfun]
  refine order_coe_eq_of_coeff_eq_zero_iff fun α => ?_
  rw [key, coeff_C_mul, coeff_aeval_C_mul_X]
  simp [hc]

/-- The multiplicity of `F` at the point `p` of `ℙ K (σ → K)`: the order of vanishing of `F` at
a representative of `p`. For homogeneous `F` it does not depend on the representative
(`MvPolynomial.multiplicityAt_mk`); it takes the junk value `0` at `F = 0`. -/
noncomputable def multiplicityAt (F : MvPolynomial σ K) (p : ℙ K (σ → K)) : ℕ :=
  (F.orderAt p.rep).toNat

/-- The multiplicity of a homogeneous polynomial can be computed at any representative. -/
theorem multiplicityAt_mk {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d) {v : σ → K}
    (hv : v ≠ 0) :
    F.multiplicityAt (Projectivization.mk K v hv) = (F.orderAt v).toNat := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [multiplicityAt, ← ha, Units.smul_def, orderAt_smul hF a.ne_zero]

/-- For `F ≠ 0`, the multiplicity is the order of vanishing at the representative. -/
theorem natCast_multiplicityAt {F : MvPolynomial σ K} (hF : F ≠ 0) (p : ℙ K (σ → K)) :
    (F.multiplicityAt p : ℕ∞) = F.orderAt p.rep :=
  ENat.natCast_toNat (orderAt_ne_top hF _)

theorem le_multiplicityAt_iff {F : MvPolynomial σ K} (hF : F ≠ 0) {p : ℙ K (σ → K)} {n : ℕ} :
    n ≤ F.multiplicityAt p ↔ (n : ℕ∞) ≤ F.orderAt p.rep := by
  rw [← natCast_multiplicityAt hF, Nat.cast_le]

@[simp]
theorem multiplicityAt_zero (p : ℙ K (σ → K)) : (0 : MvPolynomial σ K).multiplicityAt p = 0 := by
  simp [multiplicityAt]

/-- Constants have multiplicity zero everywhere (for the zero constant, this is the junk
value). -/
@[simp]
theorem multiplicityAt_C (a : K) (p : ℙ K (σ → K)) :
    (C a : MvPolynomial σ K).multiplicityAt p = 0 := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · simp [multiplicityAt, orderAt_C_of_ne_zero ha]

/-- A nonzero polynomial has positive multiplicity at `p` iff it vanishes at the representative
of `p`. -/
theorem multiplicityAt_pos_iff {F : MvPolynomial σ K} (hF : F ≠ 0) {p : ℙ K (σ → K)} :
    0 < F.multiplicityAt p ↔ eval p.rep F = 0 := by
  rw [← Nat.one_le_iff_ne_zero.trans Nat.pos_iff_ne_zero.symm, le_multiplicityAt_iff hF,
    Nat.cast_one, one_le_orderAt_iff]

variable [Fintype σ]

/-- A linear form `∑ i, w i X i` vanishes to order zero at a point off its hyperplane. -/
theorem orderAt_sum_C_mul_X_of_dotProduct_ne_zero {w v : σ → K} (h : w ⬝ᵥ v ≠ 0) :
    (∑ i, C (w i) * X i).orderAt v = 0 :=
  orderAt_eq_zero_iff.2 (by simpa [dotProduct] using h)

/-- A nonzero linear form `∑ i, w i X i` vanishes to order one at the points of its
hyperplane. -/
theorem orderAt_sum_C_mul_X_of_dotProduct_eq_zero {w v : σ → K} (hw : w ≠ 0)
    (h : w ⬝ᵥ v = 0) : (∑ i, C (w i) * X i).orderAt v = 1 := by
  classical
  refine le_antisymm ?_ (one_le_orderAt_iff.2 (by simpa [dotProduct] using h))
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hcon
    exact hw (funext hcon)
  have h0 : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
  have hcoeff : (aeval (fun j => (X j + C (v j) : MvPolynomial σ K))
      (∑ j, C (w j) * X j)).coeff (Finsupp.single i 1) = w i := by
    simp [coeff_X, coeff_C, Finsupp.single_eq_single_iff, h0]
  unfold orderAt
  calc _ ≤ ((Finsupp.single i (1 : ℕ)).degree : ℕ∞) :=
        MvPowerSeries.order_le (by rw [coeff_coe, hcoeff]; exact hi)
    _ = 1 := by simp

/-- A line (hyperplane) has multiplicity one at its points. -/
theorem multiplicityAt_sum_C_mul_X_of_orthogonal {w : σ → K} (hw : w ≠ 0) {p : ℙ K (σ → K)}
    (h : p.orthogonal (Projectivization.mk K w hw)) :
    (∑ i, C (w i) * X i).multiplicityAt p = 1 := by
  rw [← p.mk_rep, Projectivization.orthogonal_mk, dotProduct_comm] at h
  rw [multiplicityAt, orderAt_sum_C_mul_X_of_dotProduct_eq_zero hw h]
  rfl

/-- A line (hyperplane) has multiplicity zero at the points off it. -/
theorem multiplicityAt_sum_C_mul_X_of_not_orthogonal {w : σ → K} (hw : w ≠ 0) {p : ℙ K (σ → K)}
    (h : ¬p.orthogonal (Projectivization.mk K w hw)) :
    (∑ i, C (w i) * X i).multiplicityAt p = 0 := by
  rw [← p.mk_rep, Projectivization.orthogonal_mk, dotProduct_comm] at h
  rw [multiplicityAt, orderAt_sum_C_mul_X_of_dotProduct_ne_zero h]
  rfl

end Field

end MvPolynomial
