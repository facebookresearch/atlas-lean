/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.AbsoluteLogHeightRoots

/-!
# Positive primitive minimal polynomials and Mahler measure

The positive-leading convention is used by Voutier, *An effective lower bound for the height of
algebraic numbers*, arXiv:1211.3110v1, Introduction. The unsigned primitive polynomial and absolute
height are the existing canonical APIs. The sign-normalization proofs adapt the C40b implementation
at formal-math commit `388108ea3ccda5b5bf9eb0b6d88f83ffecbfc528`.
-/

@[expose] public section

namespace NumberField

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The canonical primitive integral minimal polynomial, with positive leading coefficient.
Nonalgebraic inputs retain the canonical primitive-part fallback `1`. -/
noncomputable def positivePrimitiveIntMinpoly (x : K) : Polynomial ℤ :=
  let p := primitiveIntMinpoly x
  if p.leadingCoeff < 0 then -p else p

/-- Sign normalization preserves the canonical polynomial's primitivity. -/
theorem positivePrimitiveIntMinpoly_isPrimitive (x : K) :
    (positivePrimitiveIntMinpoly x).IsPrimitive := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs with h
  · rw [Polynomial.IsPrimitive]
    intro r hr
    apply primitiveIntMinpoly_isPrimitive x r
    simpa using hr
  · exact primitiveIntMinpoly_isPrimitive x

/-- Sign normalization does not turn the canonical primitive polynomial into zero. -/
theorem positivePrimitiveIntMinpoly_ne_zero (x : K) :
    positivePrimitiveIntMinpoly x ≠ 0 := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs <;> simpa using primitiveIntMinpoly_ne_zero x

/-- The sign choice gives a strictly positive integral leading coefficient. -/
theorem positivePrimitiveIntMinpoly_leadingCoeff_pos (x : K) :
    0 < (positivePrimitiveIntMinpoly x).leadingCoeff := by
  have hlc : (primitiveIntMinpoly x).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (primitiveIntMinpoly_ne_zero x)
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs with h
  · simpa using neg_pos.mpr h
  · simpa using lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hlc)

/-- Sign normalization preserves the canonical primitive polynomial's degree. -/
theorem positivePrimitiveIntMinpoly_natDegree (x : K) :
    (positivePrimitiveIntMinpoly x).natDegree = (primitiveIntMinpoly x).natDegree := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs <;> simp

/-- The signed integral polynomial has the degree of the rational minimal polynomial. -/
theorem positivePrimitiveIntMinpoly_natDegree_eq (x : K) :
    (positivePrimitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  rw [positivePrimitiveIntMinpoly_natDegree, primitiveIntMinpoly_natDegree]

/-- The signed primitive polynomial vanishes at the actual algebraic input. -/
theorem positivePrimitiveIntMinpoly_eval₂_at [CharZero K] (x : K) (hx : IsAlgebraic ℚ x) :
    Polynomial.eval₂ (Int.castRingHom K) x (positivePrimitiveIntMinpoly x) = 0 := by
  let q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := by
    ext n
    simp
  have hqroot : Polynomial.eval₂ (Int.castRingHom K) x q = 0 := by
    rw [← hcomp]
    simpa [q] using
      IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors ℤ)
        (algebraMap ℚ K) (minpoly ℚ x) (minpoly.aeval ℚ x)
  have hq : q ≠ 0 := by
    intro hq0
    have hmin0 : minpoly ℚ x = 0 :=
      IsFractionRing.integerNormalization_eq_zero_iff.mp hq0
    exact minpoly.ne_zero hx.isIntegral hmin0
  have hprim : Polynomial.eval₂ (Int.castRingHom K) x (primitiveIntMinpoly x) = 0 :=
    Polynomial.eval₂_primPart_eq_zero Int.cast_injective hq hqroot
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs <;> simp [hprim]

/-- The actual complex Mahler measure of the positive primitive integral minimal polynomial. -/
noncomputable def algebraicMahlerMeasure (x : K) : ℝ :=
  (positivePrimitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ)

/-- The source's sign convention does not change the canonical polynomial's Mahler measure. -/
theorem algebraicMahlerMeasure_eq (x : K) :
    algebraicMahlerMeasure x = (primitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ) := by
  dsimp only [algebraicMahlerMeasure, positivePrimitiveIntMinpoly]
  split_ifs with h
  · simp only [Polynomial.mapMahlerMeasure, Polynomial.map_neg]
    rw [show -(primitiveIntMinpoly x).map (Int.castRingHom ℂ) =
      Polynomial.C (-1) * (primitiveIntMinpoly x).map (Int.castRingHom ℂ) by simp]
    simp only [Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_const,
      norm_neg, norm_one, one_mul]
  · rfl

/-- A positive integral leading coefficient makes the actual Mahler measure at least one. -/
theorem one_le_algebraicMahlerMeasure (x : K) : 1 ≤ algebraicMahlerMeasure x := by
  have hlc := positivePrimitiveIntMinpoly_leadingCoeff_pos x
  have hone : (1 : ℤ) ≤ (positivePrimitiveIntMinpoly x).leadingCoeff := by omega
  have hreal : (0 : ℝ) < (positivePrimitiveIntMinpoly x).leadingCoeff := by
    exact_mod_cast hlc
  calc
    1 ≤ ((positivePrimitiveIntMinpoly x).leadingCoeff : ℝ) := by exact_mod_cast hone
    _ = ‖(positivePrimitiveIntMinpoly x).leadingCoeff‖ := by
      rw [Int.norm_eq_abs, abs_of_pos hreal]
    _ ≤ algebraicMahlerMeasure x :=
      Polynomial.leadingCoeff_le_mapMahlerMeasure _ _ Complex.isometry_intCast

/-- On algebraic inputs, the canonical absolute logarithmic height is `log M / degree`. -/
theorem absLogHeight₁_eq_log_algebraicMahlerMeasure [CharZero K]
    (x : K) (hx : IsAlgebraic ℚ x) :
    absLogHeight₁ x = Real.log (algebraicMahlerMeasure x) / (minpoly ℚ x).natDegree := by
  rw [absLogHeight₁,
    MathlibExt.NumberTheory.Height.AbsoluteWanted.absMulHeight₁_eq_mapMahlerMeasure_of_isIntegral
      x hx.isIntegral,
    ← algebraicMahlerMeasure_eq x,
    Real.log_rpow (lt_of_lt_of_le zero_lt_one (one_le_algebraicMahlerMeasure x)),
    div_eq_inv_mul]

/-- Voutier's elementary bridge from logarithmic to multiplicative lower bounds, for `M > 1`. -/
theorem log_algebraicMahlerMeasure_add_one_lt (x : K) (hM : 1 < algebraicMahlerMeasure x) :
    1 + Real.log (algebraicMahlerMeasure x) < algebraicMahlerMeasure x := by
  have hpos : 0 < algebraicMahlerMeasure x := zero_lt_one.trans hM
  calc
    1 + Real.log (algebraicMahlerMeasure x) = Real.log (algebraicMahlerMeasure x) + 1 :=
      add_comm _ _
    _ < Real.exp (Real.log (algebraicMahlerMeasure x)) :=
      Real.add_one_lt_exp (Real.log_ne_zero_of_pos_of_ne_one hpos hM.ne')
    _ = algebraicMahlerMeasure x := Real.exp_log hpos

end NumberField
