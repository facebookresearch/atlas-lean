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

/-- **Positive primitive integral minimal polynomial.** Let $K$ be a field that is a
$\mathbb{Q}$-algebra, let $x \in K$, and let $p$ be the canonical primitive integral minimal
polynomial of $x$. The positive primitive integral minimal polynomial of $x$ is $-p$ if the
leading coefficient of $p$ is negative, and $p$ otherwise.

Since $p$ is nonzero, the result has positive leading coefficient. When $x$ is not algebraic
over $\mathbb{Q}$, $p$ is the constant polynomial $1$, and so is the result. -/
noncomputable def positivePrimitiveIntMinpoly (x : K) : Polynomial ℤ :=
  let p := primitiveIntMinpoly x
  if p.leadingCoeff < 0 then -p else p

/-- **The positive primitive integral minimal polynomial is primitive.** For every element $x$ of
a field $K$ that is an algebra over $\mathbb{Q}$, the positive primitive integral minimal
polynomial of $x$ is primitive: the greatest common divisor of its integer coefficients is $1$. -/
theorem positivePrimitiveIntMinpoly_isPrimitive (x : K) :
    (positivePrimitiveIntMinpoly x).IsPrimitive := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs with h
  · rw [Polynomial.IsPrimitive]
    intro r hr
    apply primitiveIntMinpoly_isPrimitive x r
    simpa using hr
  · exact primitiveIntMinpoly_isPrimitive x

/-- **The positive primitive integral minimal polynomial is nonzero.** Let $K$ be a field
that is a $\mathbb{Q}$-algebra. For every $x \in K$, the positive primitive integral minimal
polynomial of $x$ is not the zero polynomial. -/
theorem positivePrimitiveIntMinpoly_ne_zero (x : K) :
    positivePrimitiveIntMinpoly x ≠ 0 := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs <;> simpa using primitiveIntMinpoly_ne_zero x

/-- **The positive primitive integral minimal polynomial has positive leading coefficient.** For
every element $x$ of a field $K$ that is an algebra over $\mathbb{Q}$, the leading coefficient of
the positive primitive integral minimal polynomial of $x$ is a strictly positive integer. -/
theorem positivePrimitiveIntMinpoly_leadingCoeff_pos (x : K) :
    0 < (positivePrimitiveIntMinpoly x).leadingCoeff := by
  have hlc : (primitiveIntMinpoly x).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (primitiveIntMinpoly_ne_zero x)
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs with h
  · simpa using neg_pos.mpr h
  · simpa using lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hlc)

/-- **Sign normalization preserves the degree.** For every element $x$ of a field $K$ that is an
algebra over $\mathbb{Q}$, the positive primitive integral minimal polynomial of $x$ has the same
degree as the primitive integral minimal polynomial of $x$. -/
theorem positivePrimitiveIntMinpoly_natDegree (x : K) :
    (positivePrimitiveIntMinpoly x).natDegree = (primitiveIntMinpoly x).natDegree := by
  dsimp only [positivePrimitiveIntMinpoly]
  split_ifs <;> simp

/-- **The positive primitive integral minimal polynomial has the degree of the minimal
polynomial.** For every element $x$ of a field $K$ that is an algebra over $\mathbb{Q}$, the
positive primitive integral minimal polynomial of $x$ has the same degree as the minimal
polynomial of $x$ over $\mathbb{Q}$.

Degrees are natural numbers, the zero polynomial having degree $0$; if $x$ is not algebraic over
$\mathbb{Q}$, both degrees are $0$. -/
theorem positivePrimitiveIntMinpoly_natDegree_eq (x : K) :
    (positivePrimitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  rw [positivePrimitiveIntMinpoly_natDegree, primitiveIntMinpoly_natDegree]

/-- **An algebraic element is a root of its positive primitive integral minimal polynomial.** Let
$K$ be a field of characteristic zero that is an algebra over $\mathbb{Q}$, and let $x \in K$ be
algebraic over $\mathbb{Q}$. Then the positive primitive integral minimal polynomial of $x$, with
its integer coefficients mapped into $K$, vanishes at $x$. -/
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

/-- **Algebraic Mahler measure.** For an element $x$ of a field $K$ that is an algebra over
$\mathbb{Q}$, the algebraic Mahler measure $M(x)$ is the Mahler measure of the positive primitive
integral minimal polynomial of $x$, regarded as a polynomial with complex coefficients. If $x$ is
not algebraic over $\mathbb{Q}$, this polynomial is the constant $1$, so $M(x) = 1$. -/
noncomputable def algebraicMahlerMeasure (x : K) : ℝ :=
  (positivePrimitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ)

/-- **The sign normalization does not change the Mahler measure.** For every element $x$ of a
field $K$ that is an algebra over $\mathbb{Q}$, the algebraic Mahler measure of $x$, that is the
Mahler measure of the positive primitive integral minimal polynomial of $x$, equals the Mahler
measure of the primitive integral minimal polynomial of $x$, both polynomials being regarded as
polynomials with complex coefficients. -/
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

/-- **The algebraic Mahler measure is at least one.** For every element $x$ of a field $K$ that
is an algebra over $\mathbb{Q}$, the algebraic Mahler measure $M(x)$ of $x$ satisfies
$1 \le M(x)$.

This holds because the positive primitive integral minimal polynomial of $x$ has a positive
integer leading coefficient. -/
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

/-- **Absolute logarithmic height from the algebraic Mahler measure.** Let $K$ be a field of
characteristic zero that is an algebra over $\mathbb{Q}$, and let $x \in K$ be algebraic over
$\mathbb{Q}$. Let $d$ be the degree of the minimal polynomial of $x$ over $\mathbb{Q}$, and let
$M(x)$ be the algebraic Mahler measure of $x$, the Mahler measure of the positive primitive
integral minimal polynomial of $x$ regarded as a complex polynomial. Then the absolute
logarithmic height of $x$ equals $\log M(x) / d$. -/
theorem absLogHeight₁_eq_log_algebraicMahlerMeasure [CharZero K]
    (x : K) (hx : IsAlgebraic ℚ x) :
    absLogHeight₁ x = Real.log (algebraicMahlerMeasure x) / (minpoly ℚ x).natDegree := by
  rw [absLogHeight₁,
    MathlibExt.NumberTheory.Height.AbsoluteWanted.absMulHeight₁_eq_mapMahlerMeasure_of_isIntegral
      x hx.isIntegral,
    ← algebraicMahlerMeasure_eq x,
    Real.log_rpow (lt_of_lt_of_le zero_lt_one (one_le_algebraicMahlerMeasure x)),
    div_eq_inv_mul]

/-- **One plus the logarithm of a Mahler measure above one is below it.** Let $x$ be an element
of a field $K$ that is an algebra over $\mathbb{Q}$, and let $M(x)$ be its algebraic Mahler
measure. If $M(x) > 1$, then $1 + \log M(x) < M(x)$.

Voutier uses this elementary inequality to pass from lower bounds for $\log M(x)$ to lower bounds
for $M(x)$. -/
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
