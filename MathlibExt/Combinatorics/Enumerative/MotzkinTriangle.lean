/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Motzkin triangle as a Riordan array

This file records the formal-power-series description of the Motzkin triangle from Yassine
Otmani, *The 2-Pascal Triangle and a Related Riordan Array*:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Otmani/otmani10.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Motzkin discriminant.** The Motzkin discriminant is the formal power series
$1 - 2X - 3X^2 \in \mathbb{Q}[[X]]$, the discriminant in the generating functions for the Motzkin
triangle. -/
noncomputable def motzkinDiscriminant : PowerSeries ℚ :=
  PowerSeries.C 1 - PowerSeries.C 2 * PowerSeries.X -
    PowerSeries.C 3 * PowerSeries.X ^ 2

/-- **Square roots of the Motzkin discriminant.** A formal power series $s \in \mathbb{Q}[[X]]$ is
a Motzkin square root when $s^2 = 1 - 2X - 3X^2$ and the constant coefficient of $s$ is $1$. -/
def IsMotzkinSquareRoot (s : PowerSeries ℚ) : Prop :=
  s * s = motzkinDiscriminant ∧ PowerSeries.constantCoeff s = 1

/-- **Canonical square root of the Motzkin discriminant.** The canonical square root is the power
series $s = \sum_{n \ge 0} \binom{1/2}{n} (-2X - 3X^2)^n \in \mathbb{Q}[[X]]$, obtained by
substituting $-2X - 3X^2$ for $Y$ in the binomial series
$(1 + Y)^{1/2} = \sum_{n \ge 0} \binom{1/2}{n} Y^n$.

It is the branch of $\sqrt{1 - 2X - 3X^2}$ with constant coefficient $1$ used by the Motzkin
generating functions. -/
noncomputable def motzkinSquareRoot : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (motzkinDiscriminant - 1)

theorem motzkinSquareRoot_isSquareRoot : IsMotzkinSquareRoot motzkinSquareRoot := by
  let u : PowerSeries ℚ := motzkinDiscriminant - 1
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    norm_num [u, motzkinDiscriminant]
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  have hone : PowerSeries.subst u (1 : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hu, map_one]
  constructor
  · change (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u *
      (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u = motzkinDiscriminant
    rw [← PowerSeries.subst_mul hu, ← PowerSeries.binomialSeries_add]
    norm_num
    have hb1 : PowerSeries.binomialSeries ℚ (1 : ℚ) = 1 + PowerSeries.X := by
      simpa using (PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1)
    rw [hb1]
    simp [PowerSeries.subst_add hu, PowerSeries.subst_X hu, hone, u]
  · change PowerSeries.constantCoeff
      ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst u) = 1
    let b := PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)
    have hb0 : PowerSeries.constantCoeff (b - 1) = 0 := by
      simp [b]
    have hsub0 : PowerSeries.constantCoeff ((b - 1).subst u) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hu0 (b - 1) hb0
    have hb : b = 1 + (b - 1) := by ring
    rw [show PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = b from rfl, hb,
      PowerSeries.subst_add hu]
    simpa [hone] using hsub0

/-- **Second component of the Motzkin Riordan pair.** Let
$s = \sum_{n \ge 0} \binom{1/2}{n} (-2X - 3X^2)^n \in \mathbb{Q}[[X]]$ be the canonical square root
of $1 - 2X - 3X^2$. The power series $h \in \mathbb{Q}[[X]]$ has $n$-th coefficient
$\frac{1}{2} [X^{n+1}] (1 - X - s)$ for every $n \ge 0$. Since $1 - X - s$ has constant coefficient
$0$, this is the quotient $h = (1 - X - s)/(2X)$.

The definition uses a coefficient shift so that no division by $X$ is required. -/
noncomputable def motzkinH : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (1 - PowerSeries.X - motzkinSquareRoot) / 2

theorem two_mul_X_mul_motzkinH :
    2 * PowerSeries.X * motzkinH = 1 - PowerSeries.X - motzkinSquareRoot := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_ofNat (algebraMap ℚ (PowerSeries ℚ)) 2).symm, mul_assoc]
  ext n
  cases n with
  | zero =>
      simp [motzkinSquareRoot_isSquareRoot.2]
  | succ n =>
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp [motzkinH]
      ring

/-- **First component of the Motzkin Riordan pair.** Let
$s = \sum_{n \ge 0} \binom{1/2}{n} (-2X - 3X^2)^n \in \mathbb{Q}[[X]]$ be the canonical square root
of $1 - 2X - 3X^2$, which has constant coefficient $1$. The power series $g \in \mathbb{Q}[[X]]$ is
the multiplicative inverse $g = s^{-1}$ of $s$, that is, $g = 1/\sqrt{1 - 2X - 3X^2}$. -/
noncomputable def motzkinG : PowerSeries ℚ :=
  motzkinSquareRoot⁻¹

theorem motzkinG_mul_motzkinSquareRoot :
    motzkinG * motzkinSquareRoot = 1 := by
  exact PowerSeries.inv_mul_cancel _ (by
    rw [motzkinSquareRoot_isSquareRoot.2]
    norm_num)

/-- **Motzkin Riordan pairs.** Formal power series $g, h \in \mathbb{Q}[[X]]$ form a Motzkin Riordan
pair when there is a power series $s \in \mathbb{Q}[[X]]$ with $s^2 = 1 - 2X - 3X^2$ and constant
coefficient $1$ such that $g s = 1$ and $2 X h = 1 - X - s$.

Writing the second identity without division by $X$ keeps the characterization internal to formal
power series. The constant-coefficient condition selects the intended square-root branch. -/
def IsMotzkinRiordanPair (g h : PowerSeries ℚ) : Prop :=
  ∃ s : PowerSeries ℚ,
    IsMotzkinSquareRoot s ∧ g * s = 1 ∧
      2 * PowerSeries.X * h = 1 - PowerSeries.X - s

/-- **Bundled Motzkin Riordan pairs.** A bundled Motzkin Riordan pair consists of formal power
series $g, h \in \mathbb{Q}[[X]]$ together with a proof that they form a Motzkin Riordan pair: there
is $s \in \mathbb{Q}[[X]]$ with $s^2 = 1 - 2X - 3X^2$ and constant coefficient $1$ such that
$g s = 1$ and $2 X h = 1 - X - s$. -/
structure MotzkinRiordanPair where
  g : PowerSeries ℚ
  h : PowerSeries ℚ
  isPair : IsMotzkinRiordanPair g h

namespace MotzkinRiordanPair

/-- **Entries of a Motzkin Riordan array.** For a Motzkin Riordan pair $(g, h)$ and natural numbers
$n$ and $k$, the $(n, k)$ entry is the rational number $[X^n]\, g h^k$, the coefficient of $X^n$ in
the power series $g h^k \in \mathbb{Q}[[X]]$. -/
noncomputable def entry (p : MotzkinRiordanPair) (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (p.g * p.h ^ k)

@[simp]
theorem entry_zero_right (p : MotzkinRiordanPair) (n : ℕ) : p.entry n 0 = p.g.coeff n := by
  simp [entry]

end MotzkinRiordanPair

/-- **The canonical Motzkin Riordan pair.** Let $s \in \mathbb{Q}[[X]]$ be the canonical square
root of $1 - 2X - 3X^2$, given by the binomial series, which has constant coefficient $1$. The
canonical Motzkin Riordan pair is $(g, h)$ with $g = s^{-1}$ and $h = (1 - X - s)/(2X)$, the
Motzkin Riordan pair conditions being witnessed by $s$. -/
noncomputable def motzkinRiordanPair : MotzkinRiordanPair where
  g := motzkinG
  h := motzkinH
  isPair := ⟨motzkinSquareRoot, motzkinSquareRoot_isSquareRoot,
    motzkinG_mul_motzkinSquareRoot, two_mul_X_mul_motzkinH⟩

/-- **Motzkin triangle.** Let $s$ be the square root of $1 - 2X - 3X^2$ in the ring of formal
power series over $\mathbb{Q}$ with constant coefficient $1$, and let $g = 1/s$ and
$h = (1 - X - s)/(2X)$. For natural numbers $n$ and $k$, the $(n, k)$ entry of the Motzkin
triangle (OEIS A094531) is the rational number given by the coefficient of $X^n$ in $g h^k$. -/
noncomputable def motzkinTriangle (n k : ℕ) : ℚ :=
  motzkinRiordanPair.entry n k

private theorem motzkinSquareRoot_coeff_one :
    PowerSeries.coeff 1 motzkinSquareRoot = -1 := by
  have hs := congrArg (PowerSeries.coeff 1) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_one_mul, motzkinDiscriminant,
    PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_two :
    PowerSeries.coeff 2 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 2) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_three :
    PowerSeries.coeff 3 motzkinSquareRoot = -2 := by
  have hs := congrArg (PowerSeries.coeff 3) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hs ⊢
  linarith

private theorem motzkinSquareRoot_coeff_four :
    PowerSeries.coeff 4 motzkinSquareRoot = -4 := by
  have hs := congrArg (PowerSeries.coeff 4) motzkinSquareRoot_isSquareRoot.1
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinDiscriminant,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hs ⊢
  linarith

private theorem motzkinG_coeff_zero : PowerSeries.coeff 0 motzkinG = 1 := by
  simp [motzkinG, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    motzkinSquareRoot_isSquareRoot.2]

private theorem motzkinG_coeff_one : PowerSeries.coeff 1 motzkinG = 1 := by
  have hg := congrArg (PowerSeries.coeff 1) motzkinG_mul_motzkinSquareRoot
  rw [PowerSeries.coeff_one_mul] at hg
  have hg0 : PowerSeries.constantCoeff motzkinG = 1 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using motzkinG_coeff_zero
  norm_num [motzkinG_coeff_zero,
    hg0, motzkinSquareRoot_isSquareRoot.2, motzkinSquareRoot_coeff_one] at hg ⊢
  linarith

private theorem motzkinG_coeff_two : PowerSeries.coeff 2 motzkinG = 3 := by
  have hg := congrArg (PowerSeries.coeff 2) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two] at hg ⊢
  linarith

private theorem motzkinG_coeff_three : PowerSeries.coeff 3 motzkinG = 7 := by
  have hg := congrArg (PowerSeries.coeff 3) motzkinG_mul_motzkinSquareRoot
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinSquareRoot_isSquareRoot.2,
    motzkinSquareRoot_coeff_one, motzkinSquareRoot_coeff_two,
    motzkinSquareRoot_coeff_three] at hg ⊢
  linarith

private theorem motzkinH_coeff_zero : PowerSeries.coeff 0 motzkinH = 0 := by
  norm_num [motzkinH, motzkinSquareRoot_coeff_one]

private theorem motzkinH_coeff_one : PowerSeries.coeff 1 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_two]

private theorem motzkinH_coeff_two : PowerSeries.coeff 2 motzkinH = 1 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_three]

private theorem motzkinH_coeff_three : PowerSeries.coeff 3 motzkinH = 2 := by
  norm_num [motzkinH, PowerSeries.coeff_X, motzkinSquareRoot_coeff_four]

/-- **Initial rows of the Motzkin triangle.** Writing $T(n, k)$ for the $(n, k)$ entry of the
canonical Motzkin triangle, the rows $n = 0, 1, 2, 3$ (with $0 \le k \le n$) are
$T(0, 0) = 1$; $T(1, 0) = T(1, 1) = 1$; $T(2, 0) = 3$, $T(2, 1) = 2$, $T(2, 2) = 1$; and
$T(3, 0) = 7$, $T(3, 1) = 6$, $T(3, 2) = 3$, $T(3, 3) = 1$, matching OEIS A094531. -/
theorem motzkinTriangle_initial_rows :
    [[motzkinTriangle 0 0],
      [motzkinTriangle 1 0, motzkinTriangle 1 1],
      [motzkinTriangle 2 0, motzkinTriangle 2 1, motzkinTriangle 2 2],
      [motzkinTriangle 3 0, motzkinTriangle 3 1,
        motzkinTriangle 3 2, motzkinTriangle 3 3]] =
    [[1], [1, 1], [3, 2, 1], [7, 6, 3, 1]] := by
  norm_num [motzkinTriangle, motzkinRiordanPair, MotzkinRiordanPair.entry,
    pow_succ, PowerSeries.coeff_mul, Finset.antidiagonal, motzkinG_coeff_zero,
    motzkinG_coeff_one, motzkinG_coeff_two, motzkinG_coeff_three,
    motzkinH_coeff_zero, motzkinH_coeff_one, motzkinH_coeff_two,
    motzkinH_coeff_three]

end MetaMathlibExt
