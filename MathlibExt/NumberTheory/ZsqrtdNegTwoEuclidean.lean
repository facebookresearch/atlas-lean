/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Floor
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Euclidean domain structure on `ℤ[√-2]`

The ring `ℤ√(-2)` with norm `N(a + b√-2) = a² + 2b²` is a Euclidean domain.
Division rounds each coordinate of the exact quotient in `ℚ(√-2)` to the nearest
integer; each rounding error is at most `1/2`, so the remainder norm is at most
`3/4` of the divisor norm.
-/

namespace Zsqrtd.NegTwo

@[expose] public section

open Zsqrtd

/-- **The norm on $\mathbb{Z}[\sqrt{-2}]$ is nonnegative.** For every $x = a + b\sqrt{-2}$ in
$\mathbb{Z}[\sqrt{-2}]$, the norm $N(x) = a^2 + 2b^2$ satisfies $N(x) \ge 0$. -/
public theorem norm_nonneg' (x : Zsqrtd (-2 : ℤ)) : 0 ≤ x.norm :=
  Zsqrtd.norm_nonneg (by norm_num) x

/-- **The norm on $\mathbb{Z}[\sqrt{-2}]$ vanishes only at zero.** For $x = a + b\sqrt{-2}$ in
$\mathbb{Z}[\sqrt{-2}]$ with norm $N(x) = a^2 + 2b^2$, we have $N(x) = 0$ if and only if
$x = 0$. -/
public theorem norm_eq_zero' {x : Zsqrtd (-2 : ℤ)} : x.norm = 0 ↔ x = 0 :=
  Zsqrtd.norm_eq_zero_iff (by norm_num) x

/-- **Nonzero elements of $\mathbb{Z}[\sqrt{-2}]$ have positive norm.** For $x = a + b\sqrt{-2}$
in $\mathbb{Z}[\sqrt{-2}]$ with norm $N(x) = a^2 + 2b^2$, we have $N(x) > 0$ if and only if
$x \ne 0$. -/
public theorem norm_pos' {x : Zsqrtd (-2 : ℤ)} : 0 < x.norm ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm, norm_eq_zero']
  simp [norm_nonneg']

/-- **The norm on $\mathbb{Z}[\sqrt{-2}]$ equals its absolute value.** For every
$x = a + b\sqrt{-2}$ in $\mathbb{Z}[\sqrt{-2}]$, the norm $N(x) = a^2 + 2b^2$ satisfies
$|N(x)| = N(x)$, where $|N(x)|$ is taken as a natural number and read back as an integer. -/
public theorem abs_natCast_norm' (x : Zsqrtd (-2 : ℤ)) :
    (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg' _)

/-- Division on `ℤ√(-2)`, rounding exact quotient coordinates to nearest integers. -/
public instance instDivNegTwo : Div (Zsqrtd (-2 : ℤ)) :=
  ⟨fun x y =>
    let n := (y.norm : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩

/-- **Rounding division on $\mathbb{Z}[\sqrt{-2}]$.** Let $x, y \in \mathbb{Z}[\sqrt{-2}]$ with
$y = c + d\sqrt{-2}$, let $\bar{y} = c - d\sqrt{-2}$ be its conjugate and $N(y) = c^2 + 2d^2$ its
norm, and write $x\bar{y} = u + v\sqrt{-2}$ with $u, v \in \mathbb{Z}$. The quotient defined in
this module is $x / y = \operatorname{round}(u / N(y)) +
\operatorname{round}(v / N(y))\sqrt{-2}$, where $u / N(y)$ and $v / N(y)$ are computed in
$\mathbb{Q}$ (division by $0$ gives $0$) and $\operatorname{round}$ sends a rational number to
the nearest integer, rounding halves up. -/
public theorem div_def' (x y : Zsqrtd (-2 : ℤ)) :
    x / y = ⟨round ((x * star y).re / y.norm : ℚ),
      round ((x * star y).im / y.norm : ℚ)⟩ := by
  change Zsqrtd.mk _ _ = _
  simp [div_eq_mul_inv]

/-- Remainder on `ℤ√(-2)`. -/
public instance instModNegTwo : Mod (Zsqrtd (-2 : ℤ)) :=
  ⟨fun x y => x - y * (x / y)⟩

/-- **Remainder of the rounding division on $\mathbb{Z}[\sqrt{-2}]$.** For all $x, y$ in
$\mathbb{Z}[\sqrt{-2}]$, the remainder defined in this module is $x \bmod y = x - y\,(x / y)$,
where $x / y$ is the rounding division of $\mathbb{Z}[\sqrt{-2}]$. -/
public theorem mod_def' (x y : Zsqrtd (-2 : ℤ)) : x % y = x - y * (x / y) :=
  rfl

/-- **Error of rounded integer division.** Let $a$ and $N$ be integers with $N > 0$, and let
$q$ be the integer nearest to the rational number $a/N$ (halves rounded up). Then
$|2(a - qN)| \le N$, that is, $a$ differs from $qN$ by at most $N/2$. -/
public theorem round_error (a N : ℤ) (hN : 0 < N) :
    |2 * (a - round (a / N : ℚ) * N)| ≤ N := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have h := abs_sub_round ((a : ℚ) / N)
  have heq : ((2 * (a - round ((a : ℚ) / N) * N) : ℤ) : ℚ)
      = 2 * (N : ℚ) * (((a : ℚ) / N) - round ((a : ℚ) / N)) := by
    have hNne : (N : ℚ) ≠ 0 := ne_of_gt hNq
    push_cast
    field_simp
  have hle : |((2 * (a - round ((a : ℚ) / N) * N) : ℤ) : ℚ)| ≤ (N : ℚ) := by
    rw [heq]
    calc |2 * (N : ℚ) * (((a : ℚ) / N) - round ((a : ℚ) / N))|
        = 2 * N * |((a : ℚ) / N) - round ((a : ℚ) / N)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ 2 by norm_num),
            abs_of_nonneg hNq.le]
      _ ≤ 2 * N * (1 / 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = (N : ℚ) := by ring
  rw [abs_le] at hle
  have h1 : -N ≤ 2 * (a - round ((a : ℚ) / N) * N) := by exact_mod_cast hle.1
  have h2 : 2 * (a - round ((a : ℚ) / N) * N) ≤ N := by exact_mod_cast hle.2
  exact abs_le.mpr ⟨h1, h2⟩

/-- **Norm identity for the remainder.** Let $x, y, q \in \mathbb{Z}[\sqrt{-2}]$, write
$N(a + b\sqrt{-2}) = a^2 + 2b^2$ for the norm and $\bar{y}$ for the conjugate of $y$, and write
$x\bar{y} = u + v\sqrt{-2}$ and $q = e + f\sqrt{-2}$ with $u, v, e, f \in \mathbb{Z}$. Then
$N(y)\,N(x - yq) = (u - N(y)\,e)^2 + 2\,(v - N(y)\,f)^2$. -/
public theorem norm_key (x y q : Zsqrtd (-2 : ℤ)) :
    y.norm * (x - y * q).norm
      = ((x * star y).re - y.norm * q.re) * ((x * star y).re - y.norm * q.re)
        + 2 * (((x * star y).im - y.norm * q.im)
          * ((x * star y).im - y.norm * q.im)) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  obtain ⟨e, f⟩ := q
  simp only [Zsqrtd.norm_def, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul,
    Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- **The remainder is smaller than the divisor in $\mathbb{Z}[\sqrt{-2}]$.** Let $x, y$ be
elements of $\mathbb{Z}[\sqrt{-2}]$ with $y \ne 0$, and let $N(a + b\sqrt{-2}) = a^2 + 2b^2$ be
the norm. The remainder $x \bmod y = x - y\,(x / y)$ of the rounding division of
$\mathbb{Z}[\sqrt{-2}]$ satisfies $N(x \bmod y) < N(y)$. -/
public theorem norm_mod_lt' (x : Zsqrtd (-2 : ℤ)) {y : Zsqrtd (-2 : ℤ)}
    (hy : y ≠ 0) : (x % y).norm < y.norm := by
  have hN : 0 < y.norm := norm_pos'.mpr hy
  have hA := round_error (x * star y).re y.norm hN
  have hB := round_error (x * star y).im y.norm hN
  have hq := div_def' x y
  have hqr : round (((x * star y).re : ℤ) / (y.norm : ℤ) : ℚ) = (x / y).re := by
    rw [hq]
  have hqi : round (((x * star y).im : ℤ) / (y.norm : ℤ) : ℚ) = (x / y).im := by
    rw [hq]
  rw [hqr] at hA
  rw [hqi] at hB
  have hA2 : (2 * ((x * star y).re - (x / y).re * y.norm))
      * (2 * ((x * star y).re - (x / y).re * y.norm)) ≤ y.norm * y.norm := by
    have hmem := abs_le.mp hA
    have hnn : (0 : ℤ)
        ≤ (y.norm - 2 * ((x * star y).re - (x / y).re * y.norm))
          * (y.norm + 2 * ((x * star y).re - (x / y).re * y.norm)) :=
      mul_nonneg (by linarith only [hmem]) (by linarith only [hmem])
    linarith only [hnn]
  have hB2 : (2 * ((x * star y).im - (x / y).im * y.norm))
      * (2 * ((x * star y).im - (x / y).im * y.norm)) ≤ y.norm * y.norm := by
    have hmem := abs_le.mp hB
    have hnn : (0 : ℤ)
        ≤ (y.norm - 2 * ((x * star y).im - (x / y).im * y.norm))
          * (y.norm + 2 * ((x * star y).im - (x / y).im * y.norm)) :=
      mul_nonneg (by linarith only [hmem]) (by linarith only [hmem])
    linarith only [hnn]
  have key := norm_key x y (x / y)
  rw [← mod_def'] at key
  have hNsq : (0 : ℤ) < y.norm * y.norm := mul_pos hN hN
  have h4 : 4 * (y.norm * (x % y).norm) ≤ 3 * (y.norm * y.norm) := by
    linarith only [key, hA2, hB2]
  have h5 : 4 * (y.norm * (x % y).norm) < 4 * (y.norm * y.norm) := by
    linarith only [h4, hNsq]
  have h6 : y.norm * (x % y).norm < y.norm * y.norm := by linarith only [h5]
  exact lt_of_mul_lt_mul_left h6 hN.le

/-- **The remainder is smaller than the divisor, in absolute norm.** Let $x, y$ be elements of
$\mathbb{Z}[\sqrt{-2}]$ with $y \ne 0$, and let $N(a + b\sqrt{-2}) = a^2 + 2b^2$ be the norm.
The remainder $x \bmod y = x - y\,(x / y)$ of the rounding division of $\mathbb{Z}[\sqrt{-2}]$
satisfies $|N(x \bmod y)| < |N(y)|$ as natural numbers. -/
public theorem natAbs_norm_mod_lt' (x : Zsqrtd (-2 : ℤ)) {y : Zsqrtd (-2 : ℤ)}
    (hy : y ≠ 0) : (x % y).norm.natAbs < y.norm.natAbs := by
  have h1 : ((x % y).norm.natAbs : ℤ) = (x % y).norm :=
    Int.natAbs_of_nonneg (norm_nonneg' _)
  have h2 : (y.norm.natAbs : ℤ) = y.norm := Int.natAbs_of_nonneg (norm_nonneg' _)
  apply Int.ofNat_lt.mp
  rw [h1, h2]
  exact norm_mod_lt' x hy

/-- **Multiplying by a nonzero element does not decrease the norm in $\mathbb{Z}[\sqrt{-2}]$.**
Let $N(a + b\sqrt{-2}) = a^2 + 2b^2$ be the norm on $\mathbb{Z}[\sqrt{-2}]$. For
$x, y \in \mathbb{Z}[\sqrt{-2}]$ with $y \ne 0$, we have $|N(x)| \le |N(xy)|$ as natural
numbers. -/
public theorem norm_le_norm_mul_left' (x : Zsqrtd (-2 : ℤ)) {y : Zsqrtd (-2 : ℤ)}
    (hy : y ≠ 0) : x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm']
    exact Int.add_one_le_of_lt (norm_pos'.mpr hy)))

/-- `ℤ√(-2)` is nontrivial. -/
public instance instNontrivial' : Nontrivial (Zsqrtd (-2 : ℤ)) :=
  ⟨⟨0, 1, by intro h; have := congrArg Zsqrtd.re h; simp at this⟩⟩

/-- `ℤ[√-2]` is a Euclidean domain. -/
public instance instEuclideanDomainNegTwo : EuclideanDomain (ℤ√(-2 : ℤ)) :=
  { Zsqrtd.commRing, instNontrivial' with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      have h1 : (a * star (0 : Zsqrtd (-2 : ℤ))).re = 0 := by simp
      have h2 : (a * star (0 : Zsqrtd (-2 : ℤ))).im = 0 := by simp
      rw [div_def', h1, h2]
      refine Zsqrtd.ext ?_ ?_ <;> simp
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def']
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt'
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left' a hb0 }

end

end Zsqrtd.NegTwo
