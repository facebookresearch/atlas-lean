/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic packing polynomials on lattice sectors

The shear sending `(x, y)` to `(x - y/2, y)` turns the staircases of the sector of slope
`12/7` into vertical lines. On the sheared lattice the quadratic polynomial of Brandt and
Gjaldbæk's Example 10 takes every natural-number value exactly once.

## References

- Madeline Brandt and Kåre Schou Gjaldbæk, *Classification of Quadratic Packing Polynomials on
  Sectors of R^2*, INTEGERS 25 (2025), Article A81, pp. 1–23, Definition 1, Section 2,
  and Example 10.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Lattice points of a sector.** For a real number $\alpha$, let
$S(\alpha) = \{(x, y) \in \mathbb{R}^2 : 0 \le y \le \alpha x\}$ be the sector of slope
$\alpha$. Its lattice points are $I(\alpha) = S(\alpha) \cap \mathbb{Z}^2$, viewed as a subset
of $\mathbb{R}^2$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `S(α)` and `I(α)`). -/
public def sectorLatticePoints (α : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ x y : ℤ, p = ((x : ℝ), (y : ℝ)) ∧ 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ α * x}

/-- **The origin is a lattice point of every sector.** For every real number $\alpha$, the
origin $(0, 0)$ lies in the set $I(\alpha)$ of lattice points of the sector of slope $\alpha$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 1 (definition of `I(α)`). -/
public theorem zero_mem_sectorLatticePoints (α : ℝ) : ((0 : ℝ), (0 : ℝ)) ∈ sectorLatticePoints α :=
  ⟨0, 0, by simp⟩

/-- **Quadratic packing polynomial.** A real function $P(x, y)$ of two real variables is a
quadratic packing polynomial (QPP) on a set $S \subseteq \mathbb{R}^2$ if it is a polynomial of
total degree two, that is, $P(x, y) = a x^2 + b x y + c y^2 + d x + e y + f$ for some real
$a, b, c, d, e, f$ with $a, b, c$ not all zero, and $P$ maps $S$ bijectively onto the set
$\mathbb{N}_0 = \{0, 1, 2, \dots\}$ of natural numbers.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public def IsQuadraticPackingPolynomial (S : Set (ℝ × ℝ)) (P : ℝ → ℝ → ℝ) : Prop :=
  (∃ a b c d e f : ℝ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      ∀ x y, P x y = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + f) ∧
    Set.BijOn (fun p : ℝ × ℝ => P p.1 p.2) S (Set.range ((↑) : ℕ → ℝ))

/-- A quadratic packing polynomial maps its domain bijectively onto the natural numbers. -/
public theorem IsQuadraticPackingPolynomial.bijOn {S : Set (ℝ × ℝ)} {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial S P) :
    Set.BijOn (fun p : ℝ × ℝ => P p.1 p.2) S (Set.range ((↑) : ℕ → ℝ)) :=
  hP.2

private theorem IsQuadraticPackingPolynomial.shear {S : Set (ℝ × ℝ)} {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial S P) (c : ℝ) :
    IsQuadraticPackingPolynomial ((fun p : ℝ × ℝ => (p.1 - c * p.2, p.2)) '' S)
      (fun x y => P (x + c * y) y) := by
  obtain ⟨a, b, d, e, f, g, hquad, hP_eq⟩ := hP.1
  refine ⟨⟨a, 2 * a * c + b, a * c ^ 2 + b * c + d, e, e * c + f, g, ?_, ?_⟩, ?_⟩
  · contrapose! hquad
    obtain ⟨ha, hb, hd⟩ := hquad
    simp_all
  · intro x y
    dsimp only
    rw [hP_eq]
    ring
  · have hInv : Function.Injective (fun p : ℝ × ℝ => (p.1 + c * p.2, p.2)) := by
      intro p q h
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      exact Prod.ext (by rw [h₂] at h₁; exact add_right_cancel h₁) h₂
    have himage : (fun p : ℝ × ℝ => (p.1 + c * p.2, p.2)) ''
        ((fun p : ℝ × ℝ => (p.1 - c * p.2, p.2)) '' S) = S := by
      rw [Set.image_image]
      simp
    exact hP.bijOn.comp (himage ▸ hInv.injOn.bijOn_image)

/-- Shearing the domain by `(x, y) ↦ (x - c * y, y)` and substituting the inverse shear
into the polynomial preserves and reflects the quadratic packing property. -/
public theorem isQuadraticPackingPolynomial_shear_iff {S : Set (ℝ × ℝ)} {P : ℝ → ℝ → ℝ}
    (c : ℝ) :
    IsQuadraticPackingPolynomial ((fun p : ℝ × ℝ => (p.1 - c * p.2, p.2)) '' S)
      (fun x y => P (x + c * y) y) ↔ IsQuadraticPackingPolynomial S P := by
  refine ⟨fun h => ?_, fun h => h.shear c⟩
  simpa [Set.image_image, neg_mul, sub_eq_add_neg] using h.shear (-c)

/-- **Quadratic packing polynomials take natural-number values.** If $P$ is a quadratic packing
polynomial on a set $S \subseteq \mathbb{R}^2$, then for every point $(x, y) \in S$ the value
$P(x, y)$ is a natural number.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Definition 1. -/
public theorem IsQuadraticPackingPolynomial.exists_nat_eq {S : Set (ℝ × ℝ)}
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial S P) {p : ℝ × ℝ} (hp : p ∈ S) :
    ∃ N : ℕ, (N : ℝ) = P p.1 p.2 :=
  hP.2.mapsTo hp

/-- **Staircases of a rational sector.** For natural numbers $m, n, i$, let
$l = \gcd(m - 1, n)$. The $i$-th staircase of the sector of slope $n/m$ is
$J_i = \{(x, y) \in I(n/m) : nx - (m - 1)y = li\}$, where $I(n/m)$ is the set of lattice points
of that sector.

If $m = 0$, the slope $n/m$ is read as $0$ and $l$ as $\gcd(0, n) = n$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public def sectorStaircase (m n i : ℕ) : Set (ℝ × ℝ) :=
  {p | p ∈ sectorLatticePoints ((n : ℝ) / m) ∧
    (n : ℝ) * p.1 - ((m : ℝ) - 1) * p.2 = (Nat.gcd (m - 1) n : ℝ) * i}

/-- **The origin lies on the zeroth staircase.** For all natural numbers $m, n$, the origin
$(0, 0)$ lies on the staircase $J_0$ of the sector of slope $n/m$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of the staircases `J_i`). -/
public theorem zero_mem_sectorStaircase_zero (m n : ℕ) :
    ((0 : ℝ), (0 : ℝ)) ∈ sectorStaircase m n 0 :=
  ⟨zero_mem_sectorLatticePoints _, by simp⟩

/-- **First height of a staircase.** For natural numbers $m, n, i$, the first height $\bar y_i$
of the staircase $J_i$ of the sector of slope $n/m$ is the least $y$-coordinate of a point of
$J_i$, that is, the height of its first step; it is $0$ if $J_i$ is empty.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public noncomputable def staircaseFirstHeight (m n i : ℕ) : ℕ :=
  sInf {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i}

/-- **The zeroth staircase starts at height zero.** For all natural numbers $m, n$, the first
height of the staircase $J_0$ of the sector of slope $n/m$ is $\bar y_0 = 0$; indeed the origin
lies on $J_0$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 3 (definition of `ȳ_i`). -/
public theorem staircaseFirstHeight_zero (m n : ℕ) : staircaseFirstHeight m n 0 = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨0, by simpa using zero_mem_sectorStaircase_zero m n⟩)

/-- **Step difference.** For natural numbers $m, n$ and a real function $P(x, y)$ of two real
variables, let $l = \gcd(m \mathbin{\dot-} 1, n)$, where $m \mathbin{\dot-} 1$ is subtraction
truncated at $0$ (so $l = n$ when $m = 0$). The step difference of $P$ for the sector of slope
$n/m$ is $k = P((m - 1)/l, n/l) - P(0, 0)$, with $m - 1$ here the real difference and division
by $l = 0$ read as $0$: the change $P(x + (m - 1)/l, y + n/l) - P(x, y)$ of $P$ between
consecutive steps of a staircase of the sector, evaluated at the base point $(0, 0)$.

For every polynomial of Stanton's form (Theorem 2 of the source) this difference does not
depend on the base point, which is how the source defines $k$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Section 2 (definition of `k`). -/
public noncomputable def consecutiveStepDifference (m n : ℕ) (P : ℝ → ℝ → ℝ) : ℝ :=
  P (((m : ℝ) - 1) / Nat.gcd (m - 1) n) ((n : ℝ) / Nat.gcd (m - 1) n) - P 0 0

/-- If the sheared form is `f x + c * y`, the step difference is `c` times the
vertical spacing `n / gcd (m - 1) n`. -/
public theorem consecutiveStepDifference_of_sheared_form {m n : ℕ} (hn : 0 < n)
    {P : ℝ → ℝ → ℝ} {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ x y, P (x + ((m : ℝ) - 1) / n * y) y = f x + c * y) :
    consecutiveStepDifference m n P = c * ((n : ℝ) / Nat.gcd (m - 1) n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hadd : (0 : ℝ) + ((m : ℝ) - 1) / n * ((n : ℝ) / Nat.gcd (m - 1) n) =
      ((m : ℝ) - 1) / Nat.gcd (m - 1) n := by rw [zero_add, div_mul_div_cancel₀ hn']
  rw [consecutiveStepDifference, ← hadd, h]
  have hzero := h 0 0
  simp only [mul_zero, add_zero] at hzero
  rw [hzero, add_sub_cancel_left]

/-- **Step difference of the slope-$12/7$ example.** Let
$P(x, y) = 6(x - y/2)(x - y/2 - 3/2) + x + y + 2$. For $m = 7$ and $n = 12$ (the sector of
slope $12/7$), the step difference of $P$ is $k = 3$: with $l = \gcd(6, 12) = 6$, one has
$P(1, 2) - P(0, 0) = 3$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10. -/
public theorem consecutiveStepDifference_example_twelve_sevenths :
    consecutiveStepDifference 7 12
      (fun x y => 6 * (x - y / 2) * (x - y / 2 - 3 / 2) + x + y + 2) = 3 := by
  have h : Nat.gcd (7 - 1) 12 = 6 := by norm_num
  simp only [consecutiveStepDifference, h]
  norm_num

namespace ShearedTwelveSevenths

private noncomputable abbrev sector : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (p.1 - 1 / 2 * p.2, p.2)) '' sectorLatticePoints ((12 : ℝ) / 7)

private noncomputable def value (p : ℝ × ℝ) : ℝ :=
  6 * p.1 * (p.1 - 3 / 2) + p.1 + 3 / 2 * p.2 + 2

-- Staircase i has abscissa i/2. Its heights have the parity of i and run up to 6i.
private noncomputable def point (i j : ℕ) : ℝ × ℝ :=
  ((i : ℝ) / 2, ↑(i % 2 + 2 * j))

private def width (i : ℕ) : ℕ := 3 * i + 1 - i % 2

private theorem mem_sector_iff {p : ℝ × ℝ} :
    p ∈ sector ↔ ∃ i j : ℕ, j < width i ∧ point i j = p := by
  constructor
  · rintro ⟨_, ⟨x, y, rfl, hy, hxy⟩, rfl⟩
    have hy' : 0 ≤ y := by exact_mod_cast hy
    have hxy' : 7 * y ≤ 12 * x := by
      exact_mod_cast (show 7 * (y : ℝ) ≤ 12 * x by linarith)
    let i := (2 * x - y).toNat
    let j := y.toNat / 2
    have hi : (i : ℤ) = 2 * x - y := by dsimp [i]; omega
    have height : ((i % 2 + 2 * j : ℕ) : ℤ) = y := by dsimp [j]; omega
    refine ⟨i, j, ?_, Prod.ext ?_ ?_⟩
    · unfold width
      omega
    · change (i : ℝ) / 2 = x - 1 / 2 * y
      have : (i : ℝ) = 2 * x - y := by exact_mod_cast hi
      linarith
    · change (↑(i % 2 + 2 * j) : ℝ) = y
      simpa only [Int.cast_natCast] using congrArg (Int.cast (R := ℝ)) height
  · rintro ⟨i, j, hj, rfl⟩
    let y := i % 2 + 2 * j
    let x := (i + y) / 2
    have hsum : 2 * x = i + y := by dsimp [x, y]; omega
    have hbound : 7 * y ≤ 12 * x := by
      unfold width at hj
      dsimp [y] at *
      omega
    refine ⟨((x : ℝ), (y : ℝ)), ⟨x, y, by simp, by positivity, ?_⟩, Prod.ext ?_ rfl⟩
    · push_cast
      have : 7 * (y : ℝ) ≤ 12 * x := by exact_mod_cast hbound
      linarith
    · change (x : ℝ) - 1 / 2 * y = i / 2
      have : 2 * (x : ℝ) = i + y := by exact_mod_cast hsum
      linarith

-- Count the points on the first t staircases in the congruence class r modulo 3.
private def offset (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => offset r t + width (3 * t + r)

private theorem offset_strictMono (r : ℕ) : StrictMono (offset r) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [offset]
  have h (i : ℕ) : 0 < width i := by unfold width; omega
  exact Nat.lt_add_of_pos_right (h _)

-- The next staircase of the same residue starts three above the current last value.
private theorem value_next (i : ℕ) :
    value (point (i + 3) 0) = value (point i 0) + 3 * width i := by
  have hparity : ((i + 3) % 2 : ℕ) + i % 2 = 1 := by omega
  have hwidth : width i + i % 2 = 3 * i + 1 := by unfold width; omega
  have hp : (↑((i + 3) % 2) : ℝ) + ↑(i % 2) = 1 := by exact_mod_cast hparity
  have hw : (width i : ℝ) + ↑(i % 2) = 3 * i + 1 := by exact_mod_cast hwidth
  simp only [value, point, Nat.mul_zero, Nat.add_zero, Nat.cast_add, Nat.cast_ofNat]
  linarith

private theorem value_point {r : ℕ} (hr : r < 3) (t j : ℕ) :
    value (point (3 * t + r) j) = ↑(2 - r + 3 * (offset r t + j)) := by
  have first : value (point (3 * t + r) 0) = ↑(2 - r + 3 * offset r t) := by
    induction t with
    | zero => interval_cases r <;> norm_num [value, point, offset]
    | succ t ih =>
      rw [show 3 * (t + 1) + r = (3 * t + r) + 3 by omega, value_next, ih, offset]
      push_cast
      ring
  simp only [value, point, Nat.mul_zero, Nat.add_zero] at first ⊢
  push_cast at first ⊢
  linarith

end ShearedTwelveSevenths

open ShearedTwelveSevenths

/-- **The slope-$12/7$ example on the sheared sector.** Let $M(x, y) = (x - y/2, y)$ and let
$\hat I(12/7) = M(I(12/7))$ be the image under $M$ of the lattice points $I(12/7)$ of the sector
of slope $12/7$. Then $\hat P(x, y) = 6x(x - 3/2) + x + \frac{3}{2} y + 2$ is a quadratic
packing polynomial on $\hat I(12/7)$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Example 10 and Figure 3 (`integers-2025-A81-thm-3`). -/
public theorem isQuadraticPackingPolynomial_sheared_example_twelve_sevenths :
    IsQuadraticPackingPolynomial
      ((fun p : ℝ × ℝ => (p.1 - 1 / 2 * p.2, p.2)) '' sectorLatticePoints ((12 : ℝ) / 7))
      (fun x y => 6 * x * (x - 3 / 2) + x + 3 / 2 * y + 2) := by
  refine ⟨⟨6, 0, 0, -8, 3 / 2, 2, Or.inl (by norm_num), fun x y => by ring⟩, ?_⟩
  change Set.BijOn value sector _
  have coordinates {p : ℝ × ℝ} (hp : p ∈ sector) :
      ∃ r < 3, ∃ t j : ℕ, j < width (3 * t + r) ∧ point (3 * t + r) j = p := by
    obtain ⟨i, j, hj, rfl⟩ := mem_sector_iff.mp hp
    refine ⟨i % 3, by omega, i / 3, j, ?_⟩
    rw [Nat.div_add_mod]
    exact ⟨hj, rfl⟩
  constructor
  · rintro p hp
    obtain ⟨r, hr, t, j, _, rfl⟩ := coordinates hp
    exact ⟨_, (value_point hr t j).symm⟩
  constructor
  · intro p hp q hq heq
    obtain ⟨r, hr, t, j, hj, rfl⟩ := coordinates hp
    obtain ⟨s, hs, u, k, hk, rfl⟩ := coordinates hq
    rw [value_point hr, value_point hs, Nat.cast_inj] at heq
    obtain rfl : r = s := by omega
    -- Equal values in this residue class lie in the same block of consecutive quotients.
    have htu : t = u := by
      apply le_antisymm <;> by_contra! h
      all_goals
        have hle := (offset_strictMono r).monotone (Nat.succ_le_of_lt h)
        rw [offset] at hle
        omega
    subst u
    congr 1
    omega
  · rintro _ ⟨n, rfl⟩
    let r := 2 - n % 3
    have hr : r < 3 := by dsimp [r]; omega
    -- Locate the block containing the quotient of n by 3.
    obtain ⟨t, _, hlo, hhi⟩ := (offset_strictMono r).tendsto_atTop.exists_le_lt_succ
      (show offset r 0 ≤ n / 3 from Nat.zero_le _)
    rw [offset] at hhi
    let j := n / 3 - offset r t
    refine ⟨point (3 * t + r) j, mem_sector_iff.mpr ⟨_, _, ?_, rfl⟩, ?_⟩
    · dsimp [j]
      omega
    · rw [value_point hr, Nat.cast_inj]
      have hres : 2 - r = n % 3 := by dsimp [r]; omega
      rw [hres]
      dsimp [j]
      omega

end

end MetaMathlibExt
