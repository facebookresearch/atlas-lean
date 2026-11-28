/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquares
import Mathlib.Tactic.Ring

/-!
# Choudhry's family (3.32) of square triples with square symmetric functions

For arbitrary integers $m$ and $n$, the three entries in (3.32) and all three of their
elementary symmetric functions are integer squares. The proof checks explicit square roots.
It writes the parameter polynomials in terms of $x = (2mn)^2$ and $y = (m^2 - n^2)^2$,
so that $x + y = (m^2 + n^2)^2$. The resulting polynomial identities require no division,
including when either parameter is zero or $m^2 = n^2$.

## References

* Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the Products of the Integers,
  Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026), Article A35, pp. 1–15,
  Theorem 2, family (3.32). https://math.colgate.edu/~integers/aa35/aa35.pdf
-/

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

local notation "shiftedQuartic" m:arg n:arg => m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4

local notation "firstDegreeTwelve" m:arg n:arg =>
  m ^ 12 - 26 * m ^ 10 * n ^ 2 + 79 * m ^ 8 * n ^ 4
    - 44 * m ^ 6 * n ^ 6 + 79 * m ^ 4 * n ^ 8 - 26 * m ^ 2 * n ^ 10 + n ^ 12

local notation "secondDegreeTwelve" m:arg n:arg =>
  m ^ 12 - 10 * m ^ 10 * n ^ 2 + 15 * m ^ 8 * n ^ 4
    - 204 * m ^ 6 * n ^ 6 + 15 * m ^ 4 * n ^ 8 - 10 * m ^ 2 * n ^ 10 + n ^ 12

private abbrev firstCubic (x y : ℤ) : ℤ :=
  x ^ 3 - x ^ 2 * y - 5 * x * y ^ 2 + y ^ 3

private abbrev secondCubic (x y : ℤ) : ℤ :=
  y ^ 3 - x * y ^ 2 - x ^ 2 * y - 3 * x ^ 3

private theorem family332_symmetric_sums (s t u : ℤ) (hu : u ^ 2 = s ^ 2 + t ^ 2) :
    let x := s ^ 2
    let y := t ^ 2
    let p := firstCubic x y
    let r := secondCubic x y
    let a := 4 * x ^ 2 * y * p ^ 2
    let b := (x + y) * (y - x) ^ 2 * p ^ 2
    let c := 4 * x * y ^ 2 * r ^ 2
    IsSquare (a + b + c) ∧ IsSquare (a * b + b * c + c * a) := by
  intro x y p r a b c
  let f := x ^ 4 + 10 * x ^ 2 * y ^ 2 - 4 * x * y ^ 3 + y ^ 4
  let g := x ^ 5 + 3 * x ^ 4 * y + 8 * x ^ 3 * y ^ 2 - 4 * x ^ 2 * y ^ 3 - x * y ^ 4 + y ^ 5
  have hsum : a + b + c = (x + y) * f ^ 2 := by
    dsimp only [a, b, c, p, r, f, firstCubic, secondCubic]
    ring
  have hpairs : a * b + b * c + c * a = 4 * x * y * p ^ 2 * g ^ 2 := by
    dsimp only [a, b, c, p, r, g, firstCubic, secondCubic]
    ring
  refine ⟨⟨u * f, ?_⟩, ⟨2 * s * t * p * g, ?_⟩⟩
  · rw [hsum, ← (show u ^ 2 = x + y from hu)]
    ring
  · rw [hpairs]
    dsimp only [x, y]
    ring

/-- **Choudhry's family (3.32) of square triples with square symmetric functions.** For all
integers $m$ and $n$, let $Q = m^4 - 6 m^2 n^2 + n^4$,
$P = m^{12} - 26 m^{10} n^2 + 79 m^8 n^4 - 44 m^6 n^6 + 79 m^4 n^8 - 26 m^2 n^{10} + n^{12}$ and
$R = m^{12} - 10 m^{10} n^2 + 15 m^8 n^4 - 204 m^6 n^6 + 15 m^4 n^8 - 10 m^2 n^{10} + n^{12}$,
and put $a = 64 m^4 n^4 (m^2 - n^2)^2 P^2$, $b = (m^2 + n^2)^2 Q^2 P^2$ and
$c = 16 m^2 n^2 (m^2 - n^2)^4 R^2$. Then each of $a$, $b$, $c$, $a + b + c$, $ab + bc + ca$ and
$abc$ is the square of an integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 2, family (3.32). -/
public theorem hasSquareElementarySymmetricFunctions_family332_and_entries_square
    (m n : ℤ) :
    let a := 64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 2
      * (firstDegreeTwelve m n) ^ 2
    let b := (m ^ 2 + n ^ 2) ^ 2 * (shiftedQuartic m n) ^ 2
      * (firstDegreeTwelve m n) ^ 2
    let c := 16 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 4
      * (secondDegreeTwelve m n) ^ 2
    HasSquareElementarySymmetricFunctions a b c ∧
      IsSquare a ∧ IsSquare b ∧ IsSquare c := by
  intro a b c
  let s := 2 * m * n
  let t := m ^ 2 - n ^ 2
  let u := m ^ 2 + n ^ 2
  let x := s ^ 2
  let y := t ^ 2
  let p := firstCubic x y
  let r := secondCubic x y
  have hu : u ^ 2 = x + y := by
    dsimp only [u, x, y, s, t]
    ring
  have hQ : shiftedQuartic m n = y - x := by
    dsimp only [x, y, s, t]
    ring
  have hP : firstDegreeTwelve m n = p := by
    dsimp only [p, firstCubic, x, y, s, t]
    ring
  have hR : secondDegreeTwelve m n = r := by
    dsimp only [r, secondCubic, x, y, s, t]
    ring
  have ha : a = 4 * x ^ 2 * y * p ^ 2 := by
    dsimp only [a]
    rw [hP]
    dsimp only [x, y, s, t]
    ring
  have hb : b = (x + y) * (y - x) ^ 2 * p ^ 2 := by
    change u ^ 2 * (shiftedQuartic m n) ^ 2 * (firstDegreeTwelve m n) ^ 2 = _
    rw [hu, hQ, hP]
  have hc : c = 4 * x * y ^ 2 * r ^ 2 := by
    dsimp only [c]
    rw [hR]
    dsimp only [x, y, s, t]
    ring
  have haSq : IsSquare a := by
    refine ⟨2 * x * t * p, ?_⟩
    rw [ha]
    dsimp only [y]
    ring
  have hbSq : IsSquare b := by
    refine ⟨u * (y - x) * p, ?_⟩
    rw [hb, ← hu]
    ring
  have hcSq : IsSquare c := by
    refine ⟨2 * s * y * r, ?_⟩
    rw [hc]
    dsimp only [x]
    ring
  refine ⟨(hasSquareElementarySymmetricFunctions_iff_of_isSquare haSq hbSq hcSq).2 ?_,
    haSq, hbSq, hcSq⟩
  rw [ha, hb, hc]
  exact family332_symmetric_sums s t u hu

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
