/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import MathlibExt.Combinatorics.CleanLatticeParallelogram.ConvergentVectors
public import MathlibExt.Combinatorics.CleanLatticeParallelogram.Determinant
public import MathlibExt.Combinatorics.CleanLatticeParallelogram.Lame
public import MathlibExt.Combinatorics.CleanLatticeParallelogram.PairedColumns
public import MathlibExt.Combinatorics.CleanLatticeParallelogram.Reflection

/-!
# Clean lattice parallelograms

Statements from Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric
Relationship between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026),
Article A10 (arXiv:2401.04356; TeX source read for the definitions).

Points of the plane are `ℝ × ℝ` (`ℝ²`) and lattice points are the images of `ℤ × ℤ`
(`latticePoints`). `latticeParallelogram u v` is `{s u + t v : 0 ≤ s, t ≤ 1}`; `P_{a,n}` is
`latticeParallelogram (1, 0) (a, n)`, the clean parallelogram with vertices `(0,0)`, `(1,0)`,
`(a,n)`, `(a+1,n)` (`1 ≤ a < n`, `gcd(a,n) = 1`). An affine unimodular map is
`x ↦ M x + u` with `M ∈ GL_2(ℤ)` and `u ∈ ℤ²` (`unimodularMap`). Interiors and boundaries are
the topological ones in `ℝ × ℝ`. Stark's convergent vectors `v_i = (B_i, A_i)` (`convergentVec`)
and the partial quotients `q_i` (`partialQuotient`) of `n / a` are read off Mathlib's
`GenContFract.of`; `m` is the least index at which `GenContFract.of (n / a)` terminates, so
`n / a = [q_0, …, q_m]`.
-/

open MeasureTheory

namespace MetaMathlibExt

@[expose] public section

/-- **Unimodular equivalences between the parallelograms $P_{b,n}$.** For natural numbers $b$
and $n$ let $P_{b,n}$ be the parallelogram spanned by $(1, 0)$ and $(b, n)$, with vertices
$(0, 0)$, $(1, 0)$, $(b, n)$, $(b + 1, n)$. Let $n$, $a$ and $a'$ be natural numbers with $n > 1$,
$1 \le a < n$, $\gcd(a, n) = 1$, $1 \le a' < n$ and $a a' \equiv 1 \pmod{n}$. Then $P_{a,n}$ is
unimodularly equivalent to each of $P_{n-a,n}$, $P_{a',n}$ and $P_{n-a',n}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 2 (`integers-2026-A10-lem-2`). -/
public theorem_wanted stdCleanParallelogram_unimodularlyEquivalent {a n ai : ℕ} (hn : 1 < n)
    (ha : 1 ≤ a) (han : a < n) (hcop : Nat.Coprime a n) (hai : 1 ≤ ai) (hain : ai < n)
    (hinv : a * ai ≡ 1 [MOD n]) :
    UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram (n - a) n) ∧
      UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram ai n) ∧
      UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram (n - ai) n)

/-- **Clean parallelograms are unimodularly equivalent to standard ones.** Let $u$ and $v$ be
lattice points spanning a clean lattice parallelogram $P$ whose area is an integer $n \ge 2$. Then
there is an integer $a$ with $1 \le a < n$ and $\gcd(a, n) = 1$ such that $P$ is unimodularly
equivalent to the standard clean parallelogram $P_{a,n}$.

For area $1$ (the unit square) there is no such $a$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 3 (`integers-2026-A10-thm-3`). -/
public theorem_wanted cleanParallelogram_unimodularlyEquivalent_std {u v : ℝ × ℝ} {n : ℕ}
    (hclean : IsCleanParallelogram u v) (hn : 2 ≤ n)
    (harea : volume (latticeParallelogram u v) = n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧ Nat.Coprime a n ∧
      UnimodularlyEquivalent (latticeParallelogram u v) (stdCleanParallelogram a n)

/-- **Interior lattice points of a standard clean parallelogram.** Let $1 \le a < n$ with
$\gcd(a, n) = 1$, let $P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, and
write $\langle x \rangle = x - \lfloor x \rfloor$ for the fractional part of a real number $x$.
The lattice points in the interior of $P_{a,n}$ are exactly the points
$\langle k(n - a)/n \rangle \, (1, 0) + (k/n) \, (a, n)$ for $k = 1, \dots, n - 1$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 3 (`integers-2026-A10-lem-3`). -/
public theorem_wanted interior_stdCleanParallelogram_latticePoints {a n : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n) :
    interior (stdCleanParallelogram a n) ∩ latticePoints =
      (fun k : ℕ => (Int.fract ((k : ℝ) * (n - a) / n) + (k : ℝ) * a / n, (k : ℝ))) ''
        Set.Icc 1 (n - 1)

/-- **The point reflection symmetry of $P_{a,n}$.** Let $a$ and $n$ be natural numbers with
$1 \le a < n$ and $\gcd(a, n) = 1$, let $P_{a,n} \subseteq \mathbb{R}^2$ be the parallelogram
with vertices $(0, 0)$, $(1, 0)$, $(a, n)$, $(a + 1, n)$, and let
$S : \mathbb{R}^2 \to \mathbb{R}^2$ be $S(x, y) = (a + 1 - x, n - y)$. Then $S(P_{a,n}) = P_{a,n}$,
and $S$ is an isometry of $\mathbb{R}^2$ for the maximum distance
$d((x, y), (x', y')) = \max(|x - x'|, |y - y'|)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 4 (`integers-2026-A10-lem-4`). -/
public theorem_wanted stdCleanParallelogram_symmetry {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) :
    (fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)) '' stdCleanParallelogram a n =
        stdCleanParallelogram a n ∧
      Isometry fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)

/-- **The last partial quotient of $n/a$ is at least $2$.** Let $a$ and $n$ be natural numbers
with $1 \le a < n$, and let $n/a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of
$n/a$, where $q_0 = \lfloor n/a \rfloor$ and $m$ is the number of partial quotients after $q_0$
produced by the continued fraction algorithm (so $m = 0$ exactly when $a$ divides $n$). Then
$q_m \ge 2$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 7 (`integers-2026-A10-lem-7`). -/
public theorem_wanted partialQuotient_last_ge_two {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) :
    2 ≤ partialQuotient ((n : ℚ) / a) m

/-- **Distances of the convergent vectors to the line $y = (n / a) x$.** Let $1 \le a < n$ be
coprime integers, let $n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of
$n / a$, where $m$ is the least index at which it terminates, and let $v_j = (B_j, A_j)$ be its
convergent vectors. For $p = (x, y) \in \mathbb{R}^2$ let $d(p) = |n x - a y| / \sqrt{n^2 + a^2}$
be the distance from $p$ to the line $y = (n / a) x$. Then: if $m \ge 1$, then
$d(v_0) < n / (2 \sqrt{n^2 + a^2})$ and $d(v_{m-1}) > 0$; for every natural number $i$ with
$i + 1 < m$ we have $d(v_{i+1}) < d(v_i)$, so the distances strictly decrease along
$v_0, v_1, \dots, v_{m-1}$; and for every $i$ with $1 \le i \le m - 1$, every lattice point
$(\beta, \alpha)$ with $0 < \beta < a$, $0 < \alpha < n$, $\beta \le B_i$ and
$(\beta, \alpha) \ne v_{i-1}, v_i$ satisfies $d(\beta, \alpha) > d(v_{i-1})$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 5 (`integers-2026-A10-thm-5`). -/
public theorem_wanted convergentVec_dist_strictAnti {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) :
    let d : ℝ × ℝ → ℝ := fun p => |(n : ℝ) * p.1 - a * p.2| / √((n : ℝ) ^ 2 + a ^ 2)
    (0 < m → d (convergentVec ((n : ℚ) / a) 0) < n / (2 * √((n : ℝ) ^ 2 + a ^ 2)) ∧
        0 < d (convergentVec ((n : ℚ) / a) ((m : ℤ) - 1))) ∧
      (∀ i : ℕ, i + 1 < m →
        d (convergentVec ((n : ℚ) / a) ((i : ℤ) + 1)) < d (convergentVec ((n : ℚ) / a) i)) ∧
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ m → ∀ β α : ℤ, 0 < β → β < a → 0 < α → α < n →
        (β : ℝ) ≤ (convergentVec ((n : ℚ) / a) i).1 →
        ((β : ℝ), (α : ℝ)) ≠ convergentVec ((n : ℚ) / a) ((i : ℤ) - 1) →
        ((β : ℝ), (α : ℝ)) ≠ convergentVec ((n : ℚ) / a) i →
        d (convergentVec ((n : ℚ) / a) ((i : ℤ) - 1)) < d ((β : ℝ), (α : ℝ))

/-- **Convergent vectors in the quarters of $P_{a,n}$.** Let $1 \le a < n$ be coprime integers,
let $n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, where $m$ is
the least index at which it terminates, and let $v_i$ be its convergent vectors. The lines
$y = (n / a)(x - 1/2)$ and $y = n / 2$ cut the parallelogram $P_{a,n}$ with vertices $(0, 0)$,
$(1, 0)$, $(a, n)$, $(a + 1, n)$ into four closed parallelograms: $P_1$ (lower left), spanned by
$(1/2, 0)$ and $(a/2, n/2)$, and its translates $P_2 = P_1 + (1/2, 0)$ (lower right),
$P_3 = P_1 + ((a + 1)/2, n/2)$ (upper right) and $P_4 = P_1 + (a/2, n/2)$ (upper left). Let
$S(p) = (a + 1, n) - p$. Then for every $i$ with $0 \le i < m$: if $i$ is even, then
$v_i \in P_1$ and $S(v_i) \in P_3$; if $i$ is odd, then $v_i + (1, 0) \in P_2$ and
$S(v_i + (1, 0)) \in P_4$.

These points form the sets $V_1$ and $V_2$ of the paper.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 8 (`integers-2026-A10-lem-8`). -/
public theorem_wanted convergentVec_mem_quarters {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) {i : ℕ} (him : i < m) :
    let P₁ := latticeParallelogram ((1 / 2 : ℝ), 0) ((a : ℝ) / 2, (n : ℝ) / 2)
    let S : ℝ × ℝ → ℝ × ℝ := fun p => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)
    let v := convergentVec ((n : ℚ) / a) i
    (Even i → v ∈ P₁ ∧ S v ∈ (· + ((1 / 2 : ℝ) + a / 2, (n : ℝ) / 2)) '' P₁) ∧
      (Odd i → v + (1, 0) ∈ (· + ((1 / 2 : ℝ), 0)) '' P₁ ∧
        S (v + (1, 0)) ∈ (· + ((a : ℝ) / 2, (n : ℝ) / 2)) '' P₁)

/-- **Lattice points of the triangle with vertices $0$, $v_{i-2}$, $v_i$.** Let $1 \le a < n$ be
integers, let $n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, where
$m$ is the least index at which it terminates, and let $v_j$ be its convergent vectors. For every
integer $i$ with $0 \le i \le m$, let $T_i$ be the closed triangle with vertices $0$, $v_{i-2}$
and $v_i$. Then the segment $[v_{i-2}, v_i]$ contains exactly $q_i + 1$ lattice points, the
interior of $T_i$ contains no lattice point, and every lattice point of $T_i$ other than its
vertices lies on the segment $[v_{i-2}, v_i]$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 9 (`integers-2026-A10-lem-9`). -/
public theorem_wanted convergentVec_triangle_latticePoints {a n m : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m)
    {i : ℕ} (him : i ≤ m) :
    let v' := convergentVec ((n : ℚ) / a) ((i : ℤ) - 2)
    let v := convergentVec ((n : ℚ) / a) i
    ((segment ℝ v' v ∩ latticePoints).ncard : ℚ) = partialQuotient ((n : ℚ) / a) i + 1 ∧
      interior (convexHull ℝ {0, v', v}) ∩ latticePoints = ∅ ∧
      (convexHull ℝ {0, v', v} ∩ latticePoints) \ {0, v', v} ⊆ segment ℝ v' v

/-- **Vertices of the interior hull of a standard clean parallelogram.** Let $1 \le a < n$ with
$\gcd(a, n) = 1$, let $P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, and let
$n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, with $m \ge 2$.
Write $A_i / B_i$ for its $i$-th convergent, and put $v_{-1} = (0, 1)$, $v_i = (B_i, A_i)$ for
$i \ge 0$, $u_i = v_i + (1, 0)$ (so $u_{-1} = (1, 1)$) and $w = (a + 1, n)$. Then the vertices of
the convex hull of the lattice points in the interior of $P_{a,n}$ are exactly $u_{-1}$ and
$w - u_{-1}$, the points $u_i$ and $w - u_i$ for odd $i$ with $0 \le i < m$, and the points $v_i$
and $w - v_i$ for even $i$ with $0 \le i < m$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 6 (`integers-2026-A10-thm-6`). -/
public theorem_wanted extremePoints_interiorHull_stdCleanParallelogram {a n m : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) (hm2 : 2 ≤ m) :
    let v := convergentVec ((n : ℚ) / a)
    let u : ℤ → ℝ × ℝ := fun i => v i + (1, 0)
    let um : ℝ × ℝ := ((a : ℝ) + 1, (n : ℝ))
    Set.extremePoints ℝ (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints)) =
      {u (-1), um - u (-1)} ∪ {p | ∃ i : ℕ, Odd i ∧ i < m ∧ (p = u i ∨ p = um - u i)} ∪
        {p | ∃ i : ℕ, Even i ∧ i < m ∧ (p = v i ∨ p = um - v i)}

/-- **Vertices and area of the interior hull of a standard clean parallelogram.** Let
$1 \le a < n$ with $\gcd(a, n) = 1$, let
$P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, let
$n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, and let $H$ be the
convex hull of the lattice points in the interior of $P_{a,n}$. If $H$ has positive area, then
$H$ has $2(m + 1)$ vertices when $q_0 > 1$ and $2m$ vertices otherwise (that is, when $q_0 = 1$),
and $q_0 + q_1 + \dots + q_m = \mathrm{area}(P_{a,n}) - \mathrm{area}(H)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 11 (`integers-2026-A10-lem-11`). -/
public theorem_wanted interiorHull_stdCleanParallelogram_vertices_area {a n m : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m)
    (hpos : 0 < volume (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints))) :
    let H := convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints)
    let q := partialQuotient ((n : ℚ) / a)
    (Set.extremePoints ℝ H).ncard = (if 1 < q 0 then 2 * (m + 1) else 2 * m) ∧
      ((∑ i ∈ Finset.range (m + 1), q i : ℚ) : ℝ) =
        (volume (stdCleanParallelogram a n)).toReal - (volume H).toReal

/-- **Clean interior hulls and Fibonacci numbers.** Let $F_0 = 0$, $F_1 = 1$,
$F_{k+2} = F_{k+1} + F_k$ be the Fibonacci numbers. Let $1 \le a < n$ with $\gcd(a, n) = 1$, let
$P_{a,n} = \{s (1, 0) + t (a, n) : 0 \le s \le 1,\ 0 \le t \le 1\}$, and let $H$ be the convex
hull of the lattice points in the interior of $P_{a,n}$. Then the lattice points on the boundary of
$H$ are exactly the vertices of $H$ if and only if there is a natural number $k$ with $n = F_k$
and either $a = F_{k-1}$ or $a = F_{k-2}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Corollary 1 (`integers-2026-A10-cor-1`). -/
public theorem_wanted interiorHull_stdCleanParallelogram_clean_iff_fib {a n : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n) :
    let H := convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints)
    frontier H ∩ latticePoints = Set.extremePoints ℝ H ↔
      ∃ k : ℕ, n = Nat.fib k ∧ (a = Nat.fib (k - 1) ∨ a = Nat.fib (k - 2))

end

end MetaMathlibExt
