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

/-- **The integer lattice in the plane.** The lattice points of $\mathbb{R}^2$ are the points
$(a, b)$ with $a, b \in \mathbb{Z}$; they form the image of $\mathbb{Z}^2$ in $\mathbb{R}^2$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1. -/
def latticePoints : Set (ℝ × ℝ) :=
  Set.range fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ))

/-- **Parallelogram spanned by two vectors.** For $u, v \in \mathbb{R}^2$, the parallelogram
spanned by $u$ and $v$ is the set $\{s u + t v : 0 \le s \le 1,\ 0 \le t \le 1\}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def latticeParallelogram (u v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ p = s • u + t • v}

/-- **The parallelogram $P_{a,n}$.** For natural numbers $a$ and $n$, the set
$P_{a,n} \subseteq \mathbb{R}^2$ is the closed parallelogram spanned by $(1, 0)$ and $(a, n)$,
that is, the set of points $s (1, 0) + t (a, n)$ with $0 \le s \le 1$ and $0 \le t \le 1$. For
$n \ge 1$ it is the parallelogram with vertices $(0, 0)$, $(1, 0)$, $(a, n)$ and $(a + 1, n)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2. -/
def stdCleanParallelogram (a n : ℕ) : Set (ℝ × ℝ) :=
  latticeParallelogram (1, 0) (a, n)

/-- **Integer affine maps of the plane.** For a $2 \times 2$ integer matrix $M$ with entries
$m_{ij}$ and an integer vector $u = (u_1, u_2) \in \mathbb{Z}^2$, the map
$T_{M,u} : \mathbb{R}^2 \to \mathbb{R}^2$ is
$T_{M,u}(x, y) = (m_{11} x + m_{12} y + u_1, m_{21} x + m_{22} y + u_2)$, that is,
$p \mapsto M p + u$. It is an affine unimodular map when $\det M = \pm 1$; the definition itself
puts no condition on $\det M$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def unimodularMap (M : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((M 0 0 : ℝ) * p.1 + (M 0 1 : ℝ) * p.2 + u.1, (M 1 0 : ℝ) * p.1 + (M 1 1 : ℝ) * p.2 + u.2)

/-- **Unimodularly equivalent sets.** Two sets $P, Q \subseteq \mathbb{R}^2$ are unimodularly
equivalent when some affine unimodular map sends $P$ onto $Q$: there are a $2 \times 2$ integer
matrix $M$ with $\det M = 1$ or $\det M = -1$ and an integer vector $u \in \mathbb{Z}^2$ such that
$\{M x + u : x \in P\} = Q$.

In the paper's notation, where $T$ is the map and $P_1$ and $P_2$ are the two sets, the displayed
condition $T(P_1) = T(P_2)$ is a typo for $T(P_1) = P_2$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def UnimodularlyEquivalent (P Q : Set (ℝ × ℝ)) : Prop :=
  ∃ (M : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ), (M.det = 1 ∨ M.det = -1) ∧
    unimodularMap M u '' P = Q

/-- **Unimodular equivalence is reflexive.** Every subset $P$ of $\mathbb{R}^2$ is unimodularly
equivalent to itself (take the identity matrix and the zero translation).

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
theorem unimodularlyEquivalent_refl (P : Set (ℝ × ℝ)) : UnimodularlyEquivalent P P := by
  refine ⟨1, 0, Or.inl Matrix.det_one, ?_⟩
  have : unimodularMap 1 0 = id := by
    funext p
    simp [unimodularMap]
  simp [this]

/-- **Clean lattice parallelogram.** For points $u, v \in \mathbb{R}^2$, the parallelogram
spanned by $u$ and $v$ is clean when $u$ and $v$ are lattice points and the lattice points on the
boundary of the parallelogram are exactly $0$, $u$, $v$ and $u + v$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2 (definition after Reznick). -/
def IsCleanParallelogram (u v : ℝ × ℝ) : Prop :=
  u ∈ latticePoints ∧ v ∈ latticePoints ∧
    frontier (latticeParallelogram u v) ∩ latticePoints = {0, u, v, u + v}

/-- **Interior lattice points of $P_{a,n}$ on a vertical line.** For natural numbers $a$ and $n$,
let $P_{a,n}$ be the parallelogram spanned by $(1, 0)$ and $(a, n)$, with vertices $(0, 0)$,
$(1, 0)$, $(a, n)$, $(a + 1, n)$. For an integer $k$, the set $S_k$ is the set of integers $y$
such that $(k, y)$ lies in the interior of $P_{a,n}$, that is, the $y$-coordinates of the lattice
points in the interior of $P_{a,n}$ on the line $x = k$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2. -/
def stdColumn (a n : ℕ) (k : ℤ) : Set ℤ :=
  {y | ((k : ℝ), (y : ℝ)) ∈ interior (stdCleanParallelogram a n)}

/-- **Point reflection between the two triangles of a parallelogram.** Let $u$ and $v$ be
linearly independent vectors in $\mathbb{R}^2$ and let $P$ be the parallelogram they span. The map
$p \mapsto u + v - p$ is a bijection from the set of points of the triangle
$\operatorname{conv}\{0, u, v\}$ that lie in the interior of $P$ onto the set of points of the
triangle $\operatorname{conv}\{u, v, u + v\}$ that lie in the interior of $P$.

The map sends $s u + t v$ to $(1 - s) u + (1 - t) v$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 1 (`integers-2026-A10-lem-1`). -/
public theorem_wanted antidiagonal_triangle_bijOn {u v : ℝ × ℝ} (huv : LinearIndependent ℝ ![u, v]) :
    Set.BijOn (fun p => u + v - p)
      (convexHull ℝ {0, u, v} ∩ interior (latticeParallelogram u v))
      (convexHull ℝ {u, v, u + v} ∩ interior (latticeParallelogram u v))

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

/-- **Lowest and highest interior lattice points of $P_{a,n}$ on each vertical line.** Let $a$
and $n$ be natural numbers with $1 \le a < n$ and $\gcd(a, n) = 1$, let $P_{a,n}$ be the
parallelogram with vertices $(0, 0)$, $(1, 0)$, $(a, n)$, $(a + 1, n)$, and for an integer $k$
let $S_k$ be the set of integers $y$ such that $(k, y)$ lies in the interior of $P_{a,n}$. If
$a = 1$, the least element of $S_1$ is $1$ and the greatest is $n - 1$. If $a > 1$, then: for
every integer $k$ with $2 \le k \le a - 1$, the least element of $S_k$ is
$\lceil (k - 1) n / a \rceil$ and the greatest is $\lfloor k n / a \rfloor$; the least element of
$S_1$ is $1$ and the greatest is $\lfloor n / a \rfloor$; and the least element of $S_a$ is
$\lceil (a - 1) n / a \rceil$ and the greatest is $n - 1$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 5 (`integers-2026-A10-lem-5`). -/
public theorem_wanted stdColumn_least_greatest {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) :
    (a = 1 → IsLeast (stdColumn a n 1) 1 ∧ IsGreatest (stdColumn a n 1) (n - 1)) ∧
      (1 < a →
        (∀ k : ℕ, 2 ≤ k → k ≤ a - 1 →
          IsLeast (stdColumn a n k) ⌈(((k - 1 : ℕ) * n : ℕ) : ℚ) / a⌉ ∧
            IsGreatest (stdColumn a n k) ⌊((k * n : ℕ) : ℚ) / a⌋) ∧
        IsLeast (stdColumn a n 1) 1 ∧ IsGreatest (stdColumn a n 1) ⌊(n : ℚ) / a⌋ ∧
        IsLeast (stdColumn a n a) ⌈(((a - 1 : ℕ) * n : ℕ) : ℚ) / a⌉ ∧
        IsGreatest (stdColumn a n a) (n - 1))

/-- **Lowest and highest interior lattice points of $P_{a,n}$ on paired vertical lines.** Let $a$
and $n$ be natural numbers with $1 \le a < n$ and $\gcd(a, n) = 1$, let $P_{a,n}$ be the
parallelogram with vertices $(0, 0)$, $(1, 0)$, $(a, n)$, $(a + 1, n)$, and for an integer $k$
let $S_k$ be the set of integers $y$ such that $(k, y)$ lies in the interior of $P_{a,n}$. Let
$k, l \ge 1$ be natural numbers with $k + l = a + 1$, and suppose that $y_L$ is the least element
of $S_k$ and $y_H$ is the greatest element of $S_l$. Then $y_L + y_H = n$, and $(l, y_H)$ lies on
the boundary of the convex hull of the points of $\mathbb{Z}^2$ in the interior of $P_{a,n}$ if
and only if $(k, y_L)$ does.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 6 (`integers-2026-A10-lem-6`). -/
public theorem_wanted stdColumn_low_add_high {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l = a + 1)
    {yL yH : ℤ} (hL : IsLeast (stdColumn a n k) yL) (hH : IsGreatest (stdColumn a n l) yH) :
    yL + yH = n ∧
      ((((l : ℝ), (yH : ℝ)) ∈
          frontier (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints))) ↔
        (((k : ℝ), (yL : ℝ)) ∈
          frontier (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints))))

/-- **Number of steps of Euclid's algorithm.** For natural numbers $u$ and $v$, the number of
division steps of Euclid's algorithm on $(u, v)$ is $0$ if $v = 0$, and otherwise one more than
the number of division steps on $(v, u \bmod v)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 5.3 (division steps of the Euclidean algorithm). -/
def euclidSteps (u v : ℕ) : ℕ :=
  if h : v = 0 then 0 else euclidSteps v (u % v) + 1
termination_by v
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- **Euclid's algorithm on small inputs.** Euclid's algorithm takes exactly one division step
on $(2, 1)$, two division steps on $(3, 2)$ and five division steps on $(13, 8)$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 5.3. -/
theorem euclidSteps_small_values :
    euclidSteps 2 1 = 1 ∧ euclidSteps 3 2 = 2 ∧ euclidSteps 13 8 = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [euclidSteps]

/-- **Lamé's theorem (1844).** Let $F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$ be the
Fibonacci numbers, and let $N \ge 1$. Let $u > v > 0$ be natural numbers on which Euclid's
algorithm takes exactly $N$ division steps, and suppose that $u \le u'$ whenever $u' > v' > 0$
are natural numbers on which it takes exactly $N$ division steps. Then $u = F_{N+2}$ and
$v = F_{N+1}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 7 (`integers-2026-A10-thm-7`). -/
public theorem_wanted lame_euclidSteps_minimal {N u v : ℕ} (hN : 1 ≤ N) (huv : v < u) (hv : 0 < v)
    (hsteps : euclidSteps u v = N)
    (hmin : ∀ u' v', v' < u' → 0 < v' → euclidSteps u' v' = N → u ≤ u') :
    u = Nat.fib (N + 2) ∧ v = Nat.fib (N + 1)

/-- **Convergent vectors of a continued fraction.** Let $x$ be a rational number with regular
continued fraction $[q_0; q_1, q_2, \dots]$, and let $A_j$ and $B_j$ be the numerators and
denominators of its convergents, given by $A_{-2} = 0$, $A_{-1} = 1$, $B_{-2} = 1$, $B_{-1} = 0$
and $A_j = q_j A_{j-1} + A_{j-2}$, $B_j = q_j B_{j-1} + B_{j-2}$ for $j \ge 0$. Stark's
convergent vectors of $x$ are $v_j = (B_j, A_j)$ for $j \ge -2$, so $v_{-2} = (1, 0)$,
$v_{-1} = (0, 1)$ and $v_j = v_{j-2} + q_j v_{j-1}$ for every $j \ge 0$ for which $q_j$ exists.

If the expansion terminates with $q_m$, then $v_j = v_m$ for all $j > m$; for $j < -2$ the
value is set to $v_0$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3 (CF algorithm). -/
def convergentVec (x : ℚ) (i : ℤ) : ℝ × ℝ :=
  if i = -2 then (1, 0)
  else if i = -1 then (0, 1)
  else ((((GenContFract.of x).dens i.toNat : ℚ) : ℝ), (((GenContFract.of x).nums i.toNat : ℚ) : ℝ))

/-- **Partial quotients of a rational number.** Let $x$ be a rational number. The continued
fraction algorithm sets $x_0 = x$ and $q_0 = \lfloor x_0 \rfloor$ and, as long as $x_j$ is not an
integer, $x_{j+1} = 1/(x_j - q_j)$ and $q_{j+1} = \lfloor x_{j+1} \rfloor$; it stops at the first
index $m$ for which $x_m$ is an integer, so that $x = [q_0; q_1, \dots, q_m]$. For a natural
number $i$, the $i$-th partial quotient of $x$ is $q_i$ when $i \le m$ and $0$ when $i > m$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3. -/
def partialQuotient (x : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then (GenContFract.of x).h else ((GenContFract.of x).partDens.get? (i - 1)).getD 0

/-- **Initial convergent vectors.** For every rational number $x$, the convergent vectors of the
regular continued fraction of $x$ begin with $v_{-2} = (1, 0)$, $v_{-1} = (0, 1)$ and
$v_0 = (1, \lfloor x \rfloor)$, and its zeroth partial quotient is $q_0 = \lfloor x \rfloor$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3 (CF algorithm, Step 1 and Step 2). -/
theorem convergentVec_initial (x : ℚ) :
    convergentVec x (-2) = (1, 0) ∧ convergentVec x (-1) = (0, 1) ∧
      convergentVec x 0 = (1, ((⌊x⌋ : ℤ) : ℝ)) ∧ partialQuotient x 0 = ⌊x⌋ := by
  refine ⟨by simp [convergentVec], by simp [convergentVec], ?_, by
    simp [partialQuotient, GenContFract.of_h_eq_floor]⟩
  simp [convergentVec, GenContFract.zeroth_den_eq_one, GenContFract.zeroth_num_eq_h,
    GenContFract.of_h_eq_floor]

/-- **Recurrence for convergent vectors.** Let $x$ be a rational number with regular continued
fraction $[q_0; q_1, q_2, \dots]$ and convergent vectors $v_{-2}, v_{-1}, v_0, \dots$, and let
$i \ge 0$. If the expansion of $x$ has a term $b$ in position $i + 2$ (it does not terminate
before $q_{i+2}$), then $q_{i+2} = b$ and $v_{i+2} = v_i + b \, v_{i+1}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3 (CF algorithm, Step 3). -/
theorem convergentVec_recurrence (x : ℚ) (i : ℕ) {b : ℚ}
    (hb : (GenContFract.of x).partDens.get? (i + 1) = some b) :
    convergentVec x ((i : ℤ) + 2) =
      convergentVec x i + (b : ℝ) • convergentVec x ((i : ℤ) + 1) ∧
      partialQuotient x (i + 2) = b := by
  obtain ⟨gp, hs, hgb⟩ := GenContFract.exists_s_b_of_partDen hb
  have ha : gp.a = 1 := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hs)
  have hA := GenContFract.nums_recurrence hs rfl rfl
  have hB := GenContFract.dens_recurrence hs rfl rfl
  refine ⟨?_, by simp [partialQuotient, hb]⟩
  have h2 : ((i : ℤ) + 2).toNat = i + 2 := by omega
  have h1 : ((i : ℤ) + 1).toNat = i + 1 := by omega
  have h0 : (i : ℤ).toNat = i := by omega
  have n22 : (i : ℤ) + 2 ≠ -2 := by omega
  have n21 : (i : ℤ) + 2 ≠ -1 := by omega
  have n12 : (i : ℤ) + 1 ≠ -2 := by omega
  have n11 : (i : ℤ) + 1 ≠ -1 := by omega
  have n02 : (i : ℤ) ≠ -2 := by omega
  have n01 : (i : ℤ) ≠ -1 := by omega
  simp only [convergentVec, h2, h1, h0, hA, hB, ha, hgb, n22, n21, n12, n11, n02, n01,
    ite_false]
  ext <;> simp <;> ring

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

/-- **Lattice points of the parallelogram of two consecutive convergent vectors.** Let
$1 \le a < n$ be integers, let $n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction
of $n / a$, where $m$ is the least index at which it terminates, and let $v_i$ be its convergent
vectors. For every integer $i$ with $-2 \le i < m$, the lattice points of the parallelogram
spanned by $v_i$ and $v_{i+1}$ are exactly $0$, $v_i$, $v_{i+1}$ and $v_i + v_{i+1}$, and every
point of $\mathbb{Z}^2$ equals $s v_i + t v_{i+1}$ for some integers $s$ and $t$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 4 (`integers-2026-A10-thm-4`). -/
public theorem_wanted convergentVec_parallelogram_latticePoints {a n m : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m)
    {i : ℤ} (hi : -2 ≤ i) (him : i < m) :
    latticeParallelogram (convergentVec ((n : ℚ) / a) i) (convergentVec ((n : ℚ) / a) (i + 1)) ∩
        latticePoints =
      {0, convergentVec ((n : ℚ) / a) i, convergentVec ((n : ℚ) / a) (i + 1),
        convergentVec ((n : ℚ) / a) i + convergentVec ((n : ℚ) / a) (i + 1)} ∧
      ∀ p ∈ latticePoints, ∃ s t : ℤ,
        p = (s : ℝ) • convergentVec ((n : ℚ) / a) i + (t : ℝ) • convergentVec ((n : ℚ) / a) (i + 1)

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

/-- **A determinant of three convergent vectors.** Let $1 \le a < n$ be integers, let
$n / a = [q_0; q_1, \dots, q_m]$ be the regular continued fraction of $n / a$, where $m$ is the
least index at which it terminates, and let $v_j = (B_j, A_j)$ be its convergent vectors. Then
for every natural number $i$ with $i + 2 \le m$, the determinant of the $3 \times 3$ matrix with
rows $(1, B_{i-2}, A_{i-2})$, $(1, B_i, A_i)$ and $(1, B_{i+2}, A_{i+2})$ equals
$(-1)^{i+1} q_i q_{i+1} q_{i+2}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 10 (`integers-2026-A10-lem-10`). -/
public theorem_wanted convergentVec_det_three {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) {i : ℕ}
    (him : i + 2 ≤ m) :
    let v := convergentVec ((n : ℚ) / a)
    let q := partialQuotient ((n : ℚ) / a)
    Matrix.det !![1, (v ((i : ℤ) - 2)).1, (v ((i : ℤ) - 2)).2;
        1, (v i).1, (v i).2;
        1, (v ((i : ℤ) + 2)).1, (v ((i : ℤ) + 2)).2] =
      (-1) ^ (i + 1) * ((q i * q (i + 1) * q (i + 2) : ℚ) : ℝ)

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
