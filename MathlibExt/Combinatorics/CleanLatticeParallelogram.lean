/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Clean lattice parallelograms

The standard lattice parallelogram is spanned by `(1, 0)` and `(a, n)`.
`stdColumn_least_greatest` gives the extremal heights of its interior lattice points on each
integer vertical line. The definitions and statements follow Gabriel Khan, Mizan R. Khan,
Riaz R. Khan, and Peng Zhao, *A Geometric Relationship between Continued Fractions and Clean
Lattice Parallelograms*, INTEGERS 26 (2026), Article A10 (arXiv:2401.04356).
-/

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

namespace stdColumn_least_greatest

/-- In coordinates along the two sides, the interior is the open unit square. -/
private theorem mem_interior_iff {a n : ℕ} (hn : 0 < n) (x y : ℝ) :
    (x, y) ∈ interior (stdCleanParallelogram a n) ↔
      (x - 1) * n < y * a ∧ y * a < x * n ∧ 0 < y ∧ y < n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := fun p => (p.1 - p.2 / n * a, p.2 / n)
      invFun := fun p => (p.1 + p.2 * a, p.2 * n)
      left_inv := fun p => by simp [div_mul_cancel₀ _ hn'.ne']
      right_inv := fun p => by simp [mul_div_cancel_right₀ _ hn'.ne']
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hP : stdCleanParallelogram a n = e ⁻¹' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
    ext p
    constructor
    · rintro ⟨s, t, hs₀, hs₁, ht₀, ht₁, rfl⟩
      simp [e, Prod.smul_mk, smul_eq_mul, mul_div_cancel_right₀ _ hn'.ne', hs₀, hs₁, ht₀, ht₁]
    · rintro ⟨hs, ht⟩
      refine ⟨(e p).1, (e p).2, hs.1, hs.2, ht.1, ht.2, ?_⟩
      ext <;> simp [e, div_mul_cancel₀ _ hn'.ne']
  rw [hP, ← e.preimage_interior, interior_prod_eq, interior_Icc]
  change ((0 < x - y / n * a ∧ x - y / n * a < 1) ∧ 0 < y / n ∧ y / n < 1) ↔ _
  rw [div_mul_eq_mul_div, sub_pos, sub_lt_comm (b := y * a / n), div_lt_iff₀ hn',
    lt_div_iff₀ hn', div_pos_iff_of_pos_right hn', div_lt_iff₀ hn', one_mul]
  tauto

/-- The height where a sloping edge crosses an integer vertical line. -/
private abbrev edge (a n j : ℕ) : ℚ := ((j * n : ℕ) : ℚ) / a

private theorem mem_column_iff {a n j : ℕ} (hj : j < a) (hn : 0 < n) (y : ℤ) :
    y ∈ stdColumn a n (↑(j + 1 : ℕ)) ↔ edge a n j < y ∧ (y : ℚ) < edge a n (j + 1) := by
  have ha : (0 : ℚ) < a := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  change ((((j + 1 : ℕ) : ℤ) : ℝ), (y : ℝ)) ∈ interior (stdCleanParallelogram a n) ↔ _
  rw [mem_interior_iff hn]
  simp only [edge, div_lt_iff₀ ha, lt_div_iff₀ ha, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Int.cast_add, Int.cast_one, Int.cast_natCast, add_sub_cancel_right]
  norm_cast
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hl, hu⟩
    refine ⟨hl, hu, ?_, ?_⟩
    · have : 0 < y * (a : ℤ) := lt_of_le_of_lt (by positivity) hl
      exact pos_of_mul_pos_left this (by positivity)
    · have hmax : ((j : ℤ) + 1) * n ≤ (a : ℤ) * n := by
        gcongr
        exact_mod_cast hj
      exact lt_of_mul_lt_mul_right (hu.trans_le (by simpa [mul_comm] using hmax)) (by positivity)

private theorem column_extrema {a n j : ℕ} (hj : j < a) (han : a < n) :
    IsLeast (stdColumn a n (↑(j + 1 : ℕ))) (⌊edge a n j⌋ + 1) ∧
      IsGreatest (stdColumn a n (↑(j + 1 : ℕ))) (⌈edge a n (j + 1)⌉ - 1) := by
  have ha : (0 : ℚ) < a := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hwidth : edge a n j + 1 < edge a n (j + 1) := by
    simp only [edge, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    linarith [show (a : ℚ) < n by exact_mod_cast han]
  have hle : ⌊edge a n j⌋ + 1 ≤ ⌈edge a n (j + 1)⌉ - 1 := by
    have hlt : ⌊edge a n j⌋ + 1 < ⌈edge a n (j + 1)⌉ := by
      apply Int.lt_ceil.mpr
      push_cast
      linarith [Int.floor_le (edge a n j)]
    omega
  have hset : stdColumn a n (↑(j + 1 : ℕ)) =
      Set.Icc (⌊edge a n j⌋ + 1) (⌈edge a n (j + 1)⌉ - 1) := by
    ext y
    rw [mem_column_iff hj (by omega), ← Int.floor_lt, ← Int.lt_ceil, Set.mem_Icc]
    omega
  exact hset ▸ ⟨isLeast_Icc hle, isGreatest_Icc hle⟩

private theorem ceil_eq_floor_add_one {a n j : ℕ} (hcop : Nat.Coprime a n)
    (hj : 0 < j) (hja : j < a) : ⌈edge a n j⌉ = ⌊edge a n j⌋ + 1 := by
  apply (Int.ceil_eq_floor_add_one_iff_notMem _).mpr
  rintro ⟨z, hz⟩
  have hd : a ∣ j * n := (Rat.den_div_natCast_eq_one_iff _ _ (by omega)).mp
    (show (edge a n j).den = 1 by rw [← hz, Rat.den_intCast])
  exact hja.not_ge (Nat.le_of_dvd hj (hcop.dvd_of_dvd_mul_right hd))

end stdColumn_least_greatest

open stdColumn_least_greatest

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
theorem stdColumn_least_greatest {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) :
    (a = 1 → IsLeast (stdColumn a n 1) 1 ∧ IsGreatest (stdColumn a n 1) (n - 1)) ∧
      (1 < a →
        (∀ k : ℕ, 2 ≤ k → k ≤ a - 1 →
          IsLeast (stdColumn a n k) ⌈(((k - 1 : ℕ) * n : ℕ) : ℚ) / a⌉ ∧
            IsGreatest (stdColumn a n k) ⌊((k * n : ℕ) : ℚ) / a⌋) ∧
        IsLeast (stdColumn a n 1) 1 ∧ IsGreatest (stdColumn a n 1) ⌊(n : ℚ) / a⌋ ∧
        IsLeast (stdColumn a n a) ⌈(((a - 1 : ℕ) * n : ℕ) : ℚ) / a⌉ ∧
        IsGreatest (stdColumn a n a) (n - 1)) := by
  have extrema (k : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) :
      IsLeast (stdColumn a n k) (⌊edge a n (k - 1)⌋ + 1) ∧
        IsGreatest (stdColumn a n k) (⌈edge a n k⌉ - 1) := by
    simpa only [Nat.sub_add_cancel hk] using
      (column_extrema (j := k - 1) (by omega : k - 1 < a) han)
  have first := extrema 1 le_rfl ha
  constructor
  · rintro rfl
    simpa [edge] using first
  · intro ha₁
    have last := extrema a ha le_rfl
    have ha' : (a : ℚ) ≠ 0 := by positivity
    have top : edge a n a = n := by simp [edge, mul_div_cancel_left₀ _ ha']
    rw [← ceil_eq_floor_add_one hcop (by omega : 0 < a - 1) (by omega), top,
      Int.ceil_natCast] at last
    rw [ceil_eq_floor_add_one hcop Nat.zero_lt_one ha₁, add_sub_cancel_right] at first
    have first' : IsLeast (stdColumn a n 1) 1 ∧ IsGreatest (stdColumn a n 1) ⌊(n : ℚ) / a⌋ := by
      simpa [edge] using first
    refine ⟨?_, first'.1, first'.2, last.1, last.2⟩
    intro k hk hka
    have middle := extrema k (by omega) (by omega)
    rwa [← ceil_eq_floor_add_one hcop (by omega : 0 < k - 1) (by omega),
      ceil_eq_floor_add_one hcop (by omega : 0 < k) (by omega), add_sub_cancel_right] at middle

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

end

end MetaMathlibExt
