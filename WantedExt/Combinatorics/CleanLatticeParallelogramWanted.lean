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

/-- The lattice `ℤ²` as a subset of `ℝ²`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1. -/
def latticePoints : Set (ℝ × ℝ) :=
  Set.range fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ))

/-- The parallelogram `{s u + t v : 0 ≤ s, t ≤ 1}` spanned by `u` and `v`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def latticeParallelogram (u v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ p = s • u + t • v}

/-- `P_{a,n}`, the parallelogram with vertices `(0,0)`, `(1,0)`, `(a,n)`, `(a+1,n)`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2. -/
def stdCleanParallelogram (a n : ℕ) : Set (ℝ × ℝ) :=
  latticeParallelogram (1, 0) (a, n)

/-- The affine unimodular map `x ↦ M x + u` (used with `det M = ±1`).

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def unimodularMap (M : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((M 0 0 : ℝ) * p.1 + (M 0 1 : ℝ) * p.2 + u.1, (M 1 0 : ℝ) * p.1 + (M 1 1 : ℝ) * p.2 + u.2)

/-- `P` and `Q` are unimodularly equivalent: some affine unimodular map sends `P` onto `Q`.
(The paper's displayed condition `T(P_1) = T(P_2)` is a typo for `T(P_1) = P_2`.)

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
def UnimodularlyEquivalent (P Q : Set (ℝ × ℝ)) : Prop :=
  ∃ (M : Matrix (Fin 2) (Fin 2) ℤ) (u : ℤ × ℤ), (M.det = 1 ∨ M.det = -1) ∧
    unimodularMap M u '' P = Q

/-- Every set is unimodularly equivalent to itself (identity matrix, zero translation).

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 1.1. -/
theorem unimodularlyEquivalent_refl (P : Set (ℝ × ℝ)) : UnimodularlyEquivalent P P := by
  refine ⟨1, 0, Or.inl Matrix.det_one, ?_⟩
  have : unimodularMap 1 0 = id := by
    funext p
    simp [unimodularMap]
  simp [this]

/-- A lattice parallelogram spanned by lattice points `u`, `v` is clean when its only lattice
points on the boundary are its four vertices.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2 (definition after Reznick). -/
def IsCleanParallelogram (u v : ℝ × ℝ) : Prop :=
  u ∈ latticePoints ∧ v ∈ latticePoints ∧
    frontier (latticeParallelogram u v) ∩ latticePoints = {0, u, v, u + v}

/-- The interior lattice points of `P_{a,n}` on the vertical line `x = k` (the paper's `S_k`),
as their `y`-coordinates.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 2. -/
def stdColumn (a n : ℕ) (k : ℤ) : Set ℤ :=
  {y | ((k : ℝ), (y : ℝ)) ∈ interior (stdCleanParallelogram a n)}

/-- For linearly independent `u`, `v`, the involution `p ↦ u + v - p`
(`s u + t v ↔ (1 - s) u + (1 - t) v`) is a bijection between the points of the triangle
`T_1 = conv{0, u, v}` and of `T_2 = conv{u, v, u + v}` that lie in the interior of the
parallelogram spanned by `u` and `v`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 1 (`integers-2026-A10-lem-1`). -/
public theorem_wanted antidiagonal_triangle_bijOn {u v : ℝ × ℝ} (huv : LinearIndependent ℝ ![u, v]) :
    Set.BijOn (fun p => u + v - p)
      (convexHull ℝ {0, u, v} ∩ interior (latticeParallelogram u v))
      (convexHull ℝ {u, v, u + v} ∩ interior (latticeParallelogram u v))

/-- For `n > 1`, `1 ≤ a < n` with `gcd(a, n) = 1`, and `a⁻¹ ∈ [1, n - 1]` with
`a a⁻¹ ≡ 1 (mod n)`, the clean parallelograms `P_{a,n}`, `P_{n-a,n}`, `P_{a⁻¹,n}`,
`P_{n-a⁻¹,n}` are unimodularly equivalent (each to `P_{a,n}`).

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 2 (`integers-2026-A10-lem-2`). -/
public theorem_wanted stdCleanParallelogram_unimodularlyEquivalent {a n ai : ℕ} (hn : 1 < n)
    (ha : 1 ≤ a) (han : a < n) (hcop : Nat.Coprime a n) (hai : 1 ≤ ai) (hain : ai < n)
    (hinv : a * ai ≡ 1 [MOD n]) :
    UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram (n - a) n) ∧
      UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram ai n) ∧
      UnimodularlyEquivalent (stdCleanParallelogram a n) (stdCleanParallelogram (n - ai) n)

/-- A clean lattice parallelogram spanned by `u`, `v` with area `n ≥ 2` is unimodularly
equivalent to some `P_{a,n}` with `1 ≤ a < n` and `gcd(a, n) = 1`. (For area `1` the unit
square has no such `a`.)

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 3 (`integers-2026-A10-thm-3`). -/
public theorem_wanted cleanParallelogram_unimodularlyEquivalent_std {u v : ℝ × ℝ} {n : ℕ}
    (hclean : IsCleanParallelogram u v) (hn : 2 ≤ n)
    (harea : volume (latticeParallelogram u v) = n) :
    ∃ a : ℕ, 1 ≤ a ∧ a < n ∧ Nat.Coprime a n ∧
      UnimodularlyEquivalent (latticeParallelogram u v) (stdCleanParallelogram a n)

/-- The lattice points in the interior of `P_{a,n}` are exactly
`⟨k(n-a)/n⟩ (1, 0) + (k/n) (a, n)` for `k = 1, …, n - 1`, where `⟨·⟩` is the fractional part.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 3 (`integers-2026-A10-lem-3`). -/
public theorem_wanted interior_stdCleanParallelogram_latticePoints {a n : ℕ} (ha : 1 ≤ a)
    (han : a < n) (hcop : Nat.Coprime a n) :
    interior (stdCleanParallelogram a n) ∩ latticePoints =
      (fun k : ℕ => (Int.fract ((k : ℝ) * (n - a) / n) + (k : ℝ) * a / n, (k : ℝ))) ''
        Set.Icc 1 (n - 1)

/-- The map `S(x, y) = -(x, y) + (a + 1, n)` sends `P_{a,n}` onto itself and is an isometry.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 4 (`integers-2026-A10-lem-4`). -/
public theorem_wanted stdCleanParallelogram_symmetry {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) :
    (fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)) '' stdCleanParallelogram a n =
        stdCleanParallelogram a n ∧
      Isometry fun p : ℝ × ℝ => ((a + 1 : ℝ) - p.1, (n : ℝ) - p.2)

/-- Lowest and highest interior lattice points of `P_{a,n}` on the line `x = k`: if `a = 1`,
they are `(1, 1)` and `(1, n - 1)`; if `a > 1`, they are `(k, ⌈(k-1)n/a⌉)` and `(k, ⌊kn/a⌋)` for
`2 ≤ k ≤ a - 1`, `(1, 1)` and `(1, ⌊n/a⌋)` for `k = 1`, and `(a, ⌈(a-1)n/a⌉)` and `(a, n - 1)`
for `k = a`.

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

/-- For `k, l ≥ 1` with `k + l = a + 1`, `L(S_k) + H(S_l) = (a + 1, n)`, i.e. `H(S_l)` and
`L(S_k)` are exchanged by `S`; hence `H(S_l)` lies on the boundary of the interior hull
`P_{a,n}^{(1)} = conv(interior(P_{a,n}) ∩ ℤ²)` iff `L(S_k)` does.

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

/-- The number of division steps of Euclid's algorithm on `(u, v)`: `0` when `v = 0`, otherwise
one more than on `(v, u mod v)`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 5.3 (division steps of the Euclidean algorithm). -/
def euclidSteps (u v : ℕ) : ℕ :=
  if h : v = 0 then 0 else euclidSteps v (u % v) + 1
termination_by v
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- `euclidSteps` on small inputs: `(2, 1)` needs one step, `(3, 2)` two, `(13, 8)` five.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 5.3. -/
theorem euclidSteps_small_values :
    euclidSteps 2 1 = 1 ∧ euclidSteps 3 2 = 2 ∧ euclidSteps 13 8 = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [euclidSteps]

/-- (Lamé, 1844) For `N ≥ 1`, if `u > v > 0` need exactly `N` division steps and `u` is the
smallest integer admitting such a `v`, then `u = F_{N+2}` and `v = F_{N+1}`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 7 (`integers-2026-A10-thm-7`). -/
public theorem_wanted lame_euclidSteps_minimal {N u v : ℕ} (hN : 1 ≤ N) (huv : v < u) (hv : 0 < v)
    (hsteps : euclidSteps u v = N)
    (hmin : ∀ u' v', v' < u' → 0 < v' → euclidSteps u' v' = N → u ≤ u') :
    u = Nat.fib (N + 2) ∧ v = Nat.fib (N + 1)

/-- Stark's convergent vectors of the regular continued fraction `[q_0, q_1, …]` of `x`:
`v_{-2} = (1, 0)`, `v_{-1} = (0, 1)` and, for `i ≥ 0`, `v_i = (B_i, A_i)` where `A_i / B_i` is the
`i`-th convergent (Mathlib's `GenContFract.nums` and `GenContFract.dens` of `GenContFract.of x`),
so that `v_i = v_{i-2} + q_i v_{i-1}`.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3 (CF algorithm). -/
def convergentVec (x : ℚ) (i : ℤ) : ℝ × ℝ :=
  if i = -2 then (1, 0)
  else if i = -1 then (0, 1)
  else ((((GenContFract.of x).dens i.toNat : ℚ) : ℝ), (((GenContFract.of x).nums i.toNat : ℚ) : ℝ))

/-- The partial quotient `q_i` of the regular continued fraction of `x`: `q_0 = ⌊x⌋` and, for
`i ≥ 1`, the `(i - 1)`-st partial denominator of `GenContFract.of x` (`0` past termination).

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Section 3. -/
def partialQuotient (x : ℚ) (i : ℕ) : ℚ :=
  if i = 0 then (GenContFract.of x).h else ((GenContFract.of x).partDens.get? (i - 1)).getD 0

/-- Initial convergent vectors: `v_{-2} = (1, 0)`, `v_{-1} = (0, 1)`, `v_0 = (1, ⌊x⌋)`, and
`q_0 = ⌊x⌋`.

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

/-- The recurrence `v_{i+2} = v_i + q_{i+2} v_{i+1}` for `i ≥ 0`, whenever `q_{i+2}` exists.

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

/-- The last partial quotient of the continued fraction `[q_0, …, q_m]` of `n / a`
(`1 ≤ a < n`) satisfies `q_m ≥ 2`. Here `m` is the least index at which `GenContFract.of (n / a)`
terminates.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 7 (`integers-2026-A10-lem-7`). -/
public theorem_wanted partialQuotient_last_ge_two {a n m : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hm : IsLeast {k | (GenContFract.of ((n : ℚ) / a)).TerminatedAt k} m) :
    2 ≤ partialQuotient ((n : ℚ) / a) m

/-- For `1 ≤ a < n` and `-2 ≤ i < m`, the parallelogram spanned by `v_i` and `v_{i+1}` contains
no lattice points other than its vertices, and `ℤ v_i + ℤ v_{i+1} = ℤ²`. (The determinant
identity `det(v_i, v_{i+1}) = (-1)^i` itself is Mathlib's `SimpContFract.determinant` for
`i ≥ 0`.)

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

/-- Let `d_i = |n B_i - a A_i| / √(n² + a²)` be the distance from `v_i = (B_i, A_i)` to the line
`y = (n / a) x`. For `1 ≤ a < n` coprime: `n / (2√(n² + a²)) > d_0 > d_1 > ⋯ > d_{m-1} > 0`; and
for `1 ≤ i ≤ m - 1`, every lattice point `(β, α)` with `0 < β < a`, `0 < α < n`, `β ≤ B_i`,
`(β, α) ≠ v_{i-1}, v_i` is farther from the line than `v_{i-1}`.

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

/-- Split `P_{a,n}` by the lines `y = (n / a)(x - 1/2)` and `y = n / 2` into the quarter
parallelograms `P_1` (lower left), `P_2` (lower right), `P_3` (upper right), `P_4` (upper left),
and let `S(p) = (a + 1, n) - p`. For `1 ≤ a < n` coprime and `0 ≤ i < m`: if `i` is even then
`v_i ∈ P_1` and `S(v_i) ∈ P_3`; if `i` is odd then `v_i + (1, 0) ∈ P_2` and
`S(v_i + (1, 0)) ∈ P_4` (the sets `V_1`, `V_2` of the paper).

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

/-- For `1 ≤ a < n` and `0 ≤ i ≤ m`, in the triangle `T_i` with vertices `0`, `v_{i-2}`, `v_i`:
the segment `[v_{i-2}, v_i]` contains exactly `q_i + 1` lattice points, `T_i` has no interior
lattice points, and every non-vertex lattice point of `T_i` lies on `[v_{i-2}, v_i]`.

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

/-- For `1 ≤ a < n` and `0 ≤ i ≤ m - 2`,
`det [[1, B_{i-2}, A_{i-2}], [1, B_i, A_i], [1, B_{i+2}, A_{i+2}]] = (-1)^{i-1} q_i q_{i+1} q_{i+2}`
(written `(-1)^{i+1}`).

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

/-- For `1 ≤ a < n` coprime with `n / a = [q_0, q_1, …, q_m]`, `m ≥ 2`, and `u_i = v_i + (1, 0)`
(so `u_{-1} = (1, 1)` and `u_m = (a + 1, n)`): the vertices of the interior hull
`P_{a,n}^{(1)} = conv(interior(P_{a,n}) ∩ ℤ²)` are exactly `u_{-1}`, `u_m - u_{-1}`, `u_i` and
`u_m - u_i` for odd `i < m`, and `v_i` and `u_m - v_i` for even `i < m`.

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

/-- For `1 ≤ a < n` coprime with `n / a = [q_0, …, q_m]` and interior hull
`P_{a,n}^{(1)}` of positive area: `P_{a,n}^{(1)}` has `2(m + 1)` vertices if `q_0 > 1` and `2m`
if `q_0 = 1`, and `∑_{i=0}^m q_i = area(P_{a,n}) - area(P_{a,n}^{(1)})`.

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

/-- For `1 ≤ a < n` coprime, the interior hull `P_{a,n}^{(1)}` is a clean lattice polygon (its
only boundary lattice points are its vertices) if and only if `n = F_k` and `a = F_{k-1}` or
`a = F_{k-2}` for some `k`.

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
