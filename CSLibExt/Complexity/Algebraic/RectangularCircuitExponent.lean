/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.MatrixMultiplication
public import CSLibExt.Complexity.Algebraic.MatrixMultiplicationExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Rectangular matrix multiplication in the actual arithmetic-circuit model

The field is fixed before the asymptotic quantifiers. Each circuit must compute
every input matrix pair. Its coefficients and graph may depend on dimension and
epsilon, but not on those input values. The inner dimension is `ceil (n ^ k)`.

This operation exponent is distinct from the tensor-rank exponent. No asymptotic
equivalence, division-elimination result or field-characteristic transfer is assumed.
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

open MatrixMultiplicationExponent Filter

@[expose] public section

/-- **Admissible rectangular circuit exponents.** Let $F$ be a field and $k, w$ real numbers. The
exponent $w$ is admissible at aspect $k$ over $F$ when $k \ge 0$, $w \ge 0$, and for every
$\varepsilon > 0$ there are a real $C > 0$ and a natural number $N \ge 1$ such that for every
$n \ge N$ some arithmetic circuit over $F$ computes the product of an $n \times \lceil n^k \rceil$
matrix and an $\lceil n^k \rceil \times n$ matrix with at most $C n^{w + \varepsilon}$ gates.

The circuit may depend on $n$ and $\varepsilon$, and it must be correct on every pair of matrices
with entries in $F$. -/
def HasRectangularCircuitExponent (F : Type u) [Field F] (k w : ℝ) : Prop :=
  0 ≤ k ∧ 0 ≤ w ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∃ c : MatrixArithmeticCircuit F n (rectangularInnerDimension n k) n,
      IsMatrixMultiplication c ∧ (c.size : ℝ) ≤ C * (n : ℝ) ^ (w + ε)

/-- **Rectangular circuit exponent.** For a field $F$ and a real $k$, the rectangular circuit
exponent of $F$ at aspect $k$ is the infimum in $[0, \infty]$ of the admissible rectangular circuit
exponents for $F$ at aspect $k$: the reals $w \ge 0$ such that $k \ge 0$ and, for every
$\varepsilon > 0$, there are $C > 0$ and $N \ge 1$ such that for every $n \ge N$ some arithmetic
circuit over $F$ of size at most $C n^{w + \varepsilon}$ computes the product of an
$n \times \lceil n^k \rceil$ matrix and a $\lceil n^k \rceil \times n$ matrix. The infimum of the
empty family is $\infty$; in particular the exponent is $\infty$ when $k < 0$. -/
noncomputable def rectangularCircuitExponent (F : Type u) [Field F] (k : ℝ) : ENNReal :=
  sInf {W : ENNReal | ∃ w : ℝ, W = ENNReal.ofReal w ∧ HasRectangularCircuitExponent F k w}

/-- **Dual matrix multiplication exponent (arithmetic circuits).** For a field $F$, the dual
matrix multiplication exponent $\alpha(F) \in [0, \infty]$ of the arithmetic-circuit model is the
supremum of all real $k \ge 0$ at which the rectangular matrix multiplication exponent of the
arithmetic-circuit model over $F$ equals $2$. -/
noncomputable def dualCircuitExponent (F : Type u) [Field F] : ENNReal :=
  sSup {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
    rectangularCircuitExponent F k = 2}

/-- **Admissible exponents bound the rectangular circuit exponent.** Let $F$ be a field and let
$k$ and $w$ be reals. If $w$ is an admissible rectangular circuit exponent for $F$ at aspect $k$,
then the rectangular circuit exponent of $F$ at aspect $k$ is at most $w$. -/
theorem rectangularCircuitExponent_le_of_admissible (F : Type u) [Field F] {k w : ℝ}
    (h : HasRectangularCircuitExponent F k w) :
    rectangularCircuitExponent F k ≤ ENNReal.ofReal w := sInf_le ⟨w, rfl, h⟩

/-- **Lower bounds for the rectangular circuit exponent.** Let $F$ be a field, $k$ a real number
and $W \in [0, \infty]$. If $W \le w$ for every real $w$ that is an admissible exponent at aspect
$k$ over $F$, then $W$ is at most the rectangular matrix multiplication exponent of the
arithmetic-circuit model over $F$ at aspect $k$. -/
theorem le_rectangularCircuitExponent (F : Type u) [Field F] {k : ℝ} {W : ENNReal}
    (h : ∀ w : ℝ, HasRectangularCircuitExponent F k w → W ≤ ENNReal.ofReal w) :
    W ≤ rectangularCircuitExponent F k := by
  apply le_sInf
  rintro _ ⟨w, rfl, hw⟩
  exact h w hw

/-- **Aspects with circuit exponent two bound the dual exponent.** Let $F$ be a field and $k \ge 0$
a real number. If the rectangular matrix multiplication exponent of the arithmetic-circuit model
over $F$ at aspect $k$ equals $2$, then $k \le \alpha(F)$, where $\alpha(F)$ is the dual matrix
multiplication exponent of the arithmetic-circuit model. -/
theorem le_dualCircuitExponent (F : Type u) [Field F] {k : ℝ} (hk : 0 ≤ k)
    (h : rectangularCircuitExponent F k = 2) : ENNReal.ofReal k ≤ dualCircuitExponent F :=
  le_sSup ⟨k, hk, rfl, h⟩

/-- **Upper bounds for the dual circuit exponent.** Let $F$ be a field and $K \in [0, \infty]$.
If $k \le K$ for every real $k \ge 0$ at which the rectangular matrix multiplication exponent of
the arithmetic-circuit model over $F$ equals $2$, then the dual matrix multiplication exponent
$\alpha(F)$ of the arithmetic-circuit model satisfies $\alpha(F) \le K$. -/
theorem dualCircuitExponent_le (F : Type u) [Field F] {K : ENNReal}
    (h : ∀ k : ℝ, 0 ≤ k → rectangularCircuitExponent F k = 2 → ENNReal.ofReal k ≤ K) :
    dualCircuitExponent F ≤ K := by
  apply sSup_le
  rintro _ ⟨k, hk, rfl, he⟩
  exact h k hk he

/-- **Exponent two is admissible at aspect zero.** For every field $F$, the exponent $2$ is an
admissible rectangular circuit exponent at aspect $0$ over $F$: for every $\varepsilon > 0$ there
are a real $C > 0$ and a natural number $N \ge 1$ such that for every $n \ge N$ some arithmetic
circuit over $F$ computes the product of an $n \times \lceil n^0 \rceil$ matrix and a
$\lceil n^0 \rceil \times n$ matrix, that is of an $n \times 1$ matrix and a $1 \times n$ matrix,
with at most $C n^{2 + \varepsilon}$ gates.

The outer-product circuit, with $n^2$ gates, is such a circuit. -/
theorem hasRectangularCircuitExponent_zero_two (F : Type u) [Field F] :
    HasRectangularCircuitExponent F 0 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro ε hε
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro n hn
  rw [rectangularInnerDimension_zero]
  refine ⟨outerMatrixCircuit F n n, outerMatrixCircuit_correct n n, ?_⟩
  simp only [outerMatrixCircuit_size, Nat.cast_mul, one_mul]
  calc
    (n : ℝ) * n = (n : ℝ) ^ (2 : ℝ) := by norm_num [Real.rpow_natCast, pow_two]
    _ ≤ (n : ℝ) ^ (2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-- **The rounded inner dimension is positive.** For every natural number $n \ge 1$ and every real
$k$, the rounded inner dimension $\lceil n^k \rceil$ is positive. -/
theorem rectangularInnerDimension_pos {n : ℕ} (hn : 1 ≤ n) (k : ℝ) :
    0 < rectangularInnerDimension n k := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) k)

/-- **Admissible rectangular circuit exponents are at least two.** Let $F$ be a field and let $k$
and $w$ be reals. If $w$ is an admissible rectangular circuit exponent for $F$ at aspect $k$, then
$w \ge 2$.

A circuit computing the product of an $n \times \lceil n^k \rceil$ matrix and a
$\lceil n^k \rceil \times n$ matrix with $n \ge 1$ has a separate gate for each of the $n^2$ output
entries, so it has at least $n^2$ gates. -/
theorem HasRectangularCircuitExponent.two_le {F : Type u} [Field F] {k w : ℝ}
    (h : HasRectangularCircuitExponent F k w) : 2 ≤ w := by
  by_contra hw
  have hε : 0 < (2 - w) / 2 := by linarith
  obtain ⟨C, _, N, hN, hb⟩ := h.2.2 ((2 - w) / 2) hε
  let p : ℝ := w + (2 - w) / 2
  have hd : 0 < 2 - p := by dsimp [p]; linarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 - p)) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hnC, hn⟩ :=
    ((ht.eventually (eventually_gt_atTop C)).and (eventually_ge_atTop N)).exists
  obtain ⟨c, hc, hs⟩ := hb n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hN.trans hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have ho : (n : ℝ) * n ≤ (c.size : ℝ) := by
    exact_mod_cast hc.output_cost_le ⟨0, rectangularInnerDimension_pos (hN.trans hn) k⟩
  have hmul := mul_lt_mul_of_pos_left hnC (Real.rpow_pos_of_pos hnpos p)
  rw [mul_comm ((n : ℝ) ^ p) C, ← Real.rpow_add hnpos] at hmul
  have he : p + (2 - p) = 2 := by linarith
  rw [he] at hmul
  have ho' : (n : ℝ) ^ (2 : ℝ) ≤ C * (n : ℝ) ^ p := by
    calc
      (n : ℝ) ^ (2 : ℝ) = (n : ℝ) * n := by norm_num [Real.rpow_natCast, pow_two]
      _ ≤ C * (n : ℝ) ^ p := ho.trans hs
  exact (not_lt_of_ge ho') hmul

/-- **The rectangular circuit exponent is at least two.** For every field $F$ and every real $k$,
the rectangular circuit exponent of $F$ at aspect $k$ is at least $2$ (it may be $\infty$). -/
theorem two_le_rectangularCircuitExponent (F : Type u) [Field F] (k : ℝ) :
    2 ≤ rectangularCircuitExponent F k := by
  apply le_rectangularCircuitExponent F
  intro w hw
  simpa using ENNReal.ofReal_le_ofReal hw.two_le

/-- **The rectangular circuit exponent at aspect zero is two.** For every field $F$, the
rectangular circuit exponent of $F$ at aspect $0$ equals $2$.

The upper bound comes from the outer-product circuit, which multiplies an $n \times 1$ matrix by a
$1 \times n$ matrix with $n^2$ multiplications. -/
theorem rectangularCircuitExponent_zero (F : Type u) [Field F] :
    rectangularCircuitExponent F 0 = 2 := by
  apply le_antisymm
  · simpa using rectangularCircuitExponent_le_of_admissible F
      (hasRectangularCircuitExponent_zero_two F)
  · exact two_le_rectangularCircuitExponent F 0

/-- **Some aspect has rectangular circuit exponent two.** For every field $F$, there is a real
$k \ge 0$ at which the rectangular matrix multiplication exponent of the arithmetic-circuit model
over $F$ equals $2$. Hence the set of such $k$, viewed in $[0, \infty]$, whose supremum is the dual
matrix multiplication exponent, is nonempty. -/
theorem dualCircuitExponent_family_nonempty (F : Type u) [Field F] :
    {K : ENNReal | ∃ k : ℝ, 0 ≤ k ∧ K = ENNReal.ofReal k ∧
      rectangularCircuitExponent F k = 2}.Nonempty :=
  ⟨0, 0, by norm_num, by norm_num, rectangularCircuitExponent_zero F⟩

/-- **Admissible circuit exponents are upward closed.** Let $F$ be a field and $k, w, w'$ real
numbers with $w \le w'$. If $w$ is an admissible exponent at aspect $k$ over $F$, then so is
$w'$. -/
theorem HasRectangularCircuitExponent.mono {F : Type u} [Field F] {k w w' : ℝ}
    (h : HasRectangularCircuitExponent F k w) (hww' : w ≤ w') :
    HasRectangularCircuitExponent F k w' := by
  obtain ⟨hk, hw, h⟩ := h
  refine ⟨hk, hw.trans hww', ?_⟩
  intro ε hε
  obtain ⟨C, hC, N, hN, hb⟩ := h ε hε
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn
  obtain ⟨c, hc, hs⟩ := hb n hn
  refine ⟨c, hc, hs.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.trans hn)
    (by linarith)

/-- **Exponents above the circuit exponent are admissible.** Let $F$ be a field and $k, w$ real
numbers with $w > 0$. If the rectangular matrix multiplication exponent of the arithmetic-circuit
model over $F$ at aspect $k$ is less than $w$, then $w$ is an admissible exponent at aspect $k$
over $F$. -/
theorem hasRectangularCircuitExponent_of_inf_lt (F : Type u) [Field F] {k w : ℝ}
    (hw : 0 < w) (h : rectangularCircuitExponent F k < ENNReal.ofReal w) :
    HasRectangularCircuitExponent F k w := by
  obtain ⟨_, ⟨v, rfl, hv⟩, hvw⟩ := sInf_lt_iff.mp h
  exact hv.mono ((ENNReal.ofReal_lt_ofReal_iff hw).mp hvw).le

/-- **Upper bounds on the rectangular circuit exponent.** Let $F$ be a field and let $k \ge 0$ and
$w \ge 0$ be reals. The rectangular circuit exponent of $F$ at aspect $k$ is at most $w$ if and
only if $w$ is an admissible rectangular circuit exponent for $F$ at aspect $k$: for every
$\varepsilon > 0$ there are $C > 0$ and $N \ge 1$ such that for every $n \ge N$ some arithmetic
circuit over $F$ of size at most $C n^{w + \varepsilon}$ computes the product of an
$n \times \lceil n^k \rceil$ matrix and a $\lceil n^k \rceil \times n$ matrix. -/
theorem rectangularCircuitExponent_le_iff (F : Type u) [Field F] {k w : ℝ}
    (hk : 0 ≤ k) (hw : 0 ≤ w) :
    rectangularCircuitExponent F k ≤ ENNReal.ofReal w ↔ HasRectangularCircuitExponent F k w := by
  constructor
  · intro h
    refine ⟨hk, hw, ?_⟩
    intro ε hε
    have hp : 0 < w + ε / 2 := by linarith
    have hl : rectangularCircuitExponent F k < ENNReal.ofReal (w + ε / 2) :=
      h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith))
    obtain ⟨C, hC, N, hN, hb⟩ :=
      (hasRectangularCircuitExponent_of_inf_lt F hp hl).2.2 (ε / 2) (by linarith)
    refine ⟨C, hC, N, hN, ?_⟩
    intro n hn
    have he : (w + ε / 2) + ε / 2 = w + ε := by ring
    simpa only [he] using hb n hn
  · exact rectangularCircuitExponent_le_of_admissible F

/-- **A finite rectangular circuit exponent is attained.** Let $F$ be a field and $k \ge 0$ a real
number. If the rectangular matrix multiplication exponent $\omega$ of the arithmetic-circuit model
over $F$ at aspect $k$ is finite, then $\omega$ is itself an admissible exponent at aspect $k$
over $F$. -/
theorem rectangularCircuitExponent_endpoint (F : Type u) [Field F] {k : ℝ}
    (hk : 0 ≤ k) (hfinite : rectangularCircuitExponent F k ≠ ⊤) :
    HasRectangularCircuitExponent F k (rectangularCircuitExponent F k).toReal := by
  apply (rectangularCircuitExponent_le_iff F hk ENNReal.toReal_nonneg).mp
  rw [ENNReal.ofReal_toReal hfinite]

/-- **Square matrix multiplication circuit exponent.** For a field $F$, the square matrix
multiplication circuit exponent of $F$ is the rectangular circuit exponent of $F$ at aspect $1$.
Since $\lceil n^1 \rceil = n$, it is the infimum in $[0, \infty]$ of the reals $w \ge 0$ such that
for every $\varepsilon > 0$ there are $C > 0$ and $N \ge 1$ such that for every $n \ge N$ some
arithmetic circuit over $F$ of size at most $C n^{w + \varepsilon}$ computes the product of two
$n \times n$ matrices, and it is $\infty$ when there is no such $w$. -/
noncomputable def squareMatrixMultiplicationCircuitExponent (F : Type u) [Field F] :
    ENNReal :=
  rectangularCircuitExponent F 1

/-- **The square circuit exponent is the aspect-one rectangular exponent.** For every field $F$,
the square matrix multiplication circuit exponent of $F$ equals the rectangular circuit exponent
of $F$ at aspect $1$. -/
theorem squareMatrixMultiplicationCircuitExponent_def (F : Type u) [Field F] :
    squareMatrixMultiplicationCircuitExponent F = rectangularCircuitExponent F 1 :=
  rfl

/-- **The square circuit exponent is at least two.** For every field $F$, the square matrix
multiplication circuit exponent of $F$ is at least $2$.

This trivial bound holds because a circuit computing the product of two $n \times n$ matrices has
a separate gate for each of the $n^2$ output entries. -/
theorem two_le_squareMatrixMultiplicationCircuitExponent (F : Type u) [Field F] :
    2 ≤ squareMatrixMultiplicationCircuitExponent F :=
  two_le_rectangularCircuitExponent F 1

/-- **Upper bounds on the square matrix multiplication circuit exponent.** Let $F$ be a field with
square matrix multiplication circuit exponent $\omega(F) \in [0, \infty]$, and let $w \ge 0$ be
real. Then $\omega(F) \le w$ if and only if $F$ has rectangular circuit exponent $w$ at aspect
$1$: for every $\varepsilon > 0$ there are a real $C > 0$ and a natural number $N \ge 1$ such
that for every $n \ge N$ some arithmetic circuit over $F$ with at most $C n^{w + \varepsilon}$
gates computes the product of every pair of $n \times n$ matrices over $F$. -/
theorem squareMatrixMultiplicationCircuitExponent_le_iff (F : Type u) [Field F]
    {w : ℝ} (hw : 0 ≤ w) :
    squareMatrixMultiplicationCircuitExponent F ≤ ENNReal.ofReal w ↔
      HasRectangularCircuitExponent F 1 w :=
  rectangularCircuitExponent_le_iff F (by norm_num) hw

/-- **The square matrix multiplication circuit exponent is attained.** Let $F$ be a field whose
square matrix multiplication circuit exponent $\omega(F)$ is finite. Then $F$ has rectangular
circuit exponent $\omega(F)$ at aspect $1$: for every $\varepsilon > 0$ there are a real $C > 0$
and a natural number $N \ge 1$ such that for every $n \ge N$ some arithmetic circuit over $F$ with
at most $C n^{\omega(F) + \varepsilon}$ gates computes the product of every pair of $n \times n$
matrices over $F$. -/
theorem squareMatrixMultiplicationCircuitExponent_endpoint (F : Type u) [Field F]
    (hfinite : squareMatrixMultiplicationCircuitExponent F ≠ ⊤) :
    HasRectangularCircuitExponent F 1
      (squareMatrixMultiplicationCircuitExponent F).toReal :=
  rectangularCircuitExponent_endpoint F (by norm_num) hfinite

end

end Cslib.Complexity.Algebraic
