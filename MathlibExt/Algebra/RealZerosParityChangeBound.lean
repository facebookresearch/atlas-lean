/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Refuting the parity-change bound on real zeros (AMR-021-0014)

The conjecture bounds the number of distinct real zeros of a polynomial with
positive coefficients by the number of parity changes in its positive-`c̃`
index sequence. This module defines the bound and refutes it with an explicit
polynomial.
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Roots
import MathlibExt.Algebra.Polynomial.LinearCoeffList
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibExt.Algebra.RealZerosParityChangeBoundWanted

@[expose] public section

/-! Source record `AMR-021-0014`. -/

/-- **Newton-type coefficient differences.** For a real polynomial $f = \sum_k a_k x^k$ and a
natural number $k$, $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$, where $a_j = 0$ for $j$
above the degree of $f$; for $k = 0$ the second term vanishes, so $\tilde c_0(f) = a_0^2$. -/
def cTilde (f : Polynomial ℝ) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * (f.coeff k) ^ 2 -
    (k : ℝ) * f.coeff (k - 1) * f.coeff (k + 1)

/-- **Indices with positive Newton-type difference.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$ (with $n = 0$ for $f = 0$), set $a_{n+1} = 0$,
$\tilde c_0(f) = a_0^2$ and $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$.
This is the list of the indices $k \in \{0, \dots, n\}$ with $\tilde c_k(f) > 0$, in increasing
order. -/
noncomputable def posIndices (f : Polynomial ℝ) : List ℕ :=
  ((Finset.range (f.natDegree + 1)).filter (fun k => 0 < cTilde f k)).sort (· ≤ ·)

/-- **Parity changes of the positive-difference indices.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$ (with $n = 0$ for $f = 0$), set $a_{n+1} = 0$,
$\tilde c_0(f) = a_0^2$ and $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$.
Let $k_1 < k_2 < \dots < k_m$ be the indices $k \le n$ with $\tilde c_k(f) > 0$. Then $v(f)$ is the
number of $i < m$ such that $k_i$ and $k_{i+1}$ have different parities. -/
noncomputable def vVal (f : Polynomial ℝ) : ℕ :=
  ((posIndices f).zip ((posIndices f).drop 1)).countP
    (fun p => p.1 % 2 ≠ p.2 % 2)

/-- **Parity-change bound on real zeros (conjecture).** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$, set $a_{n+1} = 0$, $\tilde c_0(f) = a_0^2$ and
$\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$, and let $v(f)$ be the
number of parity changes between consecutive terms of the increasing list of indices $k \le n$
with $\tilde c_k(f) > 0$. The conjecture asserts that every such $f$ with $a_k > 0$ for all
$0 \le k \le n$ has at most $v(f)$ distinct real zeros.

Source: AMR-021-0014. -/
def conjecture : Prop :=
  ∀ f : Polynomial ℝ,
    (∀ k ∈ Finset.range (f.natDegree + 1), 0 < f.coeff k) →
    Set.ncard {x : ℝ | f.eval x = 0} ≤ vVal f

end

open Polynomial

-- Use the article's split-root witness, scaled by 10000^23 to have integer coefficients.
private noncomputable def splitQuadratic : Polynomial ℤ := C 363 + C (-199) * X + C 38 * X ^ 2

private noncomputable def splitFactor (j : ℕ) : Polynomial ℤ :=
  C (10000 + (j : ℤ)) + X * C 10000

private noncomputable def splitPolynomial (n : ℕ) : Polynomial ℤ :=
  (∏ j ∈ Finset.range n, splitFactor j) * splitQuadratic

private noncomputable def witness : Polynomial ℝ := (splitPolynomial 23).map (Int.castRingHom ℝ)

-- Compute the coefficient list in ascending order, using the dense linear-factor update.
private def splitCoeffs : ℕ → List ℤ
  | 0 => [363, -199, 38]
  | n + 1 => mulLinearCoeffList (10000 + (n : ℤ)) 10000 (splitCoeffs n)

private theorem splitPolynomial_succ (n : ℕ) :
    splitPolynomial (n + 1) = splitFactor n * splitPolynomial n := by
  simp only [splitPolynomial, Finset.prod_range_succ]
  ring

private theorem ofCoeffList_splitCoeffs (n : ℕ) :
    ofCoeffList (splitCoeffs n) = splitPolynomial n := by
  induction n with
  | zero =>
    simp [splitCoeffs, splitPolynomial, splitQuadratic, ofCoeffList_cons]
    ring
  | succ n ih =>
    rw [splitCoeffs, ofCoeffList_mulLinearCoeffList, ih, splitPolynomial_succ, splitFactor]

private theorem coeff_witness (k : ℕ) : witness.coeff k = ((splitCoeffs 23).getD k 0 : ℝ) := by
  rw [witness, coeff_map, ← ofCoeffList_splitCoeffs, coeff_ofCoeffList]
  rfl

private theorem splitCoeffs_pos : ∀ k : Fin 26, 0 < (splitCoeffs 23).getD k 0 := by
  decide +kernel

private theorem coeff_witness_pos {k : ℕ} (hk : k < 26) : 0 < witness.coeff k := by
  rw [coeff_witness, Int.cast_pos]
  exact splitCoeffs_pos ⟨k, hk⟩

private theorem natDegree_witness : witness.natDegree = 25 := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    have hlen : (splitCoeffs 23).length = 26 := by decide +kernel
    rw [coeff_witness, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp
  · exact le_natDegree_of_ne_zero (ne_of_gt (coeff_witness_pos (k := 25) (by decide)))

private def integerDifference (k : ℕ) : ℤ :=
  let a := (splitCoeffs 23).getD
  ((k : ℤ) + 1) * (a k 0) ^ 2 - (k : ℤ) * a (k - 1) 0 * a (k + 1) 0

private theorem cTilde_witness (k : ℕ) : cTilde witness k = (integerDifference k : ℝ) := by
  simp [cTilde, integerDifference, coeff_witness]

private theorem vVal_witness : vVal witness = 21 := by
  let kept := (List.range 26).filter (fun k => 0 < integerDifference k)
  have hfilter : (Finset.range 26).filter (fun k => 0 < cTilde witness k) = kept.toFinset := by
    ext k
    simp [kept, cTilde_witness, Int.cast_pos]
  have hn : kept.Nodup := by
    dsimp only [kept]
    decide +kernel
  have hs : kept.Pairwise (· ≤ ·) := by
    dsimp only [kept]
    decide +kernel
  have hsort : kept.toFinset.sort (· ≤ ·) = kept :=
    (List.toFinset_sort (· ≤ ·) hn).mpr hs
  unfold vVal posIndices
  rw [natDegree_witness, show 25 + 1 = 26 by rfl, hfilter, hsort]
  dsimp only [kept]
  decide +kernel

private noncomputable def splitRoot (j : Fin 23) : ℝ := -((10000 : ℝ) + (j.val : ℝ)) / 10000

private theorem splitRoot_injective : Function.Injective splitRoot := by
  intro i j hij
  apply Fin.ext
  change -((10000 : ℝ) + (i.val : ℝ)) / 10000 = -((10000 : ℝ) + (j.val : ℝ)) / 10000 at hij
  have hcast : (i.val : ℝ) = (j.val : ℝ) := by linarith
  exact Nat.cast_injective hcast

private theorem eval_splitRoot (j : Fin 23) : witness.eval (splitRoot j) = 0 := by
  rw [witness, eval_map, splitPolynomial, eval₂_mul]
  change (eval₂RingHom (Int.castRingHom ℝ) (splitRoot j))
    (∏ i ∈ Finset.range 23, splitFactor i) * _ = 0
  rw [map_prod]
  refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_range.mpr j.isLt) ?_) _
  norm_num [splitFactor, splitRoot]

private theorem realRoots_witness : 23 ≤ Set.ncard {x : ℝ | witness.eval x = 0} := by
  have hsubset : Set.range splitRoot ⊆ {x : ℝ | witness.eval x = 0} := by
    rintro _ ⟨j, rfl⟩
    exact eval_splitRoot j
  have hne : witness ≠ 0 := by
    intro h
    simpa [h] using coeff_witness_pos (k := 0) (by decide)
  have h := Set.ncard_le_ncard hsubset (finite_setOfPred_isRoot hne)
  rwa [Set.ncard_range_of_injective splitRoot_injective, Nat.card_fin] at h

/--
**The parity-change bound on real zeros is false.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$, set $a_{n+1} = 0$, $\tilde c_0(f) = a_0^2$ and
$\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$, and let $v(f)$ be the
number of parity changes between consecutive terms of the increasing list of indices $k \le n$
with $\tilde c_k(f) > 0$. There is such an $f$ with $a_k > 0$ for all $0 \le k \le n$ whose number
of distinct real zeros exceeds $v(f)$.

Katkova, Shapiro and Vishnyakova (Sec. 5) disprove Conjecture 9 via iterated primitives $Q_n$ of
an explicit $Q_{15}$. Splitting the repeated root also refutes the distinct-zero reading used
here: $\prod_{j<23}(x+1+j/10^4)\,(38x^2-199x+363)$ has positive coefficients, 23 distinct real
zeros and $v = 21$.

Source: Olga Katkova, Boris Shapiro and Anna Vishnyakova, In search of Newton-type
inequalities, arXiv:2403.12200 (2024), https://arxiv.org/abs/2403.12200. Moved from
`OpenConjectures/Algebra/RealZerosParityChangeBound`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  have hle := h witness fun k hk =>
    coeff_witness_pos (by simpa [natDegree_witness] using Finset.mem_range.mp hk)
  rw [vVal_witness] at hle
  exact (by decide : ¬ 23 ≤ 21) (realRoots_witness.trans hle)

end MathlibExt.Algebra.RealZerosParityChangeBoundWanted
