/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Sqrt
public import MathlibExt.NumberTheory.GeneralizedFrobeniusNumber
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.LinearCombination

/-! # Generalized Frobenius numbers of triangular numbers

The representations by the reduced triangular triple are partitioned by the coefficient of the
first triangular number. The remaining coefficients represent the residual integer by the reduced
pair of generators. For a coprime pair `a < b` with generalized Frobenius number `g`, if
`m > g + k * a` then `m - j * a` has at least as many representations as `g + (k - j) * a`.
At the shifted pair cutoff for a triangular triple, each slice counts the pair cutoffs it exceeds.
These inequalities describe a triangle of lattice points with a partially included boundary.

## References

* Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
  Numbers*, INTEGERS 26 (2026), Article A63, pp. 1–22, Definition 1, Lemmas 2–4, and Lemma 5.
* Kittipong Subwattanachai, *Generalized Frobenius Number of Three Variables*, Kyushu J. Math.
  80 (2026), pp. 49–63, equation (2) and Lemmas 6–7 (the two-generator cutoff results).
* Matthias Beck and Sinai Robins, *A formula related to the Frobenius problem in two
  dimensions*, in *Number Theory: New York Seminar 2003*, Springer, 2004, pp. 17–23,
  Corollary 3.4 (the two-generator formula cited by Subwattanachai).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Three consecutive triangular numbers.** For a natural number $n$, the triangular triple of
$n$ is $(t_n, t_{n+1}, t_{n+2})$, where $t_m = m(m+1)/2$ is the $m$-th triangular number.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
def triangularTriple (n : ℕ) : Fin 3 → ℕ :=
  ![n * (n + 1) / 2, (n + 1) * (n + 2) / 2, (n + 2) * (n + 3) / 2]

/-- **Triangular triple at $n = 1$.** The three consecutive triangular numbers
$(t_1, t_2, t_3)$, where $t_m = m(m+1)/2$, are $(1, 3, 6)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction. -/
theorem triangularTriple_one : triangularTriple 1 = ![1, 3, 6] := by
  decide

/-- **Triangular Frobenius threshold.** For natural numbers $n$ and $s$, the threshold $N_s$ is
the integer $N_s^{\mathrm{even}} = 6\lfloor\sqrt{s+1}\rfloor - 6$ when $n$ is even and
$N_s^{\mathrm{odd}} = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ when $n$ is odd.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
def triangularFrobeniusBound (n s : ℕ) : ℤ :=
  if Even n then 6 * (Nat.sqrt (s + 1) : ℤ) - 6 else 6 * ((Nat.sqrt (4 * s + 5) - 1) / 2 : ℕ) - 3

/-- **Triangular Frobenius threshold at $s = 0$.** At $s = 0$ the triangular Frobenius threshold
$N_s$ equals $0$ for $n = 0$ (the even case, $N_0^{\mathrm{even}} = 6\lfloor\sqrt{1}\rfloor - 6$)
and $-3$ for $n = 1$ (the odd case, $N_0^{\mathrm{odd}} = 6\lfloor(\sqrt{5} - 1)/2\rfloor - 3$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, equation (4). -/
theorem triangularFrobeniusBound_zero :
    triangularFrobeniusBound 0 0 = 0 ∧ triangularFrobeniusBound 1 0 = -3 := by
  decide +kernel

/-- **The parameter $x_s$ of the triangular Frobenius formula.** For natural numbers $n$, $k$
and $i$, let $x$ be $i$ if $i \le k$ and $i - k - 1$ if $i > k$ when $n$ is even, and $2i$ if
$i \le k$ and $2(i - k) - 1$ if $i > k$ when $n$ is odd. For $s = k(k+1) + i$ with
$0 \le i \le 2k+1$ this is the integer $x_s$ (written $x_s^{\mathrm{even}}$ or
$x_s^{\mathrm{odd}}$ by the parity of $n$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusX (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then i else i - k - 1) else (if i ≤ k then 2 * i else 2 * (i - k) - 1)

/-- **The parameter $y_s$ of the triangular Frobenius formula.** For natural numbers $n$, $k$
and $i$, let $y$ be $2(k - i)$ if $i \le k$ and $4k + 3 - 2i$ if $i > k$ when $n$ is even, and
$k - i$ if $i \le k$ and $2k + 1 - i$ if $i > k$ when $n$ is odd, where a difference that would
be negative is replaced by $0$ (this happens only for $i > 2k + 1$). For $s = k(k+1) + i$ with
$0 \le i \le 2k+1$ this is the integer $y_s$ (written $y_s^{\mathrm{even}}$ or
$y_s^{\mathrm{odd}}$ by the parity of $n$).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1. -/
def triangularFrobeniusY (n k i : ℕ) : ℕ :=
  if Even n then (if i ≤ k then 2 * (k - i) else 4 * k + 3 - 2 * i)
  else (if i ≤ k then k - i else 2 * k + 1 - i)

/-- **Triangular Frobenius parameters at $s = 5$.** Take $k = 1$ and $i = 3$, so that
$s = k(k+1) + i = 5$. Then $(x_s, y_s) = (1, 1)$ for $n = 0$ (the even case) and
$(x_s, y_s) = (3, 0)$ for $n = 1$ (the odd case).

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Definition 1 and Table 2. -/
theorem triangularFrobeniusXY_five :
    (triangularFrobeniusX 0 1 3, triangularFrobeniusY 0 1 3) = (1, 1) ∧
      (triangularFrobeniusX 1 1 3, triangularFrobeniusY 1 1 3) = (3, 0) := by
  decide

private theorem frobeniusRepCount_cons {k : ℕ} (a : ℕ) (ha : 0 < a) (b : Fin k → ℕ) (m : ℕ) :
    frobeniusRepCount (Fin.cons a b) m =
      ∑ j ∈ Finset.range (m / a + 1), frobeniusRepCount b ((m : ℤ) - j * a) := by
  let indices := Finset.range (m / a + 1)
  let tails (j : ℕ) := {y : Fin k → ℕ | ∑ i, (y i : ℤ) * b i = (m : ℤ) - j * a}
  let fiber (j : ℕ) : Set (Fin (k + 1) → ℕ) := Fin.cons j '' tails j
  have partition : {x : Fin (k + 1) → ℕ |
      ∑ i, (x i : ℤ) * (Fin.cons a b : Fin (k + 1) → ℕ) i = m} =
      ⋃ j ∈ (indices : Set ℕ), fiber j := by
    ext x
    obtain ⟨j, y, rfl⟩ := Fin.exists_cons x
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      have hle : (j : ℤ) * a ≤ m := by
        rw [← h]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
          mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      have hj : j ≤ m / a := (Nat.le_div_iff_mul_le ha).2 (by exact_mod_cast hle)
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), y, eq_sub_iff_add_eq'.2 h, rfl⟩
    · rintro ⟨l, _, z, hz, heq⟩
      obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp heq
      exact eq_sub_iff_add_eq'.1 hz
  have disjoint : (indices : Set ℕ).PairwiseDisjoint fiber := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, _, rfl⟩ ⟨y, _, heq⟩
    exact hij (Fin.cons_inj.mp heq).1.symm
  rw [frobeniusRepCount, partition, indices.finite_toSet.encard_biUnion disjoint,
    finsum_mem_coe_finset]
  exact Finset.sum_congr rfl fun j _ =>
    (Fin.cons_right_injective (α := fun _ : Fin (k + 1) => ℕ) j).encard_image (tails j)

/-- **Splitting off the first generator of the reduced triangular triple.** For a natural number
$r$ write $t_r = r(r+1)/2$, and for an integer $m$ and natural numbers $a_1, \dots, a_k$ let
$d(m; a_1, \dots, a_k)$ be the number of representations of $m$ by $(a_1, \dots, a_k)$. Let
$n \ge 1$, $d_1 = \gcd(t_{n+1}, t_{n+2})$, $a = t_{n+1}/d_1$ and $b = t_{n+2}/d_1$. Then for every
natural number $m$,

$$d(m; t_n, a, b) = \sum_{j=0}^{\lfloor m/t_n \rfloor} d(m - j t_n; a, b).$$

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 2 (`integers-2026-A63-lem-2`). -/
theorem frobeniusRepCount_triangular_reduced_eq_sum (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] m =
      ∑ j ∈ Finset.range (m / t n + 1),
        frobeniusRepCount ![t (n + 1) / d₁, t (n + 2) / d₁] ((m : ℤ) - j * t n) := by
  intro t d₁
  have ht : 0 < t n := Nat.div_pos (by
    calc
      2 ≤ n + 1 := by omega
      _ ≤ n * (n + 1) := Nat.le_mul_of_pos_left _ hn) (by decide)
  exact frobeniusRepCount_cons (t n) ht ![t (n + 1) / d₁, t (n + 2) / d₁] m

namespace frobeniusRepCount_pair_sub_ge

/-- Translate a representation by adding `u` to its first coefficient and subtracting `v`
from its second coefficient. -/
private theorem count_le_of_translate {a b u v : ℕ} {n m : ℤ}
    (hsum : n + (u : ℤ) * a = m + (v : ℤ) * b)
    (hmin : ∀ x y : ℕ, (x : ℤ) * a + (y : ℤ) * b = n → v ≤ y) :
    frobeniusRepCount ![a, b] n ≤ frobeniusRepCount ![a, b] m := by
  simp only [frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Set.encard_le_encard_of_injOn (f := fun x : Fin 2 → ℕ => ![x 0 + u, x 1 - v])
  · intro x hx
    change (x 0 : ℤ) * a + (x 1 : ℤ) * b = n at hx
    change ((x 0 + u : ℕ) : ℤ) * a + ((x 1 - v : ℕ) : ℤ) * b = m
    rw [Nat.cast_add, Nat.cast_sub (hmin _ _ hx)]
    linear_combination hx + hsum
  · intro x hx y hy hxy
    have h₀ : x 0 + u = y 0 + u := congrFun hxy 0
    have h₁ : x 1 - v = y 1 - v := congrFun hxy 1
    have hx₁ := hmin _ _ hx
    have hy₁ := hmin _ _ hy
    exact funext (Fin.forall_fin_two.mpr ⟨by omega, by omega⟩)

/-- At `g + b` the count increases, so some representation has second coefficient zero. -/
private theorem dvd_add_generator {a b s : ℕ} {g : ℤ} (hb : 0 < b)
    (hg : IsGenFrobeniusNumber ![a, b] s g) : (a : ℤ) ∣ g + b := by
  by_contra h
  have hle : frobeniusRepCount ![a, b] (g + b) ≤ frobeniusRepCount ![a, b] g := by
    apply count_le_of_translate (u := 0) (v := 1) (by simp)
    intro x y hxy
    by_contra! hy
    obtain rfl : y = 0 := by omega
    exact h ⟨x, by simpa [mul_comm] using hxy.symm⟩
  exact (hg.2 (g + b) (by omega)).not_ge (hle.trans hg.1)

/-- Choose a residue `v < a` for which `d + v * b` is a multiple of `a`. -/
private theorem exists_shift {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) (d : ℕ) :
    ∃ u v : ℕ, v < a ∧ d + v * b = u * a := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨v, hv, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime (c * d) hab.symm ha.ne'
  have hdiv : c + 1 ∣ d + v * b := by
    apply Nat.dvd_of_mod_eq_zero
    rw [mul_comm v b, Nat.add_mod, hmod, ← Nat.add_mod, add_comm, ← Nat.succ_mul, Nat.mul_mod_right]
  obtain ⟨u, hu⟩ := hdiv
  exact ⟨u, v, hv, by simpa [mul_comm (c + 1) u] using hu⟩

end frobeniusRepCount_pair_sub_ge

open frobeniusRepCount_pair_sub_ge in
/-- **Representation counts above a shifted two-generator Frobenius number.** Let $a < b$ be
coprime positive integers, let $s$ and $k$ be natural numbers, let $g$ be the generalized Frobenius
number $g(a, b; s)$, and for an integer $m$ let $d(m; a, b)$ be the number of representations of
$m$ by $(a, b)$. If $m$ is an integer with $m > g + ka$, then for every natural number $j$,
$d(m - ja; a, b) \ge d(g + (k - j)a; a, b)$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 4 (`integers-2026-A63-lem-4`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
theorem frobeniusRepCount_pair_sub_ge (a b : ℕ) (ha : 0 < a) (hab' : a < b)
    (hab : Nat.Coprime a b) (s k : ℕ) (g : ℤ) (hg : IsGenFrobeniusNumber ![a, b] s g) (m : ℤ)
    (hm : g + k * a < m) (j : ℕ) :
    frobeniusRepCount ![a, b] (g + ((k : ℤ) - j) * a) ≤ frobeniusRepCount ![a, b] (m - j * a) := by
  -- The positive gap can be added by trading fewer than `a` copies of `b` for copies of `a`.
  let d := (m - (g + k * a)).toNat
  have hd : (d : ℤ) = m - (g + k * a) := Int.toNat_of_nonneg (by omega)
  obtain ⟨u, v, hv, huv⟩ := exists_shift ha hab d
  have hshift : (d : ℤ) + (v : ℤ) * b = (u : ℤ) * a := by exact_mod_cast huv
  apply count_le_of_translate (u := u) (v := v)
  · linear_combination hd - hshift
  · intro x y hxy
    obtain ⟨q, hq⟩ := dvd_add_generator (a := a) (by omega) hg
    -- Since `a ∣ g + b`, each source representation has `a ∣ y + 1`, hence `y ≥ a - 1`.
    have hdiv : (a : ℤ) ∣ ((y : ℤ) + 1) * b := by
      refine ⟨q + k - j - x, ?_⟩
      linear_combination hxy + hq
    have hy : a ∣ (y + 1) := hab.dvd_of_dvd_mul_right (by exact_mod_cast hdiv)
    have := Nat.le_of_dvd (by omega : 0 < y + 1) hy
    omega


namespace frobeniusRepCount_pair_sub_ge

/-- Swapping the generators swaps the two coordinates of a representation. -/
private theorem pairCount_swap (a b : ℕ) (m : ℤ) :
    frobeniusRepCount ![a, b] m = frobeniusRepCount ![b, a] m := by
  simp only [frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Set.encard_congr
  let e : (Fin 2 → ℕ) ≃ (Fin 2 → ℕ) :=
    ⟨fun x => ![x 1, x 0], fun x => ![x 1, x 0],
      fun x => funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩),
      fun x => funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)⟩
  apply e.subtypeEquiv
  intro x
  change ((x 0 : ℤ) * a + (x 1 : ℤ) * b = m) ↔
    ((x 1 : ℤ) * b + (x 0 : ℤ) * a = m)
  rw [add_comm]

/-- On the residue class of `G s` modulo `a`, `G r` is a cutoff for the representation count. -/
private theorem pairCutoff_le_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (G : ℕ → ℤ) (hG : ∀ r, IsGenFrobeniusNumber ![a, b] r (G r))
    (c : ℕ) (hc : a ∣ c) (j : ℤ) (s r : ℕ) :
    frobeniusRepCount ![a, b] (G s + j * c) ≤ r ↔ G s + j * c ≤ G r := by
  refine ⟨fun le => not_lt.mp fun lt => (hG r).2 _ lt |>.not_ge le, fun le => ?_⟩
  -- Every cutoff has residue `-b` modulo `a`, so the gap is a multiple of `a`.
  have hds := dvd_add_generator hb (hG s)
  have hdr := dvd_add_generator hb (hG r)
  have hc' : (a : ℤ) ∣ (c : ℤ) := by exact_mod_cast hc
  have hd : (a : ℤ) ∣ G r - (G s + j * c) := by
    have h := dvd_sub (dvd_sub hdr hds) (dvd_mul_of_dvd_right hc' j)
    convert h using 1; omega
  obtain ⟨z, hz⟩ := hd
  have hz0 : 0 ≤ z :=
    Int.nonneg_of_mul_nonneg_right (hz ▸ sub_nonneg.mpr le) (by exact_mod_cast ha)
  have hshift : G s + j * c + (z.toNat : ℤ) * a = G r := by
    rw [Int.toNat_of_nonneg hz0]
    linear_combination -hz
  have hmono : frobeniusRepCount ![a, b] (G s + j * c) ≤ frobeniusRepCount ![a, b] (G r) := by
    apply count_le_of_translate (u := z.toNat) (v := 0)
    · simpa using hshift
    · intro _ _ _
      exact Nat.zero_le _
  exact hmono.trans (hG r).1

end frobeniusRepCount_pair_sub_ge

-- Keep the source hypotheses in the signature even though the residue argument is stronger.
set_option linter.unusedVariables false in
open frobeniusRepCount_pair_sub_ge in
/-- **Representation counts between consecutive two-generator Frobenius numbers.** Let $a$ and $b$
be coprime positive integers. For a natural number $r$ let $g(a, b; r)$ be the generalized
Frobenius number of $(a, b)$ at $r$, and for an integer $m$ let $d(m; a, b)$ be the number of
representations of $m$ by $(a, b)$. Let $i$ and $s$ be natural numbers, let $c$ be a positive
integer divisible by $a$ or by $b$, and let $j$ be an integer. Then $d(g(a, b; s) + jc; a, b) = i$
if and only if $g(a, b; s) + jc \le g(a, b; i)$ and, in case $i \ge 1$, also
$g(a, b; i - 1) < g(a, b; s) + jc$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 3 (`integers-2026-A63-lem-3`), quoted from
Subwattanachai, *Generalized Frobenius number of three variables*. -/
theorem frobeniusRepCount_pair_eq_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (G : ℕ → ℤ) (hG : ∀ r, IsGenFrobeniusNumber ![a, b] r (G r))
    (i s c : ℕ) (hc : 0 < c) (hdvd : a ∣ c ∨ b ∣ c) (j : ℤ) :
    frobeniusRepCount ![a, b] (G s + j * c) = i ↔
      (i = 0 ∨ G (i - 1) < G s + j * c) ∧ G s + j * c ≤ G i := by
  -- The residue-class argument only needs positivity of the two generators.
  clear hab hc
  have cutoff (r : ℕ) :
      frobeniusRepCount ![a, b] (G s + j * c) ≤ r ↔ G s + j * c ≤ G r := by
    rcases hdvd with hd | hd
    · exact pairCutoff_le_iff a b ha hb G hG c hd j s r
    · have hSwap (q : ℕ) : IsGenFrobeniusNumber ![b, a] q (G q) := by
        constructor
        · rw [pairCount_swap b a]; exact (hG q).1
        · intro m hm
          rw [pairCount_swap b a]
          exact (hG q).2 m hm
      rw [pairCount_swap a b]
      exact pairCutoff_le_iff b a hb ha G hSwap c hd j s r
  cases i with
  | zero => simp [← cutoff]
  | succ i =>
    simp only [Nat.succ_ne_zero, false_or, Nat.succ_sub_one, ← cutoff, ← not_le]
    constructor
    · intro heq
      rw [heq]
      exact ⟨fun h => (Nat.not_succ_le_self i) (by exact_mod_cast h), le_rfl⟩
    · intro ⟨hi, hs⟩
      exact le_antisymm hs (by
        rw [Nat.cast_succ]
        exact (ENat.add_one_le_iff (by simp)).2 (lt_of_not_ge hi))


open frobeniusRepCount_pair_sub_ge in
/-- The two-generator cutoff is `(r + 1) * a * b - a - b`. -/
private theorem pairFrobenius_formula {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (r : ℕ) :
    IsGenFrobeniusNumber ![a, b] r (((r : ℤ) + 1) * a * b - a - b) := by
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  constructor
  · simp only [frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    let S : Set (Fin 2 → ℕ) := {z | (z 0 : ℤ) * a + (z 1 : ℤ) * b = ((r : ℤ) + 1) * a * b - a - b}
    change S.encard ≤ r
    have hquot (z : Fin 2 → ℕ) (hz : z ∈ S) : a * ((z 1 + 1) / a) = z 1 + 1 := by
      change (z 0 : ℤ) * a + (z 1 : ℤ) * b = _ at hz
      have hd : (a : ℤ) ∣ ((z 1 : ℤ) + 1) * b := by
        refine ⟨((r : ℤ) + 1) * b - 1 - z 0, ?_⟩
        linear_combination hz
      exact Nat.mul_div_cancel' (hab.dvd_of_dvd_mul_right (by exact_mod_cast hd))
    calc
      S.encard ≤ (↑(Finset.Ioc 0 r) : Set ℕ).encard := by
        apply Set.encard_le_encard_of_injOn (f := fun z => (z 1 + 1) / a)
        · intro z hz
          have hq := hquot z hz
          change (z 0 : ℤ) * a + (z 1 : ℤ) * b = _ at hz
          let l := (z 1 + 1) / a
          have hl : 0 < l := by
            change a * l = z 1 + 1 at hq
            by_contra! h
            rw [Nat.eq_zero_of_le_zero h, mul_zero] at hq
            omega
          have hq' : (a : ℤ) * l = z 1 + 1 := by exact_mod_cast hq
          have hcancel : (a : ℤ) * ((l : ℤ) * b + z 0) =
              (a : ℤ) * (((r : ℤ) + 1) * b - 1) := by
            linear_combination hz + (b : ℤ) * hq'
          have he := mul_left_cancel₀ ha'.ne' hcancel
          refine Finset.mem_Ioc.mpr ⟨hl, ?_⟩
          by_contra! h
          have hr : (r : ℤ) + 1 ≤ l := by exact_mod_cast h
          linarith [mul_le_mul_of_nonneg_right hr hb'.le, Int.natCast_nonneg (z 0)]
        · intro z hz w hw he
          change (z 1 + 1) / a = (w 1 + 1) / a at he
          have hzy := hquot z hz
          have hwy := hquot w hw
          have hy : z 1 = w 1 := by rw [he] at hzy; omega
          change (z 0 : ℤ) * a + (z 1 : ℤ) * b = _ at hz
          change (w 0 : ℤ) * a + (w 1 : ℤ) * b = _ at hw
          have he' : (z 0 : ℤ) * a = (w 0 : ℤ) * a := by rw [hy] at hz; linarith
          exact funext (Fin.forall_fin_two.mpr
            ⟨by exact_mod_cast mul_right_cancel₀ ha'.ne' he', hy⟩)
      _ = r := by rw [Set.encard_coe_eq_coe_finsetCard, Nat.card_Ioc, Nat.sub_zero]
  · intro m hm
    let d := ((-m) % a).toNat
    have hd : (d : ℤ) = (-m) % a := Int.toNat_of_nonneg (Int.emod_nonneg _ ha'.ne')
    obtain ⟨u, v, hv, huv⟩ := exists_shift ha hab d
    have huv' : (d : ℤ) + (v : ℤ) * b = (u : ℤ) * a := by exact_mod_cast huv
    have hdiv : (a : ℤ) ∣ m - (v : ℤ) * b := by
      refine ⟨-((-m) / a + u), ?_⟩
      linear_combination Int.emod_add_mul_ediv (-m) a - huv' + hd
    obtain ⟨z, hz⟩ := hdiv
    have hv' : (v : ℤ) ≤ a - 1 := by
      have : (v : ℤ) < a := by exact_mod_cast hv
      omega
    have hzb : (r : ℤ) * b ≤ z := by
      by_contra! hz'
      have hle : z ≤ (r : ℤ) * b - 1 := by omega
      linarith [mul_le_mul_of_nonneg_left hle ha'.le, mul_le_mul_of_nonneg_right hv' hb'.le]
    simp only [frobeniusRepCount, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcard : (r : ℕ∞) < (↑(Finset.range (r + 1)) : Set ℕ).encard := by
      rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range, ENat.natCast_lt_natCast]
      exact Nat.lt_succ_self r
    apply hcard.trans_le
    apply Set.encard_le_encard_of_injOn (f := fun l : ℕ => ![(z - l * b).toNat, v + l * a])
    · intro l hl
      have hl' : (l : ℤ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      have hnonneg : 0 ≤ z - l * b :=
        sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hl' hb'.le).trans hzb)
      change (((z - l * b).toNat : ℕ) : ℤ) * a + ((v + l * a : ℕ) : ℤ) * b = m
      rw [Int.toNat_of_nonneg hnonneg, Nat.cast_add, Nat.cast_mul]
      linear_combination -hz
    · intro l _ l' _ he
      have he' : v + l * a = v + l' * a := congrFun he 1
      exact mul_right_cancel₀ ha.ne' (Nat.add_left_cancel he')

open frobeniusRepCount_pair_sub_ge in
/-- A slice counts one for each pair cutoff strictly below its argument. -/
private theorem pairCount_eq_sum_cutoffs {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : a ∣ c) (G : ℕ → ℤ) (hG : ∀ r, IsGenFrobeniusNumber ![a, b] r (G r))
    (x : ℕ) (d : ℤ) (L : ℕ) (hL : G x + d * c ≤ G L)
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ q, G q < G x + d * c ↔ P q) :
    frobeniusRepCount ![a, b] (G x + d * c) =
      ((∑ q ∈ Finset.range L, if P q then 1 else 0 : ℕ) : ℕ∞) := by
  let C := frobeniusRepCount ![a, b] (G x + d * c)
  have hC : C ≠ ⊤ := frobeniusRepCount_ne_top (by
    intro j
    fin_cases j <;> assumption) _
  have hc' : (C.toNat : ℕ∞) = C := ENat.natCast_toNat hC
  have hcut (q : ℕ) : P q ↔ q < C.toNat := by
    rw [← hP q, ← not_le, ← pairCutoff_le_iff a b ha hb G hG c hc d x q]
    change ¬ C ≤ q ↔ _
    calc
      ¬ C ≤ q ↔ ¬ (C.toNat : ℕ∞) ≤ q := by rw [hc']
      _ ↔ q < C.toNat := by rw [ENat.natCast_le_natCast, not_le]
  have hbound : C.toNat ≤ L := by
    have h : C ≤ L := (pairCutoff_le_iff a b ha hb G hG c hc d x L).2 hL
    rwa [← hc', ENat.natCast_le_natCast] at h
  change C = _
  refine hc'.symm.trans (congrArg (fun r : ℕ => (r : ℕ∞)) ?_)
  simp only [hcut, Finset.sum_boole, Nat.cast_id]
  rw [show (Finset.range L).filter (· < C.toNat) = Finset.range C.toNat by
    ext q; simp only [Finset.mem_filter, Finset.mem_range]; omega, Finset.card_range]

/-- Truncate or pad the range of first coefficients after identifying the support of the slices. -/
private theorem triangular_count_eq_sum_cutoffs (n x y L : ℕ) (hn : 1 ≤ n)
    (G : ℕ → ℤ) (P : ℕ → ℕ → Prop) [DecidableRel P]
    (h : let t : ℕ → ℕ := fun j => j * (j + 1) / 2
         let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
         let a := t (n + 1) / d₁
         let b := t (n + 2) / d₁
         0 < a ∧ 0 < b ∧ a ∣ t n ∧ (∀ r, IsGenFrobeniusNumber ![a, b] r (G r)))
    (hP : ∀ j q : ℕ, G q < G x + ((y : ℤ) - j) * (n * (n + 1) / 2 : ℕ) ↔ P j q)
    (hsupport : ∀ j q, P j q → j < L ∧ q < L) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] (G x + y * t n) =
      ((∑ j ∈ Finset.range L, ∑ q ∈ Finset.range L, if P j q then 1 else 0 : ℕ) : ℕ∞) := by
  intro t d₁
  let a := t (n + 1) / d₁
  let b := t (n + 2) / d₁
  let c := t n
  let m : ℤ := G x + y * c
  change 0 < a ∧ 0 < b ∧ a ∣ c ∧ (∀ r, IsGenFrobeniusNumber ![a, b] r (G r)) at h
  obtain ⟨ha, hb, hc, hG⟩ := h
  have hc' : 0 < c := Nat.div_pos (by
    calc
      2 ≤ n + 1 := by omega
      _ ≤ n * (n + 1) := Nat.le_mul_of_pos_left _ hn) (by decide)
  let M := if 0 ≤ m then m.toNat / c + 1 else 0
  let f (j : ℕ) := frobeniusRepCount ![a, b] (m - j * c)
  have hslice (j : ℕ) : f j =
      ((∑ q ∈ Finset.range L, if P j q then 1 else 0 : ℕ) : ℕ∞) := by
    have he : m - j * c = G x + ((y : ℤ) - j) * c := by dsimp [m]; ring
    have hL : G x + ((y : ℤ) - j) * c ≤ G L := by
      by_contra! hl
      exact (Nat.lt_irrefl L) (hsupport j L ((hP j L).mp hl)).2
    dsimp only [f]
    rw [he]
    exact pairCount_eq_sum_cutoffs ha hb hc G hG x _ L hL (P j) (hP j)
  have hM (j : ℕ) (hj : M ≤ j) : f j = 0 := by
    apply frobeniusRepCount_eq_zero_of_neg
    by_cases hm : 0 ≤ m
    · have hnat : m.toNat < j * c := by
        exact (Nat.div_lt_iff_lt_mul hc').mp (by simpa [M, hm] using hj)
      have hcast : (m.toNat : ℤ) < (j : ℤ) * c := by exact_mod_cast hnat
      exact sub_neg.mpr (by simpa only [Int.toNat_of_nonneg hm] using hcast)
    · exact sub_neg_of_lt (lt_of_lt_of_le (lt_of_not_ge hm) (by positivity))
  have hL (j : ℕ) (hj : L ≤ j) : f j = 0 := by
    rw [hslice]
    have hz (q : ℕ) : ¬ P j q := fun h => (not_lt_of_ge hj) (hsupport j q h).1
    simp [hz]
  change frobeniusRepCount ![c, a, b] m = _
  calc
    frobeniusRepCount ![c, a, b] m = ∑ j ∈ Finset.range M, f j := by
      by_cases hm : 0 ≤ m
      · have hsum := frobeniusRepCount_triangular_reduced_eq_sum n hn m.toNat
        change frobeniusRepCount ![c, a, b] (m.toNat : ℤ) =
          ∑ j ∈ Finset.range (m.toNat / c + 1),
            frobeniusRepCount ![a, b] ((m.toNat : ℤ) - j * c) at hsum
        rw [Int.toNat_of_nonneg hm] at hsum
        simpa [M, hm, f] using hsum
      · rw [frobeniusRepCount_eq_zero_of_neg _ (lt_of_not_ge hm)]
        simp [M, hm]
    _ = ∑ j ∈ Finset.range L, f j := by
      rcases le_total M L with h | h
      · apply Finset.sum_subset (Finset.range_mono h)
        intro j _ hj
        exact hM j (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))
      · symm
        apply Finset.sum_subset (Finset.range_mono h)
        intro j _ hj
        exact hL j (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))
    _ = _ := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun j _ => hslice j

/-- Count the strict interior and the selected boundary points of the cutoff triangle. -/
private theorem sum_cutoff_triangle (k δ : ℕ) (hδ : δ ≤ 1) (P : ℕ → Prop)
    [DecidablePred P] :
    (∑ p ∈ Finset.range (2 * k + 2), ∑ w ∈ Finset.range (2 * k + 2),
      if w + 2 * p < 2 * k + δ ∨ (w + 2 * p = 2 * k + δ ∧ P p) then 1 else 0 : ℕ) =
        (k + 1) * (k + δ) + ((Finset.range (k + 1)).filter P).card := by
  have hrow (p : ℕ) (hp : p < k + 1) :
      (∑ w ∈ Finset.range (2 * k + 2),
        if w + 2 * p < 2 * k + δ ∨ (w + 2 * p = 2 * k + δ ∧ P p) then 1 else 0 : ℕ) =
      (2 * k + δ - 2 * p) + if P p then 1 else 0 := by
    have heq : (Finset.range (2 * k + 2)).filter
        (fun w => w + 2 * p < 2 * k + δ ∨ (w + 2 * p = 2 * k + δ ∧ P p)) =
        Finset.range (2 * k + δ - 2 * p + if P p then 1 else 0) := by
      ext w
      by_cases h : P p <;> simp only [Finset.mem_filter, Finset.mem_range, h, ite_true, ite_false,
        and_true, and_false, or_false] <;> omega
    simp only [Finset.sum_boole, heq, Finset.card_range, Nat.cast_id]
  have hstrict (l : ℕ) : (∑ p ∈ Finset.range (l + 1), (2 * l + δ - 2 * p)) =
      (l + 1) * (l + δ) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ']
      have hsucc (p : ℕ) : 2 * (l + 1) + δ - 2 * (p + 1) = 2 * l + δ - 2 * p := by omega
      simp only [hsucc, mul_zero, Nat.sub_zero, ih]
      ring
  calc
    _ = ∑ p ∈ Finset.range (k + 1), ∑ w ∈ Finset.range (2 * k + 2),
          if w + 2 * p < 2 * k + δ ∨ (w + 2 * p = 2 * k + δ ∧ P p) then 1 else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro p _ hp
      have hp' : k + 1 ≤ p := by simpa only [Finset.mem_range, not_lt] using hp
      apply Finset.sum_eq_zero
      intro w _
      rw [ite_eq_right (by omega)]
    _ = ∑ p ∈ Finset.range (k + 1), ((2 * k + δ - 2 * p) + if P p then 1 else 0) :=
      Finset.sum_congr rfl fun p hp => hrow p (Finset.mem_range.mp hp)
    _ = _ := by simp only [Finset.sum_add_distrib, hstrict, Finset.sum_boole, Nat.cast_id]

/-- Divide the two generators by their common factor when the remaining factors are coprime. -/
private theorem reduceCoprimePair {a b d : ℕ} (hd : 0 < d) (hab : Nat.Coprime a b) :
    let D := Nat.gcd (a * d) (b * d)
    (a * d) / D = a ∧ (b * d) / D = b := by
  dsimp only
  rw [Nat.gcd_mul_right, hab.gcd_eq_one, one_mul]
  exact ⟨Nat.mul_div_cancel _ hd, Nat.mul_div_cancel _ hd⟩

private theorem triangular_even_factors (p : ℕ) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d := Nat.gcd (t (2 * p + 1)) (t (2 * p + 2))
    t (2 * p) = (2 * p + 1) * p ∧
      t (2 * p + 1) / d = 2 * p + 1 ∧ t (2 * p + 2) / d = 2 * p + 3 ∧
      Nat.Coprime (2 * p + 1) (2 * p + 3) := by
  have ht₀ : (2 * p) * (2 * p + 1) = 2 * ((2 * p + 1) * p) := by ring
  have ht₁ : (2 * p + 1) * (2 * p + 1 + 1) = 2 * ((2 * p + 1) * (p + 1)) := by ring
  have ht₂ : (2 * p + 2) * (2 * p + 2 + 1) = 2 * ((2 * p + 3) * (p + 1)) := by ring
  let d := Nat.gcd (2 * p + 1) (2 * p + 3)
  have h₁ : d ∣ 2 * p + 1 := Nat.gcd_dvd_left ..
  have h₂ : d ∣ 2 * p + 3 := Nat.gcd_dvd_right ..
  have hd₂ : d ∣ 2 := by simpa using Nat.dvd_sub h₂ h₁
  have hpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have hdle := Nat.le_of_dvd (by decide : 0 < 2) hd₂
  have hab : Nat.Coprime (2 * p + 1) (2 * p + 3) := by
    change d = 1
    by_contra! h
    have htwo : d = 2 := by omega
    rw [htwo] at h₁
    omega
  dsimp only
  rw [show 2 * p * (2 * p + 1) / 2 = (2 * p + 1) * p by omega,
    show (2 * p + 1) * (2 * p + 1 + 1) / 2 = (2 * p + 1) * (p + 1) by omega,
    show (2 * p + 2) * (2 * p + 2 + 1) / 2 = (2 * p + 3) * (p + 1) by omega]
  exact ⟨rfl, (reduceCoprimePair (by omega) hab).1, (reduceCoprimePair (by omega) hab).2, hab⟩

private theorem triangular_odd_factors (p : ℕ) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d := Nat.gcd (t (2 * p + 1 + 1)) (t (2 * p + 1 + 2))
    t (2 * p + 1) = (p + 1) * (2 * p + 1) ∧
      t (2 * p + 1 + 1) / d = p + 1 ∧ t (2 * p + 1 + 2) / d = p + 2 ∧
      Nat.Coprime (p + 1) (p + 2) := by
  have ht₀ : (2 * p + 1) * (2 * p + 1 + 1) = 2 * ((p + 1) * (2 * p + 1)) := by ring
  have ht₁ : (2 * p + 1 + 1) * (2 * p + 1 + 1 + 1) = 2 * ((p + 1) * (2 * p + 3)) := by ring
  have ht₂ : (2 * p + 1 + 2) * (2 * p + 1 + 2 + 1) = 2 * ((p + 2) * (2 * p + 3)) := by ring
  have hab : Nat.Coprime (p + 1) (p + 2) := by
    change Nat.gcd (p + 1) (p + 2) = 1
    apply Nat.dvd_one.mp
    simpa using Nat.dvd_sub (Nat.gcd_dvd_right (p + 1) (p + 2)) (Nat.gcd_dvd_left (p + 1) (p + 2))
  dsimp only
  rw [show (2 * p + 1) * (2 * p + 1 + 1) / 2 = (p + 1) * (2 * p + 1) by omega,
    show (2 * p + 1 + 1) * (2 * p + 1 + 1 + 1) / 2 = (p + 1) * (2 * p + 3) by omega,
    show (2 * p + 1 + 2) * (2 * p + 1 + 2 + 1) / 2 = (p + 2) * (2 * p + 3) by omega]
  exact ⟨rfl, (reduceCoprimePair (by omega) hab).1, (reduceCoprimePair (by omega) hab).2, hab⟩

private theorem cutoff_even_iff (p k δ x y j q : ℕ) (hδ : δ ≤ 1)
    (hy : 2 * x + y = 2 * k + δ) (h₁ : 3 * x ≤ p)
    (h₂ : 3 * (k + δ) ≤ p + 2) :
    0 < ((x : ℤ) - q) * (2 * p + 3) + ((y : ℤ) - j) * p ↔
      j + 2 * q < 2 * k + δ ∨ (j + 2 * q = 2 * k + δ ∧ q < x) := by
  have he : ((x : ℤ) - q) * (2 * p + 3) + ((y : ℤ) - j) * p =
      ((2 * (k : ℤ) + δ) - j - 2 * q) * p + 3 * ((x : ℤ) - q) := by
    have hy' : 2 * (x : ℤ) + y = 2 * k + δ := by exact_mod_cast hy
    linear_combination (p : ℤ) * hy'
  rw [he]
  rcases lt_trichotomy (j + 2 * q) (2 * k + δ) with hl | heq | hg
  · have hq : q + 1 ≤ k + δ := by omega
    have hprod := mul_le_mul_of_nonneg_right
      (show (1 : ℤ) ≤ 2 * (k : ℤ) + δ - j - 2 * q by omega)
      (Int.natCast_nonneg p)
    exact iff_of_true (by omega) (Or.inl hl)
  · have hz : (2 * (k : ℤ) + δ) - j - 2 * q = 0 := by omega
    rw [hz, zero_mul, zero_add]
    simp only [heq, lt_self_iff_false, true_and, false_or]
    omega
  · have hprod := mul_le_mul_of_nonneg_right
      (show 2 * (k : ℤ) + δ - j - 2 * q ≤ -1 by omega)
      (Int.natCast_nonneg p)
    rw [neg_one_mul] at hprod
    omega

private theorem cutoff_odd_iff (b k δ x y j q : ℕ) (hδ : δ ≤ 1) (hb : 2 ≤ b)
    (hy : x + 2 * y = 2 * k + δ) (hyk : y ≤ k) (h₁ : 3 * k + 1 ≤ b)
    (h₂ : δ = 1 → y = 0 → 3 * k + 4 ≤ b) :
    0 < ((x : ℤ) - q) * b + ((y : ℤ) - j) * (2 * (b : ℤ) - 3) ↔
      q + 2 * j < 2 * k + δ ∨ (q + 2 * j = 2 * k + δ ∧ y < j) := by
  have he : ((x : ℤ) - q) * b + ((y : ℤ) - j) * (2 * (b : ℤ) - 3) =
      ((2 * (k : ℤ) + δ) - q - 2 * j) * b + 3 * ((j : ℤ) - y) := by
    have hy' : (x : ℤ) + 2 * y = 2 * k + δ := by exact_mod_cast hy
    linear_combination (b : ℤ) * hy'
  rw [he]
  rcases lt_trichotomy (q + 2 * j) (2 * k + δ) with hl | heq | hg
  · have hprod := mul_le_mul_of_nonneg_right
      (show (1 : ℤ) ≤ 2 * (k : ℤ) + δ - q - 2 * j by omega) (Int.natCast_nonneg b)
    exact iff_of_true (by omega) (Or.inl hl)
  · have hz : (2 * (k : ℤ) + δ) - q - 2 * j = 0 := by omega
    rw [hz, zero_mul, zero_add]
    simp only [heq, lt_self_iff_false, true_and, false_or]
    omega
  · have hn : ¬ (0 < (2 * (k : ℤ) + δ - q - 2 * j) * b + 3 * ((j : ℤ) - y)) := by
      by_cases hj : j ≤ k
      · have hprod := mul_le_mul_of_nonneg_right
          (show 2 * (k : ℤ) + δ - q - 2 * j ≤ -1 by omega) (Int.natCast_nonneg b)
        rw [neg_one_mul] at hprod
        omega
      · have hmono := mul_le_mul_of_nonneg_right (show (k : ℤ) + 1 ≤ j by omega)
          (show 0 ≤ 2 * (b : ℤ) - 3 by omega)
        have hq : 0 ≤ (q : ℤ) * b := by positivity
        have hlast : ((δ : ℤ) - 2) * b + 3 * ((k : ℤ) + 1 - y) ≤ 0 := by
          rcases (show δ = 0 ∨ δ = 1 by omega) with hd | hd
          · simp [hd]; omega
          · by_cases hy₀ : y = 0
            · have := h₂ hd hy₀
              simp [hd, hy₀]; omega
            · simp [hd]; omega
        linarith
    exact iff_of_false hn (by omega)

/-- **Representation count of the reduced triangular triple at a shifted Frobenius number.** For a
natural number $r$ write $t_r = r(r+1)/2$. Let $n$, $k$, $i$ be natural numbers with $i \le 2k + 1$
and put $s = k(k+1) + i$. Let $N_s = 6\lfloor\sqrt{s+1}\rfloor - 6$ if $n$ is even and
$N_s = 6\lfloor(\sqrt{4s+5} - 1)/2\rfloor - 3$ if $n$ is odd, and suppose $n > N_s$. For even $n$
let $(x_s, y_s) = (i, 2(k - i))$ if $i \le k$ and $(x_s, y_s) = (i - k - 1, 4k - 2i + 3)$ if
$i > k$; for odd $n$ let $(x_s, y_s) = (2i, k - i)$ if $i \le k$ and
$(x_s, y_s) = (2(i - k) - 1, 2k - i + 1)$ if $i > k$. Put $d_1 = \gcd(t_{n+1}, t_{n+2})$,
$a = t_{n+1}/d_1$ and $b = t_{n+2}/d_1$. If $g$ is the generalized Frobenius number
$g(a, b; x_s)$, then the number of representations of $g + y_s t_n$ by $(t_n, a, b)$ is $s$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Lemma 5 (`integers-2026-A63-lem-5`). -/
theorem frobeniusRepCount_triangular_reduced_at_pair_frobenius (n k i : ℕ)
    (hi : i ≤ 2 * k + 1) (hn : triangularFrobeniusBound n (k * (k + 1) + i) < n) :
    let t : ℕ → ℕ := fun j => j * (j + 1) / 2
    let d₁ := Nat.gcd (t (n + 1)) (t (n + 2))
    ∀ g₂ : ℤ, IsGenFrobeniusNumber ![t (n + 1) / d₁, t (n + 2) / d₁]
        (triangularFrobeniusX n k i) g₂ →
      frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁]
          (g₂ + triangularFrobeniusY n k i * t n) = k * (k + 1) + i := by
  intro t d₁ g hg
  have hn₀ : 1 ≤ n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    subst n
    have hroot : 1 ≤ (k * (k + 1) + i + 1).sqrt := Nat.le_sqrt.mpr (by omega)
    have h0 : Even (0 : ℕ) := ⟨0, rfl⟩
    simp only [triangularFrobeniusBound, ite_eq_left h0, Nat.cast_zero] at hn
    omega
  let x := triangularFrobeniusX n k i
  let y := triangularFrobeniusY n k i
  let δ : ℕ := if i ≤ k then 0 else 1
  have hδ : δ ≤ 1 := by dsimp [δ]; split <;> omega
  by_cases he : Even n
  · have hEven := he
    obtain ⟨p, hp⟩ := hEven
    have hn' : n = 2 * p := by omega
    have hroot : k ≤ (k * (k + 1) + i + 1).sqrt := Nat.le_sqrt.mpr (by nlinarith)
    have hroot' (hki : k ≤ i) : k + 1 ≤ (k * (k + 1) + i + 1).sqrt :=
      Nat.le_sqrt.mpr (by nlinarith)
    have hsize : 3 * k ≤ p + 2 := by
      simp only [triangularFrobeniusBound, ite_eq_left he] at hn
      omega
    have hsize' (hki : k ≤ i) : 3 * k + 1 ≤ p := by
      have := hroot' hki
      simp only [triangularFrobeniusBound, ite_eq_left he] at hn
      omega
    have hparams : 2 * x + y = 2 * k + δ ∧ 3 * x ≤ p ∧ 3 * (k + δ) ≤ p + 2 ∧
        x ≤ k ∧ (k + 1) * (k + δ) + x = k * (k + 1) + i := by
      by_cases h : i ≤ k
      · have hx : x = i := by simp [x, triangularFrobeniusX, he, h]
        have hy : y = 2 * (k - i) := by simp [y, triangularFrobeniusY, he, h]
        have hd : δ = 0 := by simp [δ, h]
        rw [hx, hy, hd]
        have hpx : 3 * i ≤ p := by
          by_cases hh : k ≤ i
          · have := hsize' hh
            omega
          · omega
        simp only [Nat.add_zero]
        refine ⟨by omega, hpx, hsize, h, ?_⟩
        rw [mul_comm (k + 1)]
      · have hx : x = i - k - 1 := by simp [x, triangularFrobeniusX, he, h]
        have hy : y = 4 * k + 3 - 2 * i := by simp [y, triangularFrobeniusY, he, h]
        have hd : δ = 1 := by simp [δ, h]
        have hp' := hsize' (by omega)
        refine ⟨by omega, by omega, by omega, by omega, ?_⟩
        rw [hx, hd]
        have hmul : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := by ring
        omega
    obtain ⟨hxy, hx, hky, hxk, hsum⟩ := hparams
    obtain ⟨hc, ha, hb, hab⟩ := triangular_even_factors p
    let a := 2 * p + 1
    let b := 2 * p + 3
    let G (r : ℕ) : ℤ := ((r : ℤ) + 1) * a * b - a - b
    have hG (r : ℕ) : IsGenFrobeniusNumber ![a, b] r (G r) :=
      pairFrobenius_formula (by omega) (by omega) hab r
    have hdata : t n = a * p ∧ t (n + 1) / d₁ = a ∧ t (n + 2) / d₁ = b := by
      dsimp only [t, d₁, a, b]
      rw [hn']
      exact ⟨hc, ha, hb⟩
    obtain ⟨hc, ha, hb⟩ := hdata
    have hg' : g = G x := hg.unique (by simpa only [ha, hb] using hG x)
    let P (j q : ℕ) := j + 2 * q < 2 * k + δ ∨ (j + 2 * q = 2 * k + δ ∧ q < x)
    have hP (j q : ℕ) : G q < G x + ((y : ℤ) - j) * (n * (n + 1) / 2 : ℕ) ↔ P j q := by
      change G q < G x + ((y : ℤ) - j) * t n ↔ _
      have hmul : G x + ((y : ℤ) - j) * t n - G q =
          (a : ℤ) * (((x : ℤ) - q) * (2 * p + 3) + ((y : ℤ) - j) * p) := by
        rw [hc, Nat.cast_mul]
        dsimp only [G, b]
        push_cast
        ring
      have ha' : (0 : ℤ) < a := by dsimp [a]; positivity
      rw [← sub_pos, hmul, mul_pos_iff_of_pos_left ha']
      exact cutoff_even_iff p k δ x y j q hδ hxy hx hky
    have hsupport (j q : ℕ) (h : P j q) : j < 2 * k + 2 ∧ q < 2 * k + 2 := by
      dsimp only [P] at h
      omega
    change frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] (g + y * t n) = _
    rw [hg', triangular_count_eq_sum_cutoffs n x y _ hn₀ G P ?_ hP hsupport]
    · norm_cast
      rw [Finset.sum_comm]
      change (∑ q ∈ Finset.range (2 * k + 2), ∑ j ∈ Finset.range (2 * k + 2),
        if j + 2 * q < 2 * k + δ ∨ (j + 2 * q = 2 * k + δ ∧ q < x) then 1 else 0) = _
      rw [sum_cutoff_triangle k δ hδ (· < x), show (Finset.range (k + 1)).filter (· < x) =
        Finset.range x by ext q; simp only [Finset.mem_filter, Finset.mem_range]; omega,
        Finset.card_range, hsum]
    · change 0 < t (n + 1) / d₁ ∧ 0 < t (n + 2) / d₁ ∧
        (t (n + 1) / d₁ ∣ t n) ∧ _
      rw [ha, hb, hc]
      exact ⟨by dsimp [a]; omega, by dsimp [b]; omega, ⟨p, rfl⟩, hG⟩
  · obtain ⟨p, hp⟩ := Nat.not_even_iff_odd.mp he
    have hn' : n = 2 * p + 1 := by omega
    let S := k * (k + 1) + i
    have hroot : 2 * k + 1 ≤ (4 * S + 5).sqrt := Nat.le_sqrt.mpr (by dsimp [S]; nlinarith)
    have hroot' (hv : i = 2 * k + 1) : 2 * k + 3 ≤ (4 * S + 5).sqrt :=
      Nat.le_sqrt.mpr (by dsimp [S]; rw [hv]; nlinarith)
    change triangularFrobeniusBound n S < n at hn
    have hsize : 3 * k + 1 ≤ p + 2 := by
      simp only [triangularFrobeniusBound, ite_eq_right he] at hn
      omega
    have hsize' (hv : i = 2 * k + 1) : 3 * k + 4 ≤ p + 2 := by
      have := hroot' hv
      simp only [triangularFrobeniusBound, ite_eq_right he] at hn
      omega
    have hparams : x + 2 * y = 2 * k + δ ∧ y ≤ k ∧ (δ = 1 → y = 0 → i = 2 * k + 1) ∧
        (k + 1) * (k + δ) + (k - y) = k * (k + 1) + i := by
      by_cases h : i ≤ k
      · have hx : x = 2 * i := by simp [x, triangularFrobeniusX, he, h]
        have hy : y = k - i := by simp [y, triangularFrobeniusY, he, h]
        have hd : δ = 0 := by simp [δ, h]
        rw [hx, hy, hd]
        simp only [Nat.add_zero]
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [mul_comm (k + 1) k]
        omega
      · have hx : x = 2 * (i - k) - 1 := by simp [x, triangularFrobeniusX, he, h]
        have hy : y = 2 * k + 1 - i := by simp [y, triangularFrobeniusY, he, h]
        have hd : δ = 1 := by simp [δ, h]
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [hy, hd]
        have hmul : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := by ring
        omega
    obtain ⟨hxy, hy, hend, hsum⟩ := hparams
    obtain ⟨hc, ha, hb, hab⟩ := triangular_odd_factors p
    let a := p + 1
    let b := p + 2
    let G (r : ℕ) : ℤ := ((r : ℤ) + 1) * a * b - a - b
    have hG (r : ℕ) : IsGenFrobeniusNumber ![a, b] r (G r) :=
      pairFrobenius_formula (by omega) (by omega) hab r
    have hdata : t n = a * (2 * p + 1) ∧ t (n + 1) / d₁ = a ∧ t (n + 2) / d₁ = b := by
      dsimp only [t, d₁, a, b]
      rw [hn']
      exact ⟨hc, ha, hb⟩
    obtain ⟨hc, ha, hb⟩ := hdata
    have hg' : g = G x := hg.unique (by simpa only [ha, hb] using hG x)
    let P (j q : ℕ) := q + 2 * j < 2 * k + δ ∨ (q + 2 * j = 2 * k + δ ∧ y < j)
    have hP (j q : ℕ) : G q < G x + ((y : ℤ) - j) * (n * (n + 1) / 2 : ℕ) ↔ P j q := by
      change G q < G x + ((y : ℤ) - j) * t n ↔ _
      have hmul : G x + ((y : ℤ) - j) * t n - G q =
          (a : ℤ) * (((x : ℤ) - q) * b + ((y : ℤ) - j) * (2 * (b : ℤ) - 3)) := by
        rw [hc, Nat.cast_mul]
        dsimp only [G, b]
        push_cast
        ring
      have ha' : (0 : ℤ) < a := by dsimp [a]; positivity
      rw [← sub_pos, hmul, mul_pos_iff_of_pos_left ha']
      exact cutoff_odd_iff b k δ x y j q hδ (by dsimp [b]; omega) hxy hy hsize
        (fun h₁ h₂ => hsize' (hend h₁ h₂))
    have hsupport (j q : ℕ) (h : P j q) : j < 2 * k + 2 ∧ q < 2 * k + 2 := by
      dsimp only [P] at h
      omega
    change frobeniusRepCount ![t n, t (n + 1) / d₁, t (n + 2) / d₁] (g + y * t n) = _
    rw [hg', triangular_count_eq_sum_cutoffs n x y _ hn₀ G P ?_ hP hsupport]
    · norm_cast
      change (∑ j ∈ Finset.range (2 * k + 2), ∑ q ∈ Finset.range (2 * k + 2),
        if q + 2 * j < 2 * k + δ ∨ (q + 2 * j = 2 * k + δ ∧ y < j) then 1 else 0) = _
      rw [sum_cutoff_triangle k δ hδ (y < ·), show (Finset.range (k + 1)).filter (y < ·) =
        Finset.Ico (y + 1) (k + 1) by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Nat.card_Ico, Nat.add_sub_add_right, hsum]
    · change 0 < t (n + 1) / d₁ ∧ 0 < t (n + 2) / d₁ ∧
        (t (n + 1) / d₁ ∣ t n) ∧ _
      rw [ha, hb, hc]
      exact ⟨by dsimp [a]; omega, by dsimp [b]; omega, ⟨2 * p + 1, rfl⟩, hG⟩

end

end MetaMathlibExt
