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
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Tactic.LinearCombination

/-! # Generalized Frobenius numbers of triangular numbers

The representations by the reduced triangular triple are partitioned by the coefficient of the
first triangular number. The remaining coefficients represent the residual integer by the reduced
pair of generators. For a coprime pair `a < b` with generalized Frobenius number `g`, if
`m > g + k * a` then `m - j * a` has at least as many representations as `g + (k - j) * a`.
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

end

end MetaMathlibExt
