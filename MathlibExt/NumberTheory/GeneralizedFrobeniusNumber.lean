/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Interval.Finset.Nat

/-! # Generalized Frobenius numbers

The representation count `d(m; a₁, …, a_k)` of an integer `m` by a vector of natural generators,
valued in `ℕ∞` so that an infinite representation set (possible only with a zero generator) counts
as `⊤` rather than collapsing to `0`, and the predicate `IsGenFrobeniusNumber a s g` saying that
`g = max {m ∈ ℤ | d(m; a) ≤ s}` is the generalized Frobenius number `g(a; s)`.
For three positive generators and a natural target, a bounded search over two coefficients gives
an exact count. Given a positive generator, checking the integers immediately above a candidate
cutoff in a window of that generator's length suffices to certify its maximality.

## References

* Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
  Numbers*, INTEGERS 26 (2026), Article A63, pp. 1–22, Introduction (definitions of
  `d(n; a₁, …, a_k)` and `g(A; s)`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of representations by a vector of generators.** For natural numbers
$a_1, \dots, a_k$ and an integer $m$, the representation count $d(m; a_1, \dots, a_k)$ is the
number of tuples $(x_1, \dots, x_k)$ of natural numbers with $x_1 a_1 + \dots + x_k a_k = m$,
counted as an extended natural number, so that it is $\infty$ when there are infinitely many such
tuples.

It is $0$ for $m < 0$, and finite when every $a_i$ is positive.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
noncomputable def frobeniusRepCount {k : ℕ} (a : Fin k → ℕ) (m : ℤ) : ℕ∞ :=
  {x : Fin k → ℕ | ∑ i, (x i : ℤ) * a i = m}.encard

/-- **Negative integers have no representations.** For all natural numbers $a_1, \dots, a_k$ and
every integer $m < 0$, the representation count $d(m; a_1, \dots, a_k)$ is $0$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
theorem frobeniusRepCount_eq_zero_of_neg {k : ℕ} (a : Fin k → ℕ) {m : ℤ} (hm : m < 0) :
    frobeniusRepCount a m = 0 := by
  rw [frobeniusRepCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  intro x (hx : ∑ i, (x i : ℤ) * a i = m)
  have : 0 ≤ ∑ i, (x i : ℤ) * a i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
  rw [hx] at this
  omega

/-- **Finitely many representations for positive generators.** If $a_1, \dots, a_k$ are positive
natural numbers, then for every integer $m$ the representation count $d(m; a_1, \dots, a_k)$ is
finite.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `d(n; a₁, …, a_k)`). -/
theorem frobeniusRepCount_ne_top {k : ℕ} {a : Fin k → ℕ} (ha : ∀ i, 0 < a i) (m : ℤ) :
    frobeniusRepCount a m ≠ ⊤ := by
  rw [frobeniusRepCount, Set.encard_ne_top_iff]
  refine (Set.finite_Iic (fun _ : Fin k => m.toNat)).subset ?_
  intro x hx j
  have hx : ∑ i, (x i : ℤ) * a i = m := hx
  have hle : (x j : ℤ) * a j ≤ ∑ i, (x i : ℤ) * a i :=
    Finset.single_le_sum (f := fun i => (x i : ℤ) * a i)
      (fun i _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)) (Finset.mem_univ j)
  have h1 : (x j : ℤ) ≤ (x j : ℤ) * a j :=
    le_mul_of_one_le_right (Int.natCast_nonneg _) (by exact_mod_cast ha j)
  change x j ≤ m.toNat
  omega

/-- **Generalized Frobenius number.** For natural numbers $a_1, \dots, a_k$ and $s$, write
$d(m; a)$ for the number of representations of an integer $m$ by $a = (a_1, \dots, a_k)$. An
integer $g$ is the generalized Frobenius number $g(a; s) = \max \{m \in \mathbb{Z} \mid
d(m; a) \le s\}$ when $d(g; a) \le s$ and $d(m; a) > s$ for every integer $m > g$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `g(A; s)`). -/
def IsGenFrobeniusNumber {k : ℕ} (a : Fin k → ℕ) (s : ℕ) (g : ℤ) : Prop :=
  frobeniusRepCount a g ≤ s ∧ ∀ m : ℤ, g < m → (s : ℕ∞) < frobeniusRepCount a m

/-- **Uniqueness of the generalized Frobenius number.** For natural numbers $a_1, \dots, a_k$ and
$s$, if the integers $g$ and $g'$ are both the generalized Frobenius number $g(a_1, \dots, a_k; s)$,
then $g = g'$.

Source: Kittipong Subwattanachai, *Formulas for the Generalized Frobenius Number of Triangular
Numbers*, INTEGERS 26 (2026), Article A63, Introduction (definition of `g(A; s)` as a maximum). -/
theorem IsGenFrobeniusNumber.unique {k : ℕ} {a : Fin k → ℕ} {s : ℕ} {g g' : ℤ}
    (h : IsGenFrobeniusNumber a s g) (h' : IsGenFrobeniusNumber a s g') : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · exact absurd h'.1 (not_le.2 (h.2 g' hlt))
  · exact heq
  · exact absurd h.1 (not_le.2 (h'.2 g hgt))

/-- **Representation count of a triple by bounded pairs.** For natural generators $a,b,c$ with
$a,b,c > 0$ and a natural target $m$, count the pairs $(x,z)$ with $x \le m/a$, $z \le m/c$,
$a x + c z \le m$, and $b$ dividing $m - (a x + c z)$. Each such pair determines exactly one
middle coefficient. -/
theorem frobeniusRepCount_triple_eq_card (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    frobeniusRepCount ![a, b, c] m =
      (((Finset.range (m / a + 1) ×ˢ Finset.range (m / c + 1)).filter fun (x, z) =>
        x * a + z * c ≤ m ∧ (m - (x * a + z * c)) % b = 0).card : ℕ∞) := by
  let pairs := (Finset.range (m / a + 1) ×ˢ Finset.range (m / c + 1)).filter fun (x, z) =>
    x * a + z * c ≤ m ∧ (m - (x * a + z * c)) % b = 0
  let reps : Set (Fin 3 → ℕ) := {x | x 0 * a + x 1 * b + x 2 * c = m}
  have hcount : frobeniusRepCount ![a, b, c] m = reps.encard := by
    rw [frobeniusRepCount]
    congr 1
    ext x
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      reps, Set.mem_ofPred_eq]
    norm_cast
  rw [hcount, ← Set.encard_coe_eq_coe_finsetCard pairs]
  apply Set.encard_congr
  refine Set.BijOn.equiv (fun x : Fin 3 → ℕ => (x 0, x 2)) ⟨?_, ?_, ?_⟩
  · intro x (hx : x 0 * a + x 1 * b + x 2 * c = m)
    simp only [pairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff]
    refine ⟨⟨(Nat.le_div_iff_mul_le ha).2 (by omega), (Nat.le_div_iff_mul_le hc).2 (by omega)⟩,
      by omega, ?_⟩
    rw [show m - (x 0 * a + x 2 * c) = x 1 * b by omega, Nat.mul_mod_left]
  · intro x (hx : x 0 * a + x 1 * b + x 2 * c = m)
      y (hy : y 0 * a + y 1 * b + y 2 * c = m) h
    have h₀ : x 0 = y 0 := congrArg Prod.fst h
    have h₂ : x 2 = y 2 := congrArg Prod.snd h
    rw [h₀, h₂] at hx
    have h₁ : x 1 = y 1 := Nat.mul_right_cancel hb (by omega)
    exact funext (Fin.forall_fin_succ.mpr ⟨h₀, Fin.forall_fin_two.mpr ⟨h₁, h₂⟩⟩)
  · rintro ⟨x, z⟩ h
    have hp : x * a + z * c ≤ m ∧ (m - (x * a + z * c)) % b = 0 :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp h)).2
    refine ⟨![x, (m - (x * a + z * c)) / b, z], ?_, rfl⟩
    change x * a + (m - (x * a + z * c)) / b * b + z * c = m
    rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hp.2)]
    omega

/-- **Generalized Frobenius number from one generator window.** For a vector $a$ of natural
numbers, a positive generator $a_i$, a natural level $s$, and an integer $g$, the integer $g$ is
$g(a;s)$ if and only if its representation count is at most $s$ and the count exceeds $s$ at each
integer in $(g,g+a_i]$. -/
theorem isGenFrobeniusNumber_iff_window {k : ℕ} (a : Fin k → ℕ) (i : Fin k) (hi : 0 < a i)
    (s : ℕ) (g : ℤ) :
    IsGenFrobeniusNumber a s g ↔ frobeniusRepCount a g ≤ s ∧
      ∀ j : Fin (a i), (s : ℕ∞) < frobeniusRepCount a (g + (j : ℤ) + 1) := by
  constructor
  · intro h
    exact ⟨h.1, fun j => h.2 _ (by omega)⟩
  · rintro ⟨hg, hw⟩
    refine ⟨hg, fun m hm => ?_⟩
    let d : ℤ := a i
    let q : ℕ := ((m - g - 1) / d).toNat
    let r : ℤ := (m - g - 1) % d
    have hd : 0 < d := by
      change (0 : ℤ) < (a i : ℤ)
      exact_mod_cast hi
    have hr₀ : 0 ≤ r := Int.emod_nonneg _ hd.ne'
    have hr : r < d := Int.emod_lt_of_pos _ hd
    let j : Fin (a i) := ⟨r.toNat, by omega⟩
    have hj : (j : ℤ) = r := Int.toNat_of_nonneg hr₀
    have hq : (q : ℤ) = (m - g - 1) / d := Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hd.le)
    have hm' : g + (j : ℤ) + 1 + d * q = m := by
      rw [hj, hq]
      have h := Int.emod_add_mul_ediv (m - g - 1) d
      omega
    refine (hw j).trans_le ?_
    rw [frobeniusRepCount, frobeniusRepCount]
    -- Add the same number of copies of generator `i` to every representation in the window.
    apply Set.encard_le_encard_of_injOn
      (f := fun x : Fin k → ℕ => fun j => x j + if j = i then q else 0)
    · intro x (hx : ∑ j, (x j : ℤ) * a j = g + (j : ℤ) + 1)
      change ∑ l, ((x l + if l = i then q else 0 : ℕ) : ℤ) * a l = m
      simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, hx]
      rw [show (∑ l : Fin k, ((if l = i then q else 0 : ℕ) : ℤ) * a l) = d * q by
        simp [apply_ite, Finset.sum_ite_eq', d, mul_comm]]
      exact hm'
    · intro x _ y _ h
      exact funext fun l => Nat.add_right_cancel (congrFun h l)

end

end MetaMathlibExt
