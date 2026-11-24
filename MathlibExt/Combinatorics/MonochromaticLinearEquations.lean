/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic solutions of linear equations with at least three colours

Statements from Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using
at Least Three Colors*, INTEGERS 25 (2025), Article A88 (preprint arXiv:2501.17136, from
which the definitions are taken).

The main theorem constructs a fractional colouring below the uniform monochromatic count
for every odd-length equation satisfying the coprimality hypotheses.

An equation `a₁x₁ + ⋯ + aₖxₖ = 0` is given by its coefficient vector `a : Fin k → ℤ`.

* Over a finite abelian group `G` the paper measures colourings by the expected proportion of
  monochromatic solutions of a probabilistic colouring (its equation (2.1)), so
  `IsUncommonOverFiniteGroup G a r` asks for weights `w c x ≥ 0` with `∑_c w c x = 1` whose
  monochromatic weight `∑_c ∑_{x ∈ sol} ∏_i w c (xᵢ)` is below the uniform value
  `r^{1-k} · #sol`. Deterministic colourings would not do: on `ℤ/2` the equation
  `x₁ + x₂ + x₃ = 0` has `4` solutions and every deterministic `3`-colouring has at least one
  monochromatic solution, a proportion `≥ 1/4 > 1/9`.
* Over the integers an equation is `r`-common if every `r`-colouring of `[n]` has at least
  `(1 - o(1)) r^{1-k}` times the number of solutions in `[n]^k` monochromatic, and
  `IsUncommonOverIntegers a r` is the negation of that.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Canceling partition.** Let $a_1, \dots, a_k$ be integers, the coefficients of the
linear equation $a_1x_1 + \cdots + a_kx_k = 0$. The equation has a canceling partition when
its indices split into pairs of distinct indices $i, j$ with $a_i + a_j = 0$; precisely,
when there is a permutation $\sigma$ of the indices $1, \dots, k$ such that for every $i$
we have $\sigma(\sigma(i)) = i$, $\sigma(i) \ne i$ and $a_i + a_{\sigma(i)} = 0$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (definition of canceling
partition). -/
public def HasCancelingPartition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), (∀ i, σ (σ i) = i) ∧ (∀ i, σ i ≠ i) ∧ ∀ i, a i + a (σ i) = 0

/-- **A canceling partition for $x_1 + 2x_2 - x_3 - 2x_4 = 0$.** The equation
$x_1 + 2x_2 - x_3 - 2x_4 = 0$, with coefficient vector $(1, 2, -1, -2)$, has a canceling
partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem hasCancelingPartition_one_two_neg_one_neg_two :
    HasCancelingPartition (![1, 2, -1, -2] : Fin 4 → ℤ) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide, by decide, by decide⟩

/-- **The equation $x_1 + x_2 = 0$ has no canceling partition.** The equation
$x_1 + x_2 = 0$, with coefficient vector $(1, 1)$, has no canceling partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_hasCancelingPartition_one_one :
    ¬ HasCancelingPartition (![1, 1] : Fin 2 → ℤ) := by
  rintro ⟨σ, -, -, hsum⟩
  have h1 : ∀ j : Fin 2, (![1, 1] : Fin 2 → ℤ) j = 1 := by decide
  have h := hsum 0
  rw [h1, h1] at h
  omega

/-- **Uncommon equations over a finite abelian group.** Let $G$ be a finite abelian group,
let $a_1, \dots, a_k$ be integers, let $r$ be a natural number, and let $S \subseteq G^k$ be
the set of solutions of $a_1x_1 + \cdots + a_kx_k = 0$. The equation is $r$-uncommon over
$G$ when there are functions $w_1, \dots, w_r \colon G \to \mathbb{R}$ with $w_c(x) \ge 0$ for
all $c$ and $x$, and $w_1(x) + \cdots + w_r(x) = 1$ for every $x \in G$, such that

$$r^{k-1} \sum_{c=1}^{r} \sum_{(x_1, \dots, x_k) \in S} \prod_{i=1}^{k} w_c(x_i) < |S|,$$

where $r^{k-1}$ is read as $1$ when $k = 0$.

The functions $w_c$ form a fractional $r$-colouring of $G$, and the double sum is its
weighted count of monochromatic solutions. For $k \ge 1$ the condition says that this count
is below $r^{1-k}|S|$, its value for the uniform weights $w_c(x) = 1/r$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2 (equation (2.1)). -/
public def IsUncommonOverFiniteGroup (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ w : Fin r → G → ℝ, (∀ c x, 0 ≤ w c x) ∧ (∀ x, ∑ c, w c x = 1) ∧
    (r : ℝ) ^ (k - 1) *
        ∑ c, ∑ x ∈ univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0), ∏ i, w c (x i) <
      ((univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0)).card : ℝ)

/-- **No equation is 1-uncommon over a finite abelian group.** For every finite abelian group
$G$, every $k \ge 0$ and all integers $a_1, \dots, a_k$, the equation
$a_1 x_1 + \dots + a_k x_k = 0$ is not $1$-uncommon over $G$.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2. -/
public theorem not_isUncommonOverFiniteGroup_one (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) : ¬ IsUncommonOverFiniteGroup G a 1 := by
  rintro ⟨w, -, hw, hlt⟩
  have h1 : ∀ x, w 0 x = 1 := fun x => by simpa using hw x
  simp [h1] at hlt

/-- **Uncommon equations over the integers.** Let $a_1, \dots, a_k$ be integers and let $r$
be a natural number. For each $n$, write $[n]$ for the set of integers $1, \dots, n$ and
$S_n$ for the set of solutions $(x_1, \dots, x_k) \in [n]^k$ of
$a_1x_1 + \cdots + a_kx_k = 0$; for a colouring $\chi$ of the integers with $r$ colours, let
$M_\chi(n)$ be the number of solutions in $S_n$ whose entries all have the same colour.
The equation is $r$-uncommon over the integers when there is $\varepsilon > 0$ such that
for infinitely many $n$ some such colouring $\chi$ satisfies
$r^{k-1} M_\chi(n) < (1 - \varepsilon)|S_n|$, where $r^{k-1}$ is read as $1$ when $k = 0$.

For $k \ge 1$ this says that the equation is not $r$-common: it is not the case that every
$r$-colouring of $[n]$ has at least $(1 - o(1)) r^{1-k}|S_n|$ monochromatic solutions.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (`r`-common over the integers). -/
public def IsUncommonOverIntegers {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop, ∃ χ : ℤ → Fin r,
    (r : ℝ) ^ (k - 1) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0 ∧ ∀ i j, χ (x i) = χ (x j))).card : ℝ) <
      (1 - ε) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0)).card : ℝ)

/-- **No equation is 1-uncommon over the integers.** For every $k \ge 0$ and all integers
$a_1, \dots, a_k$, the equation $a_1 x_1 + \dots + a_k x_k = 0$ is not $1$-uncommon over the
integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_isUncommonOverIntegers_one {k : ℕ} (a : Fin k → ℤ) :
    ¬ IsUncommonOverIntegers a 1 := by
  rintro ⟨ε, hε, h⟩
  obtain ⟨n, χ, hlt⟩ := h.exists
  simp only [Nat.cast_one, one_pow, one_mul] at hlt
  rw [Finset.filter_congr
    (fun x _ => and_iff_left (fun i j => Subsingleton.elim (χ (x i)) (χ (x j))))] at hlt
  have h0 : (0 : ℝ) ≤ _ := Nat.cast_nonneg
    (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
      (fun x => ∑ i, a i * x i = 0)).card)
  nlinarith

namespace isUncommonOverFiniteGroup_of_odd

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A constant function plus a point mass at zero, parametrized by total mass and spike. -/
private noncomputable def kernel (p t : ℝ) (x : G) : ℝ :=
  (p - t) / Fintype.card G + if x = 0 then t else 0

private lemma sum_kernel (p t : ℝ) : ∑ x : G, kernel p t x = p := by
  have hq : (Fintype.card G : ℝ) ≠ 0 := by positivity
  simp [kernel, sum_add_distrib]
  field_simp
  ring

omit [DecidableEq G] in
private lemma smul_bijective (a : ℤ) (h : a.natAbs.Coprime (Fintype.card G)) :
    Function.Bijective (fun x : G => a • x) := by
  have hb : Function.Bijective (fun x : G => a.natAbs • x) :=
    (Nat.card_eq_fintype_card (α := G) ▸ h.symm).nsmul_right_bijective
  cases a with
  | ofNat n => simpa using hb
  | negSucc n =>
    change Function.Bijective (fun x : G => (n + 1) • x) at hb
    change Function.Bijective (fun x : G => (-((n + 1 : ℕ) : ℤ)) • x)
    simp only [neg_zsmul, natCast_zsmul]
    exact (Equiv.neg G).bijective.comp hb

-- Convolution multiplies both parameters. Coprimality lets us permute the second kernel.
private lemma convolution (a : ℤ) (h : a.natAbs.Coprime (Fintype.card G))
    (p t b d : ℝ) (y : G) :
    ∑ x : G, kernel p t x * kernel b d (y - a • x) = kernel (p * b) (t * d) y := by
  have hb : Function.Bijective (fun x : G => y - a • x) :=
    (Equiv.subLeft y).bijective.comp (smul_bijective a h)
  have hsum := (hb.sum_comp (kernel b d)).trans (sum_kernel b d)
  calc
    _ = (p - t) / Fintype.card G * (∑ x : G, kernel b d (y - a • x)) +
          t * kernel b d y := by
      conv_lhs =>
        enter [2, x, 1]
        unfold kernel
      simp only [add_mul, sum_add_distrib, ← mul_sum, ite_mul, zero_mul]
      simp
    _ = _ := by
      rw [hsum]
      by_cases hy : y = 0 <;> simp [kernel, hy] <;> ring

-- Induct on the coordinates, retaining an arbitrary right-hand side for the tail equation.
private lemma solution_sum {n : ℕ} (a : Fin n → ℤ)
    (h : ∀ i, (a i).natAbs.Coprime (Fintype.card G)) (p t : ℝ) (y : G) :
    (∑ x : Fin n → G, if ∑ i, a i • x i = y then ∏ i, kernel p t (x i) else 0) =
      kernel (p ^ n) (t ^ n) y := by
  induction n generalizing y with
  | zero => simp [kernel, eq_comm]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => G)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    simp_rw [add_comm (a 0 • _), ← eq_sub_iff_add_eq, ← mul_ite_zero, ← mul_sum,
      ih (fun i => a i.succ) (fun i => h i.succ)]
    simpa only [pow_succ'] using convolution (a 0) (h 0) p t (p ^ n) (t ^ n) y

private lemma weighted_count {n : ℕ} (a : Fin n → ℤ)
    (h : ∀ i, (a i).natAbs.Coprime (Fintype.card G)) (p t : ℝ) :
    (∑ x ∈ univ.filter (fun x : Fin n → G => ∑ i, a i • x i = 0), ∏ i, kernel p t (x i)) =
      p ^ n / Fintype.card G + (1 - 1 / Fintype.card G) * t ^ n := by
  rw [sum_filter, solution_sum a h]
  simp [kernel]
  ring

private lemma kernel_nonneg {t : ℝ} (ht : -1 ≤ t) (ht' : t ≤ 1) (x : G) :
    0 ≤ kernel (Fintype.card G) t x := by
  have hq : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hq' : (0 : ℝ) < Fintype.card G := by linarith
  by_cases hx : x = 0
  · simp only [kernel, hx, ite_true]
    rw [div_add' _ _ _ hq'.ne', le_div_iff₀ hq']
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ t + 1 by linarith)]
  · simp [kernel, hx, div_nonneg (sub_nonneg.mpr (ht'.trans hq)) hq'.le]

-- A zero-sum perturbation normalizes the colours at each point. Its power sum gives
-- the entire deviation from the uniform monochromatic count.
private lemma uncommon_of_power_sum [Nontrivial G] {n r : ℕ} (hr : 0 < r)
    (a : Fin (n + 1) → ℤ) (h : ∀ i, (a i).natAbs.Coprime (Fintype.card G))
    (t : Fin r → ℝ) (ht : ∀ c, -1 ≤ t c ∧ t c ≤ 1) (hs : ∑ c, t c = 0)
    (hp : ∑ c, t c ^ (n + 1) < 0) : IsUncommonOverFiniteGroup G a r := by
  let q : ℝ := Fintype.card G
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast Fintype.one_lt_card (α := G)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine ⟨fun c x => kernel q (t c) x / r,
    fun c x => div_nonneg (kernel_nonneg (ht c).1 (ht c).2 x) hr'.le, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0 <;>
      simp [kernel, hx, ← sum_div, sum_add_distrib, sum_sub_distrib, hs, q, hr'.ne',
        Fintype.card_ne_zero]
  · let sol := univ.filter (fun x : Fin (n + 1) → G => ∑ i, a i • x i = 0)
    have count (u : ℝ) : (∑ x ∈ sol, ∏ i, kernel q u (x i)) =
        q ^ (n + 1) / q + (1 - 1 / q) * u ^ (n + 1) :=
      weighted_count a h q u
    have hcard : (sol.card : ℝ) = q ^ (n + 1) / q := by
      simpa [kernel, q, Fintype.card_ne_zero] using count 0
    have hdev : (1 - 1 / q) * ∑ c, t c ^ (n + 1) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr (by rwa [div_lt_one (by linarith : 0 < q)])) hp
    change (r : ℝ) ^ (n + 1 - 1) * (∑ c, ∑ x ∈ sol, ∏ i, (kernel q (t c) (x i) / r)) <
      sol.card
    simp_rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin, ← sum_div, count]
    rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.add_sub_cancel, hcard, pow_succ (r : ℝ)]
    calc
      _ = ((r : ℝ) * (q ^ (n + 1) / q) + (1 - 1 / q) * ∑ c, t c ^ (n + 1)) / r := by
        field_simp [hr'.ne']
      _ < _ := (div_lt_iff₀ hr').mpr (by linarith)

end isUncommonOverFiniteGroup_of_odd

open isUncommonOverFiniteGroup_of_odd in
/-- **Uncommonness of odd-length equations over finite abelian groups.** Let $G$ be a
nontrivial finite abelian group, let $m \ge 1$, and let $a_1, \dots, a_{2m+1}$ be integers
each coprime to the order $|G|$. Then for every $r \ge 3$ the equation
$a_1x_1 + \cdots + a_{2m+1}x_{2m+1} = 0$ is $r$-uncommon over $G$.

Since $|G| \ge 2$, coprimality forces every $a_i$ to be nonzero.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 1 (`integers-2025-A88-thm-1`). -/
public theorem isUncommonOverFiniteGroup_of_odd (G : Type*) [AddCommGroup G]
    [Fintype G] [DecidableEq G] [Nontrivial G] (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ)
    (hcop : ∀ i, Nat.Coprime (a i).natAbs (Fintype.card G)) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverFiniteGroup G a r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  let t : Fin (s + 3) → ℝ := Fin.cons (-1) (Fin.cons (1 / 2) (Fin.cons (1 / 2) (fun _ => 0)))
  apply uncommon_of_power_sum (by omega) a hcop t
  · norm_num [t, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  · norm_num [t, Fin.sum_univ_succ]
  · have hpow := pow_lt_pow_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) (show 1 < 2 * m + 1 by omega)
    have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    simp [t, Fin.sum_univ_succ, hodd.neg_pow] at hpow ⊢
    linarith

end

end MetaMathlibExt
