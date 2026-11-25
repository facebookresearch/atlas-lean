/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Locally nilpotent integer polynomials

The classification at `-1` follows the orbit argument of Sayak Sengupta,
[*Locally nilpotent polynomials over ℤ*](https://arxiv.org/abs/2309.10303), §4.
A return to a previous orbit value modulo a prime traps all later values in the same
finite list of residues. This constrains the first place the orbit can depart from
the translation `x ↦ x - 1`.

Reflection `u(x) ↦ -u(-x)` (Fact 3.1) negates every orbit value and transports the
classification to `1` (Theorem 4.1). The first three families at each point reach zero
within three steps. This gives the classification of the locally nilpotent polynomials
whose orbits never reach zero at `±1` (Corollary 4.3).
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Weakly locally nilpotent polynomial at a point.** Let $u \in \mathbb{Z}[x]$ and
$r \in \mathbb{Z}$, and let $A$ be a set of natural numbers. Write $u^{(m)}$ for the $m$-fold
iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then $u$ is weakly locally nilpotent at $r$
outside $A$ if for every prime $p \notin A$ there is $m \ge 1$ such that $p$ divides
$u^{(m)}(r)$. For $A = \emptyset$ this is called locally nilpotent at $r$.

Only the primes in $A$ matter, so $A$ is usually taken to be a set of primes.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsWeaklyLocallyNilpotentAt (u : ℤ[X]) (r : ℤ) (A : Set ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ A → ∃ m, 0 < m ∧ (p : ℤ) ∣ (fun x => u.eval x)^[m] r

/-- **Nilpotent polynomial at a point.** Let $u \in \mathbb{Z}[x]$ and $r \in \mathbb{Z}$, and
write $u^{(n)}$ for the $n$-fold iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then $u$ is
nilpotent at $r$ if $u^{(n)}(r) = 0$ for some $n \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2. -/
public def IsNilpotentAt (u : ℤ[X]) (r : ℤ) : Prop :=
  ∃ n, 0 < n ∧ (fun x => u.eval x)^[n] r = 0

/-- **Iterates of $x + 1$.** Let $u(x) = x + 1 \in \mathbb{Z}[x]$ and write $u^{(m)}$ for its
$m$-fold iterate as a map $\mathbb{Z} \to \mathbb{Z}$. For every integer $r$ and every natural
number $m$, $u^{(m)}(r) = r + m$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem iterate_eval_X_add_one (r : ℤ) (m : ℕ) :
    (fun x => (X + 1 : ℤ[X]).eval x)^[m] r = r + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp
    ring

/-- **$x + 1$ is locally nilpotent at $1$.** Let $u(x) = x + 1 \in \mathbb{Z}[x]$ and write
$u^{(m)}$ for the $m$-fold iterate of $u$ as a map $\mathbb{Z} \to \mathbb{Z}$. Then for every
prime $p$ there is $m \ge 1$ such that $p$ divides $u^{(m)}(1)$.

One can take $m = p - 1$, since $u^{(p-1)}(1) = p$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem isWeaklyLocallyNilpotentAt_X_add_one :
    IsWeaklyLocallyNilpotentAt (X + 1) 1 ∅ := by
  intro p hp _
  refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
  rw [iterate_eval_X_add_one]
  have : ((p - 1 : ℕ) : ℤ) = p - 1 := by have := hp.one_le; push_cast [this]; ring
  rw [this]
  simp

/-- **$x + 1$ is not nilpotent at $1$.** The polynomial $x + 1 \in \mathbb{Z}[x]$ is not nilpotent
at $1$.

Writing $u(x) = x + 1$, the iterates satisfy $u^{(n)}(1) = n + 1 \ne 0$ for every $n \ge 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Section 2, example (e). -/
public theorem not_isNilpotentAt_X_add_one : ¬ IsNilpotentAt (X + 1) 1 := by
  rintro ⟨n, _, hn⟩
  rw [iterate_eval_X_add_one] at hn
  omega

end

namespace locallyNilpotentAt_neg_one_classification

variable {u : ℤ[X]} {k : ℤ}

/-- If the orbit has visited each of `-1, …, -k` and then returns to one of them
modulo a prime, that prime divides one of `1, …, k`. -/
private theorem prime_le_of_return (hu : IsWeaklyLocallyNilpotentAt u (-1) ∅)
    (hk : 1 ≤ k) (hstep : ∀ i : ℤ, 1 ≤ i → i < k → u.eval (-i) = -i - 1)
    {j : ℤ} (hj : 1 ≤ j) (hjk : j ≤ k) {p : ℕ} (hp : p.Prime)
    (hreturn : (p : ℤ) ∣ u.eval (-k) + j) : (p : ℤ) ≤ k := by
  have hcycle (m : ℕ) : ∃ i : ℤ, 1 ≤ i ∧ i ≤ k ∧
      (fun x => u.eval x)^[m] (-1) ≡ -i [ZMOD (p : ℤ)] := by
    induction m with
    | zero => exact ⟨1, le_rfl, hk, Int.ModEq.refl _⟩
    | succ m ih =>
      obtain ⟨i, hi, hik, hmod⟩ := ih
      rw [Function.iterate_succ_apply']
      have heval : u.eval ((fun x => u.eval x)^[m] (-1)) ≡ u.eval (-i) [ZMOD (p : ℤ)] :=
        Int.modEq_of_dvd (hmod.dvd.trans (sub_dvd_eval_sub _ _ u))
      rcases hik.eq_or_lt with rfl | hlt
      · refine ⟨j, hj, hjk, heval.trans ?_⟩
        apply Int.ModEq.symm
        simpa [Int.modEq_iff_dvd] using hreturn
      · refine ⟨i + 1, by omega, by omega, ?_⟩
        simpa [hstep i hi hlt, neg_add, sub_eq_add_neg, add_comm] using heval
  obtain ⟨m, _, hm⟩ := hu p hp (by simp)
  obtain ⟨i, hi, hik, hmod⟩ := hcycle m
  have hd : (p : ℤ) ∣ i := by
    simpa using Int.modEq_zero_iff_dvd.mp (hmod.symm.trans hm.modEq_zero_int)
  exact (Int.le_of_dvd (by omega) hd).trans hik

/-- A nonunit integer has a positive prime divisor, including when the integer is zero. -/
private theorem prime_divisor {z : ℤ} (h₁ : z ≠ 1) (h₂ : z ≠ -1) :
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ z := by
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show z.natAbs ≠ 1 by omega)
  exact ⟨p, hp, Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)⟩

/-- After the orbit segment `-1, …, -k`, the next value is zero or `-(k+1)`. -/
private theorem next_value (hu : IsWeaklyLocallyNilpotentAt u (-1) ∅)
    (hk : 1 ≤ k) (hstep : ∀ i : ℤ, 1 ≤ i → i < k → u.eval (-i) = -i - 1) :
    u.eval (-k) = 0 ∨ u.eval (-k) = -k - 1 := by
  let b := u.eval (-k)
  have bound {i : ℤ} (hi : 1 ≤ i) (hik : i ≤ k) {p : ℕ} (hp : p.Prime)
      (hd : (p : ℤ) ∣ b + i) := prime_le_of_return hu hk hstep hi hik hp hd
  have noRepeat (i : ℤ) (hi : 1 ≤ i) (hik : i ≤ k) : b ≠ -i := by
    obtain ⟨p, hpk, hp⟩ := Nat.exists_infinite_primes (k.toNat + 1)
    intro he
    have := bound hi hik hp (by simp [he])
    omega
  -- Comparing the inputs -k and -(k-d) gives this divisibility for every smaller d.
  have small (d : ℤ) (hd : 0 < d) (hdk : d < k) : d ∣ b + k + 1 := by
    have h := sub_dvd_eval_sub (-(k - d)) (-k) u
    rw [hstep (k - d) (by omega) (by omega)] at h
    change -(k - d) - -k ∣ -(k - d) - 1 - b at h
    have h' : d ∣ -(b + k + 1) + d := by convert h using 1 <;> ring
    exact dvd_neg.mp ((dvd_add_left (dvd_refl d)).mp h')
  change b = 0 ∨ b = -k - 1
  by_contra! h
  have hbk : b + k ≠ 1 := by
    intro he
    by_cases hk' : k = 1
    · omega
    · exact noRepeat (k - 1) (by omega) (by omega) (by omega)
  -- A prime divisor of b + k must equal k, since every smaller prime divides b + k + 1.
  obtain ⟨p, hp, hpb⟩ := prime_divisor hbk (show b + k ≠ -1 by omega)
  have hpk : (p : ℤ) = k := by
    refine (bound hk le_rfl hp hpb).eq_of_not_lt ?_
    intro hlt
    have h₁ := (dvd_add_right hpb).mp (small p (by exact_mod_cast hp.pos) hlt)
    exact hp.not_dvd_one (by exact_mod_cast h₁)
  have hkb : k ∣ b := (dvd_add_left (dvd_refl k)).mp (hpk ▸ hpb)
  have hb₂ : b + 1 ≠ -1 := by
    intro he
    by_cases hk' : k = 1
    · omega
    · exact noRepeat 2 (by decide) (by omega) (by omega)
  -- A prime divisor of b + 1 then divides k, hence also b.
  obtain ⟨q, hq, hqb⟩ := prime_divisor (show b + 1 ≠ 1 by omega) hb₂
  have hqk : (q : ℤ) ∣ k := by
    rcases (bound (i := 1) le_rfl hk hq hqb).eq_or_lt with he | hlt
    · rw [he]
    · apply (dvd_add_right hqb).mp
      convert small q (by exact_mod_cast hq.pos) hlt using 1
      ring
  have hd := (dvd_add_right (hqk.trans hkb)).mp hqb
  exact hq.not_dvd_one (by exact_mod_cast hd)

/-- At the first departure from the translation, the orbit hits zero. Comparing
with the value at `-1` bounds the index of this departure by three. -/
private theorem orbit_cases (hu : IsWeaklyLocallyNilpotentAt u (-1) ∅) :
    u.eval (-1) = 0 ∨
    (u.eval (-1) = -2 ∧ u.eval (-2) = 0) ∨
    (u.eval (-1) = -2 ∧ u.eval (-2) = -3 ∧ u.eval (-3) = 0) ∨ u = X - 1 := by
  classical
  by_cases h : ∃ n : ℕ, u.eval (-(n : ℤ) - 1) ≠ -(n : ℤ) - 2
  · let n := Nat.find h
    have hn : u.eval (-(n : ℤ) - 1) ≠ -(n : ℤ) - 2 := Nat.find_spec h
    have hstep (i : ℤ) (hi : 1 ≤ i) (hin : i < (n : ℤ) + 1) : u.eval (-i) = -i - 1 := by
      have he := not_not.mp (Nat.find_min h (m := (i - 1).toNat) (by change _ < n; omega))
      rw [show -((i - 1).toNat : ℤ) - 1 = -i by omega] at he
      exact he.trans (by omega)
    have hz : u.eval (-(n : ℤ) - 1) = 0 := by
      have he := next_value hu (k := (n : ℤ) + 1) (by omega) hstep
      rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by omega] at he
      exact he.resolve_right (by omega)
    have hn₂ : n ≤ 2 := by
      by_contra! hlarge
      have hd := sub_dvd_eval_sub (-1) (-(n : ℤ) - 1) u
      rw [hz, hstep 1 le_rfl (by omega)] at hd
      have hd' : (n : ℤ) ∣ -2 := by convert hd using 1 <;> ring
      have := Int.le_of_dvd (by decide : (0 : ℤ) < 2) (dvd_neg.mp hd')
      omega
    interval_cases n
    · exact Or.inl (by simpa using hz)
    · exact Or.inr (Or.inl ⟨by simpa using hstep 1 le_rfl (by decide), by simpa using hz⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by simpa using hstep 1 le_rfl (by decide),
        by simpa using hstep 2 (by decide) (by decide), by simpa using hz⟩))
  · right; right; right
    apply u.eq_of_infinite_eval_eq
    apply (Set.Iio_infinite (0 : ℤ)).mono
    intro x hx
    have hx' : x < 0 := hx
    have he := not_not.mp (not_exists.mp h (-x - 1).toNat)
    change u.eval x = (X - 1 : ℤ[X]).eval x
    rw [eval_sub, eval_X, eval_one]
    rw [show -((-x - 1).toNat : ℤ) - 1 = x by omega] at he
    exact he.trans (by omega)

private theorem factor_at {v : ℤ[X]} (a : ℕ) (ha : v.eval (-(a : ℤ)) = 0) :
    ∃ q : ℤ[X], v = q * (X + (a : ℤ[X])) := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr (show v.IsRoot (-(a : ℤ)) from ha)
  exact ⟨q, by simpa [mul_comm] using hq⟩

private theorem factor_at_two_roots {v : ℤ[X]} (h₁ : v.eval (-1) = 0) (h₂ : v.eval (-2) = 0) :
    ∃ q : ℤ[X], v = q * (X + 1) * (X + 2) := by
  obtain ⟨p, hp⟩ := factor_at 1 h₁
  norm_num at hp
  rw [hp] at h₂
  obtain ⟨q, hq⟩ := factor_at (v := p) 2 (by norm_num at h₂ ⊢; omega)
  refine ⟨q, ?_⟩
  rw [hp, hq]
  push_cast
  ring

private theorem positive_degree {a b : ℤ} (h : u.eval a ≠ u.eval b) : 0 < u.natDegree := by
  by_contra! hdeg
  rw [eq_C_of_natDegree_le_zero hdeg, eval_C, eval_C] at h
  exact h rfl

private theorem local_of_hit {n : ℕ} (hn : 0 < n) (h : (fun x => u.eval x)^[n] (-1) = 0) :
    IsWeaklyLocallyNilpotentAt u (-1) ∅ :=
  fun _ _ _ => ⟨n, hn, h ▸ dvd_zero _⟩

end locallyNilpotentAt_neg_one_classification

open locallyNilpotentAt_neg_one_classification

/-- **Classification of locally nilpotent polynomials at $-1$.** A polynomial $u \in \mathbb{Z}[x]$
of positive degree is locally nilpotent at $-1$ if and only if it has one of the following forms,
for some $p \in \mathbb{Z}[x]$: $(x+1)p(x)$ with $p \ne 0$; $-2x - 4 + p(x)(x+1)(x+2)$;
$2x^2 + 7x + 3 + p(x)(x+1)(x+2)(x+3)$; or $u = x - 1$.

These are the images of the polynomials locally nilpotent at $1$ under $u(x) \mapsto -u(-x)$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.2. -/
public theorem locallyNilpotentAt_neg_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X + 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X - 4 + p * (X + 1) * (X + 2)} ∪
        {u | ∃ p : ℤ[X], u = 2 * X ^ 2 + 7 * X + 3 + p * (X + 1) * (X + 2) * (X + 3)} ∪
        {X - 1} := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hdeg, hu⟩
    rcases orbit_cases hu with h₁ | ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | he
    · obtain ⟨q, hq⟩ := factor_at 1 h₁
      norm_num at hq
      refine Or.inl (Or.inl (Or.inl ⟨q, ?_, by rw [hq, mul_comm]⟩))
      rintro rfl
      simp [hq] at hdeg
    · let v : ℤ[X] := -2 * X - 4
      obtain ⟨q, hq⟩ := factor_at_two_roots (v := u - v)
        (by norm_num [v, h₁]) (by norm_num [v, h₂])
      exact Or.inl (Or.inl (Or.inr ⟨q, by rw [← hq]; dsimp [v]; ring⟩))
    · let v : ℤ[X] := 2 * X ^ 2 + 7 * X + 3
      obtain ⟨p, hp⟩ := factor_at_two_roots (v := u - v)
        (by norm_num [v, h₁]) (by norm_num [v, h₂])
      have hroot := congrArg (eval (-3 : ℤ)) hp
      obtain ⟨q, hq⟩ := factor_at (v := p) 3 (by norm_num [v, h₃] at hroot ⊢; omega)
      refine Or.inl (Or.inr ⟨q, ?_⟩)
      rw [hq] at hp
      dsimp [v] at hp
      linear_combination hp
    · exact Or.inr he
  · rintro (((⟨q, hq, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩) | rfl)
    · refine ⟨?_, local_of_hit (n := 1) (by decide) (by simp)⟩
      change 0 < ((X + C (1 : ℤ)) * q).natDegree
      rw [natDegree_mul (X_add_C_ne_zero 1) hq, natDegree_X_add_C]
      omega
    · let u : ℤ[X] := -2 * X - 4 + q * (X + 1) * (X + 2)
      have h₁ : u.eval (-1) = -2 := by norm_num [u]
      have h₂ : u.eval (-2) = 0 := by norm_num [u]
      exact ⟨positive_degree (u := u) (a := -1) (b := -2) (by omega),
        local_of_hit (u := u) (n := 2) (by decide) (by
          change u.eval (u.eval (-1)) = 0
          rw [h₁, h₂])⟩
    · let u : ℤ[X] := 2 * X ^ 2 + 7 * X + 3 + q * (X + 1) * (X + 2) * (X + 3)
      have h₁ : u.eval (-1) = -2 := by norm_num [u]
      have h₂ : u.eval (-2) = -3 := by norm_num [u]
      have h₃ : u.eval (-3) = 0 := by norm_num [u]
      exact ⟨positive_degree (u := u) (a := -1) (b := -3) (by omega),
        local_of_hit (u := u) (n := 3) (by decide) (by
          change u.eval (u.eval (u.eval (-1))) = 0
          rw [h₁, h₂, h₃])⟩
    · refine ⟨by change 0 < (X - C (1 : ℤ)).natDegree; rw [natDegree_X_sub_C]; decide, ?_⟩
      intro p hp _
      have iter (m : ℕ) : (fun x => (X - 1 : ℤ[X]).eval x)^[m] (-1) = -1 - m := by
        induction m with
        | zero => simp
        | succ m ih => rw [Function.iterate_succ_apply', ih]; simp; ring
      refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
      rw [iter, show -1 - ((p - 1 : ℕ) : ℤ) = -(p : ℤ) by have := hp.one_le; omega]
      simp

namespace locallyNilpotent_not_nilpotentAt_one_neg_one

/-- The reflection of `u`, the polynomial `-u.comp (-X)`, takes the value `-u(-x)` at `x`. -/
private theorem eval_neg_comp_neg_X (u : ℤ[X]) (x : ℤ) :
    (-u.comp (-X)).eval x = -u.eval (-x) := by
  simp [eval_comp]

/-- The reflection `v(x) = -u(-x)` negates orbits: `v^{(n)}(-r) = -u^{(n)}(r)` (Fact 3.1). -/
private theorem iterate_neg_comp_neg_X (u : ℤ[X]) (r : ℤ) (n : ℕ) :
    (fun x => (-u.comp (-X)).eval x)^[n] (-r) = -(fun x => u.eval x)^[n] r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, eval_neg_comp_neg_X,
      neg_neg]

/-- The reflection `u(x) ↦ -u(-x)` is an involution. -/
private theorem neg_comp_neg_X_involutive (u : ℤ[X]) : -(-u.comp (-X)).comp (-X) = u := by
  rw [neg_comp, neg_neg, comp_assoc, neg_comp, X_comp, neg_neg, comp_X]

/-- The reflection `-u(-x)` has positive degree and is locally nilpotent but not nilpotent at
`-r` if and only if `u` has these properties at `r`. -/
private theorem neg_comp_neg_X_mem_iff {u : ℤ[X]} {r : ℤ} :
    (0 < (-u.comp (-X)).natDegree ∧ IsWeaklyLocallyNilpotentAt (-u.comp (-X)) (-r) ∅ ∧
        ¬ IsNilpotentAt (-u.comp (-X)) (-r)) ↔
      (0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u r ∅ ∧ ¬ IsNilpotentAt u r) := by
  simp only [natDegree_neg, natDegree_comp, natDegree_X, mul_one, IsWeaklyLocallyNilpotentAt,
    IsNilpotentAt, iterate_neg_comp_neg_X, dvd_neg, neg_eq_zero]

/-- Apart from `x - 1`, every polynomial of the classification at `-1` reaches zero within
three steps. -/
private theorem eq_X_sub_one_of_not_isNilpotentAt {u : ℤ[X]} (hdeg : 0 < u.natDegree)
    (hu : IsWeaklyLocallyNilpotentAt u (-1) ∅) (hnil : ¬ IsNilpotentAt u (-1)) : u = X - 1 := by
  have hmem : u ∈ {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅} :=
    ⟨hdeg, hu⟩
  rw [locallyNilpotentAt_neg_one_classification] at hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hmem
  rcases hmem with (((⟨q, -, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩) | h)
  · exact (hnil ⟨1, one_pos, by simp⟩).elim
  · exact (hnil ⟨2, two_pos, by norm_num [Function.iterate_succ_apply']⟩).elim
  · exact (hnil ⟨3, three_pos, by norm_num [Function.iterate_succ_apply']⟩).elim
  · exact h

end locallyNilpotent_not_nilpotentAt_one_neg_one

open locallyNilpotent_not_nilpotentAt_one_neg_one

/-- **Locally nilpotent but not nilpotent polynomials at $\pm 1$.** The only polynomial
$u \in \mathbb{Z}[x]$ of positive degree that is locally nilpotent at $1$ but not nilpotent at $1$
is $x + 1$, and the only polynomial of positive degree that is locally nilpotent at $-1$ but not
nilpotent at $-1$ is $x - 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.3. -/
public theorem locallyNilpotent_not_nilpotentAt_one_neg_one :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅ ∧ ¬ IsNilpotentAt u 1} =
        {X + 1} ∧
      {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u (-1) ∅ ∧
        ¬ IsNilpotentAt u (-1)} = {X - 1} := by
  have hplus : 0 < (X + 1 : ℤ[X]).natDegree ∧ IsWeaklyLocallyNilpotentAt (X + 1) 1 ∅ ∧
      ¬ IsNilpotentAt (X + 1) 1 :=
    ⟨by change 0 < (X + C (1 : ℤ)).natDegree; rw [natDegree_X_add_C]; exact one_pos,
      isWeaklyLocallyNilpotentAt_X_add_one, not_isNilpotentAt_X_add_one⟩
  have hminus : -(X + 1 : ℤ[X]).comp (-X) = X - 1 := by
    rw [add_comp, X_comp, one_comp]
    ring
  refine ⟨Set.ext fun u => ⟨fun h => ?_, ?_⟩, Set.ext fun u => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨hdeg, hu, hnil⟩ := neg_comp_neg_X_mem_iff.mpr h
    rw [Set.mem_singleton_iff, ← neg_comp_neg_X_involutive u,
      eq_X_sub_one_of_not_isNilpotentAt hdeg hu hnil, ← hminus, neg_comp_neg_X_involutive]
  · rintro rfl
    exact hplus
  · exact eq_X_sub_one_of_not_isNilpotentAt h.1 h.2.1 h.2.2
  · rintro rfl
    rw [← hminus]
    exact neg_comp_neg_X_mem_iff.mpr hplus

/-- **Classification of locally nilpotent polynomials at $1$.** A polynomial $u \in \mathbb{Z}[x]$
of positive degree is locally nilpotent at $1$ if and only if it has one of the following forms,
for some $p \in \mathbb{Z}[x]$: $(x-1)p(x)$ with $p \ne 0$; $-2x + 4 + p(x)(x-1)(x-2)$;
$-2x^2 + 7x - 3 + p(x)(x-1)(x-2)(x-3)$; or $u = x + 1$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Theorem 4.1. -/
public theorem locallyNilpotentAt_one_classification :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 1 ∅} =
      {u | ∃ p : ℤ[X], p ≠ 0 ∧ u = (X - 1) * p} ∪
        {u | ∃ p : ℤ[X], u = -2 * X + 4 + p * (X - 1) * (X - 2)} ∪
        {u | ∃ p : ℤ[X], u = -2 * X ^ 2 + 7 * X - 3 + p * (X - 1) * (X - 2) * (X - 3)} ∪
        {X + 1} := by
  ext u
  have hmem : -(u.comp (-X)) ∈ {v : ℤ[X] | 0 < v.natDegree ∧
      IsWeaklyLocallyNilpotentAt v (-1) ∅} ↔
      u ∈ {v : ℤ[X] | 0 < v.natDegree ∧ IsWeaklyLocallyNilpotentAt v 1 ∅} := by
    simp only [Set.mem_ofPred_eq, natDegree_neg, natDegree_comp, natDegree_X, mul_one,
      IsWeaklyLocallyNilpotentAt, iterate_neg_comp_neg_X, dvd_neg]
  rw [← hmem, locallyNilpotentAt_neg_one_classification]
  have reflect_eq (v : ℤ[X]) : -(u.comp (-X)) = v ↔ u = -(v.comp (-X)) :=
    ⟨fun h => by rw [← neg_comp_neg_X_involutive u, h],
      fun h => by rw [h, neg_comp_neg_X_involutive]⟩
  have reflect_first (p : ℤ[X]) : -(((X + 1) * p).comp (-X)) = (X - 1) * p.comp (-X) := by
    simp only [mul_comp, add_comp, X_comp, one_comp]
    ring
  have reflect_second (p : ℤ[X]) :
      -((-2 * X - 4 + p * (X + 1) * (X + 2)).comp (-X)) =
        -2 * X + 4 + -(p.comp (-X)) * (X - 1) * (X - 2) := by
    simp only [add_comp, sub_comp, mul_comp, neg_comp, ofNat_comp, X_comp, one_comp]
    ring
  have reflect_third (p : ℤ[X]) :
      -((2 * X ^ 2 + 7 * X + 3 + p * (X + 1) * (X + 2) * (X + 3)).comp (-X)) =
        -2 * X ^ 2 + 7 * X - 3 + p.comp (-X) * (X - 1) * (X - 2) * (X - 3) := by
    simp only [add_comp, mul_comp, pow_comp, ofNat_comp, X_comp, one_comp]
    ring
  have reflect_translation : -((X - 1 : ℤ[X]).comp (-X)) = X + 1 := by
    simp only [sub_comp, X_comp, one_comp]
    ring
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, reflect_eq, reflect_first,
    reflect_second, reflect_third, reflect_translation]
  have comp_surj : Function.Surjective (fun p : ℤ[X] => p.comp (-X)) :=
    (show Function.Involutive (fun p : ℤ[X] => p.comp (-X)) from
      comp_neg_X_comp_neg_X).surjective
  have neg_comp_surj : Function.Surjective (fun p : ℤ[X] => -(p.comp (-X))) :=
    (show Function.Involutive (fun p : ℤ[X] => -(p.comp (-X))) from
      neg_comp_neg_X_involutive).surjective
  refine or_congr (or_congr (or_congr ?_ ?_) ?_) Iff.rfl
  · simpa only [ne_eq, comp_neg_X_eq_zero_iff] using
      (comp_surj.exists (p := fun p => p ≠ 0 ∧ u = (X - 1) * p)).symm
  · exact (neg_comp_surj.exists (p := fun p => u = -2 * X + 4 + p * (X - 1) * (X - 2))).symm
  · exact (comp_surj.exists
      (p := fun p => u = -2 * X ^ 2 + 7 * X - 3 + p * (X - 1) * (X - 2) * (X - 3))).symm

end MetaMathlibExt
