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
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Resultant.Basic
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

At `0`, the polynomials of positive degree that are locally nilpotent but whose orbit never
reaches zero are the linear polynomials of Corollary 4.5. The source deduces that such a
polynomial is linear from a general result on orbits modulo primes that it quotes (its Fact 1.1);
here that step is proved directly for the orbit of `0`. Every prime dividing the difference of two
consecutive orbit values divides `u(0)`. If `u` has degree at least `2`, some factor `F` of
`u(x) - x` is coprime to `u'` over `ℚ`, and `F ∘ u = F M` with `M` nonconstant. The values of `F`
along the orbit form a divisibility chain, and the resultant of `F` and `M` bounds their common
divisors with the values of `M`. So at all but finitely many points of the orbit, `M` takes values
dividing a fixed power of `u(0)`, which is impossible on an infinite orbit.
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

namespace locallyNilpotent_not_nilpotentAt_zero

/-- A nonzero integer has a prime that does not divide it. -/
private theorem exists_prime_not_dvd {b : ℤ} (hb : b ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ b := by
  obtain ⟨p, hpb, hp⟩ := Nat.exists_infinite_primes (b.natAbs + 1)
  refine ⟨p, hp, fun h => ?_⟩
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hb) (Int.natCast_dvd.mp h)
  omega

/-- Congruent inputs stay congruent along the iterates of an integer polynomial. -/
private theorem dvd_iterate_sub (u : ℤ[X]) {n x y : ℤ} (h : n ∣ x - y) (j : ℕ) :
    n ∣ (fun x => u.eval x)^[j] x - (fun x => u.eval x)^[j] y := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ih.trans (sub_dvd_eval_sub _ _ u)

/-- If the orbit of `0` is locally nilpotent, a prime dividing the difference of two consecutive
orbit values divides `u(0)`: modulo that prime the orbit is constant from then on, and it is also
periodic through `0`. -/
private theorem dvd_eval_zero_of_dvd_succ_sub {u : ℤ[X]} (hu : IsWeaklyLocallyNilpotentAt u 0 ∅)
    {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : (p : ℤ) ∣ (fun x => u.eval x)^[k + 1] 0 - (fun x => u.eval x)^[k] 0) :
    (p : ℤ) ∣ u.eval 0 := by
  set f := fun x => u.eval x
  have hconst (j : ℕ) : (p : ℤ) ∣ f^[k + j] 0 - f^[k] 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := dvd_iterate_sub u hk j
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show j + (k + 1) = k + (j + 1) by ring, show j + k = k + j by ring] at h1
      have h2 := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at h2
  obtain ⟨m, hm, hpm⟩ := hu p hp (Set.notMem_empty p)
  have hper (t : ℕ) : (p : ℤ) ∣ f^[t * m] 0 := by
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 := dvd_iterate_sub u (x := f^[m] 0) (y := 0) (by simpa using hpm) (t * m)
      rw [← Function.iterate_add_apply] at h1
      rw [show (t + 1) * m = t * m + m by ring]
      have h2 := dvd_add h1 ih
      rwa [sub_add_cancel] at h2
  have h1 : (p : ℤ) ∣ f^[k * m + 1] 0 - f 0 := by
    rw [Function.iterate_succ_apply']
    exact (show (p : ℤ) ∣ f^[k * m] 0 - 0 by simpa using hper k).trans (sub_dvd_eval_sub _ _ u)
  have hkm : k ≤ k * m := Nat.le_mul_of_pos_right k hm
  have h2 := hconst (k * m - k)
  have h3 := hconst (k * m + 1 - k)
  rw [show k + (k * m - k) = k * m by omega] at h2
  rw [show k + (k * m + 1 - k) = k * m + 1 by omega] at h3
  have := dvd_sub (dvd_add (dvd_sub h3 h2) (hper k)) h1
  convert this using 1
  ring

/-- A locally nilpotent orbit of `0` that never returns to `0` takes infinitely many values. -/
private theorem range_infinite {u : ℤ[X]} (hu : IsWeaklyLocallyNilpotentAt u 0 ∅)
    (hnil : ¬ IsNilpotentAt u 0) :
    (Set.range fun k => (fun x => u.eval x)^[k] 0).Infinite := by
  classical
  intro hfin
  have hP : ∏ v ∈ hfin.toFinset.erase 0, v ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v hv => Finset.ne_of_mem_erase hv
  obtain ⟨p, hp, hpP⟩ := exists_prime_not_dvd hP
  obtain ⟨m, hm, hpm⟩ := hu p hp (Set.notMem_empty p)
  have hmem : (fun x => u.eval x)^[m] 0 ∈ hfin.toFinset.erase 0 :=
    Finset.mem_erase.mpr ⟨fun h => hnil ⟨m, hm, h⟩, hfin.mem_toFinset.mpr ⟨m, rfl⟩⟩
  exact hpP (hpm.trans (Finset.dvd_prod_of_mem (fun v => v) hmem))

/-- An integer all of whose prime factors divide `b`, none to the power `N`, divides `b ^ N`. -/
private theorem dvd_pow_of_forall_prime {m b : ℤ} (N : ℕ) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ^ N ∣ m) : m ∣ b ^ N := by
  have hm : m ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp, hpb⟩ := exists_prime_not_dvd hb
    exact hpb (h p hp (dvd_zero _)).1
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow]
  refine (Nat.factorization_prime_le_iff_dvd (Int.natAbs_ne_zero.mpr hm)
    (pow_ne_zero _ (Int.natAbs_ne_zero.mpr hb))).mp fun p hp => ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hpm : p ∣ m.natAbs
  · obtain ⟨hpb, hpN⟩ := h p hp (Int.natCast_dvd.mpr hpm)
    have h1 : 1 ≤ b.natAbs.factorization p :=
      hp.factorization_pos_of_dvd (Int.natAbs_ne_zero.mpr hb) (Int.natCast_dvd.mp hpb)
    have h2 : m.natAbs.factorization p < N := by
      by_contra! hle
      apply hpN
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast]
      exact (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr hm)).mpr hle
    nlinarith
  · rw [Nat.factorization_eq_zero_of_not_dvd hpm]
    exact Nat.zero_le _

/-- A nonconstant integer polynomial takes values dividing a fixed nonzero integer only at
finitely many integers. -/
private theorem finite_setOf_eval_dvd {M : ℤ[X]} (hM : 0 < M.natDegree) {c : ℤ} (hc : c ≠ 0) :
    {t : ℤ | M.eval t ∣ c}.Finite := by
  have hsub : {t : ℤ | M.eval t ∣ c} ⊆
      ⋃ v ∈ Finset.Icc (-|c|) |c|, {t | IsRoot (M - C v) t} := by
    intro t ht
    have hle := abs_le.mp (Int.le_of_dvd (abs_pos.mpr hc) ((abs_dvd_abs _ _).mpr ht))
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc, exists_prop, IsRoot.def,
      eval_sub, eval_C, sub_eq_zero]
    exact ⟨M.eval t, hle, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun v _ => ?_) hsub
  refine finite_setOfPred_isRoot fun h => ?_
  have := congrArg natDegree h
  rw [natDegree_sub_C, natDegree_zero] at this
  omega

/-- The core of the argument. Suppose that a factor `F` of `u - X` satisfies `F ∘ u = F * M` with
`M` nonconstant, and that some integer combination of `F` and `M` is a nonzero constant `ρ`. Then
the values `E k = F(u^(k)(0))` form a divisibility chain with `E (k + 1) = E k * M(u^(k)(0))`,
whose prime factors all divide `u(0)`, and `M(u^(k)(0))` shares with `E k` only divisors of `ρ`.
Hence `M(u^(k)(0))` divides a fixed power of `u(0)` for all but finitely many `k`, which forces
the orbit of `0` to be finite. -/
private theorem false_of_factor {u : ℤ[X]} (hu : IsWeaklyLocallyNilpotentAt u 0 ∅)
    (hnil : ¬ IsNilpotentAt u 0) {F M A B : ℤ[X]} {ρ : ℤ} (hFg : F ∣ u - X)
    (hFM : F.comp u = F * M) (hM : 0 < M.natDegree) (hρ : ρ ≠ 0)
    (hAB : F * A + M * B = C ρ) : False := by
  set a : ℕ → ℤ := fun k => (fun x => u.eval x)^[k] 0
  have ha_succ (k : ℕ) : a (k + 1) = u.eval (a k) := Function.iterate_succ_apply' _ _ _
  have hb : u.eval 0 ≠ 0 := fun h => hnil ⟨1, one_pos, h⟩
  set E : ℕ → ℤ := fun k => F.eval (a k) with hEdef
  set m : ℕ → ℤ := fun k => M.eval (a k) with hmdef
  have hE (k : ℕ) : E (k + 1) = E k * m k := by
    simp only [hEdef, hmdef, ha_succ, ← eval_comp, hFM, eval_mul]
  have hEdvd (k j : ℕ) : E k ∣ E (k + j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← add_assoc, hE]
      exact ih.trans (dvd_mul_right _ _)
  have hgcd (k : ℕ) (c : ℤ) (h1 : c ∣ E k) (h2 : c ∣ m k) : c ∣ ρ := by
    have := congrArg (eval (a k)) hAB
    simp only [eval_add, eval_mul, eval_C] at this
    rw [← this]
    exact dvd_add (h1.mul_right _) (h2.mul_right _)
  obtain ⟨G, hG⟩ := hFg
  have hED (k : ℕ) : E k ∣ a (k + 1) - a k := by
    have := congrArg (eval (a k)) hG
    simp only [eval_sub, eval_X, eval_mul] at this
    rw [ha_succ, this]
    exact dvd_mul_right _ _
  have hmb (k p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ m k) : (p : ℤ) ∣ u.eval 0 := by
    have h1 : (p : ℤ) ∣ a (k + 1 + 1) - a (k + 1) :=
      (h.trans (by rw [hE]; exact dvd_mul_left _ _)).trans (hED (k + 1))
    exact dvd_eval_zero_of_dvd_succ_sub hu hp h1
  set N := ρ.natAbs
  have hkey (p : ℕ) (hp : p.Prime) (k k' : ℕ) (hk : k < k') (h1 : (p : ℤ) ^ N ∣ m k)
      (h2 : (p : ℤ) ^ N ∣ m k') : False := by
    have h3 : (p : ℤ) ^ N ∣ E k' := by
      have := hEdvd (k + 1) (k' - (k + 1))
      rw [show k + 1 + (k' - (k + 1)) = k' by omega] at this
      exact (h1.trans (by rw [hE]; exact dvd_mul_left _ _)).trans this
    have h5 := Int.natAbs_dvd_natAbs.mpr (hgcd k' _ h3 h2)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h5
    have h6 := Nat.le_of_dvd (Int.natAbs_pos.mpr hρ) h5
    have h7 : N < p ^ N := Nat.lt_pow_self hp.one_lt
    omega
  -- The indices where `M` takes a value divisible by `p ^ N` for some prime `p` of `u(0)`.
  set bad : Set ℕ := ⋃ p ∈ (u.eval 0).natAbs.primeFactors, {k | (p : ℤ) ^ N ∣ m k}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
    refine Set.Subsingleton.finite fun k hk k' hk' => ?_
    have hp' := (Nat.mem_primeFactors.mp hp).1
    rcases lt_trichotomy k k' with h | h | h
    · exact (hkey p hp' k k' h hk hk').elim
    · exact h
    · exact (hkey p hp' k' k h hk' hk).elim
  have hT := finite_setOf_eval_dvd hM (pow_ne_zero N hb)
  apply range_infinite hu hnil
  refine ((hbad.image a).union hT).subset ?_
  rintro _ ⟨k, rfl⟩
  by_cases hk : k ∈ bad
  · exact Or.inl ⟨k, hk, rfl⟩
  · refine Or.inr (dvd_pow_of_forall_prime N hb fun p hp hpm => ⟨hmb k p hp hpm, fun hpN => ?_⟩)
    refine hk (Set.mem_biUnion (Nat.mem_primeFactors.mpr ⟨hp, ?_, Int.natAbs_ne_zero.mpr hb⟩)
      hpN)
    exact Int.natCast_dvd.mp (hmb k p hp hpm)

/-- For `u` of degree at least `2`, some factor `F` of `u - X` of positive degree is coprime over
`ℚ` to `u'`: divide `u - X` by its greatest common divisor with `u'` over `ℚ`, then clear
denominators and take the primitive part, which still divides `u - X` by Gauss's lemma. Writing
`F ∘ u = F * M`, the polynomial `M` is nonconstant and congruent to `u'` modulo `F`, so the
resultant of `F` and `M` is a nonzero integer combination of `F` and `M`. -/
private theorem exists_factor {u : ℤ[X]} (hu : 2 ≤ u.natDegree) :
    ∃ F M : ℤ[X], F ∣ u - X ∧ F.comp u = F * M ∧ 0 < M.natDegree ∧
      ∃ A B : ℤ[X], ∃ ρ : ℤ, ρ ≠ 0 ∧ F * A + M * B = C ρ := by
  classical
  set φ := Int.castRingHom ℚ
  have hφ : Function.Injective φ := RingHom.injective_int φ
  set g : ℚ[X] := (u - X).map φ with hgdef
  set d : ℚ[X] := derivative (u.map φ) with hddef
  have hgd : derivative g = d - 1 := by simp [hgdef, hddef, derivative_map]
  have hdeg : (u.map φ).natDegree = u.natDegree := natDegree_map_eq_of_injective hφ u
  have hd0 : d ≠ 0 := by
    rw [hddef, Ne, derivative_eq_zero, hdeg]
    omega
  have hgdeg : g.natDegree = u.natDegree := by
    rw [hgdef, natDegree_map_eq_of_injective hφ, natDegree_sub_eq_left_of_natDegree_lt]
    rw [natDegree_X]
    omega
  have hddeg : d.natDegree < u.natDegree := by
    rw [← hdeg]
    exact natDegree_derivative_lt (by omega)
  obtain ⟨f, hf⟩ := gcd_dvd_left g d
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hgdeg
    omega
  have hh0 : gcd g d ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hf
    exact hg0 hf
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hf
    exact hg0 hf
  have hfdeg : 0 < f.natDegree := by
    have h1 := congrArg natDegree hf
    have h2 := natDegree_le_of_dvd (gcd_dvd_right g d) hd0
    rw [natDegree_mul hh0 hf0] at h1
    omega
  have hcop : IsCoprime f d := by
    refine EuclideanDomain.isCoprime_of_dvd (fun h' => hf0 h'.1) fun z hz _ hzf hzd => ?_
    have hzh : z ∣ gcd g d := dvd_gcd (hzf.trans ⟨gcd g d, hf.trans (mul_comm _ _)⟩) hzd
    have hz2 : z ^ 2 ∣ g := by
      rw [hf, sq]
      exact mul_dvd_mul hzh hzf
    have h1 := pow_sub_one_dvd_derivative_of_pow_dvd hz2
    rw [hgd, show 2 - 1 = 1 by rfl, pow_one] at h1
    have h2 := dvd_sub hzd h1
    rw [sub_sub_cancel] at h2
    exact hz (isUnit_of_dvd_one h2)
  -- Clear the denominators of `f` and take the primitive part.
  obtain ⟨c, hc, hcf⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f
  set F₀ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  have hF₀ : F₀ ≠ 0 := IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hf0
  set F := F₀.primPart
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hc
  have hmapF₀ : F₀.map φ = C (c : ℚ) * f := by
    have h1 : algebraMap ℤ ℚ = φ := RingHom.ext_int _ _
    rw [← h1, hcf, zsmul_eq_mul, ← C_eq_intCast]
  have hFF₀ : F.map φ ∣ F₀.map φ := Polynomial.map_dvd φ (primPart_dvd F₀)
  have hunit : IsUnit (C (c : ℚ)) := isUnit_C.mpr (Ne.isUnit hc0)
  have hFg : F ∣ u - X := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast F (u - X) (isPrimitive_primPart F₀)]
    refine hFF₀.trans ?_
    rw [hmapF₀]
    exact hunit.mul_left_dvd.mpr ⟨gcd g d, hf.trans (mul_comm _ _)⟩
  have hFcop : IsCoprime (F.map φ) d := by
    refine IsCoprime.of_isCoprime_of_dvd_left ?_ hFF₀
    rw [hmapF₀]
    exact IsCoprime.mul_left (isCoprime_one_left.of_isCoprime_of_dvd_left hunit.dvd) hcop
  have hFdeg : 0 < F.natDegree := by
    have h1 : (F₀.map φ).natDegree = (F.map φ).natDegree := by
      rw [eq_C_content_mul_primPart F₀, Polynomial.map_mul, map_C, natDegree_C_mul]
      rw [Ne, map_eq_zero_iff φ hφ, content_eq_zero_iff]
      exact hF₀
    rw [hmapF₀, natDegree_C_mul hc0, natDegree_map_eq_of_injective hφ] at h1
    omega
  -- The cofactor `M` of `F` in `F ∘ u`, from the Taylor expansion of `F` at `X`.
  obtain ⟨G, hG⟩ := hFg
  obtain ⟨k, hk⟩ := binomExpansion (F.map C) X (u - X)
  rw [add_sub_cancel, ← eval₂_eq_eval_map, ← eval₂_eq_eval_map, eval₂_C_X, derivative_map,
    ← eval₂_eq_eval_map, eval₂_C_X] at hk
  change F.comp u = F + derivative F * (u - X) + k * (u - X) ^ 2 at hk
  set M := 1 + derivative F * G + k * F * G ^ 2
  have hFM : F.comp u = F * M := by
    rw [hk, hG]
    ring
  have hMd : M = derivative u + F * (k * G ^ 2 - derivative G) := by
    have h1 := congrArg derivative hG
    simp only [derivative_sub, derivative_X, derivative_mul] at h1
    linear_combination -h1
  have hF0 : F ≠ 0 := primPart_ne_zero F₀
  have hMdeg : 0 < M.natDegree := by
    have hcomp := natDegree_comp (p := F) (q := u)
    have hpos : 0 < F.natDegree * u.natDegree := Nat.mul_pos hFdeg (by omega)
    have hM0 : M ≠ 0 := by
      intro h0
      rw [hFM, h0, mul_zero, natDegree_zero] at hcomp
      omega
    rw [hFM, natDegree_mul hF0 hM0] at hcomp
    have : F.natDegree * 2 ≤ F.natDegree * u.natDegree := Nat.mul_le_mul_left _ hu
    omega
  have hMcop : IsCoprime (F.map φ) (M.map φ) := by
    rw [hMd, Polynomial.map_add, Polynomial.map_mul, ← derivative_map]
    exact hFcop.add_mul_left_right _
  refine ⟨F, M, ⟨G, hG⟩, hFM, hMdeg, ?_⟩
  obtain ⟨A, B, -, -, hAB⟩ :=
    exists_mul_add_mul_eq_C_resultant F M le_rfl le_rfl (Or.inl hFdeg.ne')
  refine ⟨A, B, _, ?_, hAB⟩
  have h1 := resultant_ne_zero _ _ hMcop
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map] at h1
  intro h0
  rw [h0, map_zero] at h1
  exact h1 rfl

/-- The orbit of `0` under `ax + b` is `b (1 + a + ⋯ + a^(n-1))` (Remark 2.2 of the source). -/
private theorem iterate_linear (a b : ℤ) (n : ℕ) :
    (fun x => (C a * X + C b).eval x)^[n] 0 = b * ∑ i ∈ Finset.range n, a ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, geom_sum_succ]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring

/-- A polynomial of degree at least `2` that is locally nilpotent at `0` is nilpotent at `0`. -/
private theorem natDegree_le_one_of_not_isNilpotentAt {u : ℤ[X]}
    (hu : IsWeaklyLocallyNilpotentAt u 0 ∅) (hnil : ¬ IsNilpotentAt u 0) : u.natDegree ≤ 1 := by
  by_contra! h
  obtain ⟨F, M, hFg, hFM, hM, A, B, ρ, hρ, hAB⟩ := exists_factor (u := u) h
  exact false_of_factor hu hnil hFg hFM hM hρ hAB

/-- `ax + b` with `b ≠ 0` and `|a| ≥ 2` never sends `0` back to `0`. -/
private theorem iterate_linear_ne_zero {a b : ℤ} (hb : b ≠ 0) (ha : a.natAbs ≠ 1) {n : ℕ}
    (hn : 0 < n) : b * ∑ i ∈ Finset.range n, a ^ i ≠ 0 := by
  refine mul_ne_zero hb fun h => ha ?_
  have h1 := geom_sum_mul a n
  rw [h, zero_mul, eq_comm, sub_eq_zero] at h1
  have h2 := congrArg Int.natAbs h1
  rw [Int.natAbs_pow, Int.natAbs_one] at h2
  exact (Nat.pow_eq_one.mp h2).resolve_right hn.ne'

/-- `ax + b` with every prime factor of `a` dividing `b` is locally nilpotent at `0`: primes
dividing `b` divide the first iterate; for any other prime `p`, the iterate of index `p` (if
`a ≡ 1`) or `p - 1` (otherwise, by Fermat's little theorem) is divisible by `p`. -/
private theorem isWeaklyLocallyNilpotentAt_linear {a b : ℤ}
    (hab : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) :
    IsWeaklyLocallyNilpotentAt (C a * X + C b) 0 ∅ := by
  intro p hp _
  simp only [iterate_linear]
  by_cases hpb : (p : ℤ) ∣ b
  · exact ⟨1, one_pos, by simpa using hpb⟩
  have := Fact.mk hp
  have ha : (a : ZMod p) ≠ 0 := fun h =>
    hpb (hab p hp ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))
  by_cases ha1 : (a : ZMod p) = 1
  · refine ⟨p, hp.pos, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    push_cast
    simp [ha1]
  · refine ⟨p - 1, by have := hp.two_le; omega, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
    push_cast
    rw [geom_sum_eq ha1, ZMod.pow_card_sub_one_eq_one ha]
    simp

end locallyNilpotent_not_nilpotentAt_zero

open locallyNilpotent_not_nilpotentAt_zero

/-- **Polynomials locally nilpotent but not nilpotent at $0$.** A polynomial $u \in \mathbb{Z}[x]$
of degree at least $1$ is locally nilpotent at $0$ and not nilpotent at $0$ if and only if either
$u = x + b$ for some integer $b \ne 0$, or $u = ax + b$ for some integers $a$ and $b$ with
$b \ne 0$ such that $a$ has at least one prime divisor and every prime divisor of $a$ divides $b$.

Source: Sayak Sengupta, *Locally Nilpotent Polynomials over Z*, INTEGERS 24 (2024),
Article A13, Corollary 4.5. -/
public theorem locallyNilpotent_not_nilpotentAt_zero :
    {u : ℤ[X] | 0 < u.natDegree ∧ IsWeaklyLocallyNilpotentAt u 0 ∅ ∧ ¬ IsNilpotentAt u 0} =
      {u | ∃ b : ℤ, b ≠ 0 ∧ u = X + C b} ∪
        {u | ∃ a b : ℤ, b ≠ 0 ∧ (∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ a) ∧
          (∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b) ∧ u = C a * X + C b} := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hdeg, hu, hnil⟩
    have h1 : u.natDegree = 1 := le_antisymm (natDegree_le_one_of_not_isNilpotentAt hu hnil) hdeg
    have hu_eq : u = C (u.coeff 1) * X + C (u.coeff 0) := eq_X_add_C_of_natDegree_le_one h1.le
    have ha : u.coeff 1 ≠ 0 := by
      rw [← h1]
      exact mt leadingCoeff_eq_zero.mp (by rintro rfl; simp at hdeg)
    set a := u.coeff 1
    set b := u.coeff 0
    rw [hu_eq] at hu hnil
    simp only [IsNilpotentAt, iterate_linear] at hnil
    have hb : b ≠ 0 := fun h => hnil ⟨1, one_pos, by simp [h]⟩
    by_cases ha1 : a = 1
    · exact Or.inl ⟨b, hb, by rw [hu_eq, ha1, C_1, one_mul]⟩
    by_cases ham1 : a = -1
    · exact (hnil ⟨2, two_pos, by simp [ham1, Finset.sum_range_succ]⟩).elim
    refine Or.inr ⟨a, b, hb, ?_, fun p hp hpa => ?_, hu_eq⟩
    · obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a.natAbs ≠ 1 by omega)
      exact ⟨p, hp, Int.natCast_dvd.mpr hpa⟩
    · obtain ⟨m, hm, hpm⟩ := hu p hp (Set.notMem_empty p)
      rw [iterate_linear] at hpm
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
      rw [zero_add, geom_sum_succ, mul_add, mul_one, mul_left_comm] at hpm
      exact (dvd_add_right (dvd_mul_of_dvd_left hpa _)).mp hpm
  · rintro (⟨b, hb, rfl⟩ | ⟨a, b, hb, ⟨q, hq, hqa⟩, hab, rfl⟩)
    · have hX : (X + C b : ℤ[X]) = C 1 * X + C b := by rw [C_1, one_mul]
      refine ⟨by rw [natDegree_X_add_C]; exact one_pos, ?_, ?_⟩
      · rw [hX]
        exact isWeaklyLocallyNilpotentAt_linear fun p hp h1 =>
          absurd (Int.eq_one_of_dvd_one (by positivity) h1) (by exact_mod_cast hp.one_lt.ne')
      · rw [hX]
        rintro ⟨n, hn, h⟩
        rw [iterate_linear] at h
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
        rcases mul_eq_zero.mp h with h | h
        · exact hb h
        · omega
    · have ha : a ≠ 0 := by
        rintro rfl
        obtain ⟨p, hp, hpb⟩ := exists_prime_not_dvd hb
        exact hpb (hab p hp (dvd_zero _))
      have ha1 : a.natAbs ≠ 1 := fun h => hq.one_lt.ne' (by
        have := Int.natCast_dvd.mp hqa
        rw [h] at this
        exact Nat.dvd_one.mp this)
      refine ⟨by rw [natDegree_linear ha]; exact one_pos,
        isWeaklyLocallyNilpotentAt_linear hab, ?_⟩
      rintro ⟨n, hn, h⟩
      rw [iterate_linear] at h
      exact iterate_linear_ne_zero hb ha1 hn h

end MetaMathlibExt
