/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.HalesJewett

/-!
# Vanishing blocks for symmetric functions

We use a monochromatic arithmetic progression of prefix sums to find consecutive
blocks of equal length whose sums vanish in `ZMod n`. Over `ZMod 6`, every sequence
contains a block of length at least two whose sum plus product vanishes.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$m$-vanishing family.** Let $n$ be a natural number and let $F = (f^{(l)})_{l \ge 0}$ be a
family of functions $f^{(l)} : (\mathbb{Z}/n\mathbb{Z})^l \to M$ into a type $M$ with a zero
element. For a natural number $m$, $F$ is $m$-vanishing if for every sequence
$a_0, a_1, a_2, \dots$ of elements of $\mathbb{Z}/n\mathbb{Z}$ there are a length $l > 1$ and a
start $s \ge 0$ such that $f^{(l)}(a_{s+jl}, a_{s+jl+1}, \dots, a_{s+jl+l-1}) = 0$ for every
$j < m$; that is, the sequence contains $m$ consecutive blocks of a common length $l > 1$ on each
of which $f^{(l)}$ vanishes.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public def IsMVanishingFamily {n : ℕ} {M : Type*} [Zero M] (m : ℕ)
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ a : ℕ → ZMod n, ∃ l, 1 < l ∧ ∃ s, ∀ j < m, F l (fun i => a (s + j * l + i)) = 0

/-- **Vanishing family.** Let $n$ be a natural number. A family $F$ of functions on blocks over
$\mathbb{Z}/n\mathbb{Z}$ with values in a type with a zero is vanishing if it is $m$-vanishing for
every positive integer $m$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
vanishing). -/
public def IsVanishingFamily {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ m, 0 < m → IsMVanishingFamily m F

/-- **The sum-plus-product family $F_c$.** For $c \in \mathbb{Z}/n$, the family $F_c$ over
$\mathbb{Z}/n$ sends a block $(b_1, \dots, b_l)$ of elements of $\mathbb{Z}/n$, of any length
$l \ge 0$, to $b_1 + \dots + b_l + c\, b_1 b_2 \cdots b_l$, where an empty sum is $0$ and an
empty product is $1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public def sumAddMulProdFamily {n : ℕ} (c : ZMod n) (l : ℕ) (b : Fin l → ZMod n) :
    ZMod n :=
  ∑ i, b i + c * ∏ i, b i

/-- **Monotonicity of $m$-vanishing.** Let $F$ be a family of functions on blocks over
$\mathbb{Z}/n$ with values in a type $M$ with a zero. If $F$ is $m$-vanishing and $m' \le m$,
then $F$ is $m'$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem IsMVanishingFamily.mono {n : ℕ} {M : Type*} [Zero M]
    {F : (l : ℕ) → (Fin l → ZMod n) → M} {m m' : ℕ} (h : IsMVanishingFamily m F)
    (hm : m' ≤ m) : IsMVanishingFamily m' F := by
  intro a
  obtain ⟨l, hl, s, hs⟩ := h a
  exact ⟨l, hl, s, fun j hj => hs j (lt_of_lt_of_le hj hm)⟩

/-- **Every family is $0$-vanishing.** For every natural number $n$ and every family $F$ of
functions $f^{(l)} : (\mathbb{Z}/n\mathbb{Z})^l \to M$, $l \ge 0$, into a type $M$ with a zero
element, $F$ is $0$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem isMVanishingFamily_zero {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : IsMVanishingFamily 0 F :=
  fun _ => ⟨2, Nat.one_lt_two, 0, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

/-- **The sum-plus-product family on blocks of length two.** For $c \in \mathbb{Z}/n$ and
$b_0, b_1 \in \mathbb{Z}/n$, the sum-plus-product family $F_c$ over $\mathbb{Z}/n$ satisfies
$F_c(b_0, b_1) = b_0 + b_1 + c\, b_0 b_1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public theorem sumAddMulProdFamily_two {n : ℕ} (c : ZMod n) (b : Fin 2 → ZMod n) :
    sumAddMulProdFamily c 2 b = b 0 + b 1 + c * (b 0 * b 1) := by
  simp [sumAddMulProdFamily, Fin.sum_univ_two, Fin.prod_univ_two]

/-- **Zero-sum van der Waerden theorem.** For every positive integer $n$, the family over
$\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to $\sum_i b_i$ is vanishing: for
every $m > 0$, every sequence over $\mathbb{Z}/n\mathbb{Z}$ contains $m$ consecutive blocks of a
common length $l > 1$, each with sum zero.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 1
(`integers-2026-A25-thm-1`). -/
public theorem isVanishingFamily_sum {n : ℕ} (hn : 0 < n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) => ∑ i, b i) := by
  intro m _ a
  have : NeZero n := ⟨hn.ne'⟩
  let prefixSum (k : ℕ) := ∑ i ∈ Finset.range k, a i
  -- Color each index by the prefix sum at twice that index.
  obtain ⟨d, hd, s, c, hmono⟩ := Combinatorics.exists_mono_homothetic_copy
    (Finset.range (m + 1)) (fun t => prefixSum (t * 2))
  have boundary (j : ℕ) (hj : j ≤ m) : prefixSum (s * 2 + j * (d * 2)) = c := by
    have hj' := hmono j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa [nsmul_eq_mul, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.add_comm] using hj'
  refine ⟨d * 2, by omega, s * 2, ?_⟩
  intro j hj
  -- The block sum is the difference of the prefix sums at its two boundaries.
  change ∑ i : Fin (d * 2), a (s * 2 + j * (d * 2) + i) = 0
  rw [Fin.sum_univ_eq_sum_range (fun i => a (s * 2 + j * (d * 2) + i)),
    ← Finset.sum_range_add_sub_sum_range]
  change prefixSum (s * 2 + j * (d * 2) + d * 2) - prefixSum (s * 2 + j * (d * 2)) = 0
  rw [Nat.add_assoc, ← Nat.succ_mul, boundary (j + 1) hj, boundary j hj.le, sub_self]

namespace isMVanishingFamily_one_sumAddMulProd_one_six

private abbrev Summary := ZMod 6 × ZMod 6

private def extend (x : ZMod 6) (p : Summary) : Summary :=
  (p.1 + x, p.2 * x)

-- Every continuation must either make the running product zero or complete a vanishing block.
-- Only extended suffixes have length at least two. A singleton seeds the next step.
private def forced : ℕ → ZMod 6 → List Summary → Bool
  | 0, _, _ => false
  | d + 1, product, suffixes => (List.finRange 6).all fun (x : ZMod 6) =>
    let longer := suffixes.map (extend x)
    ((product * x == 0) || longer.any (fun p => p.1 + p.2 == 0)) ||
      forced d (product * x) ((x, x) :: longer)

private theorem forced_fourteen : forced 14 1 [] = true := by decide +kernel

private def summary (a : ℕ → ZMod 6) (s l : ℕ) : Summary :=
  (∑ i : Fin l, a (s + i), ∏ i : Fin l, a (s + i))

private theorem summary_succ (a : ℕ → ZMod 6) (s l : ℕ) :
    summary a s (l + 1) = extend (a (s + l)) (summary a s l) := by
  simp [summary, extend, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]

-- Each stored pair is the sum and product of a nonempty suffix ending just before index k.
private theorem exists_block_of_forced (a : ℕ → ZMod 6) (d k : ℕ) (suffixes : List Summary)
    (h : forced d (∏ i ∈ Finset.range k, a i) suffixes = true)
    (hnz : ∀ t ≤ k + d, (∏ i ∈ Finset.range t, a i) ≠ 0)
    (hs : ∀ p ∈ suffixes, ∃ s l, 0 < l ∧ s + l = k ∧ summary a s l = p) :
    ∃ s l, 1 < l ∧ sumAddMulProdFamily 1 l (fun i => a (s + i)) = 0 := by
  induction d generalizing k suffixes with
  | zero => simp [forced] at h
  | succ d ih =>
    have step := List.all_eq_true.mp h (a k) (List.mem_finRange (a k))
    have hprod := hnz (k + 1) (by omega)
    rw [Finset.prod_range_succ] at hprod
    simp only [hprod, beq_iff_eq, Bool.or_eq_true, false_or] at step
    have longer (p) (hp : p ∈ suffixes.map (extend (a k))) :
        ∃ s l, 1 < l ∧ s + l = k + 1 ∧ summary a s l = p := by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨s, l, hl, rfl, rfl⟩ := hs q hq
      exact ⟨s, l + 1, by omega, rfl, summary_succ ..⟩
    rcases step with hit | next
    · obtain ⟨p, hp, hz⟩ := List.any_eq_true.mp hit
      obtain ⟨s, l, hl, _, rfl⟩ := longer p hp
      exact ⟨s, l, hl, by simpa [summary, sumAddMulProdFamily] using hz⟩
    · apply ih (k + 1) _ (by simpa only [Finset.prod_range_succ] using next)
      · exact fun t ht => hnz t (by omega)
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨k, 1, by decide, rfl, by simp [summary]⟩
        · obtain ⟨s, l, hl, hend, heq⟩ := longer p hp
          exact ⟨s, l, by omega, hend, heq⟩

end isMVanishingFamily_one_sumAddMulProd_one_six

open isMVanishingFamily_one_sumAddMulProd_one_six in
/-- **The sum-plus-product family is $1$-vanishing over $\mathbb{Z}/6\mathbb{Z}$.** Let $F_1$ be
the family over $\mathbb{Z}/6\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to
$\sum_i b_i + \prod_i b_i$. Then $F_1$ is $1$-vanishing: every sequence over
$\mathbb{Z}/6\mathbb{Z}$ contains a block of consecutive terms, of some length $l > 1$, on which
$F_1$ vanishes.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 3
(`integers-2026-A25-lem-3`). -/
public theorem isMVanishingFamily_one_sumAddMulProd_one_six :
    IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 6)) := by
  intro a
  suffices h : ∃ s l, 1 < l ∧ sumAddMulProdFamily 1 l (fun i => a (s + i)) = 0 by
    obtain ⟨s, l, hl, hz⟩ := h
    exact ⟨l, hl, s, by simpa using hz⟩
  -- Two equal prefix sums at multiples of 14 enclose a long zero-sum block.
  obtain ⟨u, v, huv, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => ∑ i ∈ Finset.range (14 * n), a i) (fun _ => Set.mem_univ _)
  let s := 14 * u
  let l := 14 * (v - u)
  have hlen : 14 ≤ l := by dsimp [l]; omega
  have hend : s + l = 14 * v := by dsimp [s, l]; omega
  let b (i : ℕ) := a (s + i)
  have hsum : ∑ i : Fin l, b i = 0 := by
    rw [Fin.sum_univ_eq_sum_range b]
    change ∑ i ∈ Finset.range l, a (s + i) = 0
    rw [← Finset.sum_range_add_sub_sum_range, hend, ← heq]
    exact sub_self _
  by_cases hprod : (∏ i ∈ Finset.range l, b i) = 0
  · refine ⟨s, l, by omega, ?_⟩
    change sumAddMulProdFamily 1 l (fun i => b i) = 0
    simp [sumAddMulProdFamily, hsum, Fin.prod_univ_eq_prod_range b, hprod]
  · have hnz (t : ℕ) (ht : t ≤ 14) : (∏ i ∈ Finset.range t, b i) ≠ 0 := by
      apply mt _ hprod
      intro htzero
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show t ≤ l by omega)
      rw [hr, Finset.prod_range_add, htzero, zero_mul]
    obtain ⟨s', l', hl', hz⟩ := exists_block_of_forced b 14 0 [] (by simpa using forced_fourteen)
      (by simpa using hnz) (by simp)
    exact ⟨s + s', l', hl', by simpa only [b, Nat.add_assoc] using hz⟩

end

end MetaMathlibExt
