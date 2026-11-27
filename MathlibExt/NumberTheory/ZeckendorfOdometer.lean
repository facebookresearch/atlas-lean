/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Zeckendorf
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.Iterate
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Sort
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Stopping a block in the Zeckendorf odometer

The block stopping theorem bounds which digits can change when a block of Fibonacci
summands is added to a Zeckendorf-adic integer.

Each digit of a finite iterate depends on a finite prefix of the input, so it suffices to
analyze addition of natural numbers. The proof splits each input at the upper window of
four zeros. To bound how far a carry from the two upper tails can descend, it translates
their indices down and uses the conjugate of the golden ratio to control normalization.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Zeckendorf-adic integers.** The Zeckendorf-adic integers $\mathbb{X}$ are the digit
sequences $x = (x_k)_{k \ge 0}$ with $x_k \in \{0, 1\}$ such that $x_0 = x_1 = 0$ and no two
consecutive digits are both $1$, that is, $x_k x_{k+1} = 0$ for every $k$.

Digit $k \ge 2$ carries the weight $F_k$ (with $F_1 = F_2 = 1$). The unused digits $x_0$ and
$x_1$ keep the paper's indexing, in which
$\mathbb{X} = \{x \in \{0,1\}^{\mathbb{N}_{\ge 2}} : x_k x_{k+1} = 0 \text{ for all } k \ge 2\}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (arXiv:2309.14285v2). -/
public def zeckAdic : Set (ℕ → Bool) :=
  {x | x 0 = false ∧ x 1 = false ∧ ∀ k, x k = false ∨ x (k + 1) = false}

/-- **Zeckendorf digit sequence of a natural number.** Let $F_k$ be the Fibonacci numbers
($F_0 = 0$, $F_1 = F_2 = 1$). Every $n \in \mathbb{N}$ has a unique Zeckendorf representation
$n = F_{k_1} + \dots + F_{k_m}$ with $k_1 > \dots > k_m \ge 2$ and no two consecutive indices.
The Zeckendorf digit sequence of $n$ is the binary sequence $(x_k)_{k \in \mathbb{N}}$ with
$x_k = 1$ if $k$ is one of the indices $k_1, \dots, k_m$ and $x_k = 0$ otherwise.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (the map `i`). -/
public def zeckAdicOfNat (n : ℕ) : ℕ → Bool := fun k => decide (k ∈ Nat.zeckendorf n)

/-- **The Zeckendorf odometer.** The odometer is the map $T$ on digit sequences
$x = (x_k)_{k \in \mathbb{N}}$ with $x_k \in \{0, 1\}$ defined as follows. If $x_k = x_{k+1} = 0$
for some $k \ge 2$, let $k$ be the least such index; then $T(x)_j = 0$ for $j < k$, $T(x)_k = 1$
and $T(x)_j = x_j$ for $j > k$. If there is no such $k$, then $T(x)$ is the zero sequence.

On a Zeckendorf-adic integer, where digit $k \ge 2$ carries the weight of the Fibonacci number
$F_k$, the map $T$ is addition of $1$, and $x + r$ denotes $T^r(x)$ for $r \in \mathbb{N}$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Section 2.2 (definition of `T`). -/
public noncomputable def zeckOdometer (x : ℕ → Bool) : ℕ → Bool :=
  open Classical in
  if h : ∃ k, 2 ≤ k ∧ x k = false ∧ x (k + 1) = false then
    fun j => if j < Nat.find h then false else if j = Nat.find h then true else x j
  else fun _ => false

end

namespace zeckOdometer_stopping_block

open Nat (fib fib_mono fib_add_two fib_add zeckendorf zeckendorf_sum_fib
  isZeckendorfRep_zeckendorf sum_zeckendorf_fib)

private abbrev value (l : List ℕ) := (l.map fib).sum

private abbrev Gap (a b : ℕ) := b + 2 ≤ a

local instance gapTrans : IsTrans ℕ Gap := ⟨fun _ _ _ h₁ h₂ => by unfold Gap at *; omega⟩

private theorem rep_iff {l : List ℕ} :
    l.IsZeckendorfRep ↔ l.Pairwise Gap ∧ ∀ i ∈ l, 2 ≤ i := by
  change List.IsChain Gap (l ++ [0]) ↔ _
  simp [List.isChain_iff_pairwise, List.pairwise_append, Gap]

private theorem rep_filter {l : List ℕ} (h : l.IsZeckendorfRep) (p : ℕ → Bool) :
    (l.filter p).IsZeckendorfRep := by
  obtain ⟨h, h'⟩ := rep_iff.mp h
  exact rep_iff.mpr ⟨h.filter _, fun i hi => h' i (List.mem_filter.mp hi).1⟩

private theorem rep_cons {a : ℕ} {l : List ℕ} (ha : 2 ≤ a) (hl : l.IsZeckendorfRep)
    (hgap : ∀ b ∈ l, b + 2 ≤ a) : (a :: l).IsZeckendorfRep := by
  simp_all [rep_iff, List.pairwise_cons, Gap]

private theorem rep_append {l s : List ℕ} (hl : l.IsZeckendorfRep) (hs : s.IsZeckendorfRep)
    (h : ∀ a ∈ l, ∀ b ∈ s, b + 2 ≤ a) : (l ++ s).IsZeckendorfRep := by
  simp_all [rep_iff, List.pairwise_append, Gap, or_imp]

private theorem value_lt {l : List ℕ} (h : l.IsZeckendorfRep) {n : ℕ} (hn : 0 < n)
    (hb : ∀ i ∈ l, i < n) : value l < fib n := by
  apply h.sum_fib_lt
  intro a ha
  have := List.mem_of_mem_head? ha
  simp only [List.mem_append, List.mem_singleton] at this
  rcases this with ha | rfl
  · exact hb _ ha
  · exact hn

private theorem mem_lt {v n i : ℕ} (hv : v < fib n) (hi : i ∈ zeckendorf v) : i < n := by
  apply lt_of_not_ge
  intro h
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fib) hi)
  simp only [sum_zeckendorf_fib] at this
  exact (hv.trans_le ((fib_mono h).trans this)).false

/-! ### Finite prefixes and the action of one odometer step -/

private def digits (x : ℕ → Bool) : ℕ → List ℕ
  | 0 => []
  | n + 1 => if x n then n :: digits x n else digits x n

private theorem mem_digits {x : ℕ → Bool} {i n : ℕ} :
    i ∈ digits x n ↔ i < n ∧ x i = true := by
  induction n with
  | zero => simp [digits]
  | succ n ih =>
    simp only [digits]
    split <;> simp_all <;> grind

private theorem digits_rep {x : ℕ → Bool} (hx : x ∈ zeckAdic) (n : ℕ) :
    (digits x n).IsZeckendorfRep := by
  induction n with
  | zero => exact List.IsZeckendorfRep_nil
  | succ n ih =>
    simp only [digits]
    split
    next h =>
      obtain ⟨h0, h1, hn⟩ := hx
      refine rep_cons (by by_contra! hn; interval_cases n <;> simp_all) ih fun i hi => ?_
      obtain ⟨hi, hxi⟩ := mem_digits.mp hi
      have := hn i
      grind
    next => exact ih

private theorem ofNat_value {l : List ℕ} (hl : l.IsZeckendorfRep) (i : ℕ) :
    zeckAdicOfNat (value l) i = decide (i ∈ l) := by rw [zeckAdicOfNat, zeckendorf_sum_fib hl]

private theorem apart {l : List ℕ} (hl : l.IsZeckendorfRep) {i : ℕ} (hi : i ∈ l) :
    i + 1 ∉ l := by
  have hp := (rep_iff.mp hl).1
  induction l with
  | nil => simp at hi
  | cons a l ih =>
    simp only [List.pairwise_cons] at hp
    simp only [List.mem_cons] at *
    grind [rep_iff, List.pairwise_cons]

private theorem ofNat_adic (v : ℕ) : zeckAdicOfNat v ∈ zeckAdic := by
  have h := isZeckendorfRep_zeckendorf v
  have hb := (rep_iff.mp h).2
  simp only [zeckAdicOfNat, zeckAdic, Set.mem_ofPred_eq, decide_eq_false_iff_not]
  exact ⟨fun hi => by have := hb _ hi; omega, fun hi => by have := hb _ hi; omega,
    fun i => or_iff_not_imp_left.mpr fun hi => apart h (not_not.mp hi)⟩

private theorem rep_ext {l s : List ℕ} (hl : l.IsZeckendorfRep) (hs : s.IsZeckendorfRep)
    (hm : ∀ i, i ∈ l ↔ i ∈ s) : l = s := by
  have pl := (rep_iff.mp hl).1
  have ps := (rep_iff.mp hs).1
  have hp := (List.perm_ext_iff_of_nodup (pl.imp (by unfold Gap; omega))
    (ps.imp (by unfold Gap; omega))).2 hm
  exact hp.eq_of_pairwise (fun _ _ h₁ h₂ => by unfold Gap at *; omega) pl ps

private abbrev stop (x : ℕ → Bool) (k : ℕ) :=
  2 ≤ k ∧ x k = false ∧ x (k + 1) = false

private theorem digit_step {x : ℕ → Bool} {k : ℕ} :
    zeckOdometer x k = true ↔
      (stop x k ∧ ∀ i < k, ¬stop x i) ∨ (x k = true ∧ ∃ i < k, stop x i) := by
  classical
  unfold zeckOdometer
  split
  next h =>
    have hs := Nat.find_spec h
    have hm : ∀ i < Nat.find h, ¬stop x i := fun i hi => Nat.find_min h hi
    have hb : ∀ i, stop x i → Nat.find h ≤ i := fun i hi => Nat.find_min' h hi
    rcases lt_trichotomy k (Nat.find h) with hk | rfl | hk
    · simp only [ite_eq_left hk, Bool.false_eq_true, false_iff]
      grind only
    · simp only [lt_irrefl, ite_false, ite_true, true_iff]
      exact Or.inl ⟨hs, hm⟩
    · simp only [ite_eq_right hk.not_gt, ite_eq_right hk.ne']
      grind only
  next h =>
    simp only [Bool.false_eq_true, false_iff]
    grind only

private theorem iterate_local {x y : ℕ → Bool} (r k : ℕ)
    (h : ∀ i ≤ k + r, x i = y i) : zeckOdometer^[r] x k = zeckOdometer^[r] y k := by
  induction r generalizing x y with
  | zero => exact h k (by omega)
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih
    intro j hj
    have hs (i : ℕ) (hi : i ≤ j) : stop x i ↔ stop y i := by
      simp only [stop, h i (by omega), h (i + 1) (by omega)]
    apply Bool.eq_iff_iff.mpr
    rw [digit_step, digit_step, hs j le_rfl, h j (by omega)]
    grind only

private theorem prefix_before_stop {x : ℕ → Bool} (hx : x ∈ zeckAdic) {n : ℕ}
    (hn : 2 ≤ n) (hz : x n = false) (hm : ∀ i < n, ¬stop x i) :
    value (digits x n) + 1 = fib n := by
  obtain ⟨h0, h1, ha⟩ := hx
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 => omega
    | 2 => simp [value, digits, h0, h1]
    | 3 =>
      have hh := hm 2 (by decide)
      have ht : x 2 = true := by grind only
      simp [value, digits, h0, h1, ht, fib_add_two]
    | i + 4 =>
      have hh := hm (i + 3) (by omega)
      have ht : x (i + 3) = true := by grind only
      have hf : x (i + 2) = false := (ha (i + 2)).resolve_right (by simp [ht])
      have hi := ih (i + 2) (by omega) (by omega) hf (fun j hj => hm j (by omega))
      rw [show i + 4 = (i + 2) + 2 by rfl, fib_add_two]
      rw [digits, ite_eq_left ht, digits, ite_eq_right (by simp [hf])]
      change fib (i + 3) + value (digits x (i + 2)) + 1 = fib (i + 2) + fib (i + 3)
      omega

private theorem ofNat_succ (v : ℕ) : zeckOdometer (zeckAdicOfNat v) = zeckAdicOfNat (v + 1) := by
  classical
  let x := zeckAdicOfNat v
  have hx := ofNat_adic v
  let N := v.zeckendorf.sum + 3
  have hbound {i : ℕ} (hi : i ∈ zeckendorf v) : i + 2 ≤ N := by
    have := List.le_sum_of_mem hi
    dsimp [N]
    omega
  have hex : ∃ i, stop x i := by
    refine ⟨N, by dsimp [N]; omega, ?_, ?_⟩ <;>
      simp only [x, zeckAdicOfNat, decide_eq_false_iff_not] <;>
      intro hi <;> have := hbound hi <;> omega
  let j := Nat.find hex
  obtain ⟨hj, hz, hz'⟩ := Nat.find_spec hex
  have hm (i : ℕ) (hi : i < j) : ¬stop x i := Nat.find_min hex hi
  let hi := v.zeckendorf.filter (j < ·)
  let lo := digits x j
  have hs := isZeckendorfRep_zeckendorf v
  have hu := rep_filter hs (j < ·)
  have hu' : ∀ i ∈ hi, j + 2 ≤ i := by
    intro i hi
    obtain ⟨him, hgt⟩ := List.mem_filter.mp hi
    change decide (j < i) = true at hgt
    have hn : j + 1 ∉ zeckendorf v := of_decide_eq_false hz'
    have hn' : i ≠ j + 1 := fun e => hn (e ▸ him)
    simp only [decide_eq_true_eq] at hgt
    omega
  have horig : hi ++ lo = v.zeckendorf := by
    apply rep_ext (rep_append hu (digits_rep hx j) fun a ha b hb => by
      have := hu' a ha; have := (mem_digits.mp hb).1; omega) hs
    intro i
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, mem_digits, zeckAdicOfNat]
    have hnot : j ∉ zeckendorf v := of_decide_eq_false hz
    grind only
  have hval : value (hi ++ [j]) = v + 1 := by
    have he := congrArg value horig
    have he' : value (digits x j) + 1 = fib j := prefix_before_stop hx hj hz hm
    simp only [value, List.map_append, List.sum_append, sum_zeckendorf_fib] at he
    simp only [value, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    change value hi + value (digits x j) = v at he
    change value hi + fib j = v + 1
    omega
  have hrep : (hi ++ [j]).IsZeckendorfRep :=
    rep_append hu (rep_cons hj List.IsZeckendorfRep_nil (by simp)) (by simpa using hu')
  funext k
  change zeckOdometer x k = _
  rw [← hval, ofNat_value hrep]
  unfold zeckOdometer
  rw [dite_eq_left hex]
  change (if k < j then false else if k = j then true else x k) = _
  simp only [hi, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton,
    x, zeckAdicOfNat]
  rcases lt_trichotomy k j with hk | rfl | hk <;> simp [*] <;> grind only

private theorem ofNat_iterate (v r : ℕ) :
    zeckOdometer^[r] (zeckAdicOfNat v) = zeckAdicOfNat (v + r) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', ih, ofNat_succ, Nat.add_assoc]

/-! ### Addition of two upper tails -/

open scoped goldenRatio

private noncomputable abbrev err (l : List ℕ) : ℝ := (l.map (ψ ^ ·)).sum

-- Reading a binary word from its least significant end bounds its conjugate value.
private theorem shift_interval {e : ℝ} (h : -1 < e ∧ e < φ) (n : ℕ) :
    -1 < ψ ^ n * e ∧ ψ ^ n * e < φ := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    constructor
    · simpa [Real.goldenConj_mul_goldenRatio] using
        mul_lt_mul_of_neg_left ih.2 Real.goldenConj_neg
    · linarith [mul_lt_mul_of_neg_left ih.1 Real.goldenConj_neg, Real.goldenRatio_add_goldenConj]

private theorem err_bound {l : List ℕ} (hl : l.Pairwise Gap) (t : ℕ)
    (ht : ∀ i ∈ l, t ≤ i) : ∃ e : ℝ, (-1 < e ∧ e < φ) ∧ err l = ψ ^ t * e := by
  induction l using List.reverseRecOn generalizing t with
  | nil => exact ⟨0, ⟨by norm_num, Real.goldenRatio_pos⟩, by simp [err]⟩
  | append_singleton l a ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨e, he, hE⟩ := ih hl.1 (a + 1) fun i hi => by
      have := hl.2.2 i hi a (by simp)
      unfold Gap at this
      omega
    have ha := ht a (by simp)
    have hw : -1 < 1 + ψ * e ∧ 1 + ψ * e < φ := by
      have h₁ := mul_lt_mul_of_neg_left he.2 Real.goldenConj_neg
      have h₂ := mul_lt_mul_of_neg_left he.1 Real.goldenConj_neg
      rw [Real.goldenConj_mul_goldenRatio] at h₁
      constructor <;> linarith [Real.goldenRatio_add_goldenConj]
    refine ⟨_, shift_interval hw (a - t), ?_⟩
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le ha]
    simp only [err, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at hE ⊢
    rw [hE, pow_succ]
    ring

private abbrev nextValue (l : List ℕ) := (l.map fun i => fib (i + 1)).sum

private theorem next_error (l : List ℕ) :
    (nextValue l : ℝ) - φ * (value l : ℝ) = err l := by
  induction l with
  | nil => simp [nextValue, value, err]
  | cons a l ih =>
    simp only [nextValue, value, err, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    linarith [Real.fib_succ_sub_goldenRatio_mul_fib a]

-- A canonical expansion has conjugate value in the open interval (-ψ², -ψ) of length one.
-- Two expansions starting at index four also have their combined conjugate value in this
-- interval. Since normalization preserves the Fibonacci value, the two conjugate values
-- differ by an integer, so they coincide.
private theorem next_add {l s : List ℕ} (hl : l.Pairwise Gap) (hs : s.Pairwise Gap)
    (hl4 : ∀ i ∈ l, 4 ≤ i) (hs4 : ∀ i ∈ s, 4 ≤ i) :
    nextValue (zeckendorf (value l + value s)) = nextValue l + nextValue s := by
  let z := zeckendorf (value l + value s)
  have hz := rep_iff.mp (isZeckendorfRep_zeckendorf (value l + value s))
  obtain ⟨e₁, he₁, h₁⟩ := err_bound hl 4 hl4
  obtain ⟨e₂, he₂, h₂⟩ := err_bound hs 4 hs4
  obtain ⟨e, he, h⟩ := err_bound hz.1 2 hz.2
  change err z = _ at h
  have hsq := Real.goldenConj_sq
  have hprod := Real.goldenConj_mul_goldenRatio
  have hsneg := Real.goldenConj_neg
  have hsign : 0 < ψ ^ 2 := sq_pos_of_neg hsneg
  have hfour : 0 < ψ ^ 4 := by simpa only [← pow_mul] using sq_pos_of_pos hsign
  have hrange : -(ψ ^ 2) < err z ∧ err z < -ψ := by
    rw [h]
    constructor
    · linarith [mul_lt_mul_of_pos_left he.1 hsign]
    · calc
        _ < ψ ^ 2 * φ := mul_lt_mul_of_pos_left he.2 hsign
        _ = -ψ := by linear_combination ψ * hprod
  have hsum : -(ψ ^ 2) < err l + err s ∧ err l + err s < -ψ := by
    rw [h₁, h₂]
    have hhalf : 2 * ψ ^ 2 < 1 := by nlinarith [Real.goldenRatio_lt_two, hsq, hprod,
      Real.goldenRatio_add_goldenConj]
    constructor
    · nlinarith [mul_lt_mul_of_pos_left he₁.1 hfour, mul_lt_mul_of_pos_left he₂.1 hfour,
        mul_lt_mul_of_pos_left hhalf hsign]
    · have hfac : ψ ^ 4 * φ = ψ ^ 2 * (-ψ) := by linear_combination ψ ^ 3 * hprod
      nlinarith [mul_lt_mul_of_pos_left he₁.2 hfour, mul_lt_mul_of_pos_left he₂.2 hfour,
        mul_lt_mul_of_pos_right hhalf (neg_pos.mpr hsneg)]
  have hv : value z = value l + value s := sum_zeckendorf_fib _
  have hd := next_error z
  rw [hv, Nat.cast_add] at hd
  have hdiff : (nextValue z : ℝ) - (nextValue l + nextValue s : ℕ) =
      err z - (err l + err s) := by
    rw [Nat.cast_add]
    linarith only [hd, next_error l, next_error s]
  have hlt : (nextValue z : ℝ) < (nextValue l + nextValue s : ℕ) + 1 := by linarith
  have hgt : ((nextValue l + nextValue s : ℕ) : ℝ) < nextValue z + 1 := by linarith
  exact le_antisymm (Nat.le_of_lt_succ (by exact_mod_cast hlt))
    (Nat.le_of_lt_succ (by exact_mod_cast hgt))

private theorem translate_value (l : List ℕ) (d : ℕ) :
    value (l.map (· + (d + 1))) = value l * fib d + nextValue l * fib (d + 1) := by
  induction l with
  | nil => simp [value, nextValue]
  | cons a l ih =>
    simp only [value, nextValue, List.map_cons, List.sum_cons] at *
    rw [← Nat.add_assoc a d 1, fib_add, ih]
    ring

-- Translate the indices down by d, normalize, and translate them back. The Fibonacci
-- addition formula expresses the translated value using exactly the two preserved coordinates.
private theorem high_sum {l s : List ℕ} {d : ℕ} (hl : l.IsZeckendorfRep)
    (hs : s.IsZeckendorfRep) (hlb : ∀ i ∈ l, d + 4 ≤ i) (hsb : ∀ i ∈ s, d + 4 ≤ i) :
    ∃ z : List ℕ, z.IsZeckendorfRep ∧ (∀ i ∈ z, d + 2 ≤ i) ∧ value z = value l + value s := by
  let lower (a : List ℕ) := a.map (· - d)
  let raise (a : List ℕ) := a.map (· + d)
  have lower_spec (a : List ℕ) (ha : a.IsZeckendorfRep) (hb : ∀ i ∈ a, d + 4 ≤ i) :
      (lower a).Pairwise Gap ∧ (∀ i ∈ lower a, 4 ≤ i) ∧ raise (lower a) = a := by
    refine ⟨List.pairwise_map.mpr ((rep_iff.mp ha).1.imp_of_mem ?_), ?_, ?_⟩
    · intro i j hi hj h
      have := hb i hi
      have := hb j hj
      unfold Gap at *
      omega
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      have := hb j hj
      omega
    · simp only [lower, raise, List.map_map]
      simpa using (List.map_congr_left (f := (· + d) ∘ (· - d)) (g := id)
        (l := a) fun i hi => Nat.sub_add_cancel (by have := hb i hi; omega))
  obtain ⟨pl, bl, el⟩ := lower_spec l hl hlb
  obtain ⟨ps, bs, es⟩ := lower_spec s hs hsb
  let a := zeckendorf (value (lower l) + value (lower s))
  have pa := rep_iff.mp (isZeckendorfRep_zeckendorf (value (lower l) + value (lower s)))
  have ba : ∀ i ∈ raise a, d + 2 ≤ i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := pa.2 j hj
    omega
  refine ⟨raise a, rep_iff.mpr ⟨List.pairwise_map.mpr (pa.1.imp (by unfold Gap; omega)),
    fun i hi => by have := ba i hi; omega⟩, ba, ?_⟩
  have hv : value a = value (lower l) + value (lower s) := sum_zeckendorf_fib _
  have hn := next_add pl ps bl bs
  change nextValue a = _ at hn
  rw [← el, ← es]
  change value (a.map (· + d)) = value ((lower l).map (· + d)) + value ((lower s).map (· + d))
  cases d with
  | zero => simpa using hv
  | succ d => simp only [translate_value, hv, hn]; ring

-- A single summand just below a tail can carry upwards through adjacent indices.
private theorem add_below {l : List ℕ} (hl : l.IsZeckendorfRep) {j : ℕ} (hj : 2 ≤ j)
    (hb : ∀ i ∈ l, j < i) :
    ∃ z : List ℕ, z.IsZeckendorfRep ∧ (∀ i ∈ z, j ≤ i) ∧ value z = value l + fib j := by
  induction l using List.reverseRecOn generalizing j with
  | nil =>
    exact ⟨[j], rep_cons hj List.IsZeckendorfRep_nil (by simp), by simp, by simp [value]⟩
  | append_singleton l a ih =>
    have hp := rep_iff.mp hl
    rw [List.pairwise_append] at hp
    have hprev (i : ℕ) (hi : i ∈ l) : a + 2 ≤ i := hp.1.2.2 i hi a (by simp)
    have hja := hb a (by simp)
    by_cases ha : a = j + 1
    · subst a
      have hl' := rep_iff.mpr ⟨hp.1.1, fun i hi => hp.2 i (by simp [hi])⟩
      obtain ⟨z, hz, hzb, hv⟩ := ih hl' (j := j + 2) (by omega)
        (fun i hi => by have := hprev i hi; omega)
      refine ⟨z, hz, fun i hi => by have := hzb i hi; omega, ?_⟩
      simp only [value, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero, fib_add_two] at hv ⊢
      omega
    · have hgap (i : ℕ) (hi : i ∈ l ++ [a]) : j + 2 ≤ i := by
        simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with hi | rfl
        · have := hprev i hi
          omega
        · omega
      refine ⟨(l ++ [a]) ++ [j], rep_append hl (rep_cons hj List.IsZeckendorfRep_nil (by simp))
        (by simpa using hgap), ?_, by simp [value, Nat.add_assoc]⟩
      simp only [List.mem_append, List.mem_singleton]
      grind only [List.mem_append, List.mem_singleton]

private theorem join_low {l : List ℕ} (hl : l.IsZeckendorfRep) {d u k : ℕ} (hd : 4 ≤ d)
    (hb : ∀ i ∈ l, d ≤ i) (hu : u < fib d) (hk : k + 2 ≤ d) :
    zeckAdicOfNat (value l + u) k = zeckAdicOfNat u k := by
  let s := zeckendorf u
  have hs := isZeckendorfRep_zeckendorf u
  have hsb (i : ℕ) (hi : i ∈ s) := mem_lt hu hi
  by_cases hm : d - 1 ∈ s
  · let t := s.filter (· ≠ d - 1)
    have ht := rep_filter hs (fun i => decide (i ≠ d - 1))
    have htb (i : ℕ) (hi : i ∈ t) : i + 2 ≤ d - 1 := by
      obtain ⟨him, hn⟩ := List.mem_filter.mp hi
      have hlt := hsb i him
      have hne := apart hs him
      simp only [decide_eq_true_eq] at hn
      by_contra! h
      have : i + 1 = d - 1 := by omega
      exact hne (this ▸ hm)
    have hls : (d - 1) :: t = s := by
      apply rep_ext (rep_cons (by omega) ht htb) hs
      intro i
      simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
      grind only
    obtain ⟨z, hz, hzb, hv⟩ := add_below hl (j := d - 1) (by omega)
      fun i hi => by have := hb i hi; omega
    have hz' := rep_append hz ht fun i hi j hj => (htb j hj).trans (hzb i hi)
    have hu' : fib (d - 1) + value t = u := by
      change value ((d - 1) :: t) = u
      rw [hls]
      exact sum_zeckendorf_fib u
    have he : value (z ++ t) = value l + u := by
      rw [show value (z ++ t) = value z + value t by simp [value], hv]
      omega
    rw [← he, ofNat_value hz']
    have hn : k ∉ z := fun h => by have := hzb k h; omega
    simp [hn, zeckAdicOfNat, show k ≠ d - 1 by omega]
  · have hz := rep_append hl hs fun i hi j hj => by
      have := hb i hi
      have := hsb j hj
      have : j ≠ d - 1 := fun h => hm (h ▸ hj)
      omega
    have he : value (l ++ s) = value l + u := by simp [value, s]
    rw [← he, ofNat_value hz]
    have hn : k ∉ l := fun h => by have := hb k h; omega
    simp [hn, zeckAdicOfNat]

/-! ### Splitting the shift at the block -/

private def block (ℓ : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (ℓ + 2 * n + 3) :: block ℓ n

private theorem mem_block {ℓ n j : ℕ} :
    j ∈ block ℓ n ↔ ∃ i < n, j = ℓ + 2 * i + 3 := by
  induction n with
  | zero => simp [block]
  | succ n ih =>
    simp only [block, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi, he⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, he⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | h
      · exact Or.inl rfl
      · exact Or.inr ⟨i, h, rfl⟩

private theorem block_rep (ℓ n : ℕ) : (block ℓ n).IsZeckendorfRep := by
  induction n with
  | zero => exact List.IsZeckendorfRep_nil
  | succ n ih =>
    apply rep_cons (by omega) ih
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_block.mp hj
    omega

private theorem block_value (ℓ n : ℕ) :
    value (block ℓ n) = ∑ i ∈ Finset.range n, fib (ℓ + 2 * i + 3) := by
  induction n with
  | zero => simp [block, value]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.add_comm (value _)]
    rfl

private abbrev lowPart (r ℓ : ℕ) := (zeckendorf r).filter (· ≤ ℓ)
private abbrev highPart (r d : ℕ) := (zeckendorf r).filter (d + 4 ≤ ·)

private theorem split_shift {ℓ m r : ℕ} (hr1 : ℓ + 1 ∉ zeckendorf r)
    (hr7 : ℓ + 2 * m + 7 ∉ zeckendorf r)
    (hrb : ∀ i ≤ m + 1, ℓ + 2 * i + 3 ∈ zeckendorf r) :
    let d := ℓ + 2 * m + 4
    highPart r d ++ (block ℓ (m + 2) ++ lowPart r ℓ) = zeckendorf r := by
  intro d
  have hr := isZeckendorfRep_zeckendorf r
  have hl (i : ℕ) (hi : i ∈ lowPart r ℓ) : i ≤ ℓ := of_decide_eq_true (List.mem_filter.mp hi).2
  have hh (i : ℕ) (hi : i ∈ highPart r d) : d + 4 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
  have hb := rep_append (block_rep ℓ (m + 2)) (rep_filter hr (· ≤ ℓ)) fun i hi j hj => by
    obtain ⟨a, ha, rfl⟩ := mem_block.mp hi
    have := hl j hj
    omega
  apply rep_ext (rep_append (rep_filter hr _) hb fun i hi j hj => ?_) hr
  · intro i
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq, mem_block]
    constructor
    · rintro (⟨h, -⟩ | ⟨a, ha, rfl⟩ | ⟨h, -⟩)
      · exact h
      · exact hrb a (by omega)
      · exact h
    · intro hi
      by_cases hhigh : d + 4 ≤ i
      · exact Or.inl ⟨hi, hhigh⟩
      by_cases hlow : i ≤ ℓ
      · exact Or.inr (Or.inr ⟨hi, hlow⟩)
      right
      left
      have ha1 : i ≠ ℓ + 1 := fun h => hr1 (h ▸ hi)
      have ha7 : i ≠ ℓ + 2 * m + 7 := fun h => hr7 (h ▸ hi)
      have hn := apart hr hi
      have hfirst := hrb 0 (by omega)
      have hi2 : i ≠ ℓ + 2 := by
        intro he
        exact hn (by simpa [he] using hfirst)
      let a := (i - (ℓ + 3)) / 2
      have hab : a ≤ m + 1 := by dsimp [a, d] at *; omega
      have hna := apart hr (hrb a hab)
      refine ⟨a, by omega, ?_⟩
      by_contra! hne
      have : ℓ + 2 * a + 3 + 1 = i := by dsimp [a]; omega
      exact hna (this ▸ hi)
  · have := hh i hi
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨a, ha, rfl⟩ := mem_block.mp hj
      dsimp [d] at *
      omega
    · have := hl j hj
      dsimp [d] at *
      omega

private theorem split_input {v d : ℕ} (hzero : ∀ i, d ≤ i → i < d + 4 → i ∉ zeckendorf v) :
    highPart v d ++ ((zeckendorf v).filter (· < d)) = zeckendorf v := by
  have hv := isZeckendorfRep_zeckendorf v
  apply rep_ext (rep_append (rep_filter hv _) (rep_filter hv _) ?_) hv
  · intro i
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    grind only
  · intro i hi j hj
    have hi' : d + 4 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
    have hj' : j < d := of_decide_eq_true (List.mem_filter.mp hj).2
    omega

private theorem upper_digits {l : List ℕ} (hl : l.IsZeckendorfRep) {d u : ℕ}
    (hb : ∀ i ∈ l, d + 4 ≤ i) (hu : u < fib (d + 3)) {k : ℕ} (hk : d + 3 ≤ k) :
    zeckAdicOfNat (value l + u) k = decide (k ∈ l) := by
  have h := rep_append hl (isZeckendorfRep_zeckendorf u) fun i hi j hj => by
    have := hb i hi
    have := mem_lt hu hj
    omega
  have hv : value (l ++ zeckendorf u) = value l + u := by simp [value]
  rw [← hv, ofNat_value h]
  have hn : k ∉ zeckendorf u := fun hi => (mem_lt hu hi).not_ge hk
  simp [hn]

-- The greatest index of the lower sum is d + 1 or d + 2. Removing that digit
-- leaves a value below F_d in either case.
private theorem lower_digits {l s : List ℕ} (hl : l.IsZeckendorfRep) (hs : s.IsZeckendorfRep)
    {d A k : ℕ} (hd : 4 ≤ d) (hlb : ∀ i ∈ l, d + 4 ≤ i) (hsb : ∀ i ∈ s, d + 4 ≤ i)
    (hA : fib (d + 1) ≤ A) (hA' : A < fib (d + 2) + fib d) (hk : k + 2 ≤ d) :
    zeckAdicOfNat (value l + value s + A) k = zeckAdicOfNat (value l + A) k := by
  obtain ⟨z, hz, hzb, hv⟩ := high_sum hl hs hlb hsb
  suffices ∃ j, (j = d + 1 ∨ j = d + 2) ∧ fib j ≤ A ∧ A - fib j < fib d by
    obtain ⟨j, hj, hjA, hrem⟩ := this
    obtain ⟨w, hw, hwb, he⟩ : ∃ w : List ℕ, w.IsZeckendorfRep ∧ (∀ i ∈ w, d ≤ i) ∧
        value w = value z + fib j := by
      rcases hj with rfl | rfl
      · obtain ⟨w, hw, hb, he⟩ := add_below hz (j := d + 1) (by omega)
          fun i hi => by have := hzb i hi; omega
        exact ⟨w, hw, fun i hi => by have := hb i hi; omega, he⟩
      · have hsing := rep_cons (a := d + 2) (by omega) List.IsZeckendorfRep_nil (by simp)
        obtain ⟨w, hw, hb, he⟩ := high_sum (d := d - 2) hz hsing
          (fun i hi => by have := hzb i hi; omega) (by simp; omega)
        exact ⟨w, hw, fun i hi => by have := hb i hi; omega, by simpa [value] using he⟩
    have hjb : d ≤ j ∧ j ≤ d + 2 := by omega
    let t := l ++ [j]
    have ht : t.IsZeckendorfRep := rep_append hl
      (rep_cons (by omega) List.IsZeckendorfRep_nil (by simp))
      (by simpa using fun i hi => show j + 2 ≤ i by have := hlb i hi; omega)
    have htb (i : ℕ) (hi : i ∈ t) : d ≤ i := by
      obtain h | h := List.mem_append.mp hi
      · have := hlb i h
        omega
      · simp only [List.mem_singleton] at h
        omega
    have het : value t = value l + fib j := by simp [t, value]
    have hw' := join_low hw hd hwb hrem hk
    have ht' := join_low ht hd htb hrem hk
    rw [show value l + value s + A = value w + (A - fib j) by omega,
        show value l + A = value t + (A - fib j) by omega]
    exact hw'.trans ht'.symm
  by_cases hb : A < fib (d + 2)
  · refine ⟨d + 1, Or.inl rfl, hA, ?_⟩
    rw [fib_add_two] at hb
    omega
  · exact ⟨d + 2, Or.inr rfl, by omega, by omega⟩

private theorem finite_block {ℓ m r v : ℕ} (hr1 : ℓ + 1 ∉ zeckendorf r)
    (hr7 : ℓ + 2 * m + 7 ∉ zeckendorf r)
    (hrb : ∀ i ≤ m + 1, ℓ + 2 * i + 3 ∈ zeckendorf r) :
    let d := ℓ + 2 * m + 4
    let rt := value (lowPart r ℓ)
    let S := value (block ℓ (m + 2))
    (∀ i, d ≤ i → i < d + 4 → i ∉ zeckendorf v) →
    (∀ k, d + 3 ≤ k → zeckAdicOfNat (v + (rt + S)) k = zeckAdicOfNat (v + rt) k ∧
      zeckAdicOfNat (v + rt) k = zeckAdicOfNat v k) ∧
      ∀ k, k + 2 ≤ d → zeckAdicOfNat (v + r) k = zeckAdicOfNat (v + (rt + S)) k := by
  intro d rt S hzero
  let l := highPart v d
  let s := highPart r d
  let b := (zeckendorf v).filter (· < d)
  let A := value b + (rt + S)
  have hl := rep_filter (isZeckendorfRep_zeckendorf v) (d + 4 ≤ ·)
  have hs := rep_filter (isZeckendorfRep_zeckendorf r) (d + 4 ≤ ·)
  have hbound (n i : ℕ) (hi : i ∈ highPart n d) : d + 4 ≤ i :=
    of_decide_eq_true (List.mem_filter.mp hi).2
  have hv : value l + value b = v := by
    have := congrArg value (split_input hzero)
    simpa only [value, List.map_append, List.sum_append, sum_zeckendorf_fib] using this
  have hr : value s + (S + rt) = r := by
    have := congrArg value (split_shift hr1 hr7 hrb)
    simpa only [value, List.map_append, List.sum_append, sum_zeckendorf_fib] using this
  have hb : value b < fib d := value_lt (rep_filter (isZeckendorfRep_zeckendorf v) _) (by
    dsimp [d]; omega) fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2
  have hrep := rep_append (block_rep ℓ (m + 2))
    (rep_filter (isZeckendorfRep_zeckendorf r) (· ≤ ℓ)) fun i hi j hj => by
      obtain ⟨a, _, rfl⟩ := mem_block.mp hi
      have h : j ≤ ℓ := of_decide_eq_true (List.mem_filter.mp hj).2
      omega
  have hshift : rt + S < fib (d + 2) := by
    have hlt := value_lt hrep (n := d + 2) (by omega) fun i hi => by
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨a, ha, rfl⟩ := mem_block.mp hi
        dsimp [d]
        omega
      · have h : i ≤ ℓ := of_decide_eq_true (List.mem_filter.mp hi).2
        dsimp [d]
        omega
    change value ((block ℓ (m + 2)) ++ lowPart r ℓ) < _ at hlt
    simpa only [value, List.map_append, List.sum_append, Nat.add_comm] using hlt
  have hA : fib (d + 1) ≤ A := by
    have hmem : d + 1 ∈ block ℓ (m + 2) :=
      mem_block.mpr ⟨m + 1, by omega, by dsimp [d]; omega⟩
    have hle : fib (d + 1) ≤ S := List.le_sum_of_mem (List.mem_map_of_mem (f := fib) hmem)
    dsimp only [A]
    omega
  have hA' : A < fib (d + 2) + fib d := by dsimp only [A]; omega
  have hsmall : A < fib (d + 3) := by
    rw [fib_add_two (n := d + 1)]
    change A < fib (d + 1) + fib (d + 2)
    have : fib d ≤ fib (d + 1) := fib_mono (Nat.le_succ d)
    omega
  constructor
  · intro k hk
    have h₁ := upper_digits hl (hbound v) hsmall hk
    have h₂ := upper_digits hl (hbound v) (u := value b + rt)
      (by dsimp only [A] at hsmall; omega) hk
    have h₃ := upper_digits hl (hbound v) (u := value b) (by dsimp only [A] at hsmall; omega) hk
    change zeckAdicOfNat (value l + A) k = _ at h₁
    change zeckAdicOfNat (value l + (value b + rt)) k = _ at h₂
    change zeckAdicOfNat (value l + value b) k = _ at h₃
    rw [show value l + A = v + (rt + S) by dsimp only [A]; omega] at h₁
    rw [← Nat.add_assoc, hv] at h₂
    rw [hv] at h₃
    exact ⟨h₁.trans h₂.symm, h₂.trans h₃.symm⟩
  · intro k hk
    have h := lower_digits hl hs (by dsimp [d]; omega) (hbound v) (hbound r) hA hA' hk
    change zeckAdicOfNat (value l + value s + A) k = zeckAdicOfNat (value l + A) k at h
    dsimp only [A] at h
    rwa [show value l + value s + (value b + (rt + S)) = v + r by omega,
      show value l + (value b + (rt + S)) = v + (rt + S) by omega] at h

private theorem low_add {v r ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    (hℓ0 : ℓ ∉ Nat.zeckendorf v) (hℓ1 : ℓ + 1 ∉ Nat.zeckendorf v)
    (hr : ∀ j, 2 ≤ j → j ≤ ℓ + 1 → j ∉ Nat.zeckendorf r)
    {k : ℕ} (hk : k + 2 ≤ ℓ) :
    zeckAdicOfNat (v + r) k = zeckAdicOfNat v k := by
  have hvrep := isZeckendorfRep_zeckendorf v
  have hrrep := isZeckendorfRep_zeckendorf r
  have hge (i : ℕ) (hi : i ∈ Nat.zeckendorf r) : ℓ + 2 ≤ i := by
    have hi2 := (rep_iff.mp hrrep).2 i hi
    by_contra hc
    have hlt : i < ℓ + 2 := Nat.not_le.mp hc
    exact hr i hi2 (by omega) hi
  have hlow (i : ℕ) (hi : i ∈ Nat.zeckendorf v) : i < ℓ ∨ ℓ + 2 ≤ i := by
    have hi2 := (rep_iff.mp hvrep).2 i hi
    rcases lt_trichotomy i ℓ with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hi) hℓ0
    · have h' : i = ℓ + 1 ∨ ℓ + 2 ≤ i := by omega
      rcases h' with h' | h'
      · exact absurd (h' ▸ hi) hℓ1
      · exact Or.inr h'
  let lv := (Nat.zeckendorf v).filter (· < ℓ)
  let hv := (Nat.zeckendorf v).filter (ℓ + 2 ≤ ·)
  have hlvrep : lv.IsZeckendorfRep := rep_filter hvrep _
  have hhvrep : hv.IsZeckendorfRep := rep_filter hvrep _
  have hsplit : hv ++ lv = Nat.zeckendorf v := by
    refine rep_ext (rep_append hhvrep hlvrep fun a ha b hb => ?_) hvrep ?_
    · have ha' : ℓ + 2 ≤ a := of_decide_eq_true (List.mem_filter.mp ha).2
      have hb' : b < ℓ := of_decide_eq_true (List.mem_filter.mp hb).2
      omega
    · intro i
      constructor
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact (List.mem_filter.mp h).1
        · exact (List.mem_filter.mp h).1
      · intro h
        rcases hlow i h with hlt | hge'
        · exact List.mem_append.mpr (Or.inr
            (List.mem_filter.mpr ⟨h, by simp only [decide_eq_true_eq]; exact hlt⟩))
        · exact List.mem_append.mpr (Or.inl
            (List.mem_filter.mpr ⟨h, by simp only [decide_eq_true_eq]; exact hge'⟩))
  have hval : value hv + value lv = v := by
    have h := congrArg value hsplit
    simpa only [value, List.map_append, List.sum_append, sum_zeckendorf_fib] using h
  have hlvlt : value lv < Nat.fib ℓ :=
    value_lt hlvrep (by omega) fun i hi =>
      of_decide_eq_true (List.mem_filter.mp hi).2
  obtain ⟨z, hzrep, hzb, hzv⟩ := high_sum (d := ℓ - 2) hhvrep hrrep
    (fun i hi => by
      have hi' : ℓ + 2 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
      omega)
    (fun i hi => by have := hge i hi; omega)
  have hzlo : ∀ i ∈ z, ℓ ≤ i := fun i hi => by have := hzb i hi; omega
  have hjoinV : zeckAdicOfNat (value hv + value lv) k = zeckAdicOfNat (value lv) k :=
    join_low hhvrep hℓ
      (fun i hi => by
        have hi' : ℓ + 2 ≤ i := of_decide_eq_true (List.mem_filter.mp hi).2
        omega)
      hlvlt hk
  have hjoinR : zeckAdicOfNat (value z + value lv) k = zeckAdicOfNat (value lv) k :=
    join_low hzrep hℓ hzlo hlvlt hk
  have hvr : v + r = value z + value lv := by
    have hrval : value (Nat.zeckendorf r) = r := sum_zeckendorf_fib r
    omega
  rw [hvr, ← hval]
  exact hjoinR.trans hjoinV.symm

end zeckOdometer_stopping_block

open zeckOdometer_stopping_block in
set_option linter.unusedVariables false in
/-- **Stopping condition for a block of size $m + 2$.** Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$, $\ell \ge 2$ and $m \in \mathbb{N}$ with $x_i = 0$ for
$i \in \{\ell, \ell+1, \ell+2, \ell+3, \ell+2m+4, \ell+2m+5, \ell+2m+6, \ell+2m+7\}$, and let
$r$ satisfy $r_{\ell+1} = r_{\ell+2m+7} = 0$ and $r_{\ell+2i+3} = 1$ for $i = 0, \dots, m+1$.
Let $\tilde r = \sum_{j \in Z(r),\, j \le \ell} F_j$ be the part of $r$ of index at most $\ell$,
and let $S = \sum_{i=0}^{m+1} F_{\ell+2i+3}$. Then
$(x + \tilde r + S)_k = (x + \tilde r)_k = x_k$ for every $k \ge \ell + 2m + 7$, and
$(x + r)_k = (x + \tilde r + S)_k$ for every $k$ with $2 \le k \le \ell + 2m + 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 14 (`jis-2024-24.3.2-cor-14`). -/
public theorem zeckOdometer_stopping_block {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ m r : ℕ} (hℓ : 2 ≤ ℓ)
    (hx0 : ∀ i ∈ ({ℓ, ℓ + 1, ℓ + 2, ℓ + 3, ℓ + 2 * m + 4, ℓ + 2 * m + 5, ℓ + 2 * m + 6,
      ℓ + 2 * m + 7} : Finset ℕ), x i = false)
    (hr1 : ℓ + 1 ∉ Nat.zeckendorf r) (hr7 : ℓ + 2 * m + 7 ∉ Nat.zeckendorf r)
    (hrb : ∀ i ≤ m + 1, ℓ + 2 * i + 3 ∈ Nat.zeckendorf r) :
    let rt := (((Nat.zeckendorf r).filter (· ≤ ℓ)).map Nat.fib).sum
    let S := ∑ i ∈ Finset.range (m + 2), Nat.fib (ℓ + 2 * i + 3)
    (∀ k, ℓ + 2 * m + 7 ≤ k → zeckOdometer^[rt + S] x k = zeckOdometer^[rt] x k ∧
        zeckOdometer^[rt] x k = x k) ∧
      ∀ k, 2 ≤ k → k ≤ ℓ + 2 * m + 2 → zeckOdometer^[r] x k = zeckOdometer^[rt + S] x k := by
  let d := ℓ + 2 * m + 4
  intro rt S
  have hS : S = value (block ℓ (m + 2)) := (block_value _ _).symm
  suffices ∀ k, (d + 3 ≤ k → zeckOdometer^[rt + S] x k = zeckOdometer^[rt] x k ∧
      zeckOdometer^[rt] x k = x k) ∧
      (k + 2 ≤ d → zeckOdometer^[r] x k = zeckOdometer^[rt + S] x k) by
    exact ⟨fun k hk => (this k).1 (by dsimp [d]; omega),
      fun k _ hk => (this k).2 (by dsimp [d]; omega)⟩
  intro k
  let N := k + r + rt + S + 1
  let v := value (digits x N)
  have hrep := digits_rep hx N
  have hpre (i : ℕ) (hi : i < N) : zeckAdicOfNat v i = x i := by
    change zeckAdicOfNat (value (digits x N)) i = x i
    rw [ofNat_value hrep]
    apply Bool.eq_iff_iff.mpr
    simp [mem_digits, hi]
  have hzero (i : ℕ) (hi : d ≤ i) (hi' : i < d + 4) : i ∉ Nat.zeckendorf v := by
    change i ∉ Nat.zeckendorf (value (digits x N))
    rw [Nat.zeckendorf_sum_fib hrep, mem_digits]
    have he : i = d ∨ i = d + 1 ∨ i = d + 2 ∨ i = d + 3 := by omega
    have hz := hx0 i (by rcases he with rfl | rfl | rfl | rfl <;> simp [d, Nat.add_assoc])
    simp [hz]
  have hf := finite_block hr1 hr7 hrb hzero
  change (∀ j, d + 3 ≤ j →
    zeckAdicOfNat (v + (rt + value (block ℓ (m + 2)))) j = zeckAdicOfNat (v + rt) j ∧
    zeckAdicOfNat (v + rt) j = zeckAdicOfNat v j) ∧ _ at hf
  rw [← hS] at hf
  have hit (a : ℕ) (ha : k + a < N) : zeckOdometer^[a] x k = zeckAdicOfNat (v + a) k := by
    rw [← ofNat_iterate]
    exact iterate_local a k fun i hi => (hpre i (by omega)).symm
  rw [hit (rt + S) (by dsimp [N]; omega), hit rt (by dsimp [N]; omega),
    hit r (by dsimp [N]; omega), ← hpre k (by dsimp [N]; omega)]
  exact ⟨hf.1 k, hf.2 k⟩

open zeckOdometer_stopping_block in
/-- **Adding $r$ without low digits leaves the low digits unchanged.** Write $F_j$ for the
Fibonacci numbers ($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in
the Zeckendorf representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two
consecutive), and let $r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), and write $x + n = T^n(x)$ for the $n$-th
iterate of the Zeckendorf odometer $T$. Let $x \in \mathbb{X}$ and $\ell \ge 2$ with
$x_\ell = x_{\ell+1} = 0$, and let $r$ satisfy $r_j = 0$ for $2 \le j \le \ell + 1$. Then
$(x + r)_n = x_n$ for every $n$ with $2 \le n \le \ell - 2$.

Source: Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation:
An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27
(2024), Article 24.3.2, Corollary 9 (`jis-2024-24.3.2-cor-9`). -/
public theorem zeckOdometer_iterate_low_digits {x : ℕ → Bool} (hx : x ∈ zeckAdic)
    {ℓ r : ℕ} (hℓ : 2 ≤ ℓ) (hx0 : x ℓ = false) (hx1 : x (ℓ + 1) = false)
    (hr : ∀ j, 2 ≤ j → j ≤ ℓ + 1 → j ∉ Nat.zeckendorf r) :
    ∀ n, 2 ≤ n → n ≤ ℓ - 2 → zeckOdometer^[r] x n = x n := by
  intro n hn2 hnℓ
  have hℓ4 : 4 ≤ ℓ := by omega
  let N := n + r + ℓ + 3
  let v := value (digits x N)
  have hrep := digits_rep hx N
  have hpre (i : ℕ) (hi : i < N) : zeckAdicOfNat v i = x i := by
    change zeckAdicOfNat (value (digits x N)) i = x i
    rw [ofNat_value hrep]
    apply Bool.eq_iff_iff.mpr
    simp [mem_digits, hi]
  have hℓ0 : ℓ ∉ Nat.zeckendorf v := by
    have h := hpre ℓ (by dsimp [N]; omega)
    rw [hx0] at h
    exact of_decide_eq_false h
  have hℓ1 : ℓ + 1 ∉ Nat.zeckendorf v := by
    have h := hpre (ℓ + 1) (by dsimp [N]; omega)
    rw [hx1] at h
    exact of_decide_eq_false h
  have hpre' : ∀ i ≤ n + r, x i = zeckAdicOfNat v i :=
    fun i hi => (hpre i (by dsimp [N]; omega)).symm
  calc zeckOdometer^[r] x n = zeckOdometer^[r] (zeckAdicOfNat v) n :=
        iterate_local r n hpre'
    _ = zeckAdicOfNat (v + r) n := by rw [ofNat_iterate]
    _ = zeckAdicOfNat v n := low_add hℓ4 hℓ0 hℓ1 hr (by omega)
    _ = x n := hpre n (by dsimp [N]; omega)

end MetaMathlibExt
