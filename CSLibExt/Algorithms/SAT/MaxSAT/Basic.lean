/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# MAX-SAT: the one-half and seven-eighths bounds

Averaging over all `2 ^ n` assignments of `n` Boolean variables: a nonempty
clause is satisfied by at least half of them, and a clause with three literals
on three distinct variables by `7 / 8` of them. Summing over the clauses of a
formula gives an assignment satisfying at least that fraction of the clauses.

## Representation

* Clauses are finsets of literals `Lit n = Fin n × Bool` over the variables
  `Fin n`; `clauseSat x c` says that `x` satisfies some literal of `c`.
* A formula is an indexed family `F : ι → Finset (Lit n)` over a finset `s` of
  indices, so a clause occurring at several indices counts once per occurrence,
  as in the MAX-SAT objective. `max_sat_half` and `max_e3sat_seven_eighths` are
  stated this way.
* `max_sat_half_finset` and `max_e3sat_seven_eighths_finset` are the special
  case of a duplicate-free formula, given as a finset of clauses.
* `cnf_max_sat_half` and `cnf_max_e3sat_seven_eighths` state the bounds for the
  canonical formulas `Cslib.Logic.PL.CNF` (lists of clauses, so repeated
  clauses are kept) under the canonical semantics
  `Cslib.Logic.PL.CNFClause.Satisfies`, counting satisfied clause positions.
-/

@[expose] public section

namespace Cslib.Algorithms.SAT.MaxSAT

open Cslib.Logic.PL

/-- A literal over variables `Fin n`: `(var, positive)`. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- An assignment satisfies a clause, a finset of literals, if it satisfies
some literal in it. -/
def clauseSat {n : ℕ} (x : Fin n → Bool) (c : Finset (Lit n)) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

noncomputable instance {n : ℕ} (x : Fin n → Bool) (c : Finset (Lit n)) :
    Decidable (clauseSat x c) :=
  Classical.propDecidable _

private lemma card_univ_fun_bool (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma double_count {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Finset (Lit n)) :
    (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((s.filter (fun i => clauseSat x (F i))).card : ℝ)) =
    ∑ i ∈ s, ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x (F i))).card : ℝ)) := by
  have h1 : ∀ x : Fin n → Bool,
      ((s.filter (fun i => clauseSat x (F i))).card : ℝ) =
      ∑ i ∈ s, (if clauseSat x (F i) then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.card_filter]
    push_cast
    rfl
  have h2 : ∀ i : ι,
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x (F i))).card : ℝ)) =
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
        (if clauseSat x (F i) then (1 : ℝ) else 0) := by
    intro i
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [h1, h2]
  exact Finset.sum_comm

private lemma bool_ne_iff {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

private lemma bool_eq_of_ne_not {a b : Bool} (h : ¬ (a = !b)) : a = b := by
  cases a <;> cases b <;> simp_all

private lemma bool_not_eq_not_self {b : Bool} (h : b = !b) : False := by
  cases b <;> simp_all

private lemma sat_ge_half_per_clause {n : ℕ} {c : Finset (Lit n)}
    (hc : c.Nonempty) :
    (1 / 2 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℝ)) := by
  obtain ⟨l0, hl0⟩ := hc
  let flip : (Fin n → Bool) → (Fin n → Bool) :=
    fun x => Function.update x l0.1 (!x l0.1)
  have hflip_inv : ∀ x, flip (flip x) = x := by
    intro x
    apply funext
    intro i
    by_cases hi : i = l0.1
    · subst hi
      simp [flip, Function.update_self]
    · simp [flip, hi]
  have hflip_inj : Function.Injective flip := by
    intro x y hxy
    have h := congrArg flip hxy
    rw [hflip_inv, hflip_inv] at h
    exact h
  have hmaps : Set.MapsTo flip
      ↑((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => ¬ clauseSat x c))
      ↑((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    have hne : x l0.1 ≠ l0.2 := fun heq => hx ⟨l0, hl0, heq⟩
    have hxeq : x l0.1 = !l0.2 := bool_ne_iff hne
    exact ⟨l0, hl0, by simp [flip, Function.update_self, hxeq]⟩
  have hinj : Set.InjOn flip
      ↑((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => ¬ clauseSat x c)) := by
    intro x _ y _ hxy
    exact hflip_inj hxy
  have hle : (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card) ≤
      (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card) :=
    Finset.card_le_card_of_injOn flip hmaps hinj
  have hcard : (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card) +
      (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card) =
      ((Finset.univ : Finset (Fin n → Bool)).card) :=
    Finset.card_filter_add_card_filter_not _
  have huniv : (((Finset.univ : Finset (Fin n → Bool)).card : ℕ) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hcardR : ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card : ℕ) : ℝ) +
      ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
      (2 : ℝ) ^ n := by
    have h : ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card +
        ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
        ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) := by
      exact_mod_cast hcard
    rw [Nat.cast_add] at h
    rw [h, huniv]
  have hleR : ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card : ℕ) : ℝ) := by
    exact_mod_cast hle
  linarith

private def forced {n : ℕ} (c : Finset (Lit n)) (v : Fin n) : Bool :=
  decide ((v, false) ∈ c)

private lemma forced_eq {n : ℕ} {c : Finset (Lit n)}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n)))
    {l : Lit n} (hl : l ∈ c) :
    forced c l.1 = !l.2 := by
  obtain ⟨v, p⟩ := l
  simp only at hl ⊢
  cases p
  · simp [forced, hl]
  · have hne : (v, false) ∉ c := by
      intro hmem
      have h1 : (v, true) ∈ (↑c : Set (Lit n)) := Finset.mem_coe.mpr hl
      have h2 : (v, false) ∈ (↑c : Set (Lit n)) := Finset.mem_coe.mpr hmem
      have heq := hInj h1 h2 rfl
      simp at heq
    simp [forced, hne]

private lemma not_sat_iff {n : ℕ} {x : Fin n → Bool}
    {c : Finset (Lit n)} :
    ¬ clauseSat x c ↔ ∀ l ∈ c, x l.1 = !l.2 := by
  constructor
  · intro hnsat l hl
    by_contra hne
    have hEq : x l.1 = l.2 := bool_eq_of_ne_not hne
    exact hnsat ⟨l, hl, hEq⟩
  · intro hall hsat
    obtain ⟨l, hl, heq⟩ := hsat
    have hfall := hall l hl
    rw [heq] at hfall
    exact bool_not_eq_not_self hfall

private lemma vars_card {n : ℕ} {c : Finset (Lit n)}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    (c.image (fun l : Lit n => l.1)).card = c.card :=
  Finset.card_image_of_injOn hInj

private lemma card_le_of_injOn {n : ℕ} {c : Finset (Lit n)}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    c.card ≤ n := by
  have hvars := Finset.card_image_of_injOn (s := c)
    (f := fun l : Lit n => l.1) hInj
  have hle : (c.image (fun l : Lit n => l.1)).card ≤
      ((Finset.univ : Finset (Fin n)).card) :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

private lemma prod_eq_indicator {n : ℕ} (c : Finset (Lit n))
    (x : Fin n → Bool) :
    (∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
      then (if x v = forced c v then (1 : ℝ) else 0) else 1)) =
    (if ∀ v ∈ c.image (fun l : Lit n => l.1), x v = forced c v
      then (1 : ℝ) else 0) := by
  by_cases h : ∀ v ∈ c.image (fun l : Lit n => l.1), x v = forced c v
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro v _
    by_cases hv : v ∈ c.image (fun l : Lit n => l.1)
    · simp [hv, h v hv]
    · simp [hv]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨v0, hv0mem, hv0ne⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ v0)
    simp [hv0mem, hv0ne]

private lemma forall_vars_iff {n : ℕ} {c : Finset (Lit n)}
    {x : Fin n → Bool}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    ((∀ v ∈ c.image (fun l : Lit n => l.1), x v = forced c v) ↔
      (∀ l ∈ c, x l.1 = !l.2)) := by
  constructor
  · intro hall l hl
    have hmem : l.1 ∈ c.image (fun l : Lit n => l.1) :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    have hx := hall l.1 hmem
    rw [forced_eq hInj hl] at hx
    exact hx
  · intro hall v hv
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
    rw [forced_eq hInj hl]
    exact hall l hl

private lemma prod_eq_falsify {n : ℕ} {c : Finset (Lit n)}
    {x : Fin n → Bool}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    (∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
      then (if x v = forced c v then (1 : ℝ) else 0) else 1)) =
    (if ¬ clauseSat x c then (1 : ℝ) else 0) := by
  have hiff : (∀ v ∈ c.image (fun l : Lit n => l.1),
      x v = forced c v) ↔ ¬ clauseSat x c :=
    (forall_vars_iff hInj).trans not_sat_iff.symm
  rw [prod_eq_indicator]
  simp only [hiff]

private lemma sum_prod_eq_falsify_card {n : ℕ} {c : Finset (Lit n)}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    (∑ x : Fin n → Bool, ∏ v : Fin n, (if v ∈ c.image
      (fun l : Lit n => l.1)
      then (if x v = forced c v then (1 : ℝ) else 0) else 1)) =
    ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) := by
  have h1 : ∀ x : Fin n → Bool,
      (∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
        then (if x v = forced c v then (1 : ℝ) else 0) else 1)) =
      (if ¬ clauseSat x c then (1 : ℝ) else 0) :=
    fun x => prod_eq_falsify hInj
  simp only [h1]
  have h2 : ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
        (if ¬ clauseSat x c then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    rfl
  exact h2.symm

private lemma factorize {n : ℕ} (c : Finset (Lit n)) :
    (∑ x : Fin n → Bool, ∏ v : Fin n, (if v ∈ c.image
      (fun l : Lit n => l.1)
      then (if x v = forced c v then (1 : ℝ) else 0) else 1)) =
    ∏ v : Fin n, ∑ b : Bool, (if v ∈ c.image (fun l : Lit n => l.1)
      then (if b = forced c v then (1 : ℝ) else 0) else 1) :=
  (Fintype.prod_sum (fun v : Fin n => fun b : Bool =>
    (if v ∈ c.image (fun l : Lit n => l.1)
      then (if b = forced c v then (1 : ℝ) else 0) else 1))).symm

private lemma per_var_sum {n : ℕ} (c : Finset (Lit n)) (v : Fin n) :
    (∑ b : Bool, (if v ∈ c.image (fun l : Lit n => l.1)
      then (if b = forced c v then (1 : ℝ) else 0) else 1)) =
    (if v ∈ c.image (fun l : Lit n => l.1) then (1 : ℝ) else 2) := by
  by_cases hv : v ∈ c.image (fun l : Lit n => l.1)
  · simp [hv]
  · simp [hv]

private lemma prod_vars_eq_pow {n : ℕ} (c : Finset (Lit n))
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    (∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
      then (1 : ℝ) else 2)) =
    (2 : ℝ) ^ (n - c.card) := by
  have hEq : ∀ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
      then (1 : ℝ) else 2) =
      (if v ∉ c.image (fun l : Lit n => l.1) then 2 else 1) := by
    intro v
    by_cases hv : v ∈ c.image (fun l : Lit n => l.1)
    · simp [hv]
    · simp [hv]
  have hP1 : (∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
      then (1 : ℝ) else 2)) =
      ∏ v : Fin n, (if v ∉ c.image (fun l : Lit n => l.1)
        then (2 : ℝ) else 1) := by
    apply Finset.prod_congr rfl
    intro v _
    exact hEq v
  rw [hP1]
  have hP2 : (∏ v : Fin n, (if v ∉ c.image (fun l : Lit n => l.1)
      then (2 : ℝ) else 1)) =
      ∏ _v ∈ (Finset.univ : Finset (Fin n)).filter
        (fun v => v ∉ c.image (fun l : Lit n => l.1)), (2 : ℝ) := by
    rw [← Finset.prod_filter]
  rw [hP2, Finset.prod_const]
  have hcard : (((Finset.univ : Finset (Fin n)).filter
      (fun v => v ∉ c.image (fun l : Lit n => l.1))).card) =
      n - c.card := by
    have hcomp := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (fun v => v ∈ c.image (fun l : Lit n => l.1))
    have hfilter_eq : (Finset.univ : Finset (Fin n)).filter
        (fun v => v ∈ c.image (fun l : Lit n => l.1)) =
        c.image (fun l : Lit n => l.1) := by
      apply Finset.ext
      intro v
      simp
    have hvars := vars_card hInj
    have huniv : ((Finset.univ : Finset (Fin n)).card) = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hfilter_eq, hvars, huniv] at hcomp
    omega
  rw [hcard]

private lemma falsify_card_real {n : ℕ} {c : Finset (Lit n)}
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
    (2 : ℝ) ^ (n - c.card) := by
  have h1 := sum_prod_eq_falsify_card hInj
  have h2 := factorize c
  have h3 : (∏ v : Fin n, ∑ b : Bool, (if v ∈ c.image
      (fun l : Lit n => l.1)
      then (if b = forced c v then (1 : ℝ) else 0) else 1)) =
      ∏ v : Fin n, (if v ∈ c.image (fun l : Lit n => l.1)
        then (1 : ℝ) else 2) := by
    apply Finset.prod_congr rfl
    intro v _
    exact per_var_sum c v
  have h4 := prod_vars_eq_pow c hInj
  rw [← h1, h2, h3, h4]

private lemma sat_ge_seven_eighths_per_clause {n : ℕ} {c : Finset (Lit n)}
    (hcard3 : c.card = 3)
    (hInj : Set.InjOn (fun l : Lit n => l.1) (↑c : Set (Lit n))) :
    (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℝ)) := by
  have hle3 : 3 ≤ n := by
    have h := card_le_of_injOn hInj
    omega
  have hcardNat : (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card) +
      (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card) =
      ((Finset.univ : Finset (Fin n → Bool)).card) :=
    Finset.card_filter_add_card_filter_not _
  have huniv : ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hfalsify := falsify_card_real hInj
  rw [hcard3] at hfalsify
  have hcardR : ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card : ℕ) : ℝ) +
      ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
      (2 : ℝ) ^ n := by
    have h : ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card +
        ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => ¬ clauseSat x c)).card : ℕ) : ℝ) =
        ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) := by
      exact_mod_cast hcardNat
    rw [Nat.cast_add] at h
    rw [h, huniv]
  have hpow : (2 : ℝ) ^ n = 8 * (2 : ℝ) ^ (n - 3) := by
    have hn : n - 3 + 3 = n := Nat.sub_add_cancel hle3
    calc (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 3 + 3) := by rw [hn]
      _ = (2 : ℝ) ^ (n - 3) * (2 : ℝ) ^ 3 := by rw [pow_add]
      _ = 8 * (2 : ℝ) ^ (n - 3) := by
        have h8 : (2 : ℝ) ^ 3 = 8 := by norm_num
        rw [h8]
        ring
  linarith

/-- MAX-E3SAT, counting clause occurrences: for a family `F` of clauses
indexed by `s`, each with three literals on three distinct variables, some
assignment satisfies the clauses at no fewer than `7 / 8` of the indices. A
uniformly random assignment satisfies each such clause with probability
`7 / 8`; a clause occurring at several indices counts once per index. -/
theorem max_e3sat_seven_eighths {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Finset (Lit n))
    (hF : ∀ i ∈ s, (F i).card = 3 ∧
      Set.InjOn (fun l : Lit n => l.1) (F i)) :
    ∃ x : Fin n → Bool,
      (7 / 8 : ℝ) * s.card ≤
        ((s.filter (fun i => clauseSat x (F i))).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have huniv_ne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hsum_lt : (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      (((s.filter (fun i => clauseSat x (F i))).card : ℕ) : ℝ)) <
      ∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
        ((7 / 8 : ℝ) * (s.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty huniv_ne (fun x _ => hcon x)
  have huniv : ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hRHS : (∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((7 / 8 : ℝ) * (s.card : ℝ))) =
      (s.card : ℝ) * ((7 / 8 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul, huniv]
    ring
  have hper : ∀ i ∈ s, (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x (F i))).card : ℕ) : ℝ) := by
    intro i hi
    obtain ⟨hcard3, hInj⟩ := hF i hi
    exact sat_ge_seven_eighths_per_clause hcard3 hInj
  have hle : (∑ i ∈ s, ((7 / 8 : ℝ) * (2 : ℝ) ^ n)) ≤
      ∑ i ∈ s, ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x (F i))).card : ℕ) : ℝ) :=
    Finset.sum_le_sum hper
  have hLHS_const : (∑ _i ∈ s, ((7 / 8 : ℝ) * (2 : ℝ) ^ n)) =
      (s.card : ℝ) * ((7 / 8 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdc := double_count s F
  linarith

/-- MAX-SAT, counting clause occurrences: for a family `F` of nonempty
clauses indexed by `s`, some assignment satisfies the clauses at no fewer than
half of the indices. A clause occurring at several indices counts once per
index. -/
theorem max_sat_half {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Finset (Lit n)) (hF : ∀ i ∈ s, (F i).Nonempty) :
    ∃ x : Fin n → Bool,
      (1 / 2 : ℝ) * s.card ≤
        ((s.filter (fun i => clauseSat x (F i))).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have huniv_ne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hsum_lt : (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      (((s.filter (fun i => clauseSat x (F i))).card : ℕ) : ℝ)) <
      ∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
        ((1 / 2 : ℝ) * (s.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty huniv_ne (fun x _ => hcon x)
  have huniv : ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hRHS : (∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((1 / 2 : ℝ) * (s.card : ℝ))) =
      (s.card : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul, huniv]
    ring
  have hper : ∀ i ∈ s, (1 / 2 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x (F i))).card : ℕ) : ℝ) := by
    intro i hi
    exact sat_ge_half_per_clause (hF i hi)
  have hle : (∑ i ∈ s, ((1 / 2 : ℝ) * (2 : ℝ) ^ n)) ≤
      ∑ i ∈ s, ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x (F i))).card : ℕ) : ℝ) :=
    Finset.sum_le_sum hper
  have hLHS_const : (∑ _i ∈ s, ((1 / 2 : ℝ) * (2 : ℝ) ^ n)) =
      (s.card : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdc := double_count s F
  linarith

/-- MAX-E3SAT for a duplicate-free formula, given as a finset `F` of clauses,
each with three literals on three distinct variables: some assignment
satisfies at least `7 / 8 * |F|` of them. Repeated clauses cannot be
expressed here; see `max_e3sat_seven_eighths`. -/
theorem max_e3sat_seven_eighths_finset {n : ℕ} (F : Finset (Finset (Lit n)))
    (hF : ∀ c ∈ F, c.card = 3 ∧
      Set.InjOn (fun l : Lit n => l.1) c) :
    ∃ x : Fin n → Bool,
      (7 / 8 : ℝ) * F.card ≤
        ((F.filter (fun c => clauseSat x c)).card : ℝ) :=
  max_e3sat_seven_eighths F id hF

/-- MAX-SAT for a duplicate-free formula, given as a finset `F` of nonempty
clauses: some assignment satisfies at least half of them. Repeated clauses
cannot be expressed here; see `max_sat_half`. -/
theorem max_sat_half_finset {n : ℕ} (F : Finset (Finset (Lit n)))
    (hF : ∀ c ∈ F, c.Nonempty) :
    ∃ x : Fin n → Bool,
      (1 / 2 : ℝ) * F.card ≤
        ((F.filter (fun c => clauseSat x c)).card : ℝ) :=
  max_sat_half F id hF

/-! ### Canonical CNF formulas -/

/-- The literals over `Fin n` whose `(index, polarity)` pair occurs in a
canonical clause. -/
private def toLitFinset (n : ℕ) (C : CNFClause) : Finset (Lit n) :=
  Finset.univ.filter (fun l : Lit n => ((l.1 : ℕ), l.2) ∈ C)

/-- An assignment of `Fin n`, extended by `false` to all natural indices. -/
private def extendAssign {n : ℕ} (x : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then x ⟨i, h⟩ else false

private lemma mem_toLitFinset {n : ℕ} {C : CNFClause} {l : Lit n} :
    l ∈ toLitFinset n C ↔ ((l.1 : ℕ), l.2) ∈ C := by
  simp [toLitFinset]

private lemma clauseSat_toLitFinset_iff {n : ℕ} {C : CNFClause}
    (x : Fin n → Bool) (hC : ∀ l ∈ C, l.1 < n) :
    clauseSat x (toLitFinset n C) ↔ CNFClause.Satisfies (extendAssign x) C := by
  constructor
  · rintro ⟨l, hl, hx⟩
    refine ⟨((l.1 : ℕ), l.2), mem_toLitFinset.mp hl, ?_⟩
    simp [CNFLiteral.Satisfies, extendAssign, hx]
  · rintro ⟨⟨a, b⟩, hab, hsat⟩
    have ha : a < n := hC _ hab
    refine ⟨(⟨a, ha⟩, b), mem_toLitFinset.mpr hab, ?_⟩
    simpa [CNFLiteral.Satisfies, extendAssign, ha] using hsat

private lemma toLitFinset_nonempty {n : ℕ} {C : CNFClause} (hne : C ≠ [])
    (hC : ∀ l ∈ C, l.1 < n) : (toLitFinset n C).Nonempty := by
  obtain ⟨⟨a, b⟩, hab⟩ := List.exists_mem_of_ne_nil C hne
  exact ⟨(⟨a, hC _ hab⟩, b), mem_toLitFinset.mpr hab⟩

private lemma toLitFinset_three {n : ℕ} {C : CNFClause} (hlen : C.length = 3)
    (hnd : (C.map Prod.fst).Nodup) (hC : ∀ l ∈ C, l.1 < n) :
    (toLitFinset n C).card = 3 ∧
      Set.InjOn (fun l : Lit n => l.1) (toLitFinset n C : Set (Lit n)) := by
  have himage : (toLitFinset n C).image (fun l : Lit n => ((l.1 : ℕ), l.2)) =
      C.toFinset := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨l, hl, hl'⟩
      rw [← hl']
      exact mem_toLitFinset.mp hl
    · intro hab
      exact ⟨(⟨a, hC _ hab⟩, b), mem_toLitFinset.mpr hab, rfl⟩
  have hinj : Function.Injective (fun l : Lit n => ((l.1 : ℕ), l.2)) := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hij, rfl⟩ := h
    rw [Fin.ext hij]
  refine ⟨?_, ?_⟩
  · have hcard := Finset.card_image_of_injective (toLitFinset n C) hinj
    rw [himage, List.toFinset_card_of_nodup (List.Nodup.of_map Prod.fst hnd),
      hlen] at hcard
    exact hcard.symm
  · intro l hl l' hl' h
    have heq := List.inj_on_of_nodup_map hnd (mem_toLitFinset.mp hl)
      (mem_toLitFinset.mp hl') (congrArg Fin.val h)
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext h heq.2

private lemma exists_var_bound (φ : CNF) :
    ∃ N : ℕ, ∀ C ∈ φ, ∀ l ∈ C, l.1 < N := by
  induction φ with
  | nil => exact ⟨0, by simp⟩
  | cons C φ ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ l ∈ C, l.1 < M := by
      clear hN
      induction C with
      | nil => exact ⟨0, by simp⟩
      | cons l C ihC =>
        obtain ⟨M, hM⟩ := ihC
        refine ⟨M + l.1 + 1, fun l' hl' => ?_⟩
        rcases List.mem_cons.mp hl' with rfl | hl'
        · omega
        · have := hM l' hl'
          omega
    refine ⟨N + M, fun C' hC' l hl => ?_⟩
    rcases List.mem_cons.mp hC' with rfl | hC'
    · have := hM l hl
      omega
    · have := hN C' hC' l hl
      omega

open Classical in
/-- MAX-SAT for canonical CNF formulas: if every clause of `φ` is nonempty,
some assignment satisfies the clauses at no fewer than half of the positions of
`φ`. A clause repeated in `φ` counts once per position. -/
theorem cnf_max_sat_half (φ : CNF) (hφ : ∀ C ∈ φ, C ≠ []) :
    ∃ v : ℕ → Bool, (1 / 2 : ℝ) * φ.length ≤
      (((Finset.univ : Finset (Fin φ.length)).filter
        (fun i => CNFClause.Satisfies v φ[i])).card : ℝ) := by
  obtain ⟨N, hN⟩ := exists_var_bound φ
  obtain ⟨x, hx⟩ := max_sat_half (Finset.univ : Finset (Fin φ.length))
    (fun i => toLitFinset N φ[i])
    (fun i _ => toLitFinset_nonempty (hφ _ (List.getElem_mem _))
      (hN _ (List.getElem_mem _)))
  refine ⟨extendAssign x, ?_⟩
  have hfilter : (Finset.univ : Finset (Fin φ.length)).filter
        (fun i => clauseSat x (toLitFinset N φ[i])) =
      (Finset.univ : Finset (Fin φ.length)).filter
        (fun i => CNFClause.Satisfies (extendAssign x) φ[i]) :=
    Finset.filter_congr (fun i _ =>
      clauseSat_toLitFinset_iff x (hN _ (List.getElem_mem _)))
  rw [← hfilter]
  rw [Finset.card_univ, Fintype.card_fin] at hx
  exact hx

open Classical in
/-- MAX-E3SAT for canonical CNF formulas: if every clause of `φ` has three
literals on three distinct variables, some assignment satisfies the clauses at
no fewer than `7 / 8` of the positions of `φ`. A clause repeated in `φ` counts
once per position. -/
theorem cnf_max_e3sat_seven_eighths (φ : CNF)
    (hφ : ∀ C ∈ φ, C.length = 3 ∧ (C.map Prod.fst).Nodup) :
    ∃ v : ℕ → Bool, (7 / 8 : ℝ) * φ.length ≤
      (((Finset.univ : Finset (Fin φ.length)).filter
        (fun i => CNFClause.Satisfies v φ[i])).card : ℝ) := by
  obtain ⟨N, hN⟩ := exists_var_bound φ
  obtain ⟨x, hx⟩ := max_e3sat_seven_eighths (Finset.univ : Finset (Fin φ.length))
    (fun i => toLitFinset N φ[i])
    (fun i _ => toLitFinset_three (hφ _ (List.getElem_mem _)).1
      (hφ _ (List.getElem_mem _)).2 (hN _ (List.getElem_mem _)))
  refine ⟨extendAssign x, ?_⟩
  have hfilter : (Finset.univ : Finset (Fin φ.length)).filter
        (fun i => clauseSat x (toLitFinset N φ[i])) =
      (Finset.univ : Finset (Fin φ.length)).filter
        (fun i => CNFClause.Satisfies (extendAssign x) φ[i]) :=
    Finset.filter_congr (fun i _ =>
      clauseSat_toLitFinset_iff x (hN _ (List.getElem_mem _)))
  rw [← hfilter]
  rw [Finset.card_univ, Fintype.card_fin] at hx
  exact hx

end Cslib.Algorithms.SAT.MaxSAT
