/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section



/-- A literal over variables `Fin n`: `(var, positive)`. A clause
is a finset of literals; an assignment satisfies a clause if it
satisfies some literal in it. -/
abbrev Lit (n : ℕ) := Fin n × Bool

def clauseSat {n : ℕ} (x : Fin n → Bool) (c : Finset (Lit n)) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

noncomputable instance {n : ℕ} (x : Fin n → Bool) (c : Finset (Lit n)) :
    Decidable (clauseSat x c) :=
  Classical.propDecidable _

private lemma card_univ_fun_bool (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma double_count {n : ℕ} (F : Finset (Finset (Lit n))) :
    (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((F.filter (fun c => clauseSat x c)).card : ℝ)) =
    ∑ c ∈ F, ((((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => clauseSat x c)).card : ℝ)) := by
  have h1 : ∀ x : Fin n → Bool,
      ((F.filter (fun c => clauseSat x c)).card : ℝ) =
      ∑ c ∈ F, (if clauseSat x c then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.card_filter]
    push_cast
    rfl
  have h2 : ∀ c : Finset (Lit n),
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℝ)) =
      ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
        (if clauseSat x c then (1 : ℝ) else 0) := by
    intro c
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

/-- MAX-E3SAT: a uniformly random assignment satisfies each
3-literal clause (three distinct variables) with probability
`7 / 8`, so some assignment satisfies at least `7 / 8` of all
clauses. Counting form: for every formula `F` of such clauses,
there is an assignment satisfying at least `7 / 8 * |F|` clauses
(in the real-valued count of satisfied clauses). -/
theorem max_e3sat_seven_eighths {n : ℕ} (F : Finset (Finset (Lit n)))
    (hF : ∀ c ∈ F, c.card = 3 ∧
      Set.InjOn (fun l : Lit n => l.1) c) :
    ∃ x : Fin n → Bool,
      (7 / 8 : ℝ) * F.card ≤
        ((F.filter (fun c => clauseSat x c)).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have huniv_ne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hsum_lt : (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      (((F.filter (fun c => clauseSat x c)).card : ℕ) : ℝ)) <
      ∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
        ((7 / 8 : ℝ) * (F.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty huniv_ne (fun x _ => hcon x)
  have huniv : ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hRHS : (∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((7 / 8 : ℝ) * (F.card : ℝ))) =
      (F.card : ℝ) * ((7 / 8 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul, huniv]
    ring
  have hper : ∀ c ∈ F, (7 / 8 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℕ) : ℝ) := by
    intro c hc
    obtain ⟨hcard3, hInj⟩ := hF c hc
    exact sat_ge_seven_eighths_per_clause hcard3 hInj
  have hle : (∑ c ∈ F, ((7 / 8 : ℝ) * (2 : ℝ) ^ n)) ≤
      ∑ c ∈ F, ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℕ) : ℝ) :=
    Finset.sum_le_sum hper
  have hLHS_const : (∑ _c ∈ F, ((7 / 8 : ℝ) * (2 : ℝ) ^ n)) =
      (F.card : ℝ) * ((7 / 8 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdc := double_count F
  linarith

/-- MAX-SAT: for clauses of any positive length, some assignment
satisfies at least half the clauses. -/
theorem max_sat_half {n : ℕ} (F : Finset (Finset (Lit n)))
    (hF : ∀ c ∈ F, c.Nonempty) :
    ∃ x : Fin n → Bool,
      (1 / 2 : ℝ) * F.card ≤
        ((F.filter (fun c => clauseSat x c)).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have huniv_ne : (Finset.univ : Finset (Fin n → Bool)).Nonempty :=
    ⟨fun _ => false, Finset.mem_univ _⟩
  have hsum_lt : (∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
      (((F.filter (fun c => clauseSat x c)).card : ℕ) : ℝ)) <
      ∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
        ((1 / 2 : ℝ) * (F.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty huniv_ne (fun x _ => hcon x)
  have huniv : ((((Finset.univ : Finset (Fin n → Bool)).card : ℕ)) : ℝ) =
      (2 : ℝ) ^ n := by
    rw [Finset.card_univ, card_univ_fun_bool, Nat.cast_pow, Nat.cast_two]
  have hRHS : (∑ _x ∈ (Finset.univ : Finset (Fin n → Bool)),
      ((1 / 2 : ℝ) * (F.card : ℝ))) =
      (F.card : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul, huniv]
    ring
  have hper : ∀ c ∈ F, (1 / 2 : ℝ) * (2 : ℝ) ^ n ≤
      ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℕ) : ℝ) := by
    intro c hc
    exact sat_ge_half_per_clause (hF c hc)
  have hle : (∑ c ∈ F, ((1 / 2 : ℝ) * (2 : ℝ) ^ n)) ≤
      ∑ c ∈ F, ((((Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => clauseSat x c)).card : ℕ) : ℝ) :=
    Finset.sum_le_sum hper
  have hLHS_const : (∑ _c ∈ F, ((1 / 2 : ℝ) * (2 : ℝ) ^ n)) =
      (F.card : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hdc := double_count F
  linarith
