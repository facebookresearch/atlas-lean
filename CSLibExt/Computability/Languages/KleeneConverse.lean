/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kleene's theorem, converse direction
-/
module

public import Cslib.Computability.Languages.RegularLanguage
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Computability.DFA
public import Mathlib.Computability.Language
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Data.Fin.Basic

/-!
# Kleene's theorem, converse direction: regular languages are denoted by regular expressions

Every regular language over a finite alphabet is denoted by a regular expression. The proof
is Arden's lemma applied to the system of language equations of a DFA, eliminating one state
at a time: for a DFA `M`, the languages `M.acceptsFrom q` satisfy
`X q = (∑ j, A q j * X j) + B q`, where `A q j` is the finite union of the singletons `{[a]}`
with `M.step q a = j` and `B q` is `1` on accepting states and `0` otherwise. Eliminating the
last state with Arden's lemma (`Language.self_eq_mul_add_iff`, which requires `[] ∉ A q q`,
true since every `A q j` is a union of singletons) leaves a smaller system of the same shape,
and induction on the number of states shows every `X q` is denoted by a regular expression.

The finiteness of the alphabet is essential: over an infinite alphabet the language of all
one-letter words is regular but no regular expression denotes it (`exists_regular_not_regex`),
since a regular expression mentions only finitely many letters.

## Main results

* `Cslib.Language.IsRegular.exists_regex`: Kleene's theorem, converse direction.
* `Cslib.Language.isRegular_iff_exists_regex`: Kleene's theorem, both directions.
* `Cslib.Language.exists_regular_not_regex`: sharpness of the finite-alphabet hypothesis.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

namespace KleeneConverse

variable {α : Type*}

/-- A language is denoted by a regular expression when it is `r.matches'` for some `r`. -/
def IsRegexDenoted (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

/-- The empty language is denoted by `0`. -/
theorem IsRegexDenoted.zero : IsRegexDenoted (0 : Language α) :=
  ⟨0, RegularExpression.matches'_zero⟩

/-- The language `{[]}` is denoted by `1`. -/
theorem IsRegexDenoted.one : IsRegexDenoted (1 : Language α) :=
  ⟨1, RegularExpression.matches'_epsilon⟩

/-- A singleton `{[a]}` is denoted by `char a`. -/
theorem IsRegexDenoted.char (a : α) : IsRegexDenoted ({[a]} : Language α) :=
  ⟨RegularExpression.char a, RegularExpression.matches'_char a⟩

/-- Denoted languages are closed under union. -/
theorem IsRegexDenoted.add {L K : Language α} (hL : IsRegexDenoted L) (hK : IsRegexDenoted K) :
    IsRegexDenoted (L + K) := by
  obtain ⟨r, hr⟩ := hL
  obtain ⟨s, hs⟩ := hK
  exact ⟨r + s, by rw [RegularExpression.matches'_add, hr, hs]⟩

/-- Denoted languages are closed under concatenation. -/
theorem IsRegexDenoted.mul {L K : Language α} (hL : IsRegexDenoted L) (hK : IsRegexDenoted K) :
    IsRegexDenoted (L * K) := by
  obtain ⟨r, hr⟩ := hL
  obtain ⟨s, hs⟩ := hK
  exact ⟨r * s, by rw [RegularExpression.matches'_mul, hr, hs]⟩

/-- Denoted languages are closed under Kleene star. -/
theorem IsRegexDenoted.kstar {L : Language α} (hL : IsRegexDenoted L) :
    IsRegexDenoted (L∗) := by
  obtain ⟨r, hr⟩ := hL
  exact ⟨r.star, by rw [RegularExpression.matches'_star, hr]⟩

/-- Denoted languages are closed under finite unions. -/
theorem IsRegexDenoted.sum {ι : Type*} {s : Finset ι} {f : ι → Language α}
    (h : ∀ i ∈ s, IsRegexDenoted (f i)) : IsRegexDenoted (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRegexDenoted.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Membership in a finite union of languages. -/
theorem mem_sum {ι : Type*} {s : Finset ι} {f : ι → Language α} {w : List α} :
    w ∈ ∑ i ∈ s, f i ↔ ∃ i ∈ s, w ∈ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Language.mem_add]
      constructor
      · rintro (h | hsum)
        · exact ⟨a, Finset.mem_insert_self a s, h⟩
        · obtain ⟨i, hi, hw⟩ := ih.mp hsum
          exact ⟨i, Finset.mem_insert_of_mem hi, hw⟩
      · rintro ⟨i, hi, hw⟩
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hw
        · exact Or.inr (ih.mpr ⟨i, hi, hw⟩)

/-- The empty word is not in a concatenation whose right factor excludes it. -/
theorem nil_notMem_mul_of_nil_notMem_right {L K : Language α} (hK : [] ∉ K) :
    [] ∉ L * K := by
  intro hmem
  obtain ⟨a, _, b, hb, hab⟩ := Language.mem_mul.mp hmem
  have h2 : a = [] ∧ b = [] := List.append_eq_nil_iff.mp hab
  exact hK (h2.2 ▸ hb)

/-- The system of equations of a DFA at a state: the coefficient of `X j` in the
equation for `X q`, the finite union of the singletons `{[a]}` over the letters taking
`q` to `j`. -/
def coeff {σ : Type*} [DecidableEq σ] [Fintype α] (M : DFA α σ) (q j : σ) : Language α :=
  ∑ a ∈ Finset.univ.filter (fun a => M.step q a = j), ({[a]} : Language α)

/-- The constant term of the equation for `X q`: `1` on accepting states, `0` otherwise. -/
def constTerm {σ : Type*} (M : DFA α σ) (q : σ) : Language α := by
  classical
  exact if q ∈ M.accept then 1 else 0

/-- The language accepted from a state: the unknown `X q` of the system. -/
def fromState {σ : Type*} (M : DFA α σ) (q : σ) : Language α :=
  M.acceptsFrom q

/-- Membership in a coefficient: the word is a single letter taking `q` to `j`. -/
theorem mem_coeff {σ : Type*} [DecidableEq σ] [Fintype α] {M : DFA α σ} {q j : σ} {w : List α} :
    w ∈ coeff M q j ↔ ∃ a, M.step q a = j ∧ w = [a] := by
  unfold coeff
  rw [mem_sum]
  constructor
  · rintro ⟨a, ha, hw⟩
    rw [Finset.mem_filter] at ha
    exact ⟨a, ha.2, hw⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩, rfl⟩

/-- No coefficient contains the empty word. -/
theorem nil_notMem_coeff {σ : Type*} [DecidableEq σ] [Fintype α] {M : DFA α σ} {q j : σ} :
    [] ∉ coeff M q j := by
  rw [mem_coeff]
  rintro ⟨a, _, h⟩
  exact List.cons_ne_self a [] h.symm

/-- Every coefficient is denoted by a regular expression. -/
theorem denoted_coeff {σ : Type*} [DecidableEq σ] [Fintype α] {M : DFA α σ} {q j : σ} :
    IsRegexDenoted (coeff M q j) := by
  unfold coeff
  apply IsRegexDenoted.sum
  intro a _
  exact IsRegexDenoted.char a

/-- Every constant term is denoted by a regular expression. -/
theorem denoted_constTerm {σ : Type*} {M : DFA α σ} {q : σ} :
    IsRegexDenoted (constTerm M q) := by
  unfold constTerm
  split_ifs
  · exact IsRegexDenoted.one
  · exact IsRegexDenoted.zero

/-- The DFA equations: from `q`, either step on a letter and continue, or stop if `q`
accepts. -/
theorem fromState_eq {σ : Type*} [DecidableEq σ] [Fintype σ] [Fintype α] {M : DFA α σ} {q : σ} :
    fromState M q = (∑ j, coeff M q j * fromState M j) + constTerm M q := by
  apply Language.ext
  intro w
  rw [Language.mem_add]
  cases w with
  | nil =>
      have hsum : [] ∉ ∑ j : σ, coeff M q j * fromState M j := by
        rw [mem_sum]
        rintro ⟨j, _, h⟩
        obtain ⟨u, hu, _, _, huv⟩ := Language.mem_mul.mp h
        have h2 : u = [] ∧ _ := List.append_eq_nil_iff.mp huv
        exact nil_notMem_coeff (h2.1 ▸ hu)
      constructor
      · intro h
        have hacc : q ∈ M.accept := h
        right
        unfold constTerm
        rw [ite_eq_left hacc]
        exact Language.nil_mem_one
      · rintro (h | h)
        · exact absurd h hsum
        · unfold constTerm at h
          split_ifs at h with hacc
          · exact hacc
          · exact absurd h (Language.notMem_zero _)
  | cons a w =>
      have hconst : a :: w ∉ constTerm M q := by
        unfold constTerm
        split_ifs with _
        · intro h
          exact absurd (Language.mem_one _ |>.mp h) (by simp)
        · exact Language.notMem_zero _
      constructor
      · intro h
        left
        rw [mem_sum]
        refine ⟨M.step q a, Finset.mem_univ _, ?_⟩
        rw [Language.mem_mul]
        exact ⟨[a], (mem_coeff).2 ⟨a, rfl, rfl⟩, w, h, rfl⟩
      · rintro (h | h)
        · rw [mem_sum] at h
          obtain ⟨j, _, hmul⟩ := h
          obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp hmul
          obtain ⟨a', ha', rfl⟩ := mem_coeff.mp hu
          have hcons : a' = a ∧ v = w := by
            rw [List.cons_append] at huv
            exact List.cons.inj huv
          obtain ⟨rfl, rfl⟩ := hcons
          rw [← ha'] at hv
          exact hv
        · exact absurd h hconst

/-- The coefficient of the reduced system obtained by eliminating the last state: the old
coefficient, plus the detour through the last state, which may loop there any number of
times. -/
def elimCoeff {n : ℕ} (A : Fin (n + 1) → Fin (n + 1) → Language α) :
    Fin n → Fin n → Language α :=
  fun i j =>
    A (Fin.castSucc i) (Fin.castSucc j) +
      A (Fin.castSucc i) (Fin.last n) * (A (Fin.last n) (Fin.last n))∗ *
        A (Fin.last n) (Fin.castSucc j)

/-- The constant term of the reduced system obtained by eliminating the last state. -/
def elimConst {n : ℕ} (A : Fin (n + 1) → Fin (n + 1) → Language α)
    (B : Fin (n + 1) → Language α) : Fin n → Language α :=
  fun i =>
    B (Fin.castSucc i) +
      A (Fin.castSucc i) (Fin.last n) * (A (Fin.last n) (Fin.last n))∗ * B (Fin.last n)

/-- **Solving a system of language equations.** If the languages `X i` satisfy
`X i = (∑ j, A i j * X j) + B i` with every coefficient `A i j` excluding the empty word
and every coefficient and constant term denoted by a regular expression, then every `X i`
is denoted by a regular expression. The proof eliminates the last state with Arden's lemma
and applies the induction hypothesis to the reduced system. -/
theorem exists_regex_of_system (n : ℕ) :
    ∀ {A : Fin n → Fin n → Language α} {B X : Fin n → Language α},
      (∀ i j, IsRegexDenoted (A i j)) → (∀ i j, [] ∉ A i j) →
      (∀ i, IsRegexDenoted (B i)) → (∀ i, X i = (∑ j, A i j * X j) + B i) →
      ∀ i, IsRegexDenoted (X i) := by
  induction n with
  | zero =>
      intro A B X _ _ _ _ i
      exact Fin.elim0 i
  | succ n ih =>
      intro A B X hA hAnil hB hX
      have hLast : X (Fin.last n) = (A (Fin.last n) (Fin.last n))∗ *
          ((∑ j : Fin n, A (Fin.last n) (Fin.castSucc j) * X (Fin.castSucc j)) +
            B (Fin.last n)) := by
        have hArden : X (Fin.last n) = A (Fin.last n) (Fin.last n) * X (Fin.last n) +
            ((∑ j : Fin n, A (Fin.last n) (Fin.castSucc j) * X (Fin.castSucc j)) +
              B (Fin.last n)) := by
          conv_lhs => rw [hX (Fin.last n), Fin.sum_univ_castSucc]
          ac_rfl
        exact (Language.self_eq_mul_add_iff (hAnil _ _)).mp hArden
      have hSub : ∀ i : Fin n, A (Fin.castSucc i) (Fin.last n) * X (Fin.last n) =
          (∑ j : Fin n, (A (Fin.castSucc i) (Fin.last n) * (A (Fin.last n) (Fin.last n))∗ *
              A (Fin.last n) (Fin.castSucc j)) * X (Fin.castSucc j)) +
            A (Fin.castSucc i) (Fin.last n) * (A (Fin.last n) (Fin.last n))∗ *
              B (Fin.last n) := by
        intro i
        rw [hLast, mul_add, mul_add]
        congr 1
        · rw [← mul_assoc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← mul_assoc]
        · rw [← mul_assoc]
      have hA' : ∀ i j, IsRegexDenoted (elimCoeff A i j) := by
        intro i j
        unfold elimCoeff
        exact (hA _ _).add (((hA _ _).mul (hA _ _).kstar).mul (hA _ _))
      have hAnil' : ∀ i j, [] ∉ elimCoeff A i j := by
        intro i j
        unfold elimCoeff
        rw [Language.mem_add]
        rintro (h | h)
        · exact hAnil _ _ h
        · exact nil_notMem_mul_of_nil_notMem_right (hAnil _ _) h
      have hB' : ∀ i, IsRegexDenoted (elimConst A B i) := by
        intro i
        unfold elimConst
        exact (hB _).add (((hA _ _).mul (hA _ _).kstar).mul (hB _))
      have hX' : ∀ i, X (Fin.castSucc i) =
          (∑ j, elimCoeff A i j * X (Fin.castSucc j)) + elimConst A B i := by
        intro i
        calc X (Fin.castSucc i)
            = (∑ j : Fin (n + 1), A (Fin.castSucc i) j * X j) + B (Fin.castSucc i) := hX _
          _ = (∑ j : Fin n, A (Fin.castSucc i) (Fin.castSucc j) * X (Fin.castSucc j)) +
                A (Fin.castSucc i) (Fin.last n) * X (Fin.last n) + B (Fin.castSucc i) := by
              rw [Fin.sum_univ_castSucc]
          _ = (∑ j : Fin n, A (Fin.castSucc i) (Fin.castSucc j) * X (Fin.castSucc j)) +
                ((∑ j : Fin n, (A (Fin.castSucc i) (Fin.last n) *
                    (A (Fin.last n) (Fin.last n))∗ * A (Fin.last n) (Fin.castSucc j)) *
                    X (Fin.castSucc j)) +
                  A (Fin.castSucc i) (Fin.last n) * (A (Fin.last n) (Fin.last n))∗ *
                    B (Fin.last n)) + B (Fin.castSucc i) := by
              rw [hSub i]
          _ = (∑ j, elimCoeff A i j * X (Fin.castSucc j)) + elimConst A B i := by
              unfold elimCoeff elimConst
              simp only [add_mul, Finset.sum_add_distrib]
              ac_rfl
      have hDen : ∀ i : Fin n, IsRegexDenoted (X (Fin.castSucc i)) :=
        ih (A := elimCoeff A) (B := elimConst A B) (X := fun i => X (Fin.castSucc i))
          hA' hAnil' hB' hX'
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hDen j
      · rw [hLast]
        exact ((hA _ _).kstar).mul
          ((IsRegexDenoted.sum (s := Finset.univ)
            (f := fun j => A (Fin.last n) (Fin.castSucc j) * X (Fin.castSucc j))
            (fun j _ => (hA _ _).mul (hDen j))).add (hB _))

/-- The language of a DFA with `Fin n` states is denoted by a regular expression. -/
theorem exists_regex_of_dfa_fin {n : ℕ} [Finite α] (M : DFA α (Fin n)) :
    ∃ r : RegularExpression α, r.matches' = M.accepts := by
  classical
  have := Fintype.ofFinite α
  have hDen := exists_regex_of_system n (A := coeff M) (B := constTerm M) (X := fromState M)
    (fun _ _ => denoted_coeff) (fun _ _ => nil_notMem_coeff) (fun _ => denoted_constTerm)
    (fun _ => fromState_eq)
  obtain ⟨r, hr⟩ := hDen M.start
  exact ⟨r, hr⟩

/-- The language of a DFA over a finite state type is denoted by a regular expression. -/
theorem exists_regex_of_dfa {σ : Type*} [Finite σ] [Finite α] (M : DFA α σ) :
    ∃ r : RegularExpression α, r.matches' = M.accepts := by
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite α
  obtain ⟨r, hr⟩ := exists_regex_of_dfa_fin (M.reindex (Fintype.equivFin σ))
  exact ⟨r, by rw [hr, DFA.accepts_reindex]⟩

/-- The letters occurring in a regular expression. -/
def regexLetters [DecidableEq α] : RegularExpression α → Finset α
  | .zero => ∅
  | .epsilon => ∅
  | .char a => {a}
  | .plus P Q => regexLetters P ∪ regexLetters Q
  | .comp P Q => regexLetters P ∪ regexLetters Q
  | .star P => regexLetters P

/-- Every letter of a word matched by `r` occurs in `r`. -/
theorem mem_matches'_letters [DecidableEq α] {r : RegularExpression α} {w : List α}
    (hw : w ∈ r.matches') {a : α} (ha : a ∈ w) : a ∈ regexLetters r := by
  induction r generalizing w with
  | zero => exact absurd hw (Language.notMem_zero _)
  | epsilon =>
      obtain rfl : w = [] := Language.mem_one _ |>.mp hw
      exact absurd ha List.not_mem_nil
  | char a₀ =>
      rw [RegularExpression.matches'_char] at hw
      change w = [a₀] at hw
      obtain rfl := hw
      rw [List.mem_singleton] at ha
      exact Finset.mem_singleton.2 ha
  | plus P Q ihP ihQ =>
      obtain h | h := Language.mem_add _ _ _ |>.mp hw
      · exact Finset.mem_union_left _ (ihP h ha)
      · exact Finset.mem_union_right _ (ihQ h ha)
  | comp P Q ihP ihQ =>
      obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hw
      obtain h | h := List.mem_append.mp ha
      · exact Finset.mem_union_left _ (ihP hu h)
      · exact Finset.mem_union_right _ (ihQ hv h)
  | star P ihP =>
      obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
      obtain ⟨y, hy, hay⟩ := List.mem_flatten.mp ha
      exact ihP (hL y hy) hay

/-- The three-state DFA accepting exactly the one-letter words. -/
def singletonDFA : DFA α (Fin 3) where
  step q _ := if q = 0 then 1 else 2
  start := 0
  accept := {1}

/-- The one-letter-word DFA accepts exactly the words of length one. -/
theorem singletonDFA_accepts :
    (singletonDFA : DFA α (Fin 3)).accepts = {w : List α | w.length = 1} := by
  have step_zero : ∀ a : α, (singletonDFA : DFA α (Fin 3)).step 0 a = 1 :=
    fun _ => rfl
  have step_one : ∀ a : α, (singletonDFA : DFA α (Fin 3)).step 1 a = 2 :=
    fun _ => rfl
  have step_two : ∀ a : α, (singletonDFA : DFA α (Fin 3)).step 2 a = 2 :=
    fun _ => rfl
  have evalFrom_two : ∀ w : List α,
      (singletonDFA : DFA α (Fin 3)).evalFrom 2 w = 2 := by
    intro w
    induction w with
    | nil => rfl
    | cons c w ih => rw [DFA.evalFrom_cons, step_two, ih]
  apply Language.ext
  intro w
  cases w with
  | nil =>
      constructor
      · intro h
        rw [DFA.mem_accepts] at h
        change (0 : Fin 3) ∈ ({1} : Set (Fin 3)) at h
        rw [Set.mem_singleton_iff] at h
        exact absurd h (by decide)
      · intro h
        change (0 : ℕ) = 1 at h
        exact absurd h (by decide)
  | cons a w =>
      cases w with
      | nil =>
          constructor
          · intro _
            change (1 : ℕ) = 1
            rfl
          · intro _
            rw [DFA.mem_accepts]
            change (1 : Fin 3) ∈ ({1} : Set (Fin 3))
            exact Set.mem_singleton 1
      | cons b w =>
          constructor
          · intro h
            rw [DFA.mem_accepts] at h
            have hev : (singletonDFA : DFA α (Fin 3)).eval (a :: b :: w) = 2 := by
              change (singletonDFA : DFA α (Fin 3)).evalFrom 0 (a :: b :: w) = 2
              rw [DFA.evalFrom_cons, step_zero, DFA.evalFrom_cons, step_one, evalFrom_two]
            rw [hev] at h
            change (2 : Fin 3) ∈ ({1} : Set (Fin 3)) at h
            rw [Set.mem_singleton_iff] at h
            exact absurd h (by decide)
          · intro h
            change w.length + 2 = 1 at h
            exact absurd h (by omega)

end KleeneConverse

/-- **Kleene's theorem, converse direction** (Sipser, *Introduction to the Theory of
Computation*, 3rd ed., Theorem 1.54): every regular language over a finite alphabet is denoted
by a regular expression. Source: M. Sipser, *Introduction to the Theory of Computation*, 3rd
ed., Theorem 1.54. -/
theorem IsRegular.exists_regex {α : Type*} [Finite α] {L : Language α} (hL : L.IsRegular) :
    ∃ r : RegularExpression α, r.matches' = L := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact KleeneConverse.exists_regex_of_dfa M

/-- **Kleene's theorem** (Sipser, 3rd ed., Theorem 1.54): over a finite alphabet, a language
is regular if and only if it is denoted by a regular expression. Source: M. Sipser,
*Introduction to the Theory of Computation*, 3rd ed., Theorem 1.54. -/
theorem isRegular_iff_exists_regex {α : Type*} [Finite α] {L : Language α} :
    L.IsRegular ↔ ∃ r : RegularExpression α, r.matches' = L :=
  ⟨IsRegular.exists_regex, fun ⟨r, hr⟩ => by rw [← hr]; exact IsRegular.regex⟩

/-- **Sharpness of the finite-alphabet hypothesis**: over an infinite alphabet, the language
of one-letter words is regular but is denoted by no regular expression, since a regular
expression mentions only finitely many letters. Source: M. Sipser, *Introduction to the
Theory of Computation*, 3rd ed., Theorem 1.54 (finite alphabet). -/
theorem exists_regular_not_regex {α : Type*} [Infinite α] :
    ∃ L : Language α, L.IsRegular ∧ ∀ r : RegularExpression α, r.matches' ≠ L := by
  classical
  refine ⟨{w | w.length = 1}, ?_, ?_⟩
  · exact ⟨Fin 3, inferInstance, (KleeneConverse.singletonDFA : DFA α (Fin 3)),
      KleeneConverse.singletonDFA_accepts⟩
  · intro r hr
    obtain ⟨a, _, ha⟩ := Set.Infinite.exists_notMem_finset Set.infinite_univ
      (KleeneConverse.regexLetters r)
    have hmem : [a] ∈ ({w : List α | w.length = 1} : Language α) := by simp
    rw [← hr] at hmem
    exact ha (KleeneConverse.mem_matches'_letters hmem (by simp))

end Cslib.Language
