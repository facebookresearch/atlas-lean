/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Lie.WittMultigradedValue
public import MathlibExt.Combinatorics.Words.PrimitiveWord
public import Mathlib.Data.List.Rotate

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- **Content of a word.** Let $r$ be a natural number. The content of a word $w$ over the alphabet
$\{0, \dots, r-1\}$ is the function that assigns to each letter $i$ the number of occurrences of $i$
in $w$. -/
def wittWordContent {r : ℕ} (w : List (Fin r)) : Fin r → ℕ :=
  fun i => w.count i

/-- **Lyndon word.** Let $\alpha$ be a linearly ordered alphabet, and order the words over
$\alpha$ lexicographically. A word $w$ over $\alpha$ of length $n$ is a Lyndon word if it is
nonempty and, for every $k$ with $0 < k < n$, $w$ is strictly smaller than its rotation by $k$,
the word obtained by moving the first $k$ letters of $w$ to the end. -/
def IsLyndonWord {α : Type*} [LinearOrder α] (w : List α) : Prop :=
  w ≠ [] ∧ ∀ k, 0 < k → k < w.length → w < w.rotate k

/-- **Content is additive under concatenation.** For a natural number $r$, words $u$ and $v$ over
the alphabet $\{0, \dots, r-1\}$, and every letter $i$, the number of occurrences of $i$ in the
concatenation $uv$ is the number of occurrences of $i$ in $u$ plus the number of occurrences
of $i$ in $v$. -/
@[simp]
theorem wittWordContent_append {r : ℕ} (u v : List (Fin r)) :
    wittWordContent (u ++ v) = fun i => wittWordContent u i + wittWordContent v i := by
  funext i
  simp [wittWordContent]

/-- **Content of a one-letter word.** Let $r$ be a natural number. For every letter $i$ of the
alphabet $\{0, \dots, r-1\}$, the content of the one-letter word $i$ takes the value $1$ at $i$ and
the value $0$ at every other letter. -/
@[simp]
theorem wittWordContent_singleton {r : ℕ} (i : Fin r) :
    wittWordContent [i] = Function.update (fun _ => 0) i 1 := by
  funext j
  by_cases h : j = i
  · subst j
    simp [wittWordContent]
  · simp [wittWordContent, h, Ne.symm h]

/-- **Content of a word after prepending a letter.** Let $r$ be a natural number, let $w$ be a word
over the alphabet $\{0, \dots, r-1\}$, let $i$ be a letter, and write $c(u)$ for the content of a
word $u$ (the number of occurrences of each letter in $u$). If $iw$ denotes $w$ with $i$ prepended,
then $c(iw)(i) = c(w)(i) + 1$ and $c(iw)(j) = c(w)(j)$ for every letter $j \ne i$. -/
@[simp]
theorem wittWordContent_cons {r : ℕ} (i : Fin r) (w : List (Fin r)) :
    wittWordContent (i :: w) =
      Function.update (wittWordContent w) i (wittWordContent w i + 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [wittWordContent]
  · simp [wittWordContent, h, Ne.symm h]

/-- **The content of a word sums to its length.** For a natural number $r$ and a word $w$ over
the alphabet $\{0, \dots, r-1\}$, summing over all letters $i$ the number of occurrences of $i$
in $w$ gives the length of $w$. -/
@[simp]
theorem sum_wittWordContent {r : ℕ} (w : List (Fin r)) :
    (∑ i, wittWordContent w i) = w.length := by
  rw [← List.sum_toFinset_count_eq_length w]
  symm
  apply Finset.sum_subset
  · simp
  · intro i _ hi
    exact List.count_eq_zero_of_not_mem (by simpa using hi)

/-- **Words with prescribed content.** Let $r$ be a natural number. Given a function $d$ from the
alphabet $\{0, \dots, r-1\}$ to the natural numbers, the words of content $d$ are the words $w$ over
this alphabet whose content equals $d$, that is, in which each letter $i$ occurs exactly $d(i)$
times. -/
def WordsOfContent {r : ℕ} (degree : Fin r → ℕ) :=
  {w : List (Fin r) // wittWordContent w = degree}

/-- **Lyndon words of given content.** For a natural number $r$ and natural numbers
$n_0, \dots, n_{r-1}$, the set of Lyndon words over the alphabet $\{0, \dots, r-1\}$, ordered as
the natural numbers, in which each letter $i$ occurs exactly $n_i$ times. -/
def LyndonWordsOfContent {r : ℕ} (degree : Fin r → ℕ) :=
  {w : WordsOfContent degree // IsLyndonWord w.1}

private def wittWordsToVector {r : ℕ} (degree : Fin r → ℕ) :
    WordsOfContent degree → List.Vector (Fin r) (∑ i, degree i) :=
  fun w => ⟨w.1, by rw [← sum_wittWordContent, w.2]⟩

private theorem wittWordsToVector_injective {r : ℕ} (degree : Fin r → ℕ) :
    Function.Injective (wittWordsToVector degree) := by
  intro u v h
  apply Subtype.ext
  exact congr_arg (fun z : List.Vector (Fin r) (∑ i, degree i) => z.1) h

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (WordsOfContent degree) :=
  Finite.of_injective (wittWordsToVector degree) (wittWordsToVector_injective degree)

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) : Fintype (WordsOfContent degree) :=
  Fintype.ofFinite _

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (LyndonWordsOfContent degree) :=
  Finite.of_injective (fun w => w.1) fun _ _ h => Subtype.ext h

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) : Fintype (LyndonWordsOfContent degree) :=
  Fintype.ofFinite _

private def wittDegreePred {r : ℕ} (degree : Fin r → ℕ) (i : Fin r) : Fin r → ℕ :=
  Function.update degree i (degree i - 1)

private theorem sum_wittDegreePred {r : ℕ} (degree : Fin r → ℕ) (i : Fin r)
    (hi : 0 < degree i) :
    (∑ j, wittDegreePred degree i j) = (∑ j, degree j) - 1 := by
  rw [wittDegreePred, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ degree (Finset.mem_univ i)
  omega

private theorem wittWord_ne_nil {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) : w.1 ≠ [] := by
  intro hw
  have hzero : (∑ i, degree i) = 0 := by
    rw [← w.2, sum_wittWordContent, hw]
    rfl
  exact (Nat.ne_of_gt hdegree) hzero

private theorem wittWord_head_tail {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    let i := w.1.head (wittWord_ne_nil w hdegree)
    0 < degree i ∧ wittWordContent w.1.tail = wittDegreePred degree i := by
  let hne := wittWord_ne_nil w hdegree
  let i := w.1.head hne
  have hcontent : wittWordContent (i :: w.1.tail) = degree := by
    rw [List.cons_head_tail hne]
    exact w.2
  rw [wittWordContent_cons] at hcontent
  have hi := congr_fun hcontent i
  constructor
  · simp [i] at hi
    omega
  · funext j
    have hj := congr_fun hcontent j
    by_cases hji : j = i
    · subst j
      simp [wittDegreePred, i] at hi ⊢
      omega
    · simp only [ne_eq, hji, not_false_eq_true, Function.update_of_ne,
        wittDegreePred, i] at hj ⊢
      exact hj

private abbrev WittPositiveLetter {r : ℕ} (degree : Fin r → ℕ) :=
  {i : Fin r // 0 < degree i}

private def wittWordsHeadTail {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1) :=
  let h := wittWord_head_tail w hdegree
  ⟨⟨w.1.head (wittWord_ne_nil w hdegree), h.1⟩, ⟨w.1.tail, h.2⟩⟩

private def wittWordsCons {r : ℕ} (degree : Fin r → ℕ) :
    (Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1)) →
      WordsOfContent degree
  | ⟨i, w⟩ => ⟨i.1 :: w.1, by
      rw [wittWordContent_cons, w.2]
      funext j
      by_cases hji : j = i.1
      · subst j
        have hi : 0 < degree i.1 := i.2
        simp only [wittDegreePred, Function.update_self]
        omega
      · simp [wittDegreePred, hji]⟩

private def wittWordsConsEquiv {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    WordsOfContent degree ≃
      Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1) where
  toFun := wittWordsHeadTail degree hdegree
  invFun := wittWordsCons degree
  left_inv w := by
    apply Subtype.ext
    exact List.cons_head_tail (wittWord_ne_nil w hdegree)
  right_inv p := by
    rcases p with ⟨i, w⟩
    rfl

private theorem card_wordsOfContent_eq_sum {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    Fintype.card (WordsOfContent degree) =
      ∑ i : WittPositiveLetter degree,
        Fintype.card (WordsOfContent (wittDegreePred degree i.1)) := by
  rw [Fintype.card_congr (wittWordsConsEquiv degree hdegree)]
  exact Fintype.card_sigma

private theorem sum_wittPositiveLetter {r : ℕ} (degree : Fin r → ℕ) :
    (∑ i : WittPositiveLetter degree, degree i.1) = ∑ i, degree i := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => 0 < degree i) (by simp)]
  apply Finset.sum_subset (Finset.filter_subset (fun i => 0 < degree i) Finset.univ)
  intro i _ hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
  omega

private theorem prod_factorial_wittDegreePred {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (hi : 0 < degree i) :
    degree i * (∏ j, Nat.factorial (wittDegreePred degree i j)) =
      ∏ j, Nat.factorial (degree j) := by
  rw [wittDegreePred]
  have hfun : (fun j => Nat.factorial (Function.update degree i (degree i - 1) j)) =
      Function.update (fun j => Nat.factorial (degree j)) i (Nat.factorial (degree i - 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.prod_erase_mul Finset.univ (fun j => Nat.factorial (degree j))
    (Finset.mem_univ i)]
  have hsucc : degree i - 1 + 1 = degree i := by omega
  have hfac : Nat.factorial (degree i) = degree i * Nat.factorial (degree i - 1) := by
    calc
      Nat.factorial (degree i) = Nat.factorial (degree i - 1 + 1) :=
        congr_arg Nat.factorial hsucc.symm
      _ = (degree i - 1 + 1) * Nat.factorial (degree i - 1) :=
        Nat.factorial_succ (degree i - 1)
      _ = degree i * Nat.factorial (degree i - 1) := by rw [hsucc]
  rw [hfac]
  ac_rfl

private theorem prod_factorial_mul_multinomial_pred {r : ℕ} (degree : Fin r → ℕ)
    (i : Fin r) (hi : 0 < degree i) :
    (∏ j, Nat.factorial (degree j)) *
        Nat.multinomial Finset.univ (wittDegreePred degree i) =
      degree i * Nat.factorial ((∑ j, degree j) - 1) := by
  calc
    (∏ j, Nat.factorial (degree j)) *
          Nat.multinomial Finset.univ (wittDegreePred degree i) =
        (degree i * ∏ j, Nat.factorial (wittDegreePred degree i j)) *
          Nat.multinomial Finset.univ (wittDegreePred degree i) := by
            rw [prod_factorial_wittDegreePred degree i hi]
    _ = degree i * ((∏ j, Nat.factorial (wittDegreePred degree i j)) *
          Nat.multinomial Finset.univ (wittDegreePred degree i)) := by ac_rfl
    _ = degree i * Nat.factorial (∑ j, wittDegreePred degree i j) := by
      rw [Nat.multinomial_spec]
    _ = degree i * Nat.factorial ((∑ j, degree j) - 1) := by
      rw [sum_wittDegreePred degree i hi]

private theorem multinomial_eq_sum_pred {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    Nat.multinomial Finset.univ degree =
      ∑ i : WittPositiveLetter degree,
        Nat.multinomial Finset.univ (wittDegreePred degree i.1) := by
  apply Nat.mul_left_cancel (n := ∏ j, Nat.factorial (degree j)) (by positivity)
  rw [Nat.multinomial_spec]
  rw [Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_congr rfl fun i _ =>
      prod_factorial_mul_multinomial_pred degree i.1 i.2]
    rw [← Finset.sum_mul, sum_wittPositiveLetter]
  let n := ∑ i, degree i
  have hsucc : n - 1 + 1 = n := by dsimp [n]; omega
  calc
    Nat.factorial n = Nat.factorial (n - 1 + 1) := congr_arg Nat.factorial hsucc.symm
    _ = (n - 1 + 1) * Nat.factorial (n - 1) := Nat.factorial_succ (n - 1)
    _ = n * Nat.factorial (n - 1) := by rw [hsucc]

/-- **Words of given content are counted by the multinomial coefficient.** Let $r$ be a natural
number, let $n_0, \dots, n_{r-1}$ be natural numbers, and let $n = n_0 + \dots + n_{r-1}$. The
number of words over the alphabet $\{0, \dots, r-1\}$ in which each letter $i$ occurs exactly
$n_i$ times is the multinomial coefficient
$\binom{n}{n_0, \ldots, n_{r-1}} = \frac{n!}{n_0! \cdots n_{r-1}!}$. -/
theorem card_wordsOfContent_eq_multinomial {r : ℕ} (degree : Fin r → ℕ) :
    Fintype.card (WordsOfContent degree) = Nat.multinomial Finset.univ degree := by
  induction hn : (∑ i, degree i) using Nat.strong_induction_on generalizing degree with
  | h n ih =>
      by_cases hn0 : n = 0
      · have hdegree : degree = fun _ => 0 := by
          funext i
          exact ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Nat.zero_le _).mp
            (hn.trans hn0)) i (Finset.mem_univ i)
        subst degree
        have hcard : Fintype.card (WordsOfContent (fun _ : Fin r => 0)) = 1 := by
          apply Fintype.card_eq_one_iff.mpr
          refine ⟨⟨[], by funext i; simp [wittWordContent]⟩, fun w => ?_⟩
          apply Subtype.ext
          apply List.eq_nil_of_length_eq_zero
          rw [← sum_wittWordContent, w.2]
          simp
        rw [hcard]
        simp [Nat.multinomial]
      · have hdegree : 0 < ∑ i, degree i := hn.symm ▸ Nat.pos_of_ne_zero hn0
        rw [card_wordsOfContent_eq_sum degree hdegree]
        rw [multinomial_eq_sum_pred degree hdegree]
        apply Finset.sum_congr rfl
        intro i _
        apply ih ((∑ j, degree j) - 1)
        · omega
        · exact sum_wittDegreePred degree i.1 i.2

private theorem wittExistsRotationPeriod {α : Type*} (w : List α) (hw : w ≠ []) :
    ∃ p, 0 < p ∧ w.rotate p = w := by
  exact ⟨w.length, List.length_pos_of_ne_nil hw, w.rotate_length⟩

private noncomputable def wittPeriod {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : ℕ :=
  Nat.find (wittExistsRotationPeriod w hw)

private theorem wittPeriod_pos {α : Type*} [DecidableEq α] (w : List α) (hw : w ≠ []) :
    0 < wittPeriod w hw := by
  exact (Nat.find_spec (wittExistsRotationPeriod w hw)).1

private theorem wittRotate_period {α : Type*} [DecidableEq α] (w : List α) (hw : w ≠ []) :
    w.rotate (wittPeriod w hw) = w := by
  exact (Nat.find_spec (wittExistsRotationPeriod w hw)).2

private theorem wittPeriod_le_length {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) :
    wittPeriod w hw ≤ w.length := by
  exact Nat.find_min' (wittExistsRotationPeriod w hw)
    ⟨List.length_pos_of_ne_nil hw, w.rotate_length⟩

private theorem wittPeriod_min {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) {q : ℕ}
    (hq0 : 0 < q) (hq : w.rotate q = w) : wittPeriod w hw ≤ q := by
  exact Nat.find_min' (wittExistsRotationPeriod w hw) ⟨hq0, hq⟩

private theorem wittRotate_mul_eq {α : Type*} (w : List α) {p : ℕ}
    (hp : w.rotate p = w) (q : ℕ) : w.rotate (p * q) = w := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ]
      rw [← w.rotate_rotate, ih, hp]

private theorem wittPeriod_dvd_length {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : wittPeriod w hw ∣ w.length := by
  let p := wittPeriod w hw
  have hp0 : 0 < p := wittPeriod_pos w hw
  have hp : w.rotate p = w := wittRotate_period w hw
  have hrem : w.rotate (w.length % p) = w := by
    calc
      w.rotate (w.length % p) =
          (w.rotate (p * (w.length / p))).rotate (w.length % p) := by
            rw [wittRotate_mul_eq w hp]
      _ = w.rotate (p * (w.length / p) + w.length % p) := w.rotate_rotate _ _
      _ = w.rotate w.length := by
        congr 1
        simpa [add_comm] using (Nat.mod_add_div w.length p)
      _ = w := w.rotate_length
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hne
  have hpos : 0 < w.length % p := Nat.pos_of_ne_zero hne
  have hle : p ≤ w.length % p := wittPeriod_min w hw hpos hrem
  exact (Nat.not_le_of_lt (Nat.mod_lt w.length hp0)) hle

private theorem wittHasPeriod_of_rotate_eq {α : Type*} {w : List α} {p : ℕ}
    (hple : p ≤ w.length) (hrot : w.rotate p = w) : w.HasPeriod p := by
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hip : i + p < w.length := by omega
  have hiw : i < w.length := by omega
  have h := congr_arg (fun z : List α => z[i]?) hrot
  rw [List.getElem?_rotate hiw, Nat.mod_eq_of_lt hip] at h
  exact h.symm

private def wittWordPower {α : Type*} (u : List α) (d : ℕ) : List α :=
  (List.replicate d u).flatten

private theorem length_wittWordPower {α : Type*} (u : List α) (d : ℕ) :
    (wittWordPower u d).length = d * u.length := by
  simp [wittWordPower, List.length_flatten]

private theorem wittWordContent_power {r : ℕ} (u : List (Fin r)) (d : ℕ) :
    wittWordContent (wittWordPower u d) = fun i => d * wittWordContent u i := by
  induction d with
  | zero =>
      funext i
      simp [wittWordPower, wittWordContent]
  | succ d ih =>
      rw [show wittWordPower u (d + 1) = u ++ wittWordPower u d by
        simp [wittWordPower, List.replicate_succ]]
      rw [wittWordContent_append, ih]
      funext i
      simp [Nat.succ_mul, add_comm]

private theorem wittEq_wordPower_take_of_hasPeriod {α : Type*} {w : List α} {p d : ℕ}
    (hp0 : 0 < p) (hd0 : 0 < d) (hlen : w.length = p * d) (per : w.HasPeriod p) :
    w = wittWordPower (w.take p) d := by
  have hple : p ≤ w.length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_right p hd0
  have htake : (w.take p).length = p := by simp [hple]
  rw [wittWordPower, ← List.ofFn_get (w.take p), ← List.ofFn_fin_repeat]
  apply List.ext_getElem
  · rw [List.length_ofFn]
    rw [hlen, htake, mul_comm]
  · intro i hiw hirhs
    have himod : i % p < (w.take p).length := by
      rw [List.length_take, min_eq_left hple]
      exact Nat.mod_lt i hp0
    have hper := per.getElem?_mod p i w hiw
    have himodw : i % p < w.length := (Nat.mod_lt i hp0).trans_le hple
    have hperval : w[i % p] = w[i] := by
      rw [List.getElem?_eq_getElem himodw, List.getElem?_eq_getElem hiw] at hper
      exact Option.some.inj hper
    rw [List.getElem_ofFn, Fin.repeat_apply]
    calc
      w[i] = w[i % p] := hperval.symm
      _ = (w.take p)[i % p] := (List.getElem_take).symm
      _ = (w.take p).get _ := by
        congr 1
        simp [htake]

private noncomputable def wittRoot {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : List α :=
  w.take (wittPeriod w hw)

private noncomputable def wittExponent {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : ℕ :=
  w.length / wittPeriod w hw

private theorem length_wittRoot {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : (wittRoot w hw).length = wittPeriod w hw := by
  simp [wittRoot, wittPeriod_le_length]

private theorem wittExponent_pos {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : 0 < wittExponent w hw := by
  apply Nat.div_pos (wittPeriod_le_length w hw)
  exact wittPeriod_pos w hw

private theorem wittPeriod_mul_exponent {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) :
    wittPeriod w hw * wittExponent w hw = w.length := by
  exact Nat.mul_div_cancel' (wittPeriod_dvd_length w hw)

private theorem wittWord_eq_root_power {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : w = wittWordPower (wittRoot w hw) (wittExponent w hw) := by
  apply wittEq_wordPower_take_of_hasPeriod
  · exact wittPeriod_pos w hw
  · exact wittExponent_pos w hw
  · exact (wittPeriod_mul_exponent w hw).symm
  · exact wittHasPeriod_of_rotate_eq (wittPeriod_le_length w hw)
      (wittRotate_period w hw)

private theorem wittRotate_injective_of_period_eq_length {α : Type*} [DecidableEq α]
    {w : List α} (hw : w ≠ []) (hperiod : wittPeriod w hw = w.length)
    {i j : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hrotate : w.rotate i = w.rotate j) : i = j := by
  have aux : ∀ {a b : ℕ}, a < b → b < w.length →
      w.rotate a = w.rotate b → False := by
    intro a b hab hb hrot
    have ha : a ≤ w.length := (hab.trans hb).le
    have heq₁ : a + (w.length - a) = w.length := Nat.add_sub_of_le ha
    have heq₂ : b + (w.length - a) = w.length + (b - a) := by omega
    have hfix : w.rotate (b - a) = w := by
      calc
        w.rotate (b - a) = (w.rotate w.length).rotate (b - a) := by
          rw [w.rotate_length]
        _ = w.rotate (w.length + (b - a)) := w.rotate_rotate _ _
        _ = w.rotate (b + (w.length - a)) := by rw [heq₂]
        _ = (w.rotate b).rotate (w.length - a) := (w.rotate_rotate _ _).symm
        _ = (w.rotate a).rotate (w.length - a) := by rw [hrot]
        _ = w.rotate (a + (w.length - a)) := w.rotate_rotate _ _
        _ = w := by rw [heq₁, w.rotate_length]
    have hle := wittPeriod_min w hw (q := b - a) (by omega) hfix
    rw [hperiod] at hle
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact aux hij hj hrotate
  · exact aux hji hi hrotate.symm

private theorem wittWordPower_succ {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u (d + 1) = u ++ wittWordPower u d := by
  simp [wittWordPower, List.replicate_succ]

private theorem wittWordPower_add {α : Type*} (u : List α) (a b : ℕ) :
    wittWordPower u (a + b) = wittWordPower u a ++ wittWordPower u b := by
  rw [wittWordPower, List.replicate_add, List.flatten_append]
  rfl

private theorem wittWordPower_append_self {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u d ++ u = u ++ wittWordPower u d := by
  induction d with
  | zero => simp [wittWordPower]
  | succ d ih =>
      rw [wittWordPower_succ]
      simp only [List.append_assoc]
      rw [ih]

private theorem wittRotate_length_power {α : Type*} (u : List α) (d : ℕ) :
    (wittWordPower u d).rotate u.length = wittWordPower u d := by
  cases d with
  | zero => simp [wittWordPower]
  | succ d =>
      rw [wittWordPower_succ, List.rotate_append_length_eq]
      exact wittWordPower_append_self u d

private theorem wittIsPrimitiveWord_iff_period_eq_length {α : Type*} [DecidableEq α]
    {w : List α} (hw : w ≠ []) :
    IsPrimitiveWord w ↔ wittPeriod w hw = w.length := by
  constructor
  · intro hprimitive
    have hexponent : wittExponent w hw = 1 :=
      hprimitive.2 (wittRoot w hw) (wittExponent w hw)
        (wittWord_eq_root_power w hw).symm
    calc
      wittPeriod w hw = wittPeriod w hw * wittExponent w hw := by
        rw [hexponent, mul_one]
      _ = w.length := wittPeriod_mul_exponent w hw
  · intro hperiod
    refine ⟨hw, ?_⟩
    intro v n hpower
    change wittWordPower v n = w at hpower
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      apply hw
      simpa [wittWordPower] using hpower.symm
    have hv : v ≠ [] := by
      intro hv
      subst v
      apply hw
      simpa [wittWordPower] using hpower.symm
    have hvpos : 0 < v.length := List.length_pos_of_ne_nil hv
    have hrot : w.rotate v.length = w := by
      rw [← hpower]
      exact wittRotate_length_power v n
    have hle := wittPeriod_min w hw hvpos hrot
    rw [hperiod] at hle
    have hlength := congr_arg List.length hpower
    rw [length_wittWordPower] at hlength
    by_contra hn1
    have hn2 : 2 ≤ n := by omega
    have hmul : 2 * v.length ≤ n * v.length := Nat.mul_le_mul_right v.length hn2
    rw [hlength] at hmul
    omega

private theorem wittRotate_ne_of_nodup_cyclicPermutations {α : Type*} {w : List α}
    (hw0 : w ≠ []) (hw : w.cyclicPermutations.Nodup) {k : ℕ}
    (hk0 : 0 < k) (hk : k < w.length) : w.rotate k ≠ w := by
  intro hrotate
  have hlen := List.length_cyclicPermutations_of_ne_nil w hw0
  let i : Fin w.cyclicPermutations.length := ⟨0, by rw [hlen]; omega⟩
  let j : Fin w.cyclicPermutations.length := ⟨k, by rw [hlen]; exact hk⟩
  have hget : w.cyclicPermutations.get i = w.cyclicPermutations.get j := by
    rw [List.get_cyclicPermutations, List.get_cyclicPermutations]
    simpa [i, j] using hrotate.symm
  have hij := List.nodup_iff_injective_get.mp hw hget
  have hval := congr_arg Fin.val hij
  simp [i, j] at hval
  omega

/-- **Primitivity via distinct rotations.** Let $w$ be a word of length $n$, and for
$0 \le k < n$ let $w_k$ be the rotation of $w$ by $k$, obtained by moving the first $k$ letters
of $w$ to the end. Then $w$ is primitive if and only if $w$ is nonempty and the $n$ words
$w_0, w_1, \dots, w_{n-1}$ are pairwise distinct. -/
theorem isPrimitiveWord_iff_nodup_cyclicPermutations {α : Type*} {w : List α} :
    IsPrimitiveWord w ↔ w ≠ [] ∧ w.cyclicPermutations.Nodup := by
  classical
  constructor
  · intro hw
    refine ⟨hw.1, List.nodup_iff_injective_get.mpr ?_⟩
    intro i j hget
    apply Fin.ext
    apply wittRotate_injective_of_period_eq_length hw.1
      ((wittIsPrimitiveWord_iff_period_eq_length hw.1).mp hw)
    · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
      exact i.2
    · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
      exact j.2
    · simpa only [List.get_cyclicPermutations] using hget
  · rintro ⟨hw0, hw⟩
    apply (wittIsPrimitiveWord_iff_period_eq_length hw0).2
    apply le_antisymm (wittPeriod_le_length w hw0)
    by_contra hnot
    have hlt : wittPeriod w hw0 < w.length := Nat.lt_of_not_ge hnot
    exact wittRotate_ne_of_nodup_cyclicPermutations hw0 hw
      (wittPeriod_pos w hw0) hlt (wittRotate_period w hw0)

/-- **Nontrivial rotations move a primitive word.** If $w$ is a primitive word of length $n$
and $0 < k < n$, then the rotation of $w$ by $k$, obtained by moving the first $k$ letters of $w$
to the end, is different from $w$. -/
theorem rotate_ne_of_isPrimitiveWord {α : Type*} {w : List α}
    (hw : IsPrimitiveWord w) {k : ℕ} (hk0 : 0 < k) (hk : k < w.length) :
    w.rotate k ≠ w := by
  exact wittRotate_ne_of_nodup_cyclicPermutations hw.1
    (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2 hk0 hk

private theorem wittWordPower_power {α : Type*} (u : List α) (e d : ℕ) :
    wittWordPower (wittWordPower u e) d = wittWordPower u (d * e) := by
  induction d with
  | zero => simp [wittWordPower]
  | succ d ih =>
      rw [wittWordPower_succ, ih, ← wittWordPower_add]
      congr 1
      simp [Nat.add_mul, add_comm]

private theorem wittWordPower_eq_ofFn {α : Type*} (u : List α) (d : ℕ) :
    wittWordPower u d = List.ofFn (Fin.repeat d u.get) := by
  rw [List.ofFn_fin_repeat, List.ofFn_get]
  rfl

private theorem wittGetElem_power {α : Type*} {u : List α} {d i : ℕ}
    (hu : u ≠ []) (hi : i < (wittWordPower u d).length) :
    (wittWordPower u d)[i] =
      u[i % u.length]'(Nat.mod_lt i (List.length_pos_of_ne_nil hu)) := by
  have heq := congr_arg (fun z : List α => z[i]?) (wittWordPower_eq_ofFn u d)
  have hifn : i < (List.ofFn (Fin.repeat d u.get)).length := by
    simpa [length_wittWordPower] using hi
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hifn,
    List.getElem_ofFn, Fin.repeat_apply] at heq
  have hval := Option.some.inj heq
  calc
    (wittWordPower u d)[i] = u.get _ := hval
    _ = u[i % u.length]'(Nat.mod_lt i (List.length_pos_of_ne_nil hu)) := by
      apply congr_arg u.get
      apply Fin.ext
      simp [Fin.modNat]

private theorem wittRotate_eq_of_power_rotate_eq {α : Type*} {u : List α}
    (hu : u ≠ []) {d q : ℕ} (hd : 0 < d)
    (hrotate : (wittWordPower u d).rotate q = wittWordPower u d) :
    u.rotate q = u := by
  let W := wittWordPower u d
  have hlen : W.length = d * u.length := length_wittWordPower u d
  have hpW : u.length ≤ W.length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_left u.length hd
  have hpdvd : u.length ∣ W.length := by
    rw [hlen]
    exact ⟨d, by simp [mul_comm]⟩
  have hWpos : 0 < W.length := by
    rw [hlen]
    exact Nat.mul_pos hd (List.length_pos_of_ne_nil hu)
  apply List.ext_getElem
  · simp
  · intro i hirot hiu
    have hi : i < u.length := hiu
    have hiW : i < W.length := hi.trans_le hpW
    have hiWr : i < (W.rotate q).length := by simpa using hiW
    have hopt := congr_arg (fun z : List α => z[i]?) hrotate
    rw [List.getElem?_eq_getElem hiWr, List.getElem?_eq_getElem hiW] at hopt
    have hval := Option.some.inj hopt
    rw [List.getElem_rotate] at hval
    have hleft := wittGetElem_power hu
      (Nat.mod_lt (i + q) hWpos :
        (i + q) % W.length < (wittWordPower u d).length)
    have hright := wittGetElem_power hu hiW
    rw [hleft, hright] at hval
    rw [List.getElem_rotate]
    simpa only [Nat.mod_mod_of_dvd (i + q) hpdvd, Nat.mod_eq_of_lt hi] using hval

private theorem wittWordPower_ne_nil {α : Type*} {u : List α} (hu : u ≠ [])
    {d : ℕ} (hd : 0 < d) : wittWordPower u d ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [length_wittWordPower]
  exact Nat.mul_pos hd (List.length_pos_of_ne_nil hu)

private theorem wittPeriod_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittPeriod (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = u.length := by
  let W := wittWordPower u d
  let hW : W ≠ [] := wittWordPower_ne_nil hu.1 hd
  apply le_antisymm
  · apply wittPeriod_min W hW (List.length_pos_of_ne_nil hu.1)
    exact wittRotate_length_power u d
  · by_contra hnot
    have hlt : wittPeriod W hW < u.length := Nat.lt_of_not_ge hnot
    have hrootrotate : u.rotate (wittPeriod W hW) = u :=
      wittRotate_eq_of_power_rotate_eq hu.1 hd (wittRotate_period W hW)
    exact rotate_ne_of_isPrimitiveWord hu (wittPeriod_pos W hW) hlt hrootrotate

private theorem wittTake_length_power {α : Type*} (u : List α) {d : ℕ} (hd : 0 < d) :
    (wittWordPower u d).take u.length = u := by
  cases d with
  | zero => omega
  | succ d =>
      rw [wittWordPower_succ]
      simp

private theorem wittRoot_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittRoot (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = u := by
  rw [wittRoot, wittPeriod_power_of_primitive hu hd]
  exact wittTake_length_power u hd

private theorem wittExponent_power_of_primitive {α : Type*} [DecidableEq α]
    {u : List α} (hu : IsPrimitiveWord u) {d : ℕ} (hd : 0 < d) :
    wittExponent (wittWordPower u d) (wittWordPower_ne_nil hu.1 hd) = d := by
  rw [wittExponent, wittPeriod_power_of_primitive hu hd, length_wittWordPower]
  exact Nat.mul_div_left d (List.length_pos_of_ne_nil hu.1)

private theorem wittRoot_isPrimitive {α : Type*} [DecidableEq α]
    (w : List α) (hw : w ≠ []) : IsPrimitiveWord (wittRoot w hw) := by
  let u := wittRoot w hw
  have hu : u ≠ [] := by
    apply List.ne_nil_of_length_pos
    dsimp [u]
    rw [length_wittRoot]
    exact wittPeriod_pos w hw
  let q := wittPeriod u hu
  let v := wittRoot u hu
  let e := wittExponent u hu
  let d := wittExponent w hw
  have hudecomp : u = wittWordPower v e := by
    exact wittWord_eq_root_power u hu
  have hpowerfix : (wittWordPower u d).rotate q = wittWordPower u d := by
    calc
      (wittWordPower u d).rotate q =
          (wittWordPower (wittWordPower v e) d).rotate q :=
        congr_arg (fun z => (wittWordPower z d).rotate q) hudecomp
      _ = (wittWordPower v (d * e)).rotate q :=
        congr_arg (fun z => z.rotate q) (wittWordPower_power v e d)
      _ = wittWordPower v (d * e) := by
        rw [show q = v.length by
          dsimp [q, v]
          exact (length_wittRoot u hu).symm]
        exact wittRotate_length_power v (d * e)
      _ = wittWordPower (wittWordPower v e) d := (wittWordPower_power v e d).symm
      _ = wittWordPower u d :=
        congr_arg (fun z => wittWordPower z d) hudecomp.symm
  have hwdecomp : w = wittWordPower u d := wittWord_eq_root_power w hw
  have hfix : w.rotate q = w := by
    calc
      w.rotate q = (wittWordPower u d).rotate q := congr_arg (fun z => z.rotate q) hwdecomp
      _ = wittWordPower u d := hpowerfix
      _ = w := hwdecomp.symm
  change IsPrimitiveWord u
  apply (wittIsPrimitiveWord_iff_period_eq_length hu).2
  apply le_antisymm (wittPeriod_le_length u hu)
  have hle : wittPeriod w hw ≤ q :=
    wittPeriod_min w hw (wittPeriod_pos u hu) hfix
  calc
    u.length = wittPeriod w hw := by
      dsimp [u]
      exact length_wittRoot w hw
    _ ≤ q := hle

/-- **Primitive words of given content.** For a natural number $r$ and natural numbers
$n_0, \dots, n_{r-1}$, the set of primitive words over the alphabet $\{0, \dots, r-1\}$ in which
each letter $i$ occurs exactly $n_i$ times. -/
def PrimitiveWordsOfContent {r : ℕ} (degree : Fin r → ℕ) :=
  {w : WordsOfContent degree // IsPrimitiveWord w.1}

instance {r : ℕ} (degree : Fin r → ℕ) : Finite (PrimitiveWordsOfContent degree) :=
  Finite.of_injective (fun w => w.1) fun _ _ h => Subtype.ext h

noncomputable instance {r : ℕ} (degree : Fin r → ℕ) :
    Fintype (PrimitiveWordsOfContent degree) :=
  Fintype.ofFinite _

private theorem wittRotate_injective {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsLyndonWord w) {i j : ℕ} (hi : i < w.length) (hj : j < w.length)
    (hrotate : w.rotate i = w.rotate j) : i = j := by
  have aux : ∀ {a b : ℕ}, a < b → b < w.length →
      w.rotate a = w.rotate b → False := by
    intro a b hab hb hrot
    have ha : a ≤ w.length := (hab.trans hb).le
    have heq₁ : a + (w.length - a) = w.length := Nat.add_sub_of_le ha
    have heq₂ : b + (w.length - a) = w.length + (b - a) := by omega
    have hfix : w.rotate (b - a) = w := by
      calc
        w.rotate (b - a) = (w.rotate w.length).rotate (b - a) := by
          rw [w.rotate_length]
        _ = w.rotate (w.length + (b - a)) := w.rotate_rotate _ _
        _ = w.rotate (b + (w.length - a)) := by rw [heq₂]
        _ = (w.rotate b).rotate (w.length - a) := (w.rotate_rotate _ _).symm
        _ = (w.rotate a).rotate (w.length - a) := by rw [hrot]
        _ = w.rotate (a + (w.length - a)) := w.rotate_rotate _ _
        _ = w := by rw [heq₁, w.rotate_length]
    have hlt := hw.2 (b - a) (by omega) (by omega)
    rw [hfix] at hlt
    exact (lt_irrefl _ hlt)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact aux hij hj hrotate
  · exact aux hji hi hrotate.symm

/-- **Lyndon words are primitive.** Every Lyndon word over a linearly ordered alphabet is
primitive. -/
theorem isPrimitiveWord_of_isLyndonWord {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsLyndonWord w) : IsPrimitiveWord w := by
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  refine ⟨hw.1, List.nodup_iff_injective_get.mpr ?_⟩
  intro i j hget
  apply Fin.ext
  apply wittRotate_injective hw
  · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
    exact i.2
  · rw [← List.length_cyclicPermutations_of_ne_nil w hw.1]
    exact j.2
  · simpa only [List.get_cyclicPermutations] using hget

private def wittMinRotation {α : Type*} [LinearOrder α] (w : List α) : List α :=
  w.cyclicPermutations.min (List.cyclicPermutations_ne_nil w)

private theorem wittMinRotation_isRotated {α : Type*} [LinearOrder α] (w : List α) :
    wittMinRotation w ~r w := by
  rw [← List.mem_cyclicPermutations_iff]
  exact List.min_mem (List.cyclicPermutations_ne_nil w)

private theorem wittMinRotation_isPrimitive {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsPrimitiveWord w) : IsPrimitiveWord (wittMinRotation w) := by
  let hrot := wittMinRotation_isRotated w
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  constructor
  · intro hnil
    have hwrot : w ~r [] := by simpa [hnil] using hrot.symm
    exact hw.1 (List.isRotated_nil_iff.mp hwrot)
  · exact hrot.cyclicPermutations.nodup_iff.mpr
      (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2

private theorem wittMinRotation_isLyndon {α : Type*} [LinearOrder α] {w : List α}
    (hw : IsPrimitiveWord w) : IsLyndonWord (wittMinRotation w) := by
  refine ⟨(wittMinRotation_isPrimitive hw).1, fun k hk0 hk => ?_⟩
  have hrot := wittMinRotation_isRotated w
  have hmem : (wittMinRotation w).rotate k ∈ w.cyclicPermutations := by
    rw [List.mem_cyclicPermutations_iff]
    exact (List.IsRotated.forall (wittMinRotation w) k).trans hrot
  have hle : wittMinRotation w ≤ (wittMinRotation w).rotate k :=
    List.min_le_of_mem hmem
  have hne := rotate_ne_of_isPrimitiveWord (wittMinRotation_isPrimitive hw) hk0 hk
  exact lt_of_le_of_ne hle hne.symm

private theorem wittWordContent_minRotation {r : ℕ} (w : List (Fin r)) :
    wittWordContent (wittMinRotation w) = wittWordContent w := by
  funext i
  exact (wittMinRotation_isRotated w).perm.count_eq i

private noncomputable def wittMinRotationIndex {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsPrimitiveWord w) : Fin w.length :=
  let k := Classical.choose (wittMinRotation_isRotated w)
  ⟨k % w.length, Nat.mod_lt k (List.length_pos_of_ne_nil hw.1)⟩

private theorem wittMinRotation_rotate_index {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsPrimitiveWord w) :
    (wittMinRotation w).rotate (wittMinRotationIndex hw) = w := by
  let hrot := wittMinRotation_isRotated w
  let k := Classical.choose hrot
  have hk : (wittMinRotation w).rotate k = w := Classical.choose_spec hrot
  have hlen : (wittMinRotation w).length = w.length := hrot.perm.length_eq
  change (wittMinRotation w).rotate (k % w.length) = w
  rw [← hlen, List.rotate_mod]
  exact hk

private theorem length_wordsOfContent {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) : w.1.length = ∑ i, degree i := by
  rw [← sum_wittWordContent, w.2]

private theorem wittWordContent_rotate {r : ℕ} (w : List (Fin r)) (k : ℕ) :
    wittWordContent (w.rotate k) = wittWordContent w := by
  funext i
  exact (List.rotate_perm w k).count_eq i

private theorem isPrimitiveWord_rotate {α : Type*} {w : List α}
    (hw : IsPrimitiveWord w) (k : ℕ) : IsPrimitiveWord (w.rotate k) := by
  let hrot := List.IsRotated.forall w k
  apply isPrimitiveWord_iff_nodup_cyclicPermutations.mpr
  constructor
  · exact List.rotate_eq_nil_iff.not.mpr hw.1
  · exact hrot.cyclicPermutations.nodup_iff.mpr
      (isPrimitiveWord_iff_nodup_cyclicPermutations.mp hw).2

private def wittRotateLyndon {r : ℕ} (degree : Fin r → ℕ) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) →
      PrimitiveWordsOfContent degree
  | ⟨w, k⟩ =>
      ⟨⟨w.1.1.rotate k, (wittWordContent_rotate w.1.1 k).trans w.1.2⟩,
        isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k⟩

private def wittPrimitiveMin {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) : LyndonWordsOfContent degree :=
  ⟨⟨wittMinRotation w.1.1, (wittWordContent_minRotation w.1.1).trans w.1.2⟩,
    wittMinRotation_isLyndon w.2⟩

private noncomputable def wittPrimitiveMinIndex {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) : Fin (∑ i, degree i) :=
  Fin.cast (length_wordsOfContent w.1) (wittMinRotationIndex w.2)

private noncomputable def wittPrimitiveToLyndonRotation {r : ℕ}
    {degree : Fin r → ℕ} (w : PrimitiveWordsOfContent degree) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) :=
  ⟨wittPrimitiveMin w, wittPrimitiveMinIndex w⟩

private theorem wittRotateLyndon_primitiveTo {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) :
    wittRotateLyndon degree (wittPrimitiveToLyndonRotation w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  change (wittMinRotation w.1.1).rotate (wittMinRotationIndex w.2) = w.1.1
  exact wittMinRotation_rotate_index w.2

private theorem eq_of_isLyndonWord_of_isRotated {α : Type*} [LinearOrder α]
    {u v : List α} (hu : IsLyndonWord u) (hv : IsLyndonWord v) (hrot : u ~r v) : u = v := by
  have le_of_rotated : ∀ {a b : List α}, IsLyndonWord a → a ~r b → a ≤ b := by
    intro a b ha hab
    obtain ⟨k, rfl⟩ := hab
    have hlen : 0 < a.length := List.length_pos_of_ne_nil ha.1
    by_cases hk0 : k % a.length = 0
    · rw [← List.rotate_mod, hk0, List.rotate_zero]
    · exact le_of_lt <| (List.rotate_mod a k) ▸
        ha.2 (k % a.length) (Nat.pos_of_ne_zero hk0) (Nat.mod_lt k hlen)
  exact le_antisymm (le_of_rotated hu hrot) (le_of_rotated hv hrot.symm)

private theorem wittMinRotation_rotate_eq_of_lyndon {α : Type*} [LinearOrder α]
    {w : List α} (hw : IsLyndonWord w) (k : ℕ) :
    wittMinRotation (w.rotate k) = w := by
  have hprimitive := isPrimitiveWord_of_isLyndonWord hw
  apply eq_of_isLyndonWord_of_isRotated
    (wittMinRotation_isLyndon (isPrimitiveWord_rotate hprimitive k)) hw
  exact (wittMinRotation_isRotated (w.rotate k)).trans (List.IsRotated.forall w k)

private theorem wittPrimitiveTo_rotateLyndon {r : ℕ} (degree : Fin r → ℕ)
    (p : LyndonWordsOfContent degree × Fin (∑ i, degree i)) :
    wittPrimitiveToLyndonRotation (wittRotateLyndon degree p) = p := by
  rcases p with ⟨w, k⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact wittMinRotation_rotate_eq_of_lyndon w.2 k
  · apply Fin.ext
    change (wittMinRotationIndex
      (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)).1 = k.1
    apply wittRotate_injective w.2
    · simpa using (wittMinRotationIndex
        (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)).2
    · rw [length_wordsOfContent w.1]
      exact k.2
    · have hrotate := wittMinRotation_rotate_index
          (isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k)
      rw [wittMinRotation_rotate_eq_of_lyndon w.2 k] at hrotate
      exact hrotate

private noncomputable def wittLyndonRotationEquivPrimitive {r : ℕ}
    (degree : Fin r → ℕ) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) ≃
      PrimitiveWordsOfContent degree where
  toFun := wittRotateLyndon degree
  invFun := wittPrimitiveToLyndonRotation
  left_inv := wittPrimitiveTo_rotateLyndon degree
  right_inv := wittRotateLyndon_primitiveTo

private theorem card_primitiveWords_eq_mul_lyndonWords {r : ℕ}
    (degree : Fin r → ℕ) :
    Fintype.card (PrimitiveWordsOfContent degree) =
      (∑ i, degree i) * Fintype.card (LyndonWordsOfContent degree) := by
  rw [← Fintype.card_congr (wittLyndonRotationEquivPrimitive degree)]
  simp [mul_comm]
private theorem wittGcd_ne_zero {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) : Finset.univ.gcd degree ≠ 0 := by
  rw [Finset.gcd_ne_zero_iff]
  by_contra h
  have hall : ∀ i ∈ Finset.univ, degree i = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i, hi, hne⟩
  have hzero : (∑ i, degree i) = 0 := Finset.sum_eq_zero hall
  omega

private theorem wittDegree_eq_exponent_mul_rootContent {r : ℕ}
    {degree : Fin r → ℕ} (w : WordsOfContent degree)
    (hdegree : 0 < ∑ i, degree i) :
    degree = fun i => wittExponent w.1 (wittWord_ne_nil w hdegree) *
      wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) i := by
  calc
    degree = wittWordContent w.1 := w.2.symm
    _ = wittWordContent (wittWordPower
        (wittRoot w.1 (wittWord_ne_nil w hdegree))
        (wittExponent w.1 (wittWord_ne_nil w hdegree))) :=
      congr_arg wittWordContent (wittWord_eq_root_power w.1 (wittWord_ne_nil w hdegree))
    _ = _ := wittWordContent_power _ _

private theorem wittRoot_content {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) =
      fun i => degree i / wittExponent w.1 (wittWord_ne_nil w hdegree) := by
  let d := wittExponent w.1 (wittWord_ne_nil w hdegree)
  have hd : 0 < d := wittExponent_pos w.1 (wittWord_ne_nil w hdegree)
  have hmul := wittDegree_eq_exponent_mul_rootContent w hdegree
  funext i
  have hi := congr_fun hmul i
  dsimp [d] at hd ⊢
  rw [hi]
  exact (Nat.mul_div_cancel_left _ hd).symm

private theorem wittExponent_dvd_gcd {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    wittExponent w.1 (wittWord_ne_nil w hdegree) ∣ Finset.univ.gcd degree := by
  apply Finset.dvd_gcd
  intro i _
  refine ⟨wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) i, ?_⟩
  exact congr_fun (wittDegree_eq_exponent_mul_rootContent w hdegree) i

private abbrev WittPrimitiveRootData {r : ℕ} (degree : Fin r → ℕ) :=
  Σ d : {d // d ∈ Nat.divisors (Finset.univ.gcd degree)},
    PrimitiveWordsOfContent (fun i => degree i / d.1)

private noncomputable def wittWordToRootData {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    WittPrimitiveRootData degree :=
  let hw := wittWord_ne_nil w hdegree
  let d := wittExponent w.1 hw
  ⟨⟨d, Nat.mem_divisors.mpr
      ⟨wittExponent_dvd_gcd w hdegree, wittGcd_ne_zero degree hdegree⟩⟩,
    ⟨⟨wittRoot w.1 hw, wittRoot_content w hdegree⟩, wittRoot_isPrimitive w.1 hw⟩⟩

private def wittRootDataToWord {r : ℕ} (degree : Fin r → ℕ)
    (p : WittPrimitiveRootData degree) : WordsOfContent degree :=
  ⟨wittWordPower p.2.1.1 p.1.1, by
    rw [wittWordContent_power, p.2.1.2]
    funext i
    have hdg : p.1.1 ∣ Finset.univ.gcd degree := (Nat.mem_divisors.mp p.1.2).1
    have hgd : Finset.univ.gcd degree ∣ degree i := Finset.gcd_dvd (Finset.mem_univ i)
    exact Nat.mul_div_cancel' (hdg.trans hgd)⟩

private theorem wittRootDataToWord_wordToRootData {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    wittRootDataToWord degree (wittWordToRootData degree hdegree w) = w := by
  apply Subtype.ext
  change wittWordPower
      (wittRoot w.1 (wittWord_ne_nil w hdegree))
      (wittExponent w.1 (wittWord_ne_nil w hdegree)) = w.1
  exact (wittWord_eq_root_power w.1 (wittWord_ne_nil w hdegree)).symm

private theorem wittPrimitiveWords_heq_of_word_eq {r : ℕ} {a b : Fin r → ℕ}
    {u : PrimitiveWordsOfContent a} {v : PrimitiveWordsOfContent b}
    (h : u.1.1 = v.1.1) : HEq u v := by
  have hab : a = b := by
    rw [← u.1.2, ← v.1.2, h]
  subst b
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  exact h

private theorem wittWordToRootData_rootDataToWord {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (p : WittPrimitiveRootData degree) :
    wittWordToRootData degree hdegree (wittRootDataToWord degree p) = p := by
  rcases p with ⟨⟨d, hdmem⟩, u⟩
  have hdg := (Nat.mem_divisors.mp hdmem).1
  have hgpos : 0 < Finset.univ.gcd degree :=
    Nat.pos_of_ne_zero (wittGcd_ne_zero degree hdegree)
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdg hgpos
  dsimp only [wittWordToRootData, wittRootDataToWord]
  have he : wittExponent (wittWordPower u.1.1 d) _ = d :=
    wittExponent_power_of_primitive u.2 hd
  apply Sigma.ext
  · exact Subtype.ext he
  · apply wittPrimitiveWords_heq_of_word_eq
    exact wittRoot_power_of_primitive u.2 hd

private noncomputable def wittWordsRootDataEquiv {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    WordsOfContent degree ≃ WittPrimitiveRootData degree where
  toFun := wittWordToRootData degree hdegree
  invFun := wittRootDataToWord degree
  left_inv := wittRootDataToWord_wordToRootData degree hdegree
  right_inv := wittWordToRootData_rootDataToWord degree hdegree

private theorem card_words_eq_sum_primitive {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    Fintype.card (WordsOfContent degree) =
      ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
        Fintype.card (PrimitiveWordsOfContent (fun i => degree i / d)) := by
  rw [Fintype.card_congr (wittWordsRootDataEquiv degree hdegree)]
  rw [Fintype.card_sigma]
  exact Finset.sum_attach (Nat.divisors (Finset.univ.gcd degree))
    (fun d => Fintype.card (PrimitiveWordsOfContent (fun i => degree i / d)))

private theorem wittGcd_div {r : ℕ} (degree : Fin r → ℕ) {k : ℕ}
    (hk : k ∣ Finset.univ.gcd degree) :
    Finset.univ.gcd (fun i => degree i / k) = Finset.univ.gcd degree / k := by
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_div_iff_mul_dvd hk).2
    apply Finset.dvd_gcd
    intro i _
    have hkdi : k ∣ degree i := hk.trans (Finset.gcd_dvd (Finset.mem_univ i))
    have hdiv := Nat.mul_dvd_mul_left k
      (Finset.gcd_dvd (s := Finset.univ) (f := fun j => degree j / k)
        (Finset.mem_univ i))
    simpa [Nat.mul_div_cancel' hkdi] using hdiv
  · apply Finset.dvd_gcd
    intro i _
    have hkdi : k ∣ degree i := hk.trans (Finset.gcd_dvd (Finset.mem_univ i))
    exact (Nat.div_dvd_div_iff_right hk hkdi).2
      (Finset.gcd_dvd (Finset.mem_univ i))

private theorem wittSum_div_pos {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) {k : ℕ} (hk0 : 0 < k)
    (hk : ∀ i, k ∣ degree i) : 0 < ∑ i, degree i / k := by
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hdegree
  apply Finset.sum_pos_iff.mpr
  exact ⟨i, Finset.mem_univ i, Nat.div_pos (Nat.le_of_dvd hi (hk i)) hk0⟩

private theorem card_primitiveWords_eq_moebius_sum {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    (Fintype.card (PrimitiveWordsOfContent degree) : ℤ) =
      ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
        ArithmeticFunction.moebius d *
          (Nat.multinomial Finset.univ (fun i => degree i / d) : ℤ) := by
  let g := Finset.univ.gcd degree
  let A : ℕ → ℤ := fun n =>
    Fintype.card (PrimitiveWordsOfContent (fun i => degree i / (g / n)))
  let C : ℕ → ℤ := fun n =>
    Fintype.card (WordsOfContent (fun i => degree i / (g / n)))
  have hg0 : g ≠ 0 := wittGcd_ne_zero degree hdegree
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hpremise : ∀ n > 0, n ∈ {n : ℕ | n ∣ g} →
      (∑ i ∈ n.divisors, A i) = C n := by
    intro n hn hnG
    let k := g / n
    let beta : Fin r → ℕ := fun i => degree i / k
    have hkG : k ∣ g := Nat.div_dvd_of_dvd hnG
    have hk0 : 0 < k := Nat.div_pos (Nat.le_of_dvd hgpos hnG) hn
    have hkdegree : ∀ i, k ∣ degree i := fun i =>
      hkG.trans (Finset.gcd_dvd (Finset.mem_univ i))
    have hbeta : 0 < ∑ i, beta i := wittSum_div_pos degree hdegree hk0 hkdegree
    have hgcdBeta : Finset.univ.gcd beta = n := by
      dsimp [beta]
      rw [wittGcd_div degree hkG]
      exact Nat.div_div_self hnG hg0
    have hcard := card_words_eq_sum_primitive beta hbeta
    rw [hgcdBeta] at hcard
    have hnat :
        (∑ i ∈ n.divisors,
          Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))) =
          Fintype.card (WordsOfContent beta) := by
      calc
        (∑ i ∈ n.divisors,
            Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))) =
            ∑ e ∈ n.divisors,
              Fintype.card (PrimitiveWordsOfContent
                (fun j => degree j / (g / (n / e)))) := by
          symm
          exact Nat.sum_div_divisors n fun i =>
            Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))
        _ = ∑ e ∈ n.divisors,
              Fintype.card (PrimitiveWordsOfContent (fun j => beta j / e)) := by
          apply Finset.sum_congr rfl
          intro e he
          have heN : e ∣ n := Nat.dvd_of_mem_divisors he
          have hden : g / (n / e) = k * e := by
            calc
              g / (n / e) = (k * n) / (n / e) := by
                congr 1
                exact (Nat.div_mul_cancel hnG).symm
              _ = k * (n / (n / e)) := Nat.mul_div_assoc k (Nat.div_dvd_of_dvd heN)
              _ = k * e := by rw [Nat.div_div_self heN hn.ne']
          have hfun : (fun j => degree j / (g / (n / e))) =
              (fun j => beta j / e) := by
            funext j
            dsimp [beta]
            rw [hden, Nat.div_div_eq_div_mul]
          rw [hfun]
        _ = Fintype.card (WordsOfContent beta) := hcard.symm
    change (∑ i ∈ n.divisors,
      (Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i))) : ℤ)) =
        (Fintype.card (WordsOfContent beta) : ℤ)
    exact_mod_cast hnat
  have hinversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      {n : ℕ | n ∣ g} (fun _ _ hmn hnG => hmn.trans hnG)).mp hpremise g hgpos
      (dvd_refl g)
  calc
    (Fintype.card (PrimitiveWordsOfContent degree) : ℤ) = A g := by
      simp [A, Nat.div_self hgpos]
    _ = ∑ x ∈ g.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * C x.2 := hinversion.symm
    _ = ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d * C (g / d) := by
      exact Nat.sum_divisorsAntidiagonal fun d e =>
        ArithmeticFunction.moebius d * C e
    _ = ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d *
          (Nat.multinomial Finset.univ (fun i => degree i / d) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdG : d ∣ g := Nat.dvd_of_mem_divisors hd
      congr 1
      dsimp [C]
      rw [Nat.div_div_self hdG hg0]
      exact_mod_cast card_wordsOfContent_eq_multinomial (fun i => degree i / d)

/-- **Witt's formula for the number of Lyndon words of given content.** Let $r$ be a natural
number and let $n_0, \dots, n_{r-1}$ be natural numbers with $n = n_0 + \dots + n_{r-1} > 0$.
Order the alphabet $\{0, \dots, r-1\}$ as the natural numbers and order words over it
lexicographically. Then the number of Lyndon words over this alphabet in which each letter $i$
occurs exactly $n_i$ times equals, as a rational number, Witt's multigraded value
$M(n_0, \dots, n_{r-1}) = \frac{1}{n} \sum_{d \mid g} \mu(d) \binom{n/d}{n_0/d, \ldots, n_{r-1}/d}$,
where $g = \gcd(n_0, \dots, n_{r-1})$, the sum runs over the positive divisors $d$ of $g$, and
$\mu$ is the Möbius function. -/
theorem card_lyndonWordsOfContent_eq_wittMultigradedValue {r : ℕ}
    (degree : Fin r → ℕ) (hdegree : 0 < ∑ i, degree i) :
    (Fintype.card (LyndonWordsOfContent degree) : ℚ) = wittMultigradedValue degree := by
  let n := ∑ i, degree i
  have hn : 0 < n := hdegree
  have hmobZ := card_primitiveWords_eq_moebius_sum degree hdegree
  have hmobQ :
      (Fintype.card (PrimitiveWordsOfContent degree) : ℚ) =
        ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
            (Nat.multinomial Finset.univ (fun i => degree i / d) : ℚ) := by
    exact_mod_cast hmobZ
  have horbit :
      (Fintype.card (PrimitiveWordsOfContent degree) : ℚ) =
        (n : ℚ) * Fintype.card (LyndonWordsOfContent degree) := by
    exact_mod_cast card_primitiveWords_eq_mul_lyndonWords degree
  rw [wittMultigradedValue]
  change (Fintype.card (LyndonWordsOfContent degree) : ℚ) =
    if n = 0 then 0 else (1 / (n : ℚ)) * _
  rw [ite_eq_right hn.ne']
  rw [← hmobQ, horbit]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ hnq, one_mul]

end MetaMathlibExt
