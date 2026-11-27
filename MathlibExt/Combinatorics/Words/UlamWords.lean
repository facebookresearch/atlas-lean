/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Defs

import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Logic.Equiv.Bool

/-!
# Binary Ulam words

Statements from Paul Adutwum, Hopper Clark, Ro Emerson, Alexandra (Sasha) Sheydvasser,
Arseniy (Senia) Sheydvasser, and Axelle Tougouma, *Distributions of Ulam Words up to Length
30*, INTEGERS 25 (2025), Article A102 (arXiv:2410.01217v2).

Words over `{0, 1}` are `List Bool` with `false = 0`, `true = 1`. Following Bade, Cui,
Labelle, and Li (as quoted in Section 1 of the paper), `0` and `1` are Ulam, and a word
`w ≠ 0, 1` is Ulam iff there is exactly one pair of Ulam words `u₁ ≠ u₂` with `w = u₁ u₂`.
The integer `π(w)` of a word is its binary value, most significant letter first, written
`Nat.ofDigits 2 (w.reverse.map Bool.toNat)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fuel-bounded Ulam test.** For a natural number $f$ (the fuel) and a word $w$ in the letters
$0$ and $1$, the test returns false when $f = 0$. With fuel $f + 1$ it returns true when $w$ has
length $1$; otherwise it returns true exactly when there is exactly one $k$ with
$1 \le k < |w|$ such that the prefix $w_1 \cdots w_k$ and the suffix $w_{k+1} \cdots w_{|w|}$
are distinct and both pass the test with fuel $f$.

This is the Ulam recursion: with fuel at least $|w|$, the test decides whether $w$ is an Ulam
word.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def ulamWordAux : ℕ → List Bool → Bool
  | 0, _ => false
  | f + 1, w =>
    if w.length = 1 then true
    else
      ((List.range (w.length - 1)).countP fun k =>
        w.take (k + 1) != w.drop (k + 1) && ulamWordAux f (w.take (k + 1)) &&
          ulamWordAux f (w.drop (k + 1))) == 1

/-- **Ulam words.** Ulam words are finite words over the alphabet $\{0, 1\}$, defined by
recursion on the length. The empty word is not an Ulam word, and the two words $0$ and $1$ of
length $1$ are Ulam words. A word $w$ of length at least $2$ is an Ulam word if and only if there
is exactly one way to write $w = uv$ with $u$ and $v$ nonempty, distinct Ulam words.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(definition of Ulam words, after Bade, Cui, Labelle, and Li). -/
public def IsUlamWord (w : List Bool) : Prop :=
  ulamWordAux w.length w = true

/-- Ulam-ness is decidable.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public instance instDecidablePredListBoolIsUlamWord : DecidablePred IsUlamWord := fun w =>
  inferInstanceAs (Decidable (ulamWordAux w.length w = true))

/-- **Ulam words of length at most three.** The empty word is not an Ulam word, and both words
$0$ and $1$ of length one are Ulam words. The Ulam words of length two are exactly $01$ and $10$,
and the Ulam words of length three are exactly $001$, $011$, $100$ and $110$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem isUlamWord_small :
    IsUlamWord [false] ∧ IsUlamWord [true] ∧ ¬ IsUlamWord [] ∧
      ¬ IsUlamWord [false, false] ∧ IsUlamWord [false, true] ∧ IsUlamWord [true, false] ∧
      ¬ IsUlamWord [true, true] ∧
      ¬ IsUlamWord [false, false, false] ∧ IsUlamWord [false, false, true] ∧
      ¬ IsUlamWord [false, true, false] ∧ IsUlamWord [false, true, true] ∧
      IsUlamWord [true, false, false] ∧ ¬ IsUlamWord [true, false, true] ∧
      IsUlamWord [true, true, false] ∧ ¬ IsUlamWord [true, true, true] := by
  decide

/-- **Ulam words of length four: examples.** The words $0001$ and $1011$ are Ulam words, while
$0011$ and $0110$ are not.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₄`). -/
public theorem isUlamWord_length_four_examples :
    IsUlamWord [false, false, false, true] ∧ ¬ IsUlamWord [false, false, true, true] ∧
      IsUlamWord [true, false, true, true] ∧ ¬ IsUlamWord [false, true, true, false] := by
  decide

/-- **Number of Ulam words of a given length.** For a natural number $n$, $\#U_n$ denotes the
number of Ulam words of length $n$, that is, of words $w_1 \cdots w_n$ of length $n$ in the
letters $0$ and $1$ that are Ulam words.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public def ulamWordCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).card

/-- **Numbers of short Ulam words.** There are $2$, $2$, $4$ and $8$ Ulam words of length $1$,
$2$, $3$ and $4$ respectively: $\#U_1 = 2$, $\#U_2 = 2$, $\#U_3 = 4$ and $\#U_4 = 8$, where
$\#U_n$ is the number of Ulam words of length $n$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(displayed `U₁, …, U₄`). -/
public theorem ulamWordCount_small :
    ulamWordCount 1 = 2 ∧ ulamWordCount 2 = 2 ∧ ulamWordCount 3 = 4 ∧ ulamWordCount 4 = 8 := by
  decide

/-- **Ulam words in a residue class.** For natural numbers $N$ and $n$ and a residue class
$a \in \mathbb{Z}/N\mathbb{Z}$, this is the number of Ulam words $w$ of length $n$ in the letters
$0$ and $1$ whose binary value $\pi(w)$, read with the most significant letter first, lies in the
class $a$ modulo $N$. For $N = 0$, $\mathbb{Z}/0\mathbb{Z}$ is $\mathbb{Z}$ and the condition is
$\pi(w) = a$.

The paper's relative density $\rho_{a,N}(n)$ is this number divided by the number $\#U_n$ of
Ulam words of length $n$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 3, definition of `ρ_{a,N}(n)`). -/
public def ulamResidueCount (N n : ℕ) (a : ZMod N) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool =>
    IsUlamWord (List.ofFn v) ∧
      ((Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat) : ℕ) : ZMod N) = a).card

/-- **Residues of the Ulam words of length 2 modulo 3.** Read the Ulam words of length $2$ as
binary numerals, most significant letter first. None of their values is congruent to $0$ modulo
$3$, exactly one is congruent to $1$, and exactly one is congruent to $2$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 6. -/
public theorem ulamResidueCount_three_two :
    ulamResidueCount 3 2 0 = 0 ∧ ulamResidueCount 3 2 1 = 1 ∧ ulamResidueCount 3 2 2 = 1 := by
  decide

namespace isUlamWord_map_not_and_ulamResidueCount_eq

-- Complementation commutes with taking each factor of a cut and reflects their inequality.
private theorem aux_map_not (f : ℕ) (w : List Bool) :
    ulamWordAux f (w.map not) = ulamWordAux f w := by
  induction f generalizing w with
  | zero => rfl
  | succ f ih =>
    simp only [ulamWordAux, List.length_map]
    split
    · rfl
    · apply congrArg (· == 1)
      apply List.countP_congr
      intro k _
      simp only [← List.map_take, ← List.map_drop, ih, Bool.and_eq_true, bne_iff_ne,
        (List.map_injective_iff.mpr Bool.not_injective).ne_iff]

-- Read the digits least significant first, as in Nat.ofDigits.
private theorem ofDigits_not_add (w : List Bool) :
    Nat.ofDigits 2 ((w.map not).map Bool.toNat) + Nat.ofDigits 2 (w.map Bool.toNat) + 1 =
      2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    cases b <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false] <;>
      omega

private theorem card_complement (N n : ℕ) (a : ZMod N) :
    ulamResidueCount N n a = ulamResidueCount N n (2 ^ n - 1 - a) := by
  unfold ulamResidueCount
  apply Finset.card_equiv (Equiv.piCongrRight fun _ => Equiv.boolNot)
  intro v
  have hsum := congrArg (Nat.cast : ℕ → ZMod N) (ofDigits_not_add (List.ofFn v).reverse)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, List.length_reverse,
    List.length_ofFn] at hsum
  have hword : List.ofFn ((Equiv.piCongrRight fun _ => Equiv.boolNot) v) =
      (List.ofFn v).map not := (List.map_ofFn (g := not) (f := v)).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [hword, IsUlamWord, List.length_map, aux_map_not,
    ← List.map_reverse (f := not)]
  rw [eq_sub_iff_add_eq.mpr (eq_sub_iff_add_eq.mpr hsum), sub_right_inj]

end isUlamWord_map_not_and_ulamResidueCount_eq

open isUlamWord_map_not_and_ulamResidueCount_eq in
/-- **Complement symmetry of Ulam words.** For a word $w$ over $\{0, 1\}$, let $\bar w$ be its
complement (every letter swapped) and let $\pi(w)$ be the integer whose binary expansion is $w$,
most significant letter first. If $w$ is an Ulam word of length $n$, then $\bar w$ is an Ulam
word and $\pi(\bar w) + \pi(w) = 2^n - 1$. Moreover, for all natural numbers $N$ and $n$ and every
$a \in \mathbb{Z}/N\mathbb{Z}$, the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ equals the number of Ulam words $w$ of length $n$ with
$\pi(w) \equiv 2^n - 1 - a \pmod N$.

For $n \ge 1$, writing $\rho_{a,N}(n)$ for the proportion of Ulam words $w$ of length $n$ with
$\pi(w) \equiv a \pmod N$ among all Ulam words of length $n$, the second statement says
$\rho_{a,N}(n) = \rho_{2^n-1-a,N}(n)$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 11. -/
public theorem isUlamWord_map_not_and_ulamResidueCount_eq :
    (∀ w : List Bool, IsUlamWord w →
      IsUlamWord (w.map not) ∧
        Nat.ofDigits 2 ((w.map not).reverse.map Bool.toNat) +
            Nat.ofDigits 2 (w.reverse.map Bool.toNat) = 2 ^ w.length - 1) ∧
      ∀ (N n : ℕ) (a : ZMod N),
        ulamResidueCount N n a = ulamResidueCount N n (2 ^ n - 1 - a) := by
  refine ⟨?_, card_complement⟩
  intro w hw
  constructor
  · simpa only [IsUlamWord, List.length_map, aux_map_not] using hw
  · simpa only [List.map_reverse (f := not), List.length_reverse] using
      Nat.eq_sub_of_add_eq (ofDigits_not_add w.reverse)

/-- **Residue symmetries of Ulam words modulo 2 and 3.** For natural numbers $N$ and $n$ and a
residue $a \in \mathbb{Z}/N\mathbb{Z}$, let $c_{a,N}(n)$ be the number of Ulam words of length
$n$ whose value as a binary numeral, most significant letter first, is congruent to $a$ modulo
$N$. Then for every $n \ge 1$ we have $c_{0,2}(n) = c_{1,2}(n)$, and for every
$a \in \mathbb{Z}/3\mathbb{Z}$ we have $c_{a,3}(n) = c_{-a,3}(n)$ if $n$ is even and
$c_{a,3}(n) = c_{1-a,3}(n)$ if $n$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102,
Corollary 2. -/
public theorem ulamResidueCount_mod_two_three (n : ℕ) (hn : 1 ≤ n) :
    ulamResidueCount 2 n 0 = ulamResidueCount 2 n 1 ∧
      ∀ a : ZMod 3, ulamResidueCount 3 n a =
        if Even n then ulamResidueCount 3 n (-a) else ulamResidueCount 3 n (1 - a) := by
  constructor
  · simpa only [show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : n ≠ 0),
      sub_zero, show (0 : ZMod 2) - 1 = 1 by decide] using
      isUlamWord_map_not_and_ulamResidueCount_eq.2 2 n 0
  · intro a
    rw [isUlamWord_map_not_and_ulamResidueCount_eq.2 3 n a,
      show (2 : ZMod 3) = -1 by decide, neg_one_pow_eq_ite]
    split <;> simp [show (-1 : ZMod 3) - 1 = 1 by decide]

/-- **Sorted binary values of Ulam words.** For a natural number $n$, this is the list
$u_1 < u_2 < \dots < u_k$ of the distinct binary values $\pi(w)$, read with the most significant
letter first, of the Ulam words $w$ of length $n$, in increasing order.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, ordered elements of `π(U_n)`). -/
public def ulamValuesSorted (n : ℕ) : List ℕ :=
  ((Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)).image
    fun v => Nat.ofDigits 2 ((List.ofFn v).reverse.map Bool.toNat)).sort (· ≤ ·)

/-- **Binary values of the Ulam words of length 3.** The increasing list of the distinct binary
values $\pi(w)$, read with the most significant letter first, of the Ulam words $w$ of length $3$
has exactly the entries $1, 3, 4, 6$.

These values come from the Ulam words $001$, $011$, $100$, $110$ of length $3$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1. -/
public theorem ulamValuesSorted_three :
    (ulamValuesSorted 3).toFinset = {1, 3, 4, 6} := by
  rw [ulamValuesSorted, Finset.sort_toFinset]
  decide

/-- **Mean gap of the Ulam values.** For $n \in \mathbb{N}$, read each Ulam word of length $n$
as a binary numeral, most significant letter first, and list the resulting values in increasing
order as $u_1 < u_2 < \dots < u_k$. The mean gap of these values is the rational number
$$\mu_g(n) = \frac{1}{k - 1} \sum_{i=1}^{k-1} (u_{i+1} - u_i),$$
where a quotient by $0$ is read as $0$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 1
(Conjecture 2, `μ_g(n)` as the mean of the gap distribution `p_n`). -/
public def ulamGapMean (n : ℕ) : ℚ :=
  (((List.zipWith (fun a b : ℕ => b - a) (ulamValuesSorted n)
      (ulamValuesSorted n).tail).sum : ℕ) : ℚ) /
    (((ulamValuesSorted n).length : ℚ) - 1)

/-- **Stages of the discrete Sierpiński triangle.** The stages
$S_n \subseteq \mathbb{N} \times \mathbb{N}$ of the discrete Sierpiński triangle are defined by
$S_0 = \{(2, 1)\}$ and $S_{n+1} = S_n \cup (S_n + (2^n, 0)) \cup (S_n + (2^n, 2^n))$, where
$S + (u, v) = \{(x + u, y + v) : (x, y) \in S\}$ denotes a translate.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4
(recursive definition of `S_n`). -/
public def discreteSierpinskiStage : ℕ → Set (ℕ × ℕ)
  | 0 => {(2, 1)}
  | n + 1 =>
    discreteSierpinskiStage n ∪ (fun p => (p.1 + 2 ^ n, p.2)) '' discreteSierpinskiStage n ∪
      (fun p => (p.1 + 2 ^ n, p.2 + 2 ^ n)) '' discreteSierpinskiStage n

/-- **The discrete Sierpiński triangle.** The discrete Sierpiński triangle is the set
$\mathcal{S} = \bigcup_{n \ge 0} S_n \subseteq \mathbb{N} \times \mathbb{N}$, the union of all the
stages $S_n$ of the discrete Sierpiński triangle.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public def discreteSierpinski : Set (ℕ × ℕ) :=
  ⋃ n, discreteSierpinskiStage n

/-- **The first stage of the discrete Sierpiński triangle.** The stage $S_1$ of the discrete
Sierpiński triangle is $\{(2, 1), (3, 1), (3, 2)\}$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Section 4. -/
public theorem discreteSierpinskiStage_one :
    discreteSierpinskiStage 1 = {(2, 1), (3, 1), (3, 2)} := by
  ext p
  simp only [discreteSierpinskiStage, Set.image_singleton, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  norm_num
  tauto

namespace isUlamWord_three_ones_zeros_iff

-- In a constant word the two factors of any successful split would both be the same singleton.
private theorem length_eq_one_of_replicate {f n : ℕ} {c : Bool}
    (h : ulamWordAux f (List.replicate n c) = true) : n = 1 := by
  induction f generalizing n with
  | zero => simp [ulamWordAux] at h
  | succ f ih =>
    by_contra hn
    simp only [ulamWordAux, List.length_replicate, ite_eq_right hn, beq_iff_eq] at h
    obtain ⟨k, _, hk⟩ := List.countP_pos_iff.mp (h ▸ Nat.zero_lt_one)
    simp only [List.take_replicate, List.drop_replicate, Bool.and_eq_true, bne_iff_ne] at hk
    obtain ⟨⟨hne, hl⟩, hr⟩ := hk
    exact hne (by rw [ih hl, ih hr])

-- When only the two endpoints can contribute, the split count is the sum of their indicators.
private theorem count_ends (p : ℕ → Bool) {s : ℕ} (hs : s ≠ 0)
    (h : ∀ k, 0 < k → k < s → ¬p k) :
    (List.range (s + 1)).countP p = (if p 0 then 1 else 0) + (if p s then 1 else 0) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  rw [List.range_succ, List.countP_append, List.countP_singleton, List.range_succ_eq_map,
    List.countP_cons, List.countP_map]
  have hm : (List.range t).countP (p ∘ Nat.succ) = 0 :=
    List.countP_eq_zero.mpr fun k hk =>
      h (k + 1) (by omega) (Nat.succ_lt_succ (List.mem_range.mp hk))
  rw [hm, Nat.zero_add]

private abbrev block (a b : ℕ) := List.replicate a true ++ List.replicate b false

-- A mixed block of length at least three has two different endpoint cuts. Every interior cut
-- has a constant factor of length at least two.
private theorem block_succ (a b : ℕ) (hab : a + b ≠ 0) :
    IsUlamWord (block (a + 1) (b + 1)) ↔
      (IsUlamWord (block a (b + 1)) ↔ ¬IsUlamWord (block (a + 1) b)) := by
  let w := block (a + 1) (b + 1)
  let p (k : ℕ) := w.take (k + 1) != w.drop (k + 1) &&
    ulamWordAux (a + b + 1) (w.take (k + 1)) && ulamWordAux (a + b + 1) (w.drop (k + 1))
  have hw : w.length = a + b + 1 + 1 := by simp [w, block]; omega
  have hmid (k : ℕ) (hk : 0 < k) (hs : k < a + b) : ¬p k := by
    intro hp
    simp only [p, Bool.and_eq_true] at hp
    obtain ⟨⟨_, hl⟩, hr⟩ := hp
    by_cases h : k + 1 ≤ a + 1
    · have ht : w.take (k + 1) = List.replicate (k + 1) true := by
        rw [show w = _ ++ _ from rfl, List.take_append_of_le_length (by simpa using h)]
        simp [Nat.min_eq_left h]
      rw [ht] at hl
      have := length_eq_one_of_replicate hl
      omega
    · have hd : w.drop (k + 1) = List.replicate (b + 1 - (k - a)) false := by
        simp [w, block, List.drop_append, Nat.sub_eq_zero_of_le (by omega : a + 1 ≤ k + 1)]
      rw [hd] at hr
      have := length_eq_one_of_replicate hr
      omega
  have hsingle (c : Bool) : ulamWordAux (a + b + 1) [c] = true := rfl
  have hfirst : p 0 ↔ IsUlamWord (block a (b + 1)) := by
    have hlen : (block a (b + 1)).length = a + b + 1 := by simp [block, Nat.add_assoc]
    have hne : [true] ≠ block a (b + 1) := by
      apply ne_of_apply_ne List.length
      simp only [hlen, List.length_singleton]
      omega
    change ([true] != block a (b + 1) && ulamWordAux (a + b + 1) [true] &&
      ulamWordAux (a + b + 1) (block a (b + 1))) = true ↔ _
    simp [IsUlamWord, hlen, hsingle, hne]
  have hlast : p (a + b) ↔ IsUlamWord (block (a + 1) b) := by
    have hlen : (block (a + 1) b).length = a + b + 1 := by simp [block]; omega
    have hne : block (a + 1) b ≠ [false] := by
      apply ne_of_apply_ne List.length
      simp only [hlen, List.length_singleton]
      omega
    have hend : w = block (a + 1) b ++ [false] := by
      simp only [w, block, List.replicate_succ' (n := b), List.append_assoc]
    simp only [p, hend, ← hlen, List.take_append_length, List.drop_append_length]
    rw [hlen]
    simp [IsUlamWord, hlen, hsingle, hne]
  change ulamWordAux w.length w = true ↔ _
  rw [hw, ulamWordAux, ite_eq_right (by omega : w.length ≠ 1)]
  change ((List.range (w.length - 1)).countP p == 1) = true ↔ _
  rw [hw, Nat.add_one_sub_one, count_ends p hab hmid, beq_iff_eq, ← hfirst, ← hlast]
  cases p 0 <;> cases p (a + b) <;> decide

private theorem one_leading (b : ℕ) : IsUlamWord (block 1 b) := by
  induction b with
  | zero => decide
  | succ b ih =>
    cases b with
    | zero => decide
    | succ b =>
      apply (block_succ 0 (b + 1) (by omega)).2
      have hzeros : ¬IsUlamWord (block 0 (b + 2)) := by
        intro h
        have := length_eq_one_of_replicate (n := b + 2) (c := false) h
        omega
      simp [hzeros, ih]

private theorem two_leading (b : ℕ) : IsUlamWord (block 2 b) ↔ b % 2 = 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [block_succ 1 b (by omega), ih]
    simp only [one_leading, true_iff]
    omega

private theorem three_leading (b : ℕ) :
    IsUlamWord (block 3 b) ↔ (b + 3) % 4 = 0 ∨ (b + 3) % 4 = 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [block_succ 2 b (by omega), two_leading, ih]
    omega

end isUlamWord_three_ones_zeros_iff

/-- **Ulam words with three leading ones.** For every $n \ge 3$, the word $1^3 0^{n-3}$ (three
ones followed by $n - 3$ zeros) is an Ulam word if and only if $n \equiv 0 \pmod 4$ or
$n \equiv 1 \pmod 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 3. -/
public theorem isUlamWord_three_ones_zeros_iff (n : ℕ) (hn : 3 ≤ n) :
    IsUlamWord (List.replicate 3 true ++ List.replicate (n - 3) false) ↔
      n % 4 = 0 ∨ n % 4 = 1 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa only [Nat.add_sub_cancel] using isUlamWord_three_ones_zeros_iff.three_leading b

namespace isUlamWord_zeros_four_ones_zeros_iff

open isUlamWord_three_ones_zeros_iff

-- Every proper cut shortens the word, so extra fuel cannot affect the result.
private theorem aux_eq {w : List Bool} (f g : ℕ) (hf : w.length ≤ f) (hg : w.length ≤ g) :
    ulamWordAux f w = ulamWordAux g w := by
  cases w with
  | nil => cases f <;> cases g <;> rfl
  | cons c w =>
    have hw : 0 < (c :: w).length := Nat.succ_pos _
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
    rw [ulamWordAux, ulamWordAux]
    split
    · rfl
    · apply congrArg (· == 1)
      apply List.countP_congr
      intro k hk
      have hk' := List.mem_range.mp hk
      have ht := List.length_take (i := k + 1) (l := c :: w)
      have hd := List.length_drop (i := k + 1) (l := c :: w)
      rw [aux_eq (w := (c :: w).take (k + 1)) f g (by omega) (by omega),
        aux_eq (w := (c :: w).drop (k + 1)) f g (by omega) (by omega)]
termination_by f

private def cut (w : List Bool) (k : ℕ) : Bool :=
  decide (w.take (k + 1) ≠ w.drop (k + 1) ∧
    IsUlamWord (w.take (k + 1)) ∧ IsUlamWord (w.drop (k + 1)))

private theorem cut_iff (w : List Bool) (k : ℕ) :
    cut w k ↔ w.take (k + 1) ≠ w.drop (k + 1) ∧
      IsUlamWord (w.take (k + 1)) ∧ IsUlamWord (w.drop (k + 1)) :=
  decide_eq_true_iff

private theorem cut_append {w u v : List Bool} {k : ℕ} (hw : w = u ++ v)
    (hk : k + 1 = u.length) : cut w k ↔ u ≠ v ∧ IsUlamWord u ∧ IsUlamWord v := by
  rw [cut_iff, hw, hk, List.take_append_length, List.drop_append_length]

private theorem count_cuts {w : List Bool} (hw : 2 ≤ w.length) :
    IsUlamWord w ↔ (List.range (w.length - 1)).countP (cut w) = 1 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length ≠ 0)
  rw [IsUlamWord, hn, ulamWordAux, ite_eq_right (by omega), beq_iff_eq, ← hn]
  apply iff_of_eq
  apply congrArg (· = 1)
  apply List.countP_congr
  intro k hk
  have hk' := List.mem_range.mp hk
  have ht := List.length_take (i := k + 1) (l := w)
  have hd := List.length_drop (i := k + 1) (l := w)
  rw [cut_iff]
  simp only [IsUlamWord, Bool.and_eq_true, bne_iff_ne, and_assoc]
  rw [aux_eq (w := w.take (k + 1)) n _ (by omega) (Nat.le_refl _),
    aux_eq (w := w.drop (k + 1)) n _ (by omega) (Nat.le_refl _)]

-- Reversal exchanges the cuts k and |w| - 2 - k, with the factors in opposite order.
private theorem aux_reverse (f : ℕ) (w : List Bool) :
    ulamWordAux f w.reverse = ulamWordAux f w := by
  induction f generalizing w with
  | zero => rfl
  | succ f ih =>
    simp only [ulamWordAux, List.length_reverse]
    split
    · rfl
    · apply congrArg (· == 1)
      conv_rhs => rw [← List.countP_reverse, List.range_eq_range', List.reverse_range']
      rw [List.countP_map]
      apply List.countP_congr
      intro k hk
      have hk' := List.mem_range.mp hk
      simp only [Function.comp_apply, Nat.zero_add, List.take_reverse, List.drop_reverse,
        ih, Bool.and_eq_true, bne_iff_ne, ne_eq, List.reverse_inj]
      rw [show w.length - 1 - 1 - k + 1 = w.length - (k + 1) by omega]
      tauto

private theorem ulam_reverse (w : List Bool) : IsUlamWord w.reverse ↔ IsUlamWord w := by
  simp only [IsUlamWord, List.length_reverse, aux_reverse]

private theorem four_leading (b : ℕ) : IsUlamWord (block 4 (b + 1)) ↔ (b + 1) % 4 = 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [block_succ 3 (b + 1) (by omega), three_leading, ih]
    omega

end isUlamWord_zeros_four_ones_zeros_iff

namespace isUlamWord_zeros_two_ones_zeros_iff

open isUlamWord_three_ones_zeros_iff isUlamWord_zeros_four_ones_zeros_iff

private abbrev padded (a n b : ℕ) :=
  List.replicate a false ++ List.replicate n true ++ List.replicate b false

private theorem middle_cut (a b i j : ℕ) :
    cut (padded (a + 1) (i + (j + 1)) (b + 1)) (a + i) ↔
      IsUlamWord (block i (a + 1)) ∧ IsUlamWord (block (j + 1) (b + 1)) := by
  let u := List.replicate (a + 1) false ++ List.replicate i true
  let v := block (j + 1) (b + 1)
  have hw : padded (a + 1) (i + (j + 1)) (b + 1) = u ++ v := by
    simp only [u, v, padded, block, List.replicate_add, List.append_assoc]
  have hne : u ≠ v := by simp [u, v, block, List.replicate_succ]
  have hu : (block i (a + 1)).reverse = u := by simp [block, u]
  rw [cut_append (u := u) (v := v) hw (by simp [u]; omega), and_iff_right hne, ← hu,
    ulam_reverse]

private theorem outer_cuts (a n b : ℕ) :
    (cut (padded (a + 1) (n + 1) (b + 1)) 0 ↔ IsUlamWord (padded a (n + 1) (b + 1))) ∧
    (cut (padded (a + 1) (n + 1) (b + 1)) (a + (n + 1) + b) ↔
      IsUlamWord (padded (a + 1) (n + 1) b)) := by
  have hs : IsUlamWord [false] := by decide
  constructor
  · have hne : [false] ≠ padded a (n + 1) (b + 1) := by
      apply ne_of_apply_ne List.length
      simp [padded]
      omega
    have hw : padded (a + 1) (n + 1) (b + 1) = [false] ++ padded a (n + 1) (b + 1) := rfl
    rw [cut_append (k := 0) hw rfl, and_iff_right hne, and_iff_right hs]
  · have hne : padded (a + 1) (n + 1) b ≠ [false] := by
      apply ne_of_apply_ne List.length
      simp [padded]
      omega
    have hw : padded (a + 1) (n + 1) (b + 1) = padded (a + 1) (n + 1) b ++ [false] := by
      simp only [padded, List.replicate_succ' (n := b), List.append_assoc]
    rw [cut_append hw (by simp [padded]; omega), and_iff_right hne, and_iff_left hs]

private theorem other_cuts (a n b : ℕ) :
    (∀ k < a, ¬cut (padded (a + 1) n (b + 1)) (k + 1)) ∧
    (∀ k < b, ¬cut (padded (a + 1) n (b + 1)) (a + n + k)) := by
  constructor
  · intro k hk h
    have ht := ((cut_iff _ _).mp h).2.1
    have he : (padded (a + 1) n (b + 1)).take (k + 2) = List.replicate (k + 2) false := by
      rw [padded, List.append_assoc, List.take_append_of_le_length (by simp; omega)]
      simp [Nat.min_eq_left (by omega : k + 2 ≤ a + 1)]
    rw [he] at ht
    have := length_eq_one_of_replicate ht
    omega
  · intro k hk h
    have hd := ((cut_iff _ _).mp h).2.2
    have he : (padded (a + 1) n (b + 1)).drop (a + n + k + 1) =
        List.replicate (b + 1 - k) false := by
      rw [padded, List.drop_append]
      simp only [List.length_append, List.length_replicate, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by simp; omega), List.nil_append,
        show a + n + k + 1 - (a + 1 + n) = k by omega]
    rw [he] at hd
    have := length_eq_one_of_replicate hd
    omega

-- With zeros at both ends, only the two singleton-zero cuts and the cuts strictly
-- inside the block of ones can contribute to the count.
private theorem padded_iff (a n b : ℕ) :
    IsUlamWord (padded (a + 1) (n + 1) (b + 1)) ↔
      (if IsUlamWord (padded a (n + 1) (b + 1)) then 1 else 0) +
      (List.range n).countP (fun k => cut (padded (a + 1) (n + 1) (b + 1)) (a + 1 + k)) +
      (if IsUlamWord (padded (a + 1) (n + 1) b) then 1 else 0) = 1 := by
  let w := padded (a + 1) (n + 1) (b + 1)
  have hindex : a + 1 + n = a + (n + 1) := by omega
  have h := other_cuts a (n + 1) b
  have hleft : (List.range a).countP (cut w ∘ Nat.succ) = 0 :=
    List.countP_eq_zero.mpr fun k hk => h.1 k (List.mem_range.mp hk)
  have hright : (List.range b).countP (cut w ∘ (a + 1 + n + ·)) = 0 :=
    List.countP_eq_zero.mpr fun k hk => by
      simpa only [Function.comp_apply, hindex, w] using h.2 k (List.mem_range.mp hk)
  change IsUlamWord w ↔ _
  rw [count_cuts (by simp [w]; omega),
    show w.length - 1 = a + 1 + n + (b + 1) by simp [w]; omega,
    List.range_add, List.countP_append, List.countP_map, List.range_add,
    List.countP_append, List.countP_map, List.range_succ_eq_map (n := a),
    List.countP_cons, List.countP_map, hleft, List.range_succ (n := b),
    List.countP_append, List.countP_singleton, hright]
  have ends := outer_cuts a n b
  simp only [Function.comp_apply, Nat.zero_add, w, hindex, ends.1, ends.2, Function.comp_def]

end isUlamWord_zeros_two_ones_zeros_iff

open isUlamWord_zeros_two_ones_zeros_iff isUlamWord_three_ones_zeros_iff
  isUlamWord_zeros_four_ones_zeros_iff in
/-- **Ulam words with a block of two ones.** For natural numbers $a$ and $b$, the binary word
$0^a 11 0^b$ ($a$ zeros, then two ones, then $b$ zeros) is an Ulam word if and only if $a + b$ is
odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 6
(Theorem 3.5 of Bade, Cui, Labelle, and Li). -/
public theorem isUlamWord_zeros_two_ones_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ List.replicate 2 true ++ List.replicate b false) ↔
      (a + b) % 2 = 1 := by
  change IsUlamWord (padded a 2 b) ↔ _
  cases a with
  | zero => simpa [padded, block] using two_leading b
  | succ a =>
    cases b with
    | zero =>
      simpa [padded, block] using (ulam_reverse (block 2 (a + 1))).trans (two_leading _)
    | succ b =>
      have hmid := (middle_cut a b 1 0).2 ⟨one_leading _, one_leading _⟩
      rw [padded_iff a 1 b]
      simp only [isUlamWord_zeros_two_ones_zeros_iff a (b + 1),
        isUlamWord_zeros_two_ones_zeros_iff (a + 1) b]
      simp only [show List.range 1 = [0] by rfl, List.countP_singleton, Nat.add_zero, hmid,
        ite_true]
      split_ifs <;> omega
termination_by a + b

open isUlamWord_zeros_two_ones_zeros_iff isUlamWord_three_ones_zeros_iff
  isUlamWord_zeros_four_ones_zeros_iff in
/-- **Ulam words with a block of four ones.** For natural numbers $a$ and $b$ with $a + b \ge 1$,
the binary word $0^a 1111 0^b$ ($a$ zeros, then four ones, then $b$ zeros) is an Ulam word if
and only if $a + b \equiv 1 \pmod 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 1. -/
public theorem isUlamWord_zeros_four_ones_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ List.replicate 4 true ++ List.replicate b false) ↔
      (a + b) % 4 = 1 := by
  change IsUlamWord (padded a 4 b) ↔ _
  cases a with
  | zero =>
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    simpa [padded, block] using four_leading b
  | succ a =>
    cases b with
    | zero =>
      simpa [padded, block] using (ulam_reverse (block 4 (a + 1))).trans (four_leading a)
    | succ b =>
      have h₁ := middle_cut a b 1 2
      have h₂ := middle_cut a b 2 1
      have h₃ := middle_cut a b 3 0
      simp only [Nat.reduceAdd, one_leading, three_leading, true_and, and_true] at h₁ h₃
      simp only [Nat.reduceAdd, two_leading] at h₂
      rw [padded_iff a 3 b]
      simp only [isUlamWord_zeros_four_ones_zeros_iff a (b + 1) (by omega),
        isUlamWord_zeros_four_ones_zeros_iff (a + 1) b (by omega)]
      simp only [show List.range 3 = [0, 1, 2] by rfl, List.countP_cons, List.countP_nil,
        Nat.add_zero, h₁, h₂, h₃]
      split_ifs <;> omega
termination_by a + b

open isUlamWord_zeros_two_ones_zeros_iff isUlamWord_three_ones_zeros_iff
  isUlamWord_zeros_four_ones_zeros_iff in
/-- **Parity criterion for Ulam words with a single one.** For natural numbers $a$ and $b$, the
binary word $0^a 1 0^b$ ($a$ zeros, then a one, then $b$ zeros) is an Ulam word if and only if
the binomial coefficient $\binom{a + b}{a}$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 8;
Bade, Cui, Labelle, and Li, *Ulam Sets in New Settings*, arXiv:2008.02762v2, Theorem 3.3. -/
public theorem isUlamWord_zeros_one_zeros_iff (a b : ℕ) :
    IsUlamWord (List.replicate a false ++ [true] ++ List.replicate b false) ↔
      Odd ((a + b).choose a) := by
  change IsUlamWord (padded a 1 b) ↔ _
  cases a with
  | zero => simpa [padded, block] using iff_true_intro (one_leading b)
  | succ a =>
    cases b with
    | zero =>
      simpa [padded, block] using
        (ulam_reverse (block 1 (a + 1))).trans (iff_true_intro (one_leading (a + 1)))
    | succ b =>
      -- There are no cuts inside the one-letter block. The endpoint cuts contribute
      -- exactly when the corresponding smaller Ulam words occur.
      rw [padded_iff a 0 b]
      simp only [List.range_zero, List.countP_nil, Nat.add_zero]
      change ((if IsUlamWord (List.replicate a false ++ [true] ++
          List.replicate (b + 1) false) then 1 else 0) +
        (if IsUlamWord (List.replicate (a + 1) false ++ [true] ++
          List.replicate b false) then 1 else 0) = 1) ↔ _
      have hl := isUlamWord_zeros_one_zeros_iff a (b + 1)
      have hr := isUlamWord_zeros_one_zeros_iff (a + 1) b
      simp only [hl, hr]
      have hPascal : (a + 1 + (b + 1)).choose (a + 1) =
          (a + (b + 1)).choose a + (a + 1 + b).choose (a + 1) := by
        rw [show a + 1 + (b + 1) = (a + (b + 1)) + 1 by omega, Nat.choose_succ_succ',
          show a + 1 + b = a + (b + 1) by omega]
      rw [hPascal, Nat.odd_add, ← Nat.not_odd_iff_even]
      by_cases hl : Odd ((a + (b + 1)).choose a) <;>
        by_cases hr : Odd ((a + 1 + b).choose (a + 1)) <;> simp [hl, hr]
termination_by a + b

namespace card_ulam_zeros_one_zeros

private theorem odd_choose_digit (m a : ℕ) :
    Odd (m.choose a) ↔ a % 2 ≤ m % 2 ∧ Odd ((m / 2).choose (a / 2)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := m) (k := a) (p := 2)
  have hbit : Odd ((m % 2).choose (a % 2)) ↔ a % 2 ≤ m % 2 := by
    rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with hm | hm <;>
      rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with ha | ha <;>
      rw [hm, ha] <;> decide
  rw [Nat.odd_iff, h, ← Nat.odd_iff, Nat.odd_mul, hbit]

-- Lucas's theorem makes the admissible low bit independent of the higher bits.
private theorem card_odd_choose_step (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun a => Odd (m.choose a))).card =
      ((Finset.range (m / 2 + 1)).filter (fun a => Odd ((m / 2).choose a))).card *
        (m % 2 + 1) := by
  rw [← Finset.card_range (n := m % 2 + 1), ← Finset.card_product]
  refine Finset.card_nbij' (fun a => (a / 2, a % 2)) (fun p => 2 * p.1 + p.2) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha
    rw [odd_choose_digit] at ha
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, ha.2.2⟩, by omega⟩
  · rintro ⟨q, r⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have hdiv : (2 * q + r) / 2 = q := by omega
    rw [odd_choose_digit, hdiv]
    exact ⟨by omega, by omega, hp.1.2⟩
  · intro a _
    change 2 * (a / 2) + a % 2 = a
    omega
  · rintro ⟨q, r⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
    change ((2 * q + r) / 2, (2 * q + r) % 2) = (q, r)
    exact Prod.ext (by omega) (by omega)

private theorem card_odd_choose (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun a => Odd (m.choose a))).card =
      2 ^ (Nat.digits 2 m).sum := by
  by_cases hm : m = 0
  · subst m
    decide
  · rw [card_odd_choose_step, card_odd_choose (m / 2),
      Nat.digits_eq_cons_digits_div (by decide : 1 < 2) hm, List.sum_cons, pow_add, mul_comm]
    rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with h | h <;> simp [h]
termination_by m
decreasing_by omega

end card_ulam_zeros_one_zeros

open card_ulam_zeros_one_zeros in
/-- **Counting Ulam words with a single one.** For every $n \ge 1$, the number of
$a \in \{0, \dots, n - 1\}$ for which the word $0^a 1 0^{n-1-a}$ ($a$ zeros, then a one, then
$n - 1 - a$ zeros) is an Ulam word equals $2^{s_2(n-1)}$, where $s_2(m)$ is the sum of the binary
digits of $m$. This number is the term $G(n - 1)$ of Gould's sequence.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 5
(Corollary 3.4 of Bade, Cui, Labelle, and Li). -/
public theorem card_ulam_zeros_one_zeros (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.range n).filter fun a =>
        IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (n - 1 - a) false)).card =
      2 ^ (Nat.digits 2 (n - 1)).sum := by
  have hfilter :
      ((Finset.range n).filter fun a =>
        IsUlamWord (List.replicate a false ++ [true] ++ List.replicate (n - 1 - a) false)) =
      (Finset.range n).filter fun a => Odd ((n - 1).choose a) := by
    apply Finset.filter_congr
    intro a ha
    rw [isUlamWord_zeros_one_zeros_iff, show a + (n - 1 - a) = n - 1 by
      have := Finset.mem_range.mp ha
      omega]
  rw [hfilter]
  simpa only [Nat.sub_add_cancel hn] using card_odd_choose (n - 1)


namespace two_mul_add_four_le_ulamWordCount

open isUlamWord_three_ones_zeros_iff isUlamWord_zeros_four_ones_zeros_iff

private abbrev pad (a : ℕ) (middle : List Bool) (b : ℕ) : List Bool :=
  List.replicate a false ++ middle ++ List.replicate b false

-- The initial run of zeros is recovered from the first true letter.
private theorem eq_padding_of_eq {a b : ℕ} {u v : List Bool}
    (h : List.replicate a false ++ (true :: u) = List.replicate b false ++ (true :: v)) :
    a = b := by
  have less_impossible {i j : ℕ} {x y : List Bool} (hij : i < j)
      (he : List.replicate i false ++ (true :: x) = List.replicate j false ++ (true :: y)) :
      False := by
    have hget := congrArg (fun l : List Bool => l[i]?) he
    rw [List.getElem?_append_right (by simp),
      List.getElem?_append_left (by simpa using hij)] at hget
    simp [hij] at hget
  rcases lt_trichotomy a b with hlt | he | hgt
  · exact (less_impossible hlt h).elim
  · exact he
  · exact (less_impossible hgt h.symm).elim

private theorem ulam_iff_unique_cut {w : List Bool} (hw : 2 ≤ w.length) :
    IsUlamWord w ↔ ∃ k, (k < w.length - 1 ∧ cut w k) ∧
      ∀ j, j < w.length - 1 → cut w j → j = k := by
  rw [count_cuts hw, List.countP_eq_length_filter]
  let ks := (List.range (w.length - 1)).filter (cut w)
  change ks.length = 1 ↔ _
  have hmem (k : ℕ) : k ∈ ks ↔ k < w.length - 1 ∧ cut w k := by simp [ks]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp h
    exact ⟨k, (hmem k).mp (by simp [hk]), fun j hj hc => by
      simpa [hk] using (hmem j).mpr ⟨hj, hc⟩⟩
  · rintro ⟨k, hk, hu⟩
    have hnodup : ks.Nodup := List.nodup_range.filter _
    have hcount := List.count_eq_one_of_mem hnodup ((hmem k).mpr hk)
    rw [List.count_eq_length_filter, List.filter_eq_self.mpr ?_] at hcount
    · exact hcount
    · intro j hj
      obtain ⟨hj, hc⟩ := (hmem j).mp hj
      simp [hu j hj hc]

private abbrev spaced (a b : ℕ) : List Bool := pad a [true, false, true] b

private theorem spaced_left_cut (a b k : ℕ) (hk : k < a) :
    cut (spaced a b) k ↔ k = 0 ∧ IsUlamWord (spaced (a - 1) b) := by
  by_cases hzero : k = 0
  · subst k
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hw : spaced (a + 1) b = [false] ++ spaced a b := rfl
    have hne : [false] ≠ spaced a b := by
      apply ne_of_apply_ne List.length
      simp [spaced]; omega
    rw [cut_append (k := 0) hw rfl, and_iff_right hne, and_iff_right isUlamWord_small.1]
    simp
  · have ht : (spaced a b).take (k + 1) = List.replicate (k + 1) false := by
      change (List.replicate a false ++ [true, false, true] ++
        List.replicate b false).take (k + 1) = _
      rw [List.append_assoc, List.take_append_of_le_length (by simp; omega)]
      simp [Nat.min_eq_left (by omega : k + 1 ≤ a)]
    simp only [hzero, false_and, iff_false]
    intro h
    have hlen := length_eq_one_of_replicate (ht ▸ ((cut_iff _ _).mp h).2.1)
    omega

private theorem spaced_right_cut (a b k : ℕ) (hk : a + 2 ≤ k) (hk' : k < a + b + 2) :
    cut (spaced a b) k ↔ k = a + b + 1 ∧ IsUlamWord (spaced a (b - 1)) := by
  by_cases hend : k = a + b + 1
  · subst k
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have hw : spaced a (b + 1) = spaced a b ++ [false] := by
      simp only [List.replicate_succ', List.append_assoc]
    have hne : spaced a b ≠ [false] := by
      apply ne_of_apply_ne List.length
      simp [spaced]; omega
    rw [cut_append hw (by simp; omega), and_iff_right hne, and_iff_left isUlamWord_small.1]
    simp
  · have hd : (spaced a b).drop (k + 1) = List.replicate (a + b + 2 - k) false := by
      change (List.replicate a false ++ [true, false, true] ++
        List.replicate b false).drop (k + 1) = _
      rw [List.drop_append, List.drop_eq_nil_of_le (by simp; omega), List.nil_append]
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil,
        List.drop_replicate]
      congr 1
      omega
    simp only [hend, false_and, iff_false]
    intro h
    have hlen := length_eq_one_of_replicate (hd ▸ ((cut_iff _ _).mp h).2.2)
    omega

-- The two internal cuts each have a single one on each side. Equality of the factors
-- would require total padding one, which is outside the range used here.
private theorem spaced_inner_cuts (a b : ℕ) (hab : 2 ≤ a + b) :
    (cut (spaced a b) a ↔ b % 2 = 0) ∧
      (cut (spaced a b) (a + 1) ↔ a % 2 = 0) := by
  constructor
  · let u := List.replicate a false ++ [true]
    let v := false :: true :: List.replicate b false
    have hw : spaced a b = u ++ v := by simp [u, v, List.append_assoc]
    have hne : u ≠ v := by
      intro he
      have ha := eq_padding_of_eq (b := 1) (u := []) (v := List.replicate b false) he
      have hl := congrArg List.length he
      simp [u, v] at hl
      omega
    have hu : IsUlamWord u := by simpa [u] using (isUlamWord_zeros_one_zeros_iff a 0).2 (by simp)
    have hv : IsUlamWord v ↔ b % 2 = 0 := by
      change IsUlamWord (pad 1 [true] b) ↔ _
      rw [isUlamWord_zeros_one_zeros_iff, Nat.choose_one_right, Nat.odd_iff]
      omega
    rw [cut_append hw (by simp [u]), and_iff_right hne, and_iff_right hu, hv]
  · let u := List.replicate a false ++ [true, false]
    let v := true :: List.replicate b false
    have hw : spaced a b = u ++ v := by simp [u, v, List.append_assoc]
    have hne : u ≠ v := by
      intro he
      have ha := eq_padding_of_eq (b := 0) (u := [false]) (v := List.replicate b false) he
      have hl := congrArg List.length he
      simp [u, v] at hl
      omega
    have hv : IsUlamWord v := by
      exact (isUlamWord_zeros_one_zeros_iff 0 b).2 (by simp)
    have hu : IsUlamWord u ↔ a % 2 = 0 := by
      have hchoose : (a + 1).choose a = (a + 1).choose 1 := by
        simpa only [Nat.add_sub_cancel] using Nat.choose_symm (n := a + 1) (k := 1) (by omega)
      rw [show u = pad a [true] 1 by simp [u, List.append_assoc],
        isUlamWord_zeros_one_zeros_iff, hchoose, Nat.choose_one_right, Nat.odd_iff]
      omega
    rw [cut_append (k := a + 1) hw (by simp [u]), and_iff_right hne,
      and_iff_left hv, hu]

-- For even lengths at least six, every shift of the block 101 is Ulam.
private theorem spaced_iff (a b : ℕ) (hab : 2 ≤ a + b) :
    IsUlamWord (spaced a b) ↔ (a + b) % 2 = 1 := by
  by_cases hsmall : a + b = 2
  · rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · have hb : b = 2 := by omega
      subst b
      decide
    · have hb : b = 1 := by omega
      subst b
      decide
    · have hb : b = 0 := by omega
      subst b
      decide
  have hlen : (spaced a b).length - 1 = a + b + 2 := by simp; omega
  rw [ulam_iff_unique_cut (by omega), hlen]
  have hl (ha : 0 < a) : IsUlamWord (spaced (a - 1) b) ↔ (a + b) % 2 = 0 :=
    (spaced_iff (a - 1) b (by omega)).trans (by omega)
  have hr (hb : 0 < b) : IsUlamWord (spaced a (b - 1)) ↔ (a + b) % 2 = 0 :=
    (spaced_iff a (b - 1) (by omega)).trans (by omega)
  have hc := spaced_inner_cuts a b hab
  by_cases hodd : (a + b) % 2 = 1
  · simp only [hodd, iff_true]
    have unique (j : ℕ) (hj : j < a + b + 2) (h : cut (spaced a b) j) :
        (j = a ∧ b % 2 = 0) ∨ (j = a + 1 ∧ a % 2 = 0) := by
      by_cases hleft : j < a
      · have hbad := (hl (by omega)).mp ((spaced_left_cut a b j hleft).mp h).2
        omega
      by_cases hright : a + 2 ≤ j
      · have hbad := (hr (by omega)).mp ((spaced_right_cut a b j hright hj).mp h).2
        omega
      rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
      · exact Or.inl ⟨rfl, hc.1.mp h⟩
      · exact Or.inr ⟨rfl, hc.2.mp h⟩
    by_cases hb : b % 2 = 0
    · exact ⟨a, ⟨by omega, hc.1.mpr hb⟩, fun j hj h => by have := unique j hj h; omega⟩
    · exact ⟨a + 1, ⟨by omega, hc.2.mpr (by omega)⟩,
        fun j hj h => by have := unique j hj h; omega⟩
  · simp only [hodd, iff_false]
    rintro ⟨k, -, hu⟩
    by_cases hb : b % 2 = 0
    · have h₁ := hu a (by omega) (hc.1.mpr hb)
      have h₂ := hu (a + 1) (by omega) (hc.2.mpr (by omega))
      omega
    · have h₁ := hu 0 (by omega) ((spaced_left_cut a b 0 (by omega)).mpr
        ⟨rfl, (hl (by omega)).mpr (by omega)⟩)
      have h₂ := hu (a + b + 1) (by omega)
        ((spaced_right_cut a b _ (by omega) (by omega)).mpr
          ⟨rfl, (hr (by omega)).mpr (by omega)⟩)
      omega
termination_by a + b
decreasing_by all_goals omega


private theorem count_letters (w : List Bool) : w.count false + w.count true = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp <;> omega

-- A family using strictly fewer than half ones is disjoint from its bitwise complement.
private theorem twice_card_le {ι : Type} [Fintype ι] {n : ℕ} (w : ι → List Bool)
    (hi : Function.Injective w) (hlen : ∀ i, (w i).length = n) (hu : ∀ i, IsUlamWord (w i))
    (hwt : ∀ i, 2 * (w i).count true < n) : 2 * Fintype.card ι ≤ ulamWordCount n := by
  let word (p : Bool × ι) : List Bool := if p.1 then (w p.2).map not else w p.2
  have hword (p : Bool × ι) : (word p).length = n := by
    rcases p with ⟨b, i⟩
    cases b <;> simp [word, hlen]
  have hflip (i : ι) : ((w i).map not).count true + (w i).count true = n := by
    rw [show ((w i).map not).count true = (w i).count false from
      List.count_map_of_injective (w i) not Bool.not_injective false, count_letters, hlen]
  have separate (i j : ι) (he : w i = (w j).map not) : False := by
    have he' := congrArg (List.count true) he
    have h := hflip j
    have h₁ := hwt i
    have h₂ := hwt j
    omega
  have hinj : Function.Injective word := by
    rintro ⟨b, i⟩ ⟨c, j⟩ h
    cases b <;> cases c
    · exact congrArg (false, ·) (hi h)
    · exact (separate i j h).elim
    · exact (separate j i h.symm).elim
    · exact congrArg (true, ·) (hi ((List.map_injective_iff.mpr Bool.not_injective) h))
  let f (p : Bool × ι) (i : Fin n) : Bool := (word p)[i.val]'(by rw [hword]; exact i.isLt)
  have hf (p : Bool × ι) : List.ofFn (f p) = word p := by
    apply List.ext_getElem (by simp [hword])
    intro i _ _
    rw [List.getElem_ofFn]
  let U := Finset.univ.filter fun v : Fin n → Bool => IsUlamWord (List.ofFn v)
  let g (p : Bool × ι) : ↥U := ⟨f p, by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, hf]
    rcases p with ⟨b, i⟩
    cases b
    · exact hu i
    · exact (isUlamWord_map_not_and_ulamResidueCount_eq.1 _ (hu i)).1⟩
  have hc := Fintype.card_le_of_injective g (by
    intro p q h
    have he := congrArg (fun v : ↥U => List.ofFn v.val) h
    exact hinj (by simpa only [g, hf] using he))
  change 2 * Fintype.card ι ≤ U.card
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] using hc

private abbrev placed (n : ℕ) (middle : List Bool) (a : ℕ) : List Bool :=
  pad a middle (n - middle.length - a)

private theorem placed_weight (n a : ℕ) (w : List Bool) :
    (placed n w a).count true = w.count true := by
  simp [placed, pad, List.count_append, List.count_replicate]

private theorem placed_length (n a : ℕ) (w : List Bool) (h : a + w.length ≤ n) :
    (placed n w a).length = n := by
  simp [placed, pad]
  omega

-- Each middle starts with one, so within a family the starting positions are distinct.
-- Between the two families the numbers of ones distinguish the words.
private theorem twice_card_padded_le (n : ℕ) (s t : Finset ℕ) (u v : List Bool)
    (hs : ∀ a ∈ s, a + (true :: u).length ≤ n ∧ IsUlamWord (placed n (true :: u) a))
    (ht : ∀ a ∈ t, a + (true :: v).length ≤ n ∧ IsUlamWord (placed n (true :: v) a))
    (hw : (true :: u).count true ≠ (true :: v).count true)
    (hu : 2 * (true :: u).count true < n) (hv : 2 * (true :: v).count true < n) :
    2 * (s.card + t.card) ≤ ulamWordCount n := by
  let w : ↥s ⊕ ↥t → List Bool := Sum.elim (fun a => placed n (true :: u) a.val)
    (fun a => placed n (true :: v) a.val)
  have hinj : Function.Injective w := by
    have same {a b : ℕ} {z : List Bool}
        (h : placed n (true :: z) a = placed n (true :: z) b) : a = b := by
      apply eq_padding_of_eq
        (u := z ++ List.replicate (n - (true :: z).length - a) false)
        (v := z ++ List.replicate (n - (true :: z).length - b) false)
      simpa only [placed, pad, List.append_assoc, List.cons_append] using h
    have different {a b : ℕ} (h : placed n (true :: u) a = placed n (true :: v) b) : False :=
      hw (by simpa only [placed_weight] using congrArg (List.count true) h)
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext (same h))
      | inr b => exact (different h).elim
    | inr a =>
      cases y with
      | inl b => exact (different h.symm).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext (same h))
  have hc := twice_card_le w hinj
    (fun i => match i with
      | .inl a => placed_length _ _ _ (hs a.val a.property).1
      | .inr a => placed_length _ _ _ (ht a.val a.property).1)
    (fun i => match i with
      | .inl a => (hs a.val a.property).2
      | .inr a => (ht a.val a.property).2)
    (fun i => match i with
      | .inl a => by simpa only [w, Sum.elim_inl, placed_weight] using hu
      | .inr a => by simpa only [w, Sum.elim_inr, placed_weight] using hv)
  simpa only [Fintype.card_sum, Fintype.card_coe] using hc

private theorem single_at_iff (n a : ℕ) (ha : a < n) :
    IsUlamWord (placed n [true] a) ↔ Odd ((n - 1).choose a) := by
  change IsUlamWord (pad a [true] (n - 1 - a)) ↔ _
  rw [isUlamWord_zeros_one_zeros_iff, show a + (n - 1 - a) = n - 1 by omega]

private theorem adjacent_two (n : ℕ) (hodd : n % 2 = 1) (a : ℕ)
    (ha : a ∈ Finset.range (n - 1)) :
    a + ([true, true] : List Bool).length ≤ n ∧ IsUlamWord (placed n [true, true] a) := by
  have h := Finset.mem_range.mp ha
  refine ⟨by simp; omega, (isUlamWord_zeros_two_ones_zeros_iff _ _).2 ?_⟩
  change (a + (n - 2 - a)) % 2 = 1
  omega

end two_mul_add_four_le_ulamWordCount

open two_mul_add_four_le_ulamWordCount in
/-- **Linear lower bound on the number of Ulam words.** For every natural number $n \ge 6$, the
number of Ulam words of length $n$ is at least $2n + 4$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 1. -/
public theorem two_mul_add_four_le_ulamWordCount (n : ℕ) (hn : 6 ≤ n) :
    2 * n + 4 ≤ ulamWordCount n := by
  by_cases he : n % 2 = 0
  · -- Four single-one words and every shift of 101; both families have complements.
    let s : Finset ℕ := {0, 1, n - 2, n - 1}
    have hc : s.card = 4 := by
      have h₀ : (0 : ℕ) ∉ ({1, n - 2, n - 1} : Finset ℕ) := by simp; omega
      have h₁ : (1 : ℕ) ∉ ({n - 2, n - 1} : Finset ℕ) := by simp; omega
      have h₂ : n - 2 ∉ ({n - 1} : Finset ℕ) := by simp; omega
      rw [show s = insert 0 (insert 1 (insert (n - 2) {n - 1})) from rfl,
        Finset.card_insert_of_notMem h₀, Finset.card_insert_of_notMem h₁,
        Finset.card_insert_of_notMem h₂, Finset.card_singleton]
    have hs (a : ℕ) (ha : a ∈ s) :
        a + ([true] : List Bool).length ≤ n ∧ IsUlamWord (placed n [true] a) := by
      have ha' : a = 0 ∨ a = 1 ∨ a = n - 2 ∨ a = n - 1 := by simpa [s] using ha
      refine ⟨by simp; omega, (single_at_iff n a (by omega)).2 ?_⟩
      rcases ha' with rfl | rfl | rfl | rfl
      · simp
      · rw [Nat.choose_one_right, Nat.odd_iff]; omega
      · rw [show n - 2 = n - 1 - 1 by omega, Nat.choose_symm (by omega : 1 ≤ n - 1),
          Nat.choose_one_right, Nat.odd_iff]
        omega
      · simp
    have ht (a : ℕ) (ha : a ∈ Finset.range (n - 2)) :
        a + ([true, false, true] : List Bool).length ≤ n ∧
          IsUlamWord (placed n [true, false, true] a) := by
      have h := Finset.mem_range.mp ha
      refine ⟨by simp; omega, (spaced_iff a (n - 3 - a) (by omega)).2 (by omega)⟩
    have h := twice_card_padded_le n s (Finset.range (n - 2)) [] [false, true] hs ht
      (by decide) (by change 2 < n; omega) (by change 4 < n; omega)
    rw [hc, Finset.card_range] at h
    omega
  have hodd : n % 2 = 1 := by omega
  by_cases hthree : n % 4 = 3
  · -- Shifts of 11 and the three single-one positions 0, 2, n - 1.
    let s : Finset ℕ := {0, 2, n - 1}
    have hc : s.card = 3 := by
      have h₀ : (0 : ℕ) ∉ ({2, n - 1} : Finset ℕ) := by simp; omega
      have h₂ : (2 : ℕ) ∉ ({n - 1} : Finset ℕ) := by simp; omega
      rw [show s = insert 0 (insert 2 {n - 1}) from rfl, Finset.card_insert_of_notMem h₀,
        Finset.card_insert_of_notMem h₂, Finset.card_singleton]
    have hs (a : ℕ) (ha : a ∈ s) :
        a + ([true] : List Bool).length ≤ n ∧ IsUlamWord (placed n [true] a) := by
      have ha' : a = 0 ∨ a = 2 ∨ a = n - 1 := by simpa [s] using ha
      refine ⟨by simp; omega, (single_at_iff n a (by omega)).2 ?_⟩
      rcases ha' with rfl | rfl | rfl
      · simp
      · rw [card_ulam_zeros_one_zeros.odd_choose_digit]
        change 0 ≤ (n - 1) % 2 ∧ Odd (((n - 1) / 2).choose 1)
        rw [Nat.choose_one_right, Nat.odd_iff]
        omega
      · simp
    have h := twice_card_padded_le n s (Finset.range (n - 1)) [] [true] hs (adjacent_two n hodd)
      (by decide) (by change 2 < n; omega) (by change 4 < n; omega)
    rw [hc, Finset.card_range] at h
    omega
  · -- Shifts of 11 and 1111: in this residue class n is at least nine.
    have ht (a : ℕ) (ha : a ∈ Finset.range (n - 3)) :
        a + ([true, true, true, true] : List Bool).length ≤ n ∧
          IsUlamWord (placed n [true, true, true, true] a) := by
      have h := Finset.mem_range.mp ha
      refine ⟨by simp; omega, (isUlamWord_zeros_four_ones_zeros_iff a (n - 4 - a) (by omega)).2 ?_⟩
      omega
    have h := twice_card_padded_le n (Finset.range (n - 1)) (Finset.range (n - 3)) [true]
      [true, true, true] (adjacent_two n hodd) ht (by decide)
      (by change 4 < n; omega) (by change 8 < n; omega)
    rw [Finset.card_range, Finset.card_range] at h
    omega

end

end MetaMathlibExt
