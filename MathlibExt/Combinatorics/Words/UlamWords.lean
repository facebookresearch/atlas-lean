/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.ZMod.Defs

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

namespace ulamResidueCount_mod_two_three

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

end ulamResidueCount_mod_two_three

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
      ulamResidueCount_mod_two_three.card_complement 2 n 0
  · intro a
    rw [ulamResidueCount_mod_two_three.card_complement 3 n a,
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

end

end MetaMathlibExt
