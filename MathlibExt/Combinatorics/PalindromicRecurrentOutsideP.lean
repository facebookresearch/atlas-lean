/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

import Mathlib.Data.List.Infix
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

/-!
# Labbé's palindromic fixed point outside class P

Labbé's primitive ternary substitution has a palindromic, uniformly recurrent
fixed point that no nonidentity morphism conjugate to class P generates.
The proof uses the binary substitution and palindrome recursion from
Labbé, *A counterexample to a question of Hof, Knill and Simon*,
[arXiv:1307.1589v1](https://arxiv.org/abs/1307.1589v1).
-/

namespace MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted

@[expose] public section

/-- **The ternary alphabet of Labbé's counterexample.** The alphabet is the three-letter set
$\{0, 1, 2\}$.

Labbé's counterexample is over a ternary alphabet. -/
abbrev Sigma := Fin 3

/-- **Morphisms of the ternary alphabet.** A morphism of the ternary alphabet $\{0, 1, 2\}$ is
given by its letter map: a function $\varphi$ that sends each letter $a$ to a finite word
$\varphi(a)$ over $\{0, 1, 2\}$, possibly the empty word. -/
abbrev Morphism := Sigma → List Sigma

/-- **Image of a word under a morphism.** A morphism $\varphi$ acts on a word
$w = w_1 w_2 \cdots w_k$ by $\varphi(w) = \varphi(w_1) \varphi(w_2) \cdots \varphi(w_k)$, the
concatenation of the images of its letters; the empty word is sent to the empty word. -/
def extend (φ : Morphism) (w : List Sigma) : List Sigma :=
  List.flatten (w.map φ)

/-- **Iterated images of words under a morphism.** Let $\varphi$ be a morphism of the ternary
alphabet $\{0, 1, 2\}$, acting on finite words letter by letter. Its iterates $\varphi^n$ on
finite words are defined by $\varphi^0(w) = w$ and $\varphi^{n+1}(w) = \varphi(\varphi^n(w))$
for every natural number $n$ and every finite word $w$ over $\{0, 1, 2\}$. -/
def extendIter (φ : Morphism) : Nat → List Sigma → List Sigma
  | 0 => id
  | n + 1 => (extend φ) ∘ (extendIter φ n)

/-- **Primitive morphisms.** Let $\varphi$ be a morphism of the ternary alphabet $\{0, 1, 2\}$,
sending each letter to a finite word, and let $\varphi^n$ be the $n$-th iterate of its letter by
letter extension to finite words, with $\varphi^0$ the identity. Then $\varphi$ is primitive when
there is a natural number $n$ such that for all letters $a$ and $b$, the letter $b$ occurs in the
word $\varphi^n(a)$. -/
def IsPrimitive (φ : Morphism) : Prop :=
  ∃ n : Nat, ∀ a b : Sigma, b ∈ extendIter φ n [a]

/-- **Palindromes.** A finite word $w$ over the alphabet $\{0, 1, 2\}$ is a palindrome when it
equals its reversal, that is, reads the same backwards; in particular the empty word is a
palindrome. -/
def IsPalindrome (w : List Sigma) : Prop := w = w.reverse

/-- **Class P.** A morphism $\varphi$ is in class P (Hof–Knill–Simon) when there is a palindrome $p$
such that for every letter $a$, $\varphi(a) = p q_a$ for some palindrome $q_a$. The palindromes
$p$ and $q_a$ may be empty.

Source: Labbé 2014, Section 2. -/
def InClassP (φ : Morphism) : Prop :=
  ∃ p : List Sigma, IsPalindrome p ∧
    ∀ a : Sigma, ∃ q : List Sigma, IsPalindrome q ∧ φ a = p ++ q

/-- **Infinite words.** An infinite word over the alphabet $\{0, 1, 2\}$ is a sequence
$u = u_0 u_1 u_2 \cdots$ of letters indexed by the natural numbers, that is, a map
$\mathbb{N} \to \{0, 1, 2\}$. -/
abbrev InfWord := Nat → Sigma

/-- **Occurrence of a word at a position.** A finite word $w = w_0 w_1 \cdots w_{n-1}$ over the
ternary alphabet $\{0, 1, 2\}$ occurs in an infinite word $u = u_0 u_1 u_2 \cdots$ over the same
alphabet at position $k$ when $w_i = u_{k+i}$ for every $i < n$. -/
def OccursAt (w : List Sigma) (u : InfWord) (k : Nat) : Prop :=
  ∀ i : Fin w.length, w[i] = u (k + i.val)

/-- **Factors of an infinite word.** A finite word $w$ is a factor of an infinite word $u$ when it
occurs in $u$ at some position: there is $k \in \mathbb{N}$ with $w_i = u_{k+i}$ for every
$i < |w|$ (letters of $w$ indexed from $0$). In particular the empty word is a factor of every
infinite word. -/
def IsFactor (w : List Sigma) (u : InfWord) : Prop :=
  ∃ k : Nat, OccursAt w u k

/-- **Fixed point of a morphism.** An infinite word $u$ is a fixed point of a morphism $\varphi$
when it is the limit of the iterates of a prolongable letter: there is a letter $a$ such that
$\varphi(a)$ begins with $a$, the words $\varphi^m(a)$ ($m \ge 0$) are arbitrarily long, and every
$\varphi^m(a)$ is a prefix of $u$. -/
def IsFixedPoint (φ : Morphism) (u : InfWord) : Prop :=
  ∃ a : Sigma, (φ a).head? = some a ∧
    (∀ L : Nat, ∃ m : Nat,
      L ≤ (extendIter φ m [a]).length) ∧
    ∀ m : Nat, ∀ i : Fin (extendIter φ m [a]).length,
      (extendIter φ m [a])[i] = u i.val

/-- **Palindromic infinite words.** An infinite word $u = u_0 u_1 u_2 \cdots$ over the ternary
alphabet $\{0, 1, 2\}$ is palindromic when it has arbitrarily long palindromic factors: for every
natural number $N$ there is a finite word $w = w_0 \cdots w_{n-1}$ with $n \ge N$ that reads the
same backwards and occurs in $u$: for some position $k$, $w_i = u_{k+i}$ for all $i < n$.

Over the finite ternary alphabet this is equivalent to having infinitely many palindromic factors.

Source: Labbé 2014. -/
def IsPalindromic (u : InfWord) : Prop :=
  ∀ N : Nat, ∃ w : List Sigma, N ≤ w.length ∧ IsPalindrome w ∧ IsFactor w u

/-- **Uniformly recurrent infinite words.** Let $u = u_0 u_1 u_2 \cdots$ be an infinite word over
the ternary alphabet $\{0, 1, 2\}$, and say that a finite word $w = w_0 \cdots w_{n-1}$ occurs in
$u$ at position $m$ when $w_i = u_{m+i}$ for every $i < n$. Then $u$ is uniformly recurrent when
for every finite word $w$ that occurs in $u$ at some position, there is a natural number $B$ such
that for every position $k$, the word $w$ occurs in $u$ at position $k + j$ for some $j \le B$. -/
def IsUniformlyRecurrent (u : InfWord) : Prop :=
  ∀ w : List Sigma, IsFactor w u →
    ∃ B : Nat, ∀ k : Nat, ∃ j : Nat, j ≤ B ∧ OccursAt w u (k + j)

/-- **Conjugate morphisms.** Let $\psi$ and $\theta$ be morphisms of the ternary alphabet
$\{0, 1, 2\}$, each sending every letter to a finite word, and write $xy$ for the concatenation of
words $x$ and $y$. Then $\psi$ and $\theta$ are conjugate when there is a finite word $w$ such that
$\psi(a) w = w \theta(a)$ for every letter $a$, or there is a finite word $w$ such that
$\theta(a) w = w \psi(a)$ for every letter $a$.

Source: Labbé 2014, Section 2; Lothaire. -/
def MorphConjugate (ψ θ : Morphism) : Prop :=
  (∃ w : List Sigma, ∀ a : Sigma, ψ a ++ w = w ++ θ a) ∨
    (∃ w : List Sigma, ∀ a : Sigma, θ a ++ w = w ++ ψ a)

/-- **Identity morphism.** A morphism $\psi$ is the identity morphism when $\psi(a)$ is the
one-letter word $a$ for every letter $a$. -/
def IsIdentityMorphism (ψ : Morphism) : Prop :=
  ∀ a : Sigma, ψ a = [a]

/-- **Palindromic uniformly recurrent fixed point outside class P.** The proposition that there
exist a primitive morphism $\varphi$ on the alphabet $\{0, 1, 2\}$ and an infinite word $u$ such
that $u$ is a fixed point of $\varphi$, $u$ is palindromic and uniformly recurrent, and no morphism
$\psi$ that has $u$ as a fixed point and is not the identity is conjugate to a morphism in class P.

Here a fixed point of a morphism $\psi$ is an infinite word $u$ for which there is a letter $a$ such
that $\psi(a)$ begins with $a$, the words $\psi^m(a)$ are arbitrarily long, and every $\psi^m(a)$ is
a prefix of $u$.

Source: Labbé, A counterexample to a question of Hof, Knill and Simon, EJC 21
(2014) #P3.11, Theorem 10 in arXiv:1307.1589v1. -/
def conjecture : Prop :=
  ∃ φ : Morphism, IsPrimitive φ ∧
    ∃ u : InfWord, IsFixedPoint φ u ∧ IsPalindromic u ∧
      IsUniformlyRecurrent u ∧
      ¬ ∃ ψ : Morphism, IsFixedPoint ψ u ∧ ¬ IsIdentityMorphism ψ ∧
        ∃ θ : Morphism, MorphConjugate ψ θ ∧ InClassP θ

end

open List
open MetaMathlibExt (morphExtend morphIterate morphIterate_prefix morphIterate_succ_right)

variable {α β : Type*}

private abbrev a : Sigma := 0
private abbrev b : Sigma := 1
private abbrev c : Sigma := 2

private def gamma : Morphism := fun x =>
  if x = a then [a, c, a] else if x = b then [c, a, b] else [b]

private def mu : Bool → List Bool
  | false => [false, true]
  | true => [false, false, true]

private def code : Bool → List Sigma
  | false => [a, c]
  | true => [a, b]

private abbrev piWord (w : List Bool) : List Sigma := w.flatMap code

private theorem iterate_append (f : α → List α) (n : Nat) (x y : List α) :
    morphIterate f n (x ++ y) = morphIterate f n x ++ morphIterate f n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp [morphIterate, morphExtend, ih, List.flatMap_append]

private theorem iterate_eq_extendIter (f : Morphism) (n : Nat) (w : List Sigma) :
    morphIterate f n w = extendIter f n w := by
  induction n with
  | zero => rfl
  | succ n ih => change (morphIterate f n w).flatMap f = extend f (extendIter f n w); rw [ih]; rfl

private theorem iterate_add (f : α → List α) (m n : Nat) (w : List α) :
    morphIterate f (m + n) w = morphIterate f n (morphIterate f m w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (morphIterate f (m + n) w).flatMap f = (morphIterate f n (morphIterate f m w)).flatMap f
    rw [ih]

private theorem iterate_flatMap (f : α → List α) (n : Nat) (w : List α) :
    morphIterate f n w = w.flatMap (fun x => morphIterate f n [x]) := by
  induction w with
  | nil => induction n <;> simp_all [morphIterate, morphExtend]
  | cons x w ih =>
    change morphIterate f n ([x] ++ w) = _
    rw [iterate_append, ih, List.flatMap_cons]

private theorem code_mu (w : List Bool) : piWord (w.flatMap mu) = extend gamma (piWord w) := by
  change (w.flatMap mu).flatMap code = (w.flatMap code).flatMap gamma
  rw [List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  funext x
  cases x <;> decide

private theorem code_iterate (n : Nat) (w : List Bool) :
    piWord (morphIterate mu n w) = morphIterate gamma n (piWord w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change piWord ((morphIterate mu n w).flatMap mu) =
      (morphIterate gamma n (piWord w)).flatMap gamma
    rw [code_mu, ih]
    rfl

private abbrev binaryPrefix (n : Nat) : List Bool := morphIterate mu n [false]
private abbrev firstBlock (n : Nat) : List Sigma := piWord (binaryPrefix n)
private abbrev secondBlock (n : Nat) : List Sigma := piWord (morphIterate mu n [true])

private theorem firstBlock_succ (n : Nat) :
    firstBlock (n + 1) = firstBlock n ++ secondBlock n := by
  change piWord (binaryPrefix (n + 1)) = _
  rw [show binaryPrefix (n + 1) = morphIterate mu n ([false] ++ [true]) from
    morphIterate_succ_right ..]
  simp only [iterate_append, piWord, List.flatMap_append]

private theorem secondBlock_succ (n : Nat) :
    secondBlock (n + 1) = firstBlock n ++ firstBlock (n + 1) := by
  change piWord (morphIterate mu (n + 1) [true]) = _
  rw [show morphIterate mu (n + 1) [true] =
    morphIterate mu n ([false] ++ ([false] ++ [true])) from morphIterate_succ_right ..]
  rw [firstBlock_succ]
  simp only [iterate_append, piWord, firstBlock, binaryPrefix, secondBlock, List.flatMap_append]

private theorem piWord_length (w : List Bool) : (piWord w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons x w ih => cases x <;> simp [code, ih, Nat.mul_succ]

private theorem mu_length (w : List Bool) : 2 * w.length ≤ (w.flatMap mu).length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    cases x <;> simp [mu, List.length_flatMap, Nat.mul_succ] at * <;> omega

private theorem binaryPrefix_length (n : Nat) : n + 1 ≤ (binaryPrefix n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := mu_length (binaryPrefix n)
    change _ ≤ ((binaryPrefix n).flatMap mu).length
    omega

private theorem firstBlock_length (n : Nat) : n + 1 ≤ (firstBlock n).length := by
  rw [piWord_length]
  have := binaryPrefix_length n
  omega

private theorem binaryPrefix_mono {m n : Nat} (h : m ≤ n) :
    binaryPrefix m <+: binaryPrefix n := by
  induction n, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ n _ ih =>
    apply ih.trans
    rw [show binaryPrefix (n + 1) = morphIterate mu n [false, true] from morphIterate_succ_right ..]
    exact morphIterate_prefix (List.prefix_append [false] [true]) mu n

private theorem firstBlock_mono {m n : Nat} (h : m ≤ n) :
    firstBlock m <+: firstBlock n := (binaryPrefix_mono h).flatMap code

-- Take each letter from a sufficiently long member of the nested prefix sequence.
private def word (i : Nat) : Sigma := (firstBlock i)[i]'(firstBlock_length i)

private theorem firstBlock_get (n : Nat) {i : Nat} (h : i < (firstBlock n).length) :
    (firstBlock n)[i] = word i := by
  unfold word
  rcases Nat.le_total n i with hni | hin
  · exact (firstBlock_mono hni).getElem h
  · exact ((firstBlock_mono hin).getElem (firstBlock_length i)).symm

private theorem word_zero : word 0 = a := rfl

private theorem occurs_of_prefix {w l r : List Sigma} {n : Nat}
    (h : l ++ w ++ r <+: firstBlock n) : OccursAt w word l.length := by
  intro i
  have hi : l.length + i.val < (l ++ w ++ r).length := by
    simp only [List.length_append]
    omega
  rw [← firstBlock_get n (lt_of_lt_of_le hi h.length_le), ← h.getElem hi]
  rw [List.getElem_append_left (by simp), List.getElem_append_right (by omega)]
  simp

private theorem firstBlock_prefix_iff {w : List Sigma} {n : Nat} :
    w <+: firstBlock n ↔ w.length ≤ (firstBlock n).length ∧ OccursAt w word 0 := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := h
    refine ⟨by simp [← hr], ?_⟩
    simpa using occurs_of_prefix (l := []) (w := w) (r := r) (n := n)
      (by simp [hr])
  · rintro ⟨hlen, h⟩
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by rw [List.length_take, Nat.min_eq_left hlen]) ?_
    intro i hi _
    rw [List.getElem_take, firstBlock_get]
    simpa using h ⟨i, hi⟩

private theorem gamma_primitive : IsPrimitive gamma := by
  refine ⟨3, ?_⟩
  decide

private theorem gamma_fixed : IsFixedPoint gamma word := by
  refine ⟨a, by decide, ?_, ?_⟩
  · intro L
    refine ⟨L + 1, ?_⟩
    rw [← iterate_eq_extendIter, morphIterate_succ_right]
    have h := (morphIterate_prefix (show [a, c] <+: [a].flatMap gamma by decide) gamma L).length_le
    rw [← show piWord [false] = [a, c] from rfl, ← code_iterate] at h
    exact le_trans (Nat.le_of_lt (firstBlock_length L)) h
  · intro n i
    have h : morphIterate gamma n [a] <+: morphIterate gamma n [a, c] :=
      morphIterate_prefix (List.prefix_append [a] [c]) gamma n
    rw [← show piWord [false] = [a, c] from rfl, ← code_iterate, iterate_eq_extendIter] at h
    simpa using (firstBlock_prefix_iff.mp h).2 i

private theorem fixed_image_prefix {f : Morphism} (hf : IsFixedPoint f word)
    {w : List Sigma} {n : Nat} (h : w <+: firstBlock n) :
    ∃ m, extend f w <+: firstBlock m := by
  obtain ⟨d, _, hg, hs⟩ := hf
  obtain ⟨k, hk⟩ := hg w.length
  have hw : w <+: extendIter f k [d] := by
    rw [List.prefix_iff_eq_take]
    refine List.ext_getElem (by simp [Nat.min_eq_left hk]) ?_
    intro i hi _
    rw [List.getElem_take]
    have he : w[i] = word i := by simpa using (firstBlock_prefix_iff.mp h).2 ⟨i, hi⟩
    exact he.trans (hs k ⟨i, lt_of_lt_of_le hi hk⟩).symm
  have hq : extend f w <+: extendIter f (k + 1) [d] := hw.flatMap f
  refine ⟨(extendIter f (k + 1) [d]).length, hq.trans ?_⟩
  exact firstBlock_prefix_iff.mpr
    ⟨le_of_lt (firstBlock_length _), fun i => by simpa using hs (k + 1) i⟩

private theorem fixed_first {f : Morphism} (hf : IsFixedPoint f word) : (f a).head? = some a := by
  obtain ⟨d, hd, _, hs⟩ := hf
  have he : d = a := hs 0 ⟨0, by change 0 < 1; decide⟩
  simpa [he] using hd

-- The two-step palindrome recursion follows from the block recursions.
private theorem firstBlock_palindromes (n : Nat) :
    ∃ p : List Sigma, firstBlock (n + 1) = [a, c, a] ++ p ∧ p.reverse = p ∧ p.head? = some b := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨[b], rfl, rfl, rfl⟩
  | one => exact ⟨[b, a, c, a, c, a, b], rfl, rfl, rfl⟩
  | more n ih₁ ih₂ =>
    obtain ⟨p, hp, hrp, hbp⟩ := ih₁
    obtain ⟨q, hq, hrq, hbq⟩ := ih₂
    refine ⟨q ++ [a, c, a] ++ p ++ [a, c, a] ++ q, ?_, ?_, ?_⟩
    · rw [firstBlock_succ (n + 2), secondBlock_succ (n + 1), hq, hp]
      simp only [List.append_assoc]
    · simp only [List.reverse_append, hrp, hrq, List.append_assoc]
      rfl
    · cases q with
      | nil => simp at hbq
      | cons x xs => simpa using hbq

private theorem gamma_palindromic : IsPalindromic word := by
  intro N
  obtain ⟨p, hp, hr, _⟩ := firstBlock_palindromes (N + 2)
  refine ⟨p, ?_, hr.symm, 3, ?_⟩
  · have h := firstBlock_length (N + 3)
    rw [hp, List.length_append] at h
    simp at h
    omega
  · exact occurs_of_prefix (l := [a, c, a]) (r := []) (n := N + 3) (by simp [hp])

private theorem occurs_in_firstBlock {w : List Sigma} {k : Nat} (h : OccursAt w word k) :
    w <:+: firstBlock (k + w.length) := by
  let L := firstBlock (k + w.length)
  have hL : k + w.length ≤ L.length := le_of_lt (firstBlock_length _)
  have he : w = (L.drop k).take w.length := by
    refine List.ext_getElem (by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]) ?_
    intro i hi _
    rw [List.getElem_take, List.getElem_drop, firstBlock_get]
    exact h ⟨i, hi⟩
  change w <:+: L
  rw [he]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

private theorem iterate_infix {x y : List α} (h : x <:+: y) (f : α → List α) (n : Nat) :
    morphIterate f n x <:+: morphIterate f n y := by
  obtain ⟨l, r, rfl⟩ := h
  exact ⟨morphIterate f n l, morphIterate f n r, by simp only [iterate_append, List.append_assoc]⟩

private theorem next_block {g : α → List β} {B : Nat} (hB : ∀ x, (g x).length ≤ B)
    (xs : List α) (k : Nat) (hk : k + B < (xs.flatMap g).length) :
    ∃ l x r, xs = l ++ x :: r ∧ k ≤ (l.flatMap g).length ∧
      (l.flatMap g).length ≤ k + B := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    by_cases hzero : k = 0
    · exact ⟨[], x, xs, rfl, by simp [hzero], Nat.zero_le _⟩
    have hlen : (x :: xs).flatMap g = g x ++ xs.flatMap g := by rw [List.flatMap_cons]
    rw [hlen, List.length_append] at hk
    by_cases hinside : k ≤ (g x).length
    · cases xs with
      | nil => simp at hk; have := hB x; omega
      | cons y ys =>
        exact ⟨[x], y, ys, rfl, by simpa, by simpa using le_trans (hB x) (Nat.le_add_left B k)⟩
    · obtain ⟨l, y, r, hxs, hl, hu⟩ := ih (k - (g x).length) (by omega)
      refine ⟨x :: l, y, r, by simp [hxs], ?_, ?_⟩
      all_goals rw [List.flatMap_cons, List.length_append]; omega

private theorem gamma_recurrent : IsUniformlyRecurrent word := by
  intro w hw
  obtain ⟨k₀, hk₀⟩ := hw
  let R := k₀ + w.length + 1
  have hwR : w <:+: morphIterate gamma R [a] := by
    apply (occurs_in_firstBlock hk₀).trans
    suffices ht : firstBlock (k₀ + w.length) <+: morphIterate gamma R [a] from ht.isInfix
    rw [show R = _ + 1 from rfl, morphIterate_succ_right]
    rw [show firstBlock (k₀ + w.length) = morphIterate gamma (k₀ + w.length) [a, c] from
      code_iterate _ [false]]
    exact morphIterate_prefix (show [a, c] <+: [a].flatMap gamma by decide) gamma _
  let Q := 3 + R
  have hall : ∀ x : Sigma, w <:+: morphIterate gamma Q [x] := by
    intro x
    rw [show Q = 3 + R from rfl, iterate_add]
    apply hwR.trans
    apply iterate_infix
    exact (show ∀ y : Sigma, [a] <:+: morphIterate gamma 3 [y] by decide) x
  let B := (morphIterate gamma Q [a]).length + (morphIterate gamma Q [b]).length +
    (morphIterate gamma Q [c]).length
  have hB : ∀ x : Sigma, (morphIterate gamma Q [x]).length ≤ B := by
    intro x
    rcases (show ∀ x : Sigma, x = a ∨ x = b ∨ x = c by decide) x with rfl | rfl | rfl <;>
      dsimp [B] <;> omega
  refine ⟨B + B, ?_⟩
  intro k
  let M := (k + B) + Q
  let xs := morphIterate gamma (k + B) [a, c]
  let g := fun x => morphIterate gamma Q [x]
  have he : xs.flatMap g = firstBlock M := by
    change xs.flatMap g = piWord (morphIterate mu M [false])
    rw [code_iterate]
    exact (iterate_add gamma (k + B) Q [a, c]).trans (iterate_flatMap gamma Q xs) |>.symm
  have hg : k + B < (xs.flatMap g).length := by
    rw [he]
    have := firstBlock_length M
    dsimp [M] at *
    omega
  obtain ⟨l, x, r, hxs, hl, hu⟩ := next_block (g := g) hB xs k hg
  obtain ⟨p, s, hgs⟩ := hall x
  have hp : p.length ≤ B := by
    have hx := hB x
    change (g x).length ≤ B at hx
    change p ++ w ++ s = g x at hgs
    rw [← hgs] at hx
    simp only [List.length_append] at hx
    omega
  let j := (l.flatMap g).length + p.length - k
  have hj : k + j = (l.flatMap g).length + p.length := by dsimp [j]; omega
  refine ⟨j, by dsimp [j]; omega, ?_⟩
  rw [hj, ← List.length_append]
  apply occurs_of_prefix (n := M) (r := s ++ r.flatMap g)
  rw [← he, hxs, List.flatMap_append, List.flatMap_cons]
  change p ++ w ++ s = g x at hgs
  rw [← hgs]
  simp only [List.append_assoc, List.prefix_refl]

private theorem flatMap_prefix_cut (f : α → List β) {w : List β} {xs : List α}
    (h : w <+: xs.flatMap f) :
    ∃ l r, l <+: xs ∧ w = l.flatMap f ++ r ∧
      (r = [] ∨ ∃ x, r <+: f x ∧ r.length < (f x).length) := by
  induction xs generalizing w with
  | nil =>
    have he : w = [] := List.prefix_nil.mp h
    exact ⟨[], [], List.prefix_rfl, by simp [he], Or.inl rfl⟩
  | cons x xs ih =>
    rw [List.flatMap_cons] at h
    by_cases hlen : w.length < (f x).length
    · have hpre := List.prefix_of_prefix_length_le h (List.prefix_append (f x) (xs.flatMap f))
        (Nat.le_of_lt hlen)
      exact ⟨[], w, List.nil_prefix, rfl, Or.inr ⟨x, hpre, hlen⟩⟩
    · obtain ⟨v, rfl⟩ := List.prefix_of_prefix_length_le
        (List.prefix_append (f x) (xs.flatMap f)) h (by omega)
      obtain ⟨l, r, hl, hv, hr⟩ := ih ((List.prefix_append_right_inj _).mp h)
      refine ⟨x :: l, r, List.cons_prefix_cons.mpr ⟨rfl, hl⟩, ?_, hr⟩
      rw [List.flatMap_cons, hv, List.append_assoc]

-- This formulation of fixing the binary limit allows erasing morphisms.
private def PrefixPreserving (f : Bool → List Bool) : Prop :=
  ∀ n, ∃ m, (binaryPrefix n).flatMap f <+: binaryPrefix m

private theorem PrefixPreserving.map_prefix {f : Bool → List Bool} (hf : PrefixPreserving f)
    {w : List Bool} {n : Nat} (h : w <+: binaryPrefix n) :
    ∃ m, w.flatMap f <+: binaryPrefix m := by
  obtain ⟨m, hm⟩ := hf n
  exact ⟨m, (h.flatMap f).trans hm⟩

private theorem mu_preserves : PrefixPreserving mu :=
  fun n => ⟨n + 1, List.prefix_rfl⟩

private theorem comp_preserves {f g : Bool → List Bool}
    (hf : PrefixPreserving f) (hg : PrefixPreserving g) :
    PrefixPreserving (fun x => (f x).flatMap g) := by
  intro n
  obtain ⟨m, hm⟩ := hf n
  simpa only [← List.flatMap_assoc] using hg.map_prefix hm

private theorem prefixes_eq_of_length {f g : Bool → List Bool}
    (hf : PrefixPreserving f) (hg : PrefixPreserving g)
    (hlen : ∀ x, (f x).length = (g x).length) : f = g := by
  obtain ⟨m, hm⟩ := hf 1
  obtain ⟨n, hn⟩ := hg 1
  have hp : f false ++ f true <+: binaryPrefix (max m n) :=
    by
      simpa [binaryPrefix, morphIterate, morphExtend, mu] using
        hm.trans (binaryPrefix_mono (Nat.le_max_left m n))
  have hq : g false ++ g true <+: binaryPrefix (max m n) :=
    by
      simpa [binaryPrefix, morphIterate, morphExtend, mu] using
        hn.trans (binaryPrefix_mono (Nat.le_max_right m n))
  have hfalse : f false = g false :=
    (List.prefix_of_prefix_length_le ((List.prefix_append _ _).trans hp)
      ((List.prefix_append _ _).trans hq) (le_of_eq (hlen false))).eq_of_length (hlen false)
  have hboth := (List.prefix_of_prefix_length_le hp hq (by simp [hlen])).eq_of_length (by
    simp [hlen])
  rw [hfalse] at hboth
  have htrue := List.append_cancel_left hboth
  funext x
  cases x
  · exact hfalse
  · exact htrue

private theorem sqrt_two_facts :
    (√(2 : ℝ)) ^ 2 = 2 ∧ 1 ≤ √(2 : ℝ) ∧ √(2 : ℝ) ≤ 3/2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnon := Real.sqrt_nonneg 2
  exact ⟨h, by nlinarith, by nlinarith⟩

-- The discrepancy contracts when applying the binary substitution.
private noncomputable def discrepancy (w : List Bool) : ℝ :=
  (w.count false : ℝ) - √(2 : ℝ) * (w.count true : ℝ)

private theorem discrepancy_append (w v : List Bool) :
    discrepancy (w ++ v) = discrepancy w + discrepancy v := by
  simp only [discrepancy, List.count_append, Nat.cast_add]
  ring

private theorem count_mu (w : List Bool) :
    ((w.flatMap mu).count false = w.count false + 2 * w.count true) ∧
      ((w.flatMap mu).count true = w.count false + w.count true) := by
  induction w with
  | nil => decide
  | cons x w ih =>
    cases x <;>
      simp only [List.flatMap_cons, List.count_append, ih.1, ih.2, mu, List.count_cons] <;>
      simp <;> omega

private theorem count_bool_length (w : List Bool) : w.count false + w.count true = w.length := by
  induction w with
  | nil => decide
  | cons x xs ih => cases x <;> simp <;> omega

private theorem discrepancy_mu (w : List Bool) :
    discrepancy (w.flatMap mu) = (1 - √(2 : ℝ)) * discrepancy w := by
  simp only [discrepancy, (count_mu w).1, (count_mu w).2, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  obtain ⟨h, _, _⟩ := sqrt_two_facts
  linear_combination -(w.count true : ℝ) * h

private theorem discrepancy_short {w : List Bool} (h : w.length ≤ 2) :
    |discrepancy w| ≤ 4 := by
  obtain ⟨_, h₀, h₁⟩ := sqrt_two_facts
  have hx : (w.count false : ℝ) ≤ 2 := by
    exact_mod_cast (List.count_le_length (a := false) (l := w)).trans h
  have hy : (w.count true : ℝ) ≤ 2 := by
    exact_mod_cast (List.count_le_length (a := true) (l := w)).trans h
  have hx₀ : (0 : ℝ) ≤ w.count false := by positivity
  have hy₀ : (0 : ℝ) ≤ w.count true := by positivity
  rw [abs_le, discrepancy]
  constructor <;> nlinarith

private theorem discrepancy_prefix {w : List Bool} {n : Nat} (h : w <+: binaryPrefix n) :
    |discrepancy w| ≤ 8 := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w n with
  | ind length ih =>
    cases n with
    | zero =>
      have hh : w.length ≤ 1 := h.length_le
      exact (discrepancy_short (by omega)).trans (by norm_num)
    | succ n =>
      by_cases hw : w = []
      · norm_num [hw, discrepancy]
      obtain ⟨l, r, hl, hwr, hr⟩ := flatMap_prefix_cut mu h
      have hmul := mu_length l
      have hlw : 2 * l.length ≤ w.length := by
        rw [hwr, List.length_append]
        omega
      have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
      have hl₀ := ih l.length (by omega) hl rfl
      have hr₀ : r.length ≤ 2 := by
        rcases hr with rfl | ⟨x, _, hx⟩
        · decide
        · cases x <;> simp [mu] at hx <;> omega
      have hr₁ := discrepancy_short hr₀
      obtain ⟨_, h₀, h₁⟩ := sqrt_two_facts
      have hd : |1 - √(2 : ℝ)| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
      rw [hwr, discrepancy_append, discrepancy_mu]
      calc
        _ ≤ |(1 - √(2 : ℝ)) * discrepancy l| + |discrepancy r| := abs_add_le _ _
        _ ≤ (1/2) * 8 + 4 := by
          rw [abs_mul]
          gcongr
        _ = 8 := by norm_num

private theorem discrepancy_flatMap (f : Bool → List Bool) (w : List Bool) :
    discrepancy (w.flatMap f) =
      (w.count false : ℝ) * discrepancy (f false) +
        (w.count true : ℝ) * discrepancy (f true) := by
  induction w with
  | nil => simp [discrepancy]
  | cons x w ih =>
    rw [List.flatMap_cons, discrepancy_append, ih]
    cases x <;> simp [Nat.cast_add] <;> ring

private theorem discrepancy_preserving {f : Bool → List Bool} (hf : PrefixPreserving f) :
    √(2 : ℝ) * discrepancy (f false) + discrepancy (f true) = 0 := by
  let D := √(2 : ℝ) * discrepancy (f false) + discrepancy (f true)
  by_contra hd
  have hd : 0 < |D| := abs_pos.mpr hd
  obtain ⟨n, hn⟩ := exists_nat_gt ((8 + 8 * |discrepancy (f false)|) / |D|)
  have hm : (n : ℝ) * |D| > 8 + 8 * |discrepancy (f false)| := (div_lt_iff₀ hd).mp hn
  let w := binaryPrefix (n + 1)
  have hcount : n ≤ w.count true := by
    change n ≤ ((binaryPrefix n).flatMap mu).count true
    rw [(count_mu _).2, count_bool_length]
    have := binaryPrefix_length n
    omega
  have hcount' : (n : ℝ) ≤ w.count true := by exact_mod_cast hcount
  obtain ⟨m, hpre⟩ := hf (n + 1)
  have h₁ := discrepancy_prefix hpre
  have h₂ := discrepancy_prefix (List.prefix_rfl : w <+: w)
  have he : (w.count true : ℝ) * D =
      discrepancy (w.flatMap f) - discrepancy w * discrepancy (f false) := by
    rw [discrepancy_flatMap]
    unfold D discrepancy
    ring
  have hbound : (w.count true : ℝ) * |D| ≤ 8 + 8 * |discrepancy (f false)| := by
    rw [← abs_of_nonneg (show 0 ≤ (w.count true : ℝ) by positivity), ← abs_mul, he]
    calc
      _ ≤ |discrepancy (w.flatMap f)| + |discrepancy w * discrepancy (f false)| :=
        abs_sub _ _
      _ ≤ _ := by rw [abs_mul]; gcongr
  exact (not_lt_of_ge (le_trans (mul_le_mul_of_nonneg_right hcount' hd.le) hbound)) hm

private theorem counts_preserving {f : Bool → List Bool} (hf : PrefixPreserving f) :
    (f false).count false = (f true).count true ∧
      (f true).count false = 2 * (f false).count true := by
  let A : ℤ := (f false).count false
  let B : ℤ := (f false).count true
  let C : ℤ := (f true).count false
  let D : ℤ := (f true).count true
  have hD := discrepancy_preserving hf
  obtain ⟨hs, _, _⟩ := sqrt_two_facts
  have he : √(2 : ℝ) * ((A : ℝ) - (D : ℝ)) = (2 : ℝ) * B - C := by
    simp only [discrepancy] at hD
    dsimp [A, B, C, D]
    push_cast
    linear_combination hD + (↑((f false).count true) : ℝ) * hs
  have hAD : A = D := by
    by_contra hne
    apply irrational_sqrt_two.ne_rational (2 * B - C) (A - D)
    push_cast
    exact (eq_div_iff (sub_ne_zero.mpr (by exact_mod_cast hne))).mpr he
  have he' : (2 : ℝ) * B = C := by rw [hAD, sub_self, mul_zero] at he; linarith
  have hCB : C = 2 * B := by exact_mod_cast he'.symm
  constructor
  · dsimp [A, D] at hAD
    exact_mod_cast hAD
  · dsimp [C, B] at hCB
    exact_mod_cast hCB

-- Bounded discrepancy forces the incidence matrices to commute. The lengths of the
-- images then determine the composite morphisms, since both preserve the limit.
private theorem mu_commutes {f : Bool → List Bool} (hf : PrefixPreserving f) :
    (fun x => (mu x).flatMap f) = (fun x => (f x).flatMap mu) := by
  apply prefixes_eq_of_length (comp_preserves mu_preserves hf) (comp_preserves hf mu_preserves)
  intro x
  obtain ⟨hA, hB⟩ := counts_preserving hf
  have len (w : List Bool) : (w.flatMap mu).length = 2 * w.count false + 3 * w.count true := by
    rw [← count_bool_length (w.flatMap mu), (count_mu w).1, (count_mu w).2]
    omega
  cases x <;> simp only [mu, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append, len] <;>
    have h₁ := count_bool_length (f false) <;> have h₂ := count_bool_length (f true) <;> omega

private theorem flatMap_reflect_prefix (f : α → List β) (hn : ∀ x, f x ≠ [])
    (hc : ∀ x y, f x <+: f y → x = y) {u v : List α}
    (h : u.flatMap f <+: v.flatMap f) : u <+: v := by
  induction u generalizing v with
  | nil => exact List.nil_prefix
  | cons x xs ih =>
    cases v with
    | nil =>
      have he : f x ++ xs.flatMap f = [] := List.prefix_nil.mp h
      exact (hn x (List.append_eq_nil_iff.mp he).1).elim
    | cons y ys =>
      rw [List.flatMap_cons, List.flatMap_cons] at h
      have hx : f x <+: f y ++ ys.flatMap f := (List.prefix_append _ _).trans h
      have hy : f y <+: f y ++ ys.flatMap f := List.prefix_append _ _
      obtain hxy | hyx := List.prefix_or_prefix_of_prefix hx hy
      · have he := hc _ _ hxy
        subst y
        exact List.cons_prefix_cons.mpr ⟨rfl, ih ((List.prefix_append_right_inj _).mp h)⟩
      · have he := hc _ _ hyx
        subst y
        exact List.cons_prefix_cons.mpr ⟨rfl, ih ((List.prefix_append_right_inj _).mp h)⟩

private theorem mu_reflect_prefix {u v : List Bool}
    (h : u.flatMap mu <+: v.flatMap mu) : u <+: v :=
  flatMap_reflect_prefix mu (by decide) (by decide) h

private theorem code_reflect_prefix {u v : List Bool}
    (h : piWord u <+: piWord v) : u <+: v :=
  flatMap_reflect_prefix code (by decide) (by decide) h

private theorem absorb_mu_cut {u v : List Bool}
    (h : u <+: v.flatMap mu) (hlast : [true] <:+ u) : ∃ l : List Bool, u = l.flatMap mu := by
  obtain ⟨l, r, _, hl, hr⟩ := flatMap_prefix_cut mu h
  refine ⟨l, ?_⟩
  rcases hr with rfl | ⟨x, hpre, hlen⟩
  · simpa using hl
  · have hnt : true ∉ r := by
      rw [List.prefix_iff_eq_take] at hpre
      rw [hpre]
      cases x <;> simp only [mu, List.length_cons, List.length_nil] at hlen ⊢
      · interval_cases m : r.length <;> decide
      · interval_cases m : r.length <;> decide
    cases r with
    | nil => simpa using hl
    | cons y ys =>
      have hs : [true] <:+ y :: ys := by
        apply List.suffix_of_suffix_length_le hlast
        · rw [hl]
          exact List.suffix_append _ _
        · simp
      exact (hnt (hs.subset (by simp))).elim

private theorem mu_suffix_true {u : List Bool} (h : u ≠ []) :
    [true] <:+ u.flatMap mu := by
  rw [← List.dropLast_append_getLast h, List.flatMap_append]
  exact List.IsSuffix.trans (by cases u.getLast h <;> decide) (List.suffix_append _ _)

-- Commuting with the substitution lets us desubstitute both images at block boundaries.
private theorem mu_power_preserving {f : Bool → List Bool} (hf : PrefixPreserving f)
    (hn : f false ≠ []) : ∃ k, ∀ x, f x = morphIterate mu k [x] := by
  induction hlen : (f false).length using Nat.strong_induction_on generalizing f with
  | ind length ih =>
    let P := f false
    let Q := f true
    have hcom := mu_commutes hf
    have h₁ : P ++ Q = P.flatMap mu := by
      simpa only [mu, List.flatMap_cons, List.append_nil, List.flatMap_nil] using
        congrFun hcom false
    have h₂ : P ++ P.flatMap mu = Q.flatMap mu := by
      rw [← h₁]
      simpa only [mu, List.flatMap_cons, List.append_nil, List.flatMap_nil] using
        congrFun hcom true
    obtain ⟨m, hm⟩ := hf.map_prefix (w := [false]) (n := 0) List.prefix_rfl
    have hPpre : P <+: binaryPrefix (m + 1) := by
      simpa [P] using hm.trans (binaryPrefix_mono (Nat.le_succ m))
    by_cases hsmall : P.length ≤ 1
    · have hP : P = [false] := by
        have hpre : [false] <+: binaryPrefix (m + 1) :=
          binaryPrefix_mono (Nat.zero_le _)
        have hlen' : P.length = [false].length := by
          have hp : 0 < P.length := List.length_pos_iff.mpr hn
          simp
          omega
        exact (List.prefix_of_prefix_length_le hPpre hpre hsmall).eq_of_length hlen'
      have hQ : Q = [true] := by
        rw [hP] at h₁
        exact List.cons.inj h₁ |>.2
      refine ⟨0, fun x => ?_⟩
      cases x
      · exact hP
      · exact hQ
    have hQne : Q ≠ [] := by
      intro he
      rw [he, List.flatMap_nil, List.append_eq_nil_iff] at h₂
      exact hn h₂.1
    have hQlast : Q.getLast hQne = true := by
      have ht : [true] <:+ P ++ Q := by rw [h₁]; exact mu_suffix_true hn
      nth_rw 1 [← List.dropLast_append_getLast hQne] at ht
      have ht' := List.suffix_of_suffix_length_le ht
        (show [Q.getLast hQne] <:+ P ++ (Q.dropLast ++ [Q.getLast hQne]) by
          rw [← List.append_assoc]; exact List.suffix_append _ _) (by simp)
      simpa [List.singleton_suffix_iff_getLast?_eq_some] using ht'
    have hPlast : P.getLast hn = true := by
      by_contra hnot
      have hpfalse : P.getLast hn = false := Bool.eq_false_of_not_eq_true hnot
      have hpne : P.dropLast ≠ [] := by
        have hl := List.length_dropLast (xs := P)
        exact List.length_pos_iff.mp (by omega)
      have hpx : ([true, false, true] : List Bool) <:+ P.flatMap mu := by
        have he : P.dropLast ++ [false] = P := by
          rw [← hpfalse]
          exact List.dropLast_append_getLast hn
        rw [← he, List.flatMap_append]
        change [true] ++ [false, true] <:+ _
        obtain ⟨l, hl⟩ := mu_suffix_true hpne
        refine ⟨l, ?_⟩
        rw [← List.append_assoc, hl]
        rfl
      have hqy : ([false, false, true] : List Bool) <:+ Q.flatMap mu := by
        have he : Q.dropLast ++ [true] = Q := by
          rw [← hQlast]
          exact List.dropLast_append_getLast hQne
        rw [← he, List.flatMap_append]
        exact List.suffix_append _ _
      have hpx' : ([true, false, true] : List Bool) <:+ Q.flatMap mu :=
        hpx.trans (by rw [← h₂]; exact List.suffix_append _ _)
      have hc := List.suffix_of_suffix_length_le hpx' hqy (by decide)
      exact (by decide : ¬ ([true, false, true] : List Bool) <:+ [false, false, true]) hc
    have hps : [true] <:+ P := ⟨P.dropLast, by
      rw [← hPlast]
      exact List.dropLast_append_getLast hn⟩
    obtain ⟨p, hp⟩ := absorb_mu_cut hPpre hps
    have hpP : p <+: P := by
      apply mu_reflect_prefix
      rw [← hp, ← h₁]
      exact List.prefix_append _ _
    obtain ⟨q, hq⟩ := hpP
    have hQ : Q = q.flatMap mu := by
      apply List.append_cancel_left (as := P)
      calc
        P ++ Q = P.flatMap mu := h₁
        _ = p.flatMap mu ++ q.flatMap mu := by rw [← hq, List.flatMap_append]
        _ = P ++ q.flatMap mu := by rw [← hp]
    let g : Bool → List Bool := fun x => if x then q else p
    have hfg : ∀ x, f x = (g x).flatMap mu := by
      intro x
      cases x
      · exact hp
      · exact hQ
    have hg : PrefixPreserving g := by
      intro n
      obtain ⟨l, hl⟩ := hf n
      refine ⟨l, mu_reflect_prefix ?_⟩
      rw [List.flatMap_assoc]
      change _ <+: binaryPrefix (l + 1)
      simpa only [← hfg] using hl.trans (binaryPrefix_mono (Nat.le_succ l))
    have hgne : g false ≠ [] := by
      intro hnil
      exact hn (by rw [hfg, hnil]; rfl)
    have hsmall' : (g false).length < length := by
      have hglen := mu_length (g false)
      rw [← hfg, hlen] at hglen
      have hpos := List.length_pos_iff.mpr hn
      omega
    obtain ⟨k, hk⟩ := ih (g false).length hsmall' hg hgne rfl
    exact ⟨k + 1, fun x => by rw [hfg, hk]; rfl⟩

-- The letter a marks the start of each ac or ab block.
private theorem code_boundary {l r : List Sigma} {u : List Bool}
    (h : l ++ a :: r <+: piWord u) : ∃ p : List Bool, l = piWord p := by
  induction u generalizing l with
  | nil =>
    have hl := h.length_le
    simp at hl
  | cons x xs ih =>
    cases l with
    | nil => exact ⟨[], rfl⟩
    | cons y ys =>
      have hx : ∃ d : Sigma, code x = [a, d] ∧ d ≠ a := by
        cases x
        · exact ⟨c, rfl, by decide⟩
        · exact ⟨b, rfl, by decide⟩
      obtain ⟨d, hd, hda⟩ := hx
      change (y :: ys) ++ a :: r <+: (x :: xs).flatMap code at h
      rw [List.flatMap_cons, hd] at h
      have hy : y = a := (List.cons_prefix_cons.mp h).1
      have ht : ys ++ a :: r <+: d :: piWord xs := (List.cons_prefix_cons.mp h).2
      cases ys with
      | nil =>
        have hbad : a = d := (List.cons_prefix_cons.mp ht).1
        exact (hda hbad.symm).elim
      | cons z zs =>
        obtain ⟨hz, hzpre⟩ := List.cons_prefix_cons.mp ht
        obtain ⟨p, hp⟩ := ih hzpre
        refine ⟨x :: p, ?_⟩
        change y :: z :: zs = (x :: p).flatMap code
        rw [List.flatMap_cons, hy, hz, hp, hd]
        rfl

-- Consecutive occurrences of a around either intervening letter mark two cuts in the image.
private theorem coded_pair_images {f : Morphism} (hf : IsFixedPoint f word) (x : Bool) :
    ∃ u : List Bool, extend f (code x) = piWord u := by
  have hfac : code x ++ [a] <:+: firstBlock 2 :=
    (show ∀ x, code x ++ [a] <:+: firstBlock 2 by decide) x
  obtain ⟨l, r, he⟩ := hfac
  obtain ⟨m, hm⟩ := fixed_image_prefix hf (n := 2)
    (show l ++ code x ++ [a] <+: firstBlock 2 by
      rw [← he, List.append_assoc l (code x) [a]]
      exact List.prefix_append _ _)
  obtain ⟨s, hs⟩ := List.head?_eq_some_iff.mp (fixed_first hf)
  let P := extend f l
  let V := extend f (code x)
  have hm₁ : (P ++ V) ++ a :: s <+: firstBlock m := by
    change ((l ++ code x ++ [a]).flatMap f) <+: firstBlock m at hm
    simpa only [P, V, extend, ← List.flatMap_def, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, hs] using hm
  have hm₀ : ∃ t, V ++ a :: s = a :: t := by
    have hx : ∃ d : Sigma, code x = [a, d] := by
      cases x
      · exact ⟨c, rfl⟩
      · exact ⟨b, rfl⟩
    obtain ⟨d, hd⟩ := hx
    change ∃ t, ((code x).flatMap f) ++ a :: s = a :: t
    rw [hd, List.flatMap_cons, hs]
    exact ⟨s ++ ([d].flatMap f) ++ a :: s, by simp only [List.cons_append, List.append_assoc]⟩
  obtain ⟨t, ht⟩ := hm₀
  have hm₂ : P ++ a :: t <+: firstBlock m := by rwa [List.append_assoc, ht] at hm₁
  obtain ⟨p, hp⟩ := code_boundary hm₂
  obtain ⟨q, hq⟩ := code_boundary hm₁
  have hpq : p <+: q := by
    apply code_reflect_prefix
    rw [← hp, ← hq]
    exact List.prefix_append _ _
  obtain ⟨u, hu⟩ := hpq
  have heq : P ++ V = P ++ piWord u := by
    calc
      P ++ V = piWord q := hq
      _ = P ++ piWord u := by
        rw [← hu]
        change (p ++ u).flatMap code = _
        rw [List.flatMap_append]
        exact congrArg (· ++ piWord u) hp.symm
  exact ⟨u, List.append_cancel_left heq⟩

private theorem fixed_pair_images {f : Morphism} (hf : IsFixedPoint f word) :
    ∃ k, f a ++ f c = firstBlock k ∧ f a ++ f b = secondBlock k := by
  classical
  choose g hg using coded_pair_images hf
  have hfg (w : List Bool) : extend f (piWord w) = piWord (w.flatMap g) := by
    change (w.flatMap code).flatMap f = (w.flatMap g).flatMap code
    simp only [List.flatMap_assoc]
    exact congrArg (fun t => w.flatMap t) (funext hg)
  have hpres : PrefixPreserving g := by
    intro n
    obtain ⟨m, hm⟩ := fixed_image_prefix hf (n := n) List.prefix_rfl
    refine ⟨m, code_reflect_prefix ?_⟩
    change extend f (piWord (binaryPrefix n)) <+: firstBlock m at hm
    rwa [hfg] at hm
  have hne : g false ≠ [] := by
    intro he
    have h : f a ++ f c = [] := by
      simpa only [extend, ← List.flatMap_def, code, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, he] using hg false
    have hnil := (List.append_eq_nil_iff.mp h).1
    simpa [hnil] using fixed_first hf
  obtain ⟨k, hk⟩ := mu_power_preserving hpres hne
  refine ⟨k, ?_, ?_⟩
  · simpa only [extend, ← List.flatMap_def, code, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hk] using hg false
  · simpa only [extend, ← List.flatMap_def, code, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hk] using hg true

-- A conjugacy to class P gives a simultaneous word equation with the reversed images.
private theorem classP_mirror {f θ : Morphism} (hc : MorphConjugate f θ) (hp : InClassP θ) :
    (∃ D : List Sigma, ∀ x, f x ++ D = D ++ (f x).reverse) ∨
      ∃ K : List Sigma, ∀ x, (f x).reverse ++ K = K ++ f x := by
  obtain ⟨p, hpal, hθ⟩ := hp
  have hpal' : p.reverse = p := hpal.symm
  have hθe (x) : θ x ++ p = p ++ (θ x).reverse := by
    obtain ⟨q, hq, he⟩ := hθ x
    rw [he, List.reverse_append, hq.symm, hpal', List.append_assoc]
  rcases hc with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine Or.inl ⟨w ++ p ++ w.reverse, fun x => ?_⟩
    have hr := congrArg List.reverse (hw x)
    simp only [List.reverse_append] at hr
    calc
      f x ++ (w ++ p ++ w.reverse) = (f x ++ w) ++ p ++ w.reverse := by
        simp only [List.append_assoc]
      _ = w ++ (θ x ++ p) ++ w.reverse := by rw [hw]; simp only [List.append_assoc]
      _ = w ++ p ++ ((θ x).reverse ++ w.reverse) := by rw [hθe]; simp only [List.append_assoc]
      _ = _ := by rw [← hr]; simp only [List.append_assoc]
  · have hpref : p <+: θ a ++ w := by
      obtain ⟨q, _, h⟩ := hθ a
      rw [h, List.append_assoc]
      exact List.prefix_append _ _
    have hwref : w <+: θ a ++ w := by rw [hw]; exact List.prefix_append _ _
    rcases List.prefix_or_prefix_of_prefix hpref hwref with ⟨r, her⟩ | ⟨r, her⟩
    · refine Or.inr ⟨w.reverse ++ r, fun x => ?_⟩
      have er := congrArg List.reverse (hw x)
      simp only [List.reverse_append] at er
      have haux : (θ x).reverse ++ r = r ++ f x := by
        apply List.append_cancel_left (as := p)
        calc
          p ++ ((θ x).reverse ++ r) = (θ x ++ p) ++ r := by
            rw [hθe, List.append_assoc]
          _ = θ x ++ w := by rw [List.append_assoc, her]
          _ = p ++ (r ++ f x) := by rw [hw, ← her, List.append_assoc]
      calc
        (f x).reverse ++ (w.reverse ++ r) = (w.reverse ++ (θ x).reverse) ++ r := by
          rw [← List.append_assoc, ← er]
        _ = _ := by rw [List.append_assoc, haux, ← List.append_assoc]
    · have hrr : r <:+ p := ⟨w, her⟩
      have hwr : w.reverse <:+ p := by
        rw [← hpal']
        apply List.reverse_prefix.mp
        simpa only [List.reverse_reverse] using (show w <+: p from ⟨r, her⟩)
      have haux (x) : f x ++ r = r ++ (θ x).reverse := by
        apply List.append_cancel_left (as := w)
        calc
          w ++ (f x ++ r) = (θ x ++ w) ++ r := by rw [hw, List.append_assoc]
          _ = θ x ++ p := by rw [List.append_assoc, her]
          _ = w ++ (r ++ (θ x).reverse) := by rw [hθe, ← her, List.append_assoc]
      rcases List.suffix_or_suffix_of_suffix hwr hrr with ⟨D, hD⟩ | ⟨K, hK⟩
      · refine Or.inl ⟨D, fun x => List.append_cancel_right (bs := w.reverse) ?_⟩
        have er := congrArg List.reverse (hw x)
        simp only [List.reverse_append] at er
        calc
          (f x ++ D) ++ w.reverse = f x ++ r := by rw [List.append_assoc, hD]
          _ = r ++ (θ x).reverse := haux x
          _ = _ := by rw [← hD, List.append_assoc, er, ← List.append_assoc]
      · refine Or.inr ⟨K, fun x => List.append_cancel_right (bs := r) ?_⟩
        have er := congrArg List.reverse (hw x)
        simp only [List.reverse_append] at er
        calc
          ((f x).reverse ++ K) ++ r = (f x).reverse ++ w.reverse := by
            rw [List.append_assoc, hK]
          _ = w.reverse ++ (θ x).reverse := er.symm
          _ = (K ++ f x) ++ r := by rw [← hK, List.append_assoc, ← haux, ← List.append_assoc]

private def repeatWord (w : List α) : Nat → List α
  | 0 => []
  | n + 1 => w ++ repeatWord w n

private theorem repeatWord_add (w : List α) (m n : Nat) :
    repeatWord w (m + n) = repeatWord w m ++ repeatWord w n := by
  induction m with
  | zero => simp [repeatWord]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [repeatWord, ih, List.append_assoc]

private theorem repeatWord_length (w : List α) (n : Nat) :
    (repeatWord w n).length = n * w.length := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, ih, Nat.succ_mul, Nat.add_comm]

private theorem intertwiner_prefix {X Y K : List α} {n : Nat} (h : X ++ K = K ++ Y)
    (hlen : K.length ≤ n * X.length) : K <+: repeatWord X n := by
  have he (m : Nat) : repeatWord X m ++ K = K ++ repeatWord Y m := by
    induction m with
    | zero => simp [repeatWord]
    | succ n ih =>
      calc
        repeatWord X (n + 1) ++ K = X ++ (repeatWord X n ++ K) := by
          rw [repeatWord, List.append_assoc]
        _ = (X ++ K) ++ repeatWord Y n := by rw [ih, List.append_assoc]
        _ = _ := by rw [h, List.append_assoc]; rfl
  have hK : K <+: repeatWord X n ++ K := ⟨_, (he n).symm⟩
  exact List.prefix_of_prefix_length_le hK (List.prefix_append _ _)
    (by rwa [repeatWord_length])

private theorem shared_commuter {X Y R : List α} (hr : R ≠ [])
    (hx : X ++ R = R ++ X) (hy : Y ++ R = R ++ Y) : X <+: Y ∨ Y <+: X := by
  let n := max X.length Y.length
  have hpos : 1 ≤ R.length := List.length_pos_iff.mpr hr
  have hn : n ≤ n * R.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hpos
  exact List.prefix_or_prefix_of_prefix
    (intertwiner_prefix hx.symm ((Nat.le_max_left _ _).trans hn))
    (intertwiner_prefix hy.symm ((Nat.le_max_right _ _).trans hn))

-- Two common conjugating words are comparable as prefixes of a long periodic word.
-- Any excess in the longer one must commute with both words on the right.
private theorem shared_intertwiner_unique {X Y X' Y' K L : List α}
    (hX : X ≠ []) (hcomp : ¬ (X' <+: Y' ∨ Y' <+: X'))
    (hXK : X ++ K = K ++ X') (hYK : Y ++ K = K ++ Y')
    (hXL : X ++ L = L ++ X') (hYL : Y ++ L = L ++ Y') : K = L := by
  let n := max K.length L.length
  have hpos : 1 ≤ X.length := List.length_pos_iff.mpr hX
  have hn : n ≤ n * X.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hpos
  have hKL := List.prefix_or_prefix_of_prefix
    (intertwiner_prefix hXK ((Nat.le_max_left _ _).trans hn))
    (intertwiner_prefix hXL ((Nat.le_max_right _ _).trans hn))
  have aux {T U : List α} (hT : X ++ T = T ++ X') (hT' : Y ++ T = T ++ Y')
      (hU : X ++ U = U ++ X') (hU' : Y ++ U = U ++ Y') (hp : T <+: U) : T = U := by
    obtain ⟨R, rfl⟩ := hp
    by_contra hne
    have hR : R ≠ [] := by rintro rfl; simp at hne
    have hx : X' ++ R = R ++ X' := by
      apply List.append_cancel_left (as := T)
      rw [← List.append_assoc, ← hT, List.append_assoc, hU, List.append_assoc]
    have hy : Y' ++ R = R ++ Y' := by
      apply List.append_cancel_left (as := T)
      rw [← List.append_assoc, ← hT', List.append_assoc, hU', List.append_assoc]
    exact hcomp (shared_commuter hR hx hy)
  exact hKL.elim (aux hXK hYK hXL hYL) (fun h => (aux hXL hYL hXK hYK h).symm)

private theorem shared_commute {X Y R : List α} (hr : R ≠ [])
    (hx : X ++ R = R ++ X) (hy : Y ++ R = R ++ Y) : X ++ Y = Y ++ X := by
  have aux {U V : List α} (hU : U ++ R = R ++ U) (hV : V ++ R = R ++ V) :
      (U ++ V) ++ R = R ++ (U ++ V) := by
    rw [List.append_assoc, hV, ← List.append_assoc, hU, List.append_assoc]
  have hc := shared_commuter hr (aux hx hy) (aux hy hx)
  have he : (X ++ Y).length = (Y ++ X).length := by simp [Nat.add_comm]
  exact hc.elim (fun h => h.eq_of_length he) (fun h => (h.eq_of_length he.symm).symm)

private theorem commute_root {X Y : List α} (h : X ++ Y = Y ++ X) :
    ∃ (w : List α) (m n : Nat), X = repeatWord w m ∧ Y = repeatWord w n := by
  induction hlen : X.length + Y.length using Nat.strong_induction_on generalizing X Y with
  | ind l ih =>
    by_cases hX : X = []
    · exact ⟨Y, 0, 1, hX, by simp [repeatWord]⟩
    by_cases hY : Y = []
    · exact ⟨X, 1, 0, by simp [repeatWord], hY⟩
    have hXpos := List.length_pos_iff.mpr hX
    have hYpos := List.length_pos_iff.mpr hY
    have he : X <+: Y ∨ Y <+: X := List.prefix_or_prefix_of_prefix
      (List.prefix_append X Y) (show Y <+: X ++ Y by rw [h]; exact List.prefix_append _ _)
    rcases he with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
    · rw [← hZ, ← List.append_assoc, List.append_assoc X X Z] at h
      have hc : X ++ Z = Z ++ X := List.append_cancel_left (by
        simpa only [List.append_assoc] using h)
      have hs : X.length + Z.length < l := by
        rw [← hlen, ← hZ, List.length_append]
        omega
      obtain ⟨w, m, n, hm, hn⟩ := ih _ hs hc rfl
      exact ⟨w, m, m + n, hm, by rw [← hZ, hm, hn, repeatWord_add]⟩
    · have hc : Y ++ Z = Z ++ Y := by
        apply List.append_cancel_left (as := Y)
        simpa only [← hZ, List.append_assoc] using h.symm
      have hs : Y.length + Z.length < l := by
        rw [← hlen, ← hZ, List.length_append]
        omega
      obtain ⟨w, m, n, hm, hn⟩ := ih _ hs hc rfl
      exact ⟨w, m + n, m, by rw [← hZ, hm, hn, repeatWord_add], hm⟩

private theorem repeatWord_count [BEq α] (w : List α) (x : α) (n : Nat) :
    (repeatWord w n).count x = n * w.count x := by
  induction n with
  | zero => simp [repeatWord]
  | succ n ih => simp [repeatWord, List.count_append, ih, Nat.succ_mul, Nat.add_comm]

private theorem coprime_no_short_commuter [BEq α] {w U : List α} {x y : α}
    (hc : Nat.Coprime (w.count x) (w.count y)) (hU : U ≠ []) (hshort : U.length < w.length)
    (he : w ++ U = U ++ w) : False := by
  obtain ⟨r, m, n, hm, hn⟩ := commute_root he
  have h₁ : m ∣ w.count x := by rw [hm, repeatWord_count]; exact Nat.dvd_mul_right _ _
  have h₂ : m ∣ w.count y := by rw [hm, repeatWord_count]; exact Nat.dvd_mul_right _ _
  have h₃ := Nat.dvd_gcd h₁ h₂
  rw [hc.gcd_eq_one] at h₃
  have he : m = 1 := Nat.dvd_one.mp h₃
  have hn' : 1 ≤ n := by
    have : n ≠ 0 := by
      intro h
      exact hU (by simp [hn, h, repeatWord])
    omega
  rw [hm, hn, repeatWord_length, repeatWord_length, he, one_mul] at hshort
  exact (not_lt_of_ge (by simpa only [one_mul] using Nat.mul_le_mul_right r.length hn')) hshort

private theorem binaryPrefix_coprime (n : Nat) :
    Nat.Coprime ((binaryPrefix n).count false) ((binaryPrefix n).count true) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Nat.Coprime (((binaryPrefix n).flatMap mu).count false)
      (((binaryPrefix n).flatMap mu).count true)
    rw [(count_mu _).1, (count_mu _).2,
      show (binaryPrefix n).count false + 2 * (binaryPrefix n).count true =
          (binaryPrefix n).count true + ((binaryPrefix n).count false +
            (binaryPrefix n).count true) by omega,
      Nat.coprime_add_self_left, Nat.coprime_add_self_right]
    exact ih.symm

private theorem code_counts (w : List Bool) :
    (piWord w).count c = w.count false ∧ (piWord w).count b = w.count true := by
  induction w with
  | nil => decide
  | cons x w ih =>
    change ((x :: w).flatMap code).count c = _ ∧ ((x :: w).flatMap code).count b = _
    rw [List.flatMap_cons, List.count_append, List.count_append, ih.1, ih.2]
    cases x <;>
      simp only [code, List.count_cons, show (a == b) = false by decide,
        show (a == c) = false by decide, show (c == b) = false by decide,
        show (b == c) = false by decide] <;> simp [Nat.add_comm]

private theorem block_coprime (n : Nat) :
    Nat.Coprime ((firstBlock n).count c) ((firstBlock n).count b) := by
  change Nat.Coprime ((piWord (binaryPrefix n)).count c) ((piWord (binaryPrefix n)).count b)
  rw [(code_counts _).1, (code_counts _).2]
  exact binaryPrefix_coprime n

private theorem mu_iter_reflect_prefix {u v : List Bool} (k : Nat)
    (h : morphIterate mu k u <+: morphIterate mu k v) : u <+: v := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (mu_reflect_prefix h)

private theorem first_second_incomparable (k : Nat) :
    ¬ (firstBlock k <+: secondBlock k ∨ secondBlock k <+: firstBlock k) := by
  rintro (h | h)
  · exact (by decide : ¬ ([false] : List Bool) <+: [true])
      (mu_iter_reflect_prefix k (code_reflect_prefix h))
  · exact (by decide : ¬ ([true] : List Bool) <+: [false])
      (mu_iter_reflect_prefix k (code_reflect_prefix h))

private theorem firstBlock_last (k : Nat) : [a, c, a, b] <:+ firstBlock (k + 1) := by
  have hn : binaryPrefix k ≠ [] := List.length_pos_iff.mp (by
    have := binaryPrefix_length k
    omega)
  let x := (binaryPrefix k).getLast hn
  have he : (binaryPrefix k).dropLast ++ [x] = binaryPrefix k :=
    List.dropLast_append_getLast hn
  change [a, c, a, b] <:+ (((binaryPrefix k).flatMap mu).flatMap code)
  rw [← he, List.flatMap_append, List.flatMap_append]
  apply List.IsSuffix.trans _ (List.suffix_append _ _)
  cases x <;> decide

-- The same palindrome conjugates both reversed block images to their unreversed forms.
private theorem block_mirror (n : Nat) :
    ∃ p : List Sigma, firstBlock (n + 1) = [a, c, a] ++ p ∧ p.head? = some b ∧
      (firstBlock (n + 1)).reverse ++ p = p ++ firstBlock (n + 1) ∧
      (secondBlock (n + 1)).reverse ++ p = p ++ secondBlock (n + 1) := by
  obtain ⟨p, hp, hpr, hpb⟩ := firstBlock_palindromes n
  refine ⟨p, hp, hpb, ?_, ?_⟩
  · rw [hp, List.reverse_append, hpr]
    simp only [List.append_assoc]
    rfl
  · cases n with
    | zero =>
      have e : p = [b] := List.append_cancel_left (as := [a, c, a]) hp.symm
      rw [e]
      decide
    | succ n =>
      obtain ⟨q, hq, hqr, _⟩ := firstBlock_palindromes n
      rw [secondBlock_succ, hp, hq]
      simp only [List.reverse_append, hpr, hqr, List.append_assoc]
      rfl

private theorem short_prefix_last {w : List Sigma} (hp : w <+: [a, c, a, b])
    (hL : w.length ≤ 3) (hb : [b] <:+ w) : False := by
  have he := List.prefix_iff_eq_take.mp hp
  rw [he] at hb
  interval_cases h : w.length <;> revert hb <;> decide

private theorem proper_prefix_last_length {U : List Sigma} {n : Nat}
    (hpre : U <+: firstBlock (n + 1)) (hshort : U.length < (firstBlock (n + 1)).length)
    (hb : [b] <:+ U) : U.length + 4 ≤ (firstBlock (n + 1)).length := by
  obtain ⟨s, hs⟩ := firstBlock_last n
  by_contra h
  have hsum : (firstBlock (n + 1)).length = s.length + 4 := by rw [← hs, List.length_append]; rfl
  have hpre' : s <+: U := List.prefix_of_prefix_length_le
    (show s <+: firstBlock (n + 1) by rw [← hs]; exact List.prefix_append _ _)
    hpre (by omega)
  obtain ⟨r, hr⟩ := hpre'
  have hlen : U.length = s.length + r.length := by rw [← hr, List.length_append]
  have hpre₀ : r <+: [a, c, a, b] := by
    rw [← hr, ← hs, List.prefix_append_right_inj] at hpre
    exact hpre
  have hb' : [b] <:+ r := by
    apply List.suffix_of_suffix_length_le hb
    · rw [← hr]
      exact List.suffix_append _ _
    · change 1 ≤ r.length
      omega
  exact short_prefix_last hpre₀ (by omega) hb'

-- If the image of a shares the reversal equation, its cut must give a cyclic
-- shift fixing the whole block.
private theorem cut_commutes {U p : List Sigma} {n : Nat}
    (hp : firstBlock (n + 1) = [a, c, a] ++ p) (hpb : p.head? = some b)
    (hU : U ≠ []) (hpre : U <+: firstBlock (n + 1))
    (hshort : U.length < (firstBlock (n + 1)).length)
    (he : U.reverse ++ p = p ++ U) : firstBlock (n + 1) ++ U = U ++ firstBlock (n + 1) := by
  have hlast : [b] <:+ U := by
    have hhead := congrArg List.head? he
    have hne : U.reverse ≠ [] := by simpa using hU
    rw [List.head?_append_of_ne_nil U.reverse hne, List.head?_append, hpb] at hhead
    exact List.singleton_suffix_iff_getLast?_eq_some.mpr (by simpa using hhead)
  have hlen := proper_prefix_last_length hpre hshort hlast
  have hpLen : (firstBlock (n + 1)).length = 3 + p.length := by rw [hp, List.length_append]; rfl
  have hUp : U.reverse <+: p :=
    List.prefix_of_prefix_length_le
      (show U.reverse <+: p ++ U by rw [← he]; exact List.prefix_append _ _)
      (List.prefix_append _ _) (by rw [List.length_reverse]; omega)
  have hUlong : 4 ≤ U.length := by
    by_contra hsmall
    have hs : [a, c, a, b] <+: firstBlock (n + 1) :=
      firstBlock_mono (Nat.succ_le_succ (Nat.zero_le n))
    have hpre' := List.prefix_of_prefix_length_le hpre hs (by
      change U.length ≤ 4
      omega)
    exact short_prefix_last hpre' (by omega) hlast
  have hstart : [a, c, a] <+: U := List.prefix_of_prefix_length_le
    (show [a, c, a] <+: firstBlock (n + 1) by rw [hp]; exact List.prefix_append _ _)
    hpre (by change 3 ≤ U.length; omega)
  have hend : [a, c, a] <:+ U.reverse := by
    apply List.reverse_prefix.mp
    simpa only [List.reverse_reverse, show ([a, c, a] : List Sigma).reverse = [a, c, a] by rfl]
      using hstart
  let v := [a, c, a] ++ U.reverse
  have hv : v <+: firstBlock (n + 1) := by
    rw [hp]
    exact (List.prefix_append_right_inj _).mpr hUp
  have hvlen : v.length = 3 + U.length := by
    simp only [v, List.length_append, List.length_reverse]
    rfl
  have hvend : [a, c, a] <:+ v := hend.trans (List.suffix_append _ _)
  obtain ⟨t, ht⟩ := List.prefix_of_prefix_length_le hpre hv (by omega)
  have htl : t.length = 3 := by
    rw [← ht, List.length_append] at hvlen
    omega
  have htt : [a, c, a] = t := by
    have hts : t <:+ v := ⟨U, ht⟩
    have hle : ([a, c, a] : List Sigma).length ≤ t.length := by rw [htl]; decide
    have heq : ([a, c, a] : List Sigma).length = t.length := by rw [htl]; decide
    exact (List.suffix_of_suffix_length_le hvend hts hle).eq_of_length heq
  have hec : [a, c, a] ++ U.reverse = U ++ [a, c, a] := ht.symm.trans (by rw [htt])
  calc
    firstBlock (n + 1) ++ U = [a, c, a] ++ (p ++ U) := by rw [hp, List.append_assoc]
    _ = ([a, c, a] ++ U.reverse) ++ p := by rw [← he, List.append_assoc]
    _ = U ++ firstBlock (n + 1) := by rw [hec, List.append_assoc, hp]

private theorem block_zero_identity {f : Morphism} (ha : (f a).head? = some a)
    (hc : f a ++ f c = firstBlock 0) (hb : f a ++ f b = secondBlock 0) :
    IsIdentityMorphism f := by
  change f a ++ f c = [a, c] at hc
  change f a ++ f b = [a, b] at hb
  obtain ⟨s, hs⟩ := List.head?_eq_some_iff.mp ha
  rw [hs] at hc hb
  have h₁ : s ++ f c = [c] := List.cons.inj hc |>.2
  have h₂ : s ++ f b = [b] := List.cons.inj hb |>.2
  have hnil : s = [] := by
    cases s with
    | nil => rfl
    | cons x xs =>
      have hx : x = c := List.cons.inj h₁ |>.1
      have hy : x = b := List.cons.inj h₂ |>.1
      exact (by decide : c ≠ b) (hx.symm.trans hy) |>.elim
  rw [hnil] at hs h₁ h₂
  intro x
  rcases (show ∀ x : Sigma, x = a ∨ x = b ∨ x = c by decide) x with rfl | rfl | rfl
  · exact hs
  · exact h₂
  · exact h₁

private theorem fixed_no_classP {f θ : Morphism} (hf : IsFixedPoint f word)
    (hni : ¬ IsIdentityMorphism f) (hc : MorphConjugate f θ) (hθ : InClassP θ) : False := by
  obtain ⟨k, hW, hV⟩ := fixed_pair_images hf
  cases k with
  | zero => exact hni (block_zero_identity (fixed_first hf) hW hV)
  | succ n =>
    let W := firstBlock (n + 1)
    let V := secondBlock (n + 1)
    let U := f a
    let S := f c
    let T := f b
    have eW : U ++ S = W := hW
    have eV : U ++ T = V := hV
    have hnot : ¬ (W <+: V ∨ V <+: W) := first_second_incomparable (n + 1)
    have hWV : W ++ V ≠ V ++ W := by
      intro e
      apply hnot
      exact List.prefix_or_prefix_of_prefix (List.prefix_append W V)
        (show V <+: W ++ V by rw [e]; exact List.prefix_append _ _)
    have hUV : U <+: W ∧ U <+: V := ⟨⟨S, eW⟩, ⟨T, eV⟩⟩
    have hU : U ≠ [] := by
      intro hnil
      have h := fixed_first hf
      change U.head? = some a at h
      simp [hnil] at h
    obtain ⟨p, hp, hpb, hpW, hpV⟩ := block_mirror n
    change W.reverse ++ p = p ++ W at hpW
    change V.reverse ++ p = p ++ V at hpV
    have hpne : p ≠ [] := by rintro rfl; simp at hpb
    let L := p ++ U
    have hLW : W.reverse ++ L = L ++ (S ++ U) := by
      change W.reverse ++ (p ++ U) = (p ++ U) ++ (S ++ U)
      rw [← List.append_assoc, hpW, ← eW]
      simp only [List.append_assoc]
    have hLV : V.reverse ++ L = L ++ (T ++ U) := by
      change V.reverse ++ (p ++ U) = (p ++ U) ++ (T ++ U)
      rw [← List.append_assoc, hpV, ← eV]
      simp only [List.append_assoc]
    rcases classP_mirror hc hθ with ⟨D, hD⟩ | ⟨K, hK⟩
    · have aux (x : Sigma) {X : List Sigma} (e : U ++ f x = X) :
          (f x ++ U) ++ D = D ++ X.reverse := by
        rw [← e, List.reverse_append, List.append_assoc, hD a, ← List.append_assoc,
          hD x, List.append_assoc]
      have hcommW : W.reverse ++ (L ++ D) = (L ++ D) ++ W.reverse := by
        rw [← List.append_assoc, hLW, List.append_assoc, aux c eW, ← List.append_assoc]
      have hcommV : V.reverse ++ (L ++ D) = (L ++ D) ++ V.reverse := by
        rw [← List.append_assoc, hLV, List.append_assoc, aux b eV, ← List.append_assoc]
      have hLD : L ++ D ≠ [] := by
        intro h
        exact hpne (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
      have he := congrArg List.reverse (shared_commute hLD hcommW hcommV)
      simp only [List.reverse_append, List.reverse_reverse] at he
      exact hWV he.symm
    · have aux (x : Sigma) {X : List Sigma} (e : U ++ f x = X) :
          X.reverse ++ K = K ++ (f x ++ U) := by
        rw [← e, List.reverse_append, List.append_assoc, hK a, ← List.append_assoc,
          hK x, List.append_assoc]
      have hcomp : ¬ (S ++ U <+: T ++ U ∨ T ++ U <+: S ++ U) := by
        intro h
        apply hnot
        rw [← eW, ← eV, List.prefix_append_right_inj, List.prefix_append_right_inj]
        have hc {s t : List Sigma} (h : s ++ U <+: t ++ U) : s <+: t := by
          have hh := h.length_le
          simp only [List.length_append] at hh
          exact (List.isPrefix_append_of_length (by omega)).mp
            ((List.prefix_append _ _).trans h)
        exact h.imp hc hc
      have hX : W.reverse ≠ [] := by
        intro h
        apply hU
        have hw : W = [] := List.reverse_eq_nil_iff.mp h
        exact (List.append_eq_nil_iff.mp (eW.trans hw)).1
      have he : K = L := shared_intertwiner_unique hX hcomp (aux c eW) (aux b eV) hLW hLV
      have hUp : U.reverse ++ p = p ++ U := by
        apply List.append_cancel_right (bs := U)
        have h := hK a
        change U.reverse ++ K = K ++ U at h
        rw [he] at h
        simpa only [L, List.append_assoc] using h
      have hshort : U.length < W.length := by
        refine lt_of_le_of_ne hUV.1.length_le ?_
        intro hlen
        have h := hUV.1.eq_of_length hlen
        exact hnot (Or.inl (h ▸ hUV.2))
      exact coprime_no_short_commuter (block_coprime (n + 1)) hU hshort
        (cut_commutes hp hpb hU hUV.1 hshort hUp)

/-- **Labbé's palindromic fixed point outside class P.** The conjecture holds: there exist a
primitive morphism $\varphi$ on the alphabet $\{0, 1, 2\}$ (some power $\varphi^n$ maps every letter
to a word containing every letter) and an infinite word $u$ such that $u$ is a fixed point of
$\varphi$, $u$ is palindromic (it has arbitrarily long palindromic factors) and uniformly recurrent
(for every factor $w$ of $u$ there is $B$ such that, for every $k$, $w$ occurs in $u$ starting at
some position in $[k, k + B]$), and no morphism $\psi$ that has $u$ as a fixed point and is not the
identity is conjugate to a morphism $\theta$ in class P. Here $u$ is a fixed point of $\psi$ when,
for some letter $a$, the word $\psi(a)$ begins with $a$, the words $\psi^m(a)$ are arbitrarily
long, and every $\psi^m(a)$ is a prefix of $u$; $\psi$ and $\theta$ are conjugate when there is a
word $w$ with $\psi(a)w = w\theta(a)$ for every letter $a$, or with $\theta(a)w = w\psi(a)$ for
every letter $a$; and $\theta$ is in class P when there is a palindrome $p$ such that each
$\theta(a)$ is $p$ followed by a palindrome.

Over a binary alphabet the question of Hof, Knill and Simon has a positive answer (Tan 2007).

Source: Sébastien Labbé, A counterexample to a question of Hof, Knill and
Simon, Electron. J. Combin. 21 (2014) #P3.11, https://doi.org/10.37236/3758. Moved from
`OpenConjectures/Combinatorics/PalindromicRecurrentOutsideP`.
-/
public theorem conjecture_holds : conjecture := by
  refine ⟨gamma, gamma_primitive, word, gamma_fixed, gamma_palindromic, gamma_recurrent, ?_⟩
  rintro ⟨f, hf, hni, θ, hc, hθ⟩
  exact fixed_no_classP hf hni hc hθ

end MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted
