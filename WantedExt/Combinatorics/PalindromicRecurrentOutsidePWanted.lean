/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-4425-004: Palindromic recurrent words outside class P.
RESOLVED TRUE: Labbé (EJC 21 (2014) #P3.11, arXiv:1307.1589, Theorem 1)
exhibited a palindromic, uniformly recurrent fixed point of a primitive
ternary morphism that is fixed by no non-identity morphism with a
conjugate in class P. The binary case holds (Bo Tan, Mirror substitutions
and palindromic sequences, Theoret. Comput. Sci. 389 (2007)).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.List.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted

/-! Source record `OWR-4425-004`. Resolution: Labbé 2014, EJC 21 #P3.11. -/

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

Source: [OWR-4425-004] Labbé, A counterexample to a question of Hof, Knill and Simon, EJC 21
(2014) #P3.11, Theorem 1. -/
def conjecture : Prop :=
  ∃ φ : Morphism, IsPrimitive φ ∧
    ∃ u : InfWord, IsFixedPoint φ u ∧ IsPalindromic u ∧
      IsUniformlyRecurrent u ∧
      ¬ ∃ ψ : Morphism, IsFixedPoint ψ u ∧ ¬ IsIdentityMorphism ψ ∧
        ∃ θ : Morphism, MorphConjugate ψ θ ∧ InClassP θ

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
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted
