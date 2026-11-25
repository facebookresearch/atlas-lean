/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Choose.Multinomial

@[expose] public section

namespace MetaMathlibExt

/-- **Base-$b$ digit of a natural number.** For natural numbers $b$, $n$ and $l$, the rank-$l$
base-$b$ digit $n_l$ of $n$ is the entry at position $l$ (counting from $0$) of the list of
base-$b$ digits of $n$, least significant digit first, and $0$ when $l$ is at least the length of
that list (with $0$ having no digits). For $b \ge 2$ this is the coefficient of $b^l$ in the
base-$b$ expansion of $n$.

For $b \le 1$ the digit list follows Mathlib's convention: for $b = 0$ a positive $n$ has the
single digit $n$, and for $b = 1$ the digits of $n$ are $n$ ones.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca` (`b-ary multinomial coefficient`), notation $(k_i)_l$ and
$n_l$ of source statement `jis_2dd3152b04bd3c701907ca5c` (byte-identical duplicate
`jis_40ae94aec46faf8f37032d00`).

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex
(`df0640a5d745b80e57565a61040414d4305680a9a5700ce376a717ffdc6f2571`),
span bytes/chars 16014..16622, lines 349..359,
raw TeX SHA-256 `ce098c5865cf6b3b380b6a679820635672ac58a52901ab8de41afd2c8a54d46b`. -/
public def bAryDigit (b n l : ℕ) : ℕ := (Nat.digits b n).getD l 0

/-- **Rank-$l$ base-$b$ digits of a list.** For natural numbers $b$ and $l$ and a list
$(k_1, \dots, k_m)$ of natural numbers, this is the list $((k_1)_l, \dots, (k_m)_l)$, where
$(k_i)_l$ is the rank-$l$ base-$b$ digit of $k_i$.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
public def bAryLowerDigits (b : ℕ) (ks : List ℕ) (l : ℕ) : List ℕ :=
  ks.map (fun k => bAryDigit b k l)

/-- **Multinomial coefficient with a prescribed top.** For a natural number $t$ and a list
$(a_1, \dots, a_m)$ of natural numbers, the multinomial factor of $t$ over $(a_1, \dots, a_m)$ is
$\frac{t!}{a_1! \cdots a_m!}$ if $a_1 + \dots + a_m = t$, and $0$ otherwise.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic
child `jis_sem_8f93866ba77d801d9ead13ca`, statements
`jis_2dd3152b04bd3c701907ca5c` and `jis_40ae94aec46faf8f37032d00`. -/
public def ordinaryMultinomialFactor (top : ℕ) (lowers : List ℕ) : ℕ :=
  if lowers.sum = top then lowers.multinomial else 0

/-- **Digitwise $b$-ary multinomial factor.** For natural numbers $b$, $n$ and $l$ and a list
$(k_1, \dots, k_m)$ of natural numbers, let $n_l$ and $(k_i)_l$ be the rank-$l$ base-$b$ digits
of $n$ and $k_i$. The factor at rank $l$ is $\frac{n_l!}{(k_1)_l! \cdots (k_m)_l!}$ if
$(k_1)_l + \dots + (k_m)_l = n_l$, and $0$ otherwise.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
public def bAryMultinomialFactor (b n : ℕ) (ks : List ℕ) (l : ℕ) : ℕ :=
  ordinaryMultinomialFactor (bAryDigit b n l) (bAryLowerDigits b ks l)

/-- **Digit-length bound for the $b$-ary multinomial coefficient.** For natural numbers $b$ and
$n$ and a list $(k_1, \dots, k_m)$ of natural numbers, the bound is the largest of the numbers of
base-$b$ digits of $n, k_1, \dots, k_m$ (with $0$ having no digits).

Every nonzero base-$b$ digit of $n$ and of each $k_i$ has rank below the bound, so at every higher
rank the digitwise $b$-ary multinomial factor equals $1$; this plays the role of the source's
sufficiently large $N$.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca`, statements `jis_2dd3152b04bd3c701907ca5c`
and `jis_40ae94aec46faf8f37032d00`. -/
public def bAryMultinomialBound (b n : ℕ) (ks : List ℕ) : ℕ :=
  max ((Nat.digits b n).length)
    (((ks.map (fun k => (Nat.digits b k).length)).max?).getD 0)

/-- **The $b$-ary multinomial coefficient.** Let $b \ge 2$, let $n$ be a natural number and let
$(k_1, \dots, k_m)$ be a list of natural numbers, and write $n_l$ and $(k_i)_l$ for the rank-$l$
base-$b$ digits of $n$ and $k_i$ (taken to be $0$ beyond the last digit, with $0$ having no
digits). Let $N$ be the largest of the numbers of base-$b$ digits of $n, k_1, \dots, k_m$. The
$b$-ary multinomial coefficient of $n$ over $(k_1, \dots, k_m)$ is $\prod_{l=0}^{N-1} c_l$, where
$c_l = \frac{n_l!}{(k_1)_l! \cdots (k_m)_l!}$ if $(k_1)_l + \dots + (k_m)_l = n_l$ and $c_l = 0$
otherwise.

Source: concept `jis_term_48a88a0d7fe1b70bcdb0254d`, semantic child
`jis_sem_8f93866ba77d801d9ead13ca` (`b-ary multinomial coefficient`), atomic coefficient
definition of source statement `jis_2dd3152b04bd3c701907ca5c` (byte-identical duplicate
`jis_40ae94aec46faf8f37032d00`).

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.tex
(`df0640a5d745b80e57565a61040414d4305680a9a5700ce376a717ffdc6f2571`),
span bytes/chars 16014..16622, lines 349..359,
raw TeX SHA-256 `ce098c5865cf6b3b380b6a679820635672ac58a52901ab8de41afd2c8a54d46b`. -/
public def bAryMultinomial (b n : ℕ) (ks : List ℕ) (hb : 2 ≤ b) : ℕ :=
  let _ : 2 ≤ b := hb
  (Finset.range (bAryMultinomialBound b n ks)).prod
    (fun l => bAryMultinomialFactor b n ks l)

end MetaMathlibExt
