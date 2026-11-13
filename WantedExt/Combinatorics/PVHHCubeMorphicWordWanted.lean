/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Basic

namespace MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted

/-- **The alphabet $\{0, 1, 3, 4\}$.** The alphabet with four distinct letters, written $0$, $1$,
$3$ and $4$. -/
inductive Letter where
  | zero
  | one
  | three
  | four
  deriving DecidableEq

/-- **The substitution $0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$.** The map
sending each letter of the alphabet $\{0, 1, 3, 4\}$ to a word: $0$ to $03$, $1$ to $43$, $3$ to
$1$ and $4$ to $01$. -/
def substitution : Letter → List Letter
  | .zero => [.zero, .three]
  | .one => [.four, .three]
  | .three => [.one]
  | .four => [.zero, .one]

/-- **Iterates of the substitution on $0$.** For $k \ge 0$, the word $\sigma^k(0)$ obtained from
the one-letter word $0$ by applying the substitution $\sigma$ ($0 \mapsto 03$, $1 \mapsto 43$,
$3 \mapsto 1$, $4 \mapsto 01$) $k$ times, where $\sigma$ acts on a word by replacing each letter
with its image: $\sigma^0(0) = 0$ and $\sigma^{k+1}(0) = \sigma(\sigma^k(0))$. -/
def substitutionIterate : ℕ → List Letter
  | 0 => [.zero]
  | k + 1 => (substitutionIterate k).flatMap substitution

/-- **The fixed point generated from $0$.** Let $\sigma$ be the substitution $0 \mapsto 03$,
$1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet $\{0, 1, 3, 4\}$, extended to words
by replacing each letter with its image. An infinite word $w = w_0 w_1 w_2 \cdots$ over
$\{0, 1, 3, 4\}$ is the fixed point generated from $0$ if the word $\sigma^k(0)$ is a prefix of $w$
for every $k \ge 0$. -/
def IsGeneratedFixedPoint (w : ℕ → Letter) : Prop :=
  ∀ k i (hi : i < (substitutionIterate k).length),
    w i = (substitutionIterate k).get ⟨i, hi⟩

/-- **Value of a letter.** Each letter of the alphabet $\{0, 1, 3, 4\}$ has as its value the
integer it names: the letters $0$, $1$, $3$ and $4$ have values $0$, $1$, $3$ and $4$. -/
def letterValue : Letter → ℤ
  | .zero => 0
  | .one => 1
  | .three => 3
  | .four => 4

/-- **Sum of a factor.** For an infinite word $w = w_0 w_1 w_2 \cdots$ over the alphabet
$\{0, 1, 3, 4\}$ and natural numbers $s$ and $\ell$, the sum of the factor of length $\ell$
starting at position $s$ is the integer $\sum_{i=0}^{\ell-1} w_{s+i}$, where each letter counts
as its value. -/
def factorSum (w : ℕ → Letter) (start length : ℕ) : ℤ :=
  (Finset.range length).sum fun i ↦ letterValue (w (start + i))

/-- **Avoiding additive cubes.** An infinite word $w = w_0 w_1 w_2 \cdots$ over the alphabet
$\{0, 1, 3, 4\}$ avoids PVHH-cubes (additive cubes) if there are no natural numbers $s$ and
$\ell \ge 1$ such that the three consecutive factors $w_s \cdots w_{s+\ell-1}$,
$w_{s+\ell} \cdots w_{s+2\ell-1}$ and $w_{s+2\ell} \cdots w_{s+3\ell-1}$ of length $\ell$ all have
the same sum of letter values. -/
def AvoidsPVHHCubes (w : ℕ → Letter) : Prop :=
  ∀ start length, 0 < length →
    ¬(factorSum w start length = factorSum w (start + length) length ∧
      factorSum w (start + length) length = factorSum w (start + 2 * length) length)

/-- **Additive-cube-free fixed point conjecture.** Let $\sigma$ be the substitution
$0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet $\{0, 1, 3, 4\}$,
extended to words by replacing each letter with its image. The proposition that there is an
infinite word $w$ over $\{0, 1, 3, 4\}$ such that $\sigma^k(0)$ is a prefix of $w$ for every
$k \ge 0$ and $w$ avoids PVHH-cubes (additive cubes): no three consecutive nonempty factors of $w$
of equal length have equal sums of letter values. -/
def conjecture : Prop :=
  ∃ w : ℕ → Letter, IsGeneratedFixedPoint w ∧ AvoidsPVHHCubes w

/-- **The Cassaigne–Currie–Schaeffer–Shallit word avoids additive cubes.** Let $\sigma$ be the
substitution $0 \mapsto 03$, $1 \mapsto 43$, $3 \mapsto 1$, $4 \mapsto 01$ on the alphabet
$\{0, 1, 3, 4\}$, extended to words by replacing each letter with its image. There is an infinite
word $w = w_0 w_1 w_2 \cdots$ over $\{0, 1, 3, 4\}$ such that $\sigma^k(0)$ is a prefix of $w$ for
every $k \ge 0$, and $w$ contains no additive cube: there are no natural numbers $s$ and
$\ell \ge 1$ such that the three consecutive factors of length $\ell$ starting at positions $s$,
$s + \ell$ and $s + 2\ell$ all have the same sum of letter values.

Source: Julien Cassaigne, James
D. Currie, Luke Schaeffer and Jeffrey Shallit, Avoiding three consecutive blocks of the same
size and same sum, J. ACM 61(2) (2014), Article 10, arXiv:1106.5204,
https://arxiv.org/abs/1106.5204. Moved from `OpenConjectures/Combinatorics/PVHHCubeMorphicWord`.
-/
theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted
