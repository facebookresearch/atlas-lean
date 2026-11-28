/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Free
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.List.OfFn
public import MathlibExt.Combinatorics.InfinitaryHalesJewett
public import MathlibExt.Combinatorics.InfinitaryHalesJewettCentral

/-!
# Infinitary Hales–Jewett theorems for variable words

Statements quoted in Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary
Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74. A variable word over an alphabet `A` is
a list over `Option A` in which the variable `none` occurs; `w(a)` replaces every occurrence of
the variable by the letter `a`. Theorem 1.1 (Hales–Jewett) and Theorem 1.7 (`n`-variable words)
are Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension` and
`Combinatorics.Subspace.exists_mono_in_high_dimension`.

Section 3 of the paper fixes an increasing sequence of finite alphabets `A_0 ⊆ A_1 ⊆ ⋯` with
union `A`. Its statements are rendered with `A : ℕ → Finset α`, `Monotone A`, and the covering
hypothesis `∀ x, ∃ i, x ∈ A i`, so that the ambient type `α` is the alphabet `A` itself and the
semigroup `S_0` of nonempty words over `A` under concatenation is `FreeSemigroup α`. An
`n`-variable word (an element of `S_n`) is an element `w` of `FreeSemigroup (α ⊕ Fin n)` in which
every variable `Sum.inr i` occurs, and `w(a⃗)` is `FreeSemigroup.map (Sum.elim id a⃗) w`. Words
are indexed from `0` rather than `1`; since the alphabets increase, a sequence indexed from `1`
with `w_i` evaluated over `A_i` shifts to one indexed from `0` with `w_i` evaluated over `A_i`
(and conversely), so the shift does not change the statements. Products `x₀ x₁ ⋯ x_l` in a
semigroup are written as left folds `List.foldl (· * ·) x₀ [x₁, …, x_l]`. The largeness
notions (piecewise syndetic sets, `J`-sets, central sets, `C`-sets) are the reusable
definitions of `MathlibExt.Combinatorics.SemigroupLargeness`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitary Hales–Jewett theorem.** Let $A$ be a finite alphabet, and color the finite words
over $A$ with finitely many colors. A variable word over $A$ is a finite word over $A \cup \{v\}$,
for a variable $v \notin A$, in which $v$ occurs, and $w(a)$ is the word obtained from $w$ by
replacing every occurrence of $v$ by the letter $a$. Then there are a sequence $w_0, w_1, \dots$ of
variable words over $A$ and a color $k$ such that the word
$w_{m_1}(a_1) w_{m_2}(a_2) \cdots w_{m_l}(a_l)$ has color $k$ for all $l \ge 1$, all
$m_1 < m_2 < \cdots < m_l$ in $\mathbb{N}$ and all $a_1, \dots, a_l \in A$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.2 (Bergelson, Blass and Hindman). -/
public theorem_wanted infinitary_halesJewett {A κ : Type*} [Finite A] [Finite κ]
    (c : List A → κ) :
    ∃ (w : ℕ → List (Option A)) (k : κ), (∀ n, none ∈ w n) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → A), 1 ≤ l → StrictMono m →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

/-- **Karagiannis's infinitary Hales–Jewett theorem for increasing alphabets.** Let $X$ be a set,
let $A_0 \subseteq A_1 \subseteq \cdots$ be finite subsets of $X$ with union $A$, and color the
finite words over $X$ with finitely many colors. A variable word over $A$ is a finite word over
$A \cup \{v\}$, for a variable $v \notin X$, in which $v$ occurs, and $w(a)$ is the word obtained
from $w$ by replacing every occurrence of $v$ by the letter $a$. Then there are a sequence
$w_0, w_1, \dots$ of variable words over $A$ and a color $k$ such that the word
$w_{m_1}(a_1) w_{m_2}(a_2) \cdots w_{m_l}(a_l)$ has color $k$ for all $l \ge 1$, all
$m_1 < m_2 < \cdots < m_l$ in $\mathbb{N}$ and all $a_i \in A_{m_i}$, $i = 1, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.8 (Karagiannis). -/
public theorem_wanted infinitary_halesJewett_increasing_alphabets {α κ : Type*} [Finite κ]
    (A : ℕ → Finset α) (hA : Monotone A) (c : List α → κ) :
    ∃ (w : ℕ → List (Option α)) (k : κ),
      (∀ n, none ∈ w n ∧ ∀ x : α, some x ∈ w n → ∃ i, x ∈ A i) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → α), 1 ≤ l → StrictMono m →
        (∀ i, a i ∈ A (m i)) →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

end

end MetaMathlibExt
