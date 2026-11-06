/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted

/-- **Sumset of a finite set of integers.** For a finite set $A \subseteq \mathbb{Z}$, the sumset
$A + A = \{a + b : a, b \in A\}$, a finite set of integers.

Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzSumset (A : Finset ℤ) : Finset ℤ :=
  Finset.image (fun p : ℤ × ℤ => p.1 + p.2) (Finset.product A A)

/-- **Arithmetic progressions in a finite set of integers, as pairs.** For a natural number $k$
and a finite set $A \subseteq \mathbb{Z}$, the set of pairs $(a, d)$ of integers such that
$a + i d \in A$ for every natural number $i < k$. The pair $(a, d)$ stands for the $k$-term
arithmetic progression $a, a + d, \dots, a + (k - 1)d$; the difference $d$ may be zero or
negative.

Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzAPSet (k : ℕ) (A : Finset ℤ) : Set (ℤ × ℤ) :=
  {p : ℤ × ℤ | ∀ i : ℕ, i < k → p.1 + (i : ℤ) * p.2 ∈ A}

/-- **Katz's question on progressions in sets of small doubling.** For a finite set
$A \subseteq \mathbb{Z}$ write $A + A = \{a + b : a, b \in A\}$. This is the statement that for
every natural number $k \ge 3$ and every real number $C \ge 2$ there is a real number $c > 0$ such
that every finite set $A \subseteq \mathbb{Z}$ with $|A + A| < C|A|$ has at least $c|A|^2$ pairs
$(a, d)$ of integers with $a + i d \in A$ for all natural numbers $i < k$.

Each pair $(a, d)$ is a $k$-term arithmetic progression $a, a + d, \dots, a + (k - 1)d$ in $A$;
pairs with $d = 0$ or $d < 0$ are counted too. The question is Problem 1.5 of the AIM problem
list on additive combinatorics, posed by N. Katz.

Source: [AIM-COMBINATORICS-0211], AIM Problem Lists, Recent
trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`,
https://aimath.org/WWN/additivecomb/additivecomb.pdf. -/
def conjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ C : ℝ, 2 ≤ C → ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ,
    (Finset.card (katzSumset A) : ℝ) < C * (Finset.card A : ℝ) →
    c * ((Finset.card A : ℝ) ^ 2) ≤ (Set.ncard (katzAPSet k A) : ℝ)

/--
**Sets of small doubling contain many arithmetic progressions.** For a finite set
$A \subseteq \mathbb{Z}$ write $A + A = \{a + b : a, b \in A\}$. For every natural number $k \ge 3$
and every real number $C \ge 2$ there is a real number $c > 0$ such that every finite set
$A \subseteq \mathbb{Z}$ with $|A + A| < C|A|$ has at least $c|A|^2$ pairs $(a, d)$ of integers
with $a + i d \in A$ for all natural numbers $i < k$.

This answers Katz's Problem 1.5 affirmatively. On the AIM additive-combinatorics list B. Green
observes that a large subset of $A$ is Freiman-isomorphic to a dense subset of
$\mathbb{Z}/p\mathbb{Z}$ (Ruzsa's lemma), and Szemerédi's theorem with Varnavides averaging gives
$\gg_{k,C} |A|^2$ $k$-term progressions. The pairs with $d = 0$ counted here cover small sets.

Source: AIM
workshop problem list, Additive combinatorics (additivecomb.pdf), Problem 1.5 (N. Katz) and
remark by B. Green, https://aimath.org/WWN/additivecomb/additivecomb.pdf. Moved from
`OpenConjectures/Combinatorics/KatzSmallDoublingProgressions`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted
