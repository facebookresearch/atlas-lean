/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with unbounded commutator length (Kourovka Notebook Problem 14.13)

Kourovka Notebook, Archive of Solved Problems, Problem 14.13 (V. G. Bardakov): (a) does there exist
a simple group on which the commutator length is not bounded? (b) does there exist a finitely
presented simple group on which the commutator length is not bounded?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupUnboundedCommutatorLengthKourovka14Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.13 (V. G.
Bardakov). UnsolvedMath record UM-00700998 (`KOU-14.13`), dataset ulamai/UnsolvedMath v1.8.0.

The commutator length of `z ∈ [G, G]` is the least number of commutators `x y x⁻¹ y⁻¹` whose product
is `z`; unbounded means that for every `n` some `z ∈ [G, G]` is not a product of `n` commutators.
Finitely presented is Mathlib's `Group.IsFinitelyPresented`.
-/

/-- **Products of at most $n$ commutators.** An element $z$ of a group $G$ is a product of at most
$n$ commutators when $z = [x_1, y_1] \cdots [x_k, y_k]$ for some $k \le n$ and some
$x_1, y_1, \dots, x_k, y_k \in G$, where $[x, y] = x y x^{-1} y^{-1}$; for $k = 0$ the product is
the identity. -/
def IsProductOfCommutators {G : Type*} [Group G] (n : ℕ) (z : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ n ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = z

/-- **Unbounded commutator length.** A group $G$ has unbounded commutator length when for every
natural number $n$ some element of the derived subgroup $[G, G]$ is not a product of at most $n$
commutators $x y x^{-1} y^{-1}$ with $x, y \in G$. -/
def CommutatorLengthUnbounded (G : Type*) [Group G] : Prop :=
  ∀ n : ℕ, ∃ z ∈ commutator G, ¬ IsProductOfCommutators n z

/-- **Kourovka Problem 14.13(a) (Bardakov).** The statement that there is a simple group $G$ such
that for every natural number $n$ some element of the derived subgroup $[G, G]$ is not a product of
at most $n$ commutators $x y x^{-1} y^{-1}$ with $x, y \in G$. -/
def simpleGroupUnboundedCommutatorLength : Prop :=
  ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ CommutatorLengthUnbounded G

/-- **Kourovka Problem 14.13(b) (Bardakov).** The statement that there is a finitely presented
simple group $G$ such that for every natural number $n$ some element of the derived subgroup
$[G, G]$ is not a product of at most $n$ commutators $x y x^{-1} y^{-1}$ with $x, y \in G$. -/
def finitelyPresentedSimpleGroupUnboundedCommutatorLength : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
    CommutatorLengthUnbounded G

/-- **A simple group with unbounded commutator length.** There is a simple group $G$ such that for
every natural number $n$ some element of the derived subgroup $[G, G]$ is not a product of at most
$n$ commutators $x y x^{-1} y^{-1}$ with $x, y \in G$. This answers Kourovka Problem 14.13(a) in
the affirmative; the Kourovka Archive records examples constructed by Barge and Ghys, and finitely
generated ones by Muranov.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.13 (V. G. Bardakov); resolution:
(a) J. Barge and É. Ghys, Math. Ann. 294 (1992), 235-265, and A. Muranov, Int. J. Algebra Comput. 17
(2007), 607-659 (finitely generated examples); (b) P.-E. Caprace and K. Fujiwara, Geom. Funct. Anal.
19 (2010), 1296-1319, Kourovka Archive, Problem 14.13 (answers: a) constructed; b) Yes, there does).
-/
public theorem_wanted simpleGroupUnboundedCommutatorLength_holds :
    simpleGroupUnboundedCommutatorLength

/-- **A finitely presented simple group with unbounded commutator length.** There is a finitely
presented simple group $G$ such that for every natural number $n$ some element of the derived
subgroup $[G, G]$ is not a product of at most $n$ commutators $x y x^{-1} y^{-1}$ with
$x, y \in G$. This answers Kourovka Problem 14.13(b) in the affirmative; the Kourovka Archive cites
Caprace and Fujiwara.

Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.13 (V. G. Bardakov); resolution:
(a) J. Barge and É. Ghys, Math. Ann. 294 (1992), 235-265, and A. Muranov, Int. J. Algebra Comput. 17
(2007), 607-659 (finitely generated examples); (b) P.-E. Caprace and K. Fujiwara, Geom. Funct. Anal.
19 (2010), 1296-1319, Kourovka Archive, Problem 14.13 (answers: a) constructed; b) Yes, there does).
-/
public theorem_wanted finitelyPresentedSimpleGroupUnboundedCommutatorLength_holds :
    finitelyPresentedSimpleGroupUnboundedCommutatorLength

end MathlibExt.GroupTheory.SimpleGroupUnboundedCommutatorLengthKourovka14Problem13Wanted
