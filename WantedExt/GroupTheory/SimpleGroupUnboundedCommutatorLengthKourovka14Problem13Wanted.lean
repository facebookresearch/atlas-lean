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

/-- `z` is a product of at most `n` commutators `x y x⁻¹ y⁻¹` of elements of `G`. -/
def IsProductOfCommutators {G : Type*} [Group G] (n : ℕ) (z : G) : Prop :=
  ∃ l : List (G × G), l.length ≤ n ∧ (l.map fun p => p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod = z

/-- Commutator length is unbounded on the derived subgroup of `G`: for every `n` some element of
`[G, G]` is not a product of `n` commutators. -/
def CommutatorLengthUnbounded (G : Type*) [Group G] : Prop :=
  ∀ n : ℕ, ∃ z ∈ commutator G, ¬ IsProductOfCommutators n z

/-- Kourovka 14.13(a) (V. G. Bardakov): there is a simple group on which commutator length is
unbounded. -/
def simpleGroupUnboundedCommutatorLength : Prop :=
  ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ CommutatorLengthUnbounded G

/-- Kourovka 14.13(b) (V. G. Bardakov): there is a finitely presented simple group on which
commutator length is unbounded. -/
def finitelyPresentedSimpleGroupUnboundedCommutatorLength : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
    CommutatorLengthUnbounded G

/--
Resolved true: the Kourovka Archive records simple groups with unbounded commutator length
constructed by Barge and Ghys (finitely generated ones by Muranov). Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.13 (V. G. Bardakov); resolution:
(a) J. Barge and É. Ghys, Math. Ann. 294 (1992), 235-265, and A. Muranov, Int. J. Algebra Comput. 17
(2007), 607-659 (finitely generated examples); (b) P.-E. Caprace and K. Fujiwara, Geom. Funct. Anal.
19 (2010), 1296-1319, Kourovka Archive, Problem 14.13 (answers: a) constructed; b) Yes, there does).
-/
public theorem_wanted simpleGroupUnboundedCommutatorLength_holds :
    simpleGroupUnboundedCommutatorLength

/--
Resolved true: the Kourovka Archive answers 14.13(b) "Yes, there does", citing Caprace and Fujiwara:
some finitely presented simple group has unbounded commutator length. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.13 (V. G. Bardakov); resolution:
(a) J. Barge and É. Ghys, Math. Ann. 294 (1992), 235-265, and A. Muranov, Int. J. Algebra Comput. 17
(2007), 607-659 (finitely generated examples); (b) P.-E. Caprace and K. Fujiwara, Geom. Funct. Anal.
19 (2010), 1296-1319, Kourovka Archive, Problem 14.13 (answers: a) constructed; b) Yes, there does).
-/
public theorem_wanted finitelyPresentedSimpleGroupUnboundedCommutatorLength_holds :
    finitelyPresentedSimpleGroupUnboundedCommutatorLength

end MathlibExt.GroupTheory.SimpleGroupUnboundedCommutatorLengthKourovka14Problem13Wanted
