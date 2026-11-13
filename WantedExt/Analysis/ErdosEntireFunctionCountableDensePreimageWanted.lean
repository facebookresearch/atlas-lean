/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Realizing countable dense sets as fibers of an entire function (AMR-022-2031)

Erdos asked whether, for any two countable dense plane sets `A` and `B`,
some entire function takes values in `B` exactly on `A`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted

/-! Source record `AMR-022-2031`. -/

/-- **Erdős's problem on countable dense preimages.** This is the statement that for any two
countable dense subsets $A$ and $B$ of $\mathbb{C}$, there is an entire function
$f : \mathbb{C} \to \mathbb{C}$ such that for every $z \in \mathbb{C}$, $f(z) \in B$ if and only
if $z \in A$; that is, $f^{-1}(B) = A$.

Source: Research Problems in Function Theory, Problem 2.31 (record AMR-022-2031). -/
def conjecture : Prop :=
  ∀ A B : Set ℂ, A.Countable → Dense A → B.Countable → Dense B →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Set.univ ∧ ∀ z, (f z ∈ B ↔ z ∈ A)

/--
**Every countable dense set is a preimage of any other under an entire function.** For any two
countable dense subsets $A$ and $B$ of $\mathbb{C}$, there is an entire function
$f : \mathbb{C} \to \mathbb{C}$ such that for every $z \in \mathbb{C}$, $f(z) \in B$ if and only
if $z \in A$; that is, $f^{-1}(B) = A$.

Hayman's update to Problem 2.31 reports that Barth and Schneider constructed such functions.

Source: K. F. Barth and W. J.
Schneider, Entire functions mapping arbitrary countable dense sets and their complements onto
each other, J. London Math. Soc. (2) 4 (1972), 482-488, https://doi.org/10.1112/jlms/s2-4.3.482.
Moved from `OpenConjectures/Analysis/ErdosEntireFunctionCountableDensePreimage`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted
