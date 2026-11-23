/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1022
-/
module

public import MathlibExt.Data.Finset.PropertyB
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GraphTheory.ErdosProblem1022Wanted

/-! Source record `FC-ErdosProblem1022`, ported from FormalConjectures
`ErdosProblems/1022.lean` (`def SparseImpliesPropertyB`,
`theorem erdos_1022`, `lt_two`, `lovasz`) and checked against
erdosproblems.com/1022. The `answer` wrappers are dropped (`False`
elaborated to a negation). Property B is MathlibExt's
`Finset.HasPropertyB`. Status: resolved false (Wood [Wo13b]; formalized in Lean). The
historical positive claim (some diverging sparsity constant forces
property B) is preserved as the registered target `mainPositive`
(disproved); its negation is the unregistered companion `disprovedMain`.
The `c < 2` limitation and the pairs optimum `c = 1` are separate
established targets. -/

/-- `SparseImpliesPropertyB t c` asserts that every finite family `F` of
finite sets, all of size at least `t`, such that for every nonempty finite
set `X` there are `< c * |X|` many `A \in F` with `A \subseteq X`, has property B. -/
def SparseImpliesPropertyB (t : ℕ) (c : ℝ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ A ∈ F, t ≤ A.card) →
    (∀ X : Finset ℕ, X.Nonempty → ((F.filter (· ⊆ X)).card : ℝ) < c * (X.card : ℝ)) →
    F.HasPropertyB

/-- The historical positive claim: some diverging sparsity constant forces
property B (disproved). -/
def mainPositive : Prop :=
  ∃ c : ℕ → ℝ, Filter.Tendsto c Filter.atTop Filter.atTop ∧
    ∀ t : ℕ, SparseImpliesPropertyB t (c t)

/-- Its disproof (companion). -/
def disprovedMain : Prop := ¬ mainPositive

/-- Every sparsity constant forcing property B is below `2` (established). -/
def constantBelowTwo : Prop :=
  ∀ (t : ℕ) (c : ℝ), SparseImpliesPropertyB t c → c < 2

/-- For pairs, `c = 1` is the greatest working sparsity constant
(established). -/
def pairsOptimumOne : Prop :=
  IsGreatest {c : ℝ | SparseImpliesPropertyB 2 c} 1

/--
Resolved false: Answered negatively per erdosproblems.com/1022: 'This is false, and c_t < 2 for
all t': Wood [Wo13b] constructs, for any r ≥ 2, a triangle-free 2-degenerate r-uniform
hypergraph with chromatic number 3. The registered mainPositive is refuted; the companion
targets constantBelowTwo (c_t < 2 for every t) and pairsOptimumOne (c_2 = 1, which Erdős reports
in [Er71] was proved by Lovász) hold. This target is refuted: The page: 'This is false, and
c_t<2 for all t' (Wood [Wo13b]), so no sparsity constant tending to infinity forces property B;
formal-conjectures erdos_1022 states exactly this negation (category research solved), proved in
Lean as not_erdos_1022 (plby/lean-proofs ErdosProblems/Erdos1022.lean). Source: Wood [Wo13b]
(triangle-free 2-degenerate r-uniform hypergraphs with chromatic number 3; formalized in Lean),
per erdosproblems.com/1022, https://www.erdosproblems.com/1022; Lovasz (c_2 = 1, reported by
Erdos in [Er71]), per erdosproblems.com/1022, https://www.erdosproblems.com/1022. Moved from
`OpenConjectures/GraphTheory/ErdosProblem1022`.
-/
public theorem_wanted mainPositive_refuted : ¬ mainPositive

/--
Resolved false: Answered negatively per erdosproblems.com/1022: 'This is false, and c_t < 2 for
all t': Wood [Wo13b] constructs, for any r ≥ 2, a triangle-free 2-degenerate r-uniform
hypergraph with chromatic number 3. The registered mainPositive is refuted; the companion
targets constantBelowTwo (c_t < 2 for every t) and pairsOptimumOne (c_2 = 1, which Erdős reports
in [Er71] was proved by Lovász) hold. This target holds: The page states c_t<2 for all t, from
Wood's 2-degenerate r-uniform hypergraphs of chromatic number 3 for every r≥2 [Wo13b]; this is
the target, stated in formal-conjectures as erdos_1022.variants.lt_two (category research
solved). Source: Wood [Wo13b] (triangle-free 2-degenerate r-uniform hypergraphs with chromatic
number 3; formalized in Lean), per erdosproblems.com/1022, https://www.erdosproblems.com/1022;
Lovasz (c_2 = 1, reported by Erdos in [Er71]), per erdosproblems.com/1022,
https://www.erdosproblems.com/1022. Moved from `OpenConjectures/GraphTheory/ErdosProblem1022`.
-/
public theorem_wanted constantBelowTwo_holds : constantBelowTwo

/--
Resolved false: Answered negatively per erdosproblems.com/1022: 'This is false, and c_t < 2 for
all t': Wood [Wo13b] constructs, for any r ≥ 2, a triangle-free 2-degenerate r-uniform
hypergraph with chromatic number 3. The registered mainPositive is refuted; the companion
targets constantBelowTwo (c_t < 2 for every t) and pairsOptimumOne (c_2 = 1, which Erdős reports
in [Er71] was proved by Lovász) hold. This target holds: The page records c_2=1, Erdős's
conjecture which he reports in [Er71] was proved by Lovász; this is the target, stated in
formal-conjectures as erdos_1022.variants.lovasz, IsGreatest {c | SparseImpliesPropertyB 2 c} 1
(category research solved). Source: Wood [Wo13b] (triangle-free 2-degenerate r-uniform
hypergraphs with chromatic number 3; formalized in Lean), per erdosproblems.com/1022,
https://www.erdosproblems.com/1022; Lovasz (c_2 = 1, reported by Erdos in [Er71]), per
erdosproblems.com/1022, https://www.erdosproblems.com/1022. Moved from
`OpenConjectures/GraphTheory/ErdosProblem1022`.
-/
public theorem_wanted pairsOptimumOne_holds : pairsOptimumOne

end MathlibExt.GraphTheory.ErdosProblem1022Wanted
