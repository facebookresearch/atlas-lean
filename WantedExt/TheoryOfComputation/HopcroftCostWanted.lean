/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.Congruences.HopcroftCost

@[expose] public section

set_option autoImplicit false

namespace Cslib.HopcroftCostWanted

/-- **Hopcroft's total-work bound**: the predecessor cost of processing every splitter
popped by Hopcroft's loop is `O(|Σ| n log n)`, where `n` is the number of states. The
cost is `DFA.Hopcroft.hopcroftCost` of the popped-splitter trace
`DFA.Hopcroft.hopcroftSplitters`: for each popped splitter `(C, a)`, one predecessor
visit per state whose `a`-successor lies in `C`, i.e. `(preimage M C a).card`, plus `1`
per-splitter overhead for popping and bookkeeping. The bound is stated with an absolute
constant `C`, so no particular constant is claimed.

The summand must be the preimage size, not the splitter size `C.card`: with reverse
transitions, processing `(C, a)` visits the predecessors of `C`, and each predecessor is
visited exactly once (each state has exactly one `a`-successor). Charging `C.card`
undercounts: if all `n` states transition on `a` to one state `q`, processing the
singleton splitter `({q}, a)` costs `n` predecessor visits while `C.card` charges only
`1`. The counting lemma behind the bound, that a state lies in the smaller half of a
split block at most `log₂ n` times, is proved in CSLibExt as
`DFA.Hopcroft.smaller_half_chain_le_log`; what remains is the charging argument turning
that lemma into a bound on the predecessor cost.
Source: J. E. Hopcroft, "An `n log n` algorithm for minimizing states in a finite
automaton", Theory of Machines and Computations, 1971; J. Berstel, L. Boasson, O. Carton
and I. Fagnot, "Minimization of automata", 2010. -/
theorem_wanted hopcroft_total_work :
  ∃ C : ℕ, ∀ (α σ : Type) [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ) [DecidablePred (· ∈ M.accept)],
    DFA.Hopcroft.hopcroftCost M (DFA.Hopcroft.hopcroftSplitters M
      (Fintype.card α * (Fintype.card σ + 1)) (DFA.Hopcroft.initP M)
      (DFA.Hopcroft.initW M)) ≤
      C * Fintype.card α * (Fintype.card σ + 1) *
        (Nat.log 2 (Fintype.card σ + 1) + 1)

end Cslib.HopcroftCostWanted
