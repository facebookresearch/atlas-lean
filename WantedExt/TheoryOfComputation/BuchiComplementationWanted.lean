/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rank-based Büchi complementation with an explicit state bound
-/
module

public import Batteries.Util.ProofWanted
public import Cslib.Computability.Automata.NA.Basic

@[expose] public section

namespace Cslib.BuchiComplementationWanted

open Cslib.Automata.NA
open Cslib.Automata.ωAcceptor

/-!
# Rank-based Büchi complementation with an explicit state bound

The complement of a Büchi automaton is Büchi, but the Ramsey-based proof behind
upstream `Cslib.ωLanguage.IsRegular.compl` (via the Büchi congruence) gives no
explicit bound on the size of the complement automaton. The rank-based
constructions of Kupferman–Vardi and Schewe give a complement with
`2^O(n log n)` states, where `n` is the number of states of the input automaton.
The statement below is that bound, in the form: some universal constant `c`
works for all finite alphabets and state counts.
-/

/-- Source: O. Kupferman and M. Y. Vardi, "Weak alternating automata are not
that weak", *ACM Transactions on Computational Logic* 2 (2001), 408-429
(rank-based complementation); S. Schewe, "Büchi complementation made tight",
*Proceedings of STACS 2009*, LNCS 5518, 661-672 (tight `2^O(n log n)` bound).
-/
public theorem_wanted buchi_complement_bounded_wanted :
    ∃ c : ℕ, ∀ (n k : ℕ) (a : Buchi (Fin n) (Fin k)),
      ∃ m : ℕ, m ≤ 2 ^ (c * n * (Nat.log2 (n + 1) + 1)) ∧
        ∃ b : Buchi (Fin m) (Fin k), language b = (language a)ᶜ

end Cslib.BuchiComplementationWanted
