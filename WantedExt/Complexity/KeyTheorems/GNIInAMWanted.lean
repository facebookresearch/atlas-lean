/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graph non-isomorphism is in AM

Source:
O. Goldreich, S. Micali, and A. Wigderson, "Proofs that yield nothing but their validity, or
all languages in NP have zero-knowledge proof systems", Journal of the ACM 38 (1991), 691-729
(FOCS 1986); O. Goldwasser and M. Sipser, "Private coins versus public coins in interactive
proof systems", Advances in Computing Research 5 (1989), 73-90.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GNIInAM

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Graph non-isomorphism is in AM

Directed graph non-isomorphism is in `AM`: Arthur picks a random graph and a random isomorphic
copy, Merlin names which of the two graphs the copy came from; the set lower-bound protocol
makes this an Arthur-Merlin proof. The instance decodes as in the graph-isomorphism file, and
the predicate is the negation of isomorphism.
-/

open Classical in
/-- Directed graph non-isomorphism as a decision problem over bitstrings. -/
noncomputable def graphNonIsoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) x with
  | some i => decide (¬ ∃ f : Fin i.1 → Fin i.1, Function.Bijective f ∧
      ∀ a b : Fin i.1,
        ((a.val, b.val) ∈ i.2.1 ↔ ((f a).val, (f b).val) ∈ i.2.2))
  | none => false

/-- **Graph non-isomorphism is in AM.** Source: O. Goldreich, S. Micali, and A. Wigderson,
"Proofs that yield nothing but their validity, or all languages in NP have zero-knowledge
proof systems", Journal of the ACM 38 (1991), 691-729 (FOCS 1986); O. Goldwasser and M.
Sipser, "Private coins versus public coins in interactive proof systems", Advances in
Computing Research 5 (1989), 73-90. -/
public theorem_wanted graph_noniso_in_am :
    graphNonIsoDec ∈ AM

end MetaMathlibExt.Complexity.KeyTheorems.GNIInAM
