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
/-- **Directed graph non-isomorphism as a decision problem.** The decision problem accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of triples
$(n, E_1, E_2)$ of a natural number and two lists of pairs of natural numbers, to a triple for
which there is no bijection $f$ from $\{0, \ldots, n - 1\}$ to itself such that, for all
$a, b < n$, $(a, b) \in E_1$ if and only if $(f(a), f(b)) \in E_2$. Bitstrings that do not
decode are rejected.

Pairs in $E_1$ or $E_2$ with an entry at least $n$ play no role, so $E_1$ and $E_2$ are read as
directed graphs on the vertex set $\{0, \ldots, n - 1\}$. -/
noncomputable def graphNonIsoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) x with
  | some i => decide (¬ ∃ f : Fin i.1 → Fin i.1, Function.Bijective f ∧
      ∀ a b : Fin i.1,
        ((a.val, b.val) ∈ i.2.1 ↔ ((f a).val, (f b).val) ∈ i.2.2))
  | none => false

/-- **Graph non-isomorphism is in AM.** The directed graph non-isomorphism decision problem
belongs to the class $\mathsf{AM}$ of decision problems decided by Arthur–Merlin protocols.

Source: O. Goldreich, S. Micali, and A. Wigderson,
"Proofs that yield nothing but their validity, or all languages in NP have zero-knowledge
proof systems", Journal of the ACM 38 (1991), 691-729 (FOCS 1986); O. Goldwasser and M.
Sipser, "Private coins versus public coins in interactive proof systems", Advances in
Computing Research 5 (1989), 73-90. -/
public theorem_wanted graph_noniso_in_am :
    graphNonIsoDec ∈ AM

end MetaMathlibExt.Complexity.KeyTheorems.GNIInAM
