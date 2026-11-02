/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ST-connectivity is NL-complete

Source:
S. A. Cook, "A hierarchy for nondeterministic time complexity" (1973) and the standard NL-
completeness of directed reachability; see S. Arora and B. Barak, Computational Complexity: A
Modern Approach, 2009, Chapter 4, and C. H. Papadimitriou, Computational Complexity, 1994,
Theorem 7.3.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.STCONNLComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# ST-connectivity is NL-complete

Directed `s-t` connectivity is in `NL` and is `NL`-hard under log-space many-one reductions.
The instance is a vertex count, a directed edge list, and distinguished `s, t`; the question is
whether some directed path joins `s` to `t`. `LogSpaceRed` is the log-space reduction of the
shared file.
-/

open Classical in
/-- **Directed $s$-$t$ connectivity.** The decision problem of directed $s$-$t$ connectivity
accepts a bitstring $x$ exactly when decoding $x$ with the canonical bitstring encoding of
tuples $(n, E, s, t)$, where $n$, $s$ and $t$ are natural numbers and $E$ is a list of pairs of
natural numbers, succeeds and gives a tuple such that $s < n$, $t < n$, and there are pairwise
distinct natural numbers $v_0, \dots, v_k$, all less than $n$, with $v_0 = s$, $v_k = t$ and
$(v_j, v_{j+1}) \in E$ for every $j < k$. Bitstrings that do not decode are rejected. -/
noncomputable def stconDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × ℕ × ℕ) x with
  | some i => decide (i.2.2.1 < i.1 ∧ i.2.2.2 < i.1 ∧
      ∃ path : List ℕ, path.Nodup ∧
      path.getD 0 0 = i.2.2.1 ∧
      path.getD (path.length - 1) 0 = i.2.2.2 ∧
      (∀ v ∈ path, v < i.1) ∧
      ∀ j, j + 1 < path.length →
        (path.getD j 0, path.getD (j + 1) 0) ∈ i.2.1)
  | none => false

/-- **ST-connectivity is NL-complete.** Directed $s$-$t$ connectivity is in NL, and every
decision problem in NL is log-space many-one reducible to directed $s$-$t$ connectivity.

Source: S. A. Cook, "A hierarchy for nondeterministic
time complexity" (1973) and the standard NL-completeness of directed reachability; see S.
Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 4, and C.
H. Papadimitriou, Computational Complexity, 1994, Theorem 7.3. -/
public theorem_wanted stcon_nl_complete :
    stconDec ∈ NL ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ NL → LogSpaceRed L stconDec

end MetaMathlibExt.Complexity.KeyTheorems.STCONNLComplete
