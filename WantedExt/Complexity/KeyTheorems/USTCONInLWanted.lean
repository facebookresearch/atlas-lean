/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Undirected ST-connectivity is in L (Reingold)

Source:
O. Reingold, "Undirected connectivity in log-space", Journal of the ACM 55 (2008), 1-24 (STOC
2005).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.USTCONInL

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Undirected ST-connectivity is in L (Reingold)

Undirected `s-t` connectivity is in deterministic logarithmic space. The instance is a vertex
count, an undirected edge list, and distinguished `s, t`; the question is whether some
undirected path joins `s` to `t`. The proof is Reingold's log-space algorithm via the zig-zag
product.
-/

open Classical in
/-- **Undirected s-t connectivity as a decision problem.** A bitstring $x$ is a yes-instance
exactly when bitstring decoding of $x$, as a tuple $(n, E, s, t)$ of natural numbers $n$, $s$, $t$
and a finite list $E$ of pairs of natural numbers, succeeds and returns $(n, E, s, t)$ such that
$s < n$, $t < n$, and there are pairwise distinct natural numbers $v_0, \dots, v_k$, all less than
$n$, with $v_0 = s$, $v_k = t$ and, for every $i < k$, $(v_i, v_{i+1}) \in E$ or
$(v_{i+1}, v_i) \in E$. -/
noncomputable def ustconDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × ℕ × ℕ) x with
  | some i => decide (i.2.2.1 < i.1 ∧ i.2.2.2 < i.1 ∧
      ∃ path : List ℕ, path.Nodup ∧
      path.getD 0 0 = i.2.2.1 ∧
      path.getD (path.length - 1) 0 = i.2.2.2 ∧
      (∀ v ∈ path, v < i.1) ∧
      ∀ j, j + 1 < path.length →
        ((path.getD j 0, path.getD (j + 1) 0) ∈ i.2.1 ∨
          (path.getD (j + 1) 0, path.getD j 0) ∈ i.2.1))
  | none => false

/-- **Undirected ST-connectivity is in L (Reingold).** The undirected $s$-$t$ connectivity
decision problem lies in the class $\mathsf{L}$ of decision problems decidable in deterministic
logarithmic space.

Source: O. Reingold, "Undirected
connectivity in log-space", Journal of the ACM 55 (2008), 1-24 (STOC 2005). -/
public theorem_wanted ustcon_in_l :
    ustconDec ∈ LogSpace

end MetaMathlibExt.Complexity.KeyTheorems.USTCONInL
