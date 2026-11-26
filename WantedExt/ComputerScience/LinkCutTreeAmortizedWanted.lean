/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree.PreferredPathMachine

/-!
# Logarithmic amortized cost of splay-based link-cut trees

Source: E. Demaine, MIT 6.851, Lecture 19 (1 May 2012), §§2–4. The strict-heavy/light
classification in §4.1 concerns **represented** subtree sizes and pays for path switches. In
§4.2 the rank of an auxiliary node uses a different size: its ordinary auxiliary subtree
weighted by the mass hanging from dashed edges. The weighted rank differences telescope across
an expose; multiplying the number of switches by a fresh logarithmic bound per splay would
only give a squared logarithm. These sizes are for analysis, not fields updated by `step`.

`SplayTree.access_lemma_weighted` in `CSLibExt.Algorithms.Lean.DataStructures.SplayTree.Amortized`
concerns key search with a different pairing of rotations on odd-length paths. Its whole-tree
conclusion is not assumed for `Heap.splay`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LinkCutTree.SplayForest

/-- **Link-cut trees take logarithmic amortized time.** There is a uniform constant $C$ such
that every legal history of $m$ operations starting from the empty forest has a successful
pointer execution returning all of the specified answers and representing the specified final
forest. If $n$ vertices have been created, the execution costs at most
$C m (1 + \lfloor\log_2 n\rfloor)$ local work blocks (use $0$ for the logarithm of zero).
There is no deletion of vertices, so $n$ is the maximum population. Each allocation starts a
singleton and counts as an operation; there is no arbitrary initial tree or unpaid initial
potential. A handle, an aggregate and a monoid multiplication are unit-cost in this model.
The guarantee is on the total, not a worst-case bound for an individual operation. -/
theorem_wanted logarithmic_amortized_cost :
    ∃ C : Nat, ∀ {M : Type} [Monoid M] (ops : List (Call M)) (s : Spec M)
      (answers : List (Answer M)),
      replay specStep ({} : Spec M) ops = some (s, answers) →
      ∃ h : Heap M, replay step ({} : Heap M) ops = some (h, answers) ∧
        Represents h s ∧ h.work ≤ C * ops.length * (1 + s.count.log2)

end Cslib.Algorithms.Lean.LinkCutTree.SplayForest
