/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
EP-469: Let A be the set of positive pseudoperfect numbers minimal under
divisibility. The sum of `1 / n` over `n ∈ A` converges.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.FactorisationProperties
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted

/-! Source record `EP-469`. -/

/-- n lies in A: it is positive and pseudoperfect but no proper divisor
is. -/
def InA (n : Nat) : Prop :=
  0 < n ∧ Nat.Pseudoperfect n ∧
    ∀ m, m ∣ n → m < n → ¬Nat.Pseudoperfect m

/-- [EP-469] The reciprocal sum over the primitive pseudoperfect numbers
converges. This is now a theorem, with a separately cited formal proof. -/
def conjecture : Prop :=
  Summable (fun a : {n : Nat // InA n} => (1 : Real) / (a.val : Real))

/--
Resolved true: The reciprocal series over primitive pseudoperfect numbers has been proved
convergent; a commit-pinned, sorry-free Lean proof establishes the exact statement. Source:
plby/lean-proofs, Erdos469.lean, commit 68da20b96673899166e94638f5a7fffeb7231d35 (2026),
https://github.com/plby/lean-proofs/blob/68da20b96673899166e94638f5a7fffeb7231d35/src/latest/ErdosProblems/Erdos469.lean.
Moved from `OpenConjectures/NumberTheory/DivisorSumReciprocalConvergence`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted
