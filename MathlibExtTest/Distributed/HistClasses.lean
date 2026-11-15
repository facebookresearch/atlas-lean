/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.HistClasses

@[expose] public section

/-- With predicates on `ℕ`, the chain inclusions hold. -/
example : HistClass (fun n : ℕ => n ≤ 1) ⊆ HistClass (fun n : ℕ => n ≤ 2)
    ∧ HistClass (fun n : ℕ => n ≤ 2) ⊆ HistClass (fun n : ℕ => n ≤ 3) :=
  histClass_chain (fun _ h => by omega) (fun _ h => by omega)

/-- The same predicates give proper inclusions. -/
example : HistClass (fun n : ℕ => n ≤ 1) ⊂ HistClass (fun n : ℕ => n ≤ 2)
    ∧ HistClass (fun n : ℕ => n ≤ 2) ⊂ HistClass (fun n : ℕ => n ≤ 3) :=
  histClass_strict (fun _ h => by omega) (fun _ h => by omega)
    2 ⟨by omega, by omega⟩ 3 ⟨by omega, by omega⟩

end
