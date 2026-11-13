/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.CongruenceClosure

@[expose] public section

open MetaMathlibExt

/-- Boundary check: from `c0 = c1`, congruence gives
`f c0 = f c1` in the closure. -/
example : CongClosure (fun t s => t = GTerm.const 0 ∧ s = GTerm.const 1 ∨
      t = GTerm.const 1 ∧ s = GTerm.const 0)
    (GTerm.app (GTerm.const 0) (GTerm.const 0))
    (GTerm.app (GTerm.const 1) (GTerm.const 1)) :=
  CongClosure.congr
    (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩))
    (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩))
