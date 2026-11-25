/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.SpragueGrundyZero

open MetaMathlibExt MetaMathlibExt.SpragueGrundy

example : IsP (nimHeap 0) (nimHeap 0).start :=
  (isP_start_iff_of_equiv_nimHeap _ 0 (fun _ => Iff.rfl)).mpr rfl

example (n : ℕ) : ¬ IsP (nimHeap (n + 1)) (nimHeap (n + 1)).start :=
  fun h => Nat.succ_ne_zero n ((isP_start_iff_of_equiv_nimHeap _ (n + 1) (fun _ => Iff.rfl)).mp h)
