/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.Automatic

open MetaMathlibExt

/-- Every sequence lies in its own `2`-kernel. -/
example (a : ℕ → Fin 3) : a ∈ kKernel 2 a := chr_self_mem_kernel a

/-- The constant zero sequence is `2`-automatic by the Eilenberg bridge:
it is DFAO-computable, hence has finite `2`-kernel. -/
example : IsKAutomatic 2 (fun _ : ℕ => (0 : Fin 2)) :=
  (isKAutomatic_iff_isKAutomaticSequence 2 _).2
    ⟨le_refl 2, 1, one_pos, 0, fun s _ => s, fun _ => (0 : Fin 2),
      fun n ds _ => by simp⟩
