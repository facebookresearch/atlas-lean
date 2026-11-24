/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_AutomorphicForm_archIdent_tmul_apply.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.NumberTheory.NumberField.InfiniteAdeleBaseChange

@[expose] public section

noncomputable section

open scoped TensorProduct NumberField.LiesOver

namespace NumberField.InfiniteAdeleRingTest

universe u

/-- The exact source statement, with its original `Type` binders. -/
theorem exactSource
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : L) (a : NumberField.InfiniteAdeleRing K) (w : NumberField.InfinitePlace L) :
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    NumberField.InfiniteAdeleRing.archBaseChange K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
          (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x :=
  NumberField.InfiniteAdeleRing.archBaseChange_tmul_apply x a w

/-- The same statement at an arbitrary universe. -/
theorem exactSource_universe
    (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : L) (a : NumberField.InfiniteAdeleRing K) (w : NumberField.InfinitePlace L) :
    letI : w.LiesOver (w.comap (algebraMap K L)) := ⟨rfl⟩
    NumberField.InfiniteAdeleRing.archBaseChange K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
          (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x :=
  NumberField.InfiniteAdeleRing.archBaseChange_tmul_apply x a w

/-- The local completion factor on a pure tensor. -/
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    [w.LiesOver v] (c : v.Completion) (l : L) :
    NumberField.InfinitePlace.completionTensorFactor v w (c ⊗ₜ[K] l) =
      algebraMap v.Completion w.Completion c * algebraMap L w.Completion l :=
  NumberField.InfinitePlace.completionTensorFactor_tmul v w c l

/-- The adele coordinate factor cannot be dropped: with the zero adele, the
pure tensor maps to zero even when the scalar factor is `1`. -/
theorem zero_adele_factor_matters (w : NumberField.InfinitePlace ℚ) :
    NumberField.InfiniteAdeleRing.archBaseChange ℚ ℚ
        ((1 : ℚ) ⊗ₜ (0 : NumberField.InfiniteAdeleRing ℚ)) w = 0 :=
  NumberField.InfiniteAdeleRing.archBaseChange_tmul_zero_apply (K := ℚ) (L := ℚ) 1 w

/-- With scalar `1`, only the transported adele coordinate remains. -/
theorem one_scalar (a : NumberField.InfiniteAdeleRing ℚ)
    (w : NumberField.InfinitePlace ℚ) :
    letI : w.LiesOver (w.comap (algebraMap ℚ ℚ)) := ⟨rfl⟩
    NumberField.InfiniteAdeleRing.archBaseChange ℚ ℚ ((1 : ℚ) ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap ℚ ℚ)).Completion w.Completion
        (a (w.comap (algebraMap ℚ ℚ))) :=
  NumberField.InfiniteAdeleRing.archBaseChange_one_tmul_apply a w

end NumberField.InfiniteAdeleRingTest

end
