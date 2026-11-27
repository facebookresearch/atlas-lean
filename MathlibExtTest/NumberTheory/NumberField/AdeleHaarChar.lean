/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement and first proof step of `norm_two_completion` are the same as a step of
`nontriviallyNormedCompletion` in `Definitions/Def_M4aHerbrand_ArchSemilocal.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

import MathlibExt.NumberTheory.NumberField.AdeleHaarChar

open NumberField IsDedekindDomain

namespace AdeleHaarCharTest

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
private theorem norm_two_completion (w : InfinitePlace F) : ‖(2 : w.Completion)‖ = 2 := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _), map_ofNat]
  norm_num

/-- The adele whose archimedean components are all `2` and whose finite component is `1`. -/
private noncomputable def twoArch : AdeleRing (𝓞 F) F :=
  ((2 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

private theorem isUnit_twoArch : IsUnit (twoArch F) :=
  Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => isUnit_iff_ne_zero.mpr
    (show (2 : w.Completion) ≠ 0 from fun h => by
      simpa [h] using norm_two_completion F w), isUnit_one⟩

/-- Doubling every archimedean component multiplies Haar measure on the adeles by `2 ^ [F : ℚ]`:
a real place contributes `2` and a complex place `2 ^ 2`. -/
example :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) (isUnit_twoArch F).unit : ℝ) =
      2 ^ Module.finrank ℚ F := by
  rw [AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F _ rfl]
  change ∏ w : InfinitePlace F, ‖(2 : w.Completion)‖ ^ w.mult = _
  simp only [norm_two_completion, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end AdeleHaarCharTest
