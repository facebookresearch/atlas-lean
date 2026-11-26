/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenTransformationSums

open MetaMathlibExt

-- With no transformations, every block has the zero vector of sums.
example {n : ℕ} (hn : 0 < n) (g : Fin 0 → ZMod n → ZMod n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) (t : Fin 0) => ∑ i, g t (b i)) :=
  isVanishingFamily_transformation_sums (hn := hn) g

-- The two constant transformations modulo six jointly force the common length
-- to be divisible by both three and two.
example : ∃ l : ℕ, 1 < l ∧ 6 ∣ l := by
  let g (t : Fin 2) (_ : ZMod 6) : ZMod 6 := if t = 0 then 2 else 3
  obtain ⟨l, hl, _, hs⟩ :=
    isVanishingFamily_transformation_sums (hn := by decide) g 2 (by decide) (fun _ => 0)
  have htwo : ((2 * l : ℕ) : ZMod 6) = 0 := by
    simpa [g, nsmul_eq_mul, mul_comm] using congrFun (hs 0 (by decide)) (0 : Fin 2)
  have hthree : ((3 * l : ℕ) : ZMod 6) = 0 := by
    simpa [g, nsmul_eq_mul, mul_comm] using congrFun (hs 1 (by decide)) (1 : Fin 2)
  have h₁ := (ZMod.natCast_eq_zero_iff (2 * l) 6).mp htwo
  have h₂ := (ZMod.natCast_eq_zero_iff (3 * l) 6).mp hthree
  exact ⟨l, hl, by omega⟩
