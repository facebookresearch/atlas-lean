/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.FieldTheory.NormalBasisFrobeniusRotation

open MetaMathlibExt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- In degree one, the wrap is the only case, and the coordinate map is bijective.
example : Function.Bijective (fun a : Fin 1 → ZMod 2 => a 0) := by
  have hβ : LinearIndependent (ZMod 2)
      (fun i : Fin 1 => (1 : ZMod 2) ^ (Fintype.card (ZMod 2) ^ (i : ℕ))) := by
    rw [linearIndependent_unique_iff]
    simp
  simpa using (normalBasisMap_bijective_frobenius (ZMod 2) (ZMod 2) 1
    (Module.finrank_self (ZMod 2)) 1 hβ).1

-- Three distinct index positions distinguish the two possible directions of rotation.
example {F K : Type*} [Field F] [Fintype F] [Field K] [Fintype K] [Algebra F K]
    (hn : Module.finrank F K = 3) (β : K)
    (hβ : LinearIndependent F (fun i : Fin 3 => β ^ (Fintype.card F ^ (i : ℕ))))
    (a₀ a₁ a₂ : F) :
    (a₀ • β + a₁ • β ^ Fintype.card F + a₂ • β ^ (Fintype.card F ^ 2)) ^ Fintype.card F =
      a₂ • β + a₀ • β ^ Fintype.card F + a₁ • β ^ (Fintype.card F ^ 2) := by
  have hrot : ![a₀, a₁, a₂] ∘ ⇑(finRotate 3).symm = ![a₂, a₀, a₁] := by
    funext i
    fin_cases i <;> rfl
  have h := (normalBasisMap_bijective_frobenius F K 3 hn β hβ).2 ![a₀, a₁, a₂]
  rw [hrot] at h
  simpa [Fin.sum_univ_three, add_assoc] using h
