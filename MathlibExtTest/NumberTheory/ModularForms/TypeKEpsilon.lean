/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.TypeKEpsilon

#check @ModularForm.HasNebentypus
#check @ModularForm.typeSubmodule
#check @ModularForm.mem_typeSubmodule
#check @ModularForm.HasNebentypus.eq_zero_of_ne
#check @ModularForm.IsHeckeEigenvector

open CongruenceSubgroup ModularFormClass

open scoped MatrixGroups

-- The zero form has every type.
example (N : ℕ) (k : ℤ) (ε : DirichletCharacter ℂ N) :
    ModularForm.HasNebentypus ε (0 : ModularForm (Gamma1 N) k) :=
  (ModularForm.typeSubmodule N k ε).zero_mem

-- In weight `1`, the transformation law is hypothesis `hfε` of the Deligne–Serre statement
-- `ModularForm.exists_galoisRep_trace_det_frob_of_weight_one`.
example (N : ℕ) (ε : DirichletCharacter ℂ N) (f : ModularForm (Gamma1 N) 1) :
    ModularForm.HasNebentypus ε f ↔
      ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ τ : UpperHalfPlane,
        f (γ • τ) =
          ε ((γ 1 1 : ℤ) : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) * f τ) := by
  simp [ModularForm.HasNebentypus]

-- A form of weight `1` with the trivial character (an even character in odd weight) is zero.
example (N : ℕ) (f : ModularForm (Gamma1 N) 1) (hf : ModularForm.HasNebentypus 1 f) : f = 0 :=
  hf.eq_zero_of_ne (by rw [MulChar.one_apply isUnit_one.neg]; norm_num)

-- An eigenvector is nonzero.
example (N : ℕ) (k : ℤ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) :
    ¬ ModularForm.IsHeckeEigenvector ε (0 : ModularForm (Gamma1 N) k) a :=
  fun h => h.1 rfl
