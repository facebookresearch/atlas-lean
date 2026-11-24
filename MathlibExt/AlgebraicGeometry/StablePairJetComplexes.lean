/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# The actual three-term diagonal-resolution source

The complex is supported in degrees -2, -1, 0, with the two supplied
actual maps. This is the elementary source complex of
Huybrechts–Thomas, arXiv:0805.3527v2, equation (2.6).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairJetComplexes

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable (K I O : C) (a : K ⟶ I) (b : I ⟶ O)

def terms : ℤ → C
  | -2 => K
  | -1 => I
  | 0 => O
  | _ => 0

def differential : ∀ n : ℤ, terms K I O n ⟶ terms K I O (n+1)
  | -2 => a
  | -1 => b
  | _ => 0

def complex (h : a ≫ b = 0) : CochainComplex C ℤ :=
  CochainComplex.of (terms K I O) (differential K I O a b) (by
    intro n
    rcases n with n | n
    · cases n with
      | zero =>
        change (0 : O ⟶ 0) ≫ 0 = 0
        exact zero_comp
      | succ n =>
        change (0 : _ ⟶ _) ≫ _ = 0
        exact zero_comp
    · cases n with
      | zero =>
        change b ≫ 0 = 0
        exact comp_zero
      | succ n => cases n with
        | zero => exact h
        | succ n =>
          change (0 : _ ⟶ _) ≫ _ = 0
          exact zero_comp)

end MathlibExt.AlgebraicGeometry.StablePairJetComplexes
