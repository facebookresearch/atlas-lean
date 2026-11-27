/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Enriched.FunctorOpposite
set_option autoImplicit false
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory Opposite
namespace MathlibExtTest.EnrichedFunctorOpposite
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)
example (a : Aᵒᵖ) : (j.opposite).obj a = op (j.obj a.unop) := rfl
example (a b : Aᵒᵖ) : (j.opposite).map a b = j.map b.unop a.unop := rfl
example (a : Aᵒᵖ) : eId V a ≫ (j.opposite).map a a = eId V ((j.opposite).obj a) :=
  (j.opposite).map_id a
example (a b c : Aᵒᵖ) : eComp V a b c ≫ (j.opposite).map a c =
    ((j.opposite).map a b ⊗ₘ (j.opposite).map b c) ≫
      eComp V ((j.opposite).obj a) ((j.opposite).obj b) ((j.opposite).obj c) :=
  (j.opposite).map_comp a b c
end MathlibExtTest.EnrichedFunctorOpposite
