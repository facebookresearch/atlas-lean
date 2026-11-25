/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.PartialTotalEdgeMaps

/-!
# Stage-zero partial-total coordinate tests

These tests exercise the public coordinate API through the zero-row maps used
by the first-page and zero-column edge constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (q : ℕ) :
    B.partialTotalZeroRowToPartialTotal.f q =
      B.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q) :=
  B.partialTotalZeroRowToPartialTotal_f q

example (φ : B ⟶ B') :
    φ.f 0 ≫ B'.partialTotalZeroRowToPartialTotal =
      B.partialTotalZeroRowToPartialTotal ≫ B.partialTotalHom φ 0 :=
  B.partialTotalZeroRowToPartialTotal_naturality φ

example (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    B.partialTotalZeroRowToPartialTotal ≫ B.partialTotalι 0 =
      B.partialTotalZeroRowToTotal :=
  B.partialTotalZeroRowToPartialTotal_comp_partialTotalι

example (φ : B ⟶ B') :
    φ.f 0 ≫ B'.partialTotalZeroRowToTotal =
      B.partialTotalZeroRowToTotal ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) :=
  B.partialTotalZeroRowToTotal_naturality φ

example (φ : B ⟶ B') (n : ℕ) :
    HomologicalComplex.homologyMap (φ.f 0) n ≫
        HomologicalComplex.homologyMap
          B'.partialTotalZeroRowToPartialTotal n =
      HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal n ≫
        HomologicalComplex.homologyMap (B.partialTotalHom φ 0) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    B.partialTotalZeroRowToPartialTotal_naturality φ,
    HomologicalComplex.homologyMap_comp]

example (φ : B ⟶ B') :
    φ.f 0 ≫ B'.partialTotalZeroRowToPartialTotal ≫
        B'.partialTotalRowQuotient 0 =
      B.partialTotalZeroRowToPartialTotal ≫
        B.partialTotalRowQuotient 0 ≫ totalRowMap φ 0 := by
  rw [B.partialTotalZeroRowToPartialTotal_naturality_assoc φ,
    B.partialTotalRowQuotient_naturality]

example (φ : B ⟶ B') (n : ℕ) :
    HomologicalComplex.homologyMap (φ.f 0) n ≫
        HomologicalComplex.homologyMap B'.partialTotalZeroRowToTotal n =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal n ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    B.partialTotalZeroRowToTotal_naturality φ,
    HomologicalComplex.homologyMap_comp]

#print axioms HomologicalComplex₂.partialTotalZeroRowToPartialTotal_naturality
#print axioms HomologicalComplex₂.partialTotalZeroRowToTotal_naturality

end HomologicalComplex₂
