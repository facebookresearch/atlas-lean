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

import MathlibExt.KTheory.Exact.K0.FiniteBiproduct

/-!+# Public clients for finite biproduct classes

These clients retain arbitrary exact categories and a finite index type in an
independent universe. The last calculation combines two actual admissible
sequences with an actual finite biproduct in their middle term.
-/

open CategoryTheory Limits
open AlgebraicKTheory

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [HasFiniteBiproducts C]

example {ι : Type w} [Fintype ι] (f : ι → C) :
    K0.mk (⨁ f) = ∑ i, K0.mk (f i) :=
  K0.mk_biproduct f

example (X : C) : K0.mk (⨁ fun _ : Fin 0 => X) = 0 := by
  simpa using K0.mk_biproduct_const (ι := Fin 0) X

example (X : C) (n : ℕ) :
    K0.mk (⨁ fun _ : Fin n => X) = n • K0.mk X := by
  simpa using K0.mk_biproduct_const (ι := Fin n) X

example (S T : ShortComplex C) (hS : ExactCategory.IsAdmissibleExact S)
    (hT : ExactCategory.IsAdmissibleExact T) (L O N : C) (m : ℕ)
    (e : T.X₃ ≅ S.X₂) (eO : T.X₁ ≅ O)
    (eL : T.X₂ ≅ ⨁ fun _ : Fin m => L) (eN : S.X₃ ≅ N) :
    K0.mk S.X₁ = m • K0.mk L - K0.mk O - K0.mk N := by
  have hs := K0.mk_eq_of_admissibleExact hS
  have ht := K0.mk_eq_of_admissibleExact hT
  rw [K0.mk_congr_of_iso eO, K0.mk_congr_of_iso e,
    K0.mk_congr_of_iso eL, K0.mk_biproduct_const, Fintype.card_fin] at ht
  rw [K0.mk_congr_of_iso eN] at hs
  rw [ht]
  rw [hs]
  abel
