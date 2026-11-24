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

public import MathlibExt.Algebra.Homology.PartialTotalFunctor

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))
variable {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

example : ℕ ⥤ ChainComplex C ℕ :=
  B.partialTotalFunctor

example (p : ℕ) :
    B.partialTotalFunctor.obj p = B.partialTotal p :=
  B.partialTotalFunctor_obj p

example {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalFunctor.map (homOfLE h) = B.partialTotalMap h :=
  B.partialTotalFunctor_map h

example (p : ℕ) :
    B.partialTotalFunctor.map (homOfLE (Nat.le_succ p)) =
      B.partialTotalMap (Nat.le_succ p) :=
  B.partialTotalFunctor_map_succ p

example (φ : B ⟶ B') :
    B.partialTotalFunctor ⟶ B'.partialTotalFunctor :=
  partialTotalFunctorMap φ

example (φ : B ⟶ B') (p : ℕ) :
    (partialTotalFunctorMap φ).app p = B.partialTotalHom φ p :=
  partialTotalFunctorMap_app φ p

example :
    B.partialTotalFunctor ⟶
      (Functor.const ℕ).obj (B.total (ComplexShape.down ℕ)) :=
  B.partialTotalToTotal

example (p : ℕ) :
    B.partialTotalToTotal.app p = B.partialTotalι p :=
  B.partialTotalToTotal_app p

example : Cocone B.partialTotalFunctor :=
  B.partialTotalCocone

example :
    B.partialTotalCocone.pt = B.total (ComplexShape.down ℕ) :=
  B.partialTotalCocone_pt

example (p : ℕ) :
    B.partialTotalCocone.ι.app p = B.partialTotalι p :=
  B.partialTotalCocone_ι_app p

end HomologicalComplex₂

end
