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

public import MathlibExt.Algebra.Homology.PartialTotalEIntFiltration

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : EInt ⥤ ChainComplex C ℕ :=
  B.partialTotalEIntFiltration

example (p : ℕ) :
    B.partialTotalEIntFiltration.obj ((p : ℤ) : EInt) ≅
      B.partialTotal p :=
  B.partialTotalEIntFiltrationObjIso p

example {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalEIntFiltrationObjIso p).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE (show ((p : ℤ) : EInt) ≤ ((p' : ℤ) : EInt) by
            simpa using h)) ≫
        (B.partialTotalEIntFiltrationObjIso p').hom =
      B.partialTotalMap h :=
  B.partialTotalEIntFiltrationObjIso_inv_comp_map h

example (p : ℕ) :
    (B.partialTotalEIntFiltrationObjIso p).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE (show ((p : ℤ) : EInt) ≤ ⊤ by simp)) =
      B.partialTotalι p :=
  B.partialTotalEIntFiltrationObjIso_inv_comp_toTop p

example (q : ℕ) :
    IsZero (B.partialTotalEIntFiltration.obj
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
        (0, q))) :=
  B.isZero_partialTotalE₁LowerZero q

example (q : ℕ) :
    B.partialTotalEIntFiltration.obj
        (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
          (0, q)) ≅
      B.partialTotal 0 :=
  B.partialTotalE₁UpperIso 0 q

example (m q : ℕ) :
    (B.partialTotalE₁LowerSuccIso m q).inv ≫
        B.partialTotalEIntFiltration.map
          (homOfLE
            (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₁₂
              (m + 1, q))) ≫
        (B.partialTotalE₁UpperIso (m + 1) q).hom =
      B.partialTotalMap (Nat.le_succ m) :=
  B.partialTotalE₁IntervalMap_succ m q

end HomologicalComplex₂

end
