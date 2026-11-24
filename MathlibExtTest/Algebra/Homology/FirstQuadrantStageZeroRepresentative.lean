/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.Algebra.Homology.FirstQuadrantStageZeroRepresentative

set_option autoImplicit false
set_option warningAsError true

universe uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace HomologicalComplex₂

example
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (K : HomologicalComplex₂ D (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hneg : ∀ (n a : ℤ), a < 0 →
      IsZero (((horizontalCompleteFiltrationSpectralObject K).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (a : EInt))))))
    (q : ℕ) :
    let E := horizontalCompleteFiltrationSpectralObject K
    let F₀ := horizontalCompleteFilteredTotalComplex K ((0 : ℤ) : EInt)
    let V := K.verticalHomologyComplex q
    let n : ℤ := -(q : ℤ)
    let m : ℤ := -((0 : ℕ) : ℤ) - (q : ℤ)
    let hDegree : n = m := by simp [n, m]
    let uCol :
      F₀.extend ComplexShape.embeddingDownNat ⟶ horizontalDirectColumnCochain K 0 :=
      horizontalCompleteDirectColumnProjectionMap K 0
    let eExt :
      (F₀.extend ComplexShape.embeddingDownNat).homology n ≅ F₀.homology q :=
      F₀.extendHomologyIso ComplexShape.embeddingDownNat
        (j := q) (j' := n) (by simp [n, ComplexShape.embeddingDownNat_f])
    let castCol :
      (horizontalDirectColumnCochain K 0).homology n ⟶
        (horizontalDirectColumnCochain K 0).homology m :=
      eqToHom (congrArg
        (fun d : ℤ => (horizontalDirectColumnCochain K 0).homology d) hDegree)
    let r₀ : F₀.homology q ⟶ (K.X 0).homology q :=
      eExt.inv ≫ HomologicalComplex.homologyMap uCol n ≫ castCol ≫
        (horizontalDirectColumnHomologyIso K 0 q).hom
    (horizontalBottomRelativeHomologyStageIso K ((0 : ℤ) : EInt) q).inv ≫
      E.nativeZeroColumnStageZeroRepresentative hneg q ≫
      (horizontalSecondPageVerticalHorizontalHomologyIso K 0 q).hom =
      r₀ ≫ V.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ V).inv := by
  exact horizontalSecondPageZeroColumnStageRepresentative K hneg q

end HomologicalComplex₂
