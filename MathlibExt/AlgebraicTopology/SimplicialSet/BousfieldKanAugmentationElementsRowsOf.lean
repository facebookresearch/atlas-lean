/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanTerminalWeightRowsOf
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveDiscreteIso
import MathlibExt.CategoryTheory.CategoryBar.ElementsNerveReadbacks
import MathlibExt.CategoryTheory.ElementsDiscreteProjection
import MathlibExt.CategoryTheory.NerveCrossUniverse

/-!
# The SAME actual generalized BK augmentation in full original elements rows

Both complete original row maps identify the actual weighted row with
the original coefficient-elements nerve. The literal original
augmentation is exactly the original elements projection followed by
the complete original discrete-nerve value isomorphism. Index object,
index Hom and extra original scalar universes remain independent.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe uJ vJ w
open CategoryTheory Opposite
open scoped Simplicial
namespace SSet.BousfieldKanRowsOf
variable {J : Type uJ} [Category.{vJ} J]
  (D : J ⥤ SSet.{max uJ vJ w}) (q : SimplexCategoryᵒᵖ)

/-- Both full original inverse maps from the actual weighted row to the original coefficient-elements nerve. -/
def rowNerveIso : wbarRow D q ≅ nerve (wbarDegreeCoefficient D q).Elements :=
  terminalWeightRowIso D q ≪≫ CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D q)

/-- Every actual original weighted coefficient reads its complete original elements chain. -/
theorem rowNerveIso_weighted (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj q) :
    (rowNerveIso D q).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q x) =
    (CategoryBar.replElementsEquiv J (wbarDegreeCoefficient D q) n) ⟨p.1, x, p.2⟩ := by
  change (CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D q)).hom.app (op ⦋n⦌)
    ((terminalWeightRowDegreeIso D q n).hom
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q x)) = _
  exact congrArg ((CategoryBar.replNerveSimplicialIso (wbarDegreeCoefficient D q)).hom.app (op ⦋n⦌))
    (terminalWeightRowDegreeIso_hom_ι_apply D q n p x)

/-- Every complete original weighted coefficient keeps its exact original first elements object. -/
theorem rowNerveIso_first (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj q) :
    (((rowNerveIso D q).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q x)).obj 0) =
        (wbarDegreeCoefficient D q).elementsMk p.1.left x := by
  rw [rowNerveIso_weighted]
  exact CategoryBar.replNerveSimplicialIso_first (wbarDegreeCoefficient D q) n p.1 x p.2

variable {D q} {Z : SSet.{max uJ vJ w}}

/-- The actual original coefficient cocone in the unchanged original scalar degree. -/
def degreeCocone (τ : D ⟶ (Functor.const J).obj Z) (q : SimplexCategoryᵒᵖ) :
    wbarDegreeCoefficient D q ⟶ (Functor.const J).obj (Z.obj q) where
  app j := (τ.app j).app q
  naturality _j _k f := NatTrans.congr_app (τ.naturality f) q

/-- The whole original row projection keeps each actual original coefficient cocone value. -/
def rowProjection (τ : D ⟶ (Functor.const J).obj Z) (q : SimplexCategoryᵒᵖ) :
    (wbarDegreeCoefficient D q).Elements ⥤ Discrete (Z.obj q) :=
  Functor.Elements.discreteProjection (degreeCocone τ q)

/-- The SAME original row augmentation is the exact full original coefficient-elements projection. -/
theorem rowAugmentation_projection (τ : D ⟶ (Functor.const J).obj Z) (q : SimplexCategoryᵒᵖ) :
    (rowNerveIso D q).hom ≫
        nerveMapHomDown.{max uJ vJ w, vJ, max uJ vJ w} (rowProjection τ q) ≫
          (SSet.nerveDiscreteIso (Z.obj q)).hom = wbarRowAugmentation τ q := by
  apply NatTrans.ext
  funext b
  induction b using Opposite.rec with
  | _ b =>
    induction b using SimplexCategory.rec with
    | _ n =>
      apply wbarRow_hom_ext D q n
      intro p
      simp only [wbarRowIncl_eq_wbarIncl_app]
      apply ConcreteCategory.hom_ext
      intro x
      have hf := rowNerveIso_first D q n p x
      have hp := ConcreteCategory.congr_hom (wbarRowAugmentation_ι τ q n p) x
      change (degreeCocone τ q).app
          (((rowNerveIso D q).hom.app (op ⦋n⦌)
            ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q x)).obj 0).obj
          (((rowNerveIso D q).hom.app (op ⦋n⦌)
            ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q x)).obj 0).val = _
      rw [hf]
      exact hp.symm

end SSet.BousfieldKanRowsOf
