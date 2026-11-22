/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceHocolimFlaggedIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedRawHomAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation

/-!
# The SAME original necklace homotopy-colimit augmentation is weak

The actual canonical Bousfield--Kan augmentation on the full original
native raw Hom coefficient diagram factors through its genuine flagged
diagonal isomorphism and original raw evaluation. This proves weakness
of that SAME augmentation for every simplicial input, with no fibrancy
or comparison outcome premise.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

/-- The full original joint-coefficient augmentation retains the SAME native raw inverse and input maps. -/
def fullRawInputAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) :
    fullCoefficientDiagram K x y ⟶ (Functor.const (Object K x y)).obj (hom K x y) :=
  (rawCoefficientDiagramIso K x y).inv ≫ rawInputAugmentation K x y

/-- The original canonical Bousfield--Kan augmentation into the SAME raw input Hom. -/
def hocolimRawAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) : hocolim K x y ⟶ hom K x y :=
  SSet.bkAugmentation (rawInputAugmentation K x y)

/-- The original full coefficient augmentation reads its literal complete input and coefficient lift. -/
theorem fullRawInputAugmentation_app (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (T : Object K x y) (p : ((fullCoefficientDiagram K x y).obj T).obj q) :
    ((fullRawInputAugmentation K x y).app T).app q p =
      OriginalFlaggedNecklace.evaluation (toFlaggedObject ((degreeCoefficient K x y q).elementsMk T p)) := rfl

private theorem weighted_component_hom_ext {J : Type u} [Category.{0} J]
    (D : J ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ) (n : ℕ) {Z : Type u}
    {f g : (StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) D n).obj q ⟶ Z}
    (h : ∀ p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n,
      (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q ≫ f =
        (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q ≫ g) : f = g := by
  let e := Limits.sigmaObjIso
    (fun p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n => D.obj p.1.left) q
  apply (cancel_epi e.inv).1
  apply Limits.Sigma.hom_ext
  intro p
  have hi : Limits.Sigma.ι
      (fun p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n => (D.obj p.1.left).obj q) p ≫
        e.inv = (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app q :=
    Limits.ι_comp_sigmaObjIso_inv _ _ p
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ f) hi).trans
      ((h p).trans ((congrArg (fun m => m ≫ g) hi.symm).trans (Category.assoc _ _ _))))

/-- The SAME full coefficient Bousfield--Kan augmentation is the actual flagged diagonal evaluation. -/
theorem fullRawInputAugmentation_bk (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.bkAugmentation (fullRawInputAugmentation K x y) =
      (fullCoefficientHocolimIso K x y).hom ≫ OriginalFlaggedNecklace.Components.rawAugmentation K x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply weighted_component_hom_ext (fullCoefficientDiagram K x y) (op ⦋n⦌) n
  intro p
  apply ConcreteCategory.hom_ext
  intro a
  have hb := ConcreteCategory.congr_hom
    (SSet.bkAugmentation_app_mk_ι (fullRawInputAugmentation K x y) n p) a
  have hf := congrArg OriginalFlaggedNecklace.evaluation (fullCoefficientHocolimIso_first K x y n p a)
  exact hb.trans hf.symm

/-- The actual canonical raw augmentation retains the SAME original hocolim and flagged inverse maps. -/
theorem hocolimRawAugmentation_factor (K : SSet.{u}) (x y : K _⦋0⦌) :
    hocolimRawAugmentation K x y =
      (hocolimFlaggedIso K x y).hom ≫ OriginalFlaggedNecklace.Components.rawAugmentation K x y := by
  have hs : (rawCoefficientDiagramIso K x y).hom ≫ fullRawInputAugmentation K x y =
      rawInputAugmentation K x y ≫ (Functor.const (Object K x y)).map (𝟙 (hom K x y)) := by
    change (rawCoefficientDiagramIso K x y).hom ≫
      ((rawCoefficientDiagramIso K x y).inv ≫ rawInputAugmentation K x y) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Functor.map_id, Category.comp_id]
  have hb := SSet.bkAugmentation_naturality (rawCoefficientDiagramIso K x y).hom
    (rawInputAugmentation K x y) (fullRawInputAugmentation K x y) (𝟙 (hom K x y)) (fun T => congr_app hs T)
  change _ = hocolimRawAugmentation K x y ≫ 𝟙 (hom K x y) at hb
  exact (Category.comp_id _).symm.trans
    (hb.symm.trans ((congrArg (fun m => SSet.bkHocolimMap (rawCoefficientDiagramIso K x y).hom ≫ m)
      (fullRawInputAugmentation_bk K x y)).trans (Category.assoc _ _ _).symm))

/-- The SAME actual original necklace homotopy-colimit augmentation is weak for EVERY original simplicial input. -/
theorem hocolimRawAugmentation_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (hocolimRawAugmentation K x y) := by
  rw [hocolimRawAugmentation_factor]
  exact RespectsIso.precomp SSet.realizationWeakEquivalences (hocolimFlaggedIso K x y).hom
    (OriginalFlaggedNecklace.Components.rawAugmentation K x y)
      (OriginalFlaggedNecklace.Components.rawAugmentation_weak K x y)

/-- On EVERY complete weighted chain, the actual raw augmentation retains its SAME entire source input Hom map. -/
theorem hocolimRawAugmentation_ι (K : SSet.{u}) (x y : K _⦋0⦌) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx (Object K x y) (CategoryBar.replUnit (Object K x y)) n) :
    (StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit (Object K x y))
      (rawCoefficientDiagram K x y) n p).app (op ⦋n⦌) ≫ (hocolimRawAugmentation K x y).app (op ⦋n⦌) =
        (inputHomMap p.1.left).app (op ⦋n⦌) :=
  SSet.bkAugmentation_app_mk_ι (rawInputAugmentation K x y) n p

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
