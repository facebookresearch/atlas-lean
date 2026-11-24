/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdCoequalizer
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

@[expose] public section

/-!
# Concrete ProdCoequalizer preservation regression (KQ3)

Fixed left `TopCat.of PUnit` against the `TopCat.const`-built
`PUnit`-to-`PUnit ⊕ PUnit` parallel pair picking `Sum.inl`/`Sum.inr`. Uses
`TopCat.preservesColimitsOfShape_walkingParallelPair_prodLeft` and
`TopCat.isColimit_prodMap_cofork_of_isColimit` on this concrete coequalizer,
then checks the resulting product cofork equation on a concrete point on both
product legs via `TopCat.prodMap_prodIso_inv_apply` and
`TopCat.prod_point_ext`. Catches swapped product legs or wrong comparison
direction. No realization or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat Topology

namespace MathlibExtTest.Topology.Category.TopCat.ProdCoequalizerTests

/-- Concrete point check over the `inl`/`inr` parallel pair. -/
theorem prodCoequalizer_punit_sum_point :
    (Limits.prod.map (𝟙 (TopCat.of PUnit))
        (coequalizer.π
          ((TopCat.const (Sum.inl PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)))
          ((TopCat.const (Sum.inr PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)))))
      ((Limits.prod.map (𝟙 (TopCat.of PUnit))
        ((TopCat.const (Sum.inl PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit))))
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) =
    (Limits.prod.map (𝟙 (TopCat.of PUnit))
        (coequalizer.π
          ((TopCat.const (Sum.inl PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)))
          ((TopCat.const (Sum.inr PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)))))
      ((Limits.prod.map (𝟙 (TopCat.of PUnit))
        ((TopCat.const (Sum.inr PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit))))
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) := by
  set f : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit) :=
    (TopCat.const (Sum.inl PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit))
  set g : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit) :=
    (TopCat.const (Sum.inr PUnit.unit) : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit))
  have hProd := TopCat.isColimit_prodMap_cofork_of_isColimit
    (K := TopCat.of (PUnit : Type))
    (Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g))
    (coequalizerIsCoequalizer f g)
  have hSndCond :
      (Limits.prod.map (𝟙 (TopCat.of PUnit)) f) ≫
        ((Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
          TopCat.of (PUnit ⊕ PUnit)) ≫ coequalizer.π f g) =
      (Limits.prod.map (𝟙 (TopCat.of PUnit)) g) ≫
        ((Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
          TopCat.of (PUnit ⊕ PUnit)) ≫ coequalizer.π f g) := by
    have m : ∀ (k : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)),
        (Limits.prod.map (𝟙 (TopCat.of PUnit)) k) ≫
          (Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
            TopCat.of (PUnit ⊕ PUnit)) =
          (Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of PUnit) ⟶
            TopCat.of PUnit) ≫ k := fun k =>
      Limits.prod.map_snd (𝟙 (TopCat.of PUnit)) k
    have e : ∀ (k : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)),
        (Limits.prod.map (𝟙 (TopCat.of PUnit)) k) ≫
          ((Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
            TopCat.of (PUnit ⊕ PUnit)) ≫ coequalizer.π f g) =
        (Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of PUnit) ⟶
          TopCat.of PUnit) ≫ (k ≫ coequalizer.π f g) := by
      intro k
      rw [← Category.assoc, m k, Category.assoc]
    rw [e f, e g, coequalizer.condition f g]
  obtain ⟨dSnd, hdSnd⟩ := Cofork.IsColimit.desc' hProd
    ((Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
      TopCat.of (PUnit ⊕ PUnit)) ≫ coequalizer.π f g) hSndCond
  have hF : (Limits.prod.map (𝟙 (TopCat.of PUnit)) f)
      ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
        (PUnit.unit, PUnit.unit)) =
      (TopCat.prodIsoProd (TopCat.of PUnit)
        (TopCat.of (PUnit ⊕ PUnit))).inv
        (PUnit.unit, f PUnit.unit) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  have hG : (Limits.prod.map (𝟙 (TopCat.of PUnit)) g)
      ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
        (PUnit.unit, PUnit.unit)) =
      (TopCat.prodIsoProd (TopCat.of PUnit)
        (TopCat.of (PUnit ⊕ PUnit))).inv
        (PUnit.unit, g PUnit.unit) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  have hQF : (Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
      ((TopCat.prodIsoProd (TopCat.of PUnit)
        (TopCat.of (PUnit ⊕ PUnit))).inv
        (PUnit.unit, f PUnit.unit)) =
      (TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, (coequalizer.π f g) (f PUnit.unit)) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  have hQG : (Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
      ((TopCat.prodIsoProd (TopCat.of PUnit)
        (TopCat.of (PUnit ⊕ PUnit))).inv
        (PUnit.unit, g PUnit.unit)) =
      (TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, (coequalizer.π f g) (g PUnit.unit)) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  have hL : (Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
      ((Limits.prod.map (𝟙 (TopCat.of PUnit)) f)
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) =
      (TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, (coequalizer.π f g) (f PUnit.unit)) :=
    (congrArg _ hF).trans hQF
  have hR : (Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
      ((Limits.prod.map (𝟙 (TopCat.of PUnit)) g)
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) =
      (TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, (coequalizer.π f g) (g PUnit.unit)) :=
    (congrArg _ hG).trans hQG
  have hcond : (coequalizer.π f g) (f PUnit.unit) =
      (coequalizer.π f g) (g PUnit.unit) := by
    have h := ConcreteCategory.congr_hom (coequalizer.condition f g)
      PUnit.unit
    simpa [ConcreteCategory.comp_apply] using h
  have eFst : ∀ y : ↑(coequalizer f g),
      (Limits.prod.fst :
        (TopCat.of PUnit) ⨯ (coequalizer f g) ⟶ TopCat.of PUnit)
      ((TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, y)) =
      PUnit.unit := fun y =>
    ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_fst (TopCat.of PUnit) (coequalizer f g))
      (PUnit.unit, y)
  have eSnd : ∀ y : ↑(coequalizer f g),
      (Limits.prod.snd :
        (TopCat.of PUnit) ⨯ (coequalizer f g) ⟶ coequalizer f g)
      ((TopCat.prodIsoProd (TopCat.of PUnit) (coequalizer f g)).inv
        (PUnit.unit, y)) =
      y := fun y =>
    ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_snd (TopCat.of PUnit) (coequalizer f g))
      (PUnit.unit, y)
  have eMap : ∀ (k : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)),
      (Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
        TopCat.of (PUnit ⊕ PUnit))
      ((Limits.prod.map (𝟙 (TopCat.of PUnit)) k)
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) =
      k PUnit.unit := by
    intro k
    have e1 := ConcreteCategory.congr_hom
      (Limits.prod.map_snd (𝟙 (TopCat.of PUnit)) k)
      ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
        (PUnit.unit, PUnit.unit))
    simp only [ConcreteCategory.comp_apply] at e1
    calc (Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of (PUnit ⊕ PUnit)) ⟶
          TopCat.of (PUnit ⊕ PUnit))
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) k)
            ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
              (PUnit.unit, PUnit.unit)))
        = k ((Limits.prod.snd : (TopCat.of PUnit) ⨯ (TopCat.of PUnit) ⟶
            TopCat.of PUnit)
            ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
              (PUnit.unit, PUnit.unit))) := e1
      _ = k PUnit.unit := congrArg k
        (ConcreteCategory.congr_hom
          (TopCat.prodIsoProd_inv_snd (TopCat.of PUnit) (TopCat.of PUnit))
          (PUnit.unit, PUnit.unit))
  have hDesc : ∀ (k : TopCat.of PUnit ⟶ TopCat.of (PUnit ⊕ PUnit)),
      dSnd
        ((Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) k)
            ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
              (PUnit.unit, PUnit.unit)))) =
      (coequalizer.π f g) (k PUnit.unit) := by
    intro k
    have h := ConcreteCategory.congr_hom hdSnd
      ((Limits.prod.map (𝟙 (TopCat.of PUnit)) k)
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit)))
    simp only [ConcreteCategory.comp_apply] at h
    rw [eMap k] at h
    exact h
  refine TopCat.prod_point_ext ?_ ?_
  · exact ((congrArg _ hL).trans (eFst _)).trans
      ((eFst _).symm.trans (congrArg _ hR.symm))
  · calc (Limits.prod.snd : (TopCat.of PUnit) ⨯ (coequalizer f g) ⟶ coequalizer f g)
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
            ((Limits.prod.map (𝟙 (TopCat.of PUnit)) f)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit))))
        = (coequalizer.π f g) (f PUnit.unit) :=
          (congrArg _ hL).trans (eSnd _)
      _ = dSnd
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
            ((Limits.prod.map (𝟙 (TopCat.of PUnit)) f)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit)))) := (hDesc f).symm
      _ = dSnd
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
            ((Limits.prod.map (𝟙 (TopCat.of PUnit)) g)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit)))) :=
          (hDesc f).trans (hcond.trans (hDesc g).symm)
      _ = (coequalizer.π f g) (g PUnit.unit) := hDesc g
      _ = (Limits.prod.snd : (TopCat.of PUnit) ⨯ (coequalizer f g) ⟶ coequalizer f g)
          ((Limits.prod.map (𝟙 (TopCat.of PUnit)) (coequalizer.π f g))
            ((Limits.prod.map (𝟙 (TopCat.of PUnit)) g)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit)))) :=
          ((congrArg _ hR).trans (eSnd _)).symm

#print axioms prodCoequalizer_punit_sum_point

end MathlibExtTest.Topology.Category.TopCat.ProdCoequalizerTests
