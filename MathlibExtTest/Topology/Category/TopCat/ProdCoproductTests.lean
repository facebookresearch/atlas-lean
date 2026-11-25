/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Category.TopCat.ProdCoproduct
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

@[expose] public section

/-!
# Concrete ProdCoproduct preservation regression (KQ3)

Fixed left `TopCat.of PUnit` against the constant `ℕ` `PUnit` family.
Uses `TopCat.prodCoproductComparisonIso` and `TopCat.prodCoproductComparison_ι`
directly, then checks both product legs on an inclusion point. Catches swapped
comparison direction or wrong legs. No realization or model-category claim.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopCat

namespace MathlibExtTest.Topology.Category.TopCat.ProdCoproductTests

/-- Concrete point check over the constant `ℕ`-indexed `PUnit` family. -/
theorem prodCoproduct_nat_punit_point (j : ℕ) :
      (Limits.prod.fst :
          TopCat.of PUnit ⨯ ∐ (fun _ : ℕ => TopCat.of PUnit) ⟶ TopCat.of PUnit)
          ((TopCat.prodCoproductComparisonIso (TopCat.of PUnit)
            (fun _ : ℕ => TopCat.of PUnit)).hom
            ((Limits.Sigma.ι
              (fun _ : ℕ => TopCat.of PUnit ⨯ TopCat.of PUnit) j)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit)))) = PUnit.unit ∧
      (Limits.prod.snd :
          TopCat.of PUnit ⨯ ∐ (fun _ : ℕ => TopCat.of PUnit) ⟶
            ∐ (fun _ : ℕ => TopCat.of PUnit))
          ((TopCat.prodCoproductComparisonIso (TopCat.of PUnit)
            (fun _ : ℕ => TopCat.of PUnit)).hom
            ((Limits.Sigma.ι
              (fun _ : ℕ => TopCat.of PUnit ⨯ TopCat.of PUnit) j)
              ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
                (PUnit.unit, PUnit.unit)))) =
          (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j) PUnit.unit := by
  have hLeg := TopCat.prodCoproductComparison_ι
    (K := TopCat.of PUnit) (F := fun _ : ℕ => TopCat.of PUnit) j
  have hPt : ((TopCat.prodCoproductComparisonIso (TopCat.of PUnit)
        (fun _ : ℕ => TopCat.of PUnit)).hom
        ((Limits.Sigma.ι
          (fun _ : ℕ => TopCat.of PUnit ⨯ TopCat.of PUnit) j)
          ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
            (PUnit.unit, PUnit.unit)))) =
      ((Limits.prod.map (𝟙 (TopCat.of PUnit))
        (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j))
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) := by
    simpa [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hLeg _
  have hTrans : ((Limits.prod.map (𝟙 (TopCat.of PUnit))
        (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j))
        ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
          (PUnit.unit, PUnit.unit))) =
      (TopCat.prodIsoProd (TopCat.of PUnit)
        (∐ (fun _ : ℕ => TopCat.of PUnit))).inv
        (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j)
          PUnit.unit) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  have hEq : ((TopCat.prodCoproductComparisonIso (TopCat.of PUnit)
        (fun _ : ℕ => TopCat.of PUnit)).hom
        ((Limits.Sigma.ι
          (fun _ : ℕ => TopCat.of PUnit ⨯ TopCat.of PUnit) j)
          ((TopCat.prodIsoProd (TopCat.of PUnit) (TopCat.of PUnit)).inv
            (PUnit.unit, PUnit.unit)))) =
      (TopCat.prodIsoProd (TopCat.of PUnit)
        (∐ (fun _ : ℕ => TopCat.of PUnit))).inv
        (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j)
          PUnit.unit) :=
    hPt.trans hTrans
  have hFst : (Limits.prod.fst :
        TopCat.of PUnit ⨯ ∐ (fun _ : ℕ => TopCat.of PUnit) ⟶ TopCat.of PUnit)
        ((TopCat.prodIsoProd (TopCat.of PUnit)
          (∐ (fun _ : ℕ => TopCat.of PUnit))).inv
          (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j)
            PUnit.unit)) = PUnit.unit :=
    ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_fst (TopCat.of PUnit)
        (∐ (fun _ : ℕ => TopCat.of PUnit)))
      (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j) PUnit.unit)
  have hSnd : (Limits.prod.snd :
        TopCat.of PUnit ⨯ ∐ (fun _ : ℕ => TopCat.of PUnit) ⟶
          ∐ (fun _ : ℕ => TopCat.of PUnit))
        ((TopCat.prodIsoProd (TopCat.of PUnit)
          (∐ (fun _ : ℕ => TopCat.of PUnit))).inv
          (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j)
            PUnit.unit)) =
        (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j) PUnit.unit :=
    ConcreteCategory.congr_hom
      (TopCat.prodIsoProd_inv_snd (TopCat.of PUnit)
        (∐ (fun _ : ℕ => TopCat.of PUnit)))
      (PUnit.unit, (Limits.Sigma.ι (fun _ : ℕ => TopCat.of PUnit) j) PUnit.unit)
  exact ⟨(congrArg _ hEq).trans hFst, (congrArg _ hEq).trans hSnd⟩

#print axioms prodCoproduct_nat_punit_point

end MathlibExtTest.Topology.Category.TopCat.ProdCoproductTests
