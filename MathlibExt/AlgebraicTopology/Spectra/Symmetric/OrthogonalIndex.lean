/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionMatrix
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.Index
import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerIndex

/-!
# The native enriched symmetric to orthogonal bare index map

The entire based finite-bijection copower maps to the entire freely based
orthogonal Hom. Each original bijection has its actual coordinate matrix point.
Composition is proved on both complete source Hom factors. This is the bare
index prerequisite; sphere coefficients and operator coends remain separate.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Spectra

private abbrev SymI := PointedCGWH.CopowerIndex.{u, v, 0} Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

attribute [local instance] OrthogonalIndex.enrichedCategory

/-- The full native Hom map is induced by every original finite-bijection matrix point. -/
def symmetricOrthogonalHomMap (A B : Operad.SmallFinBijGroupoid) :
    (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A ⟶[V]
      PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B) ⟶
        OrthogonalIndex.hom.{u, v} A.of.len B.of.len :=
  (PointedCGWH.basedDiscreteCofanIsColimit.{u, v, 0} (A ⟶ B)).desc
    (Cofan.mk _ (fun f => OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)))

/-- Every original finite-bijection generator maps to its actual matrix point. -/
@[reassoc]
theorem symmetricOrthogonalHomMap_generator {A B : Operad.SmallFinBijGroupoid}
    (f : A ⟶ B) :
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (A ⟶ B) f ≫
        symmetricOrthogonalHomMap.{u, v} A B =
      OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f) :=
  (PointedCGWH.basedDiscreteCofanIsColimit.{u, v, 0} (A ⟶ B)).fac
    (Cofan.mk _ (fun g => OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix g))) ⟨f⟩

/-- Enriched identity is the original finite identity and original orthogonal matrix identity. -/
theorem symmetricOrthogonalHomMap_id (A : Operad.SmallFinBijGroupoid) :
    eId V (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) ≫
        symmetricOrthogonalHomMap.{u, v} A A =
      @eId V _ _ OrthogonalIndex (OrthogonalIndex.enrichedCategory.{u, v}) A.of.len := by
  have hId := PointedCGWH.copowerIndex_id.{u, v, 0} Operad.SmallFinBijGroupoid A
  have hGen := symmetricOrthogonalHomMap_generator.{u, v} (𝟙 A)
  have hMatrix := congrArg (OrthogonalIndex.matrixPoint.{u, v}) (smallBijectionMatrix_id A)
  exact (congrArg (fun q => q ≫ symmetricOrthogonalHomMap.{u, v} A A) hId).trans
    (hGen.trans (hMatrix.trans (OrthogonalIndex.enrichedCategory_id.{u, v} A.of.len).symm))

/-- Full enriched composition is preserved on both whole finite-bijection Hom copowers. -/
theorem symmetricOrthogonalHomMap_comp (A B C : Operad.SmallFinBijGroupoid) :
    eComp V (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid C) ≫
      symmetricOrthogonalHomMap.{u, v} A C =
        (symmetricOrthogonalHomMap.{u, v} A B ⊗ₘ symmetricOrthogonalHomMap.{u, v} B C) ≫
          @eComp V _ _ OrthogonalIndex (OrthogonalIndex.enrichedCategory.{u, v})
            A.of.len B.of.len C.of.len := by
  apply PointedCGWH.basedDiscretePair_hom_ext.{u, v, 0} (A ⟶ B) (B ⟶ C)
  intro f g
  have hSource := PointedCGWH.copowerIndex_comp_generator.{u, v, 0}
    Operad.SmallFinBijGroupoid f g
  have hTarget := (OrthogonalIndex.enrichedCategory_comp.{u, v}
    (smallBijectionMatrix f) (smallBijectionMatrix g)).1
  let p : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (A ⟶ B) ⊗
      PointedCGWH.basedDiscreteObj.{u, v, 0} (B ⟶ C) :=
    PointedCGWH.basedDiscretePairIncl.{u, v, 0} (A ⟶ B) (B ⟶ C) f g
  let c := eComp V
    (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
    (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B)
    (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid C)
  let m := symmetricOrthogonalHomMap.{u, v} A C
  let cc := @eComp V _ _ OrthogonalIndex (OrthogonalIndex.enrichedCategory.{u, v})
    A.of.len B.of.len C.of.len
  let ef := OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)
  let eg := OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix g)
  have hLeft : p ≫ (c ≫ m) =
      OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix (f ≫ g)) :=
    (Category.assoc p c m).symm.trans
      ((congrArg (fun q => q ≫ m) hSource).trans
        (symmetricOrthogonalHomMap_generator.{u, v} (f ≫ g)))
  have hTensor : p ≫ (symmetricOrthogonalHomMap.{u, v} A B ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} B C) = (λ_ (𝟙_ V)).inv ≫ (ef ⊗ₘ eg) := by
    let lf : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (A ⟶ B) :=
      PointedCGWH.basedDiscreteIncl.{u, v, 0} (A ⟶ B) f
    let lg : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (B ⟶ C) :=
      PointedCGWH.basedDiscreteIncl.{u, v, 0} (B ⟶ C) g
    have ht : (lf ⊗ₘ lg) ≫ (symmetricOrthogonalHomMap.{u, v} A B ⊗ₘ
        symmetricOrthogonalHomMap.{u, v} B C) = ef ⊗ₘ eg :=
      (tensorHom_comp_tensorHom lf lg
        (symmetricOrthogonalHomMap.{u, v} A B)
        (symmetricOrthogonalHomMap.{u, v} B C)).trans
        (congrArg₂ (fun x y => x ⊗ₘ y)
          (symmetricOrthogonalHomMap_generator.{u, v} f)
          (symmetricOrthogonalHomMap_generator.{u, v} g))
    change ((λ_ (𝟙_ V)).inv ≫ (lf ⊗ₘ lg)) ≫ _ = _
    exact (Category.assoc _ _ _).trans (congrArg (fun q => (λ_ (𝟙_ V)).inv ≫ q) ht)
  have hRight : p ≫ ((symmetricOrthogonalHomMap.{u, v} A B ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} B C) ≫ cc) =
      (λ_ (𝟙_ V)).inv ≫ (ef ⊗ₘ eg) ≫ cc :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ cc) hTensor)
  have hMatrix := congrArg (OrthogonalIndex.matrixPoint.{u, v}) (smallBijectionMatrix_comp f g)
  exact hLeft.trans (hMatrix.trans (hTarget.symm.trans hRight.symm))

/-- The genuine bare enriched index functor sends every original finite bijection to its matrix. -/
def symmetricOrthogonalIndexFunctor :
    EnrichedFunctor V SymI OrthogonalIndex where
  obj A := A.of.len
  map A B := symmetricOrthogonalHomMap.{u, v} A B
  map_id A := symmetricOrthogonalHomMap_id.{u, v} A
  map_comp A B C := symmetricOrthogonalHomMap_comp.{u, v} A B C

/-- Object dimensions are the original finite cardinalities. -/
@[simp]
theorem symmetricOrthogonalIndexFunctor_obj (A : Operad.SmallFinBijGroupoid) :
    symmetricOrthogonalIndexFunctor.{u, v}.obj
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) = A.of.len := rfl

/-- The full functor Hom component is the original finite-bijection matrix-point copower map. -/
theorem symmetricOrthogonalIndexFunctor_map (A B : Operad.SmallFinBijGroupoid) :
    symmetricOrthogonalIndexFunctor.{u, v}.map
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B) =
      symmetricOrthogonalHomMap.{u, v} A B := rfl

end CategoryTheory.Spectra
