/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionBlocks
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalIndex
import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerTensorHom

/-!
# The full tensor Hom square for finite-bijection inclusion

The actual symmetric Hom tensor is transported to the ordered orthogonal
block-sum tensor on both complete Hom factors. The identities are the
original finite identities; the zero object is the original empty finite
set, with no additional completion object.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory

/-- The full tensor Hom square preserves the original ordered native index tensor. -/
theorem symmetricOrthogonalHomMap_tensor (A A' B B' : Operad.SmallFinBijGroupoid) :
    PointedCGWH.copowerTensorHom.{u, v, 0} Operad.SmallFinBijGroupoid A A' B B' ≫
        symmetricOrthogonalHomMap.{u, v} (A ⊗ B) (A' ⊗ B') =
      (symmetricOrthogonalHomMap.{u, v} A A' ⊗ₘ symmetricOrthogonalHomMap.{u, v} B B') ≫
        OrthogonalIndex.tensorMap.{u, v} A.of.len A'.of.len B.of.len B'.of.len := by
  apply PointedCGWH.basedDiscretePair_hom_ext.{u, v, 0} (A ⟶ A') (B ⟶ B')
  intro f g
  let V := PointedCGWH.{u, v}
  let p : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (A ⟶ A') ⊗
      PointedCGWH.basedDiscreteObj.{u, v, 0} (B ⟶ B') :=
    PointedCGWH.basedDiscretePairIncl.{u, v, 0} (A ⟶ A') (B ⟶ B') f g
  let c := PointedCGWH.copowerTensorHom.{u, v, 0}
    Operad.SmallFinBijGroupoid A A' B B'
  let m := symmetricOrthogonalHomMap.{u, v} (A ⊗ B) (A' ⊗ B')
  let cc := OrthogonalIndex.tensorMap.{u, v} A.of.len A'.of.len B.of.len B'.of.len
  let ef := OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)
  let eg := OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix g)
  have hSource := PointedCGWH.copowerTensorHom_generator.{u, v, 0}
    Operad.SmallFinBijGroupoid f g
  have hTarget := (OrthogonalIndex.tensorMap_blockSum.{u, v}
    (smallBijectionMatrix f) (smallBijectionMatrix g)).1
  have hLeft : p ≫ (c ≫ m) =
      OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix (f ⊗ₘ g)) :=
    (Category.assoc p c m).symm.trans
      ((congrArg (fun q => q ≫ m) hSource).trans
        (symmetricOrthogonalHomMap_generator.{u, v} (f ⊗ₘ g)))
  have hTensor : p ≫ (symmetricOrthogonalHomMap.{u, v} A A' ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} B B') = (λ_ (𝟙_ V)).inv ≫ (ef ⊗ₘ eg) := by
    let lf : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (A ⟶ A') :=
      PointedCGWH.basedDiscreteIncl.{u, v, 0} (A ⟶ A') f
    let lg : 𝟙_ V ⟶ PointedCGWH.basedDiscreteObj.{u, v, 0} (B ⟶ B') :=
      PointedCGWH.basedDiscreteIncl.{u, v, 0} (B ⟶ B') g
    have ht : (lf ⊗ₘ lg) ≫ (symmetricOrthogonalHomMap.{u, v} A A' ⊗ₘ
        symmetricOrthogonalHomMap.{u, v} B B') = ef ⊗ₘ eg :=
      (tensorHom_comp_tensorHom lf lg
        (symmetricOrthogonalHomMap.{u, v} A A')
        (symmetricOrthogonalHomMap.{u, v} B B')).trans
        (congrArg₂ (fun x y => x ⊗ₘ y)
          (symmetricOrthogonalHomMap_generator.{u, v} f)
          (symmetricOrthogonalHomMap_generator.{u, v} g))
    change ((λ_ (𝟙_ V)).inv ≫ (lf ⊗ₘ lg)) ≫ _ = _
    exact (Category.assoc _ _ _).trans (congrArg (fun q => (λ_ (𝟙_ V)).inv ≫ q) ht)
  have hRight : p ≫ ((symmetricOrthogonalHomMap.{u, v} A A' ⊗ₘ
      symmetricOrthogonalHomMap.{u, v} B B') ≫ cc) =
      (λ_ (𝟙_ V)).inv ≫ (ef ⊗ₘ eg) ≫ cc :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ cc) hTensor)
  have hMatrix := congrArg (OrthogonalIndex.matrixPoint.{u, v})
    (smallBijectionMatrix_tensor f g)
  exact hLeft.trans (hMatrix.trans (hTarget.symm.trans hRight.symm))

/-- The source tensor object uses the original sum of finite cardinalities. -/
theorem symmetricOrthogonalIndexFunctor_tensorObj (A B : Operad.SmallFinBijGroupoid) :
    symmetricOrthogonalIndexFunctor.{u, v}.obj
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid (A ⊗ B)) =
        A.of.len + B.of.len := rfl

/-- The source monoidal unit is the actual empty finite set and maps to dimension zero. -/
theorem symmetricOrthogonalIndexFunctor_unitObj :
    symmetricOrthogonalIndexFunctor.{u, v}.obj
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid
        (𝟙_ Operad.SmallFinBijGroupoid)) = 0 := rfl

end CategoryTheory.Spectra
