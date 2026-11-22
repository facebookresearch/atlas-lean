/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerIndex

/-!
# Tensor on pointed copower Hom objects

A monoidal index gives a tensor map between pointed copowers of two Hom sets. The generator
formula sends a pair of index morphisms to their tensor product, with the required universe
enlargement.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uI

open CategoryTheory CategoryTheory.MonoidalCategory

namespace PointedCGWH

variable (I : Type uI) [Category.{w} I] [MonoidalCategory I]

/-- The original arrow tensor defines the full native copower Hom tensor map. -/
def copowerTensorHom (i i' j j' : I) :
    (copowerIndexObj.{u, v, w} I i ⟶[PointedCGWH.{u, max v w}]
        copowerIndexObj.{u, v, w} I i') ⊗
      (copowerIndexObj.{u, v, w} I j ⟶[PointedCGWH.{u, max v w}]
        copowerIndexObj.{u, v, w} I j') ⟶
      (copowerIndexObj.{u, v, w} I (i ⊗ j) ⟶[PointedCGWH.{u, max v w}]
        copowerIndexObj.{u, v, w} I (i' ⊗ j')) :=
  basedDiscreteTensorProductHom.{u, v, w} (i ⟶ i') (j ⟶ j') ≫
    basedDiscreteFunctor.{u, v, w}.map
      (↾fun p : (i ⟶ i') × (j ⟶ j') => p.1 ⊗ₘ p.2)

/-- Every original ordered arrow pair retains its literal tensor-arrow injection. -/
theorem copowerTensorHom_generator {i i' j j' : I} (f : i ⟶ i') (g : j ⟶ j') :
    basedDiscretePairIncl.{u, v, w} (i ⟶ i') (j ⟶ j') f g ≫
        copowerTensorHom.{u, v, w} I i i' j j' =
      basedDiscreteIncl.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j')) (f ⊗ₘ g) := by
  let U : PointedCGWH.{u, max v w} := 𝟙_ PointedCGWH.{u, max v w}
  let E : Type w := i ⟶ i'
  let F : Type w := j ⟶ j'
  let T : PointedCGWH.{u, max v w} :=
    basedDiscreteObj.{u, v, w} E ⊗ basedDiscreteObj.{u, v, w} F
  let P : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} (E × F)
  let H : PointedCGWH.{u, max v w} := basedDiscreteObj.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j'))
  let p : U ⟶ T := basedDiscretePairIncl.{u, v, w} E F f g
  let m : T ⟶ P := basedDiscreteTensorProductHom.{u, v, w} E F
  let n : P ⟶ H := basedDiscreteFunctor.{u, v, w}.map (↾fun q : E × F => q.1 ⊗ₘ q.2)
  let l : U ⟶ P := basedDiscreteIncl.{u, v, w} (E × F) (f, g)
  let t : U ⟶ H := basedDiscreteIncl.{u, v, w} ((i ⊗ j) ⟶ (i' ⊗ j')) (f ⊗ₘ g)
  have hm : p ≫ m = l := basedDiscreteTensorProductHom_pair.{u, v, w} E F f g
  have hn : l ≫ n = t :=
    basedDiscreteIncl_naturality.{u, v, w} (fun q : E × F => q.1 ⊗ₘ q.2) (f, g)
  change p ≫ (m ≫ n) = t
  exact (Category.assoc p m n).symm.trans
    ((congrArg (fun q : U ⟶ P => q ≫ n) hm).trans hn)

end PointedCGWH
