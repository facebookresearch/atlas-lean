/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleTensorCoefficients
public import MathlibExt.AlgebraicGeometry.Sites.FieldGaloisSkyscraperComparison

/-!
# The actual prescribed field-point skyscraper tensor pairing

The genuine point tensor-stalk isomorphism and its original adjunction counits
construct the binary skyscraper map. Its characteristic square is literal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual prescribed-point skyscraper pairing is the adjoint transpose of the original tensor
counits. -/
def fieldPointSkyscraperTensorPairing (M N : AddCommGrpCat.{max u w}) :
    let p := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) (R.obj M) (R.obj N) ⟶
      R.obj (AddCommGrpCat.of (M ⊗[ℤ] N)) :=
  let p := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let adj := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  adj.homEquiv _ _
    ((smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        (adj.counit.app M).hom.toIntLinearMap (adj.counit.app N).hom.toIntLinearMap).toAddMonoidHom)

set_option backward.isDefEq.respectTransparency.types false in
/-- Its original point counit is exactly the tensor of the two original counits after the actual
stalk tensor map. -/
theorem fieldPointSkyscraperTensorPairing_counit (M N : AddCommGrpCat.{max u w}) :
    let p := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    let adj := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    L.map (fieldPointSkyscraperTensorPairing.{u, w} k Ω M N) ≫
        adj.counit.app (AddCommGrpCat.of (M ⊗[ℤ] N)) =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (adj.counit.app M).hom.toIntLinearMap
              (adj.counit.app N).hom.toIntLinearMap).toAddMonoidHom := by
  intro p L R adj
  let b := (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
    AddCommGrpCat.ofHom (TensorProduct.map
      (adj.counit.app M).hom.toIntLinearMap (adj.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  exact (adj.homEquiv_counit _ _ (adj.homEquiv _ _ b)).symm.trans
    ((adj.homEquiv _ _).symm_apply_apply b)

end AlgebraicGeometry.Scheme.DerivedSections
