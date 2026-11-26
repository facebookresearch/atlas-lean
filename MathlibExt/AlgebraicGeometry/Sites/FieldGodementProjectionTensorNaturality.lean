/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementTensorProjection

/-!
# Tensor stalk naturality for field Godement product projections

Let k be a field and M,N coefficient families over its unique spectrum point. Tensor the two
Godement-family product projections and apply the canonical geometric stalk.

The result commutes with the source and target tensor-of-stalks comparisons. Thus the tensor
sheaf projection corresponds exactly to tensoring the projected stalk maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k, families M,N, canonical stalk L, and product projections π_M,π_N, let t_F and
t_P be the tensor-stalk comparisons for the family products and point skyscrapers. Then
L(π_M⊗π_N)≫t_P=t_F≫(Lπ_M⊗_ℤ Lπ_N). This is the source-to-target square on the specified tensor
sheaves. -/
theorem fieldGodementProjectionTensor_naturality
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    let X := Spec (.of k)
    let p := fieldGodementCanonicalPoint.{u, w} k
    let R := smallEtaleGodementSkyscrapers.{u, w} X
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let A := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    let πM := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) default
    let πN := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) default
    let f := smallEtaleTensorSheafMap.{u, w} X πM πN
    let m := (smallEtalePointTensorSheafStalkIso.{u, w} X p (R.obj M) (R.obj N)).hom
    let n :=
        (smallEtalePointTensorSheafStalkIso.{u, w} X p (A.obj (M default)) (A.obj (N default))).hom
    let t := AddCommGrpCat.ofHom (TensorProduct.map
      (L.map πM).hom.toIntLinearMap (L.map πN).hom.toIntLinearMap).toAddMonoidHom
    L.map f ≫ n = m ≫ t := by
  intro X p R L A πM πN f m n t
  exact smallEtalePointTensorSheafStalkIso_naturality.{u, w} X p πM πN

end AlgebraicGeometry.Scheme.DerivedSections
