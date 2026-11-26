/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProjectionData
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProjectionTensorNaturality

/-!
# Stalk and counit characteristics of field Godement tensor projections

Let k be a field, p₀ its unique topological point, L=x_{p₀}^* its canonical stalk, F(M) the
family skyscraper product, and P(M₀)=x_{p₀*}M₀. The source and target tensor stalks are
L(F(M))⊗L(F(N)) and L(P(M₀))⊗L(P(N₀)).

The stalk tensor comparisons commute with the projected stalk arrows L(π_M)⊗L(π_N). Composing
with the tensor of point counits equals the tensor of the family counit components. These
equations characterize both the family-projected pairing and the canonical point pairing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

/-- For a field k and additive-group families M,N on Spec(k), let L be the canonical stalk at its
unique point and F the skyscraper-product functor. Define the source stalk tensor as
L(F(M))⊗_ℤ L(F(N)), an additive group of height max(u,w). -/
def fieldGodementSourceStalkTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    AddCommGrpCat.{max u w} :=
  AddCommGrpCat.of
    (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementFamilySheaf.{u, w} k M) ⊗[ℤ]
      ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
          (fieldGodementFamilySheaf.{u, w} k N))

/-- Let k be a field, p₀ its unique spectrum point, and M,N coefficient families. The target stalk
tensor is L(x_{p₀*}M_{p₀})⊗_ℤ L(x_{p₀*}N_{p₀}), with L the canonical point stalk. -/
def fieldGodementTargetStalkTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    AddCommGrpCat.{max u w} :=
  AddCommGrpCat.of
    (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementPointSheaf.{u, w} k (M default)) ⊗[ℤ]
      ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
          (fieldGodementPointSheaf.{u, w} k (N default)))

/-- For a field k and families M,N, apply the canonical tensor-sheaf stalk isomorphism to
F(M),F(N). Its forward map is L(F(M)⊗F(N)) → L(F(M))⊗_ℤ L(F(N)), where L is the canonical
point stalk and the source tensor is sheafified. -/
def fieldGodementSourceStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementFamilyTensorSheaf.{u, w} k M N) ⟶
      fieldGodementSourceStalkTensor.{u, w} k M N :=
  (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) (fieldGodementCanonicalPoint.{u, w} k)
    (fieldGodementFamilySheaf.{u, w} k M) (fieldGodementFamilySheaf.{u, w} k N)).hom

/-- Let k be a field and M,N families. The canonical stalk tensor comparison gives L(P(M₀)⊗P(N₀))
→ L(P(M₀))⊗_ℤ L(P(N₀)), where P is the canonical point skyscraper and L its stalk. -/
def fieldGodementTargetStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).obj
        (fieldGodementPointTensorSheaf.{u, w} k M N) ⟶
      fieldGodementTargetStalkTensor.{u, w} k M N :=
  (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) (fieldGodementCanonicalPoint.{u, w} k)
    (fieldGodementPointSheaf.{u, w} k (M default))
        (fieldGodementPointSheaf.{u, w} k (N default))).hom

/-- For a field k and coefficient families M,N, take L of their product projections and tensor
them. This defines L(F(M))⊗L(F(N)) → L(P(M₀))⊗L(P(N₀)) as L(π_M)⊗_ℤ L(π_N). -/
def fieldGodementProjectedStalkTensorMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementSourceStalkTensor.{u, w} k M N ⟶ fieldGodementTargetStalkTensor.{u, w} k M N :=
  let L := (fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})
  AddCommGrpCat.ofHom (TensorProduct.map
    (L.map (fieldGodementFamilyProjection.{u, w} k M)).hom.toIntLinearMap
    (L.map (fieldGodementFamilyProjection.{u, w} k N)).hom.toIntLinearMap).toAddMonoidHom

/-- Let k be a field, M,N coefficient families, and ε the canonical point stalk–skyscraper counit.
The tensor ε_{M₀}⊗ε_{N₀} maps L(P(M₀))⊗_ℤ L(P(N₀)) to M₀⊗_ℤ N₀. -/
def fieldGodementPointCounitTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementTargetStalkTensor.{u, w} k M N ⟶ AddCommGrpCat.of (M default ⊗[ℤ] N default) :=
  let adj := (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w})
  AddCommGrpCat.ofHom (TensorProduct.map
    (adj.counit.app (M default)).hom.toIntLinearMap
    (adj.counit.app (N default)).hom.toIntLinearMap).toAddMonoidHom

/-- For a field k and families M,N, evaluate the Godement family counits at the unique spectrum
point p₀ and tensor those two additive-group maps. This gives L(F(M))⊗_ℤ L(F(N)) → M₀⊗_ℤ N₀. -/
def fieldGodementFamilyCounitTensor (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementSourceStalkTensor.{u, w} k M N ⟶ AddCommGrpCat.of (M default ⊗[ℤ] N default) :=
  let adj := smallEtaleGodementAdjunction.{u, w} (Spec (.of k))
  AddCommGrpCat.ofHom (TensorProduct.map
    ((adj.counit.app M) default).hom.toIntLinearMap
    ((adj.counit.app N) default).hom.toIntLinearMap).toAddMonoidHom

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k and families M,N, let λ be the family pairing followed by point projection, t_F
the source stalk tensor comparison, and c_F the tensor of family counits at p₀. Then
L(λ)≫ε_{M₀⊗N₀}=t_F≫c_F. Both maps go from L(F(M)⊗F(N)) to M₀⊗_ℤ N₀. -/
theorem fieldGodementProjectedPairing_characteristic
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementFamilyProjectedPairing.{u, w} k M N) ≫
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.counit.app
          (AddCommGrpCat.of (M default ⊗[ℤ] N default)) =
      fieldGodementSourceStalkTensorMap.{u, w} k M N ≫
          fieldGodementFamilyCounitTensor.{u, w} k M N :=
  fieldGodementSkyscraperPairing_projection_counit.{u, w} k M N

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field, M,N families, λ_p the canonical point pairing, t_P its stalk tensor
comparison, and c_P the tensor of point counits. Then L(λ_p)≫ε_{M₀⊗N₀}=t_P≫c_P, with source
L(P(M₀)⊗P(N₀)). -/
theorem fieldGodementPointPairing_characteristic
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementPointPairing.{u, w} k M N) ≫
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.counit.app
          (AddCommGrpCat.of (M default ⊗[ℤ] N default)) =
      fieldGodementTargetStalkTensorMap.{u, w} k M N ≫
          fieldGodementPointCounitTensor.{u, w} k M N :=
  fieldCanonicalPointSkyscraperTensorPairing_counit.{u, w} k (M default) (N default)

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k and families M,N, let t_F,t_P be the family and point tensor stalk comparisons
and v=L(π_M)⊗L(π_N). The tensor sheaf projection satisfies L(π_M⊗π_N)≫t_P=t_F≫v. -/
theorem fieldGodementStoredProjectionTensor_naturality
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((fieldGodementCanonicalPoint.{u, w} k).sheafFiber (A := AddCommGrpCat.{max u w})).map
        (fieldGodementTensorProjectionMap.{u, w} k M N) ≫
        fieldGodementTargetStalkTensorMap.{u, w} k M N =
      fieldGodementSourceStalkTensorMap.{u, w} k M N ≫
          fieldGodementProjectedStalkTensorMap.{u, w} k M N :=
  fieldGodementProjectionTensor_naturality.{u, w} k M N

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field and M,N coefficient families. The projected stalk tensor map v=L(π_M)⊗L(π_N)
followed by c_P, the tensor of canonical point counits, equals c_F, the tensor of family
counit components at the unique point: v≫c_P=c_F. -/
theorem fieldGodementStoredCounitTensor_comp
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementProjectedStalkTensorMap.{u, w} k M N ≫
        fieldGodementPointCounitTensor.{u, w} k M N =
      fieldGodementFamilyCounitTensor.{u, w} k M N :=
  fieldGodementProjectedCounitTensor.{u, w} k M N

end AlgebraicGeometry.Scheme.DerivedSections
