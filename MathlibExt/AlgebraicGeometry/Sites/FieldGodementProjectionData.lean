/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementTensorProjection
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-!
# Field Godement family projections and tensor pairings

Let k be a field, p₀ the unique topological point of Spec(k), and x_y the canonical geometric
points used by Godement. For an additive-group family M_y of height max(u,w), write F(M)=Π_y
x_{y*}M_y and P(M₀)=x_{p₀*}M_{p₀}. The product projection π_M maps F(M) to P(M₀).

The sheafified integer tensor of two family sheaves maps to the tensor of their point sheaves
by π_M⊗π_N. The family skyscraper pairing followed by projection and the canonical point
pairing have the same target P(M₀⊗_ℤ N₀).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.DerivedSections
variable (k : Type u) [Field k]

/-- Let k be a field and M_y an additive-group family indexed by the topological points of
Spec(k), at coefficient height max(u,w). Define fieldGodementFamilySheaf(M) as the product Π_y
x_{y*}M_y of the canonical point skyscrapers. -/
def fieldGodementFamilySheaf (M : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleGodementSkyscrapers.{u, w} (Spec (.of k))).obj M

/-- For a field k and M∈AddCommGrpCat.{max(u,w)}, fieldGodementPointSheaf(M) is the skyscraper
sheaf x_{p₀*}M at the canonical geometric point over the unique topological point p₀ of
Spec(k). -/
def fieldGodementPointSheaf (M : AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor.obj M

/-- Let k be a field and M_y an additive-group coefficient family on Spec(k). The product
projection at its unique point p₀ gives F(M)=Π_y x_{y*}M_y → x_{p₀*}M_{p₀}. This is the map
between fieldGodementFamilySheaf and fieldGodementPointSheaf. -/
def fieldGodementFamilyProjection (M : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilySheaf.{u, w} k M ⟶ fieldGodementPointSheaf.{u, w} k (M default) :=
  Pi.π (fun y : Spec (.of k) =>
    (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) y)).skyscraperSheafFunctor.obj
          (M y)) default

/-- For a field k and coefficient families M,N on Spec(k), define the source tensor sheaf to be
the sheafification of the sectionwise integer tensor F(M)⊗_ℤ F(N), where F is the canonical
skyscraper product functor. -/
def fieldGodementFamilyTensorSheaf (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleTensorSheaf.{u, w} (Spec (.of k))
    (fieldGodementFamilySheaf.{u, w} k M) (fieldGodementFamilySheaf.{u, w} k N)

/-- Let k be a field, M,N additive-group families, and p₀ its unique spectrum point. Define the
point tensor sheaf to be the sheafified integer tensor x_{p₀*}M_{p₀}⊗x_{p₀*}N_{p₀}. -/
def fieldGodementPointTensorSheaf (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  smallEtaleTensorSheaf.{u, w} (Spec (.of k))
    (fieldGodementPointSheaf.{u, w} k (M default)) (fieldGodementPointSheaf.{u, w} k (N default))

/-- For additive-group families M,N over Spec(k), tensor their product projections π_M and π_N to
obtain F(M)⊗F(N) → x_{p₀*}M_{p₀}⊗x_{p₀*}N_{p₀}. The source and target are the sheafified
integer tensors. -/
def fieldGodementTensorProjectionMap (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilyTensorSheaf.{u, w} k M N ⟶ fieldGodementPointTensorSheaf.{u, w} k M N :=
  smallEtaleTensorSheafMap.{u, w} (Spec (.of k))
    (fieldGodementFamilyProjection.{u, w} k M) (fieldGodementFamilyProjection.{u, w} k N)

/-- For a field k and additive-group families M,N, compose the Godement skyscraper-family pairing
F(M)⊗F(N) → F(M⊗_ℤ N) with the product projection at p₀. This defines a map to
x_{p₀*}(M_{p₀}⊗_ℤ N_{p₀}). -/
def fieldGodementFamilyProjectedPairing (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementFamilyTensorSheaf.{u, w} k M N ⟶
      fieldGodementPointSheaf.{u, w} k (AddCommGrpCat.of (M default ⊗[ℤ] N default)) :=
  smallEtaleGodementSkyscraperPairing.{u, w} (Spec (.of k)) M N ≫
    fieldGodementFamilyProjection.{u, w} k
        (smallEtaleGodementFamilyTensor.{u, w} (Spec (.of k)) M N)

/-- Let k be a field and M,N coefficient families. The canonical geometric-point pairing gives
x_{p₀*}M_{p₀}⊗x_{p₀*}N_{p₀} → x_{p₀*}(M_{p₀}⊗_ℤ N_{p₀}), with the source tensor sheafified
sectionwise over ℤ. -/
def fieldGodementPointPairing (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    fieldGodementPointTensorSheaf.{u, w} k M N ⟶
      fieldGodementPointSheaf.{u, w} k (AddCommGrpCat.of (M default ⊗[ℤ] N default)) :=
  fieldCanonicalPointSkyscraperTensorPairing.{u, w} k (M default) (N default)

end AlgebraicGeometry.Scheme.DerivedSections
