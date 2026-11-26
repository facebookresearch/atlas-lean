/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementProductCollapse
public import MathlibExt.CategoryTheory.Adjunction.ComparisonMonadIso

/-!
# Tensor pairings under the canonical field Godement projection

Let k be a field in universe u, X = Spec k and c = max(u, w).
The canonical geometric point p over the unique point of X has stalk
functor L and skyscraper right adjoint S. For coefficient groups M, N
in AddCommGrpCat c, the skyscraper pairing
μ_p : S(M) ⊗_sheaf S(N) → S(M ⊗[ℤ] N)
is the adjoint transpose of the stalk tensor comparison followed by
ε_M ⊗ ε_N, where ε is the point-adjunction counit.

The Godement right adjoint is the product of skyscrapers over points of X.
Projecting its tensor pairing to the unique point has the same counit
characteristic as μ_p. The tensor of the two product-projected point
counits is the tensor of the two Godement-family counits at that point.
The coefficient universe w is independent of u.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k : Type u) [Field k]

/-- Let k be a field in universe u, X = Spec k, c = max(u, w),
and p the canonical geometric point over X's unique point. Write L for
its stalk functor, S for its skyscraper right adjoint, and ε for the
counit of L ⊣ S.
For M, N ∈ AddCommGrpCat c, this is the sheaf morphism
μ_p : S(M) ⊗_sheaf S(N) → S(M ⊗[ℤ] N).
It is adjoint to (ε_M ⊗ ε_N) ∘ τ, where
τ : L(S(M) ⊗_sheaf S(N)) ≅ L(S(M)) ⊗[ℤ] L(S(N))
is the stalk tensor comparison. -/
def fieldCanonicalPointSkyscraperTensorPairing (M N : AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) (R.obj M) (R.obj N) ⟶
      R.obj (AddCommGrpCat.of (M ⊗[ℤ] N)) :=
  let p := fieldGodementCanonicalPoint.{u, w} k
  let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  a.homEquiv _ _
    ((smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        (a.counit.app M).hom.toIntLinearMap (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field in universe u, X = Spec k, c = max(u, w),
and p the canonical geometric point over X's unique point. Write L for
its stalk functor, S for its skyscraper right adjoint, and ε for the
counit of L ⊣ S.
For coefficient groups M, N, the pairing μ_p satisfies
ε_(M⊗N) ∘ L(μ_p) = (ε_M ⊗ ε_N) ∘ τ,
where τ : L(S(M) ⊗_sheaf S(N)) ≅ L(S(M)) ⊗[ℤ] L(S(N)).
This identifies its adjoint transpose as the tensor of the point counits. -/
theorem fieldCanonicalPointSkyscraperTensorPairing_counit (M N : AddCommGrpCat.{max u w}) :
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
    let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    L.map (fieldCanonicalPointSkyscraperTensorPairing.{u, w} k M N) ≫
        a.counit.app (AddCommGrpCat.of (M ⊗[ℤ] N)) =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (a.counit.app M).hom.toIntLinearMap
              (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom := by
  intro p L R a
  let b := (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k)) p (R.obj M) (R.obj N)).hom ≫
    AddCommGrpCat.ofHom (TensorProduct.map
      (a.counit.app M).hom.toIntLinearMap (a.counit.app N).hom.toIntLinearMap).toAddMonoidHom
  exact (a.homEquiv_counit _ _ (a.homEquiv _ _ b)).symm.trans
    ((a.homEquiv _ _).symm_apply_apply b)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field in universe u, X = Spec k, c = max(u, w),
and p the canonical geometric point over X's unique point. Write L for
its stalk functor, S for its skyscraper right adjoint, and ε for the
counit of L ⊣ S.
Let M_y, N_y be families of coefficient groups over y ∈ X, and write
R_G for the product-skyscraper Godement right adjoint and μ_G for its
pairing. Projection π to S(M_* ⊗[ℤ] N_*) at the unique point * satisfies
ε_(M_*⊗N_*) ∘ L(π ∘ μ_G) =
(ε^G_M(*) ⊗ ε^G_N(*)) ∘ τ_(R_G M,R_G N),
where ε^G is the family-adjunction counit and τ is the stalk tensor comparison. -/
theorem fieldGodementSkyscraperPairing_projection_counit
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    let X := Spec (.of k)
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let R := smallEtaleGodementSkyscrapers.{u, w} X
    let T := smallEtaleGodementFamilyTensor.{u, w} X M N
    let π := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (T y)) default
    L.map (smallEtaleGodementSkyscraperPairing.{u, w} X M N ≫ π) ≫
        p.skyscraperSheafAdjunction.counit.app (T default) =
      (smallEtalePointTensorSheafStalkIso.{u, w} X p (R.obj M) (R.obj N)).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default).hom.toIntLinearMap
          (((smallEtaleGodementAdjunction.{u, w} X).counit.app N)
              default).hom.toIntLinearMap).toAddMonoidHom := by
  intro X p L R T π
  have h := congrArg (fun f => f default)
    (smallEtaleGodementSkyscraperPairing_counit.{u, w} X M N)
  have hc := fieldGodementCounit_default.{u, w} k T
  have h' :=
      (congrArg (fun f => L.map (smallEtaleGodementSkyscraperPairing.{u, w} X M N) ≫ f) hc).symm
  exact (congrArg (fun f => f ≫ p.skyscraperSheafAdjunction.counit.app (T default))
    (L.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans (h'.trans h))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field in universe u, X = Spec k, c = max(u, w),
and p the canonical geometric point over X's unique point. Write L for
its stalk functor, S for its skyscraper right adjoint, and ε for the
counit of L ⊣ S.
For coefficient families M, N, let π_M : R_G(M) → S(M_*) and
π_N : R_G(N) → S(N_*) be the Godement product projections at the
unique point. Then
(ε_(M_*) ⊗ ε_(N_*)) ∘ (L(π_M) ⊗ L(π_N)) =
ε^G_M(*) ⊗ ε^G_N(*).
The equality is between maps of tensor products of the corresponding stalk groups. -/
theorem fieldGodementProjectedCounitTensor
    (M N : Spec (.of k) → AddCommGrpCat.{max u w}) :
    let X := Spec (.of k)
    let p := fieldGodementCanonicalPoint.{u, w} k
    let L := p.sheafFiber (A := AddCommGrpCat.{max u w})
    let adj := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    let πM := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) default
    let πN := Pi.π (fun y : X =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (N y)) default
    let t := AddCommGrpCat.ofHom (TensorProduct.map
      (L.map πM).hom.toIntLinearMap (L.map πN).hom.toIntLinearMap).toAddMonoidHom
    let c := AddCommGrpCat.ofHom (TensorProduct.map
      (adj.counit.app (M default)).hom.toIntLinearMap
      (adj.counit.app (N default)).hom.toIntLinearMap).toAddMonoidHom
    let d := AddCommGrpCat.ofHom (TensorProduct.map
      (((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default).hom.toIntLinearMap
      (((smallEtaleGodementAdjunction.{u, w} X).counit.app N)
          default).hom.toIntLinearMap).toAddMonoidHom
    t ≫ c = d := by
  intro X p L adj πM πN t c d
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a b
    change adj.counit.app (M default) (L.map πM a) ⊗ₜ[ℤ]
        adj.counit.app (N default) (L.map πN b) =
      ((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default a ⊗ₜ[ℤ]
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app N) default b
    exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b)
      (ConcreteCategory.congr_hom (fieldGodementCounit_default.{u, w} k M) a).symm
      (ConcreteCategory.congr_hom (fieldGodementCounit_default.{u, w} k N) b).symm
  · intro x y hx hy
    exact ((t ≫ c).hom.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (d.hom.map_add x y).symm)

end AlgebraicGeometry.Scheme.DerivedSections
