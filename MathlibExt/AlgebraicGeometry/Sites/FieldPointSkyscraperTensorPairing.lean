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
# Tensor pairing of skyscrapers at a field geometric point

Let Ω/k be a separable closure of fields in universe u and c = max(u, w).
At the geometric point Spec Ω → Spec k, let L be the stalk functor
and S its skyscraper right adjoint. Abelian coefficient groups are in
AddCommGrpCat c, and all tensor products of groups are over ℤ.

The skyscraper tensor pairing
μ : S(M) ⊗_sheaf S(N) → S(M ⊗[ℤ] N)
is adjoint to the stalk tensor comparison followed by the tensor of
the counits. Its defining equation is
ε_(M⊗N) ∘ L(μ) = (ε_M ⊗ ε_N) ∘ τ.
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

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and c = max(u, w). On the small étale site of Spec k, let L be
the stalk at Spec Ω → Spec k, S its skyscraper right adjoint, and
ε : L S → id the counit. All coefficient groups lie in AddCommGrpCat c.
For groups M and N, this sheaf pairing
μ : S(M) ⊗_sheaf S(N) → S(M ⊗[ℤ] N)
is the adjoint transpose of (ε_M ⊗ ε_N) ∘ τ, with
τ : L(S(M) ⊗_sheaf S(N)) ≅ L(S(M)) ⊗[ℤ] L(S(N)). -/
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
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and c = max(u, w). On the small étale site of Spec k, let L be
the stalk at Spec Ω → Spec k, S its skyscraper right adjoint, and
ε : L S → id the counit. All coefficient groups lie in AddCommGrpCat c.
For coefficient groups M, N, the pairing μ satisfies
ε_(M⊗N) ∘ L(μ) = (ε_M ⊗ ε_N) ∘ τ,
where τ is the stalk tensor comparison
L(S(M) ⊗_sheaf S(N)) ≅ L(S(M)) ⊗[ℤ] L(S(N)). -/
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
