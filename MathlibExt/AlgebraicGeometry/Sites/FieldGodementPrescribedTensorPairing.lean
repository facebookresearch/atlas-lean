/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPrescribedMonadPairing

/-!
# The Godement binary pairing at a prescribed closure point

Let Ω be a prescribed separable closure of a field k. The composite Godement-to-canonical and
canonical-to-prescribed point comparisons gives a natural isomorphism of the two endofunctors.

It preserves the binary tensor pairing: the Godement pairing followed by the comparison at F⊗G
equals tensoring the comparisons at F and G and then applying the prescribed point pairing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- For a field k and prescribed separable closure Ω, compose the singleton Godement collapse with
the canonical-to-prescribed point endofunctor comparison. This gives T_G ≅ T_Ω on small-étale
additive-group sheaves of height max(u,w), using the same monad-isomorphism components. -/
def fieldGodementPrescribedPointEndofunctorIso :
    (smallEtaleGodementMonad.{u, w} (Spec (.of k))).toFunctor ≅
      (fieldPrescribedPointMonad.{u, w} k Ω).toFunctor :=
  fieldGodementProductCollapseIso.{u, w} k ≪≫
    fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k have prescribed separable closure Ω, θ : T_G ≅ T_Ω be the Godement-to-point comparison,
and λ_Ω the prescribed point tensor pairing. For sheaves F,G,
λ_G(F,G)≫θ_{F⊗G}=(θ_F⊗θ_G)≫λ_Ω(F,G). The tensor products are the integer tensor coefficient
sheaves. -/
theorem fieldGodementPrescribedPointMonadIso_tensorPairing
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let e := fieldGodementPrescribedPointEndofunctorIso.{u, w} k Ω
    smallEtaleGodementTensorPairing.{u, w} (Spec (.of k)) F G ≫
        e.hom.app (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) =
      smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) (e.hom.app F) (e.hom.app G) ≫
        fieldPrescribedPointTensorPairing.{u, w} k Ω F G := by
  intro e
  let X := Spec (.of k)
  let a := fieldGodementProductCollapseIso.{u, w} k
  let b := fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω
  let T := smallEtaleTensorSheaf.{u, w} X F G
  have ha := fieldGodementCanonicalTensorPairing_comm.{u, w} k F G
  have hb := fieldCanonicalPrescribedPointMonadIso_tensorPairing.{u, w} k Ω F G
  have ht := smallEtaleTensorSheafMap_comp.{u, w} X
    (a.hom.app F) (b.hom.app F) (a.hom.app G) (b.hom.app G)
  change smallEtaleGodementTensorPairing.{u, w} X F G ≫ (a.hom.app T ≫ b.hom.app T) =
    smallEtaleTensorSheafMap.{u, w} X (a.hom.app F ≫ b.hom.app F) (a.hom.app G ≫ b.hom.app G) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ b.hom.app T) ha).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => smallEtaleTensorSheafMap.{u, w} X (a.hom.app F) (a.hom.app G) ≫
            f) hb).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ fieldPrescribedPointTensorPairing.{u, w} k Ω F G) ht)))))

end AlgebraicGeometry.Scheme.DerivedSections
