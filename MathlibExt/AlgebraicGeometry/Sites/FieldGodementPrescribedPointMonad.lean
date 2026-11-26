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
# The field Godement monad at a prescribed separable-closure point

Let k,Ω be fields of universe u with Ω a prescribed separable closure. On small-étale
additive-group sheaves of height max(u,w), let T_can be the monad of the canonical geometric
point over the unique spectrum point, and T_Ω the monad of Spec(Ω) → Spec(k).

The canonical-to-prescribed stalk and skyscraper comparisons give T_can ≅ T_Ω, preserving
units and multiplications. Composing with the field Godement product-collapse monad
isomorphism identifies the full field Godement monad with T_Ω.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- For a field k, the canonical geometric point at the unique topological point of Spec(k) has a
stalk–skyscraper adjunction. Its induced monad on additive-group small-étale sheaves of height
max(u,w) is fieldCanonicalPointMonad. Its endofunctor is stalk followed by skyscraper. -/
def fieldCanonicalPointMonad :
    Monad (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  ((fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction
    (A := AddCommGrpCat.{max u w})).toMonad

/-- Let Ω be a prescribed separable closure of a field k. The geometric point Spec(Ω) → Spec(k)
gives a stalk–skyscraper adjunction at coefficient height max(u,w). Its induced monad on the
same sheaf category is fieldPrescribedPointMonad. -/
def fieldPrescribedPointMonad :
    Monad (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (A := AddCommGrpCat.{max u w})).toMonad

/-- For a field k and prescribed separable closure Ω, the canonical-to-prescribed stalk and
skyscraper comparisons give an isomorphism of their stalk–skyscraper endofunctors on
small-étale additive-group sheaves. This is the adjunction endofunctor comparison
fieldCanonicalPrescribedPointEndofunctorIso. -/
def fieldCanonicalPrescribedPointEndofunctorIso :
    (fieldCanonicalPointMonad.{u, w} k).toFunctor ≅
        (fieldPrescribedPointMonad.{u, w} k Ω).toFunctor :=
  Adjunction.comparisonEndofunctorIso
    (fieldCanonicalCommonStalkIso.{u, w} k Ω default).symm
    (fieldCanonicalSkyscraperIso.{u, w} k Ω default)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let T be the canonical point monad, S the prescribed Ω-point monad, and θ their endofunctor
comparison. For a small-étale sheaf Q, η_T,Q≫θ_Q=η_S,Q. Thus the canonical and prescribed
adjunction units correspond under the fixed comparison. -/
theorem fieldCanonicalPrescribedPointEndofunctorIso_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := fieldCanonicalPointMonad.{u, w} k
    let S := fieldPrescribedPointMonad.{u, w} k Ω
    let e := fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω
    T.η.app Q ≫ e.hom.app Q = S.η.app Q := by
  intro T S e
  let p := fieldGodementCanonicalPoint.{u, w} k
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let s := fieldCanonicalSkyscraperIso.{u, w} k Ω default
  let a := fieldCanonicalSkyscraperAdjunction.{u, w} k Ω default
  let b := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let d := (fieldCanonicalCommonStalkIso.{u, w} k Ω default).inv.app Q
  have h := fieldCanonicalSkyscraperIso_unit.{u, w} k Ω default Q
  exact (Category.assoc ((fieldCanonicalPointMonad.{u, w} k).η.app Q)
    (p.skyscraperSheafFunctor.map d) (s.hom.app (q.sheafFiber.obj Q))).symm.trans h

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field k and prescribed separable closure Ω, let T,S be the canonical and prescribed
point monads and θ their endofunctor isomorphism. Then μ_T,Q≫θ_Q=(T(θ_Q)≫θ_{S(Q)})≫μ_S,Q for
every sheaf Q. The point counit comparisons give this multiplication compatibility. -/
theorem fieldCanonicalPrescribedPointEndofunctorIso_mul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := fieldCanonicalPointMonad.{u, w} k
    let S := fieldPrescribedPointMonad.{u, w} k Ω
    let e := fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω
    T.μ.app Q ≫ e.hom.app Q =
      (T.map (e.hom.app Q) ≫ e.hom.app (S.obj Q)) ≫ S.μ.app Q := by
  intro T S e
  let p := fieldGodementCanonicalPoint.{u, w} k
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let b := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  exact Adjunction.comparisonEndofunctorIso_mul a b
    (fieldCanonicalCommonStalkIso.{u, w} k Ω default).symm
    (fieldCanonicalSkyscraperIso.{u, w} k Ω default)
    (fun M => fieldCanonicalSkyscraperIso_counit.{u, w} k Ω default M) Q

/-- Let k have prescribed separable closure Ω. The canonical-to-prescribed point endofunctor
isomorphism, with its unit and multiplication equations, defines fieldCanonicalPointMonad(k) ≅
fieldPrescribedPointMonad(k,Ω). -/
def fieldCanonicalPrescribedPointMonadIso :
    fieldCanonicalPointMonad.{u, w} k ≅ fieldPrescribedPointMonad.{u, w} k Ω :=
  MonadIso.mk (fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω)
    (fieldCanonicalPrescribedPointEndofunctorIso_unit.{u, w} k Ω)
    (fieldCanonicalPrescribedPointEndofunctorIso_mul.{u, w} k Ω)

/-- For a field k and prescribed separable closure Ω, compose the Godement-to-canonical-point
monad isomorphism with the canonical-to-prescribed point isomorphism. This gives
smallEtaleGodementMonad(Spec k) ≅ fieldPrescribedPointMonad(k,Ω) on additive-group sheaves of
height max(u,w). -/
def fieldGodementPrescribedPointMonadIso :
    smallEtaleGodementMonad.{u, w} (Spec (.of k)) ≅
      fieldPrescribedPointMonad.{u, w} k Ω :=
  fieldGodementCanonicalPointMonadIso.{u, w} k ≪≫
    fieldCanonicalPrescribedPointMonadIso.{u, w} k Ω

end AlgebraicGeometry.Scheme.DerivedSections
