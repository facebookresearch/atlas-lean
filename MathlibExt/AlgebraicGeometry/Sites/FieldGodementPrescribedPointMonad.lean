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
# The actual Godement monad at the prescribed field point

The checked canonical closure point, stalk and skyscraper comparisons preserve
the original unit and counit. They identify the actual one-point monads.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual one canonical-point monad, stored on the original sheaf category. -/
def fieldCanonicalPointMonad :
    Monad (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  ((fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction
    (A := AddCommGrpCat.{max u w})).toMonad

/-- The actual prescribed Ω point monad, stored on the same original sheaf category. -/
def fieldPrescribedPointMonad :
    Monad (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :=
  ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (A := AddCommGrpCat.{max u w})).toMonad

/-- The genuine point stalk/skyscraper comparisons give the actual canonical-to-prescribed
endofunctor iso. -/
def fieldCanonicalPrescribedPointEndofunctorIso :
    (fieldCanonicalPointMonad.{u, w} k).toFunctor ≅
        (fieldPrescribedPointMonad.{u, w} k Ω).toFunctor :=
  Adjunction.comparisonEndofunctorIso
    (fieldCanonicalCommonStalkIso.{u, w} k Ω default).symm
    (fieldCanonicalSkyscraperIso.{u, w} k Ω default)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual endofunctor comparison preserves the original canonical and prescribed monad
units. -/
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
/-- The genuine original evaluation counits make the actual point monad multiplications commute. -/
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

/-- The actual canonical point monad is isomorphic to the prescribed Ω point monad through its
genuine adjunction comparisons. -/
def fieldCanonicalPrescribedPointMonadIso :
    fieldCanonicalPointMonad.{u, w} k ≅ fieldPrescribedPointMonad.{u, w} k Ω :=
  MonadIso.mk (fieldCanonicalPrescribedPointEndofunctorIso.{u, w} k Ω)
    (fieldCanonicalPrescribedPointEndofunctorIso_unit.{u, w} k Ω)
    (fieldCanonicalPrescribedPointEndofunctorIso_mul.{u, w} k Ω)

/-- The original full Godement monad is isomorphic to the original prescribed-point monad. -/
def fieldGodementPrescribedPointMonadIso :
    smallEtaleGodementMonad.{u, w} (Spec (.of k)) ≅
      fieldPrescribedPointMonad.{u, w} k Ω :=
  fieldGodementCanonicalPointMonadIso.{u, w} k ≪≫
    fieldCanonicalPrescribedPointMonadIso.{u, w} k Ω

end AlgebraicGeometry.Scheme.DerivedSections
