/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.CanonicalPointClosureJoin
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementTensorPairing

/-!
# Actual field Godement product collapse

The real singleton product projection collapses the Godement family only
after the canonical geometric point is retained as its original actual term.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k : Type u) [Field k]

/-- The original canonical geometric point at the actual unique point of Spec k. -/
abbrev fieldGodementCanonicalPoint :=
  smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) default)

/-- The actual product projection identifies each Godement object with its original canonical-point
skyscraper term. -/
def fieldGodementProductCollapseApp
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodement.{u, w} (Spec (.of k))).obj Q ≅
      ((fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w})).obj
          (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber
            (A := AddCommGrpCat.{max u w})).obj Q) :=
  productUniqueIso (fun x : Spec (.of k) =>
    (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).skyscraperSheafFunctor.obj
        ((smallEtaleGodementStalks.{u, w} (Spec (.of k))).obj Q x))

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the actual product collapse is the original skyscraper-product projection
square. -/
theorem fieldGodementProductCollapseApp_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (f : Q ⟶ Q') :
    (smallEtaleGodement.{u, w} (Spec (.of k))).map f ≫
        (fieldGodementProductCollapseApp.{u, w} k Q').hom =
      (fieldGodementProductCollapseApp.{u, w} k Q).hom ≫
        (((fieldGodementCanonicalPoint.{u, w} k).sheafFiber
          (A := AddCommGrpCat.{max u w})) ⋙
            (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor).map f :=
  smallEtaleGodementSkyscrapers_map_projection.{u, w} (Spec (.of k))
    ((smallEtaleGodementStalks.{u, w} (Spec (.of k))).map f) default

/-- The actual original Godement endofunctor is naturally the single canonical-point adjunction
endofunctor. -/
def fieldGodementProductCollapseIso :
    smallEtaleGodement.{u, w} (Spec (.of k)) ≅
      (fieldGodementCanonicalPoint.{u, w} k).sheafFiber ⋙
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor :=
  NatIso.ofComponents (fieldGodementProductCollapseApp.{u, w} k)
    (fun f => fieldGodementProductCollapseApp_naturality.{u, w} k f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product collapse carries the original Godement unit to the same canonical point
unit. -/
theorem fieldGodementProductCollapseIso_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementUnit.{u, w} (Spec (.of k))).app Q ≫
        (fieldGodementProductCollapseIso.{u, w} k).hom.app Q =
      (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.unit.app Q :=
  smallEtaleGodementUnit_projection.{u, w} (Spec (.of k)) Q default

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual family-adjunction counit has the original canonical point counit after the product
projection. -/
theorem fieldGodementCounit_default
    (M : Spec (.of k) → AddCommGrpCat.{max u w}) :
    ((smallEtaleGodementAdjunction.{u, w} (Spec (.of k))).counit.app M) default =
      (fieldGodementCanonicalPoint.{u, w} k).sheafFiber.map
        (Pi.π (fun y : Spec (.of k) =>
          (smallEtaleGeometricPointCommon.{u, w}
            (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) y)).skyscraperSheafFunctor.obj
                (M y)) default) ≫
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.counit.app
            (M default) := by
  let X := Spec (.of k)
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let p := fieldGodementCanonicalPoint.{u, w} k
  let a := p.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
  let π := Pi.π (fun y : X =>
    (smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X y)).skyscraperSheafFunctor.obj (M y)) default
  have h := adj.homEquiv_symm_id M
  have he := smallEtaleGodementAdjunction_homEquiv.{u, w} X (R.obj M) M
  have hc : (adj.counit.app M) default =
      (a.homEquiv _ _).symm π := by
    exact (congrArg (fun f => f default) h).symm.trans
      (congrArg (fun e => e.symm (𝟙 _) default) he)
  exact hc.trans (a.homEquiv_counit _ _ π)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product collapse preserves the original Godement monad multiplication. -/
theorem fieldGodementProductCollapseIso_mul
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let T := smallEtaleGodementMonad.{u, w} (Spec (.of k))
    let S := (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.toMonad
    let e := fieldGodementProductCollapseIso.{u, w} k
    T.μ.app Q ≫ e.hom.app Q =
      (T.map (e.hom.app Q) ≫ e.hom.app (S.obj Q)) ≫ S.μ.app Q := by
  intro T S e
  let X := Spec (.of k)
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let p := fieldGodementCanonicalPoint.{u, w} k
  let A := p.sheafFiber (A := AddCommGrpCat.{max u w})
  let B := p.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w})
  let M := L.obj Q
  have hp := smallEtaleGodementSkyscrapers_map_projection.{u, w} X
    ((smallEtaleGodementAdjunction.{u, w} X).counit.app M) default
  have hc := fieldGodementCounit_default.{u, w} k M
  have hn := fieldGodementProductCollapseApp_naturality.{u, w} k (e.hom.app Q)
  have hsn : S.μ.app Q = B.map (p.skyscraperSheafAdjunction.counit.app (A.obj Q)) := rfl
  change R.map ((smallEtaleGodementAdjunction.{u, w} X).counit.app M) ≫
      (fieldGodementProductCollapseApp.{u, w} k Q).hom = _
  have hbc := congrArg B.map hc
  have hstart := hp.trans (congrArg (fun f =>
    (fieldGodementProductCollapseApp.{u, w} k (T.obj Q)).hom ≫ f) hbc)
  have hsplit := (congrArg (fun f =>
    (fieldGodementProductCollapseApp.{u, w} k (T.obj Q)).hom ≫ f)
    (B.map_comp (A.map (e.hom.app Q)) (p.skyscraperSheafAdjunction.counit.app (A.obj Q)))).trans
      (Category.assoc _ _ _).symm
  have hend :=
      congrArg (fun f => f ≫ B.map (p.skyscraperSheafAdjunction.counit.app (A.obj Q))) hn.symm
  exact hstart.trans (hsplit.trans hend)

/-- The actual original Godement monad is isomorphic to its canonical one-point adjunction monad. -/
def fieldGodementCanonicalPointMonadIso :
    smallEtaleGodementMonad.{u, w} (Spec (.of k)) ≅
      (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.toMonad :=
  MonadIso.mk (fieldGodementProductCollapseIso.{u, w} k)
    (fieldGodementProductCollapseIso_unit.{u, w} k)
    (fieldGodementProductCollapseIso_mul.{u, w} k)

end AlgebraicGeometry.Scheme.DerivedSections
