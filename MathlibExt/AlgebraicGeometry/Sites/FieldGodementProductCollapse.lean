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
# Collapsing the field Godement product to its unique canonical point

Let k be a field. Its spectrum has one topological point p₀, equipped with the canonical
geometric point obtained from the residue-field separable closure. For additive-group sheaves
of height max(u,w), the Godement endofunctor is the product of the point skyscrapers of their
stalks.

Projection to p₀ is therefore a natural isomorphism from the Godement endofunctor to the
canonical stalk–skyscraper composition. It preserves the adjunction unit and multiplication,
giving an isomorphism of the corresponding monads.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k : Type u) [Field k]

/-- For a field k, take the canonical geometric morphism over the unique topological point p₀ of
Spec(k), using its residue-field separable closure. Its common-height small-étale geometric
point is fieldGodementCanonicalPoint, with additive-group coefficients at max(u,w). -/
abbrev fieldGodementCanonicalPoint :=
  smallEtaleGeometricPointCommon.{u, w}
    (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) default)

/-- Let k be a field and Q a small-étale additive-group sheaf of height max(u,w). Its Godement
object Π_{y∈Spec(k)} x_{y*}x_y^*Q is isomorphic to x_{p₀*}x_{p₀}^*Q by the product projection
at the unique topological point p₀. The canonical geometric point at that same p₀ is retained. -/
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
/-- For a field k and a sheaf map f : Q → Q′, let T_G be Godement and T_p the canonical point
endofunctor. The product-collapse maps θ satisfy T_G(f)≫θ_Q′=θ_Q≫T_p(f). These are maps of the
same small-étale sheaves at coefficient height max(u,w). -/
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

/-- For a field k, projection from the Godement product to its unique topological-point component
gives a natural isomorphism T_G ≅ x_{p₀}^*⋙x_{p₀*} on small-étale additive-group sheaves of
height max(u,w). Its component at Q is fieldGodementProductCollapseApp(Q). -/
def fieldGodementProductCollapseIso :
    smallEtaleGodement.{u, w} (Spec (.of k)) ≅
      (fieldGodementCanonicalPoint.{u, w} k).sheafFiber ⋙
        (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafFunctor :=
  NatIso.ofComponents (fieldGodementProductCollapseApp.{u, w} k)
    (fun f => fieldGodementProductCollapseApp_naturality.{u, w} k f)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k be a field, θ : T_G ≅ T_p the canonical-point product collapse, and Q a small-étale
additive-group sheaf. Then η_G,Q≫θ_Q=η_p,Q, where η_G is the Godement unit and η_p the
canonical stalk–skyscraper adjunction unit. -/
theorem fieldGodementProductCollapseIso_unit
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementUnit.{u, w} (Spec (.of k))).app Q ≫
        (fieldGodementProductCollapseIso.{u, w} k).hom.app Q =
      (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.unit.app Q :=
  smallEtaleGodementUnit_projection.{u, w} (Spec (.of k)) Q default

set_option backward.isDefEq.respectTransparency.types false in
/-- For a coefficient family M_y indexed by the topological points of Spec(k), let π_M be
projection of Π_y x_{y*}M_y to the unique component p₀. The family-adjunction counit at p₀
equals x_{p₀}^*(π_M) followed by the point counit ε_{M_{p₀}}. This identifies the counit
component used in multiplication. -/
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
/-- Let T be the field Godement monad, S the canonical point monad, and θ their product-collapse
endofunctor isomorphism. For every sheaf Q, μ_T,Q≫θ_Q=(T(θ_Q)≫θ_{S(Q)})≫μ_S,Q. This is the
monad multiplication equation for the same product projection. -/
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

/-- For a field k, the natural singleton-product collapse, together with its unit and
multiplication equations, defines an isomorphism from smallEtaleGodementMonad(Spec k) to the
monad of the canonical geometric-point stalk–skyscraper adjunction. The coefficients have
height max(u,w). -/
def fieldGodementCanonicalPointMonadIso :
    smallEtaleGodementMonad.{u, w} (Spec (.of k)) ≅
      (fieldGodementCanonicalPoint.{u, w} k).skyscraperSheafAdjunction.toMonad :=
  MonadIso.mk (fieldGodementProductCollapseIso.{u, w} k)
    (fieldGodementProductCollapseIso_unit.{u, w} k)
    (fieldGodementProductCollapseIso_mul.{u, w} k)

end AlgebraicGeometry.Scheme.DerivedSections
