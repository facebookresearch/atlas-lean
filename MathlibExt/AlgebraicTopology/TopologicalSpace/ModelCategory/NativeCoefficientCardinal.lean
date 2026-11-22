/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeBoundedSources
public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingSmash
public import MathlibExt.Topology.Category.PointedCGWH.SphereOne

/-!
# Actual native finite coefficient carrier bounds

The original native smash quotient is a surjection from its actual selected
Cartesian product. The actual realization/costar and circle isomorphisms
retain their original carriers. These maps bound the coefficient carriers by
continuum and derive source preservation at the same realized cardinal.
No cardinal or source-preservation dictionary for native coefficients enters.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open scoped Simplicial Cardinal

namespace CGWH.CoefficientCardinal

/-- The direct native realization retains the original finite realization carrier. -/
theorem finiteRealization_mk_le (T : SSet.{v}) [T.Finite] :
    #↥(SSet.toCGWH.{u, v}.obj T) ≤ Cardinal.continuum := by
  change #↥(SSet.toTop.obj T) ≤ Cardinal.continuum
  exact mk_realizedFinite_le T

end CGWH.CoefficientCardinal

namespace PointedCGWH.CoefficientCardinal

/-- Freely pointing the actual finite realization preserves the continuum bound. -/
theorem finiteCostar_mk_le (T : SSet.{v}) [T.Finite] :
    #↥(((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.obj T)).right) ≤
      Cardinal.continuum := by
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} :=
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  let e : SSet.toCGWH.{u, v}.obj ((Δ[0] : SSet.{v}) ⨿ T) ≅
      ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.obj T)).right :=
    (asIso (coprodComparison SSet.toCGWH (Δ[0] : SSet.{v}) T)).symm ≪≫
      coprod.mapIso e₀ (Iso.refl _)
  rw [← Cardinal.mk_congr (CGWH.homeoOfIso e).toEquiv]
  exact CGWH.CoefficientCardinal.finiteRealization_mk_le _

/-- The actual native smash carrier is bounded by its two original carriers. -/
theorem smash_mk_le (A C : PointedCGWH.{u, v}) :
    #↥((A ⊗ C).right) ≤ #↥A.right * #↥C.right := by
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A C
  have hq : Function.Surjective (ConcreteCategory.hom p.2.1.inl) :=
    (PointedCGWH.smashQuotient_isQuotientMap A C).surjective
  calc #↥((A ⊗ C).right)
      ≤ #↥(A.right ⊗ C.right : CGWH.{u, v}) := Cardinal.mk_le_of_surjective hq
    _ = #(A.right × C.right) := Cardinal.mk_congr (CGWH.tensorEquivProd A.right C.right)
    _ = #↥A.right * #↥C.right := by simp

/-- Actual smash products of bounded native coefficients remain bounded. -/
theorem smash_mk_le_continuum (A C : PointedCGWH.{u, v})
    (hA : #↥A.right ≤ Cardinal.continuum) (hC : #↥C.right ≤ Cardinal.continuum) :
    #↥((A ⊗ C).right) ≤ Cardinal.continuum :=
  (smash_mk_le A C).trans ((mul_le_mul' hA hC).trans
    (Cardinal.mul_eq_self Cardinal.aleph0_le_continuum).le)

/-- The original native one-sphere has its finite circle realization carrier bound. -/
theorem sphereOne_mk_le :
    #↥(PointedCGWH.sphereOne.{u, v}.right) ≤ Cardinal.continuum := by
  let _ : SSet.pointedCircle.{v}.right.Finite := by
    change (SSet.boundary.{v} 1).quotient.Finite
    infer_instance
  let e : (SSet.pointedToCGWH.{u, v}.obj SSet.pointedCircle).right ≅
      PointedCGWH.sphereOne.{u, v}.right :=
    PointedCGWH.pointedToCGWH.mapIso PointedCGWH.pointedCircleRealizationIsoSphereOne
  rw [← Cardinal.mk_congr (CGWH.homeoOfIso e).toEquiv]
  change #↥(SSet.toCGWH.{u, v}.obj SSet.pointedCircle.right) ≤ Cardinal.continuum
  exact CGWH.CoefficientCardinal.finiteRealization_mk_le _

/-- The actual smash unit is the freely pointed native zero simplex. -/
theorem unit_mk_le :
    #↥((𝟙_ PointedCGWH.{u, v}).right) ≤ Cardinal.continuum := by
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅ CGWH.point.{u, v} :=
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
  let e : ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.obj (Δ[0] : SSet.{v}))).right ≅
      ((Under.costar CGWH.point.{u, v}).obj CGWH.point).right :=
    PointedCGWH.pointedToCGWH.mapIso ((Under.costar CGWH.point.{u, v}).mapIso e₀)
  change #↥(((Under.costar CGWH.point.{u, v}).obj CGWH.point).right) ≤ _
  rw [← Cardinal.mk_congr (CGWH.homeoOfIso e).toEquiv]
  exact finiteCostar_mk_le (Δ[0] : SSet.{v})

/-- A genuine continuum bound is strictly below the literal original generator cardinal. -/
theorem carrier_bound (A : PointedCGWH.{u, v})
    (hA : #↥A.right ≤ Cardinal.continuum) :
    HasCardinalLT ↥(CGWH.cgwhToTop.obj A.right) realizedGeneratorCardinal.{v} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  change #↥A.right < Order.succ Cardinal.continuum
  exact hA.trans_lt (Order.lt_succ _)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Actual finite smash coefficients preserve the original native closed continuous chain. -/
theorem smash_preservesClosedColimit (A C : PointedCGWH.{u, v})
    (hA : #↥A.right ≤ Cardinal.continuum) (hC : #↥C.right ≤ Cardinal.continuum)
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj (Opposite.op (A ⊗ C))) :=
  PointedCGWH.BoundedSource.preservesClosedColimit (A ⊗ C)
    (carrier_bound _ (smash_mk_le_continuum A C hA hC)) E hE

/-- Every actual freely pointed finite realization preserves that same original chain. -/
theorem finiteCostar_preservesClosedColimit (T : SSet.{v}) [T.Finite]
    (E : realizedGeneratorCardinal.{v}.ord.ToType ⥤ PointedCGWH.{u, v})
    [E.IsWellOrderContinuous]
    (hE : ∀ ⦃a b⦄ (φ : a ⟶ b), IsClosedEmbedding (ConcreteCategory.hom (E.map φ).right)) :
    PreservesColimit E (coyoneda.obj
      (Opposite.op ((Under.costar CGWH.point.{u, v}).obj (SSet.toCGWH.obj T)))) :=
  PointedCGWH.BoundedSource.preservesClosedColimit _
    (carrier_bound _ (finiteCostar_mk_le T)) E hE

end PointedCGWH.CoefficientCardinal
