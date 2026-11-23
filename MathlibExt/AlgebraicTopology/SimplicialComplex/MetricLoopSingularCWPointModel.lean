/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopCWDomination
public import MathlibExt.Topology.CWComplex.SingularCWType
import MathlibExt.Topology.Category.TopCat.RealizedBasedWhitehead
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularHomotopyRelAtPoint
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyRelAtVertex
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# The original singular CW point model of raw metric loops

The original loop domination data instantiates the neutral singular counit
construction, retaining the inverse, point laws and both complete relative families.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology Set Function
open scoped Simplicial TopCat.modelCategory SSet.modelCategoryQuillen unitInterval

universe u

namespace MetricLoopSingularCWPointModelConstruction

/-- The full raw metric-loop application has only the original complex and vertex as inputs. -/
private theorem metric_loop_singular_CW_point_model {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let a : PreAbstractSimplicialComplex.MetricRealization P :=
      PreAbstractSimplicialComplex.Realization.toMetric P
        (PreAbstractSimplicialComplex.Realization.vertex P v hv)
    let M := Path a a
    let e : M := Path.refl a
    let S : SSet.{u} := TopCat.toSSet.obj (TopCat.of M)
    let C₀ : TopCat.{u} := SSet.toTop.obj S
    let c₀ : C₀ := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
    let cw := SSet.realizationClassicalCWComplex S
    letI : Topology.CWComplex (Set.univ : Set C₀) := cw
    T2Space C₀ ∧
      (∃ j : Topology.CWComplex.cell (Set.univ : Set C₀) 0,
        ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = c₀) ∧
      ∃ R : C(M, C₀),
        R e = c₀ ∧ sSetTopAdj.counit.app (TopCat.of M) c₀ = e ∧
        ∃ HL : ContinuousMap.HomotopyRel
            (R.comp (sSetTopAdj.counit.app (TopCat.of M)).hom) (ContinuousMap.id C₀) {c₀},
          ∃ HR : ContinuousMap.HomotopyRel
              ((sSetTopAdj.counit.app (TopCat.of M)).hom.comp R) (ContinuousMap.id M) {e},
            (∀ t : unitInterval, HL (t, c₀) = c₀) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ E : ContinuousMap.HomotopyEquiv C₀ M,
              E.toFun = (sSetTopAdj.counit.app (TopCat.of M)).hom ∧ E.invFun = R := by
  let a : PreAbstractSimplicialComplex.MetricRealization P :=
    PreAbstractSimplicialComplex.Realization.toMetric P
      (PreAbstractSimplicialComplex.Realization.vertex P v hv)
  let M := Path a a
  let e : M := Path.refl a
  obtain ⟨J, Q, _, v0, hv0, _, _, _, _, _, hdata⟩ :=
    PreAbstractSimplicialComplex.metricLoopCWDomination P v hv
  obtain ⟨p, q, hp, hq, Hdom, _, _⟩ := hdata
  let p' : TopCat.of M ⟶ TopCat.of Q.Realization := TopCat.ofHom p
  let q' : TopCat.of Q.Realization ⟶ TopCat.of M := TopCat.ofHom q
  let Hdom' : ContinuousMap.HomotopyRel (p' ≫ q').hom (TopCat.Hom.hom (𝟙 (TopCat.of M))) {e} :=
    Hdom.cast (by simp only [p', q', TopCat.hom_comp, TopCat.hom_ofHom])
      (TopCat.hom_id (X := TopCat.of M)).symm
  obtain ⟨hC, hzero, R, hRpoint, hepsilon, HL, HR, hLfixed, hRfixed, E, hEto, hEinv⟩ :=
    Topology.CWComplex.SingularCWType.singularCWPointModelOfDomination Q v0 hv0 (TopCat.of M) e p' q' hp hq Hdom'
  let HL' := HL.cast (TopCat.hom_comp _ _) TopCat.hom_id
  let HR' := HR.cast (TopCat.hom_comp _ _) TopCat.hom_id
  exact ⟨hC, hzero, R.hom, hRpoint, hepsilon, HL', HR', hLfixed, hRfixed, E, hEto, hEinv⟩

end MetricLoopSingularCWPointModelConstruction

public section

namespace PreAbstractSimplicialComplex

/-- Construct the actual singular CW point model and based inverse
of the original raw-loop counit. -/
theorem metricLoopSingularCWPointModel {V : Type u}
    (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let a : PreAbstractSimplicialComplex.MetricRealization P :=
      PreAbstractSimplicialComplex.Realization.toMetric P
        (PreAbstractSimplicialComplex.Realization.vertex P v hv)
    let M := Path a a
    let e : M := Path.refl a
    let S : SSet.{u} := TopCat.toSSet.obj (TopCat.of M)
    let C₀ : TopCat.{u} := SSet.toTop.obj S
    let c₀ : C₀ := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
    let cw := SSet.realizationClassicalCWComplex S
    letI : Topology.CWComplex (Set.univ : Set C₀) := cw
    T2Space C₀ ∧
      (∃ j : Topology.CWComplex.cell (Set.univ : Set C₀) 0,
        ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = c₀) ∧
      ∃ R : C(M, C₀),
        R e = c₀ ∧ sSetTopAdj.counit.app (TopCat.of M) c₀ = e ∧
        ∃ HL : ContinuousMap.HomotopyRel
            (R.comp (sSetTopAdj.counit.app (TopCat.of M)).hom) (ContinuousMap.id C₀) {c₀},
          ∃ HR : ContinuousMap.HomotopyRel
              ((sSetTopAdj.counit.app (TopCat.of M)).hom.comp R) (ContinuousMap.id M) {e},
            (∀ t : unitInterval, HL (t, c₀) = c₀) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ E : ContinuousMap.HomotopyEquiv C₀ M,
              E.toFun = (sSetTopAdj.counit.app (TopCat.of M)).hom ∧ E.invFun = R := by
  exact MetricLoopSingularCWPointModelConstruction.metric_loop_singular_CW_point_model P v hv

end PreAbstractSimplicialComplex
