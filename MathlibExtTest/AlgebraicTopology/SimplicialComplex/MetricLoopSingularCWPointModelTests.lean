/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopSingularCWPointModel

noncomputable section
set_option autoImplicit false
open CategoryTheory Topology Function Set
open scoped unitInterval Simplicial
universe u
open PreAbstractSimplicialComplex

#check PreAbstractSimplicialComplex.metricLoopSingularCWPointModel
#print axioms PreAbstractSimplicialComplex.metricLoopSingularCWPointModel

private abbrev point {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : MetricRealization P :=
  Realization.toMetric P (Realization.vertex P v hv)

private abbrev loops {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) := Path (point P v hv) (point P v hv)

private abbrev sing {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : SSet.{u} :=
  TopCat.toSSet.obj (TopCat.of (loops P v hv))

private abbrev carrier {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) := SSet.toTop.obj (sing P v hv)

private abbrev zero {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : carrier P v hv :=
  SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm (Path.refl (point P v hv)))

private abbrev counit {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : carrier P v hv ⟶ TopCat.of (loops P v hv) :=
  sSetTopAdj.counit.app (TopCat.of (loops P v hv))

-- The actual inverse preserves the literal singular vertex, and the ORIGINAL counit returns e.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ R : C(loops P v hv, carrier P v hv),
      R (Path.refl (point P v hv)) = zero P v hv ∧
      counit P v hv (zero P v hv) = Path.refl (point P v hv) := by
  obtain ⟨_, _, R, hR, hε, _, _, _, _, _, _, _⟩ := metricLoopSingularCWPointModel P v hv
  exact ⟨R, hR, hε⟩

-- The whole literal singular realization is Hausdorff and has the actual canonical zero cell.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    T2Space (carrier P v hv) ∧
      ∃ j : Topology.CWComplex.cell (Set.univ : Set (carrier P v hv)) 0,
        ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = zero P v hv := by
  obtain ⟨hT2, hzero, _, _, _, _, _, _, _, _, _, _⟩ := metricLoopSingularCWPointModel P v hv
  exact ⟨hT2, hzero⟩

-- BOTH whole endpoint maps of the left inverse family are the stated R∘epsilon and identity.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ R : C(loops P v hv, carrier P v hv),
      ∃ HL : ContinuousMap.HomotopyRel (R.comp (counit P v hv).hom)
          (ContinuousMap.id (carrier P v hv)) {zero P v hv},
        HL.toHomotopy.curry 0 = R.comp (counit P v hv).hom ∧
        HL.toHomotopy.curry 1 = ContinuousMap.id (carrier P v hv) := by
  obtain ⟨_, _, R, _, _, HL, _, _, _, _, _, _⟩ := metricLoopSingularCWPointModel P v hv
  exact ⟨R, HL, HL.toHomotopy.curry_zero, HL.toHomotopy.curry_one⟩

-- BOTH whole endpoint maps of the right inverse family are epsilon∘R and identity on ALL loops.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ R : C(loops P v hv, carrier P v hv),
      ∃ HR : ContinuousMap.HomotopyRel ((counit P v hv).hom.comp R)
          (ContinuousMap.id (loops P v hv)) {Path.refl (point P v hv)},
        HR.toHomotopy.curry 0 = (counit P v hv).hom.comp R ∧
        HR.toHomotopy.curry 1 = ContinuousMap.id (loops P v hv) := by
  obtain ⟨_, _, R, _, _, _, HR, _, _, _, _, _⟩ := metricLoopSingularCWPointModel P v hv
  exact ⟨R, HR, HR.toHomotopy.curry_zero, HR.toHomotopy.curry_one⟩

-- The actual families fix c0 and the WHOLE constant Path at all times and every inner parameter.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ R : C(loops P v hv, carrier P v hv),
      ∃ HL : ContinuousMap.HomotopyRel (R.comp (counit P v hv).hom)
          (ContinuousMap.id (carrier P v hv)) {zero P v hv},
        ∃ HR : ContinuousMap.HomotopyRel ((counit P v hv).hom.comp R)
            (ContinuousMap.id (loops P v hv)) {Path.refl (point P v hv)},
          (∀ t : unitInterval, HL (t, zero P v hv) = zero P v hv) ∧
          (∀ t : unitInterval, HR (t, Path.refl (point P v hv)) = Path.refl (point P v hv)) ∧
          ∀ t r : unitInterval, HR (t, Path.refl (point P v hv)) r = point P v hv := by
  obtain ⟨_, _, R, _, _, HL, HR, hL, hR, _, _, _⟩ := metricLoopSingularCWPointModel P v hv
  refine ⟨R, HL, HR, hL, hR, ?_⟩
  intro t r
  exact congrArg (fun γ : loops P v hv => γ r) (hR t)

-- The ordinary equivalence uses the ORIGINAL counit and the SAME R, including their point laws.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ (R : C(loops P v hv, carrier P v hv))
      (E : ContinuousMap.HomotopyEquiv (carrier P v hv) (loops P v hv)),
      E.toFun = (counit P v hv).hom ∧ E.invFun = R ∧
      E.toFun (zero P v hv) = Path.refl (point P v hv) ∧
      E.invFun (Path.refl (point P v hv)) = zero P v hv := by
  obtain ⟨_, _, R, hR, hε, _, _, _, _, E, hEto, hEinv⟩ := metricLoopSingularCWPointModel P v hv
  refine ⟨R, E, hEto, hEinv, ?_, ?_⟩
  · rw [hEto]
    exact hε
  · rw [hEinv]
    exact hR
