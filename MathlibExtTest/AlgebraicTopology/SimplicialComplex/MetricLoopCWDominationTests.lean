/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopCWDomination

noncomputable section
set_option autoImplicit false
open Topology Function Set
open scoped unitInterval
universe u
open PreAbstractSimplicialComplex

#check PreAbstractSimplicialComplex.metricLoopCWDomination
#print axioms PreAbstractSimplicialComplex.metricLoopCWDomination

private abbrev point {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : MetricRealization P :=
  Realization.toMetric P (Realization.vertex P v hv)

private abbrev loops {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) := Path (point P v hv) (point P v hv)

-- The actual cover has the actual nerve law; at e only its literal singleton is active.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J)
      (W : J → Set (loops P v hv)) (v0 : J),
      (∀ j : J, IsOpen (W j) ∧ (W j).Nonempty) ∧ LocallyFinite W ∧
      (⋃ j : J, W j = Set.univ) ∧
      (∀ s : Finset J, s ∈ Q ↔ s.Nonempty ∧ ∃ γ : loops P v hv, ∀ j ∈ s, γ ∈ W j) ∧
      ∀ s : Finset J, s.Nonempty → ((∀ j ∈ s, e ∈ W j) ↔ s = {v0}) := by
  let e : loops P v hv := Path.refl (point P v hv)
  obtain ⟨J, Q, W, v0, _, hnerve, hopen, hcover, hfinite, hunique, _⟩ :=
    metricLoopCWDomination P v hv
  refine ⟨J, Q, W, v0, hopen, hfinite, hcover, hnerve, ?_⟩
  intro s hs
  constructor
  · intro hmem
    apply Finset.Subset.antisymm
    · intro j hj
      exact Finset.mem_singleton.mpr ((hunique j).mp (hmem j hj))
    · obtain ⟨j, hj⟩ := hs
      have hj0 : j = v0 := (hunique j).mp (hmem j hj)
      simpa only [hj0, Finset.singleton_subset_iff] using hj
  · intro heq
    subst s
    intro j hj
    have hj0 : j = v0 := Finset.mem_singleton.mp hj
    subst j
    exact (hunique v0).mpr rfl

-- Both constructed continuous maps preserve the specified points, so their composition fixes e.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J) (v0 : J) (hv0 : {v0} ∈ Q)
      (p : C(loops P v hv, Q.Realization)) (q : C(Q.Realization, loops P v hv)),
      p e = Realization.vertex Q v0 hv0 ∧ q (Realization.vertex Q v0 hv0) = e ∧
      (q.comp p) e = e := by
  let e : loops P v hv := Path.refl (point P v hv)
  obtain ⟨J, Q, _, v0, hv0, _, _, _, _, _, hdata⟩ := metricLoopCWDomination P v hv
  obtain ⟨p, q, hpe, hqe, _, _, _⟩ := hdata
  refine ⟨J, Q, v0, hv0, p, q, hpe, hqe, ?_⟩
  change q (p e) = e
  rw [hpe]
  exact hqe

-- The image of e is the actual canonical CW zero cell at every zero-dimensional coordinate.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J)
      (p : C(loops P v hv, Q.Realization))
      (j : Topology.CWComplex.cell (Set.univ : Set Q.Realization) 0),
      ∀ x : Fin 0 → ℝ, Topology.CWComplex.map 0 j x = p e := by
  obtain ⟨J, Q, _, _, _, _, _, _, _, _, hdata⟩ := metricLoopCWDomination P v hv
  obtain ⟨p, _, hpe, _, _, _, j, hj⟩ := hdata
  refine ⟨J, Q, p, j, ?_⟩
  intro x
  exact (hj x).trans hpe.symm

-- The actual whole initial map is q∘p, on all loop components.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J)
      (p : C(loops P v hv, Q.Realization)) (q : C(Q.Realization, loops P v hv)),
      ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id (loops P v hv)) ({e} : Set (loops P v hv)),
        H.toHomotopy.curry 0 = q.comp p := by
  obtain ⟨J, Q, _, _, _, _, _, _, _, _, hdata⟩ := metricLoopCWDomination P v hv
  obtain ⟨p, q, _, _, H, _, _⟩ := hdata
  exact ⟨J, Q, p, q, H, H.toHomotopy.curry_zero⟩

-- The actual whole final map is the identity on the original raw Path carrier.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J)
      (p : C(loops P v hv, Q.Realization)) (q : C(Q.Realization, loops P v hv)),
      ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id (loops P v hv)) ({e} : Set (loops P v hv)),
        H.toHomotopy.curry 1 = ContinuousMap.id (loops P v hv) := by
  obtain ⟨J, Q, _, _, _, _, _, _, _, _, hdata⟩ := metricLoopCWDomination P v hv
  obtain ⟨p, q, _, _, H, _, _⟩ := hdata
  exact ⟨J, Q, p, q, H, H.toHomotopy.curry_one⟩

-- The independently specified constant loop is fixed as a WHOLE Path and at every inner parameter.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ (J : Type u) (Q : PreAbstractSimplicialComplex J)
      (p : C(loops P v hv, Q.Realization)) (q : C(Q.Realization, loops P v hv)),
      ∃ H : ContinuousMap.HomotopyRel (q.comp p) (ContinuousMap.id (loops P v hv)) ({e} : Set (loops P v hv)),
        (∀ t : unitInterval, H (t, e) = e) ∧
        ∀ t r : unitInterval, H (t, e) r = point P v hv := by
  obtain ⟨J, Q, _, _, _, _, _, _, _, _, hdata⟩ := metricLoopCWDomination P v hv
  obtain ⟨p, q, _, _, H, hfixed, _⟩ := hdata
  refine ⟨J, Q, p, q, H, hfixed, ?_⟩
  intro t r
  exact congrArg (fun γ : loops P v hv => γ r) (hfixed t)
