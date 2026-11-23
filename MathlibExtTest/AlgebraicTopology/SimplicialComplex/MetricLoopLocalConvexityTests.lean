/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopLocalConvexity

noncomputable section
set_option autoImplicit false
open CategoryTheory Topology Function Set
open scoped unitInterval NNReal
universe u
open PreAbstractSimplicialComplex

#check PreAbstractSimplicialComplex.metricLoopLocalConvexity
#print axioms PreAbstractSimplicialComplex.metricLoopLocalConvexity

private abbrev point {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) : MetricRealization P :=
  Realization.toMetric P (Realization.vertex P v hv)

private abbrev loops {V : Type u} (P : PreAbstractSimplicialComplex V)
    (v : V) (hv : {v} ∈ P) := Path (point P v hv) (point P v hv)

-- The metric is on the entire actual path carrier and preserves its old topology.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ d : MetricSpace (loops P v hv),
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace (loops P v hv)) := by
  obtain ⟨d, hd, _, _, _, _, _, _, _⟩ := metricLoopLocalConvexity P v hv
  exact ⟨d, hd⟩

-- The literal original constant-loop point is closed in the raw compact-open topology.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    IsClosed ({Path.refl (point P v hv)} : Set (loops P v hv)) := by
  obtain ⟨_, _, _, _, _, _, _, _, hclosed⟩ := metricLoopLocalConvexity P v hv
  exact hclosed

-- Both outer endpoints are observed at EVERY inner path parameter.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ U : Set (loops P v hv × loops P v hv), IsOpen U ∧
      (∀ γ : loops P v hv, (γ, γ) ∈ U) ∧
      ∃ H : ContinuousMap.Homotopy
        (⟨fun p : U => p.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(U, loops P v hv))
        (⟨fun p : U => p.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(U, loops P v hv)),
        ∀ (p : U) (r : unitInterval),
          H (0, p) r = p.val.1 r ∧ H (1, p) r = p.val.2 r := by
  obtain ⟨_, _, U, hU, hdiag, H, _, _, _⟩ := metricLoopLocalConvexity P v hv
  refine ⟨U, hU, hdiag, H, ?_⟩
  intro p r
  exact ⟨congrArg (fun γ : loops P v hv => γ r) (H.apply_zero p),
    congrArg (fun γ : loops P v hv => γ r) (H.apply_one p)⟩

-- Diagonal fixedness includes every loop component and both parameter variables.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    ∃ U : Set (loops P v hv × loops P v hv), IsOpen U ∧
      (∀ γ : loops P v hv, (γ, γ) ∈ U) ∧
      ∃ H : ContinuousMap.Homotopy
        (⟨fun p : U => p.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(U, loops P v hv))
        (⟨fun p : U => p.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(U, loops P v hv)),
        ∀ (γ : loops P v hv) (hγ : (γ, γ) ∈ U) (s r : unitInterval),
          H (s, ⟨(γ, γ), hγ⟩) r = γ r := by
  obtain ⟨_, _, U, hU, hdiag, H, hfixed, _, _⟩ := metricLoopLocalConvexity P v hv
  refine ⟨U, hU, hdiag, H, ?_⟩
  intro γ hγ s r
  exact congrArg (fun δ : loops P v hv => δ r) (hfixed γ hγ s)

-- The independently specified constant loop is fixed as a WHOLE Path and pointwise.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P) :
    let e : loops P v hv := Path.refl (point P v hv)
    ∃ U : Set (loops P v hv × loops P v hv), IsOpen U ∧
      ∃ he : (e, e) ∈ U,
      ∃ H : ContinuousMap.Homotopy
        (⟨fun p : U => p.val.1, continuous_fst.comp continuous_subtype_val⟩ : C(U, loops P v hv))
        (⟨fun p : U => p.val.2, continuous_snd.comp continuous_subtype_val⟩ : C(U, loops P v hv)),
        (∀ s : unitInterval, H (s, ⟨(e, e), he⟩) = e) ∧
        ∀ s r : unitInterval, H (s, ⟨(e, e), he⟩) r = point P v hv := by
  let e : loops P v hv := Path.refl (point P v hv)
  obtain ⟨_, _, U, hU, hdiag, H, hfixed, _, _⟩ := metricLoopLocalConvexity P v hv
  refine ⟨U, hU, hdiag e, H, (fun s => hfixed e (hdiag e) s), ?_⟩
  intro s r
  exact congrArg (fun γ : loops P v hv => γ r) (hfixed e (hdiag e) s)

-- Actual convex neighborhoods give actual paths staying inside them, with no
-- supplied cover/interpolation/CW/finite-carrier witness in this importing client.
example {V : Type u} (P : PreAbstractSimplicialComplex V) (v : V) (hv : {v} ∈ P)
    (γ : loops P v hv) :
    ∃ N : Set (loops P v hv), IsOpen N ∧ γ ∈ N ∧
      ∀ δ : loops P v hv, δ ∈ N → ∃ p : Path γ δ,
        ∀ t : unitInterval, p t ∈ N := by
  obtain ⟨_, _, U, _, _, H, _, hcover, _⟩ := metricLoopLocalConvexity P v hv
  obtain ⟨N, hN, hγ, hsquare, hstay⟩ := hcover γ
  refine ⟨N, hN, hγ, ?_⟩
  intro δ hδ
  let hp : (γ, δ) ∈ U := hsquare γ δ hγ hδ
  let p : Path γ δ := Path.mk
    ⟨fun t => H (t, ⟨(γ, δ), hp⟩),
      H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (H.apply_zero ⟨(γ, δ), hp⟩) (H.apply_one ⟨(γ, δ), hp⟩)
  exact ⟨p, fun t => hstay γ δ hγ hδ hp t⟩
