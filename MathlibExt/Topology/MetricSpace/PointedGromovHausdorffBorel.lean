/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Topology.MetricSpace.PointedGromovHausdorff
public import MathlibExt.Topology.MetricSpace.MeasurableNet
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
/-!
# Pointed Gromov–Hausdorff convergence with Borel approximation maps
Gigli–Mondino–Savaré (2015), Definition pmGH,
requires Borel maps (complete separable spaces).
When every `X n` is separable, arbitrary maps
coincide with the Borel-map version;
no assumption on `Y` is needed.
Without separability the repository relation
is an extension of GMS, not GMS itself.
-/
@[expose] public section
noncomputable section
namespace GromovHausdorff
universe u v
/-- Bridge to GMS pmGH (Borel maps):
with separable `X n`, arbitrary maps can be replaced. -/
theorem pointedGHConverges_iff_exists_measurable
    {X : ℕ → Type u} [∀ n, PseudoMetricSpace (X n)]
    [∀ n, TopologicalSpace.SeparableSpace (X n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, BorelSpace (X n)] {Y : Type v} [PseudoMetricSpace Y]
    [MeasurableSpace Y] (p : ∀ n, X n) (q : Y) :
    PointedGHConverges p q ↔
      ∀ (R : ℝ) (hR : 0 < R) (ε : ℝ) (_ : 0 < ε),
        ∀ᶠ n in Filter.atTop, ∃ f : ↥(Metric.ball (p n) R) → Y,
          Measurable f ∧ f ⟨p n, Metric.mem_ball_self hR⟩ = q ∧
            (∀ x y, |dist (f x) (f y) - dist (x : X n) (y : X n)| ≤ ε) ∧
            Metric.ball q (R - ε) ⊆ Metric.thickening ε (Set.range f) := by
  constructor
  · intro h R hR ε hε
    have hε4 : 0 < ε / 4 := by linarith
    have hev := h R hR (ε / 4) hε4
    refine Filter.Eventually.mono hev (fun n hn => ?_)
    obtain ⟨f, hbase, hdist, hcover⟩ := hn
    obtain ⟨u, ι, hu0, hιmeas, hι0, hclose⟩ := Metric.exists_measurable_index_dist_lt
      (⟨p n, Metric.mem_ball_self hR⟩ : ↥(Metric.ball (p n) R)) hε4
    have hfu : Measurable (f ∘ u) := measurable_from_nat
    have hgmeas :
        Measurable (fun x : ↥(Metric.ball (p n) R) => f (u (ι x))) :=
      hfu.comp hιmeas
    have hbase_g : f (u (ι ⟨p n, Metric.mem_ball_self hR⟩)) = q := by
      rw [hι0, hu0, hbase]
    have hdist_g : ∀ x y : ↥(Metric.ball (p n) R),
      |dist (f (u (ι x))) (f (u (ι y))) - dist (x : X n) (y : X n)| ≤ ε := by
      intro x y
      have hx : dist (x : X n) (u (ι x) : X n) < ε / 4 := by
        have h := hclose x
        rwa [Subtype.dist_eq] at h
      have hy : dist (y : X n) (u (ι y) : X n) < ε / 4 := by
        have h := hclose y
        rwa [Subtype.dist_eq] at h
      have hfab : |dist (f (u (ι x))) (f (u (ι y))) -
        dist (u (ι x) : X n) (u (ι y) : X n)| ≤ ε / 4 := hdist _ _
      have tri1 : dist (u (ι x) : X n) (u (ι y) : X n) ≤
        dist (u (ι x) : X n) (x : X n) + dist (x : X n) (u (ι y) : X n) :=
        dist_triangle _ _ _
      have tri2 : dist (x : X n) (u (ι y) : X n) ≤
        dist (x : X n) (y : X n) + dist (y : X n) (u (ι y) : X n) :=
        dist_triangle _ _ _
      have tri3 : dist (x : X n) (y : X n) ≤
        dist (x : X n) (u (ι x) : X n) + dist (u (ι x) : X n) (y : X n) :=
        dist_triangle _ _ _
      have tri4 : dist (u (ι x) : X n) (y : X n) ≤
        dist (u (ι x) : X n) (u (ι y) : X n) + dist (u (ι y) : X n) (y : X n) :=
        dist_triangle _ _ _
      have c1 : dist (u (ι x) : X n) (x : X n) =
        dist (x : X n) (u (ι x) : X n) := dist_comm _ _
      have c2 : dist (u (ι y) : X n) (y : X n) =
        dist (y : X n) (u (ι y) : X n) := dist_comm _ _
      have hab : |dist (u (ι x) : X n) (u (ι y) : X n) -
        dist (x : X n) (y : X n)| ≤ dist (x : X n) (u (ι x) : X n) +
        dist (y : X n) (u (ι y) : X n) := by
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
      have heq : dist (f (u (ι x))) (f (u (ι y))) - dist (x : X n) (y : X n) =
        (dist (f (u (ι x))) (f (u (ι y))) - dist (u (ι x) : X n) (u (ι y) : X n)) +
        (dist (u (ι x) : X n) (u (ι y) : X n) - dist (x : X n) (y : X n)) :=
        (sub_add_sub_cancel _ _ _).symm
      rw [heq]
      refine le_trans (abs_add_le _ _) ?_
      linarith
    have hcover_g : Metric.ball q (R - ε) ⊆
      Metric.thickening ε (Set.range (fun x : ↥(Metric.ball (p n) R) => f (u (ι x)))) := by
      intro y hy
      have hle : R - ε ≤ R - ε / 4 := by linarith
      have hy4 : y ∈ Metric.ball q (R - ε / 4) :=
        Metric.ball_subset_ball hle hy
      have hmem := hcover hy4
      rw [Metric.mem_thickening_iff] at hmem
      obtain ⟨z, ⟨x, rfl⟩, hlt⟩ := hmem
      have hx : dist (x : X n) (u (ι x) : X n) < ε / 4 := by
        have h := hclose x
        rwa [Subtype.dist_eq] at h
      have hfab : |dist (f x) (f (u (ι x))) -
        dist (x : X n) (u (ι x) : X n)| ≤ ε / 4 := hdist _ _
      have hfa : dist (f x) (f (u (ι x))) < ε / 2 := by
        have h2 := (abs_le.mp hfab).2
        linarith
      have tri : dist y (f (u (ι x))) ≤ dist y (f x) + dist (f x) (f (u (ι x))) :=
        dist_triangle _ _ _
      have hlt' : dist y (f (u (ι x))) < ε := by linarith
      exact Metric.mem_thickening_iff.mpr ⟨_, ⟨x, rfl⟩, hlt'⟩
    exact ⟨_, hgmeas, hbase_g, hdist_g, hcover_g⟩
  · intro h R hR ε hε
    have hev := h R hR ε hε
    refine Filter.Eventually.mono hev (fun n hn => ?_)
    obtain ⟨f, _, hbase, hdist, hcover⟩ := hn
    exact ⟨f, hbase, hdist, hcover⟩
end GromovHausdorff
