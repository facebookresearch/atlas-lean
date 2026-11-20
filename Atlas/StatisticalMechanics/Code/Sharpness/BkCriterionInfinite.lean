/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Probability.InfiniteBK
import Code.Sharpness.BkCriterionFull
import Code.Sharpness.PivotalFactorFull
import Code.Percolation.SurfaceReassembly
import Code.Lattice.PlanarTopology

open MeasureTheory Set Finset
open scoped NNReal

namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph
open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}




theorem shk_mem_boundaryEdges_iff {S : Finset (Site d)} {x y : Site d} :
    (x, y) ∈ boundaryEdges d S ↔
      x ∈ S ∧ y ∉ S ∧ (hypercubicLattice d).Adj x y := by
  classical
  constructor
  · intro hxy
    rw [boundaryEdges, Finset.mem_image] at hxy
    obtain ⟨t, ht, hteq⟩ := hxy
    rw [Finset.mem_filter] at ht
    obtain ⟨htmem, hyout⟩ := ht
    rw [Finset.mem_product] at htmem
    obtain ⟨hxS, htcoords⟩ := htmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hteq.symm
    refine ⟨hxS, hyout, ?_⟩
    change NearestNeighbour d t.1
      (coordShift t.1 t.2.1 (stepSign t.2.2))
    rw [nearestNeighbour_iff_shift]
    refine ⟨t.2.1, stepSign t.2.2, ?_, rfl⟩
    cases t.2.2 <;> simp [stepSign]
  · rintro ⟨hxS, hyS, hxy⟩
    change NearestNeighbour d x y at hxy
    rw [nearestNeighbour_iff_shift] at hxy
    obtain ⟨i, sgn, hsgn, rfl⟩ := hxy
    rcases hsgn with rfl | rfl
    · rw [boundaryEdges, Finset.mem_image]
      refine ⟨(x, (i, true)), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hxS, ⟨Finset.mem_univ i, Finset.mem_univ true⟩⟩,
          by simpa [coordShift, stepSign, Lattice.shift] using hyS⟩
      · rfl
    · rw [boundaryEdges, Finset.mem_image]
      refine ⟨(x, (i, false)), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hxS, ⟨Finset.mem_univ i, Finset.mem_univ false⟩⟩,
          by simpa [coordShift, stepSign, Lattice.shift] using hyS⟩
      · rfl



theorem shk_firstExit_inclusion_lattice (A : Set (Site d))
    (S : Finset (Site d)) (B : Set (Site d)) (u : Site d)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent (hypercubicLattice d) A u B ⊆
      ⋃ q ∈ boundaryEdges d S,
        disjointOccurrence
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1})
          (disjointOccurrence (edgeOpenEvent q.1 q.2)
            (connEvent (hypercubicLattice d) A q.2 B)) := by
  intro omega homega
  simp only [connEvent, Set.mem_setOf_eq] at homega
  obtain ⟨b, hbA, hbB, path, hsupp⟩ :=
    shk_walk_of_connToSet (hypercubicLattice d) omega A u B homega
  have hbypass_supp : ∀ z ∈ path.bypass.support, z ∈ A := fun z hz =>
    hsupp z (path.support_bypass_subset hz)
  have hbS : b ∉ (S : Set (Site d)) := hBS b hbB
  obtain ⟨x, y, hxS, hyS, hadj, htriple⟩ :=
    shk_firstExit_triple (hypercubicLattice d) omega A (S : Set (Site d)) B
      u b huS hbB hbS path.bypass path.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), shk_mem_boundaryEdges_iff.mpr ⟨hxS, hyS, hadj⟩, htriple⟩



theorem shk_connEvent_singleton_eq_connWithinEvent (T : Set (Site d))
    (u x : Site d) :
    connEvent (hypercubicLattice d) T u {x} = connWithinEvent d T u x := by
  ext omega
  constructor
  · rintro ⟨hu, b, hbT, rfl, hconn⟩
    exact ⟨hu, hbT, hconn⟩
  · rintro ⟨hu, hx, hconn⟩
    exact ⟨hu, x, hx, rfl, hconn⟩



theorem shk_connEvent_singleton_dependsOn (T : Finset (Site d)) (u x : Site d) :
    DependsOn (connEvent (hypercubicLattice d) (T : Set (Site d)) u {x})
      (internalEdgesFinset T : Set (Sym2 (Site d))) := by
  rw [shk_connEvent_singleton_eq_connWithinEvent]
  exact ih_event_dependsOn_of_indicator shp_connWithinEvent_dependsOn


theorem shk_edgeOpenEvent_dependsOn (x y : Site d) :
    DependsOn (edgeOpenEvent x y)
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  exact ih_event_dependsOn_of_indicator (by
    simpa only [edgeOpenEvent] using
      (coord_true_dependsOn (E := Sym2 (Site d)) s(x, y)))



noncomputable def shk_firstExitSupport (S Lam : Finset (Site d)) :
    Finset (Sym2 (Site d)) :=
  (internalEdgesFinset S ∪
      (boundaryEdges d S).image (fun q => s(q.1, q.2))) ∪
    internalEdgesFinset Lam




theorem bk_criterion_infinite_lattice_singleton (p : ℝ≥0) (hp : p ≤ 1)
    (Lam S : Finset (Site d)) (u x : Site d) (huS : u ∈ S) (hxS : x ∉ S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x}) ≤
      ∑ q ∈ boundaryEdges d S, (p : ℝ) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}) := by
  classical
  let bnd := boundaryEdges d S
  let P : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}
  let Q : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    edgeOpenEvent q.1 q.2
  let R : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}
  let F := shk_firstExitSupport (d := d) S Lam
  have hPdep : ∀ q ∈ bnd, DependsOn (P q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (shk_connEvent_singleton_dependsOn S u q.1).mono
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  have hQdep : ∀ q ∈ bnd, DependsOn (Q q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (shk_edgeOpenEvent_dependsOn q.1 q.2).mono
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hRdep : ∀ q ∈ bnd, DependsOn (R q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (shk_connEvent_singleton_dependsOn Lam q.2 x).mono
    intro e he
    exact Finset.mem_union_right _ he
  have hcrit := ibk_criterion_of_finite_dependsOn hp bnd P Q R F
    hPdep hQdep hRdep
    (fun q _ => isIncreasing_connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1})
    (fun q _ => isIncreasing_edgeOpenEvent q.1 q.2)
    (fun q _ => isIncreasing_connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x})
    (shk_firstExit_inclusion_lattice (Lam : Set (Site d)) S {x} u huS
      (by simpa using hxS))
  calc
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x}) ≤
        ∑ q ∈ bnd,
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (P q) *
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (Q q) *
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (R q) := hcrit
    _ = ∑ q ∈ boundaryEdges d S, (p : ℝ) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [show (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (Q q) =
          (p : ℝ) by
        simpa only [Q, edgeOpenEvent] using
          (coord_true_prob p hp s(q.1, q.2))]
      simp only [bnd, P, R]
      ring

end Sharpness

end StatMech
