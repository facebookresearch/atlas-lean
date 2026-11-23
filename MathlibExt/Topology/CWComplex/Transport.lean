/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Logic.Small.Basic

/-!
# Transport of complete classical CW structures

A homeomorphism and a dimensionwise equivalence of cell identifiers transport
the original characteristic maps, finite frontiers and weak topology. The
same-universe and upper-universe forms retain the original identifiers or
their literal universe lifts. No separation or finiteness assumption is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Function Topology

universe u v

namespace Topology.CWComplex

/-- Transport the actual CW structure along a homeomorphism and specified cell bijections. -/
@[instance_reducible]
def transportWithCells {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y)
    (cells : ℕ → Type v) (e : ∀ n, old.cell n ≃ cells n) :
    CWComplex (Set.univ : Set Y) := by
  classical
  let chart (n : ℕ) (j : cells n) : PartialEquiv (Fin n → ℝ) Y :=
    (old.map n ((e n).symm j)).transEquiv h.toEquiv
  exact
    { cell := cells
      map := chart
      source_eq n j := old.source_eq n ((e n).symm j)
      continuousOn n j := h.continuous.comp_continuousOn (old.continuousOn n ((e n).symm j))
      continuousOn_symm n j := by
        change ContinuousOn (fun y : Y => (old.map n ((e n).symm j)).symm (h.symm y))
          (h.symm ⁻¹' (old.map n ((e n).symm j)).target)
        exact (old.continuousOn_symm n ((e n).symm j)).comp
          h.continuous_invFun.continuousOn (fun _ hy => hy)
      pairwiseDisjoint' := by
        intro a _ b _ hab
        let index : (Σ n, cells n) ≃ (Σ n, old.cell n) :=
          Equiv.sigmaCongrRight (fun n => (e n).symm)
        have hne : index a ≠ index b := fun heq => hab (index.injective heq)
        have hd := old.pairwiseDisjoint' (Set.mem_univ _) (Set.mem_univ _) hne
        apply Set.disjoint_left.mpr
        rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
        have heq : old.map a.1 ((e a.1).symm a.2) p =
            old.map b.1 ((e b.1).symm b.2) q := h.injective (hpy.trans hqy.symm)
        exact Set.disjoint_left.mp hd ⟨p, hp, rfl⟩ ⟨q, hq, heq.symm⟩
      mapsTo' n j := by
        obtain ⟨I, hI⟩ := old.mapsTo' n ((e n).symm j)
        refine ⟨fun m => (I m).map (e m).toEmbedding, ?_⟩
        intro z hz
        have hZ := hI hz
        simp only [Set.mem_iUnion, Set.mem_image] at hZ ⊢
        obtain ⟨m, hm, k, hk, p, hp, heq⟩ := hZ
        refine ⟨m, hm, e m k, Finset.mem_map.mpr ⟨k, hk, rfl⟩, p, hp, ?_⟩
        change h (old.map m ((e m).symm (e m k)) p) = h (old.map n ((e n).symm j) z)
        rw [(e m).symm_apply_apply]
        exact congrArg h heq
      closed' A _ hA := by
        let B : Set X := h ⁻¹' A
        have hB : IsClosed B := old.closed' B (Set.subset_univ _) (by
          intro n j
          have hc := (hA n (e n j)).preimage h.continuous
          have heq : h ⁻¹' (A ∩ chart n (e n j) '' Metric.closedBall 0 1) =
              B ∩ old.map n j '' Metric.closedBall 0 1 := by
            ext x
            constructor
            · rintro ⟨hx, z, hz, hzx⟩
              refine ⟨hx, z, hz, ?_⟩
              apply h.injective
              change h (old.map n ((e n).symm (e n j)) z) = h x at hzx
              rw [(e n).symm_apply_apply] at hzx
              exact hzx
            · rintro ⟨hx, z, hz, hzx⟩
              refine ⟨hx, z, hz, ?_⟩
              change h (old.map n ((e n).symm (e n j)) z) = h x
              rw [(e n).symm_apply_apply, hzx]
          exact heq ▸ hc)
        have himage : h '' B = A := Set.image_preimage_eq A h.surjective
        rw [← himage]
        exact h.isClosedMap B hB
      union' := by
        ext y
        constructor
        · intro _
          exact Set.mem_univ y
        · intro _
          have hy : h.symm y ∈ ⋃ n, ⋃ j, old.map n j '' Metric.closedBall 0 1 := by
            rw [old.union']
            exact Set.mem_univ _
          simp only [Set.mem_iUnion, Set.mem_image] at hy ⊢
          obtain ⟨n, j, p, hp, heq⟩ := hy
          refine ⟨n, e n j, p, hp, ?_⟩
          change h (old.map n ((e n).symm (e n j)) p) = y
          rw [(e n).symm_apply_apply, heq, h.apply_symm_apply] }

/-- Every complete characteristic partial equivalence is the original one postcomposed with the homeomorphism. -/
@[simp]
theorem transportWithCells_map {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y)
    (cells : ℕ → Type v) (e : ∀ n, old.cell n ≃ cells n) (n : ℕ) (j : cells n) :
    (transportWithCells old h cells e).map n j =
      (old.map n ((e n).symm j)).transEquiv h.toEquiv := rfl

/-- The transported characteristic map on an original cell has its exact original value. -/
theorem transportWithCells_map_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y)
    (cells : ℕ → Type v) (e : ∀ n, old.cell n ≃ cells n)
    (n : ℕ) (j : old.cell n) (z : Fin n → ℝ) :
    (transportWithCells old h cells e).map n (e n j) z = h (old.map n j z) := by
  change h (old.map n ((e n).symm (e n j)) z) = _
  rw [(e n).symm_apply_apply]

/-- Transport within the same universe without changing any cell identifier. -/
@[instance_reducible]
def transport {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y) : CWComplex (Set.univ : Set Y) :=
  transportWithCells old h old.cell (fun _ => Equiv.refl _)

/-- Upper-universe transport uses the literal universe lifts of the original cell identifiers. -/
@[instance_reducible]
def transportULift {X : Type u} {Y : Type (max u v)} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y) : CWComplex (Set.univ : Set Y) :=
  transportWithCells old h (fun n => ULift.{v} (old.cell n)) (fun _ => Equiv.ulift.symm)

/-- Same-universe transport keeps the literal original cell identifier type. -/
@[simp]
theorem transport_cell {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y) (n : ℕ) :
    (transport old h).cell n = old.cell n := rfl

/-- The complete same-universe characteristic map is the original partial equivalence postcomposed with `h`. -/
@[simp]
theorem transport_map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y) (n : ℕ) (j : old.cell n) :
    (transport old h).map n j = (old.map n j).transEquiv h.toEquiv := rfl

/-- Upper-universe transport keeps the exact universe lift of each cell identifier type. -/
@[simp]
theorem transportULift_cell {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y) (n : ℕ) :
    (transportULift old h).cell n = ULift.{v} (old.cell n) := rfl

/-- Every complete lifted characteristic partial equivalence retains the original map and inverse. -/
theorem transportULift_map {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y)
    (n : ℕ) (j : ULift.{v} (old.cell n)) :
    (transportULift old h).map n j = (old.map n j.down).transEquiv h.toEquiv := rfl

/-- A transported original zero cell is the same original point at every zero-dimensional coordinate. -/
theorem transportWithCells_zeroCell {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (old : CWComplex (Set.univ : Set X)) (h : X ≃ₜ Y)
    (cells : ℕ → Type v) (e : ∀ n, old.cell n ≃ cells n)
    (j : old.cell 0) (x : X) (hj : old.map 0 j ![] = x) :
    ∀ z : Fin 0 → ℝ, (transportWithCells old h cells e).map 0 (e 0 j) z = h x := by
  intro z
  have hz : z = ![] := Subsingleton.elim _ _
  rw [transportWithCells_map_apply, hz, hj]

private theorem cellCenterInjective (C : TopCat.{u})
    (old : CWComplex (Set.univ : Set C)) (n : ℕ) :
    Function.Injective (fun j : old.cell n => old.map n j 0) := by
  intro i j hij
  by_contra hne
  have hidx : (⟨n, i⟩ : Σ m, old.cell m) ≠ ⟨n, j⟩ := by
    intro h
    have hIJ : i = j := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h
    exact hne hIJ
  have hd := old.pairwiseDisjoint' (Set.mem_univ _) (Set.mem_univ _) hidx
  exact Set.disjoint_left.mp hd ⟨0, by simp, rfl⟩ ⟨0, by simp, hij.symm⟩

/-- Every cell identifier fits in the homeomorphic target universe through its characteristic center. -/
theorem cellsSmallOfHomeomorph (C : TopCat.{u})
    [CWComplex (Set.univ : Set C)] {X : Type v} [TopologicalSpace X]
    (h : C ≃ₜ X) (n : ℕ) : Small.{v} (cell (Set.univ : Set C) n) :=
  small_of_injective (h.injective.comp (cellCenterInjective C inferInstance n))

/-- Transport to an arbitrary target universe using the original cell-center reindexing. -/
@[instance_reducible]
def cwComplexOfHomeomorph (C : TopCat.{u})
    [CWComplex (Set.univ : Set C)] {X : Type v} [TopologicalSpace X]
    (h : C ≃ₜ X) : CWComplex (Set.univ : Set X) := by
  let old : CWComplex (Set.univ : Set C) := inferInstance
  let _ : ∀ n : ℕ, Small.{v} (old.cell n) := fun n => cellsSmallOfHomeomorph C h n
  exact transportWithCells old h (fun n => Shrink.{v} (old.cell n)) (fun _ => equivShrink _)

/-- Every original characteristic map is retained by the arbitrary-universe cell reindexing. -/
theorem cwComplexOfHomeomorph_characteristics (C : TopCat.{u})
    [CWComplex (Set.univ : Set C)] {X : Type v} [TopologicalSpace X]
    (h : C ≃ₜ X) (n : ℕ) :
    ∃ e : cell (Set.univ : Set C) n ≃ (cwComplexOfHomeomorph C h).cell n,
      ∀ j z, (cwComplexOfHomeomorph C h).map n (e j) z = h (map n j z) := by
  let old : CWComplex (Set.univ : Set C) := inferInstance
  let _ : ∀ n : ℕ, Small.{v} (old.cell n) := fun n => cellsSmallOfHomeomorph C h n
  refine ⟨equivShrink _, ?_⟩
  intro j z
  change h (old.map n ((equivShrink _).symm (equivShrink _ j)) z) = h (old.map n j z)
  rw [Equiv.symm_apply_apply]

end Topology.CWComplex
