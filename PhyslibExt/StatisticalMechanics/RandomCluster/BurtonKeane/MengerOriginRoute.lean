/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerFanPaths
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ThreeDisjointWitnesses
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutAvoidingSurvives

/-!
# Menger routing at the origin

Menger's theorem in the box graph turns three origin branches with distinct infinite clusters into
three origin-avoiding routes, the Menger core of a trifurcation.

## i. Overview

`bc20_boxGraph d m ω` is the open subgraph induced on `B_m`. If every separator of the neighbours of
the origin from the boundary has at least two vertices, Menger gives origin-avoiding paths, so
connections survive the removal of the origin. `bc20_OriginBranchSurvival` asks for three neighbours
of the origin in distinct infinite clusters with branches surviving the removal of the origin; it
yields `MengerCore` and the routing cover.

## ii. Key results

- `bc20_hardDir_boxGraph` : Menger's hard direction in the box graph
- `bc20_connected_removeSite_of_min2` : two-vertex separators give origin-avoiding connections
- `bc20_mengerCore_of_originBranchSurvival` : origin branch survival gives the Menger core
- `bc20_originBranchSurvival_of_originFree` : survival when the clusters avoid the origin

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech.Walls

variable {d : ℕ}

/-! ## A. Definitions -/

/-- The box `B_m` is finite. -/
noncomputable instance bc20_boxFintype (d m : ℕ) : Fintype (box d m) :=
  (box_finite d m).fintype

/-- The open subgraph of `ω` induced on `B_m`. -/
noncomputable def bc20_boxGraph (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    SimpleGraph (box d m) :=
  (openSubgraph d ω).induce (box d m)

/-- The origin as a vertex of `B_m`. -/
def bc20_originBox (d m : ℕ) : box d m := ⟨0, by intro i; simp⟩

/-! ## B. Results -/

@[simp] lemma bc20_originBox_coe (d m : ℕ) : (bc20_originBox d m : Site d) = 0 := rfl

lemma bc20_hardDir_boxGraph (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (A B : Set (box d m)) : bc17_HardDir (bc20_boxGraph d m ω) A B :=
  bc19_hardDir_all (bc20_boxGraph d m ω) A B

/-- A walk in the box graph viewed as an open walk in `ℤ^d`. -/
noncomputable def bc20_mapWalk (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    (openSubgraph d ω).Walk (u : Site d) (v : Site d) :=
  p.map (Embedding.induce (box d m)).toHom

lemma bc20_mapWalk_support (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    (bc20_mapWalk d m ω p).support
      = (p.support).map (Embedding.induce (G := openSubgraph d ω) (box d m)).toHom :=
  Walk.support_map _ _

lemma bc20_connected_of_boxWalk (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    Connected d ω (u : Site d) (v : Site d) :=
  (bc20_mapWalk d m ω p).reachable

lemma bc20_boxWalk_support_mem_box (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    ∀ z ∈ (bc20_mapWalk d m ω p).support, z ∈ box d m := by
  intro z hz
  rw [bc20_mapWalk_support, List.mem_map] at hz
  obtain ⟨w, _, rfl⟩ := hz
  exact w.2

lemma bc20_edge_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hadj : (openSubgraph d ω).Adj x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    (openSubgraph d (removeSite 0 ω)).Adj x y := by
  obtain ⟨hadj', hval⟩ := hadj
  refine ⟨hadj', ?_⟩
  have h0 : (0 : Site d) ∉ s(x, y) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨fun h => hx h.symm, fun h => hy h.symm⟩
  rw [removeSite_apply_of_notMem h0]; exact hval

/-- A walk avoiding the origin, viewed as a walk after the origin is removed. -/
noncomputable def bc20_walk_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (w : (openSubgraph d ω).Walk a x) (h0 : (0 : Site d) ∉ w.support) :
    (openSubgraph d (removeSite 0 ω)).Walk a x := by
  induction w with
  | nil => exact Walk.nil
  | @cons u v t hadj p ih =>
      rw [Walk.support_cons, List.mem_cons] at h0
      push Not at h0
      obtain ⟨hu0, hrest⟩ := h0
      have hv0 : v ≠ 0 := fun hv => hrest (hv ▸ p.start_mem_support)
      exact Walk.cons (bc20_edge_removeSite ω hadj (Ne.symm hu0) hv0) (ih hrest)

lemma bc20_origin_avoid_of_boxAvoid (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v)
    (h : bc20_originBox d m ∉ p.support) :
    (0 : Site d) ∉ (bc20_mapWalk d m ω p).support := by
  intro hmem
  rw [bc20_mapWalk_support, List.mem_map] at hmem
  obtain ⟨w, hw, hw0⟩ := hmem
  have hwe : w = bc20_originBox d m := Subtype.ext hw0
  exact h (hwe ▸ hw)

universe u
variable {V : Type u} [DecidableEq V] {GG : SimpleGraph V}

omit [DecidableEq V] in
lemma bc20_unique_index_through {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin k)) (z₀ : V) {i j : Fin k}
    (hi : z₀ ∈ (F.p i).support) (hj : z₀ ∈ (F.p j).support) : i = j := by
  by_contra hne
  exact F.hdisj hne hi hj

omit [DecidableEq V] in
lemma bc20_disjointFamily_avoids_origin {A B : Set V}
    (F : bc16_DisjointPathFamily GG A B (Fin 2)) (z₀ : V) :
    ∃ i : Fin 2, z₀ ∉ (F.p i).support := by
  by_contra h
  push Not at h
  exact F.hdisj (by decide) (h 0) (h 1)

lemma bc20_origin_avoiding_boxPath_of_min2 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m) (p : (bc20_boxGraph d m ω).Walk u v),
      u ∈ A ∧ v ∈ B ∧ bc20_originBox d m ∉ p.support := by
  obtain ⟨F⟩ := bc20_hardDir_boxGraph d m ω A B 2 hmin
  obtain ⟨i, hi⟩ := bc20_disjointFamily_avoids_origin F (bc20_originBox d m)
  exact ⟨F.a i, F.b i, F.p i, F.ha i, F.hb i, hi⟩

lemma bc20_connected_removeSite_of_min2 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧
      Connected d (removeSite 0 ω) (u : Site d) (v : Site d) := by
  obtain ⟨u, v, p, hu, hv, h0⟩ := bc20_origin_avoiding_boxPath_of_min2 d m ω hmin
  refine ⟨u, v, hu, hv, ?_⟩
  exact bc4_avoiding_walk_survives_origin_cut ω (bc20_mapWalk d m ω p)
    (bc20_origin_avoid_of_boxAvoid d m ω p h0)

/-- The boundary vertices of `B_m`, as vertices of the box graph. -/
def bc20_boundaryV (d m : ℕ) : Set (box d m) := {v | (v : Site d) ∈ vertexBoundary d m}

/-- The vertices of `B_m` on the boundary of `B_R`. -/
def bc20_shellV (d m R : ℕ) : Set (box d m) := {v | (v : Site d) ∈ vertexBoundary d R}

lemma bc20_shellReach_at (d m R : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω)
      (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
    ∃ (u z : Site d), u ∈ vertexBoundary d R ∧ z ∈ vertexBoundary d m ∧
      Connected d (removeSite 0 ω) u z := by
  obtain ⟨u, v, p, hu, hv, hp0⟩ := bc20_origin_avoiding_boxPath_of_min2 d m ω hmin
  exact ⟨(u : Site d), (v : Site d), hu, hv,
    bc4_avoiding_walk_survives_origin_cut ω (bc20_mapWalk d m ω p)
      (bc20_origin_avoid_of_boxAvoid d m ω p hp0)⟩

lemma bc20_exists_shellVertex_infinite (d R : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hmin : ∀ m : ℕ, ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω)
      (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
    ∃ u ∈ vertexBoundary d R, (cluster d (removeSite 0 ω) u).Infinite := by
  classical
  choose us zs hus hzs hconns using fun m => bc20_shellReach_at d m R ω (hmin m)
  set Vb := vertexBoundary d R with hVb
  have : Finite Vb := vertexBoundary_finite d R
  let f : ℕ → Vb := fun m => ⟨us m, hus m⟩
  have hpig : ∃ u : Vb, {m | f m = u}.Infinite := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set ℕ) ⊆ ⋃ u : Vb, {m | f m = u} := fun m _ =>
      Set.mem_iUnion.mpr ⟨f m, rfl⟩
    exact Set.infinite_univ ((Set.finite_iUnion h).subset hsub)
  obtain ⟨⟨u, huVb⟩, hinf⟩ := hpig
  refine ⟨u, huVb, ?_⟩
  rw [cluster_infinite_iff]
  intro n
  obtain ⟨m, hmS, hmge⟩ := hinf.exists_gt (n + 1)
  simp only [Set.mem_ofPred_eq] at hmS
  have huseq : us m = u := congrArg Subtype.val hmS
  refine ⟨zs m, ?_, by rw [← huseq]; exact hconns m⟩
  exact fun hzn => (hzs m).2 (box_mono d (by omega : n ≤ m - 1) hzn)

lemma bc20_removeSite_cluster_ne (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ : Site d)
    (hne : cluster d ω a₁ ≠ cluster d ω a₂) :
    cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ := by
  have hle : removeSite (0 : Site d) ω ≤ ω := by
    intro e; unfold removeSite; by_cases h : (0 : Site d) ∈ e <;> simp [h]
  exact cluster_ne_of_disjoint (removeSite 0 ω) a₁ a₂ (cluster d ω a₁) (cluster d ω a₂)
    (cluster_mono hle a₁) (cluster_mono hle a₂) (bc2_disjoint_of_ne hne)

/-- Three distinct neighbours of the origin lie in pairwise distinct infinite clusters whose
branches survive the removal of the origin. -/
def bc20_OriginBranchSurvival (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    (cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) ∧
    ((cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)

lemma bc20_mengerCore_of_originBranchSurvival (d : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc20_OriginBranchSurvival d ω) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hd12, hd13, hd23⟩, hinf⟩ := h
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf
    ⟨bc20_removeSite_cluster_ne ω a₁ a₂ hd12,
      bc20_removeSite_cluster_ne ω a₁ a₃ hd13,
      bc20_removeSite_cluster_ne ω a₂ a₃ hd23⟩

lemma bc20_mengerRoutingCover_of_originBranchSurvival (d n : ℕ)
    (h : ∀ ω ∈ threeMeetBox d n, bc20_OriginBranchSurvival d ω) :
    MengerRoutingCover d n :=
  fun ω hω => bc20_mengerCore_of_originBranchSurvival d ω (h ω hω)

lemma bc20_removeSite_infinite_of_originFree (ω : ConfigSpace (Sym2 (Site d))) (a : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω a) (hinf : (cluster d ω a).Infinite) :
    (cluster d (removeSite 0 ω) a).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  obtain ⟨z, hzb, hconn⟩ := (cluster_infinite_iff ω a).mp hinf m
  obtain ⟨w⟩ := hconn
  refine ⟨z, hzb, bc4_avoiding_walk_survives_origin_cut ω w (fun hmem => h0 ?_)⟩
  rw [cluster_eq_of_connected w.reachable]
  exact ava_support_mem_cluster ω w hmem

lemma bc20_originBranchSurvival_of_originFree (d : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧
      (cluster d ω a₃).Infinite) :
    bc20_OriginBranchSurvival d ω :=
  ⟨a₁, a₂, a₃, hne, hadj, hdist,
    bc20_removeSite_infinite_of_originFree ω a₁ h0.1 hinf.1,
    bc20_removeSite_infinite_of_originFree ω a₂ h0.2.1 hinf.2.1,
    bc20_removeSite_infinite_of_originFree ω a₃ h0.2.2 hinf.2.2⟩

end StatMech.Walls
