/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanFaithfulCount
public import MathlibExt.Probability.Percolation.Universality.DualConfigLaw
public import MathlibExt.Probability.Percolation.Universality.FaceDualDichotomy

/-!
# The face-dual configuration of bond percolation on `ℤ²`

Index the faces of `ℤ²` by their lower-left corners. The dual lattice is then a copy of `ℤ²`, and
the dual edge between adjacent faces `f, g` crosses the primal edge `sharedPrimalEdge f g`. The
*face-open dual graph* `fci_faceOpenDual ω` joins adjacent faces whose separating primal edge is
closed in `ω`; it is the usual dual (closed) graph of planar percolation.

The map `{f, g} ↦ sharedPrimalEdge f g` is a bijection of the edge set of `ℤ²`. Extending it by
the identity off lattice edges and complementing gives the *face-dual configuration*
`fci_faceDualConfig ω`, whose open graph is exactly `fci_faceOpenDual ω`. At `p = 1/2` the map
`ω ↦ fci_faceDualConfig ω` preserves the Bernoulli product measure. This is the self-duality of
critical bond percolation on `ℤ²` stated with the geometric dual, in contrast to the rotated dual
`dualConfig ω`.

The file also shows that the rotated dual cannot be turned into the face dual by relabelling
sites: no map `Φ : ℤ² → ℤ²` satisfies `crossEdge (sharedPrimalEdge f g) = s(Φ f, Φ g)` for all
adjacent faces (`fci_no_frameChangeIso`).

## Main definitions

* `StatMech.Universality.fci_faceOpenDual`: adjacent faces joined when their separating edge is
  closed.
* `StatMech.Universality.fci_latticeEdgeEquiv`: the bijection `{f, g} ↦ sharedPrimalEdge f g` of
  lattice edges.
* `StatMech.Universality.fci_faceEdgeEquiv`: its extension by the identity to all of
  `Sym2 (Site 2)` (via `Equiv.Perm.ofSubtype`).
* `StatMech.Universality.fci_faceDualConfig`: the face-dual configuration.

## Main results

* `StatMech.Universality.fci_faceOpenDual_eq_openSubgraph`: the open graph of the face-dual
  configuration is the face-open dual graph.
* `StatMech.Universality.fci_faceDualConfig_measurePreserving`: at `p = 1/2` the face-dual map
  preserves the Bernoulli product measure.
* `StatMech.Universality.fci_cluster_faceOpenDual_circuit`: a finite open cluster is surrounded by
  a cycle of the face-open dual graph.
* `StatMech.Universality.fci_no_frameChangeIso`: no relabelling of sites turns rotated dual edges
  into face-dual edges.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Ch. 11.
* B. Bollobás and O. Riordan, *Percolation*, Cambridge University Press, 2006, Ch. 3.
-/

@[expose] public section

open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}

/-- A face-boundary walk viewed as a walk in the dual lattice. -/
def fci_faceWalk_to_dualWalk (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) : dualLattice.Walk u v :=
  c.mapLe (show faceBoundaryGraph S ≤ dualLattice from faceBoundaryGraph_le S)

theorem fci_faceWalk_to_dualWalk_support (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) :
    (fci_faceWalk_to_dualWalk S c).support = c.support := by
  rw [fci_faceWalk_to_dualWalk, SimpleGraph.Walk.support_mapLe_eq_support]

/-- The face-open dual graph of `ω`: adjacent faces `f, g` (indexed by lower-left corners) are
joined when the primal edge `sharedPrimalEdge f g` separating them is closed. -/
def fci_faceOpenDual (ω : ConfigSpace (Sym2 (Site 2))) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false
  symm := by
    refine ⟨?_⟩
    rintro f g ⟨hadj, hcl⟩
    exact ⟨hadj.symm, by rw [← sharedPrimalEdge_comm_of_adj hadj]; exact hcl⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem fci_faceOpenDual_adj (ω : ConfigSpace (Sym2 (Site 2))) (f g : Site 2) :
    (fci_faceOpenDual ω).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false := Iff.rfl

theorem fci_faceOpenDual_le_dualLattice (ω : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual ω ≤ dualLattice := fun _ _ h => h.1

/-- The face-boundary graph of an open cluster is contained in the face-open dual graph: its
separating edges are closed (`StatMech.Percolation.sharedPrimalEdge_isClosed`). -/
theorem fci_faceBoundaryGraph_cluster_le (o : Site 2) :
    faceBoundaryGraph (cluster 2 ω o) ≤ fci_faceOpenDual ω :=
  fun _ _ h => ⟨h.1, Percolation.sharedPrimalEdge_isClosed o h⟩

/-- A finite open cluster is surrounded by a cycle of the face-open dual graph (a closed dual
circuit). -/
theorem fci_cluster_faceOpenDual_circuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (fci_faceOpenDual ω).Walk u u), c.IsCycle := by
  obtain ⟨u, c, hcyc, _⟩ := fdd_cluster_dualCircuit_open o hfin w hz
  exact ⟨u, c.mapLe (fci_faceBoundaryGraph_cluster_le o),
    hcyc.mapLe (fci_faceBoundaryGraph_cluster_le o)⟩

/-- A face-boundary edge of the left-reach set whose separating edge is closed is an edge of the
face-open dual graph. -/
theorem fci_leftReach_faceOpenDual_adj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f g : Site 2} (h : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hcl : ω (sharedPrimalEdge f g) = false) :
    (fci_faceOpenDual ω).Adj f g :=
  ⟨h.1, hcl⟩

/-- `Φ` relabels faces so that the quarter turn of each separating edge is the edge between the
relabelled faces. No such `Φ` exists (`fci_no_frameChangeIso`). -/
def fci_FrameCompat (Φ : Site 2 → Site 2) : Prop :=
  ∀ f g : Site 2, (hypercubicLattice 2).Adj f g →
    crossEdge (sharedPrimalEdge f g) = s(Φ f, Φ g)

theorem fci_face_adj_left (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem fci_face_adj_right (a b : ℤ) :
    (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

/-- The rotated dual is not the face dual up to relabelling: the quarter turns of the edges
separating face `(0,0)` from its left and right neighbors share no vertex, so `Φ (0,0)` cannot
lie on both. -/
theorem fci_no_frameChangeIso : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := by
  rintro ⟨Φ, hΦ⟩
  have hL := hΦ ![0, 0] ![0 - 1, 0] (fci_face_adj_left 0 0)
  rw [fdd_dualEdge_leftSide] at hL
  have hR := hΦ ![0, 0] ![0 + 1, 0] (fci_face_adj_right 0 0)
  rw [fdd_dualEdge_rightSide] at hR
  have hmemL : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0], ![-(0 + 1), 0]) := by
    rw [hL]; exact Sym2.mem_mk_left _ _
  have hmemR : Φ ![0, 0] ∈ s(![(-0 : ℤ), 0 + 1], ![-(0 + 1), 0 + 1]) := by
    rw [hR]; exact Sym2.mem_mk_left _ _
  have h1 : (Φ ![0, 0]) 1 = 0 := by
    rw [Sym2.mem_iff] at hmemL
    rcases hmemL with h | h <;> rw [h] <;> simp
  have h2 : (Φ ![0, 0]) 1 = 1 := by
    rw [Sym2.mem_iff] at hmemR
    rcases hmemR with h | h <;> rw [h] <;> simp
  rw [h1] at h2; exact absurd h2 (by norm_num)

/-- Equivalently, no relabelling `Φ` makes each separating edge the inverse quarter turn of the
edge between relabelled faces. -/
theorem fci_no_open_dual_relabel :
    ¬ ∃ Φ : Site 2 → Site 2, ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g →
      sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g)) := by
  rintro ⟨Φ, hΦ⟩
  refine fci_no_frameChangeIso ⟨fun x => Φ x, ?_⟩
  intro f g hadj
  rw [hΦ f g hadj, crossEdge_mk]
  rw [show rot90Fun (rot90Inv (Φ f)) = Φ f from rot90Equiv.right_inv (Φ f),
     show rot90Fun (rot90Inv (Φ g)) = Φ g from rot90Equiv.right_inv (Φ g)]

/-- `s(f, g) ↦ sharedPrimalEdge f g` on lattice edges, and the identity on other pairs. -/
noncomputable def fci_sharedEdgeRaw : Sym2 (Site 2) → Sym2 (Site 2) :=
  Sym2.lift <| ⟨fun f g => if h : (hypercubicLattice 2).Adj f g then
      sharedPrimalEdge f g else s(f, g), by
    intro f g
    dsimp
    by_cases h : (hypercubicLattice 2).Adj f g
    · simp only [h, h.symm, ↓reduceIte]
      exact sharedPrimalEdge_comm_of_adj h
    · have h' : ¬ (hypercubicLattice 2).Adj g f := fun h' => h h'.symm
      simp only [h, h', ↓reduceIte]
      exact Sym2.eq_swap⟩

@[simp] theorem fci_sharedEdgeRaw_mk_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g := by
  change (if _h : (hypercubicLattice 2).Adj f g then
    sharedPrimalEdge f g else s(f, g)) = sharedPrimalEdge f g
  split <;> simp_all

private theorem fci_sym2_exists (e : Sym2 (Site 2)) : ∃ f g : Site 2, e = s(f, g) := by
  induction e using Sym2.inductionOn with
  | _ f g => exact ⟨f, g, rfl⟩

/-- `{f, g} ↦ sharedPrimalEdge f g` as a map on the edge set of `ℤ²`. -/
noncomputable def fci_sharedEdgeMap : (hypercubicLattice 2).edgeSet →
    (hypercubicLattice 2).edgeSet := fun e => ⟨fci_sharedEdgeRaw e.1, by
  obtain ⟨f, g, hval⟩ := fci_sym2_exists e.1
  have hfg : (hypercubicLattice 2).Adj f g :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  rw [hval, fci_sharedEdgeRaw_mk_of_adj hfg]
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq, SimpleGraph.mem_edgeSet]
  exact hadj ⟩

theorem fci_sharedEdgeMap_injective : Function.Injective fci_sharedEdgeMap := by
  intro e e' heq
  apply Subtype.ext
  obtain ⟨f, g, hval⟩ := fci_sym2_exists e.1
  obtain ⟨f', g', hval'⟩ := fci_sym2_exists e'.1
  have hfg : (hypercubicLattice 2).Adj f g :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  have hfg' : (hypercubicLattice 2).Adj f' g' :=
    (SimpleGraph.mem_edgeSet _).mp (hval' ▸ e'.2)
  have hshared : sharedPrimalEdge f g = sharedPrimalEdge f' g' := by
    have heq' := congrArg Subtype.val heq
    change fci_sharedEdgeRaw e.1 = fci_sharedEdgeRaw e'.1 at heq'
    rwa [hval, hval', fci_sharedEdgeRaw_mk_of_adj hfg,
      fci_sharedEdgeRaw_mk_of_adj hfg'] at heq'
  rw [hval, hval']
  exact (jce_sharedPrimalEdge_inj hfg hfg').mpr hshared

theorem fci_sharedEdgeMap_surjective : Function.Surjective fci_sharedEdgeMap := by
  intro e
  obtain ⟨p, q, hval⟩ := fci_sym2_exists e.1
  have hpq : (hypercubicLattice 2).Adj p q :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  obtain ⟨f, g, hfg, hshared⟩ := jfc_flankingFaces hpq
  let d : (hypercubicLattice 2).edgeSet :=
    ⟨s(f, g), (SimpleGraph.mem_edgeSet _).mpr hfg⟩
  refine ⟨d, Subtype.ext ?_⟩
  change fci_sharedEdgeRaw s(f, g) = e.1
  rw [fci_sharedEdgeRaw_mk_of_adj hfg, hshared, ← hval]

/-- The bijection `{f, g} ↦ sharedPrimalEdge f g` of the edge set of `ℤ²`, sending the dual edge
between adjacent faces to the primal edge it crosses. -/
noncomputable def fci_latticeEdgeEquiv : (hypercubicLattice 2).edgeSet ≃
    (hypercubicLattice 2).edgeSet :=
  Equiv.ofBijective fci_sharedEdgeMap
    ⟨fci_sharedEdgeMap_injective, fci_sharedEdgeMap_surjective⟩

/-- `fci_latticeEdgeEquiv` extended by the identity to all unordered pairs of sites. -/
noncomputable def fci_faceEdgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) :=
  @Equiv.Perm.ofSubtype _ (· ∈ (hypercubicLattice 2).edgeSet) (Classical.decPred _)
    fci_latticeEdgeEquiv

theorem fci_faceEdgeEquiv_mk_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    fci_faceEdgeEquiv s(f, g) = sharedPrimalEdge f g := by
  rw [fci_faceEdgeEquiv, @Equiv.Perm.ofSubtype_apply_of_mem _ _ (Classical.decPred _) _ _
    ((SimpleGraph.mem_edgeSet _).mpr h)]
  change fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g
  exact fci_sharedEdgeRaw_mk_of_adj h

/-- The face-dual configuration: the dual edge `s(f, g)` between adjacent faces is open exactly
when the primal edge `sharedPrimalEdge f g` it crosses is closed in `w`. (On pairs that are not
lattice edges it is the complement of `w`, which plays no role.) -/
noncomputable def fci_faceDualConfig (w : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) := fun e => !(w (fci_faceEdgeEquiv e))

/-- The open graph of the face-dual configuration is the face-open dual graph. -/
theorem fci_faceOpenDual_eq_openSubgraph (w : ConfigSpace (Sym2 (Site 2))) :
    fci_faceOpenDual w = openSubgraph 2 (fci_faceDualConfig w) := by
  ext f g
  constructor
  · rintro ⟨h, hclosed⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h]
    simpa using hclosed
  · rintro ⟨h, hopen⟩
    refine ⟨h, ?_⟩
    rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj h] at hopen
    simpa using hopen

/-- **Self-duality of critical bond percolation on `ℤ²`.** At `p = 1/2` the face-dual map
`ω ↦ fci_faceDualConfig ω` preserves the Bernoulli product measure: the closed dual graph of a
critical configuration has the law of the open primal graph. See Grimmett, *Percolation*, 2nd ed.,
1999, Ch. 11. -/
theorem fci_faceDualConfig_measurePreserving :
    MeasurePreserving
      (fci_faceDualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  let reindex := Equiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm
  have hreindex : MeasurePreserving reindex
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
    refine ⟨(MeasurableEquiv.piCongrLeft (fun _ => Bool) fci_faceEdgeEquiv.symm).measurable, ?_⟩
    unfold bernoulliProductMeasure
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
      fci_faceEdgeEquiv.symm
  have hcompl : MeasurePreserving
      (fun (eta : ConfigSpace (Sym2 (Site 2))) e => !(eta e))
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
    refine ⟨measurable_complement, ?_⟩
    rw [map_complement (2⁻¹ : ℝ≥0) half_le_one]
    congr 1
    exact one_sub_half
  have hcomp := hcompl.comp hreindex
  convert hcomp using 1
  funext w e
  simp [fci_faceDualConfig, reindex, Equiv.piCongrLeft_apply]

/-- Without a horizontal crossing of `rect 0 n 0 n` (`n ≥ 0`): the conclusions of
`fdd_square_dichotomy`, with the face-boundary cycle also a cycle of the dual lattice.

Despite the name this is not the box-crossing dichotomy: the cycle is not shown to be a cycle of
`fci_faceOpenDual ω` (some of its separating edges leave the square and need not be closed), nor
to cross the square from bottom to top. -/
theorem fci_square_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u),
        c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) := by
  obtain ⟨hfin, hbar, hne, ⟨u, c, hcyc⟩⟩ := fdd_square_dichotomy ω n hn hnoH
  exact ⟨hfin, hbar, hne, u, c, hcyc,
    hcyc.mapLe (show faceBoundaryGraph _ ≤ dualLattice from faceBoundaryGraph_le _)⟩

end Universality

end StatMech
