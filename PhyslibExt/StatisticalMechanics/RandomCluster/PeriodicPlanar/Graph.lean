/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology

/-!
# Periodic planar graphs and their random-cluster measures

`ℤ²`-periodic locally finite graphs, their finite orbit boxes, the free and wired finite-volume
random-cluster measures on them, and the square, triangular and hexagonal lattices as examples.

## i. Overview

A periodic graph carries an action of the translation group `ℤ²` by graph automorphisms with a
finite nonempty fundamental domain. The orbit box of radius `n` is the image of the box `[-n, n]²`
times the fundamental domain. On the induced finite graph we take the free and the wired
random-cluster measures (wired along the orbits not in the box of radius `n - 1`), push them to
configurations on all edges by declaring outside edges closed, and extract infinite-volume free
and wired measures as weak subsequential limits by compactness of the configuration space.
The definitions here carry no hypotheses beyond `0 < p < 1` and `0 < q`; the limit statements
are unconditional.

## ii. Key results

- `PeriodicGraph` : a `ℤ²`-periodic locally finite graph with a finite fundamental domain.
- `PeriodicGraph.freeInfiniteVolume_isLimit` : the free infinite-volume measure is a weak
  subsequential limit of the free orbit-box measures.
- `PeriodicGraph.wiredInfiniteVolume_isLimit` : the same for the wired measures.
- `square`, `triangular`, `hexagonal` : the three regular planar lattices as periodic graphs.

## iii. Table of contents

- A. Periodic graphs and orbit boxes
- B. Finite-volume measures
- C. Infinite-volume limits
- D. The square lattice
- E. The triangular lattice
- F. The hexagonal lattice

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.
-/

@[expose] public section

open Finset Set SimpleGraph
open MeasureTheory
namespace StatMech
namespace FK
namespace PeriodicPlanar

open StatMech.Lattice

/-! ## A. Periodic graphs and orbit boxes -/

/-- Translation of `ℤ²` by `z`, as a permutation of the sites. -/
def siteTranslate (z : Site 2) : Site 2 ≃ Site 2 where
  toFun x := x + z
  invFun x := x - z
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext i; simp

@[simp] lemma siteTranslate_apply (z x : Site 2) : siteTranslate z x = x + z := rfl

/-- A `ℤ²`-periodic graph: a locally finite simple graph with a `ℤ²`-action by graph automorphisms
and a finite nonempty fundamental domain whose translates cover all vertices. -/
structure PeriodicGraph (V : Type*) [DecidableEq V] where
  graph : SimpleGraph V
  shift : Site 2 → V ≃ V
  shift_zero : shift 0 = Equiv.refl V
  shift_add : ∀ z w v, shift (z + w) v = shift w (shift z v)
  shift_adj : ∀ z x y, graph.Adj (shift z x) (shift z y) ↔ graph.Adj x y
  fundamentalDomain : Finset V
  fundamentalDomain_nonempty : fundamentalDomain.Nonempty
  covers : ∀ v, ∃ z u, u ∈ fundamentalDomain ∧ shift z u = v
  locallyFinite : SimpleGraph.LocallyFinite graph

variable {V : Type*} [DecidableEq V]

/-- The orbit box of radius `n`: translates of the fundamental domain by sites in the box
`[-n, n]²`. -/
noncomputable def PeriodicGraph.orbitBox (P : PeriodicGraph V) (n : ℕ) : Finset V :=
  (((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain)).image
    (fun zu => P.shift zu.1 zu.2)

lemma PeriodicGraph.mem_orbitBox_iff (P : PeriodicGraph V) (n : ℕ) (v : V) :
    v ∈ P.orbitBox n ↔
      ∃ z : Site 2, z ∈ box 2 n ∧ ∃ u ∈ P.fundamentalDomain, P.shift z u = v := by
  simp only [PeriodicGraph.orbitBox, Finset.mem_image, Finset.mem_product,
    Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨z, u⟩, ⟨hz, hu⟩, huv⟩
    exact ⟨z, hz, u, hu, huv⟩
  · rintro ⟨z, hz, u, hu, huv⟩
    exact ⟨(z, u), ⟨hz, hu⟩, huv⟩

lemma PeriodicGraph.orbitBox_mono (P : PeriodicGraph V) : Monotone P.orbitBox := by
  intro m n hmn v hv
  rw [P.mem_orbitBox_iff] at hv ⊢
  obtain ⟨z, hz, u, hu, rfl⟩ := hv
  exact ⟨z, box_mono 2 hmn hz, u, hu, rfl⟩

lemma PeriodicGraph.exists_mem_orbitBox (P : PeriodicGraph V) (v : V) :
    ∃ n, v ∈ P.orbitBox n := by
  obtain ⟨z, u, hu, rfl⟩ := P.covers v
  have hzUnion : z ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
  obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hzUnion
  exact ⟨n, (P.mem_orbitBox_iff n _).2 ⟨z, hz, u, hu, rfl⟩⟩

/-- The vertices of the orbit box of radius `n`, as a subtype. -/
abbrev PeriodicGraph.OrbitVertex (P : PeriodicGraph V) (n : ℕ) :=
  {v : V // v ∈ P.orbitBox n}

/-- The orbit box has finitely many vertices. -/
noncomputable instance PeriodicGraph.instFintypeOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : Fintype (P.OrbitVertex n) :=
  Fintype.ofFinset (P.orbitBox n) (fun _ => Iff.rfl)

/-- Decidable equality on orbit-box vertices. -/
instance PeriodicGraph.instDecidableEqOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : DecidableEq (P.OrbitVertex n) :=
  Subtype.instDecidableEq

/-- The subgraph of the periodic graph induced on the orbit box. -/
def PeriodicGraph.orbitGraph (P : PeriodicGraph V) (n : ℕ) :
    SimpleGraph (P.OrbitVertex n) :=
  SimpleGraph.comap Subtype.val P.graph

/-- Adjacency in the orbit-box graph is decidable (classically). -/
noncomputable instance PeriodicGraph.instDecidableRelOrbitGraph
    (P : PeriodicGraph V) (n : ℕ) : DecidableRel (P.orbitGraph n).Adj :=
  Classical.decRel _

/-- A vertex of the orbit box of radius `n` is on the boundary if it is not in the orbit box of
radius `n - 1`. -/
def PeriodicGraph.orbitBoundary (P : PeriodicGraph V) (n : ℕ)
    (v : P.OrbitVertex n) : Prop :=
  (v : V) ∉ P.orbitBox (n - 1)

/-- The boundary predicate is decidable (classically). -/
noncomputable instance PeriodicGraph.instDecidablePredOrbitBoundary
    (P : PeriodicGraph V) (n : ℕ) : DecidablePred (P.orbitBoundary n) :=
  fun _ => Classical.dec _

/-! ## B. Finite-volume measures -/

/-- The free random-cluster measure on the orbit box of radius `n`. -/
noncomputable def PeriodicGraph.freeFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.fkPMF (P.orbitGraph n) hp hp1 hq

/-- The wired random-cluster measure on the orbit box of radius `n`, wired along its boundary. -/
noncomputable def PeriodicGraph.wiredFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.wiredFkPMF (P.orbitGraph n) (P.orbitBoundary n) hp hp1 hq

/-- The inclusion of orbit-box edges into all edges. -/
def PeriodicGraph.edgeIncl (P : PeriodicGraph V) (n : ℕ) :
    Sym2 (P.OrbitVertex n) → Sym2 V :=
  Sym2.map (Subtype.val : P.OrbitVertex n → V)

lemma PeriodicGraph.edgeIncl_injective (P : PeriodicGraph V) (n : ℕ) :
    Function.Injective (P.edgeIncl n) :=
  Sym2.map.injective Subtype.val_injective

/-- Extend a configuration on the orbit box to all edges, declaring every edge outside the box
closed. -/
noncomputable def PeriodicGraph.extendEdge (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n))) : ConfigSpace (Sym2 V) :=
  fun e => if h : e ∈ Set.range (P.edgeIncl n) then omega h.choose else false

@[simp] lemma PeriodicGraph.extendEdge_edgeIncl (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n)))
    (e : Sym2 (P.OrbitVertex n)) :
    P.extendEdge n omega (P.edgeIncl n e) = omega e := by
  unfold PeriodicGraph.extendEdge
  have hmem : P.edgeIncl n e ∈ Set.range (P.edgeIncl n) := ⟨e, rfl⟩
  rw [dite_eq_left hmem]
  congr 1
  exact P.edgeIncl_injective n hmem.choose_spec

lemma PeriodicGraph.monotone_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Monotone (P.extendEdge n) := by
  intro omega eta home e
  unfold PeriodicGraph.extendEdge
  split
  · exact home _
  · exact le_refl false

lemma PeriodicGraph.measurable_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Measurable (P.extendEdge n) :=
  Measurable.of_discrete

/-- The free orbit-box random-cluster measure, viewed on configurations of all edges. -/
noncomputable def PeriodicGraph.freeFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.freeFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    inferInstance⟩

/-- The wired orbit-box random-cluster measure, viewed on configurations of all edges. -/
noncomputable def PeriodicGraph.wiredFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.wiredFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    inferInstance⟩

/-! ## C. Infinite-volume limits -/

section Countable

variable [Countable V]

/-- A free infinite-volume random-cluster measure: a weak subsequential limit of the free orbit-box
measures. -/
noncomputable def PeriodicGraph.freeInfiniteVolume (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (CompactSpace.tendsto_subseq (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose

/-- The free infinite-volume measure is a weak limit along a subsequence of the free orbit-box
measures. -/
theorem PeriodicGraph.freeInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.freeFiniteMeasure (phi n) hp hp1 hq)
        (P.freeInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (CompactSpace.tendsto_subseq (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩

/-- A wired infinite-volume random-cluster measure: a weak subsequential limit of the wired
orbit-box measures. -/
noncomputable def PeriodicGraph.wiredInfiniteVolume (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (CompactSpace.tendsto_subseq (fun n => P.wiredFiniteMeasure n hp hp1 hq)).choose

/-- The wired infinite-volume measure is a weak limit along a subsequence of the wired orbit-box
measures. -/
theorem PeriodicGraph.wiredInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.wiredFiniteMeasure (phi n) hp hp1 hq)
        (P.wiredInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (CompactSpace.tendsto_subseq (fun n => P.wiredFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩

end Countable

/-! ## D. The square lattice -/

lemma siteTranslate_zero : siteTranslate (0 : Site 2) = Equiv.refl (Site 2) := by
  ext x i
  simp

lemma siteTranslate_add (z w v : Site 2) :
    siteTranslate (z + w) v = siteTranslate w (siteTranslate z v) := by
  ext i
  simp [add_assoc]

lemma square_shift_adj (z x y : Site 2) :
    (hypercubicLattice 2).Adj (siteTranslate z x) (siteTranslate z y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, siteTranslate_apply]
  have hsums :
      (∑ i, ((x + z) i - (y + z) i).natAbs) =
        ∑ i, (x i - y i).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [Pi.add_apply]
  rw [hsums]

/-- The square lattice `ℤ²` as a periodic graph, with a one-point fundamental domain. -/
noncomputable def square : PeriodicGraph (Site 2) where
  graph := hypercubicLattice 2
  shift := siteTranslate
  shift_zero := siteTranslate_zero
  shift_add := siteTranslate_add
  shift_adj := square_shift_adj
  fundamentalDomain := {0}
  fundamentalDomain_nonempty := ⟨0, by simp⟩
  covers v := ⟨v, 0, by simp, by ext i; simp⟩
  locallyFinite := Lattice.instLocallyFinite 2

/-! ## E. The triangular lattice -/

/-- The three step vectors `(1, 0)`, `(0, 1)`, `(-1, 1)` of the triangular lattice. -/
def triangularStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![-1, 1]] i

lemma triangularStep_ne_zero (i : Fin 3) : triangularStep i ≠ 0 := by
  fin_cases i <;> intro h
  · have := congrFun h 0
    norm_num [triangularStep] at this
  · have := congrFun h 1
    norm_num [triangularStep] at this
  · have := congrFun h 0
    norm_num [triangularStep] at this

/-- Adjacency of the triangular lattice on `ℤ²`: the sites differ by a triangular step. -/
def triangularAdj (x y : Site 2) : Prop :=
  ∃ i : Fin 3, y - x = triangularStep i ∨ x - y = triangularStep i

lemma triangularAdj_symm : Std.Symm triangularAdj := by
  constructor
  rintro x y ⟨i, h⟩
  exact ⟨i, h.symm⟩

lemma triangularAdj_irrefl : Std.Irrefl triangularAdj := by
  constructor
  rintro x ⟨i, h | h⟩
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm

/-- The triangular lattice as a simple graph on `ℤ²`. -/
def triangularGraph : SimpleGraph (Site 2) where
  Adj := triangularAdj
  symm := triangularAdj_symm
  loopless := triangularAdj_irrefl

@[simp] lemma triangularGraph_adj (x y : Site 2) :
    triangularGraph.Adj x y ↔ triangularAdj x y := Iff.rfl

/-- The neighbor of `x` in direction `i`, forward or backward. -/
def triangularNeighbor (x : Site 2) (ib : Fin 3 × Bool) : Site 2 :=
  if ib.2 then x + triangularStep ib.1 else x - triangularStep ib.1

lemma triangular_adj_neighbor (x : Site 2) (ib : Fin 3 × Bool) :
    triangularGraph.Adj x (triangularNeighbor x ib) := by
  rcases ib with ⟨i, b⟩
  rw [triangularGraph_adj]
  rcases b with _ | _
  · exact ⟨i, Or.inr (by simp [triangularNeighbor])⟩
  · exact ⟨i, Or.inl (by simp [triangularNeighbor])⟩

lemma triangular_mem_candidates_of_adj {x y : Site 2}
    (h : triangularGraph.Adj x y) :
    y ∈ Finset.univ.image (triangularNeighbor x) := by
  rw [triangularGraph_adj] at h
  obtain ⟨i, h | h⟩ := h
  · rw [Finset.mem_image]
    refine ⟨(i, true), Finset.mem_univ _, ?_⟩
    have hcoord : x + triangularStep i = y := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    simpa [triangularNeighbor] using hcoord
  · rw [Finset.mem_image]
    refine ⟨(i, false), Finset.mem_univ _, ?_⟩
    have hcoord : x - triangularStep i = y := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply] at hj ⊢
      omega
    simpa [triangularNeighbor] using hcoord

/-- The triangular lattice is locally finite (degree six). -/
noncomputable instance triangularGraph_locallyFinite :
    SimpleGraph.LocallyFinite triangularGraph := fun x =>
  Fintype.ofFinset (Finset.univ.image (triangularNeighbor x)) (by
    intro y
    rw [SimpleGraph.mem_neighborSet]
    exact ⟨(fun hy => by
        rw [Finset.mem_image] at hy
        obtain ⟨ib, _, rfl⟩ := hy
        exact triangular_adj_neighbor x ib),
      triangular_mem_candidates_of_adj⟩)

lemma triangular_shift_adj (z x y : Site 2) :
    triangularGraph.Adj (siteTranslate z x) (siteTranslate z y) ↔
      triangularGraph.Adj x y := by
  simp only [triangularGraph_adj, triangularAdj, siteTranslate_apply]
  have hyx : (y + z) - (x + z) = y - x := by abel
  have hxy : (x + z) - (y + z) = x - y := by abel
  rw [hyx, hxy]

/-- The triangular lattice as a periodic graph, with a one-point fundamental domain. -/
noncomputable def triangular : PeriodicGraph (Site 2) where
  graph := triangularGraph
  shift := siteTranslate
  shift_zero := siteTranslate_zero
  shift_add := siteTranslate_add
  shift_adj := triangular_shift_adj
  fundamentalDomain := {0}
  fundamentalDomain_nonempty := ⟨0, by simp⟩
  covers v := ⟨v, 0, by simp, by ext i; simp⟩
  locallyFinite := triangularGraph_locallyFinite

/-! ## F. The hexagonal lattice -/

/-- Vertices of the hexagonal lattice: a site of `ℤ²` and a sublattice label. -/
abbrev HexVertex := Site 2 × Bool

/-- The three step vectors `(1, 0)`, `(0, 1)`, `(1, 1)` joining the two hexagonal sublattices. -/
def hexagonalStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![1, 1]] i

/-- Adjacency of the hexagonal lattice: a vertex of the first sublattice is joined to the three
vertices of the second sublattice at a hexagonal step. -/
def hexagonalAdj (u v : HexVertex) : Prop :=
  (u.2 = false ∧ v.2 = true ∧ ∃ i : Fin 3, v.1 - u.1 = hexagonalStep i) ∨
  (v.2 = false ∧ u.2 = true ∧ ∃ i : Fin 3, u.1 - v.1 = hexagonalStep i)

lemma hexagonalAdj_symm : Std.Symm hexagonalAdj := by
  constructor
  intro u v h
  exact h.symm

lemma hexagonalAdj_irrefl : Std.Irrefl hexagonalAdj := by
  constructor
  rintro u (⟨hf, ht, _⟩ | ⟨hf, ht, _⟩) <;> simp_all

/-- The hexagonal (honeycomb) lattice as a simple graph. -/
def hexagonalGraph : SimpleGraph HexVertex where
  Adj := hexagonalAdj
  symm := hexagonalAdj_symm
  loopless := hexagonalAdj_irrefl

@[simp] lemma hexagonalGraph_adj (u v : HexVertex) :
    hexagonalGraph.Adj u v ↔ hexagonalAdj u v := Iff.rfl

/-- The `i`-th neighbor of a hexagonal-lattice vertex. -/
def hexagonalNeighbor (u : HexVertex) (i : Fin 3) : HexVertex :=
  if u.2 then (u.1 - hexagonalStep i, false) else (u.1 + hexagonalStep i, true)

lemma hexagonal_adj_neighbor (u : HexVertex) (i : Fin 3) :
    hexagonalGraph.Adj u (hexagonalNeighbor u i) := by
  rw [hexagonalGraph_adj]
  rcases h : u.2 with _ | _
  · left
    simp [hexagonalNeighbor, h]
  · right
    simp [hexagonalNeighbor, h]

lemma hexagonal_mem_candidates_of_adj {u v : HexVertex}
    (h : hexagonalGraph.Adj u v) :
    v ∈ Finset.univ.image (hexagonalNeighbor u) := by
  rw [hexagonalGraph_adj] at h
  rcases h with ⟨hu, hv, i, hi⟩ | ⟨hv, hu, i, hi⟩
  · rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · have hcoord : u.1 + hexagonalStep i = v.1 := by
        ext j
        have hj := congrFun hi j
        simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
        omega
      simpa [hexagonalNeighbor, hu] using hcoord
    · simp [hexagonalNeighbor, hu, hv]
  · rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · have hcoord : u.1 - hexagonalStep i = v.1 := by
        ext j
        have hj := congrFun hi j
        simp only [Pi.sub_apply] at hj ⊢
        omega
      simpa [hexagonalNeighbor, hu] using hcoord
    · simp [hexagonalNeighbor, hu, hv]

/-- The hexagonal lattice is locally finite (degree three). -/
noncomputable instance hexagonalGraph_locallyFinite :
    SimpleGraph.LocallyFinite hexagonalGraph := fun u =>
  Fintype.ofFinset (Finset.univ.image (hexagonalNeighbor u)) (by
    intro v
    rw [SimpleGraph.mem_neighborSet]
    exact ⟨(fun hv => by
        rw [Finset.mem_image] at hv
        obtain ⟨i, _, rfl⟩ := hv
        exact hexagonal_adj_neighbor u i),
      hexagonal_mem_candidates_of_adj⟩)

/-- Translation of the hexagonal lattice by `z`, preserving sublattice labels. -/
def hexTranslate (z : Site 2) : HexVertex ≃ HexVertex where
  toFun u := (u.1 + z, u.2)
  invFun u := (u.1 - z, u.2)
  left_inv := by intro u; ext <;> simp
  right_inv := by intro u; ext <;> simp

@[simp] lemma hexTranslate_apply (z : Site 2) (u : HexVertex) :
    hexTranslate z u = (u.1 + z, u.2) := rfl

lemma hexTranslate_zero : hexTranslate 0 = Equiv.refl HexVertex := by
  ext u <;> simp

lemma hexTranslate_add (z w : Site 2) (u : HexVertex) :
    hexTranslate (z + w) u = hexTranslate w (hexTranslate z u) := by
  ext <;> simp [add_assoc]

lemma hexagonal_shift_adj (z : Site 2) (u v : HexVertex) :
    hexagonalGraph.Adj (hexTranslate z u) (hexTranslate z v) ↔
      hexagonalGraph.Adj u v := by
  simp only [hexagonalGraph_adj, hexagonalAdj, hexTranslate_apply]
  have huv : (v.1 + z) - (u.1 + z) = v.1 - u.1 := by abel
  have hvu : (u.1 + z) - (v.1 + z) = u.1 - v.1 := by abel
  rw [huv, hvu]

/-- The hexagonal lattice as a periodic graph, with a two-point fundamental domain. -/
noncomputable def hexagonal : PeriodicGraph HexVertex where
  graph := hexagonalGraph
  shift := hexTranslate
  shift_zero := hexTranslate_zero
  shift_add := hexTranslate_add
  shift_adj := hexagonal_shift_adj
  fundamentalDomain := {(0, false), (0, true)}
  fundamentalDomain_nonempty := ⟨(0, false), by simp⟩
  covers v := ⟨v.1, (0, v.2), by rcases v with ⟨x, b⟩; cases b <;> simp,
    by rcases v with ⟨x, b⟩; ext <;> simp⟩
  locallyFinite := hexagonalGraph_locallyFinite

end PeriodicPlanar
end FK
end StatMech
