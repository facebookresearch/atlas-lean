/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FK.InfiniteVolume
import Code.Lattice.PlanarTopology

open Finset Set SimpleGraph
open MeasureTheory
namespace StatMech
namespace FK
namespace PeriodicPlanar

open Lattice


def siteTranslate (z : Site 2) : Site 2 ≃ Site 2 where
  toFun x := x + z
  invFun x := x - z
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext i; simp

@[simp] theorem siteTranslate_apply (z x : Site 2) : siteTranslate z x = x + z := rfl




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



noncomputable def PeriodicGraph.orbitBox (P : PeriodicGraph V) (n : ℕ) : Finset V :=
  (((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain)).image
    (fun zu => P.shift zu.1 zu.2)

theorem PeriodicGraph.mem_orbitBox_iff (P : PeriodicGraph V) (n : ℕ) (v : V) :
    v ∈ P.orbitBox n ↔
      ∃ z : Site 2, z ∈ box 2 n ∧ ∃ u ∈ P.fundamentalDomain, P.shift z u = v := by
  simp only [PeriodicGraph.orbitBox, Finset.mem_image, Finset.mem_product,
    Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨z, u⟩, ⟨hz, hu⟩, huv⟩
    exact ⟨z, hz, u, hu, huv⟩
  · rintro ⟨z, hz, u, hu, huv⟩
    exact ⟨(z, u), ⟨hz, hu⟩, huv⟩


theorem PeriodicGraph.orbitBox_mono (P : PeriodicGraph V) : Monotone P.orbitBox := by
  intro m n hmn v hv
  rw [P.mem_orbitBox_iff] at hv ⊢
  obtain ⟨z, hz, u, hu, rfl⟩ := hv
  exact ⟨z, box_mono 2 hmn hz, u, hu, rfl⟩


theorem PeriodicGraph.mem_orbitBox_of_eventually (P : PeriodicGraph V) (v : V) :
    ∃ n, v ∈ P.orbitBox n := by
  obtain ⟨z, u, hu, rfl⟩ := P.covers v
  have hzUnion : z ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
  obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hzUnion
  exact ⟨n, (P.mem_orbitBox_iff n _).2 ⟨z, hz, u, hu, rfl⟩⟩


abbrev PeriodicGraph.OrbitVertex (P : PeriodicGraph V) (n : ℕ) :=
  {v : V // v ∈ P.orbitBox n}

noncomputable instance PeriodicGraph.instFintypeOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : Fintype (P.OrbitVertex n) :=
  Fintype.ofFinset (P.orbitBox n) (fun _ => Iff.rfl)

instance PeriodicGraph.instDecidableEqOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : DecidableEq (P.OrbitVertex n) :=
  Subtype.instDecidableEq


def PeriodicGraph.orbitGraph (P : PeriodicGraph V) (n : ℕ) :
    SimpleGraph (P.OrbitVertex n) :=
  SimpleGraph.comap Subtype.val P.graph

noncomputable instance PeriodicGraph.instDecidableRelOrbitGraph
    (P : PeriodicGraph V) (n : ℕ) : DecidableRel (P.orbitGraph n).Adj :=
  Classical.decRel _


def PeriodicGraph.orbitBoundary (P : PeriodicGraph V) (n : ℕ)
    (v : P.OrbitVertex n) : Prop :=
  (v : V) ∉ P.orbitBox (n - 1)

noncomputable instance PeriodicGraph.instDecidablePredOrbitBoundary
    (P : PeriodicGraph V) (n : ℕ) : DecidablePred (P.orbitBoundary n) :=
  fun _ => Classical.dec _


noncomputable def PeriodicGraph.freeFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.fkPMF (P.orbitGraph n) hp hp1 hq


noncomputable def PeriodicGraph.wiredFinitePMF (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 (P.OrbitVertex n))) :=
  FK.wiredFkPMF (P.orbitGraph n) (P.orbitBoundary n) hp hp1 hq




def PeriodicGraph.edgeIncl (P : PeriodicGraph V) (n : ℕ) :
    Sym2 (P.OrbitVertex n) → Sym2 V :=
  Sym2.map (Subtype.val : P.OrbitVertex n → V)

theorem PeriodicGraph.edgeIncl_injective (P : PeriodicGraph V) (n : ℕ) :
    Function.Injective (P.edgeIncl n) :=
  Sym2.map.injective Subtype.val_injective



noncomputable def PeriodicGraph.extendEdge (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n))) : ConfigSpace (Sym2 V) :=
  fun e => if h : e ∈ Set.range (P.edgeIncl n) then omega h.choose else false

@[simp] theorem PeriodicGraph.extendEdge_edgeIncl (P : PeriodicGraph V) (n : ℕ)
    (omega : ConfigSpace (Sym2 (P.OrbitVertex n)))
    (e : Sym2 (P.OrbitVertex n)) :
    P.extendEdge n omega (P.edgeIncl n e) = omega e := by
  unfold PeriodicGraph.extendEdge
  have hmem : P.edgeIncl n e ∈ Set.range (P.edgeIncl n) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact P.edgeIncl_injective n hmem.choose_spec

theorem PeriodicGraph.monotone_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Monotone (P.extendEdge n) := by
  intro omega eta home e
  unfold PeriodicGraph.extendEdge
  split
  · exact home _
  · exact le_refl false

theorem PeriodicGraph.measurable_extendEdge (P : PeriodicGraph V) (n : ℕ) :
    Measurable (P.extendEdge n) :=
  Measurable.of_discrete



noncomputable def PeriodicGraph.freeFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.freeFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    MeasureTheory.Measure.isProbabilityMeasure_map
      (P.measurable_extendEdge n).aemeasurable⟩



noncomputable def PeriodicGraph.wiredFiniteMeasure (P : PeriodicGraph V) (n : ℕ)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  ⟨((P.wiredFinitePMF n hp hp1 hq).toMeasure).map (P.extendEdge n),
    MeasureTheory.Measure.isProbabilityMeasure_map
      (P.measurable_extendEdge n).aemeasurable⟩

section Countable

variable [Countable V]



noncomputable def PeriodicGraph.freeInfiniteVolume (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (prokhorov_seq_compact (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose

theorem PeriodicGraph.freeInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.freeFiniteMeasure (phi n) hp hp1 hq)
        (P.freeInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩



noncomputable def PeriodicGraph.wiredInfiniteVolume (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ProbabilityMeasure (ConfigSpace (Sym2 V)) :=
  (prokhorov_seq_compact (fun n => P.wiredFiniteMeasure n hp hp1 hq)).choose

theorem PeriodicGraph.wiredInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.wiredFiniteMeasure (phi n) hp hp1 hq)
        (P.wiredInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact (fun n => P.wiredFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩

end Countable



private theorem siteTranslate_zero : siteTranslate (0 : Site 2) = Equiv.refl (Site 2) := by
  ext x i
  simp

private theorem siteTranslate_add (z w v : Site 2) :
    siteTranslate (z + w) v = siteTranslate w (siteTranslate z v) := by
  ext i
  simp [add_assoc]

private theorem square_shift_adj (z x y : Site 2) :
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




def triangularStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![-1, 1]] i

theorem triangularStep_ne_zero (i : Fin 3) : triangularStep i ≠ 0 := by
  fin_cases i <;> intro h
  · have := congrFun h 0
    norm_num [triangularStep] at this
  · have := congrFun h 1
    norm_num [triangularStep] at this
  · have := congrFun h 0
    norm_num [triangularStep] at this


def triangularAdj (x y : Site 2) : Prop :=
  ∃ i : Fin 3, y - x = triangularStep i ∨ x - y = triangularStep i

private theorem triangularAdj_symm : Symmetric triangularAdj := by
  rintro x y ⟨i, h⟩
  exact ⟨i, h.symm⟩

private theorem triangularAdj_irrefl : Std.Irrefl triangularAdj := by
  constructor
  rintro x ⟨i, h | h⟩
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm


def triangularGraph : SimpleGraph (Site 2) where
  Adj := triangularAdj
  symm := triangularAdj_symm
  loopless := triangularAdj_irrefl

@[simp] theorem triangularGraph_adj (x y : Site 2) :
    triangularGraph.Adj x y ↔ triangularAdj x y := Iff.rfl

def triangularNeighbor (x : Site 2) (ib : Fin 3 × Bool) : Site 2 :=
  if ib.2 then x + triangularStep ib.1 else x - triangularStep ib.1

theorem triangular_adj_neighbor (x : Site 2) (ib : Fin 3 × Bool) :
    triangularGraph.Adj x (triangularNeighbor x ib) := by
  rcases ib with ⟨i, b⟩
  rw [triangularGraph_adj]
  rcases b with _ | _
  · exact ⟨i, Or.inr (by simp [triangularNeighbor])⟩
  · exact ⟨i, Or.inl (by simp [triangularNeighbor])⟩

theorem triangular_mem_candidates_of_adj {x y : Site 2}
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

private theorem triangular_shift_adj (z x y : Site 2) :
    triangularGraph.Adj (siteTranslate z x) (siteTranslate z y) ↔
      triangularGraph.Adj x y := by
  simp only [triangularGraph_adj, triangularAdj, siteTranslate_apply]
  have hyx : (y + z) - (x + z) = y - x := by abel
  have hxy : (x + z) - (y + z) = x - y := by abel
  rw [hyx, hxy]


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





abbrev HexVertex := Site 2 × Bool


def hexagonalStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![1, 1]] i

def hexagonalAdj (u v : HexVertex) : Prop :=
  (u.2 = false ∧ v.2 = true ∧ ∃ i : Fin 3, v.1 - u.1 = hexagonalStep i) ∨
  (v.2 = false ∧ u.2 = true ∧ ∃ i : Fin 3, u.1 - v.1 = hexagonalStep i)

private theorem hexagonalAdj_symm : Symmetric hexagonalAdj := by
  intro u v h
  exact h.symm

private theorem hexagonalAdj_irrefl : Std.Irrefl hexagonalAdj := by
  constructor
  rintro u (⟨hf, ht, _⟩ | ⟨hf, ht, _⟩) <;> simp_all


def hexagonalGraph : SimpleGraph HexVertex where
  Adj := hexagonalAdj
  symm := hexagonalAdj_symm
  loopless := hexagonalAdj_irrefl

@[simp] theorem hexagonalGraph_adj (u v : HexVertex) :
    hexagonalGraph.Adj u v ↔ hexagonalAdj u v := Iff.rfl

def hexagonalNeighbor (u : HexVertex) (i : Fin 3) : HexVertex :=
  if u.2 then (u.1 - hexagonalStep i, false) else (u.1 + hexagonalStep i, true)

theorem hexagonal_adj_neighbor (u : HexVertex) (i : Fin 3) :
    hexagonalGraph.Adj u (hexagonalNeighbor u i) := by
  rw [hexagonalGraph_adj]
  rcases h : u.2 with _ | _
  · left
    simp [hexagonalNeighbor, h]
  · right
    simp [hexagonalNeighbor, h]

theorem hexagonal_mem_candidates_of_adj {u v : HexVertex}
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


def hexTranslate (z : Site 2) : HexVertex ≃ HexVertex where
  toFun u := (u.1 + z, u.2)
  invFun u := (u.1 - z, u.2)
  left_inv := by intro u; ext <;> simp
  right_inv := by intro u; ext <;> simp

@[simp] theorem hexTranslate_apply (z : Site 2) (u : HexVertex) :
    hexTranslate z u = (u.1 + z, u.2) := rfl

private theorem hexTranslate_zero : hexTranslate 0 = Equiv.refl HexVertex := by
  ext u <;> simp

private theorem hexTranslate_add (z w : Site 2) (u : HexVertex) :
    hexTranslate (z + w) u = hexTranslate w (hexTranslate z u) := by
  ext <;> simp [add_assoc]

private theorem hexagonal_shift_adj (z : Site 2) (u v : HexVertex) :
    hexagonalGraph.Adj (hexTranslate z u) (hexTranslate z v) ↔
      hexagonalGraph.Adj u v := by
  simp only [hexagonalGraph_adj, hexagonalAdj, hexTranslate_apply]
  have huv : (v.1 + z) - (u.1 + z) = v.1 - u.1 := by abel
  have hvu : (u.1 + z) - (v.1 + z) = u.1 - v.1 := by abel
  rw [huv, hvu]


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
