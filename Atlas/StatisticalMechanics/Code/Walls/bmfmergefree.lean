/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Walls.bdecdecouple

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000




def bmf_a₁ : Site 2 := ![1, 0]

def bmf_a₂ : Site 2 := ![0, 1]

def bmf_a₃ : Site 2 := ![-1, 0]

def bmf_b₁ : Site 2 := ![2, 0]

def bmf_b₂ : Site 2 := ![0, 2]

def bmf_b₃ : Site 2 := ![-2, 0]


def bmf_I : Finset (Sym2 (Site 2)) :=
  {s(bmf_a₁, bmf_b₁), s(bmf_a₂, bmf_b₂), s(bmf_a₃, bmf_b₃)}


def bmf_η₀ : ConfigSpace ↥bmf_I := fun _ => true



def bmf_X : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω |
    ((cluster 2 (removeSite 0 ω) bmf_b₁).Infinite ∧
      (cluster 2 (removeSite 0 ω) bmf_b₂).Infinite ∧
      (cluster 2 (removeSite 0 ω) bmf_b₃).Infinite) ∧
    (¬ Connected 2 (removeSite 0 ω) bmf_b₁ bmf_b₂ ∧
      ¬ Connected 2 (removeSite 0 ω) bmf_b₁ bmf_b₃ ∧
      ¬ Connected 2 (removeSite 0 ω) bmf_b₂ bmf_b₃)}




theorem bmf_o_ne_a₁ : (0 : Site 2) ≠ bmf_a₁ := by
  intro h; have := congrFun h 0; simp [bmf_a₁] at this
theorem bmf_o_ne_a₂ : (0 : Site 2) ≠ bmf_a₂ := by
  intro h; have := congrFun h 1; simp [bmf_a₂] at this
theorem bmf_o_ne_a₃ : (0 : Site 2) ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₃] at this
theorem bmf_o_ne_b₁ : (0 : Site 2) ≠ bmf_b₁ := by
  intro h; have := congrFun h 0; simp [bmf_b₁] at this
theorem bmf_o_ne_b₂ : (0 : Site 2) ≠ bmf_b₂ := by
  intro h; have := congrFun h 1; simp [bmf_b₂] at this
theorem bmf_o_ne_b₃ : (0 : Site 2) ≠ bmf_b₃ := by
  intro h; have := congrFun h 0; simp [bmf_b₃] at this


theorem bmf_a₁_ne_a₂ : bmf_a₁ ≠ bmf_a₂ := by
  intro h; have := congrFun h 0; simp [bmf_a₁, bmf_a₂] at this
theorem bmf_a₁_ne_a₃ : bmf_a₁ ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₁, bmf_a₃] at this
theorem bmf_a₂_ne_a₃ : bmf_a₂ ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₂, bmf_a₃] at this


theorem bmf_adj_o_a₁ : (hypercubicLattice 2).Adj 0 bmf_a₁ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₁, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide
theorem bmf_adj_o_a₂ : (hypercubicLattice 2).Adj 0 bmf_a₂ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₂, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide
theorem bmf_adj_o_a₃ : (hypercubicLattice 2).Adj 0 bmf_a₃ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₃, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide


theorem bmf_adj_a₁_b₁ : (hypercubicLattice 2).Adj bmf_a₁ bmf_b₁ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₁, bmf_b₁,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide
theorem bmf_adj_a₂_b₂ : (hypercubicLattice 2).Adj bmf_a₂ bmf_b₂ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₂, bmf_b₂,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide
theorem bmf_adj_a₃_b₃ : (hypercubicLattice 2).Adj bmf_a₃ bmf_b₃ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₃, bmf_b₃,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide


theorem bmf_o_notMem_e₁ : (0 : Site 2) ∉ s(bmf_a₁, bmf_b₁) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₁, bmf_o_ne_b₁⟩
theorem bmf_o_notMem_e₂ : (0 : Site 2) ∉ s(bmf_a₂, bmf_b₂) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₂, bmf_o_ne_b₂⟩
theorem bmf_o_notMem_e₃ : (0 : Site 2) ∉ s(bmf_a₃, bmf_b₃) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₃, bmf_o_ne_b₃⟩




theorem bmf_corridor_open (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    ω s(bmf_a₁, bmf_b₁) = true ∧ ω s(bmf_a₂, bmf_b₂) = true ∧
      ω s(bmf_a₃, bmf_b₃) = true := by
  rw [mem_cylinder, Set.mem_singleton_iff] at hω
  have h1 : bmf_I.restrict ω ⟨s(bmf_a₁, bmf_b₁), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₁, bmf_b₁), by simp [bmf_I]⟩ := by rw [hω]
  have h2 : bmf_I.restrict ω ⟨s(bmf_a₂, bmf_b₂), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₂, bmf_b₂), by simp [bmf_I]⟩ := by rw [hω]
  have h3 : bmf_I.restrict ω ⟨s(bmf_a₃, bmf_b₃), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₃, bmf_b₃), by simp [bmf_I]⟩ := by rw [hω]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.restrict, bmf_η₀] using h1
  · simpa [Finset.restrict, bmf_η₀] using h2
  · simpa [Finset.restrict, bmf_η₀] using h3


theorem bmf_conn_a₁_b₁ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₁ bmf_b₁ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₁_b₁, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₁]
  exact (bmf_corridor_open ω hω).1
theorem bmf_conn_a₂_b₂ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₂ bmf_b₂ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₂_b₂, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₂]
  exact (bmf_corridor_open ω hω).2.1
theorem bmf_conn_a₃_b₃ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₃ bmf_b₃ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₃_b₃, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₃]
  exact (bmf_corridor_open ω hω).2.2











theorem bmf_hgeo :
    cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X
      ⊆ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ := by
  rintro ω ⟨hcyl, hX⟩
  obtain ⟨⟨hb1inf, hb2inf, hb3inf⟩, hb12, hb13, hb23⟩ := hX
  have c1 := bmf_conn_a₁_b₁ ω hcyl
  have c2 := bmf_conn_a₂_b₂ ω hcyl
  have c3 := bmf_conn_a₃_b₃ ω hcyl
  refine ⟨⟨bmf_a₁_ne_a₂, bmf_a₁_ne_a₃, bmf_a₂_ne_a₃⟩,
    ⟨bmf_adj_o_a₁, bmf_adj_o_a₂, bmf_adj_o_a₃⟩, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · rw [cluster_eq_of_connected c1]; exact hb1inf
    · rw [cluster_eq_of_connected c2]; exact hb2inf
    · rw [cluster_eq_of_connected c3]; exact hb3inf
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact hb12 (c1.symm.trans (h.trans c2))
    · intro h; exact hb13 (c1.symm.trans (h.trans c3))
    · intro h; exact hb23 (c2.symm.trans (h.trans c3))











theorem bmf_precursorPos_of_residues (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X)
        = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)))
          * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X)
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃) :=
  bdec_precursorPos_of_decoupled p hp1 hp0 hplt bmf_a₁ bmf_a₂ bmf_a₃ bmf_I bmf_η₀ bmf_X
    hindep hXpos bmf_hgeo










def bmf_R₁ : Set (Site 2) := {x | x 1 = 0 ∧ 2 ≤ x 0}

def bmf_R₂ : Set (Site 2) := {x | x 0 = 0 ∧ 2 ≤ x 1}

def bmf_R₃ : Set (Site 2) := {x | x 1 = 0 ∧ x 0 ≤ -2}


def bmf_OnRay (e : Sym2 (Site 2)) : Prop :=
  ∃ x y : Site 2, e = s(x, y) ∧
    ((x ∈ bmf_R₁ ∧ y ∈ bmf_R₁) ∨ (x ∈ bmf_R₂ ∧ y ∈ bmf_R₂) ∨ (x ∈ bmf_R₃ ∧ y ∈ bmf_R₃))

open Classical in

noncomputable def bmf_omegaTri : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if bmf_OnRay e then true else false

theorem bmf_omegaTri_true {e : Sym2 (Site 2)} : bmf_omegaTri e = true ↔ bmf_OnRay e := by
  unfold bmf_omegaTri; by_cases h : bmf_OnRay e <;> simp [h]



theorem bmf_R₁_notMem_R₂ {x : Site 2} (h : x ∈ bmf_R₁) : x ∉ bmf_R₂ := by
  rintro ⟨hx0, _⟩; exact absurd (hx0 ▸ h.2) (by norm_num)
theorem bmf_R₁_notMem_R₃ {x : Site 2} (h : x ∈ bmf_R₁) : x ∉ bmf_R₃ := by
  rintro ⟨_, hx0⟩; exact absurd (le_trans h.2 hx0) (by norm_num)
theorem bmf_R₂_notMem_R₁ {x : Site 2} (h : x ∈ bmf_R₂) : x ∉ bmf_R₁ :=
  fun h' => bmf_R₁_notMem_R₂ h' h
theorem bmf_R₂_notMem_R₃ {x : Site 2} (h : x ∈ bmf_R₂) : x ∉ bmf_R₃ := by
  rintro ⟨hx1, _⟩; exact absurd (hx1 ▸ h.2) (by norm_num)
theorem bmf_R₃_notMem_R₁ {x : Site 2} (h : x ∈ bmf_R₃) : x ∉ bmf_R₁ :=
  fun h' => bmf_R₁_notMem_R₃ h' h
theorem bmf_R₃_notMem_R₂ {x : Site 2} (h : x ∈ bmf_R₃) : x ∉ bmf_R₂ :=
  fun h' => bmf_R₂_notMem_R₃ h' h




theorem bmf_walk_invariant {ω : ConfigSpace (Sym2 (Site 2))} {S : Set (Site 2)}
    (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S)
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (hclosed a b hx hab)


theorem bmf_cluster_subset {ω : ConfigSpace (Sym2 (Site 2))} {S : Set (Site 2)} {b : Site 2}
    (hb : b ∈ S) (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S) :
    cluster 2 ω b ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 ω).Reachable b y)
  exact bmf_walk_invariant hclosed w hb




theorem bmf_R₁_closed (x y : Site 2) (hx : x ∈ bmf_R₁)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₁ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨_, hy'⟩ | ⟨hx', _⟩ | ⟨hx', _⟩
    · exact hy'
    · exact absurd hx' (bmf_R₁_notMem_R₂ hx)
    · exact absurd hx' (bmf_R₁_notMem_R₃ hx)
  · subst hxy; subst hyx
    rcases hcases with ⟨hy', _⟩ | ⟨_, hx'⟩ | ⟨_, hx'⟩
    · exact hy'
    · exact absurd hx' (bmf_R₁_notMem_R₂ hx)
    · exact absurd hx' (bmf_R₁_notMem_R₃ hx)

theorem bmf_R₂_closed (x y : Site 2) (hx : x ∈ bmf_R₂)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₂ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨_, hy'⟩ | ⟨hx', _⟩
    · exact absurd hx' (bmf_R₂_notMem_R₁ hx)
    · exact hy'
    · exact absurd hx' (bmf_R₂_notMem_R₃ hx)
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨hy', _⟩ | ⟨_, hx'⟩
    · exact absurd hx' (bmf_R₂_notMem_R₁ hx)
    · exact hy'
    · exact absurd hx' (bmf_R₂_notMem_R₃ hx)

theorem bmf_R₃_closed (x y : Site 2) (hx : x ∈ bmf_R₃)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₃ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨hx', _⟩ | ⟨_, hy'⟩
    · exact absurd hx' (bmf_R₃_notMem_R₁ hx)
    · exact absurd hx' (bmf_R₃_notMem_R₂ hx)
    · exact hy'
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨_, hx'⟩ | ⟨hy', _⟩
    · exact absurd hx' (bmf_R₃_notMem_R₁ hx)
    · exact absurd hx' (bmf_R₃_notMem_R₂ hx)
    · exact hy'



theorem bmf_b₁_mem_R₁ : bmf_b₁ ∈ bmf_R₁ := ⟨by simp [bmf_b₁], by simp [bmf_b₁]⟩
theorem bmf_b₂_mem_R₂ : bmf_b₂ ∈ bmf_R₂ := ⟨by simp [bmf_b₂], by simp [bmf_b₂]⟩
theorem bmf_b₃_mem_R₃ : bmf_b₃ ∈ bmf_R₃ := ⟨by simp [bmf_b₃], by simp [bmf_b₃]⟩




theorem bmf_b₁_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₁ ![2 + (k : ℤ), 0] := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero, bmf_b₁]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![2 + (n : ℤ), 0] : Site 2) ∈ bmf_R₁ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hB : (![2 + ((n : ℤ) + 1), 0] : Site 2) ∈ bmf_R₁ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![2 + (n : ℤ), 0]) (![2 + ((n : ℤ) + 1), 0]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![2 + (n : ℤ), 0] : Site 2), (![2 + ((n : ℤ) + 1), 0] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 0; simp only [Pi.zero_apply, Matrix.cons_val_zero] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]; exact ⟨_, _, rfl, Or.inl ⟨hA, hB⟩⟩⟩)

theorem bmf_b₁_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₁).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![2 + (k : ℤ), 0] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 0
    simp only [Matrix.cons_val_zero] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₁_conn_ray k)


theorem bmf_b₂_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₂ ![0, 2 + (k : ℤ)] := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero, bmf_b₂]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![0, 2 + (n : ℤ)] : Site 2) ∈ bmf_R₂ :=
      ⟨by simp, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; omega⟩
    have hB : (![0, 2 + ((n : ℤ) + 1)] : Site 2) ∈ bmf_R₂ :=
      ⟨by simp, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![0, 2 + (n : ℤ)]) (![0, 2 + ((n : ℤ) + 1)]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![0, 2 + (n : ℤ)] : Site 2), (![0, 2 + ((n : ℤ) + 1)] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 1
          simp only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]
      exact ⟨_, _, rfl, Or.inr (Or.inl ⟨hA, hB⟩)⟩⟩)

theorem bmf_b₂_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![0, 2 + (k : ℤ)] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₂_conn_ray k)


theorem bmf_b₃_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₃ ![-2 - (k : ℤ), 0] := by
  induction k with
  | zero => simp only [Nat.cast_zero, sub_zero, bmf_b₃]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![-2 - (n : ℤ), 0] : Site 2) ∈ bmf_R₃ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hB : (![-2 - ((n : ℤ) + 1), 0] : Site 2) ∈ bmf_R₃ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![-2 - (n : ℤ), 0]) (![-2 - ((n : ℤ) + 1), 0]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![-2 - (n : ℤ), 0] : Site 2), (![-2 - ((n : ℤ) + 1), 0] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 0; simp only [Pi.zero_apply, Matrix.cons_val_zero] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]
      exact ⟨_, _, rfl, Or.inr (Or.inr ⟨hA, hB⟩)⟩⟩)

theorem bmf_b₃_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₃).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![-2 - (k : ℤ), 0] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 0
    simp only [Matrix.cons_val_zero] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₃_conn_ray k)









theorem bmf_omegaTri_mem_X : bmf_omegaTri ∈ bmf_X := by
  have hc1 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₁ ⊆ bmf_R₁ :=
    bmf_cluster_subset bmf_b₁_mem_R₁ bmf_R₁_closed
  have hc2 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂ ⊆ bmf_R₂ :=
    bmf_cluster_subset bmf_b₂_mem_R₂ bmf_R₂_closed
  have hc3 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₃ ⊆ bmf_R₃ :=
    bmf_cluster_subset bmf_b₃_mem_R₃ bmf_R₃_closed
  refine ⟨⟨bmf_b₁_cluster_infinite, bmf_b₂_cluster_infinite, bmf_b₃_cluster_infinite⟩,
    ?_, ?_, ?_⟩
  · intro h; exact bmf_R₁_notMem_R₂ (hc1 (mem_cluster.mpr h)) bmf_b₂_mem_R₂
  · intro h; exact bmf_R₁_notMem_R₃ (hc1 (mem_cluster.mpr h)) bmf_b₃_mem_R₃
  · intro h; exact bmf_R₂_notMem_R₃ (hc2 (mem_cluster.mpr h)) bmf_b₃_mem_R₃


theorem bmf_X_nonempty : bmf_X.Nonempty := ⟨bmf_omegaTri, bmf_omegaTri_mem_X⟩

end StatMech.Walls
