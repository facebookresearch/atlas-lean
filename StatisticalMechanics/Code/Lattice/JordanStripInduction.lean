/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Lattice.CrossingParity
import Code.RSW.Defs
import Code.Universality.HVIntersection
import Code.Lattice.ArcSides
import Code.Lattice.TwoPathsCrossWinding

open Set SimpleGraph MeasureTheory

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality







theorem jsi_adj_cases (u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    (u 1 = v 1 ∧ (u 0 - v 0 = 1 ∨ u 0 - v 0 = -1)) ∨
    (u 0 = v 0 ∧ (u 1 - v 1 = 1 ∨ u 1 - v 1 = -1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((u 0 - v 0).natAbs = 1 ∧ (u 1 - v 1).natAbs = 0) ∨
             ((u 0 - v 0).natAbs = 0 ∧ (u 1 - v 1).natAbs = 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left; exact ⟨by omega, by omega⟩
  · right; exact ⟨by omega, by omega⟩


def jsi_cell (k r : ℤ) : Site 2 := ![k, r]

@[simp] theorem jsi_cell_0 (k r : ℤ) : jsi_cell k r 0 = k := rfl
@[simp] theorem jsi_cell_1 (k r : ℤ) : jsi_cell k r 1 = r := rfl


theorem jsi_cell_eq (k r k' r' : ℤ) : jsi_cell k r = jsi_cell k' r' ↔ k = k' ∧ r = r' := by
  constructor
  · intro h
    exact ⟨by have := congrFun h 0; simpa using this, by have := congrFun h 1; simpa using this⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]


@[simp] theorem jsi_cell_mem_rect (k r α β c d : ℤ) :
    jsi_cell k r ∈ rect α β c d ↔ α ≤ k ∧ k ≤ β ∧ c ≤ r ∧ r ≤ d := by
  simp [rect, jsi_cell]


theorem jsi_vstep_adj (k r : ℤ) : (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k (r + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [jsi_cell]



theorem jsi_hstep_adj (k k' r : ℤ) (h : k - k' = 1 ∨ k - k' = -1) :
    (hypercubicLattice 2).Adj (jsi_cell k r) (jsi_cell k' r) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [jsi_cell]; omega














structure JsiRowArc (P : Set (Site 2)) (m m' c d : ℤ) where
  
  col : ℤ → ℤ
  
  band_lo : ∀ r, c ≤ r → r ≤ d → m ≤ col r
  
  band_hi : ∀ r, c ≤ r → r ≤ d → col r ≤ m'
  
  shift : ∀ r, c ≤ r → r < d →
    col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1
  
  on_arc : ∀ z : Site 2, c ≤ z 1 → z 1 ≤ d → z 0 = col (z 1) → m ≤ z 0 → z 0 ≤ m' → z ∈ P




theorem jsi_col_consecutive {P : Set (Site 2)} {m m' c d : ℤ} (A : JsiRowArc P m m' c d)
    (r s : ℤ) (hr : c ≤ r) (hrd : r ≤ d) (hs : c ≤ s) (hsd : s ≤ d)
    (hrs : r - s = 1 ∨ r - s = -1) :
    -1 ≤ A.col r - A.col s ∧ A.col r - A.col s ≤ 1 := by
  rcases hrs with h | h
  · have hse : s + 1 = r := by omega
    have hsh := A.shift s hs (by omega); rw [hse] at hsh; omega
  · have hre : r + 1 = s := by omega
    have hsh := A.shift r hr (by omega); rw [hre] at hsh; omega






def jsi_leftRegion (col : ℤ → ℤ) (α β c d : ℤ) : Set (Site 2) :=
  {z | z ∈ rect α β c d ∧ z 0 ≤ col (z 1)}

@[simp] theorem jsi_mem_leftRegion (col : ℤ → ℤ) (α β c d : ℤ) (z : Site 2) :
    z ∈ jsi_leftRegion col α β c d ↔ z ∈ rect α β c d ∧ z 0 ≤ col (z 1) := Iff.rfl




def jsi_leftRegionLt (col : ℤ → ℤ) (α β c d : ℤ) : Set (Site 2) :=
  {z | z ∈ rect α β c d ∧ z 0 < col (z 1)}

@[simp] theorem jsi_mem_leftRegionLt (col : ℤ → ℤ) (α β c d : ℤ) (z : Site 2) :
    z ∈ jsi_leftRegionLt col α β c d ↔ z ∈ rect α β c d ∧ z 0 < col (z 1) := Iff.rfl


















theorem jsi_arcSeparatingSet {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d := by
  classical
  refine ⟨jsi_leftRegion A.col α β c d, ?_, ?_, ?_⟩
  · 
    intro z hz hzα
    refine ⟨hz, ?_⟩
    rw [hzα]
    have hzrow := mem_rect.mp hz
    exact le_trans hαm (A.band_lo (z 1) hzrow.2.2.1 hzrow.2.2.2)
  · 
    intro z hz hzβ
    rw [jsi_mem_leftRegion]
    push Not
    intro _
    rw [hzβ]
    have hzrow := mem_rect.mp hz
    have hb : A.col (z 1) ≤ m' := A.band_hi (z 1) hzrow.2.2.1 hzrow.2.2.2
    omega
  · 
    intro u v hu hv hadj hbd
    rw [bdEdge_mk] at hbd
    have hurow := mem_rect.mp hu
    have hvrow := mem_rect.mp hv
    by_cases huS : u ∈ jsi_leftRegion A.col α β c d
    · 
      have hvS : v ∉ jsi_leftRegion A.col α β c d := hbd.mp huS
      have hu_le : u 0 ≤ A.col (u 1) := huS.2
      have hv_gt : A.col (v 1) < v 0 := by
        by_contra h; push Not at h; exact hvS ⟨hv, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        left
        have hcr : u 0 = A.col (u 1) := by
          have hadj' := hypercubicLattice_adj 2 u v
          rw [hadj', Fin.sum_univ_two] at hadj
          rw [← hrow] at hv_gt; omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
      · 
        left
        have hcc := jsi_col_consecutive A (u 1) (v 1) hurow.2.2.1 hurow.2.2.2
          hvrow.2.2.1 hvrow.2.2.2 hrowdiff
        rw [← hcoleq] at hv_gt
        have hcr : u 0 = A.col (u 1) := by omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
    · 
      have hvS : v ∈ jsi_leftRegion A.col α β c d := by
        by_contra h; exact huS (hbd.mpr h)
      have hv_le : v 0 ≤ A.col (v 1) := hvS.2
      have hu_gt : A.col (u 1) < u 0 := by
        by_contra h; push Not at h; exact huS ⟨hu, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        right
        have hcr : v 0 = A.col (v 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          rw [hrow] at hu_gt; omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
      · 
        right
        have hcc := jsi_col_consecutive A (v 1) (u 1) hvrow.2.2.1 hvrow.2.2.2
          hurow.2.2.1 hurow.2.2.2 (by omega)
        rw [hcoleq] at hu_gt
        have hcr : v 0 = A.col (v 1) := by omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)







theorem jsi_arcSeparatingSetLt {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α < m) (hm'β : m' ≤ β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d := by
  classical
  refine ⟨jsi_leftRegionLt A.col α β c d, ?_, ?_, ?_⟩
  · 
    intro z hz hzα
    refine ⟨hz, ?_⟩
    rw [hzα]
    have hzrow := mem_rect.mp hz
    exact lt_of_lt_of_le hαm (A.band_lo (z 1) hzrow.2.2.1 hzrow.2.2.2)
  · 
    intro z hz hzβ
    rw [jsi_mem_leftRegionLt]
    push Not
    intro _
    rw [hzβ]
    have hzrow := mem_rect.mp hz
    have hb : A.col (z 1) ≤ m' := A.band_hi (z 1) hzrow.2.2.1 hzrow.2.2.2
    omega
  · 
    intro u v hu hv hadj hbd
    rw [bdEdge_mk] at hbd
    have hurow := mem_rect.mp hu
    have hvrow := mem_rect.mp hv
    by_cases huS : u ∈ jsi_leftRegionLt A.col α β c d
    · 
      have hvS : v ∉ jsi_leftRegionLt A.col α β c d := hbd.mp huS
      have hu_lt : u 0 < A.col (u 1) := huS.2
      have hv_ge : A.col (v 1) ≤ v 0 := by
        by_contra h; push Not at h; exact hvS ⟨hv, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        right
        have hce : A.col (u 1) = A.col (v 1) := by rw [hrow]
        have hcr : v 0 = A.col (v 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
      · 
        right
        have hcc := jsi_col_consecutive A (v 1) (u 1) hvrow.2.2.1 hvrow.2.2.2
          hurow.2.2.1 hurow.2.2.2 (by omega)
        rw [hcoleq] at hu_lt
        have hcr : v 0 = A.col (v 1) := by omega
        exact A.on_arc v hvrow.2.2.1 hvrow.2.2.2 hcr
          (le_trans (A.band_lo (v 1) hvrow.2.2.1 hvrow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (v 1) hvrow.2.2.1 hvrow.2.2.2)
    · 
      have hvS : v ∈ jsi_leftRegionLt A.col α β c d := by
        by_contra h; exact huS (hbd.mpr h)
      have hv_lt : v 0 < A.col (v 1) := hvS.2
      have hu_ge : A.col (u 1) ≤ u 0 := by
        by_contra h; push Not at h; exact huS ⟨hu, h⟩
      rcases jsi_adj_cases u v hadj with ⟨hrow, _⟩ | ⟨hcoleq, hrowdiff⟩
      · 
        left
        have hce : A.col (u 1) = A.col (v 1) := by rw [hrow]
        have hcr : u 0 = A.col (u 1) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
          omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)
      · 
        left
        have hcc := jsi_col_consecutive A (u 1) (v 1) hurow.2.2.1 hurow.2.2.2
          hvrow.2.2.1 hvrow.2.2.2 hrowdiff
        rw [← hcoleq] at hv_lt
        have hcr : u 0 = A.col (u 1) := by omega
        exact A.on_arc u hurow.2.2.1 hurow.2.2.2 hcr
          (le_trans (A.band_lo (u 1) hurow.2.2.1 hurow.2.2.2) (le_of_eq hcr.symm))
          (hcr ▸ A.band_hi (u 1) hurow.2.2.1 hurow.2.2.2)












noncomputable def jsi_hconn (k k' r : ℤ) (h : k - k' = 1 ∨ k - k' = 0 ∨ k - k' = -1) :
    (hypercubicLattice 2).Walk (jsi_cell k r) (jsi_cell k' r) := by
  classical
  by_cases h0 : k = k'
  · exact (h0 ▸ SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (jsi_cell k r) (jsi_cell k' r))
  · exact SimpleGraph.Walk.cons (jsi_hstep_adj k k' r (by omega)) SimpleGraph.Walk.nil


theorem jsi_hconn_support (k k' r : ℤ) (h) (z : Site 2)
    (hz : z ∈ (jsi_hconn k k' r h).support) :
    z = jsi_cell k r ∨ z = jsi_cell k' r := by
  classical
  unfold jsi_hconn at hz
  by_cases h0 : k = k'
  · subst h0; simp only [dif_pos, SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    left; exact hz
  · simp only [dif_neg h0, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz





noncomputable def jsi_arcWalk (col : ℤ → ℤ)
    (hsh : ∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1)
    (c : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk (jsi_cell (col c) c) (jsi_cell (col (c + n)) (c + n))
  | 0 => (SimpleGraph.Walk.nil).copy rfl (by rw [jsi_cell_eq]; norm_num)
  | (n + 1) => by
      have prev := jsi_arcWalk col hsh c n
      have vstep := jsi_vstep_adj (col (c + (n : ℤ))) (c + (n : ℤ))
      have hc := jsi_hconn (col (c + (n : ℤ))) (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)
        (by have := hsh (c + (n : ℤ)); omega)
      have step : (hypercubicLattice 2).Walk (jsi_cell (col (c + (n : ℤ))) (c + (n : ℤ)))
                    (jsi_cell (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)) :=
        SimpleGraph.Walk.cons vstep hc
      refine (prev.append step).copy rfl ?_
      have heq : c + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [jsi_cell_eq]; exact ⟨by rw [heq], heq⟩


theorem jsi_arcWalk_zero (col : ℤ → ℤ) (hsh) (c : ℤ) :
    jsi_arcWalk col hsh c 0 = (SimpleGraph.Walk.nil).copy rfl (by rw [jsi_cell_eq]; norm_num) := rfl


theorem jsi_arcWalk_succ (col : ℤ → ℤ) (hsh) (c : ℤ) (n : ℕ) :
    jsi_arcWalk col hsh c (n + 1) =
      (((jsi_arcWalk col hsh c n).append
        (SimpleGraph.Walk.cons (jsi_vstep_adj (col (c + (n : ℤ))) (c + (n : ℤ)))
          (jsi_hconn (col (c + (n : ℤ))) (col (c + (n : ℤ) + 1)) (c + (n : ℤ) + 1)
            (by have := hsh (c + (n : ℤ)); omega)))).copy rfl (by
              have heq : c + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
              rw [jsi_cell_eq]; exact ⟨by rw [heq], heq⟩)) := rfl





theorem jsi_arcWalk_support_subset (P : Set (Site 2)) (col : ℤ → ℤ) (hsh) (c : ℤ) :
    (n : ℕ) →
    (hP : ∀ j : ℕ, j ≤ n → jsi_cell (col (c + j)) (c + j) ∈ P) →
    (hPc : ∀ j : ℕ, j < n → jsi_cell (col (c + j)) (c + j + 1) ∈ P) →
    (z : Site 2) → z ∈ (jsi_arcWalk col hsh c n).support → z ∈ P
  | 0, hP, _, z, hz => by
      rw [jsi_arcWalk_zero, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hz
      have h0 := hP 0 (le_refl 0)
      rw [hz]; simpa using h0
  | (n + 1), hP, hPc, z, hz => by
      rw [jsi_arcWalk_succ, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with h | h
      · exact jsi_arcWalk_support_subset P col hsh c n
          (fun j hj => hP j (by omega)) (fun j hj => hPc j (by omega)) z h
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h; simpa using hP n (by omega)
        · rcases jsi_hconn_support _ _ _ _ z h with h1 | h1
          · subst h1; simpa using hPc n (by omega)
          · subst h1
            have heq : (c : ℤ) + (n : ℤ) + 1 = c + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
            rw [(jsi_cell_eq _ _ _ _).mpr ⟨by rw [heq], heq⟩]; exact hP (n + 1) (le_refl _)









structure JsiMonotoneArc (P : Set (Site 2)) (m m' c d : ℤ) extends JsiRowArc P m m' c d where
  
  cd : c ≤ d
  
  shift_all : ∀ r : ℤ,
    col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1
  
  corner : ∀ z : Site 2, c ≤ z 1 → z 1 ≤ d → z 0 = col (z 1 - 1) →
    m ≤ z 0 → z 0 ≤ m' → z ∈ P






theorem jsi_monotoneArc_walk {P : Set (Site 2)} {m m' c d : ℤ} (A : JsiMonotoneArc P m m' c d) :
    ∃ (n : ℕ) (W : (hypercubicLattice 2).Walk (jsi_cell (A.col c) c) (jsi_cell (A.col (c + n)) (c + n))),
      c + (n : ℤ) = d ∧ (∀ z ∈ W.support, z ∈ P) := by
  classical
  have hcd : c ≤ d := A.cd
  
  refine ⟨(d - c).toNat, jsi_arcWalk A.col A.shift_all c (d - c).toNat, by omega, ?_⟩
  intro z hz
  
  refine jsi_arcWalk_support_subset P A.col A.shift_all c (d - c).toNat ?_ ?_ z hz
  · 
    intro j hj
    have hjn : (j : ℤ) ≤ (d - c).toNat := by exact_mod_cast hj
    have hjd : c + (j : ℤ) ≤ d := by omega
    exact A.on_arc (jsi_cell (A.col (c + j)) (c + j)) (by simp only [jsi_cell_1]; omega)
      (by simp only [jsi_cell_1]; omega) (by simp)
      (A.band_lo (c + j) (by omega) hjd) (A.band_hi (c + j) (by omega) hjd)
  · 
    intro j hj
    have hjn : (j : ℤ) < (d - c).toNat := by exact_mod_cast hj
    have hjd : c + (j : ℤ) + 1 ≤ d := by omega
    exact A.corner (jsi_cell (A.col (c + j)) (c + j + 1)) (by simp only [jsi_cell_1]; omega)
      (by simp only [jsi_cell_1]; omega) (by simp)
      (A.band_lo (c + j) (by omega) (by omega)) (A.band_hi (c + j) (by omega) (by omega))






theorem jsi_separatingSide {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d :=
  jsi_arcSeparatingSet hαm hm'β A






theorem jsi_separatingSideLt {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α < m) (hm'β : m' ≤ β) (A : JsiRowArc P m m' c d) :
    ArcSeparatingSet P α β c d :=
  jsi_arcSeparatingSetLt hαm hm'β A















def JsiHasMonotoneArc (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ) : Prop :=
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
    Nonempty (JsiMonotoneArc (overlapComp ω m m' c d xB hxB) m m' c d)






theorem jsi_arc_sides_of_hasMonotone (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (h : JsiHasMonotoneArc ω m m' c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d :=
  tpc_arc_sides_of_sep ω
    (fun xB hxB => jsi_separatingSide hαm hm'β (h xB hxB).some.toJsiRowArc)












theorem jsi_arc_sides_of_rowArc (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β)
    (A : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d :=
  tpc_arc_sides_of_sep ω (fun xB hxB => jsi_separatingSide hαm hm'β (A xB hxB))











theorem jsi_rsw_strip_glue_of_rowArc
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a < m) (hmm' : m ≤ m') (hm'b : m' < b)
    (AL : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d)
    (AR : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JsiRowArc (overlapComp ω m m' c d xB hxB) m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  tpc_rsw_strip_glue_of_sep μ hpa (le_of_lt ham) hmm' (le_of_lt hm'b)
    (fun ω xB hxB => jsi_separatingSideLt ham (le_refl m') (AL ω xB hxB))
    (fun ω xB hxB => jsi_separatingSide (le_refl m) hm'b (AR ω xB hxB))

end Lattice

end StatMech
