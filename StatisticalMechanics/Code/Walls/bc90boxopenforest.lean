/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































































import Mathlib
import Code.Percolation.CanonForestCount
import Code.Walls.bc89genuinetrifae

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}














theorem bc90_genuineTrif_iff_canonical (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bc89_GenuineTrif d ω x ↔ IsCanonicalTrifurcation d ω x := by
  constructor
  · rintro ⟨a₁, a₂, a₃, hne, _hnx, hadj, hinf, hsep⟩
    exact ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
  · rintro ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩
    
    exact ⟨a₁, a₂, a₃, hne,
      ⟨((openSubgraph d ω).ne_of_adj hadj.1).symm,
       ((openSubgraph d ω).ne_of_adj hadj.2.1).symm,
       ((openSubgraph d ω).ne_of_adj hadj.2.2).symm⟩,
      hadj, hinf, hsep⟩


theorem bc90_canonical_of_genuineTrif (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc89_GenuineTrif d ω x) : IsCanonicalTrifurcation d ω x :=
  (bc90_genuineTrif_iff_canonical ω x).mp h













open Classical in














theorem bc90_spanForest_preserves_genuineTrif_deg3 (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) {x : Site d} (hxbox : x ∈ box d n)
    (hgen : bc89_GenuineTrif d ω x)
    (harmbox_x : ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
      a ∈ box d n) :
    ∃ c : Fin 3 → Site d,
      (c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2) ∧
      (∀ i, (cfc_T ω n).Adj x (c i)) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) := by
  classical
  
  obtain ⟨a₁, a₂, a₃, hne, hnx, hadj3, hinf3, hsep3⟩ := hgen
  set c0 : Fin 3 → Site d := ![a₁, a₂, a₃] with hc0
  have hadj0 : ∀ i, (openSubgraph d ω).Adj x (c0 i) := by
    intro i; fin_cases i
    · exact hadj3.1
    · exact hadj3.2.1
    · exact hadj3.2.2
  have hne0 : ∀ i, c0 i ≠ x := by
    intro i; fin_cases i
    · exact hnx.1
    · exact hnx.2.1
    · exact hnx.2.2
  have hcut0 : ¬ Connected d (removeSite x ω) (c0 0) (c0 1) ∧
      ¬ Connected d (removeSite x ω) (c0 0) (c0 2) ∧
      ¬ Connected d (removeSite x ω) (c0 1) (c0 2) :=
    ⟨hsep3.1, hsep3.2.1, hsep3.2.2⟩
  have hinf0 : ∀ i, (cluster d (removeSite x ω) (c0 i)).Infinite := by
    intro i; fin_cases i
    · exact hinf3.1
    · exact hinf3.2.1
    · exact hinf3.2.2
  have hcbox : ∀ i, c0 i ∈ box d n := fun i =>
    harmbox_x (c0 i) (hadj0 i) (hinf0 i)
  
  obtain ⟨c, zr, hcadj, hccut, _hcreach⟩ :=
    cfc_trif_data ω n hn hxbox c0 hadj0 hne0 hcbox hcut0 hinf0
  
  have hd01 : c 0 ≠ c 1 := fun h => hccut.1 (h ▸ connected_refl _ _)
  have hd02 : c 0 ≠ c 2 := fun h => hccut.2.1 (h ▸ connected_refl _ _)
  have hd12 : c 1 ≠ c 2 := fun h => hccut.2.2 (h ▸ connected_refl _ _)
  exact ⟨c, ⟨hd01, hd02, hd12⟩, hcadj, hccut⟩

open Classical in








theorem bc90_spanForest_subtype_deg3 (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) {x : Site d} (hxbox : x ∈ box d n)
    (hgen : bc89_GenuineTrif d ω x)
    (harmbox_x : ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
      a ∈ box d n)
    [DecidableRel (cfc_F ω n).Adj] :
    3 ≤ (cfc_F ω n).degree ⟨x, box_subset_succ d n hxbox⟩ := by
  classical
  obtain ⟨c, ⟨hd01, hd02, hd12⟩, hcadj, _hccut⟩ :=
    bc90_spanForest_preserves_genuineTrif_deg3 ω n hn hxbox hgen harmbox_x
  set xv : (↑(box d (n + 1)) : Type) := ⟨x, box_subset_succ d n hxbox⟩ with hxv
  
  have htransfer : ∀ i : Fin 3, ∃ cv : (↑(box d (n + 1)) : Type),
      (cv : Site d) = c i ∧ (cfc_F ω n).Adj xv cv := by
    intro i
    have hadj := hcadj i
    rw [cfc_T, SimpleGraph.map_adj] at hadj
    obtain ⟨p, q, hpq, hp, hq⟩ := hadj
    
    have hpx : (p : Site d) = x := by simpa [cfc_emb] using hp
    have hqc : (q : Site d) = c i := by simpa [cfc_emb] using hq
    refine ⟨q, hqc, ?_⟩
    have hpxv : p = xv := Subtype.ext (by rw [hpx, hxv])
    rw [← hpxv]; exact hpq
  choose cv hcvval hcvadj using htransfer
  
  have hcd01 : cv 0 ≠ cv 1 := fun h => hd01 (by rw [← hcvval 0, ← hcvval 1, h])
  have hcd02 : cv 0 ≠ cv 2 := fun h => hd02 (by rw [← hcvval 0, ← hcvval 2, h])
  have hcd12 : cv 1 ≠ cv 2 := fun h => hd12 (by rw [← hcvval 1, ← hcvval 2, h])
  exact spc_deg_ge_three (cfc_F ω n) xv (cv 0) (cv 1) (cv 2) hcd01 hcd02 hcd12
    (hcvadj 0) (hcvadj 1) (hcvadj 2)





















theorem bc90_boxOpenForest_of_genuine_armsInBox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bst_BoxOpenForest ω n := by
  have hcanon' : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x :=
    fun x hx htri => bc90_canonical_of_genuineTrif ω x (hcanon x hx htri)
  have hsfa : sfa_ArmForestReaching ω n :=
    cfc_armForestReaching_of_canonical_armsInBox ω n hn hcanon' harmbox hexists
  exact spc_boxOpenForest_of_spanForestArms ω n (sfa_spanForestArms_of_armForestReaching ω n hsfa)





theorem bc90_Tcount_le_boundary_of_genuine_armsInBox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  have hcanon' : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x :=
    fun x hx htri => bc90_canonical_of_genuineTrif ω x (hcanon x hx htri)
  exact cfc_Tcount_le_boundary_of_canonical ω n hn hcanon' harmbox



theorem bc90_genuineTcount_le_boundary_of_genuine_armsInBox (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n :=
  le_trans (bc89_genuineTcount_le_Tcount ω n)
    (bc90_Tcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox)















theorem bc90_harmbox_free_of_interior (ω : ConfigSpace (Sym2 (Site d))) {n : ℕ} (hn : 1 ≤ n)
    {x : Site d} (hxint : x ∈ box d (n - 1))
    {a : Site d} (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d n := by
  by_contra hnot
  have hlat : (hypercubicLattice d).Adj x a := hadj.1
  
  have hxint' : x ∈ box d n := box_mono d (by omega : n - 1 ≤ n) hxint
  exact (cfc_neighbour_outside_box_imp_boundary hn hxint' hlat hnot) hxint














theorem bc90_upperLines_boxOpenForest_count_free (n : ℕ) :
    bc89_genuineTcount bc60_upperLines n = 0 ∧
    bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n :=
  ⟨bc89_upperLines_genuineTcount_zero n, bc89_upperLines_genuine_le_boundary n⟩








open Classical in



theorem bc90_boxOpenForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bst_BoxOpenForest ω n :=
  bst_boxOpenForest_star ω n a hsingle hadj habdry hxne hainj hsep















































theorem bc90_status :
    
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2}, x ∈ box 2 n →
      bc89_GenuineTrif 2 ω x →
      (∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      ∃ c : Fin 3 → Site 2, (c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2) ∧ (∀ i, (cfc_T ω n).Adj x (c i)) ∧
        (¬ Connected 2 (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected 2 (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected 2 (removeSite x ω) (c 1) (c 2))) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2} (hxbox : x ∈ box 2 n),
      bc89_GenuineTrif 2 ω x →
      (∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      ∀ [DecidableRel (cfc_F ω n).Adj],
        3 ≤ (cfc_F ω n).degree ⟨x, box_subset_succ 2 n hxbox⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      (∃ x, x ∈ box 2 n ∧ IsTrifurcation 2 ω x) → bst_BoxOpenForest ω n) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x → bc89_GenuineTrif 2 ω x) →
      (∀ x, x ∈ box 2 n → IsTrifurcation 2 ω x →
        ∀ a, (openSubgraph 2 ω).Adj x a → (cluster 2 (removeSite x ω) a).Infinite → a ∈ box 2 n) →
      Tcount 2 ω n ≤ boxSV_boundaryCard 2 n) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → ∀ {x : Site 2}, x ∈ box 2 (n - 1) →
      ∀ {a : Site 2}, (openSubgraph 2 ω).Adj x a → a ∈ box 2 n) ∧
    
    (∀ n : ℕ, bc89_genuineTcount bc60_upperLines n = 0 ∧
      bc89_genuineTcount bc60_upperLines n ≤ boxSV_boundaryCard 2 n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω n hn x hxbox hgen harmbox_x
    exact bc90_spanForest_preserves_genuineTrif_deg3 ω n hn hxbox hgen harmbox_x
  · intro ω n hn x hxbox hgen harmbox_x _
    exact bc90_spanForest_subtype_deg3 ω n hn hxbox hgen harmbox_x
  · intro ω n hn hcanon harmbox hexists
    exact bc90_boxOpenForest_of_genuine_armsInBox ω n hn hcanon harmbox hexists
  · intro ω n hn hcanon harmbox
    exact bc90_Tcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox
  · intro ω n hn x hxint a hadj
    exact bc90_harmbox_free_of_interior ω hn hxint hadj
  · intro n; exact bc90_upperLines_boxOpenForest_count_free n

end StatMech.Walls
