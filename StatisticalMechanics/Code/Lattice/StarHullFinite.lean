/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Lattice.NoDiagTouchClose

open SimpleGraph Function Set

namespace StatMech

namespace Lattice












theorem shf_coord_mem_proj (K : Set (Site 2)) {x : Site 2} (hx : x ∈ ndt_StarHull K) :
    ∀ i : Fin 2, x i ∈ (fun y => y i) '' K := by
  induction hx with
  | base h => exact fun i => ⟨_, h, rfl⟩
  | @fillBL f _ _ ih00 ih11 =>
      
      intro i
      fin_cases i
      · simpa only [npd_P10, npd_P11, Matrix.cons_val_zero] using ih11 0
      · simpa only [npd_P10, npd_P00, Matrix.cons_val_one, Matrix.cons_val_fin_one] using ih00 1
  | @fillTL f _ _ ih10 ih01 =>
      
      intro i
      fin_cases i
      · simpa only [npd_P00, npd_P01, Matrix.cons_val_zero] using ih01 0
      · simpa only [npd_P00, npd_P10, Matrix.cons_val_one, Matrix.cons_val_fin_one] using ih10 1




theorem shf_starHull_subset_projBox (K : Set (Site 2)) :
    ndt_StarHull K ⊆ {x : Site 2 | ∀ i, x i ∈ (fun y => y i) '' K} :=
  fun _ hx i => shf_coord_mem_proj K hx i






theorem starHull_finite (K : Set (Site 2)) (hK : K.Finite) : (ndt_StarHull K).Finite := by
  
  have hbox : {x : Site 2 | ∀ i, x i ∈ (fun y => y i) '' K}.Finite := by
    have hpi : (Set.pi Set.univ (fun i : Fin 2 => (fun y : Site 2 => y i) '' K)).Finite :=
      Set.Finite.pi (fun i => hK.image _)
    refine hpi.subset ?_
    intro x hx i _
    exact hx i
  exact hbox.subset (shf_starHull_subset_projBox K)

end Lattice

end StatMech
