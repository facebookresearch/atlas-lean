/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHull

/-!
# Finiteness of the star hull

Every site of the star hull `ndt_StarHull K` has each of its coordinates equal to the
corresponding coordinate of some site of `K`: the fill rules only add corners of faces whose
other corners are already present. So the star hull lies in the product of the two coordinate
projections of `K`, and the star hull of a finite set is finite.

## Main results

* `StatMech.Lattice.shf_starHull_subset_projBox`: the star hull of `K` lies in the product of
  the coordinate projections of `K`.
* `StatMech.Lattice.starHull_finite`: the star hull of a finite set is finite.
-/

@[expose] public section

open SimpleGraph Function Set

namespace StatMech

namespace Lattice

/-- Each coordinate of a site of the star hull of `K` is the same coordinate of a site of `K`. -/
theorem shf_coord_mem_proj (K : Set (Site 2)) {x : Site 2} (hx : x ∈ ndt_StarHull K) :
    ∀ i : Fin 2, x i ∈ (fun y => y i) '' K := by
  induction hx with
  | base h => exact fun i => ⟨_, h, rfl⟩
  | @fillBL f _ _ ih00 ih11 =>
      intro i
      fin_cases i
      · simpa only [npd_P10, npd_P11, Matrix.cons_val_zero, Fin.zero_eta] using ih11 0
      · simpa only [npd_P10, npd_P00, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one]
          using ih00 1
  | @fillTL f _ _ ih10 ih01 =>
      intro i
      fin_cases i
      · simpa only [npd_P00, npd_P01, Matrix.cons_val_zero, Fin.zero_eta] using ih01 0
      · simpa only [npd_P00, npd_P10, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one]
          using ih10 1

/-- The star hull of `K` lies in the product of the coordinate projections of `K`. -/
theorem shf_starHull_subset_projBox (K : Set (Site 2)) :
    ndt_StarHull K ⊆ {x : Site 2 | ∀ i, x i ∈ (fun y => y i) '' K} :=
  fun _ hx i => shf_coord_mem_proj K hx i

/-- The star hull of a finite set is finite. -/
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
