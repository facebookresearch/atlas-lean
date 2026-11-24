/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryAssembly

/-!
# Every full original boundary face in dimensions at least three

The same assembled simplex is independent of its retaining inner
horn. A genuine original interior index different from the requested
face therefore recovers that whole original boundary face. All
original Hom maps, vertices and ordinal labels are retained.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomAssembly
open SimplicialEnrichment HornBoxFaces

variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (g : outerHom.{u} n ⟶ (BoundaryFaces.object f 0 ⟶[SSet.{u}]
    BoundaryFaces.object f (Fin.last (n+2))))
  (hg : (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫ g = BoundaryHomGlue.map f)

/-- A retained original inner-horn face is exactly the same whole original boundary face. -/
theorem simplex_face_of_retained (i k : Fin (n+3))
    (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) (hk : k ≠ i) :
    coherentSimplexMap (SimplexCategory.δ k) ≫ simplex f g hg i hi₀ hiₙ =
      BoundaryFaces.faceFunctor f k :=
  (HornAssembly.simplex_face (BoundaryFaces.horn f i) hi₀ hiₙ g
    (horn_extension f g hg i hi₀ hiₙ) k hk).trans (BoundaryFaces.horn_face f i k hk)

/-- Every original boundary face is retained by the same assembled simplex once there are two interior labels. -/
theorem simplex_all_faces (hn : n ≠ 0)
    (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) (k : Fin (n+3)) :
    coherentSimplexMap (SimplexCategory.δ k) ≫ simplex f g hg i hi₀ hiₙ =
      BoundaryFaces.faceFunctor f k := by
  classical
  let one : Fin (n+3) := ⟨1, by omega⟩
  let two : Fin (n+3) := ⟨2, by omega⟩
  let j : Fin (n+3) := if k = one then two else one
  have hj₀ : j ≠ 0 := by
    dsimp [j]
    split_ifs <;> intro h <;> have hv := congrArg Fin.val h
    · change 2 = 0 at hv
      omega
    · change 1 = 0 at hv
      omega
  have hjₙ : j ≠ Fin.last (n+2) := by
    dsimp [j]
    split_ifs <;> intro h <;> have hv := congrArg Fin.val h
    · change 2 = n+2 at hv
      omega
    · change 1 = n+2 at hv
      omega
  have hk : k ≠ j := by
    dsimp [j]
    split_ifs with h
    · rw [h]
      intro h12
      have hv := congrArg Fin.val h12
      change 1 = 2 at hv
      omega
    · exact h
  exact (congrArg (fun q => coherentSimplexMap (SimplexCategory.δ k) ≫ q)
    (simplex_eq f g hg i j hi₀ hiₙ hj₀ hjₙ)).trans
      (simplex_face_of_retained f g hg j k hj₀ hjₙ hk)

end CategoryTheory.CoherentRealization.BoundaryHomAssembly
