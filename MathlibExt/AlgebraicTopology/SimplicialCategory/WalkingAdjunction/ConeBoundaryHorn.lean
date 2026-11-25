/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.ConeSimplexBoundary
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan

/-!
# The actual right outer horn of a whole boundary cone

The coned codimension-one faces glue to the original last outer horn.
Each face retains its entire original cone map, original base and
identical apex. These actual faces are the geometric input to special
outer horn filling in terminal-point transport.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.WalkingAdjunction.ConeBoundaryHorn

variable {H : SSet.{u}}

/-- The actual whole coned face of a boundary cone, normalized by the native join isomorphism. -/
def face {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (j : Fin (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ H :=
  (joinStdSimplexIso n 0).inv ≫ (join.map (boundary.ι j)).app Δ[0] ≫ q

/-- The whole original base of each coned face is its original boundary face. -/
theorem face_base {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (j : Fin (n + 2)) :
    stdSimplex.δ (Fin.last (n + 1)) ≫ face q j =
      boundary.ι j ≫ joinInl (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ q := by
  dsimp only [face]
  rw [← Category.assoc, ConeSimplexBoundary.last_face_join_inv, ← Category.assoc,
    ← map_comp_joinInl, Category.assoc]

/-- Every coned face retains the identical original apex. -/
theorem face_apex {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (j : Fin (n + 2)) :
    rightVertex n ≫ face q j = joinInr (∂Δ[n + 1] : SSet.{u}) Δ[0] ≫ q := by
  dsimp only [rightVertex, face]
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, joinInr_comp_map]

/-- The original coned faces indexed by the nonmissing faces of the last outer horn. -/
def faces {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)) : (Δ[n + 1] : SSet.{u}) ⟶ H :=
  face q (j.castPred hj)

/-- Compatibility is proved from the original common apex and standard boundary relations. -/
theorem faces_compatible {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    horn.IsCompatible (faces q) := by
  cases n with
  | zero =>
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have h0 : stdSimplex.δ (0 : Fin 2) ≫ face q 0 =
        joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ q := by
      rw [← rightVertex_zero]
      exact face_apex q 0
    have h1 : stdSimplex.δ (0 : Fin 2) ≫ face q 1 =
        joinInr (∂Δ[1] : SSet.{u}) Δ[0] ≫ q := by
      rw [← rightVertex_zero]
      exact face_apex q 1
    obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last hj
    obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
    change j'.val < k'.val at hjk
    have hj0 : j' = 0 := Fin.ext (by have := k'.isLt; omega)
    have hk1 : k' = 1 := Fin.ext (by have := k'.isLt; omega)
    subst j'
    subst k'
    change stdSimplex.δ (0 : Fin 2) ≫ face q 0 = stdSimplex.δ (0 : Fin 2) ≫ face q 1
    exact h0.trans h1.symm
  | succ n =>
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last hj
    obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk
    have hj'k' : j' < k' := hjk
    have hp : k'.castSucc.pred (Fin.ne_zero_of_lt hjk) =
        (k'.pred (Fin.ne_zero_of_lt hj'k')).castSucc := by
      apply Fin.ext
      rfl
    have hc : j'.castSucc.castPred (Fin.ne_last_of_lt hjk) =
        (j'.castPred (Fin.ne_last_of_lt hj'k')).castSucc := by
      apply Fin.ext
      rfl
    dsimp only [faces]
    rw [Fin.castPred_castSucc, Fin.castPred_castSucc, hp]
    have hd : stdSimplex.δ j' =
        (stdSimplex.δ (j'.castPred (Fin.ne_last_of_lt hj'k')).castSucc :
          (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2]) := by
      simpa only [Fin.castPred_castSucc] using congrArg stdSimplex.δ hc
    rw [hd]
    dsimp only [face]
    rw [← Category.assoc, ConeSimplexBoundary.face_join_inv, Category.assoc,
      ← Category.assoc (stdSimplex.δ _), ConeSimplexBoundary.face_join_inv, Category.assoc]
    have h := (boundary.isCompatible_succ_iff _).mp (boundary.ι_isCompatible (n + 1)) j' k' hj'k'
    have hm := congrArg (fun f => (joinStdSimplexIso n 0).inv ≫
      (join.map f).app (Δ[0] : SSet.{u}) ≫ q) h
    simpa only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc] using hm

/-- The actual last outer horn map of the original whole boundary cone. -/
def hornMap {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ H := (faces_compatible q).desc

/-- Every horn face is its entire original coned face. -/
theorem hornMap_face {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H)
    (j : Fin (n + 2)) :
    horn.ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j) ≫ hornMap q = face q j := by
  exact (faces_compatible q).ι_desc j.castSucc (Fin.castSucc_ne_last j)

/-- The original last pair of vertices in a standard coned face. -/
def lastPair (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 1] :=
  yonedaEquiv.symm (stdSimplex.edge (n + 1) (Fin.last n).castSucc (Fin.last (n + 1))
    (by simp [Fin.le_def]))

private theorem lastPair_tensor (n : ℕ) : lastPair.{u} n =
    stdSimplex.map (AugmentedSimplexCategory.tensorHomOf
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) (𝟙 ⦋0⦌)) := by
  apply yonedaEquiv.injective
  rw [lastPair, Equiv.apply_symm_apply, yonedaEquiv_map]
  apply stdSimplex.objEquiv.injective
  ext i : 3
  fin_cases i <;> rfl

/-- Native join naturality retains the original last-pair map and original scalar vertex. -/
theorem lastPair_join_inv (n : ℕ) :
    lastPair.{u} n ≫ (joinStdSimplexIso n 0).inv =
      (joinStdSimplexIso 0 0).inv ≫
        (join.map (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))).app Δ[0] := by
  rw [lastPair_tensor]
  exact (joinStdSimplexIso_inv_comp_join_map_app
    (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) 0).symm

/-- The original last vertex of the standard boundary. -/
def lastBoundaryVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫ boundary.ι (0 : Fin (n + 2))

/-- The last-pair restriction is the entire original cone on the identical last boundary vertex. -/
theorem lastPair_face {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    lastPair n ≫ face q 0 =
      (joinStdSimplexIso 0 0).inv ≫ (join.map (lastBoundaryVertex n)).app Δ[0] ≫ q := by
  dsimp only [face]
  rw [← Category.assoc, lastPair_join_inv]
  simp only [lastBoundaryVertex, CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem lastPair_horn_face (n : ℕ) :
    (horn.ι (Fin.last (n + 2)) (0 : Fin (n + 3)) (by simp)).app (op ⦋1⦌)
        (yonedaEquiv (lastPair.{u} n)) = rightHornEdgeSimplex n := by
  apply Subtype.ext
  have hf := ConcreteCategory.congr_hom (NatTrans.congr_app
    (horn.ι_ι (Fin.last (n + 2)) (0 : Fin (n + 3)) (by simp)) (op ⦋1⦌))
    (yonedaEquiv (lastPair.{u} n))
  refine hf.trans ?_
  apply stdSimplex.objEquiv.injective
  ext i : 3
  fin_cases i <;> rfl

/-- The critical edge of the actual horn is the original last pair in its first coned face. -/
theorem rightHornEdge_edge {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    (SSet.rightHornEdge (hornMap q)).edge = yonedaEquiv (lastPair n ≫ face q 0) := by
  rw [SSet.rightHornEdge_edge, ← lastPair_horn_face]
  have hf := congrArg (fun f => lastPair n ≫ f) (hornMap_face q (0 : Fin (n + 2)))
  have h := congrArg yonedaEquiv hf
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at h
  exact h

/-- The critical edge retains the entire original cone on its fixed last boundary vertex. -/
theorem rightHornEdge_cone {n : ℕ} (q : (∂Δ[n + 1] : SSet.{u}) ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    (SSet.rightHornEdge (hornMap q)).edge = yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫ (join.map (lastBoundaryVertex n)).app Δ[0] ≫ q) :=
  (rightHornEdge_edge q).trans (congrArg yonedaEquiv (lastPair_face q))

end SSet.WalkingAdjunction.ConeBoundaryHorn
