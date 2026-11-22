/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomMappingCells
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentZeroFlagIso

/-!
# Actual individual coherent-edge readback

An actual coherent edge with its supplied original source and target is
uniquely reconstructed from its original Hom vertex. The adjacent Hom
flag is an actual isomorphism, and the two diagonal Hom maps are fixed
by the original identity laws. Objects are not replaced by components.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedEdgeReadback
open SimplicialEnrichment HomSimplex HomMappingCells HomFlagEvaluation
variable {C : Carrier.{u}} (x y : C)

private theorem whole_ext {A B : Carrier.{u}} (F G : A ⟶ B)
    (ho : ∀ a, F.obj a = G.obj a) (hm : ∀ a b, F.map a b ≍ G.map a b) : F = G := by
  refine EnrichedFunctor.ext SSet.{u} ho ?_
  intro a b
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hm a b))

/-- The supplied actual coherent edge reads its individual original Hom vertex. -/
def readVertex (σ : FixedSimplex x y (n := 0)) : (x ⟶[SSet.{u}] y) _⦋0⦌ :=
  SSet.yonedaEquiv (HomMappingCells.read x y σ)

/-- Reading the actual coherent edge constructed from one original Hom vertex retains that same vertex. -/
theorem read_construct (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    readVertex x y (construct x y τ) = τ :=
  (congrArg (fun f => SSet.yonedaEquiv f) (HomMappingCells.read_construct x y τ)).trans
    (SSet.yonedaEquiv.apply_symm_apply τ)

/-- The entire actual coherent edge is reconstructed from its specified original Hom vertex and both
  individual object boundaries. -/
theorem construct_read (σ : FixedSimplex x y (n := 0)) : construct x y (readVertex x y σ) = σ := by
  apply Subtype.ext
  let B := (construct x y (readVertex x y σ)).val
  have hRead : HomMappingCells.read x y (construct x y (readVertex x y σ)) = HomMappingCells.read x y σ :=
    (HomMappingCells.read_construct x y (readVertex x y σ)).trans (SSet.yonedaEquiv.symm_apply_apply _)
  have ho : ∀ a : coherentSimplex.{u} ⦋1⦌, B.obj a = σ.val.obj a := by
    intro a
    cases a with | mk a =>
      cases a with | up a =>
        rcases AdjacentHom.finTwo_vertices (ULift.up.{u} a) with h | h
        · have ha : a = 0 := congrArg ULift.down h
          subst a
          exact (object_front x y (0 : Fin 1)).trans σ.2.1.symm
        · have ha : a = 1 := congrArg ULift.down h
          subst a
          exact (object_last (n := 0) x y).trans σ.2.2.symm
  apply whole_ext B σ.val ho
  intro a b
  cases a with | mk a =>
    cases a with | up a =>
      cases b with | mk b =>
        cases b with | up b =>
          rcases AdjacentHom.finTwo_vertices (ULift.up.{u} a) with ha | ha <;>
            rcases AdjacentHom.finTwo_vertices (ULift.up.{u} b) with hb | hb
          all_goals
            have hA := congrArg ULift.down ha; have hB := congrArg ULift.down hb;
              dsimp only at hA hB; subst a; subst b
          · let e := EqualityTransport.hom (ho (.mk (ULift.up (0 : Fin 2)))) (ho (.mk (ULift.up (0 : Fin 2))))
            have h : B.map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (0 : Fin 2))) ≫ e =
                σ.val.map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (0 : Fin 2))) := by
              let _ : IsIso (eId SSet.{u} (C := coherentSimplex.{u} ⦋1⦌) (SimplicialThickening.mk (ULift.up
                (0 : Fin 2)))) :=
                HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (0 : Fin 2))
              apply (cancel_epi (eId SSet.{u} (C := coherentSimplex.{u} ⦋1⦌) (SimplicialThickening.mk
                (ULift.up (0 : Fin 2))))).mp
              exact (Category.assoc _ _ _).symm.trans
                ((congrArg (fun f => f ≫ e) (B.map_id (.mk (ULift.up (0 : Fin 2))))).trans
                  ((EqualityTransport.identity (ho (.mk (ULift.up (0 : Fin 2))))).trans (σ.val.map_id _).symm))
            exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)
          · let eB := EqualityTransport.hom (object_front x y (0 : Fin 1)) (object_last (n := 0) x y)
            let eS := EqualityTransport.hom σ.2.1 σ.2.2
            have h : B.map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (1 : Fin 2))) ≫ eB =
                σ.val.map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (1 : Fin 2))) ≫ eS := by
              let _ : IsIso (flagMap.{u} (n := 0)) := ZeroFlagIso.flag_isIso.{u}
              apply (cancel_epi (flagMap.{u} (n := 0))).mp
              exact hRead
            exact (comp_eqToHom_heq _ _).symm.trans ((heq_of_eq h).trans (comp_eqToHom_heq _ _))
          · apply (conj_eqToHom_iff_heq _ _ rfl (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
              (ho (.mk (ULift.up (1 : Fin 2)))) (ho (.mk (ULift.up (0 : Fin 2)))))).mp
            rw [eqToHom_refl, Category.id_comp]
            exact HomUnitsAndEmpty.empty_hom_ext (by change ¬(1 : Fin 2) ≤ 0; decide) _ _
          · let e := EqualityTransport.hom (ho (.mk (ULift.up (1 : Fin 2)))) (ho (.mk (ULift.up (1 : Fin 2))))
            have h : B.map (.mk (ULift.up (1 : Fin 2))) (.mk (ULift.up (1 : Fin 2))) ≫ e =
                σ.val.map (.mk (ULift.up (1 : Fin 2))) (.mk (ULift.up (1 : Fin 2))) := by
              let _ : IsIso (eId SSet.{u} (C := coherentSimplex.{u} ⦋1⦌) (SimplicialThickening.mk (ULift.up
                (1 : Fin 2)))) :=
                HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (1 : Fin 2))
              apply (cancel_epi (eId SSet.{u} (C := coherentSimplex.{u} ⦋1⦌) (SimplicialThickening.mk
                (ULift.up (1 : Fin 2))))).mp
              exact (Category.assoc _ _ _).symm.trans
                ((congrArg (fun f => f ≫ e) (B.map_id (.mk (ULift.up (1 : Fin 2))))).trans
                  ((EqualityTransport.identity (ho (.mk (ULift.up (1 : Fin 2))))).trans (σ.val.map_id _).symm))
            exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq h)

/-- The actual original Hom-vertex equivalence with fixed-endpoint coherent edges, without quotienting objects. -/
def equiv : (x ⟶[SSet.{u}] y) _⦋0⦌ ≃ FixedSimplex x y (n := 0) where
  toFun := construct x y
  invFun := readVertex x y
  left_inv := read_construct x y
  right_inv := construct_read x y

end CategoryTheory.CoherentRealization.FixedEdgeReadback
