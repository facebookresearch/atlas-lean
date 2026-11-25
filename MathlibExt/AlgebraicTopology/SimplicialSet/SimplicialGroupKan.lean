/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupUpperHornCorrection
public import Mathlib.Tactic.FinCases

/-! # Genuine Kan horn filling for the SAME original simplicial group -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

attribute [local instance] underlyingGroup

variable (G : SimplicialObject GrpCat.{u})

/-- The whole original horn maps retain their actual face coefficients, with unit only at the missing face. -/
def groupFaces {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (j : Fin (n + 3)) : (underlying G) _⦋n + 1⦌ :=
  if hj : j ≠ i then SSet.yonedaEquiv (f j hj) else 1

/-- Every prescribed original face remains exactly its whole original Yoneda coefficient. -/
theorem groupFaces_at {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (j : Fin (n + 3)) (hj : j ≠ i) : groupFaces G i f j = SSet.yonedaEquiv (f j hj) := dite_eq_left hj

/-- Actual whole horn compatibility gives the original full group-face equations, without a lifting outcome premise. -/
theorem groupFaces_compatible {n : ℕ} (i : Fin (n + 3))
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet.{u}) ⟶ underlying G)
    (hf : SSet.horn.IsCompatible f) : FaceCompatible G i (groupFaces G i f) := by
  intro k j hkj hk hj
  have h := congrArg SSet.yonedaEquiv (hf.δ_pred_comp (Fin.castSucc k) j hk hj hkj)
  have hh : (underlying G).δ k (SSet.yonedaEquiv (f j hj)) =
      (underlying G).δ (j.pred hkj.ne_zero) (SSet.yonedaEquiv (f (Fin.castSucc k) hk)) := by
    simpa only [SSet.stdSimplex.yonedaEquiv_δ_comp, Fin.castPred_castSucc] using h.symm
  exact (congrArg ((underlying G).δ k) (groupFaces_at G i f j hj)).trans
    (hh.trans (congrArg ((underlying G).δ (j.pred hkj.ne_zero)) (groupFaces_at G i f (Fin.castSucc k) hk)).symm)

/-- The SAME original simplicial group is Kan by its actual finite noncommutative horn corrections. -/
theorem underlying_isKan : SSet.KanComplex (underlying G) := by
  apply SSet.KanComplex.iff.mpr
  intro q i f hf
  cases q with
  | zero =>
    fin_cases i
    · let z := SSet.yonedaEquiv (f (1 : Fin 2) (by decide))
      refine ⟨SSet.yonedaEquiv.symm ((underlying G).σ (0 : Fin 1) z), ?_⟩
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · exact (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
          ((congrArg SSet.yonedaEquiv.symm (face_degeneracy_succ G (0 : Fin 1) z)).trans
            (SSet.yonedaEquiv.symm_apply_apply _))
    · let z := SSet.yonedaEquiv (f (0 : Fin 2) (by decide))
      refine ⟨SSet.yonedaEquiv.symm ((underlying G).σ (0 : Fin 1) z), ?_⟩
      intro j hj
      fin_cases j
      · exact (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
          ((congrArg SSet.yonedaEquiv.symm (face_degeneracy_self G (0 : Fin 1) z)).trans
            (SSet.yonedaEquiv.symm_apply_apply _))
      · exact (hj rfl).elim
  | succ n =>
    let h := groupFaces G i f
    have hc := groupFaces_compatible G i f hf
    refine ⟨SSet.yonedaEquiv.symm (hornFiller G i h), ?_⟩
    intro k hki
    have hk := hornFiller_face G i h hc k hki
    exact (SSet.stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans
      ((congrArg SSet.yonedaEquiv.symm hk).trans
        ((congrArg SSet.yonedaEquiv.symm (groupFaces_at G i f k hki)).trans
          (SSet.yonedaEquiv.symm_apply_apply _)))

end SSet.SimplicialGroupHorn
