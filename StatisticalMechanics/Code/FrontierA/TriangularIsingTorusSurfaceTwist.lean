/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSeamHomology









namespace StatMech.FrontierA

open StatMech.Onsager

@[simp] theorem triangularTorusDirectionPhase_one_one (a : Fin 6) :
    triangularTorusDirectionPhase 1 1 a = 1 := by
  fin_cases a <;> simp [triangularTorusDirectionPhase]



theorem surfaceTwistedKacWardMatrix_triangularTorusDartEquiv_apply
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2)
    (d e : triangularTorusDart L) :
    surfaceTwistedKacWardMatrix (triangularTorusGraph L)
        (triangularTorusGraphPhase L rho 1 1)
        (triangularTorusSurfaceEdgeClass L)
        (fun _ => a, fun _ => b)
        (triangularTorusEdgeWeight L t1 t2 t3)
        (triangularTorusDartEquiv L d)
        (triangularTorusDartEquiv L e) =
      if (triangularTorusDartEquiv L d).snd =
            (triangularTorusDartEquiv L e).fst ∧
          (triangularTorusDartEquiv L d).edge ≠
            (triangularTorusDartEquiv L e).edge then
        triangularTorusDirectionWeight t1 t2 t3 d.2 *
          (triangularTorusSpinDartSeamSign L a b d *
            triangularKacWardTurnMatrix rho d.2 e.2)
      else 0 := by
  rw [surfaceTwistedKacWardMatrix_apply]
  split
  · rw [← triangularTorusSpinDartSeamSign_eq_surfaceHomologyCharacter,
      triangularTorusEdgeWeight_dart]
    unfold triangularTorusGraphPhase
    dsimp only
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp only [triangularTorusDirectionPhase_one_one, one_mul]
    ring
  · rfl



theorem triangularTorusSeamKWMatrix_eq_reindex_surfaceTwisted
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    triangularTorusSeamKWMatrix L t1 t2 t3 rho a b =
      (Matrix.reindex (triangularTorusDartEquiv L).symm
        (triangularTorusDartEquiv L).symm)
        (surfaceTwistedKacWardMatrix (triangularTorusGraph L)
          (triangularTorusGraphPhase L rho 1 1)
          (triangularTorusSurfaceEdgeClass L)
          (fun _ => a, fun _ => b)
          (triangularTorusEdgeWeight L t1 t2 t3)) := by
  ext d e
  rw [Matrix.reindex_apply]
  change triangularTorusSeamKWMatrix L t1 t2 t3 rho a b d e =
    surfaceTwistedKacWardMatrix (triangularTorusGraph L)
      (triangularTorusGraphPhase L rho 1 1)
      (triangularTorusSurfaceEdgeClass L)
      (fun _ => a, fun _ => b)
      (triangularTorusEdgeWeight L t1 t2 t3)
      (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e)
  rw [surfaceTwistedKacWardMatrix_triangularTorusDartEquiv_apply]
  unfold triangularTorusSeamKWMatrix
  by_cases hs : (d.1.1 - e.1.1, d.1.2 - e.1.2) =
      triangularTorusDirectionStep L d.2
  · rw [if_pos hs]
    have hc := (triangularTorusDartEquiv_consecutive_iff L d e).mpr hs
    by_cases he : e = triangularTorusDartReverse L d
    · subst e
      have hedge := (triangularTorusDartEquiv_edge_eq_iff_reverse
        L d (triangularTorusDartReverse L d) hc).mpr rfl
      rw [if_neg (fun h => h.2 hedge)]
      rw [show (triangularTorusDartReverse L d).2 =
        triangularTorusDirectionReverse d.2 from rfl,
        triangularKacWardTurnMatrix_reverse_zero]
      ring
    · have hedge : (triangularTorusDartEquiv L d).edge ≠
          (triangularTorusDartEquiv L e).edge := by
        intro h
        exact he ((triangularTorusDartEquiv_edge_eq_iff_reverse
          L d e hc).mp h)
      rw [if_pos ⟨hc, hedge⟩]
  · rw [if_neg hs]
    have hc : ¬(triangularTorusDartEquiv L d).snd =
        (triangularTorusDartEquiv L e).fst := fun h =>
      hs ((triangularTorusDartEquiv_consecutive_iff L d e).mp h)
    rw [if_neg (fun h => hc h.1)]



theorem det_one_sub_triangularTorusSeamKWMatrix_eq_surfaceTwisted
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    (1 - triangularTorusSeamKWMatrix L t1 t2 t3 rho a b).det =
      (1 - surfaceTwistedKacWardMatrix (triangularTorusGraph L)
        (triangularTorusGraphPhase L rho 1 1)
        (triangularTorusSurfaceEdgeClass L)
        (fun _ => a, fun _ => b)
        (triangularTorusEdgeWeight L t1 t2 t3)).det := by
  rw [triangularTorusSeamKWMatrix_eq_reindex_surfaceTwisted]
  let e := (triangularTorusDartEquiv L).symm
  let M := surfaceTwistedKacWardMatrix (triangularTorusGraph L)
    (triangularTorusGraphPhase L rho 1 1)
    (triangularTorusSurfaceEdgeClass L)
    (fun _ => a, fun _ => b)
    (triangularTorusEdgeWeight L t1 t2 t3)
  have hsub : 1 - Matrix.reindex e e M =
      Matrix.reindex e e (1 - M) := by
    ext d f
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hsub, Matrix.det_reindex_self]

end StatMech.FrontierA
