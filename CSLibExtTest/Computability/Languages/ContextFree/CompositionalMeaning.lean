/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.CompositionalMeaning

/-!
# Tests for the fragment meanings

Two actual parses of one token string, Fin 2 separating and boundary
values, rejected invalid productions and ill-typed application, and
capture-avoiding instantiation.
-/

@[expose] public section

namespace Cslib.Language.CompositionalFragment.MeaningTest

open Cslib.Languages.LambdaCalculus.Stlc
open Cslib.Language.CompositionalFragment
open scoped CslibStlc

/-! ### Two actual parses of one token string -/

/-- Both parses are valid, `S`-rooted and yield the same three tokens, and
they are distinct trees. -/
private theorem two_parses_one_word :
    IsValidTree Token g surfaceTree ∧ IsValidTree Token g inverseTree ∧
      surfaceTree.rootOf = catS ∧ inverseTree.rootOf = catS ∧
      surfaceTree.yieldOf = word ∧ inverseTree.yieldOf = word ∧
      surfaceTree ≠ inverseTree := by
  refine ⟨surfaceTree_valid, inverseTree_valid, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- Classification consumed semantically: in the identity model on `Fin 2`,
a valid `S`-rooted tree is true exactly when it is the surface parse. -/
private theorem fin2_id_true_iff_surface (tr : PDerivTree Cat Token)
    (h : IsValidTree Token g tr) (hr : tr.rootOf = catS) :
    meaning (Fin 2) (fun _ => True) (fun x y => x = y) tr h hr ↔
      tr = surfaceTree := by
  have hP : ∀ x : Fin 2, True → ∃ y : Fin 2, True ∧ x = y :=
    fun x _ => ⟨x, trivial, rfl⟩
  have hQ : ¬ ∃ y : Fin 2, True ∧ ∀ x : Fin 2, True → x = y := by
    rintro ⟨y, -, hAll⟩
    have h0 := hAll 0 trivial
    have h1 := hAll 1 trivial
    have h01 : (0 : Fin 2) = 1 := h0.trans h1.symm
    have hNe : (0 : Fin 2) ≠ 1 := by decide
    exact hNe h01
  have hClass := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun x y => x = y)).2.2 tr h hr
  rw [hClass]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨-, hQ'⟩)
    · rfl
    · exact absurd hQ' hQ
  · intro hEq
    subst hEq
    left
    exact ⟨rfl, hP⟩

/-! ### Fin 2 separating and boundary values -/

private theorem fin2_id_surface_true :
    meaning (Fin 2) (fun _ => True) (fun x y => x = y)
      surfaceTree surfaceTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun x y => x = y)).1
  rw [hM]
  intro x _
  exact ⟨x, trivial, rfl⟩

private theorem fin2_id_inverse_false :
    ¬ meaning (Fin 2) (fun _ => True) (fun x y => x = y)
      inverseTree inverseTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun x y => x = y)).2.1
  rw [hM]
  rintro ⟨y, -, hAll⟩
  have h0 := hAll 0 trivial
  have h1 := hAll 1 trivial
  have h01 : (0 : Fin 2) = 1 := h0.trans h1.symm
  have hNe : (0 : Fin 2) ≠ 1 := by decide
  exact hNe h01

private theorem fin2_universal_surface_true :
    meaning (Fin 2) (fun _ => True) (fun _ _ => True)
      surfaceTree surfaceTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun _ _ => True)).1
  rw [hM]
  intro x _
  exact ⟨0, trivial, trivial⟩

private theorem fin2_universal_inverse_true :
    meaning (Fin 2) (fun _ => True) (fun _ _ => True)
      inverseTree inverseTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun _ _ => True)).2.1
  rw [hM]
  exact ⟨0, trivial, fun _ _ => trivial⟩

private theorem fin2_empty_surface_false :
    ¬ meaning (Fin 2) (fun _ => True) (fun _ _ => False)
      surfaceTree surfaceTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun _ _ => False)).1
  rw [hM]
  intro h
  obtain ⟨y, -, hF⟩ := h 0 trivial
  exact hF

private theorem fin2_empty_inverse_false :
    ¬ meaning (Fin 2) (fun _ => True) (fun _ _ => False)
      inverseTree inverseTree_valid rfl := by
  have hM := (surface_inverse_meanings (Fin 2) (fun _ => True)
    (fun _ _ => False)).2.1
  rw [hM]
  rintro ⟨y, -, hAll⟩
  exact hAll 0 trivial

/-! ### Invalid productions are rejected -/

private theorem leaf_subj_someone_not_valid :
    ¬ IsValidTree Token g (PDerivTree.leaf catSubj someoneTok) := by
  unfold IsValidTree
  decide

private theorem node_s_tv_obj_not_valid :
    ¬ IsValidTree Token g
      (PDerivTree.node catS catTV catObj
        (PDerivTree.leaf catTV admiresTok)
        (PDerivTree.leaf catObj someoneTok)) := by
  intro h
  unfold IsValidTree at h
  obtain ⟨hmem, _, _, _, _⟩ := h
  revert hmem
  decide

/-! ### Ill-typed Q-to-Q application is rejected -/

/-- No arrow type with domain `Q` equals `Q`: `Q` takes a `P` argument. -/
private theorem qTy_not_arr_qTy (B : Ty Bool) : QTy ≠ QTy ⇒ B := by
  intro h
  unfold QTy PTy eTy tTy at h
  injection h with h1 h2
  injection h1 with h3 h4
  cases h3

-- The elaborator rejects applying `everybody : Q` to `someone : Q`.
/--
error: Application type mismatch: The argument
  someoneTm
has type
  Tm LexCtx QTy
but is expected to have type
  Tm LexCtx PTy
in the application
  everybodyTm.app someoneTm
-/
#guard_msgs in
example : Tm LexCtx tTy := Tm.app everybodyTm someoneTm

/-! ### Capture-avoiding instantiation of `(λ x. λ y. x)` at free `z` -/

/-- Body of `λ x. λ y. x` under its outer binder: `λ y. x` in `[e, e]`. -/
private def captureBody : Tm [eTy, eTy] (eTy ⇒ eTy) :=
  Tm.lam (Tm.var (Var.succ Var.zero))

/-- The free variable `z` in context `[e]`. -/
private def captureZ : Tm [eTy] eTy := Tm.var Var.zero

/-- The existing instantiation: `λ y. z`. -/
private def captureTerm : Tm [eTy] (eTy ⇒ eTy) :=
  Tm.instantiate captureBody captureZ

private def fin2Zero : Fin 2 := 0
private def fin2One : Fin 2 := 1

/-- Syntactically, instantiation returns `λ y. z`, not the captured `λ y. y`. -/
private theorem capture_term :
    captureTerm = Tm.lam (Tm.var (Var.succ Var.zero)) ∧
      captureTerm ≠ Tm.lam (Tm.var Var.zero) := by
  constructor
  · rfl
  · intro h
    have h1 : captureTerm = Tm.lam (Tm.var (Var.succ Var.zero)) := rfl
    rw [h1] at h
    injection h with _ _ _ htm
    injection htm with _ _ hvar
    cases hvar

/-- The redex `(λ x. λ y. x) z` and its instantiation have the same meaning
(via `Tm.denote_instantiate`). -/
private theorem capture_redex_denote (η : Env (ID (Fin 2)) [eTy]) :
    Tm.denote (ID (Fin 2)) (Tm.app (Tm.lam captureBody) captureZ) η =
      Tm.denote (ID (Fin 2)) captureTerm η := by
  have hInst := Tm.denote_instantiate (ID (Fin 2)) captureBody captureZ η
  have hApp : Tm.denote (ID (Fin 2)) (Tm.app (Tm.lam captureBody) captureZ) η =
      Tm.denote (ID (Fin 2)) captureBody
        (Env.cons (Tm.denote (ID (Fin 2)) captureZ η) η) := rfl
  exact hApp.trans hInst.symm

/-- With `z = 0` and inner argument `y = 1`, the value is `0`, not `1`. -/
private theorem capture_denote (η : Env (ID (Fin 2)) [eTy])
    (hη : η (Var.zero : Var [eTy] eTy) = fin2Zero) :
    Tm.denote (ID (Fin 2)) captureTerm η fin2One = fin2Zero ∧
      Tm.denote (ID (Fin 2)) captureTerm η fin2One ≠ fin2One := by
  have hterm : captureTerm = Tm.lam (Tm.var (Var.succ Var.zero)) := rfl
  rw [hterm]
  have hcomp : Tm.denote (ID (Fin 2))
      (Tm.lam (Tm.var (Var.succ Var.zero) : Tm [eTy, eTy] eTy) :
        Tm [eTy] (eTy ⇒ eTy))
      η fin2One = η (Var.zero : Var [eTy] eTy) := rfl
  rw [hcomp, hη]
  constructor
  · rfl
  · show (0 : Fin 2) ≠ 1
    decide

end Cslib.Language.CompositionalFragment.MeaningTest
