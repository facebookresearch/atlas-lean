/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialBoundaryPermutation

open Equiv

namespace StatMech.FrontierD

variable {T : EvenTorus}


def fkMedialBlackDart0 (v : T.Vertex) : FKMedialBlackDart T := by
  let side := if fkMedialVertexParity v then FKMedialSide.south else .west
  refine ⟨(v, side), ?_⟩
  unfold fkMedialCheckerColor side
  by_cases h : fkMedialVertexParity v <;>
    simp [h, fkMedialSideVertical]


def fkMedialBlackDart1 (v : T.Vertex) : FKMedialBlackDart T := by
  let side := if fkMedialVertexParity v then FKMedialSide.north else .east
  refine ⟨(v, side), ?_⟩
  unfold fkMedialCheckerColor side
  by_cases h : fkMedialVertexParity v <;>
    simp [h, fkMedialSideVertical]

theorem fkMedialBlackDart0_ne_dart1 (v : T.Vertex) :
    fkMedialBlackDart0 v ≠ fkMedialBlackDart1 v := by
  intro h
  have hs := congrArg (fun d : FKMedialBlackDart T => d.1.2) h
  by_cases hp : fkMedialVertexParity v <;>
    simp [fkMedialBlackDart0, fkMedialBlackDart1, hp] at hs


def fkMedialBlackSideIndex : FKMedialSide → Bool
  | .west | .south => false
  | .east | .north => true


def fkMedialBlackDartEquivVertexBool (T : EvenTorus) :
    FKMedialBlackDart T ≃ T.Vertex × Bool where
  toFun d := (d.1.1, fkMedialBlackSideIndex d.1.2)
  invFun vb := if vb.2 then fkMedialBlackDart1 vb.1 else fkMedialBlackDart0 vb.1
  left_inv d := by
    apply Subtype.ext
    rcases d with ⟨⟨v, side⟩, hd⟩
    cases side <;> by_cases hp : fkMedialVertexParity v <;>
      simp [fkMedialBlackSideIndex, fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialCheckerColor, fkMedialSideVertical, hp] at hd ⊢
  right_inv vb := by
    rcases vb with ⟨v, b⟩
    cases b <;> by_cases hp : fkMedialVertexParity v <;>
      simp [fkMedialBlackSideIndex, fkMedialBlackDart0, fkMedialBlackDart1, hp]

theorem card_fkMedialBlackDart (T : EvenTorus) :
    Fintype.card (FKMedialBlackDart T) = 2 * T.width * T.height := by
  rw [Fintype.card_congr (fkMedialBlackDartEquivVertexBool T)]
  simp [EvenTorus.Vertex]
  ring


theorem fkMedialBlackDart_eq_zero_or_one (d : FKMedialBlackDart T) :
    d = fkMedialBlackDart0 d.1.1 \/
      d = fkMedialBlackDart1 d.1.1 := by
  have h := (fkMedialBlackDartEquivVertexBool T).symm_apply_apply d
  change (if fkMedialBlackSideIndex d.1.2 then
      fkMedialBlackDart1 d.1.1 else fkMedialBlackDart0 d.1.1) = d at h
  cases hside : fkMedialBlackSideIndex d.1.2
  · exact Or.inl (by simpa [hside] using h.symm)
  · exact Or.inr (by simpa [hside] using h.symm)


def fkMedialBlackDartSwap (v : T.Vertex) : Perm (FKMedialBlackDart T) :=
  Equiv.swap (fkMedialBlackDart0 v) (fkMedialBlackDart1 v)

theorem fkMedialBlackDartSwap_isSwap (v : T.Vertex) :
    (fkMedialBlackDartSwap v).IsSwap :=
  Equiv.Perm.swap_isSwap_iff.mpr (fkMedialBlackDart0_ne_dart1 v)

set_option maxHeartbeats 800000 in

theorem fkMedialBlackBoundaryPerm_toggle
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v) =
      fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rcases d with ⟨⟨w, side⟩, hd⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;>
      cases hc : fkMedialVertexParity v <;> cases side <;>
      simp [fkMedialBlackBoundaryPerm_val, fkMedialBlackDartSwap,
        fkMedialBlackDart0, fkMedialBlackDart1, fkMedialCheckerColor,
        fkMedialSideVertical, fkMedialTogglePairingAt, fkMedialLocalMate,
        Equiv.Perm.mul_apply, hp, hc] at hd ⊢
  · have hne0 : (⟨w, side⟩ : FKMedialDart T) ≠
        (fkMedialBlackDart0 v).1 := by
      intro h
      exact hw (congrArg (fun d : FKMedialDart T => d.1) h)
    have hne1 : (⟨w, side⟩ : FKMedialDart T) ≠
        (fkMedialBlackDart1 v).1 := by
      intro h
      exact hw (congrArg (fun d : FKMedialDart T => d.1) h)
    have hne0' : (⟨⟨w, side⟩, hd⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart0 v := fun h => hne0 (congrArg Subtype.val h)
    have hne1' : (⟨⟨w, side⟩, hd⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart1 v := fun h => hne1 (congrArg Subtype.val h)
    simp only [fkMedialBlackBoundaryPerm_val, fkMedialBlackDartSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne0' hne1']
    cases side <;>
      simp [fkMedialLocalMate, fkMedialTogglePairingAt, hw]



theorem fkMedialLoopCount_toggle_mod_two
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) % 2 =
      (fkMedialLoopCount T pairing + 1) % 2 := by
  rw [← permCycleCount_fkMedialBlackBoundaryPerm,
    ← permCycleCount_fkMedialBlackBoundaryPerm]
  apply StatMech.FrontierA.permCycleCount_mod_two_toggle_of_sign_neg
  rw [fkMedialBlackBoundaryPerm_toggle, map_mul,
    (fkMedialBlackDartSwap_isSwap v).sign_eq]
  norm_num

@[simp] theorem fkMedialTogglePairingAt_toggle
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing v) v =
      pairing := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [fkMedialTogglePairingAt]
  · simp [fkMedialTogglePairingAt, hw]


theorem fkMedialLoopCount_toggle_dichotomy
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) + 1 =
        fkMedialLoopCount T pairing ∨
      fkMedialLoopCount T pairing + 1 =
        fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) := by
  have hforward := fkMedialLoopCount_toggle_le_add_one T pairing v
  have hreverse := fkMedialLoopCount_toggle_le_add_one T
    (fkMedialTogglePairingAt pairing v) v
  rw [fkMedialTogglePairingAt_toggle] at hreverse
  have hparity := fkMedialLoopCount_toggle_mod_two T pairing v
  omega

end StatMech.FrontierD
