/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitSplitTag
import Code.FrontierA.GrahamFourColorBalancedCore











open Finset

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaOrientedFourColorDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def lpReplicaRowTagEquivFin4 : LPReplicaRowTag ≃ Fin 4 where
  toFun
    | (false, false) => 0
    | (false, true) => 1
    | (true, false) => 2
    | (true, true) => 3
  invFun x :=
    if x = 0 then (false, false)
    else if x = 1 then (false, true)
    else if x = 2 then (true, false)
    else (true, true)
  left_inv := by
    rintro ⟨r, c⟩
    cases r <;> cases c <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl


def lpReplicaTagFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    ↑(Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) ->
      Fin 4 :=
  fun c => lpReplicaRowTagEquivFin4 (tag c.1)

theorem lpReplicaTagFourColor_colorClass_zero
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 =
      lpReplicaCurrentCopies G sites m tag false false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_one
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 =
      lpReplicaCurrentCopies G sites m tag false true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_two
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 2 =
      lpReplicaCurrentCopies G sites m tag true false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_colorClass_three
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    colorClass Finset.univ (lpReplicaTagFourColor G sites m tag) 3 =
      lpReplicaCurrentCopies G sites m tag true true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [colorClass, lpReplicaTagFourColor, lpReplicaRowTagEquivFin4,
      lpReplicaCurrentCopies, htag]

theorem lpReplicaTagFourColor_rowClass_zero
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 0 =
      lpReplicaRowCopies G sites m tag false := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [rowClass, colorClass, lpReplicaTagFourColor,
      lpReplicaRowTagEquivFin4, lpReplicaRowCopies, htag]

theorem lpReplicaTagFourColor_rowClass_one
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    rowClass Finset.univ (lpReplicaTagFourColor G sites m tag) 1 =
      lpReplicaRowCopies G sites m tag true := by
  classical
  ext c
  rcases htag : tag c with ⟨r, current⟩
  cases r <;> cases current <;>
    simp [rowClass, colorClass, lpReplicaTagFourColor,
      lpReplicaRowTagEquivFin4, lpReplicaRowCopies, htag]



theorem lpReplicaRowGate_iff_leftPattern_tagFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    LPReplicaRowGate G sites m A B tag ↔
      LeftPattern (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        A B lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
        (lpReplicaTagFourColor G sites m tag) := by
  unfold LPReplicaRowGate LeftPattern RowsDisconnect
  rw [lpReplicaTagFourColor_colorClass_zero,
    lpReplicaTagFourColor_colorClass_one,
    lpReplicaTagFourColor_colorClass_two,
    lpReplicaTagFourColor_colorClass_three,
    lpReplicaTagFourColor_rowClass_zero,
    lpReplicaTagFourColor_rowClass_one]
  constructor
  · rintro ⟨h0, h1, hd0, h2, h3, hd1⟩
    exact ⟨h0, h1, h2, h3, hd0, hd1⟩
  · rintro ⟨h0, h1, h2, h3, hd0, hd1⟩
    exact ⟨h0, h1, hd0, h2, h3, hd1⟩


def LPReplicaOrientedFourColorFiber
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :=
  Σ a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      p <= m.1},
    (LPReplicaCollisionSplitLabel G sites m.1 a.1 ×
      LPReplicaProfileOrbitLabel G sites q m.1) ×
      (↑(lpReplicaDisconnProfileFamily G sites A a.1) ×
        ↑(lpReplicaDisconnProfileFamily G sites B
          (lpReplicaReflectedResidual G sites m.1 a.1)))

noncomputable instance instFintypeLPReplicaOrientedFourColorFiber
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :
    Fintype (LPReplicaOrientedFourColorFiber G sites A B q m) := by
  unfold LPReplicaOrientedFourColorFiber
  infer_instance


def LPReplicaOrientedFourColorAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q},
    LPReplicaOrientedFourColorFiber G sites A B q m

noncomputable instance instFintypeLPReplicaOrientedFourColorAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrientedFourColorAtom G sites A B q) := by
  unfold LPReplicaOrientedFourColorAtom
  infer_instance



def lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaDecoratedOrbitAtom G sites A B q ≃
      LPReplicaOrientedFourColorAtom G sites A B q where
  toFun z := ⟨z.1.1, z.1.2.1,
    ((z.2.1, z.2.2), (z.1.2.2.1, z.1.2.2.2))⟩
  invFun z := ⟨⟨z.1, ⟨z.2.1, (z.2.2.2.1, z.2.2.2.2)⟩⟩,
    (z.2.2.1.1, z.2.2.1.2)⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl


theorem card_lpReplicaOrientedFourColorFiber
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :
    Fintype.card (LPReplicaOrientedFourColorFiber G sites A B q m) =
      ∑ a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          p <= m.1},
        lpReplicaCollisionSplitMultiplicity G sites m.1 a.1 *
          lpReplicaProfileOrbitMultiplicity G sites q m.1 *
          (lpReplicaDisconnProfileFamily G sites A a.1).card *
          (lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m.1 a.1)).card := by
  classical
  unfold LPReplicaOrientedFourColorFiber
  change Fintype.card (Σ a :
      {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // p <= m.1},
      (LPReplicaCollisionSplitLabel G sites m.1 a.1 ×
        LPReplicaProfileOrbitLabel G sites q m.1) ×
        (↑(lpReplicaDisconnProfileFamily G sites A a.1) ×
          ↑(lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m.1 a.1)))) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    card_lpReplicaCollisionSplitLabel, card_lpReplicaProfileOrbitLabel,
    Fintype.card_coe, Fintype.card_coe]
  ring



theorem card_lpReplicaOrientedFourColorAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrientedFourColorAtom G sites A B q) =
      Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) := by
  exact Fintype.card_congr
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
      G sites A B q).symm


def lpReplicaOrientedFourColorTag
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    Copy (lpReplicaCurrentGraph G sites) z.1.1 -> LPReplicaRowTag :=
  lpReplicaOrbitCollisionSplitTag G sites z.1.1 z.2.1.1
    z.2.2.1.1 (Finset.mem_filter.mp z.2.2.1.1.2).2
      z.2.2.2.1.1 z.2.2.2.2.1



theorem lpReplicaOrientedFourColorTag_leftPattern
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    LeftPattern (endsM (lpReplicaCurrentGraph G sites) z.1.1) Finset.univ
      A (B.map lpReplicaCurrentReflect.toEmbedding)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
      (lpReplicaTagFourColor G sites z.1.1
        (lpReplicaOrientedFourColorTag G sites A B q z)) := by
  rw [← lpReplicaRowGate_iff_leftPattern_tagFourColor]
  exact lpReplicaRowGate_orbitCollisionSplitTag
    G sites z.1.1 z.2.1.1 z.2.1.2 z.2.2.1.1
      (Finset.mem_filter.mp z.2.2.1.1.2).2
      z.2.2.2.1.1 z.2.2.2.2.1 A B
      z.2.2.2.1.2 z.2.2.2.2.2

end

end StatMech.Ising
