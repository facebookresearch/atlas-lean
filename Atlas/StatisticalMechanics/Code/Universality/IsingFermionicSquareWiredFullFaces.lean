/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.IsingFermionicSquareWiredClosedFibers
import Code.Universality.IsingFermionicSquareWiredRibbon

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD
open StatMech.FrontierA

noncomputable section




def fkIsingSquareWedgeFaceKey (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int × Int :=
  let u := fkIsingSquareDartEndpoint n d
  match fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2 with
  | .east, .counterclockwise => (u.1 0, u.1 1)
  | .east, .clockwise => (u.1 0, u.1 1 - 1)
  | .north, .counterclockwise => (u.1 0 - 1, u.1 1)
  | .north, .clockwise => (u.1 0, u.1 1)
  | .west, .counterclockwise => (u.1 0 - 1, u.1 1 - 1)
  | .west, .clockwise => (u.1 0 - 1, u.1 1)
  | .south, .counterclockwise => (u.1 0, u.1 1 - 1)
  | .south, .clockwise => (u.1 0 - 1, u.1 1 - 1)

def fkIsingSquareInteriorFaceKey (n : Nat) (p : Int × Int) : Prop :=
  -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int)

theorem fkIsingSquareWedgeFaceKey_open_localMate
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWedgeFaceKey n
        (FKIsingMedialDart.localMate
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) d) =
      fkIsingSquareWedgeFaceKey n d := by
  rcases d with ⟨e, side⟩
  have hopen : FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset e.1 = true := by
    rw [FK.edgeSetConfig_apply]
    exact SimpleGraph.mem_edgeFinset.mpr e.2
  have hstep := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
    cases side <;>
    simp only [FKIsingMedialDart.localMate] <;>
    rw [show FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset e.1 = true from hopen] <;>
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] at hstep ⊢
  all_goals
    have h0 := congrFun hstep 0
    have h1 := congrFun hstep 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Fin.succ_zero_eq_one] at h0 h1
    constructor <;> omega

set_option maxHeartbeats 2000000 in
theorem fkIsingSquareWedgeFaceKey_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdint : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n d)) :
    fkIsingSquareWedgeFaceKey n (fkIsingSquareBondMate n hn d) =
      fkIsingSquareWedgeFaceKey n d := by
  let u := fkIsingSquareDartEndpoint n d
  let q := fkIsingSquareDartDirection n d
  let hq := fkIsingSquareDartDirection_available n d
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases ht : (fkIsingSquareSideCorner d.2).2 <;>
    cases hqdir : q <;>
    by_cases hE : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hN : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hW : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hS : fkIsingSquareDirectionAvailable n u .south <;>
    have hE' := hE <;>
    have hN' := hN <;>
    have hW' := hW <;>
    have hS' := hS <;>
    simp [fkIsingSquareDirectionAvailable, u] at hE' hN' hW' hS' <;>
    simp [fkIsingSquareDirectionAvailable, u, q, hqdir] at hq <;>
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareInteriorFaceKey,
      u, q, ht, hqdir] at hdint <;>
    simp [u] at b0 b1 <;>
    simp [fkIsingSquareBondMate, fkIsingSquareWedgeFaceKey,
      fkIsingSquareNextDirection, fkIsingSquarePreviousDirection,
      u, q, ht, hqdir, hE, hN, hW, hS] <;>
    omega

theorem fkIsingSquareWiredBoundaryDart_faceKey_not_interior
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    ¬ fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i <;>
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareWiredBoundaryDart, fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareMarkedA,
      fkIsingSquareMarkedB]

theorem fkIsingSquareWiredBondMate_eq_bondMate_of_interior
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n d)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  have hdout : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, rfl⟩
    exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn i hd
  have hBout : fkIsingSquareBondMate n hn d ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
    rintro ⟨i, hi⟩
    have hinter : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (fkIsingSquareBondMate n hn d)) := by
      rw [fkIsingSquareWedgeFaceKey_bondMate n hn d hd]
      exact hd
    rw [← hi] at hinter
    exact fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn i hinter
  have hfix : sigma d = d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hdout
  have hfix' : sigma.symm d = d := by
    calc
      sigma.symm d = sigma.symm (sigma d) := congrArg sigma.symm hfix.symm
      _ = d := sigma.symm_apply_apply d
  have hBfix : sigma (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBout
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [show (fkIsingSquareWiredShiftDartEquiv n hn).symm d = d by exact hfix']
  exact hBfix

def fkIsingSquareWiredBlackFaceKey (n : Nat) :
    FKIsingSquareWiredBlackCarrier n → Option (Int × Int)
  | ⟨.dart d, _⟩ =>
      some (fkIsingSquareWedgeFaceKey n d)
  | ⟨.bond d, _⟩ =>
      some (fkIsingSquareWedgeFaceKey n d)
  | ⟨.source, _⟩ => none
  | ⟨.terminal, _⟩ => none

private theorem fkIsingSquareWiredBlackFaceKey_boundaryStep_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareWiredBlackCarrier n)
    (p : Int × Int)
    (hx : fkIsingSquareWiredBlackFaceKey n x = some p)
    (hp : fkIsingSquareInteriorFaceKey n p) :
    fkIsingSquareWiredBlackFaceKey n
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) x) =
      some p := by
  rcases x with ⟨x, hcolor⟩
  cases x with
  | source => simp [fkIsingSquareWiredBlackFaceKey] at hx
  | terminal => simp [fkIsingSquareWiredBlackFaceKey] at hx
  | dart d =>
      have hkey : fkIsingSquareWedgeFaceKey n d = p := by
        simpa [fkIsingSquareWiredBlackFaceKey] using hx
      simp only [fkIsingSquareWiredBlackBoundaryPerm,
        Equiv.Perm.subtypePerm_apply, fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply, fkIsingSquareWiredTransitionEquiv]
      change fkIsingSquareWiredBlackFaceKey n ⟨.bond
          (FKIsingMedialDart.localMate
            (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) d), _⟩ = _
      simp only [fkIsingSquareWiredBlackFaceKey, Option.some.injEq]
      rw [fkIsingSquareWedgeFaceKey_open_localMate, hkey]
  | bond d =>
      have hkey : fkIsingSquareWedgeFaceKey n d = p := by
        simpa [fkIsingSquareWiredBlackFaceKey] using hx
      have hdint : fkIsingSquareInteriorFaceKey n
          (fkIsingSquareWedgeFaceKey n d) := by simpa only [hkey] using hp
      have hnotSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        intro h
        subst d
        exact (fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .bottom)
          hdint
      have hnotTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro h
        subst d
        exact (fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .top)
          hdint
      have htrans : fkIsingSquareWiredTransitionEquiv n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) (.bond d) =
          .bond (fkIsingSquareWiredBondMate n hn d) := by
        change fkIsingSquareWiredTransitionMate n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) (.bond d) = _
        simp [fkIsingSquareWiredTransitionMate, hnotSource, hnotTerminal]
      simp only [fkIsingSquareWiredBlackBoundaryPerm,
        Equiv.Perm.subtypePerm_apply, fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply]
      simp only [htrans]
      change fkIsingSquareWiredBlackFaceKey n
        ⟨.dart (fkIsingSquareWiredBondMate n hn d), _⟩ = _
      simp only [fkIsingSquareWiredBlackFaceKey, Option.some.injEq]
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d hdint,
        fkIsingSquareWedgeFaceKey_bondMate n hn d hdint, hkey]

private theorem fkIsingSquareWiredBlackFaceKey_pow_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareWiredBlackCarrier n)
    (p : Int × Int)
    (hx : fkIsingSquareWiredBlackFaceKey n x = some p)
    (hp : fkIsingSquareInteriorFaceKey n p) :
    ∀ k : Nat, fkIsingSquareWiredBlackFaceKey n
      (((fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ k) x) = some p := by
  intro k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact fkIsingSquareWiredBlackFaceKey_boundaryStep_of_interior
        n hn _ p ih hp

abbrev FKIsingSquareInteriorCell (n : Nat) := Fin (2 * n) × Fin (2 * n)

def fkIsingSquareInteriorCellKey (n : Nat)
    (c : FKIsingSquareInteriorCell n) : Int × Int :=
  (-(n : Int) + c.1.val, -(n : Int) + c.2.val)

def fkIsingSquareInteriorCellVertex (n : Nat)
    (c : FKIsingSquareInteriorCell n) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int) + c.1.val, -(n : Int) + c.2.val], by
    intro i
    fin_cases i <;> simp
    · have hi := c.1.isLt
      omega
    · have hj := c.2.isLt
      omega⟩

theorem fkIsingSquareInteriorCellVertex_east_available
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareInteriorCellVertex n c) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareInteriorCellVertex]
  have hi := c.1.isLt
  omega

def fkIsingSquareInteriorCellDart (n : Nat)
    (c : FKIsingSquareInteriorCell n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionDart n (fkIsingSquareInteriorCellVertex n c) .east
    (fkIsingSquareInteriorCellVertex_east_available n c) .counterclockwise

def fkIsingSquareInteriorCellBlack (n : Nat)
    (c : FKIsingSquareInteriorCell n) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (fkIsingSquareInteriorCellDart n c), by
    simp [fkIsingSquareInteriorCellDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
      fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor]⟩

@[simp] theorem fkIsingSquareInteriorCellBlack_faceKey
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareWiredBlackFaceKey n (fkIsingSquareInteriorCellBlack n c) =
      some (fkIsingSquareInteriorCellKey n c) := by
  simp [fkIsingSquareInteriorCellBlack, fkIsingSquareInteriorCellDart,
    fkIsingSquareWiredBlackFaceKey, fkIsingSquareWedgeFaceKey,
    fkIsingSquareInteriorCellKey, fkIsingSquareInteriorCellVertex]

theorem fkIsingSquareInteriorCellKey_interior
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareInteriorFaceKey n (fkIsingSquareInteriorCellKey n c) := by
  rcases c with ⟨i, j⟩
  simp [fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey]
  constructor
  · have hi : (i.val : Int) < 2 * (n : Int) := by
      exact_mod_cast i.isLt
    omega
  · have hj : (j.val : Int) < 2 * (n : Int) := by
      exact_mod_cast j.isLt
    omega

theorem fkIsingSquareInteriorCellKey_injective (n : Nat) :
    Function.Injective (fkIsingSquareInteriorCellKey n) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrArg Prod.fst h
    simp [fkIsingSquareInteriorCellKey] at h0
    omega
  · apply Fin.ext
    have h1 := congrArg Prod.snd h
    simp [fkIsingSquareInteriorCellKey] at h1
    omega

noncomputable def fkIsingSquareWiredFullInteriorCycle
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorCell n →
      StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) :=
  fun c ↦ Quot.mk _ (fkIsingSquareInteriorCellBlack n c)

theorem fkIsingSquareWiredFullInteriorCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullInteriorCycle n hn) := by
  intro c d hcd
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareInteriorCellBlack n d) :=
    Quotient.exact hcd
  obtain ⟨k, hk⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) k
  rw [hk, fkIsingSquareInteriorCellBlack_faceKey] at hkey
  apply fkIsingSquareInteriorCellKey_injective n
  exact Option.some.inj hkey.symm

private theorem fkIsingSquareWiredBoundaryDart_west_eq_leftEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryDart n hn (.west k) =
      (fkIsingSquareLeftVerticalEdge n hn k, .west) := by
  apply Prod.ext
  · apply Subtype.ext
    change s(fkIsingSquareLeftVerticalLower n hn k,
        fkIsingSquareNeighbor n (fkIsingSquareLeftVerticalLower n hn k) .north
          (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
      s(fkIsingSquareLeftVerticalUpper n hn k,
        fkIsingSquareNeighbor n (fkIsingSquareLeftVerticalUpper n hn k) .south
          (fkIsingSquareLeftVerticalUpper_south_available n hn k))
    rw [Sym2.eq_iff]
    apply Or.inr
    constructor
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [fkIsingSquareWiredBoundaryDart,
          fkIsingSquareDirectionDart, fkIsingSquareLeftVerticalEdge,
          fkIsingSquareDirectionEdge, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper, Pi.add_apply]
    · apply Subtype.ext
      funext i
      fin_cases i <;>
        simp [fkIsingSquareWiredBoundaryDart,
          fkIsingSquareDirectionDart, fkIsingSquareLeftVerticalEdge,
          fkIsingSquareDirectionEdge, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
          fkIsingSquareLeftVerticalUpper, Pi.add_apply]
  · rfl

private theorem fkIsingSquareWiredBoundaryDart_north_eq_leftEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryDart n hn (.north k) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) := by
  rfl

def fkIsingSquareWiredFullLeftDart (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (fkIsingSquareWiredBoundaryDart n hn (.west k)), by
    rw [fkIsingSquareWiredBoundaryDart_west_eq_leftEdge]
    rfl⟩

def fkIsingSquareWiredFullLeftBond (n : Nat) (hn : 0 < n)
    (k : Fin (2 * n)) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.bond (fkIsingSquareWiredBoundaryDart n hn (.north k)), by
    simp [fkIsingSquareWiredCarrierColor, fkIsingSquareWiredBoundaryDart,
      fkIsingSquareDirectionDart_turn, fkIsingSquareWiredTurnColor]⟩

private theorem fkIsingSquareWiredFullLeftDart_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareWiredFullLeftDart n hn k) =
      fkIsingSquareWiredFullLeftBond n hn k := by
  have hopen : FK.edgeSetConfig (boxGraph 2 n).edgeFinset
      (fkIsingSquareLeftVerticalEdge n hn k).1 = true := by
    rw [FK.edgeSetConfig_apply]
    exact SimpleGraph.mem_edgeFinset.mpr
      (fkIsingSquareLeftVerticalEdge n hn k).2
  have hlocal : FKIsingMedialDart.localMate
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareLeftVerticalEdge n hn k, .west) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) := by
    simp [FKIsingMedialDart.localMate, FK.edgeSetConfig]
  apply Subtype.ext
  simp only [fkIsingSquareWiredFullLeftDart,
    fkIsingSquareWiredFullLeftBond]
  simp only [fkIsingSquareWiredBoundaryDart_west_eq_leftEdge,
    fkIsingSquareWiredBoundaryDart_north_eq_leftEdge]
  simp [fkIsingSquareWiredBlackBoundaryPerm,
    fkIsingSquareWiredBoundaryStep, fkIsingSquareWiredTransitionEquiv,
    fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredFullLeftDart, fkIsingSquareWiredFullLeftBond,
    show FKIsingMedialDart.localMate
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareLeftVerticalEdge n hn k, .west) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) from hlocal]
  exact hlocal

private theorem fkIsingSquareWiredFullLeftBond_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareWiredFullLeftBond n hn k) =
      fkIsingSquareWiredFullLeftDart n hn k := by
  have hns : fkIsingSquareWiredBoundaryDart n hn (.north k) ≠
      fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hnt : fkIsingSquareWiredBoundaryDart n hn (.north k) ≠
      fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  apply Subtype.ext
  simp [fkIsingSquareWiredBlackBoundaryPerm,
    fkIsingSquareWiredBoundaryStep, fkIsingSquareWiredTransitionEquiv,
    fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredFullLeftDart, fkIsingSquareWiredFullLeftBond,
    hns, hnt]

private theorem fkIsingSquareWiredFullLeftDart_pow_mem
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    ∀ m : Nat,
      ((fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ m)
          (fkIsingSquareWiredFullLeftDart n hn k) =
          fkIsingSquareWiredFullLeftDart n hn k ∨
      ((fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ m)
          (fkIsingSquareWiredFullLeftDart n hn k) =
          fkIsingSquareWiredFullLeftBond n hn k := by
  intro m
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with ih | ih
      · rw [ih, fkIsingSquareWiredFullLeftDart_step]
        exact Or.inr rfl
      · rw [ih, fkIsingSquareWiredFullLeftBond_step]
        exact Or.inl rfl

noncomputable def fkIsingSquareWiredFullLeftCycle
    (n : Nat) (hn : 0 < n) :
    Fin (2 * n) → StatMech.FrontierA.PermCycleClass
      (fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) :=
  fun k ↦ Quot.mk _ (fkIsingSquareWiredFullLeftDart n hn k)

theorem fkIsingSquareWiredFullLeftCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullLeftCycle n hn) := by
  intro k l hkl
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareWiredFullLeftDart n hn k)
        (fkIsingSquareWiredFullLeftDart n hn l) :=
    Quotient.exact hkl
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hor := fkIsingSquareWiredFullLeftDart_pow_mem n hn k m
  rw [hm] at hor
  rcases hor with h | h
  · have hv := congrArg Subtype.val h
    simp only [fkIsingSquareWiredFullLeftDart,
      FKIsingSquareWiredCarrier.dart.injEq] at hv
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn hv
    cases hi
    rfl
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullLeftDart,
      fkIsingSquareWiredFullLeftBond] at hv

def fkIsingSquareWiredFullExteriorBlack (n : Nat) :
    FKIsingSquareWiredBlackCarrier n := ⟨.terminal, rfl⟩

private theorem fkIsingSquareWiredFullLeftCycle_ne_exterior
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    Quot.mk (Equiv.Perm.SameCycle.setoid
      (fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)))
        (fkIsingSquareWiredFullLeftDart n hn k) ≠
      Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n) := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareWiredFullLeftDart n hn k)
        (fkIsingSquareWiredFullExteriorBlack n) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hor := fkIsingSquareWiredFullLeftDart_pow_mem n hn k m
  rw [hm] at hor
  rcases hor with h | h
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullExteriorBlack,
      fkIsingSquareWiredFullLeftDart] at hv
  · have hv := congrArg Subtype.val h
    simp [fkIsingSquareWiredFullExteriorBlack,
      fkIsingSquareWiredFullLeftBond] at hv

private theorem fkIsingSquareWiredFullInteriorCycle_ne_left
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareInteriorCell n)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredFullInteriorCycle n hn c ≠
      fkIsingSquareWiredFullLeftCycle n hn k := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareWiredFullLeftDart n hn k) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) m
  rw [hm] at hkey
  simp only [fkIsingSquareWiredFullLeftDart,
    fkIsingSquareWiredBlackFaceKey, Option.some.injEq] at hkey
  apply fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn (.west k)
  rw [hkey]
  exact fkIsingSquareInteriorCellKey_interior n c

private theorem fkIsingSquareWiredFullInteriorCycle_ne_exterior
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareWiredFullInteriorCycle n hn c ≠
      Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n) := by
  intro h
  have hcycle : (fkIsingSquareWiredBlackBoundaryPerm n hn
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).SameCycle
        (fkIsingSquareInteriorCellBlack n c)
        (fkIsingSquareWiredFullExteriorBlack n) :=
    Quotient.exact h
  obtain ⟨m, hm⟩ := hcycle.exists_nat_pow_eq
  have hkey := fkIsingSquareWiredBlackFaceKey_pow_of_interior n hn
    (fkIsingSquareInteriorCellBlack n c)
    (fkIsingSquareInteriorCellKey n c)
    (fkIsingSquareInteriorCellBlack_faceKey n c)
    (fkIsingSquareInteriorCellKey_interior n c) m
  rw [hm] at hkey
  simpa [fkIsingSquareWiredFullExteriorBlack,
    fkIsingSquareWiredBlackFaceKey] using hkey

abbrev FKIsingSquareWiredFullCycleIndex (n : Nat) :=
  FKIsingSquareInteriorCell n ⊕ Option (Fin (2 * n))

noncomputable def fkIsingSquareWiredFullCycle
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredFullCycleIndex n →
      StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset))
  | Sum.inl c => fkIsingSquareWiredFullInteriorCycle n hn c
  | Sum.inr (some k) => fkIsingSquareWiredFullLeftCycle n hn k
  | Sum.inr none => Quot.mk _ (fkIsingSquareWiredFullExteriorBlack n)

theorem fkIsingSquareWiredFullCycle_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredFullCycle n hn) := by
  intro a b hab
  rcases a with c | o <;> rcases b with d | p
  · exact congrArg Sum.inl
      (fkIsingSquareWiredFullInteriorCycle_injective n hn hab)
  · cases p with
    | none => exact (fkIsingSquareWiredFullInteriorCycle_ne_exterior
        n hn c hab).elim
    | some k => exact (fkIsingSquareWiredFullInteriorCycle_ne_left
        n hn c k hab).elim
  · cases o with
    | none => exact (fkIsingSquareWiredFullInteriorCycle_ne_exterior
        n hn d hab.symm).elim
    | some k => exact (fkIsingSquareWiredFullInteriorCycle_ne_left
        n hn d k hab.symm).elim
  · cases o with
    | none =>
        cases p with
        | none => rfl
        | some k => exact (fkIsingSquareWiredFullLeftCycle_ne_exterior
            n hn k hab.symm).elim
    | some k =>
        cases p with
        | none => exact (fkIsingSquareWiredFullLeftCycle_ne_exterior
            n hn k hab).elim
        | some l =>
            exact congrArg (fun j => Sum.inr (some j))
              (fkIsingSquareWiredFullLeftCycle_injective n hn hab)

theorem fkIsingSquareWired_full_completed_componentCount_lower
    (n : Nat) (hn : 0 < n) :
    (2 * n + 1) ^ 2 - 2 * n ≤
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent := by
  have hcard := Nat.card_le_card_of_injective
    (fkIsingSquareWiredFullCycle n hn)
    (fkIsingSquareWiredFullCycle_injective n hn)
  rw [StatMech.FrontierA.natCard_permCycleClass,
    permCycleCount_fkIsingSquareWiredBlackBoundaryPerm] at hcard
  have hsource : Nat.card (FKIsingSquareWiredFullCycleIndex n) =
      (2 * n + 1) ^ 2 - 2 * n := by
    rw [Nat.card_eq_fintype_card]
    simp [FKIsingSquareWiredFullCycleIndex, FKIsingSquareInteriorCell]
    have hid : (2 * n + 1) ^ 2 =
        (2 * n) * (2 * n) + (2 * n + 1) + 2 * n := by ring
    omega
  rwa [hsource] at hcard

private theorem fkIsingSquareWiredEulerDefect_empty_le_full
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) ≤
      fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) := by
  classical
  let E := (fkSquareBoxPlanar n).G.edgeFinset
  let defect := fkIsingSquareWiredEulerDefect n hn
  let F : Finset (Sym2 (fkSquareBoxPlanar n).V) → Int :=
    fun A ↦ defect (FK.edgeSetConfig (A ∩ E))
  have hinsert : ∀ (A : Finset (Sym2 (fkSquareBoxPlanar n).V))
      (e : Sym2 (fkSquareBoxPlanar n).V), e ∉ A → F A ≤ F (insert e A) := by
    intro A e heA
    by_cases heE : e ∈ E
    · let em : FKIsingMedialVertex (fkSquareBoxPlanar n) :=
        ⟨e, by simpa only [E, SimpleGraph.mem_edgeFinset] using heE⟩
      have heAE : e ∉ A ∩ E := by simp [heA]
      have hclosed : setClosed e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heAE]
        · simp [setClosed, hfe]
      have hopen : setOpen e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (insert e A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heE]
        · simp [FK.edgeSetConfig, setOpen, hfe]
      have hmono := fkIsingSquareWiredEulerDefect_setClosed_le_setOpen
        n hn (FK.edgeSetConfig (A ∩ E)) em
      simpa only [F, defect, em, hclosed, hopen] using hmono
    · have hinter : insert e A ∩ E = A ∩ E := by
        ext f
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hfA, hfE⟩
          · exact False.elim (heE hfE)
          · exact ⟨hfA, hfE⟩
        · rintro ⟨hfA, hfE⟩
          exact ⟨Or.inr hfA, hfE⟩
      rw [show F (insert e A) = F A by simp only [F, hinter]]
  have hmono : Monotone F :=
    Finset.monotone_iff_forall_le_insert.mpr hinsert
  have h := hmono (Finset.empty_subset E)
  simpa [F, defect, E] using h



theorem fkIsingSquareWired_full_completed_componentCount
    (n : Nat) (hn : 0 < n) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (FK.edgeSetConfig
          (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent =
      (2 * n + 1) ^ 2 - 2 * n := by
  apply le_antisymm
  · have hdef := fkIsingSquareWiredEulerDefect_empty_le_full n hn
    rw [fkIsingSquareWiredEulerDefect_empty_formula,
      fkIsingSquareWiredEulerDefect_full_formula,
      fkIsingSquareWired_empty_completed_componentCount n hn] at hdef
    have hcast :
        (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
          (FK.edgeSetConfig
            (fkSquareBoxPlanar n).G.edgeFinset)).ConnectedComponent : Int) ≤
          ((2 * n + 1) ^ 2 - 2 * n : Nat) := by
      omega
    exact_mod_cast hcast
  · exact fkIsingSquareWired_full_completed_componentCount_lower n hn


theorem fkIsingSquareWiredEulerDefect_empty_full
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredEulerDefect n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
      fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) := by
  apply (fkIsingSquareWiredEulerDefect_empty_full_iff_componentCount n hn).2
  rw [fkIsingSquareWired_full_completed_componentCount n hn,
    fkIsingSquareWired_empty_completed_componentCount n hn]


theorem fkIsingSquareWiredEulerDefect_toggle_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
      fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) :=
  fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq n hn
    (fkIsingSquareWiredEulerDefect_empty_full n hn) omega e

end

end StatMech.Universality
