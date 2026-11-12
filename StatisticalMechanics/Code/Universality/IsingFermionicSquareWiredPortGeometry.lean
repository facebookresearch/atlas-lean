/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Code.Universality.IsingFermionicSquareWiredTangentCode
import Code.FrontierA.KacWardAdaptiveClosure
import Code.FrontierA.KacWardRectilinearPolygonBridge












namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section


def fkIsingSquareWiredUnitDiagonalStep : Fin 4 → Int × Int :=
  ![(-1, -1), (-1, 1), (1, -1), (1, 1)]


def fkIsingSquareWiredUnitDiagonalReverse : Fin 4 → Fin 4 :=
  ![3, 2, 1, 0]

theorem fkIsingSquareWiredUnitDiagonalStep_injective :
    Function.Injective fkIsingSquareWiredUnitDiagonalStep := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] at h ⊢

theorem fkIsingSquareWiredUnitDiagonalStep_add_reverse (a : Fin 4) :
    fkIsingSquareWiredUnitDiagonalStep a +
      fkIsingSquareWiredUnitDiagonalStep
        (fkIsingSquareWiredUnitDiagonalReverse a) = 0 := by
  fin_cases a <;> decide


def fkIsingSquareWiredIntPoint (p : Int × Int) : Complex :=
  (p.1 : Real) + (p.2 : Real) * Complex.I

theorem fkIsingSquareWiredIntPoint_injective :
    Function.Injective fkIsingSquareWiredIntPoint := by
  rintro ⟨px, py⟩ ⟨qx, qy⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [fkIsingSquareWiredIntPoint] at hre him
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast him


theorem fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
    (p q : Int × Int) (a : Fin 4) :
    ¬Sbtw Real (fkIsingSquareWiredIntPoint p)
      (fkIsingSquareWiredIntPoint q)
      (fkIsingSquareWiredIntPoint
        (p + fkIsingSquareWiredUnitDiagonalStep a)) := by
  intro hbetween
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hbetween.mem_image_Ioo
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  have hre := congrArg Complex.re ht
  fin_cases a <;>
    simp [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      AffineMap.lineMap_apply] at hre
  · have hloR : (-1 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 0 := by linarith
    have hlo : (-1 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (-1 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 0 := by linarith
    have hlo : (-1 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 1 := by linarith
    have hlo : (0 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 1 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qx : Real) - px := by linarith
    have hhiR : (qx : Real) - px < 1 := by linarith
    have hlo : (0 : Int) < qx - px := by exact_mod_cast hloR
    have hhi : qx - px < 1 := by exact_mod_cast hhiR
    omega



theorem fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
    (p q : Int × Int) (a b : Fin 4) (z : Complex)
    (hp : Sbtw Real (fkIsingSquareWiredIntPoint p) z
      (fkIsingSquareWiredIntPoint
        (p + fkIsingSquareWiredUnitDiagonalStep a)))
    (hq : Sbtw Real (fkIsingSquareWiredIntPoint q) z
      (fkIsingSquareWiredIntPoint
        (q + fkIsingSquareWiredUnitDiagonalStep b))) :
    p + (p + fkIsingSquareWiredUnitDiagonalStep a) =
      q + (q + fkIsingSquareWiredUnitDiagonalStep b) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hp.mem_image_Ioo
  obtain ⟨u, ⟨hu0, hu1⟩, huz⟩ := hq.mem_image_Ioo
  have heq : AffineMap.lineMap (fkIsingSquareWiredIntPoint (px, py))
        (fkIsingSquareWiredIntPoint
          ((px, py) + fkIsingSquareWiredUnitDiagonalStep a)) t =
      AffineMap.lineMap (fkIsingSquareWiredIntPoint (qx, qy))
        (fkIsingSquareWiredIntPoint
          ((qx, qy) + fkIsingSquareWiredUnitDiagonalStep b)) u :=
    htz.trans huz.symm
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      AffineMap.lineMap_apply, Prod.ext_iff] at hre him ⊢
  all_goals
    have hxloR : (-2 : Real) < (qx : Real) - (px : Real) := by linarith
    have hxhiR : (qx : Real) - (px : Real) < 2 := by linarith
    have hyloR : (-2 : Real) < (qy : Real) - (py : Real) := by linarith
    have hyhiR : (qy : Real) - (py : Real) < 2 := by linarith
    have hxlo : (-2 : Int) < qx - px := by exact_mod_cast hxloR
    have hxhi : qx - px < (2 : Int) := by exact_mod_cast hxhiR
    have hylo : (-2 : Int) < qy - py := by exact_mod_cast hyloR
    have hyhi : qy - py < (2 : Int) := by exact_mod_cast hyhiR
    interval_cases hx : qx - px <;>
      interval_cases hy : qy - py <;>
      have hxR := congrArg (fun x : Int => (x : Real)) hx <;>
      have hyR := congrArg (fun x : Int => (x : Real)) hy <;>
      push_cast at hxR hyR <;>
      first
      | constructor <;> omega
      | (exfalso; linarith)



noncomputable def fkIsingSquareWiredUnitDiagonalSimplePolygon
    {m : Nat} [NeZero m] (vertex : Fin m → Int × Int)
    (direction : Fin m → Fin 4)
    (hstep : ∀ i, vertex (i + 1) =
      vertex i + fkIsingSquareWiredUnitDiagonalStep (direction i))
    (hm : 3 ≤ m) (hinjective : Function.Injective vertex)
    (hmidpoint : Function.Injective
      (fun i => vertex i + vertex (i + 1))) :
    StatMech.FrontierA.KWFiniteSimplePolygon m where
  vertex := fun i => fkIsingSquareWiredIntPoint (vertex i)
  three_le := hm
  vertex_injective := fkIsingSquareWiredIntPoint_injective.comp hinjective
  vertex_not_strictly_between := by
    intro i j _ _
    rw [hstep i]
    exact fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
      (vertex i) (vertex j) (direction i)
  edgeInteriors_disjoint := by
    intro i j hij
    apply Set.disjoint_left.2
    intro z hzi hzj
    apply hij
    apply hmidpoint
    change vertex i + vertex (i + 1) = vertex j + vertex (j + 1)
    rw [hstep i, hstep j]
    exact fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
      (vertex i) (vertex j) (direction i) (direction j) z
      (by simpa [hstep i] using hzi) (by simpa [hstep j] using hzj)




theorem fkIsingSquareWired_cycle_turn_mod_sixteen_of_simplePolygon
    {m : Nat} [NeZero m]
    (polygon : StatMech.FrontierA.KWFiniteSimplePolygon m)
    (turn : Int)
    (hphase : Complex.exp
        (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) =
      StatMech.FrontierA.kwVectorPhaseCycle polygon.edgeList) :
    turn ≡ 8 [ZMOD 16] := by
  apply int_eighth_turn_mod_sixteen_of_exp_eq_neg_one
  rw [hphase]
  exact StatMech.FrontierA.kwFiniteSimplePolygonPhaseSign_adaptive polygon



def fkIsingSquareWiredPortIntPosition (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int × Int :=
  let edge := fkIsingSquareOrientedEdge n d.1
  let x := edge.tail.1 0
  let y := edge.tail.1 1
  match edge.axis, d.2 with
  | .horizontal, .west => (4 * x + 1, 4 * y)
  | .horizontal, .south => (4 * x + 2, 4 * y - 1)
  | .horizontal, .east => (4 * x + 3, 4 * y)
  | .horizontal, .north => (4 * x + 2, 4 * y + 1)
  | .vertical, .west => (4 * x - 1, 4 * y + 2)
  | .vertical, .south => (4 * x, 4 * y + 1)
  | .vertical, .east => (4 * x + 1, 4 * y + 2)
  | .vertical, .north => (4 * x, 4 * y + 3)

private theorem fkIsingSquareMedialVertex_eq_of_oriented_tail_axis
    (n : Nat) (e f : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (haxis : (fkIsingSquareOrientedEdge n e).axis =
      (fkIsingSquareOrientedEdge n f).axis)
    (htail : (fkIsingSquareOrientedEdge n e).tail =
      (fkIsingSquareOrientedEdge n f).tail) :
    e = f := by
  let a := fkIsingSquareOrientedEdge n e
  let b := fkIsingSquareOrientedEdge n f
  have haStep := a.step
  have hbStep := b.step
  have hhead : a.head = b.head := by
    apply Subtype.ext
    cases ha : a.axis <;> cases hb : b.axis
    · simp only [ha] at haStep
      simp only [hb] at hbStep
      rw [haStep, hbStep, htail]
    · simp [a, b, ha, hb] at haxis
    · simp [a, b, ha, hb] at haxis
    · simp only [ha] at haStep
      simp only [hb] at hbStep
      rw [haStep, hbStep, htail]
  apply Subtype.ext
  calc
    e.1 = s(a.tail, a.head) := a.edge_eq.symm
    _ = s(b.tail, b.head) := by rw [htail, hhead]
    _ = f.1 := b.edge_eq


theorem fkIsingSquareWiredPortIntPosition_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredPortIntPosition n) := by
  intro d f hpos
  rcases d with ⟨e, side⟩
  rcases f with ⟨f, side'⟩
  let a := fkIsingSquareOrientedEdge n e
  let b := fkIsingSquareOrientedEdge n f
  have hx := congrArg Prod.fst hpos
  have hy := congrArg Prod.snd hpos
  cases ha : a.axis <;> cases hb : b.axis <;>
    cases side <;> cases side' <;>
    simp [fkIsingSquareWiredPortIntPosition, a, b, ha, hb] at hx hy
  all_goals try omega
  all_goals
    have htail0 : a.tail.1 0 = b.tail.1 0 := by omega
    have htail1 : a.tail.1 1 = b.tail.1 1 := by omega
    have htail : a.tail = b.tail := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact htail0
      · exact htail1
    have haxis : a.axis = b.axis := ha.trans hb.symm
    have hef : e = f :=
      fkIsingSquareMedialVertex_eq_of_oriented_tail_axis n e f haxis htail
    subst f
    rfl


theorem fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    ∃ a : Fin 4,
      fkIsingSquareWiredPortIntPosition n
          (FKIsingMedialDart.localMate omega d) =
        fkIsingSquareWiredPortIntPosition n d +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases d with ⟨e, side⟩
  let a : Fin 4 := match omega e.1, side with
    | false, .west => 2
    | false, .south => 1
    | false, .east => 1
    | false, .north => 2
    | true, .west => 3
    | true, .south => 3
    | true, .east => 0
    | true, .north => 0
  refine ⟨a, ?_⟩
  cases homega : omega e.1 <;> cases side <;>
    simp only [FKIsingMedialDart.localMate, homega] <;>
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [a, homega, fkIsingSquareWiredPortIntPosition, haxis,
      fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] <;> omega


def fkIsingSquareWiredPortOffset :
    FKIsingSquareDirection → FKIsingSquareCornerTurn → Int × Int
  | .east, .counterclockwise => (1, 0)
  | .east, .clockwise => (2, -1)
  | .north, .counterclockwise => (-1, 2)
  | .north, .clockwise => (0, 1)
  | .west, .counterclockwise => (-1, 0)
  | .west, .clockwise => (-2, 1)
  | .south, .counterclockwise => (1, -2)
  | .south, .clockwise => (0, -1)



theorem fkIsingSquareWiredPortIntPosition_directionDart
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortIntPosition n
        (fkIsingSquareDirectionDart n u d hd turn) =
      (4 * u.1 0, 4 * u.1 1) +
        fkIsingSquareWiredPortOffset d turn := by
  cases d <;> cases turn <;>
    simp [fkIsingSquareWiredPortIntPosition, fkIsingSquareDirectionDart,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareCornerSide,
      fkIsingSquareEndpointForDirection, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareWiredPortOffset,
      Prod.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail] <;> omega



def fkIsingSquareWiredPortOctagonOffset : Fin 8 → Int × Int :=
  ![(1, -2), (2, -1), (1, 0), (0, 1),
    (-1, 2), (-2, 1), (-1, 0), (0, -1)]


def fkIsingSquareWiredPortSlot :
    FKIsingSquareDirection → FKIsingSquareCornerTurn → Fin 8
  | .east, .clockwise => 1
  | .east, .counterclockwise => 2
  | .north, .clockwise => 3
  | .north, .counterclockwise => 4
  | .west, .clockwise => 5
  | .west, .counterclockwise => 6
  | .south, .clockwise => 7
  | .south, .counterclockwise => 0


def fkIsingSquareWiredPortSlotDirection : Fin 8 → FKIsingSquareDirection :=
  ![.south, .east, .east, .north, .north, .west, .west, .south]


def fkIsingSquareWiredPortSlotTurn : Fin 8 → FKIsingSquareCornerTurn :=
  ![.counterclockwise, .clockwise, .counterclockwise, .clockwise,
    .counterclockwise, .clockwise, .counterclockwise, .clockwise]

@[simp] theorem fkIsingSquareWiredPortSlot_direction_turn (i : Fin 8) :
    fkIsingSquareWiredPortSlot
        (fkIsingSquareWiredPortSlotDirection i)
        (fkIsingSquareWiredPortSlotTurn i) = i := by
  fin_cases i <;> rfl

@[simp] theorem fkIsingSquareWiredPortSlotDirection_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortSlotDirection
        (fkIsingSquareWiredPortSlot d turn) = d := by
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareWiredPortSlotTurn_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortSlotTurn
        (fkIsingSquareWiredPortSlot d turn) = turn := by
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareWiredPortOctagonOffset_slot
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareWiredPortOctagonOffset
        (fkIsingSquareWiredPortSlot d turn) =
      fkIsingSquareWiredPortOffset d turn := by
  cases d <;> cases turn <;> rfl


theorem fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal (i : Fin 8) :
    ∃ a : Fin 4,
      fkIsingSquareWiredPortOctagonOffset (i + 1) =
        fkIsingSquareWiredPortOctagonOffset i +
          fkIsingSquareWiredUnitDiagonalStep a := by
  fin_cases i
  · exact ⟨3, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨2, by decide⟩




noncomputable def fkIsingSquareWiredBondArcLength
    (n : Nat) (u : (fkSquareBoxPlanar n).V) :
    FKIsingSquareDirection → Fin 8 := by
  classical
  exact fun d => match d with
  | .east => if fkIsingSquareDirectionAvailable n u .north then 1
      else if fkIsingSquareDirectionAvailable n u .west then 3 else 5
  | .north => if fkIsingSquareDirectionAvailable n u .west then 1
      else if fkIsingSquareDirectionAvailable n u .south then 3 else 5
  | .west => if fkIsingSquareDirectionAvailable n u .south then 1
      else if fkIsingSquareDirectionAvailable n u .east then 3 else 5
  | .south => if fkIsingSquareDirectionAvailable n u .east then 1
      else if fkIsingSquareDirectionAvailable n u .north then 3 else 5

theorem fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredBondArcLength n u d = 1 ∨
      fkIsingSquareWiredBondArcLength n u d = 3 ∨
      fkIsingSquareWiredBondArcLength n u d = 5 := by
  classical
  cases d <;>
    simp only [fkIsingSquareWiredBondArcLength] <;>
    split_ifs <;> simp



theorem fkIsingSquareWiredPortSlot_nextDirection
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise =
      fkIsingSquareWiredPortSlot d .counterclockwise +
        fkIsingSquareWiredBondArcLength n u d := by
  classical
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp [fkIsingSquareNextDirection, fkIsingSquareWiredBondArcLength,
      he, hnorth, hw, hs, fkIsingSquareWiredPortSlot]


def fkIsingSquareWiredSlotIntPosition (n : Nat)
    (x : (fkSquareBoxPlanar n).V × Fin 8) : Int × Int :=
  (4 * x.1.1 0, 4 * x.1.1 1) +
    fkIsingSquareWiredPortOctagonOffset x.2

theorem fkIsingSquareWiredSlotIntPosition_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredSlotIntPosition n) := by
  rintro ⟨u, i⟩ ⟨v, j⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases i <;> fin_cases j <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset] at hx hy
  all_goals try omega
  all_goals
    have h0 : u.1 0 = v.1 0 := by omega
    have h1 : u.1 1 = v.1 1 := by omega
    have huv : u = v := by
      apply Subtype.ext
      funext k
      fin_cases k
      · exact h0
      · exact h1
    subst v
    rfl


noncomputable def fkIsingSquareWiredDartSlot (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkSquareBoxPlanar n).V × Fin 8 :=
  (fkIsingSquareDartEndpoint n d,
    fkIsingSquareWiredPortSlot (fkIsingSquareDartDirection n d)
      (fkIsingSquareSideCorner d.2).2)



def fkIsingSquareWiredSlotAvailable (n : Nat)
    (x : (fkSquareBoxPlanar n).V × Fin 8) : Prop :=
  fkIsingSquareDirectionAvailable n x.1
    (fkIsingSquareWiredPortSlotDirection x.2)


noncomputable def fkIsingSquareWiredDartOfSlot (n : Nat)
    (x : (fkSquareBoxPlanar n).V × Fin 8)
    (h : fkIsingSquareWiredSlotAvailable n x) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionDart n x.1
    (fkIsingSquareWiredPortSlotDirection x.2) h
    (fkIsingSquareWiredPortSlotTurn x.2)

@[simp] theorem fkIsingSquareWiredDartSlot_dartOfSlot
    (n : Nat) (x : (fkSquareBoxPlanar n).V × Fin 8)
    (h : fkIsingSquareWiredSlotAvailable n x) :
    fkIsingSquareWiredDartSlot n
        (fkIsingSquareWiredDartOfSlot n x h) = x := by
  rcases x with ⟨u, i⟩
  simp [fkIsingSquareWiredDartOfSlot, fkIsingSquareWiredDartSlot]

@[simp] theorem fkIsingSquareWiredDartOfSlot_dartSlot
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredDartOfSlot n (fkIsingSquareWiredDartSlot n d)
        (by simpa [fkIsingSquareWiredSlotAvailable,
          fkIsingSquareWiredDartSlot] using
            fkIsingSquareDartDirection_available n d) = d := by
  simpa [fkIsingSquareWiredDartOfSlot,
    fkIsingSquareWiredDartSlot] using
      fkIsingSquareDirectionDart_reconstruct n d

theorem fkIsingSquareWiredSlotIntPosition_dartSlot
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredSlotIntPosition n
        (fkIsingSquareWiredDartSlot n d) =
      fkIsingSquareWiredPortIntPosition n d := by
  rw [← fkIsingSquareDirectionDart_reconstruct n d]
  simp [fkIsingSquareWiredDartSlot, fkIsingSquareWiredSlotIntPosition,
    fkIsingSquareWiredPortIntPosition_directionDart]

theorem fkIsingSquareWiredDartSlot_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredDartSlot n) := by
  intro d f h
  apply fkIsingSquareWiredPortIntPosition_injective n
  rw [← fkIsingSquareWiredSlotIntPosition_dartSlot n d,
    ← fkIsingSquareWiredSlotIntPosition_dartSlot n f, h]



theorem fkIsingSquareWiredSlotRingMidpoint_injective (n : Nat) :
    Function.Injective
      (fun x : (fkSquareBoxPlanar n).V × Fin 8 =>
        fkIsingSquareWiredSlotIntPosition n x +
          fkIsingSquareWiredSlotIntPosition n (x.1, x.2 + 1)) := by
  rintro ⟨u, i⟩ ⟨v, j⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases i <;> fin_cases j <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset] at hx hy
  all_goals try omega
  all_goals
    have h0 : u.1 0 = v.1 0 := by omega
    have h1 : u.1 1 = v.1 1 := by omega
    have huv : u = v := by
      apply Subtype.ext
      funext k
      fin_cases k
      · exact h0
      · exact h1
    subst v
    rfl



abbrev FKIsingSquareWiredSlotCarrier (n : Nat) :=
  (fkSquareBoxPlanar n).V × Fin 8



def fkIsingSquareWiredSlotRingActive (n : Nat)
    (x : FKIsingSquareWiredSlotCarrier n) : Prop :=
  fkIsingSquareWiredPortSlotTurn x.2 = .counterclockwise ∨
    ¬fkIsingSquareWiredSlotAvailable n x



noncomputable def fkIsingSquareWiredSlotRingGraph (n : Nat) :
    SimpleGraph (FKIsingSquareWiredSlotCarrier n) where
  Adj x y := ∃ u i, fkIsingSquareWiredSlotRingActive n (u, i) ∧
    ((x = (u, i) ∧ y = (u, i + 1)) ∨
      (y = (u, i) ∧ x = (u, i + 1)))
  symm := by
    rintro x y ⟨u, i, hi, h | h⟩
    · exact ⟨u, i, hi, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨u, i, hi, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    constructor
    rintro x ⟨u, i, _, h | h⟩
    · have hi := congrArg Prod.snd (h.1.symm.trans h.2)
      fin_cases i <;> simp at hi
    · have hi := congrArg Prod.snd (h.2.symm.trans h.1)
      fin_cases i <;> simp at hi


noncomputable def fkIsingSquareWiredSlotLocalGraph
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredSlotCarrier n) where
  Adj x y := ∃ d,
    (x = fkIsingSquareWiredDartSlot n d ∧
      y = fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)) ∨
    (y = fkIsingSquareWiredDartSlot n d ∧
      x = fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d))
  symm := by
    rintro x y ⟨d, h | h⟩
    · exact ⟨d, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨d, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    constructor
    rintro x ⟨d, h | h⟩
    · have heq := fkIsingSquareWiredDartSlot_injective n
        (h.1.symm.trans h.2)
      exact (fkIsingSquare_localMate_cornerTurn_ne n omega d)
        (congrArg (fun f => (fkIsingSquareSideCorner f.2).2) heq).symm
    · have heq := fkIsingSquareWiredDartSlot_injective n
        (h.2.symm.trans h.1)
      exact (fkIsingSquare_localMate_cornerTurn_ne n omega d)
        (congrArg (fun f => (fkIsingSquareSideCorner f.2).2) heq)


theorem fkIsingSquareWiredSlotRingGraph_step
    (n : Nat) {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotRingGraph n).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredSlotIntPosition n y =
        fkIsingSquareWiredSlotIntPosition n x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases h with ⟨u, i, _, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal i
    refine ⟨a, ?_⟩
    change
      (4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset (i + 1) =
        ((4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset i) +
            fkIsingSquareWiredUnitDiagonalStep a
    rw [ha]
    ext <;> simp <;> omega
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal i
    refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
    change
      (4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset i =
        ((4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset (i + 1)) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredUnitDiagonalReverse a)
    rw [ha]
    ext <;> fin_cases a <;>
      simp [fkIsingSquareWiredUnitDiagonalReverse,
        fkIsingSquareWiredUnitDiagonalStep] <;> omega

theorem fkIsingSquareWiredSlotRingGraph_adj_succ
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
    (fkIsingSquareWiredSlotRingGraph n).Adj (u, i) (u, i + 1) :=
  ⟨u, i, hactive, Or.inl ⟨rfl, rfl⟩⟩




theorem fkIsingSquareWiredSlotRingGraph_reachable_nextDirection
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    (fkIsingSquareWiredSlotRingGraph n).Reachable
      (u, fkIsingSquareWiredPortSlot d .counterclockwise)
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
  have step (i : Fin 8)
      (hi : fkIsingSquareWiredSlotRingActive n (u, i)) :
      (fkIsingSquareWiredSlotRingGraph n).Reachable (u, i) (u, i + 1) :=
    (fkIsingSquareWiredSlotRingGraph_adj_succ n u i hi).reachable
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · simpa [fkIsingSquareNextDirection, hnorth,
          fkIsingSquareWiredPortSlot] using
          step 2 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hnorth, hw,
            fkIsingSquareWiredPortSlot] using h23.trans (h34.trans h45)
        · have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hnorth, hw,
            fkIsingSquareWiredPortSlot] using
              h23.trans (h34.trans (h45.trans (h56.trans h67)))
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · simpa [fkIsingSquareNextDirection, hw,
          fkIsingSquareWiredPortSlot] using
          step 4 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hw, hs,
            fkIsingSquareWiredPortSlot] using h45.trans (h56.trans h67)
        · have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hw, hs,
            fkIsingSquareWiredPortSlot] using
              h45.trans (h56.trans (h67.trans (h70.trans h01)))
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · simpa [fkIsingSquareNextDirection, hs,
          fkIsingSquareWiredPortSlot] using
          step 6 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hs, he,
            fkIsingSquareWiredPortSlot] using h67.trans (h70.trans h01)
        · have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hs, he,
            fkIsingSquareWiredPortSlot] using
              h67.trans (h70.trans (h01.trans (h12.trans h23)))
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · simpa [fkIsingSquareNextDirection, he,
          fkIsingSquareWiredPortSlot] using
          step 0 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, he, hnorth,
            fkIsingSquareWiredPortSlot] using h01.trans (h12.trans h23)
        · have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, he, hnorth,
            fkIsingSquareWiredPortSlot] using
              h01.trans (h12.trans (h23.trans (h34.trans h45)))



private theorem walkCopy_exists_path_length
    {V : Type*} {G : SimpleGraph V} {a b a' b' : V}
    (p : G.Walk a b) (hp : p.IsPath) (ha : a = a') (hb : b = b') :
    ∃ q : G.Walk a' b', q.IsPath ∧ q.length = p.length := by
  let q := p.copy ha hb
  refine ⟨q, ?_, ?_⟩
  · simpa [q, SimpleGraph.Walk.isPath_def] using hp
  · simp [q]

private theorem fkIsingSquareWired_position_sum_eq_of_edge_eq_early
    {V : Type*} (position : V → Int × Int) {x y z w : V}
    (h : s(x, y) = s(z, w)) :
    position x + position y = position z + position w := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    abel

theorem fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (u, fkIsingSquareWiredPortSlot d .counterclockwise)
        (u, fkIsingSquareWiredPortSlot
          (fkIsingSquareNextDirection n u d) .clockwise),
      p.IsPath ∧ p.length = (fkIsingSquareWiredBondArcLength n u d).val := by
  have path1 (i : Fin 8)
      (hi : fkIsingSquareWiredSlotRingActive n (u, i)) :
      ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk (u, i) (u, i + 1),
        p.IsPath ∧ p.length = 1 := by
    let h := fkIsingSquareWiredSlotRingGraph_adj_succ n u i hi
    let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
    refine ⟨p, ?_, by simp [p]⟩
    simp [p, SimpleGraph.Walk.isPath_def]
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · obtain ⟨p, hp, hlen⟩ := path1 2 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hnorth,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hnorth]
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
            (SimpleGraph.Walk.cons h45 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hnorth, hw,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hnorth, hw]
        · let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
            (SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
              (SimpleGraph.Walk.cons h67 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hnorth, hw,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hnorth, hw]
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · obtain ⟨p, hp, hlen⟩ := path1 4 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hw,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hw]
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
            (SimpleGraph.Walk.cons h67 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hw, hs,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hw, hs]
        · let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
            (SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
              (SimpleGraph.Walk.cons h01 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hw, hs,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hw, hs]
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · obtain ⟨p, hp, hlen⟩ := path1 6 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hs,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hs]
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
            (SimpleGraph.Walk.cons h01 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hs, he,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hs, he]
        · let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
            (SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
              (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hs, he,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hs, he]
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · obtain ⟨p, hp, hlen⟩ := path1 0 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, he,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, he]
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
            (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, he, hnorth,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, he, hnorth]
        · let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
            (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
              (SimpleGraph.Walk.cons h45 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, he, hnorth,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, he, hnorth]



theorem fkIsingSquareWiredSlotRingGraph_reachable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredSlotRingGraph n).Reachable
      (fkIsingSquareWiredDartSlot n d)
      (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)) := by
  have hccw (x : FKIsingMedialDart (fkSquareBoxPlanar n))
      (hx : (fkIsingSquareSideCorner x.2).2 = .counterclockwise) :
      (fkIsingSquareWiredSlotRingGraph n).Reachable
        (fkIsingSquareWiredDartSlot n x)
        (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)) := by
    simpa [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hx] using
      fkIsingSquareWiredSlotRingGraph_reachable_nextDirection n hn
        (fkIsingSquareDartEndpoint n x)
        (fkIsingSquareDartDirection n x)
        (fkIsingSquareDartDirection_available n x)
  cases ht : (fkIsingSquareSideCorner d.2).2 with
  | counterclockwise =>
      exact hccw d ht
  | clockwise =>
      have hmateTurn :
          (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 =
            .counterclockwise := by
        simp [fkIsingSquareBondMate, ht]
      have hreach := hccw (fkIsingSquareBondMate n hn d) hmateTurn
      rw [fkIsingSquareBondMate_involutive n hn d] at hreach
      exact hreach.symm



theorem fkIsingSquareWiredSlotRingGraph_exists_path_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (fkIsingSquareWiredDartSlot n d)
        (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  have hccw (x : FKIsingMedialDart (fkSquareBoxPlanar n))
      (hx : (fkIsingSquareSideCorner x.2).2 = .counterclockwise) :
      ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
          (fkIsingSquareWiredDartSlot n x)
          (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)),
        p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
    obtain ⟨p, hp, hlen⟩ :=
      fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection n hn
        (fkIsingSquareDartEndpoint n x)
        (fkIsingSquareDartDirection n x)
        (fkIsingSquareDartDirection_available n x)
    have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five
      n (fkIsingSquareDartEndpoint n x) (fkIsingSquareDartDirection n x)
    have hresult : p.IsPath ∧
        (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
      refine ⟨hp, ?_⟩
      rw [hlen]
      rcases hcases with h | h | h <;> simp [h]
    obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
      (a' := fkIsingSquareWiredDartSlot n x)
      (b' := fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)) p hp
      (by simp [fkIsingSquareWiredDartSlot, hx])
      (by simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hx])
    exact ⟨q, hq, by simpa [hqLen] using hresult.2⟩
  cases ht : (fkIsingSquareSideCorner d.2).2 with
  | counterclockwise =>
      exact hccw d ht
  | clockwise =>
      have hmateTurn :
          (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 =
            .counterclockwise := by
        simp [fkIsingSquareBondMate, ht]
      obtain ⟨p, hp, hlen⟩ :=
        hccw (fkIsingSquareBondMate n hn d) hmateTurn
      obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
        (a' := fkIsingSquareWiredDartSlot n d)
        (b' := fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))
        p.reverse hp.reverse
        (by rw [fkIsingSquareBondMate_involutive n hn d]) rfl
      exact ⟨q, hq, by simpa [hqLen] using hlen⟩


theorem fkIsingSquareWiredSlotLocalGraph_step
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotLocalGraph n omega).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredSlotIntPosition n y =
        fkIsingSquareWiredSlotIntPosition n x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases h with ⟨d, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    simpa only [fkIsingSquareWiredSlotIntPosition_dartSlot] using
      fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal n omega d
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal n omega d
    refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
    rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
      fkIsingSquareWiredSlotIntPosition_dartSlot]
    rw [ha]
    ext <;> fin_cases a <;>
      simp [fkIsingSquareWiredUnitDiagonalReverse,
        fkIsingSquareWiredUnitDiagonalStep] <;> omega

set_option maxHeartbeats 2000000 in


theorem fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hmid :
      fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) =
        fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n f) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega f))) :
    s(fkIsingSquareWiredDartSlot n d,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)) =
      s(fkIsingSquareWiredDartSlot n f,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega f)) := by
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  rcases d with ⟨e, side⟩
  rcases f with ⟨f, side'⟩
  cases heaxis : (fkIsingSquareOrientedEdge n e).axis <;>
    cases hfaxis : (fkIsingSquareOrientedEdge n f).axis <;>
    cases heomega : omega e.1 <;> cases hfomega : omega f.1 <;>
    cases side <;> cases side' <;>
    simp only [FKIsingMedialDart.localMate, heomega, hfomega] at hx hy ⊢ <;>
    simp [fkIsingSquareWiredPortIntPosition, heaxis, hfaxis] at hx hy
  all_goals try omega
  all_goals
    have htail0 : (fkIsingSquareOrientedEdge n e).tail.1 0 =
        (fkIsingSquareOrientedEdge n f).tail.1 0 := by omega
    have htail1 : (fkIsingSquareOrientedEdge n e).tail.1 1 =
        (fkIsingSquareOrientedEdge n f).tail.1 1 := by omega
    have htail : (fkIsingSquareOrientedEdge n e).tail =
        (fkIsingSquareOrientedEdge n f).tail := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact htail0
      · exact htail1
    have haxis : (fkIsingSquareOrientedEdge n e).axis =
        (fkIsingSquareOrientedEdge n f).axis := heaxis.trans hfaxis.symm
    have hef : e = f :=
      fkIsingSquareMedialVertex_eq_of_oriented_tail_axis n e f haxis htail
    subst f
    simp_all [fkIsingSquareWiredDartSlot,
      FKIsingMedialDart.localMate]

set_option maxHeartbeats 2000000 in



theorem fkIsingSquareWiredSlotLocalRing_midpoint_ne
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
    fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) ≠
        fkIsingSquareWiredSlotIntPosition n (u, i) +
          fkIsingSquareWiredSlotIntPosition n (u, i + 1) := by
  intro hmid
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  have havailable := fkIsingSquareDartDirection_available n d
  rcases d with ⟨e, side⟩
  have hstep := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  all_goals
    simp only [haxis] at hstep <;>
    have hstep0 := congrFun hstep 0 <;>
    have hstep1 := congrFun hstep 1 <;>
    cases homega : omega e.1 <;> cases side <;> fin_cases i <;>
    simp only [FKIsingMedialDart.localMate, homega] at hx hy <;>
    simp [fkIsingSquareWiredPortIntPosition,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredSlotRingActive,
      fkIsingSquareWiredSlotAvailable,
      fkIsingSquareWiredPortSlotDirection,
      fkIsingSquareWiredPortSlotTurn,
      fkIsingSquareDartDirection,
      fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner,
      fkIsingSquareDirectionAvailable, haxis,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail]
        at hx hy havailable hactive hstep0 hstep1 <;>
    try omega



abbrev FKIsingSquareWiredExpandedCarrier (n : Nat) :=
  FKIsingSquareWiredSlotCarrier n ⊕ Fin (2 * n)




def fkIsingSquareWiredExpandedIntPosition (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredExpandedCarrier n → Int × Int
  | .inl x => fkIsingSquareWiredSlotIntPosition n x
  | .inr k =>
      let u := fkIsingSquareLeftVerticalLower n hn k
      (4 * u.1 0 - 2, 4 * u.1 1 + 3)

theorem fkIsingSquareWiredExpandedIntPosition_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredExpandedIntPosition n hn) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl
            (fkIsingSquareWiredSlotIntPosition_injective n h)
      | inr k =>
          exfalso
          rcases x with ⟨u, i⟩
          have hx := congrArg Prod.fst h
          have hy := congrArg Prod.snd h
          have ub0 := fkIsingSquareVertex_coordinate_bounds n u 0
          fin_cases i <;>
            simp [fkIsingSquareWiredExpandedIntPosition,
              fkIsingSquareWiredSlotIntPosition,
              fkIsingSquareWiredPortOctagonOffset,
              fkIsingSquareLeftVerticalLower] at hx hy <;> omega
  | inr k =>
      cases y with
      | inl y =>
          exfalso
          rcases y with ⟨u, i⟩
          have hx := congrArg Prod.fst h
          have hy := congrArg Prod.snd h
          have ub0 := fkIsingSquareVertex_coordinate_bounds n u 0
          fin_cases i <;>
            simp [fkIsingSquareWiredExpandedIntPosition,
              fkIsingSquareWiredSlotIntPosition,
              fkIsingSquareWiredPortOctagonOffset,
              fkIsingSquareLeftVerticalLower] at hx hy <;> omega
      | inr l =>
          apply congrArg Sum.inr
          apply Fin.ext
          have hy := congrArg Prod.snd h
          simp [fkIsingSquareWiredExpandedIntPosition,
            fkIsingSquareLeftVerticalLower] at hy
          omega

def fkIsingSquareWiredExpandedStart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalLower n hn k, 4)

def fkIsingSquareWiredExpandedMiddle
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 6)

def fkIsingSquareWiredExpandedEnd
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareWiredExpandedCarrier n :=
  .inl (fkIsingSquareLeftVerticalUpper n hn k, 7)


theorem fkIsingSquareWiredExpanded_bulge_steps
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareWiredExpandedIntPosition n hn (.inr k) =
      fkIsingSquareWiredExpandedIntPosition n hn
          (fkIsingSquareWiredExpandedStart n hn k) +
        fkIsingSquareWiredUnitDiagonalStep 1) ∧
    (fkIsingSquareWiredExpandedIntPosition n hn
        (fkIsingSquareWiredExpandedMiddle n hn k) =
      fkIsingSquareWiredExpandedIntPosition n hn (.inr k) +
        fkIsingSquareWiredUnitDiagonalStep 3) ∧
    (fkIsingSquareWiredExpandedIntPosition n hn
        (fkIsingSquareWiredExpandedEnd n hn k) =
      fkIsingSquareWiredExpandedIntPosition n hn
          (fkIsingSquareWiredExpandedMiddle n hn k) +
        fkIsingSquareWiredUnitDiagonalStep 2) := by
  simp [fkIsingSquareWiredExpandedIntPosition,
    fkIsingSquareWiredExpandedStart,
    fkIsingSquareWiredExpandedMiddle,
    fkIsingSquareWiredExpandedEnd,
    fkIsingSquareWiredSlotIntPosition,
    fkIsingSquareWiredPortOctagonOffset,
    fkIsingSquareWiredUnitDiagonalStep,
    fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper,
    Prod.ext_iff]
  omega



def fkIsingSquareWiredExpandedBulgeEndpoints
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    Fin 3 → FKIsingSquareWiredExpandedCarrier n ×
      FKIsingSquareWiredExpandedCarrier n
  | 0 => (fkIsingSquareWiredExpandedStart n hn k, .inr k)
  | 1 => ((.inr k : FKIsingSquareWiredExpandedCarrier n),
      fkIsingSquareWiredExpandedMiddle n hn k)
  | 2 => (fkIsingSquareWiredExpandedMiddle n hn k,
      fkIsingSquareWiredExpandedEnd n hn k)


def fkIsingSquareWiredExpandedBulgeEdge
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) (j : Fin 3) :
    Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
  s((fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).1,
    (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).2)


def fkIsingSquareWiredExpandedBulgeMidpoint
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) (j : Fin 3) : Int × Int :=
  fkIsingSquareWiredExpandedIntPosition n hn
      (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).1 +
    fkIsingSquareWiredExpandedIntPosition n hn
      (fkIsingSquareWiredExpandedBulgeEndpoints n hn k j).2



theorem fkIsingSquareWiredExpandedBulgeMidpoint_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fun x : Fin (2 * n) × Fin 3 =>
      fkIsingSquareWiredExpandedBulgeMidpoint n hn x.1 x.2) := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper] at hx hy
  all_goals try omega
  all_goals
    have hkl : k = l := Fin.ext (by omega)
    subst l
    rfl

set_option maxHeartbeats 1000000 in



theorem fkIsingSquareWiredSlotLocalBulge_midpoint_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n)) (j : Fin 3) :
    fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) ≠
        fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
  intro hmid
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  rcases d with ⟨e, side⟩
  have bt0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 0
  have bt1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 1
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  all_goals
    cases homega : omega e.1 <;> cases side <;> fin_cases j <;>
    simp only [FKIsingMedialDart.localMate, homega] at hx hy <;>
    simp [fkIsingSquareWiredPortIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper,
      haxis] at hx hy <;>
    omega


def fkIsingSquareWiredLeftRingRemoved (n : Nat)
    (x : FKIsingSquareWiredSlotCarrier n) : Prop :=
  x.1.1 0 = -(n : Int) ∧
    (x.2 = 4 ∨ x.2 = 5 ∨ x.2 = 6 ∨
      (x.1.1 1 = -(n : Int) ∧ (x.2 = 7 ∨ x.2 = 0)) ∨
      (x.1.1 1 = (n : Int) ∧ (x.2 = 2 ∨ x.2 = 3)))




theorem fkIsingSquareWiredSlotRingBulge_midpoint_ne
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hkeep : ¬fkIsingSquareWiredLeftRingRemoved n (u, i))
    (k : Fin (2 * n)) (j : Fin 3) :
    fkIsingSquareWiredSlotIntPosition n (u, i) +
          fkIsingSquareWiredSlotIntPosition n (u, i + 1) ≠
        fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
  intro hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  have bu0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have bu1 := fkIsingSquareVertex_coordinate_bounds n u 1
  fin_cases i <;> fin_cases j <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper,
      fkIsingSquareWiredLeftRingRemoved] at hx hy hkeep <;>
    omega



def fkIsingSquareWiredExpandedAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredExpandedCarrier n) : Prop :=
  (∃ a b, x = .inl a ∧ y = .inl b ∧
    (fkIsingSquareWiredSlotLocalGraph n omega).Adj a b) ∨
  (∃ a b, x = .inl a ∧ y = .inl b ∧
    ¬fkIsingSquareWiredLeftRingRemoved n a ∧
    ¬fkIsingSquareWiredLeftRingRemoved n b ∧
    (fkIsingSquareWiredSlotRingGraph n).Adj a b) ∨
  (∃ k : Fin (2 * n),
    s(x, y) = s(fkIsingSquareWiredExpandedStart n hn k, .inr k) ∨
    s(x, y) = s((.inr k : FKIsingSquareWiredExpandedCarrier n),
      fkIsingSquareWiredExpandedMiddle n hn k) ∨
    s(x, y) = s(fkIsingSquareWiredExpandedMiddle n hn k,
      fkIsingSquareWiredExpandedEnd n hn k))

theorem fkIsingSquareWiredExpandedAdj_symm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Symmetric (fkIsingSquareWiredExpandedAdj n hn omega) := by
  intro x y h
  rcases h with h | h | h
  · rcases h with ⟨a, b, rfl, rfl, hab⟩
    exact Or.inl ⟨b, a, rfl, rfl, hab.symm⟩
  · rcases h with ⟨a, b, rfl, rfl, ha, hb, hab⟩
    exact Or.inr (Or.inl ⟨b, a, rfl, rfl, hb, ha, hab.symm⟩)
  · exact Or.inr (Or.inr (by simpa only [Sym2.eq_swap] using h))

theorem fkIsingSquareWiredExpandedAdj_irrefl
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Irreflexive (fkIsingSquareWiredExpandedAdj n hn omega) := by
  intro x h
  rcases h with h | h | h
  · rcases h with ⟨a, b, hxa, hxb, hab⟩
    have habEq : a = b := Sum.inl.inj (hxa.symm.trans hxb)
    subst b
    exact (fkIsingSquareWiredSlotLocalGraph n omega).irrefl hab
  · rcases h with ⟨a, b, hxa, hxb, _, _, hab⟩
    have habEq : a = b := Sum.inl.inj (hxa.symm.trans hxb)
    subst b
    exact (fkIsingSquareWiredSlotRingGraph n).irrefl hab
  · rcases h with ⟨k, h | h | h⟩ <;> rw [Sym2.eq_iff] at h
    · rcases h with h | h
      · have hc := h.1.symm.trans h.2
        cases hc
      · have hc := h.2.symm.trans h.1
        cases hc
    · rcases h with h | h
      · have hc := h.1.symm.trans h.2
        cases hc
      · have hc := h.2.symm.trans h.1
        cases hc
    · rcases h with h | h
      · have heq := Sum.inl.inj (h.1.symm.trans h.2)
        have hi := congrArg Prod.snd heq
        have hiv := congrArg Fin.val hi
        norm_num at hiv
      · have heq := Sum.inl.inj (h.2.symm.trans h.1)
        have hi := congrArg Prod.snd heq
        have hiv := congrArg Fin.val hi
        norm_num at hiv


noncomputable def fkIsingSquareWiredExpandedGraph
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredExpandedCarrier n) where
  Adj := fkIsingSquareWiredExpandedAdj n hn omega
  symm := fkIsingSquareWiredExpandedAdj_symm n hn omega
  loopless := ⟨fkIsingSquareWiredExpandedAdj_irrefl n hn omega⟩

theorem fkIsingSquareWiredUnitDiagonal_step_reverse
    (p q : Int × Int) (a : Fin 4)
    (h : q = p + fkIsingSquareWiredUnitDiagonalStep a) :
    ∃ b : Fin 4, p = q + fkIsingSquareWiredUnitDiagonalStep b := by
  refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
  rw [h]
  ext <;> fin_cases a <;>
    simp [fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredUnitDiagonalStep] <;> omega



theorem fkIsingSquareWiredExpandedGraph_step
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredExpandedCarrier n}
    (h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredExpandedIntPosition n hn y =
        fkIsingSquareWiredExpandedIntPosition n hn x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  change fkIsingSquareWiredExpandedAdj n hn omega x y at h
  rcases h with h | h | h
  · rcases h with ⟨a, b, rfl, rfl, hab⟩
    simpa [fkIsingSquareWiredExpandedIntPosition] using
      fkIsingSquareWiredSlotLocalGraph_step n omega hab
  · rcases h with ⟨a, b, rfl, rfl, _, _, hab⟩
    simpa [fkIsingSquareWiredExpandedIntPosition] using
      fkIsingSquareWiredSlotRingGraph_step n hab
  · rcases h with ⟨k, h | h | h⟩ <;> rw [Sym2.eq_iff] at h
    all_goals rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨1, (fkIsingSquareWiredExpanded_bulge_steps n hn k).1⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 1
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).1
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨3, (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.1⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 3
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.1
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨2, (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 2
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.2

private theorem fkIsingSquareWiredExpandedGraph_reachable_of_ringWalk_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (p : (fkIsingSquareWiredSlotRingGraph n).Walk x y)
    (hx : x.1.1 0 ≠ -(n : Int)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (.inl x) (.inl y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x v y h p ih =>
      have hbase : x.1 = v.1 := by
        rcases h with ⟨u, i, _, h | h⟩
        · rw [h.1, h.2]
        · rw [h.2, h.1]
      have hv : v.1.1 0 ≠ -(n : Int) := by
        simpa only [hbase] using hx
      have hkeepX : ¬fkIsingSquareWiredLeftRingRemoved n x := by
        intro hremoved
        exact hx hremoved.1
      have hkeepV : ¬fkIsingSquareWiredLeftRingRemoved n v := by
        intro hremoved
        exact hv hremoved.1
      have hExpanded :
          (fkIsingSquareWiredExpandedGraph n hn omega).Adj (.inl x) (.inl v) := by
        exact Or.inr (Or.inl ⟨x, v, rfl, rfl, hkeepX, hkeepV, h⟩)
      exact hExpanded.reachable.trans (ih hv)




private theorem fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (p : (fkIsingSquareWiredSlotRingGraph n).Walk x y)
    (hp : p.IsPath) (hx : x.1.1 0 ≠ -(n : Int)) :
    ∃ q : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl x) (.inl y),
      q.IsPath ∧ q.length = p.length ∧
        q.support = p.support.map
          (fun z => (.inl z : FKIsingSquareWiredExpandedCarrier n)) ∧
        ∀ edge ∈ q.edges, ∃ u i,
          fkIsingSquareWiredSlotRingActive n (u, i) ∧
          edge = s((.inl (u, i) : FKIsingSquareWiredExpandedCarrier n),
            .inl (u, i + 1)) := by
  induction p with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil, by simp, by simp, by simp, by simp⟩
  | @cons x v y h p ih =>
      have hbase : x.1 = v.1 := by
        rcases h with ⟨u, i, _, h | h⟩
        · rw [h.1, h.2]
        · rw [h.2, h.1]
      have hv : v.1.1 0 ≠ -(n : Int) := by
        simpa only [hbase] using hx
      have hkeepX : ¬fkIsingSquareWiredLeftRingRemoved n x := by
        intro hremoved
        exact hx hremoved.1
      have hkeepV : ¬fkIsingSquareWiredLeftRingRemoved n v := by
        intro hremoved
        exact hv hremoved.1
      have hExpanded :
          (fkIsingSquareWiredExpandedGraph n hn omega).Adj (.inl x) (.inl v) :=
        Or.inr (Or.inl ⟨x, v, rfl, rfl, hkeepX, hkeepV, h⟩)
      obtain ⟨q, hq, hlen, hsupport, hedge⟩ := ih hp.of_cons hv
      let q' := SimpleGraph.Walk.cons hExpanded q
      refine ⟨q', ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change (Sum.inl x :: q.support).Nodup
        rw [List.nodup_cons]
        have hp' : x ∉ p.support ∧ p.support.Nodup := by
          simpa [SimpleGraph.Walk.isPath_def] using hp
        constructor
        · rw [hsupport]
          intro hxmem
          rw [List.mem_map] at hxmem
          obtain ⟨z, hz, hzx⟩ := hxmem
          have hzx' : z = x := Sum.inl.inj hzx
          subst z
          exact hp'.1 hz
        · rw [hsupport]
          exact hp'.2.map Sum.inl_injective
      · simp [q', hlen]
      · simp [q', hsupport]
      · intro edge hedgeMem
        simp only [q', SimpleGraph.Walk.edges_cons,
          List.mem_cons] at hedgeMem
        rcases hedgeMem with rfl | hedgeMem
        · rcases h with ⟨u, i, hi, h | h⟩
          · exact ⟨u, i, hi, by rw [h.1, h.2]⟩
          · exact ⟨u, i, hi, by rw [h.1, h.2, Sym2.eq_swap]⟩
        · exact hedge edge hedgeMem

theorem fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) := by
  obtain ⟨p⟩ := fkIsingSquareWiredSlotRingGraph_reachable_bondMate n hn d
  apply fkIsingSquareWiredExpandedGraph_reachable_of_ringWalk_not_left
    n hn omega p
  simpa [fkIsingSquareWiredDartSlot] using hleft



theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  obtain ⟨r, hr, hlen⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_bondMate n hn d
  obtain ⟨p, hp, hpLen, _, _⟩ :=
    fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
      n hn omega r hr (by
        simpa [fkIsingSquareWiredDartSlot] using hleft)
  exact ⟨p, hp, by simpa [hpLen] using hlen⟩



theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨r, hr, _⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_bondMate n hn d
  obtain ⟨p, hp, _, _, hedge⟩ :=
    fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
      n hn omega r hr (by
        simpa [fkIsingSquareWiredDartSlot] using hleft)
  refine ⟨p, hp, ?_⟩
  intro hmem
  obtain ⟨u, i, hi, hedgeEq⟩ := hedge _ hmem
  apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
  have hsym :
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (u, i) : FKIsingSquareWiredExpandedCarrier n),
        .inl (u, i + 1)) := hedgeEq
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hsym | hsym
  · have h1 := Sum.inl.inj hsym.1
    have h2 := Sum.inl.inj hsym.2
    rw [h1, h2]
  · have h1 := Sum.inl.inj hsym.1
    have h2 := Sum.inl.inj hsym.2
    rw [h1, h2]
    abel

theorem fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ a b : FKIsingSquareWiredSlotCarrier n,
      fkIsingSquareWiredDartSlot n d = a ∧
      fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) = b ∧
      ¬fkIsingSquareWiredLeftRingRemoved n a ∧
      ¬fkIsingSquareWiredLeftRingRemoved n b ∧
      (fkIsingSquareWiredSlotRingGraph n).Adj a b := by
  let u := fkIsingSquareDartEndpoint n d
  have hu0 : u.1 0 = -(n : Int) := hleft
  have hb0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have hb1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have havail := fkIsingSquareDartDirection_available n d
  cases hdir : fkIsingSquareDartDirection n d with
  | east =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · have hdslot : fkIsingSquareWiredDartSlot n d = (u, 1) := by
          simp [fkIsingSquareWiredDartSlot, u, hdir, hclockwise,
            fkIsingSquareWiredPortSlot]
        have hmateslot : fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d) = (u, 0) := by
          simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
            u, hdir, hclockwise, fkIsingSquarePreviousDirection, hs,
            fkIsingSquareWiredPortSlot]
        have hkeep0 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 0) := by
          simp [fkIsingSquareWiredLeftRingRemoved,
            fkIsingSquareDirectionAvailable] at hs ⊢
          omega
        have hkeep1 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 1) := by
          simp [fkIsingSquareWiredLeftRingRemoved]
        have hring : (fkIsingSquareWiredSlotRingGraph n).Adj (u, 0) (u, 1) :=
          fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
        exact ⟨(u, 1), (u, 0), hdslot, hmateslot,
          hkeep1, hkeep0, hring.symm⟩
      · have hu1 : u.1 1 = -(n : Int) := by
          simp [fkIsingSquareDirectionAvailable] at hs
          omega
        have hu : u = fkIsingSquareMarkedA n := by
          apply Subtype.ext
          funext i
          fin_cases i
          · simpa [fkIsingSquareMarkedA] using hu0
          · simpa [fkIsingSquareMarkedA] using hu1
        apply False.elim
        apply hboundary
        refine ⟨.bottom, ?_⟩
        rw [← fkIsingSquareDirectionDart_reconstruct n d]
        simp [fkIsingSquareWiredBoundaryEmbedding,
          fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]
  | north =>
      have he : fkIsingSquareDirectionAvailable n u .east := by
        simp [fkIsingSquareDirectionAvailable, hu0]
        omega
      have hdslot : fkIsingSquareWiredDartSlot n d = (u, 3) := by
        simp [fkIsingSquareWiredDartSlot, u, hdir, hclockwise,
          fkIsingSquareWiredPortSlot]
      have hmateslot : fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d) = (u, 2) := by
        simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          u, hdir, hclockwise, fkIsingSquarePreviousDirection, he,
          fkIsingSquareWiredPortSlot]
      have hnorth : u.1 1 < (n : Int) := by
        simpa [fkIsingSquareDirectionAvailable, u, hdir] using havail
      have hkeep2 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 2) := by
        simp [fkIsingSquareWiredLeftRingRemoved]
        omega
      have hkeep3 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 3) := by
        simp [fkIsingSquareWiredLeftRingRemoved]
        omega
      have hring : (fkIsingSquareWiredSlotRingGraph n).Adj (u, 2) (u, 3) :=
        fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
          (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      exact ⟨(u, 3), (u, 2), hdslot, hmateslot,
        hkeep3, hkeep2, hring.symm⟩
  | west =>
      exfalso
      simp [fkIsingSquareDirectionAvailable, u, hu0, hdir] at havail
  | south =>
      have hsouth : -(n : Int) < u.1 1 := by
        simpa [fkIsingSquareDirectionAvailable, u, hdir] using havail
      let kval : Int := u.1 1 + (n : Int) - 1
      have hk0 : 0 ≤ kval := by simp [kval]; omega
      have hklt : kval < 2 * (n : Int) := by simp [kval]; omega
      let k : Fin (2 * n) := ⟨kval.toNat, by
        have hcast : (kval.toNat : Int) < (2 * n : Nat) := by
          rw [Int.toNat_of_nonneg hk0]
          exact_mod_cast hklt
        exact_mod_cast hcast⟩
      have hkcast : (k.val : Int) = kval := by
        simp [k, Int.toNat_of_nonneg hk0]
      have hu : u = fkIsingSquareLeftVerticalUpper n hn k := by
        apply Subtype.ext
        funext i
        fin_cases i
        · simp [fkIsingSquareLeftVerticalUpper, hu0]
        · simp [fkIsingSquareLeftVerticalUpper, hkcast, kval]
          omega
      apply False.elim
      apply hboundary
      refine ⟨.north k, ?_⟩
      rw [← fkIsingSquareDirectionDart_reconstruct n d]
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]

theorem fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) := by
  obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
    fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
      n hn omega d hleft hclockwise hboundary
  subst a
  subst b
  exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hkeepA, hkeepB, hab⟩)

theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
    fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
      n hn omega d hleft hclockwise hboundary
  subst a
  subst b
  let hExpanded : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) :=
    Or.inr (Or.inl ⟨_, _, rfl, rfl, hkeepA, hkeepB, hab⟩)
  let p := SimpleGraph.Walk.cons hExpanded SimpleGraph.Walk.nil
  refine ⟨p, ?_, ?_⟩
  · simpa [p, SimpleGraph.Walk.isPath_def] using hExpanded.ne
  intro hmem
  have hedgeEq :
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))) := by
    simpa [p] using hmem
  rcases hab with ⟨u, i, hi, hab | hab⟩
  · apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hedgeEq
    simpa [hab.1, hab.2, fkIsingSquareWiredExpandedIntPosition] using hsum
  · apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hedgeEq
    simpa [hab.1, hab.2, fkIsingSquareWiredExpandedIntPosition,
      add_comm] using hsum

theorem fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) :=
  (fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
    n hn omega d hleft hclockwise hboundary).reachable

theorem fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  let emb := fkIsingSquareWiredBoundaryEmbedding n hn
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  have hSd : S.symm d = d := by
    have hforward : S d = d :=
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
    apply S.injective
    rw [S.apply_symm_apply, hforward]
  have hBd : fkIsingSquareBondMate n hn d ∉ Set.range emb := by
    intro hmem
    obtain ⟨i, hi⟩ := hmem
    have hback := congrArg (fkIsingSquareBondMate n hn) hi
    rw [fkIsingSquareBondMate_involutive] at hback
    apply hd
    cases i with
    | bottom =>
        refine ⟨.west ⟨0, by omega⟩, ?_⟩
        exact (fkIsingSquareBondMate_wired_bottom n hn).symm.trans hback
    | west k =>
        by_cases hk : k.val = 0
        · have hkfin : k = ⟨0, by omega⟩ := Fin.ext hk
          refine ⟨.bottom, ?_⟩
          rw [hkfin] at hback
          exact (fkIsingSquareBondMate_wired_west_zero n hn).symm.trans hback
        · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_west_succ n hn k hk).symm.trans hback
    | north k =>
        by_cases hk : k.val + 1 < 2 * n
        · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_north_not_last n hn k hk).symm.trans hback
        · refine ⟨.top, ?_⟩
          exact (fkIsingSquareBondMate_wired_north_last n hn k hk).symm.trans hback
    | top =>
        refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
        exact (fkIsingSquareBondMate_wired_top n hn).symm.trans hback
  have hSB : S (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [hSd]
  exact hSB



theorem fkIsingSquareWiredExpandedGraph_reachable_bulge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (k : Fin (2 * n)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (fkIsingSquareWiredExpandedStart n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) := by
  have h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
    Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
  have h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
  have h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedMiddle n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
  exact h0.reachable.trans (h1.reachable.trans h2.reachable)



theorem fkIsingSquareWiredExpandedGraph_exists_path_bulge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (k : Fin (2 * n)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (fkIsingSquareWiredExpandedStart n hn k)
        (fkIsingSquareWiredExpandedEnd n hn k),
      p.IsPath ∧ p.length = 3 ∧
        p.support = [fkIsingSquareWiredExpandedStart n hn k, .inr k,
          fkIsingSquareWiredExpandedMiddle n hn k,
          fkIsingSquareWiredExpandedEnd n hn k] ∧
        p.edges = [fkIsingSquareWiredExpandedBulgeEdge n hn k 0,
          fkIsingSquareWiredExpandedBulgeEdge n hn k 1,
          fkIsingSquareWiredExpandedBulgeEdge n hn k 2] := by
  let h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
    Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
  let h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
  let h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedMiddle n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
  let p := SimpleGraph.Walk.cons h0 (SimpleGraph.Walk.cons h1
    (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
  refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
  simp [p, SimpleGraph.Walk.isPath_def,
    fkIsingSquareWiredExpandedStart, fkIsingSquareWiredExpandedMiddle,
    fkIsingSquareWiredExpandedEnd]
  simp [p, fkIsingSquareWiredExpandedBulgeEdge,
    fkIsingSquareWiredExpandedBulgeEndpoints]



theorem fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (fkIsingSquareWiredExpandedStart n hn k)
        (fkIsingSquareWiredExpandedEnd n hn k),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨p, hp, _, _, hedges⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_path_bulge n hn omega k
  refine ⟨p, hp, ?_⟩
  intro hmem
  rw [hedges] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 0
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 1
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 2
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum

private theorem fkIsingSquareWired_position_sum_eq_of_edge_eq
    {V : Type*} (position : V → Int × Int) {x y z w : V}
    (h : s(x, y) = s(z, w)) :
    position x + position y = position z + position w := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    exact add_comm _ _

private theorem fkIsingSquareWiredSlotLocalGraph_edge_eq
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotLocalGraph n omega).Adj x y) :
    ∃ d, s(x, y) =
      s(fkIsingSquareWiredDartSlot n d,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)) := by
  rcases h with ⟨d, h | h⟩
  · exact ⟨d, by rw [h.1, h.2]⟩
  · refine ⟨d, ?_⟩
    rw [h.2, h.1]
    exact Sym2.eq_swap

private theorem fkIsingSquareWiredSlotRetainedRingGraph_edge_eq
    (n : Nat) {x y : FKIsingSquareWiredSlotCarrier n}
    (hx : ¬fkIsingSquareWiredLeftRingRemoved n x)
    (hy : ¬fkIsingSquareWiredLeftRingRemoved n y)
    (h : (fkIsingSquareWiredSlotRingGraph n).Adj x y) :
    ∃ u i, fkIsingSquareWiredSlotRingActive n (u, i) ∧
      ¬fkIsingSquareWiredLeftRingRemoved n (u, i) ∧
      s(x, y) = s((u, i), (u, i + 1)) := by
  rcases h with ⟨u, i, hactive, h | h⟩
  · exact ⟨u, i, hactive, h.1 ▸ hx, by rw [h.1, h.2]⟩
  · refine ⟨u, i, hactive, h.1 ▸ hy, ?_⟩
    rw [h.2, h.1]
    exact Sym2.eq_swap

private theorem fkIsingSquareWiredExpandedBulge_edge_eq
    (n : Nat) (hn : 0 < n)
    {x y : FKIsingSquareWiredExpandedCarrier n}
    (h : ∃ k : Fin (2 * n),
      s(x, y) = s(fkIsingSquareWiredExpandedStart n hn k, .inr k) ∨
      s(x, y) = s((.inr k : FKIsingSquareWiredExpandedCarrier n),
        fkIsingSquareWiredExpandedMiddle n hn k) ∨
      s(x, y) = s(fkIsingSquareWiredExpandedMiddle n hn k,
        fkIsingSquareWiredExpandedEnd n hn k)) :
    ∃ k j, s(x, y) = fkIsingSquareWiredExpandedBulgeEdge n hn k j := by
  rcases h with ⟨k, h | h | h⟩
  · exact ⟨k, 0, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩
  · exact ⟨k, 1, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩
  · exact ⟨k, 2, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩



theorem fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y z w : FKIsingSquareWiredExpandedCarrier n}
    (hxy : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y)
    (hzw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj z w)
    (hmid :
      fkIsingSquareWiredExpandedIntPosition n hn x +
          fkIsingSquareWiredExpandedIntPosition n hn y =
        fkIsingSquareWiredExpandedIntPosition n hn z +
          fkIsingSquareWiredExpandedIntPosition n hn w) :
    s(x, y) = s(z, w) := by
  change fkIsingSquareWiredExpandedAdj n hn omega x y at hxy
  change fkIsingSquareWiredExpandedAdj n hn omega z w at hzw
  rcases hxy with hxy | hxy | hxy
  · rcases hxy with ⟨a, b, rfl, rfl, hab⟩
    obtain ⟨d, hd⟩ :=
      fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hab
    have hd' :
        s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
          s(.inl (fkIsingSquareWiredDartSlot n d),
            .inl (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d))) := by
      simpa only [Sym2.map_mk] using congrArg
        (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
          (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨c, e, rfl, rfl, hce⟩
      obtain ⟨f, hf⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hce
      have hf' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (fkIsingSquareWiredDartSlot n f),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega f))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hf
      have hcanonical :
          fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n d) +
              fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d)) =
            fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n f) +
              fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega f)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn
                  (.inl (fkIsingSquareWiredDartSlot n d)) +
                fkIsingSquareWiredExpandedIntPosition n hn
                  (.inl (fkIsingSquareWiredDartSlot n
                    (FKIsingMedialDart.localMate omega d))) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hf')
      have hedge := fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq
        n omega d f hcanonical
      have hedge' :
          s((Sum.inl (fkIsingSquareWiredDartSlot n d) :
                FKIsingSquareWiredExpandedCarrier n),
              (Sum.inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d)) :
                  FKIsingSquareWiredExpandedCarrier n)) =
            s((Sum.inl (fkIsingSquareWiredDartSlot n f) :
                FKIsingSquareWiredExpandedCarrier n),
              (Sum.inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega f)) :
                  FKIsingSquareWiredExpandedCarrier n)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hedge
      exact hd'.trans (hedge'.trans hf'.symm)
    · rcases hzw with ⟨c, e, rfl, rfl, hc, he, hce⟩
      obtain ⟨u, i, hactive, hkeep, hr⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n hc he hce
      have hr' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (u, i), .inl (u, i + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
      apply False.elim
      apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega d u i hactive
      simpa [fkIsingSquareWiredExpandedIntPosition] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n d)) +
              fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d))) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hr')
    · obtain ⟨k, j, hb⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      apply False.elim
      apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne n hn omega d k j
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n d)) +
              fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d))) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hb)
  · rcases hxy with ⟨a, b, rfl, rfl, ha, hb, hab⟩
    obtain ⟨u, i, hactive, hkeep, hr⟩ :=
      fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n ha hb hab
    have hr' :
        s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
          s(.inl (u, i), .inl (u, i + 1)) := by
      simpa only [Sym2.map_mk] using congrArg
        (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
          (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨c, e, rfl, rfl, hce⟩
      obtain ⟨d, hd⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hce
      have hd' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (fkIsingSquareWiredDartSlot n d),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
      apply False.elim
      apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega d u i hactive
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hd')
    · rcases hzw with ⟨c, e, rfl, rfl, hc, he, hce⟩
      obtain ⟨v, j, hactive', hkeep', hs⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n hc he hce
      have hs' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (v, j), .inl (v, j + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hs
      have hcanonical :
          fkIsingSquareWiredSlotIntPosition n (u, i) +
              fkIsingSquareWiredSlotIntPosition n (u, i + 1) =
            fkIsingSquareWiredSlotIntPosition n (v, j) +
              fkIsingSquareWiredSlotIntPosition n (v, j + 1) := by
        simpa [fkIsingSquareWiredExpandedIntPosition] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hs')
      have hui : (u, i) = (v, j) :=
        fkIsingSquareWiredSlotRingMidpoint_injective n hcanonical
      cases hui
      exact hr'.trans hs'.symm
    · obtain ⟨k, j, hk⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      apply False.elim
      apply fkIsingSquareWiredSlotRingBulge_midpoint_ne n hn u i hkeep k j
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hk)
  · obtain ⟨k, i, hk⟩ :=
      fkIsingSquareWiredExpandedBulge_edge_eq n hn hxy
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨a, b, rfl, rfl, hab⟩
      obtain ⟨d, hd⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hab
      have hd' :
          s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
            s(.inl (fkIsingSquareWiredDartSlot n d),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
      apply False.elim
      apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne n hn omega d k i
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
              fkIsingSquareWiredExpandedIntPosition n hn x +
                fkIsingSquareWiredExpandedIntPosition n hn y := by
            simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
              fkIsingSquareWiredExpandedBulgeEdge] using
                (fkIsingSquareWired_position_sum_eq_of_edge_eq
                  (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hd')
    · rcases hzw with ⟨a, b, rfl, rfl, ha, hb, hab⟩
      obtain ⟨u, j, hactive, hkeep, hr⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n ha hb hab
      have hr' :
          s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
            s(.inl (u, j), .inl (u, j + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
      apply False.elim
      apply fkIsingSquareWiredSlotRingBulge_midpoint_ne n hn u j hkeep k i
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
              fkIsingSquareWiredExpandedIntPosition n hn x +
                fkIsingSquareWiredExpandedIntPosition n hn y := by
            simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
              fkIsingSquareWiredExpandedBulgeEdge] using
                (fkIsingSquareWired_position_sum_eq_of_edge_eq
                  (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hr')
    · obtain ⟨l, j, hl⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      have hcanonical :
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
            fkIsingSquareWiredExpandedBulgeMidpoint n hn l j := by
        simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
          fkIsingSquareWiredExpandedBulgeEdge] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedBulgeEndpoints n hn k i).1 +
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedBulgeEndpoints n hn k i).2 =
                fkIsingSquareWiredExpandedIntPosition n hn x +
                  fkIsingSquareWiredExpandedIntPosition n hn y :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hl)
      have hki : (k, i) = (l, j) :=
        fkIsingSquareWiredExpandedBulgeMidpoint_injective n hn hcanonical
      cases hki
      exact hk.trans hl.symm

noncomputable instance fkIsingSquareWiredExpandedGraph_decidableRel
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareWiredExpandedGraph n hn omega).Adj :=
  Classical.decRel _



noncomputable def fkIsingSquareWiredExpandedEmbedding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.KWStraightLineEmbedding
      (fkIsingSquareWiredExpandedGraph n hn omega) where
  vertex := fkIsingSquareWiredIntPoint ∘
    fkIsingSquareWiredExpandedIntPosition n hn
  vertex_injective := fkIsingSquareWiredIntPoint_injective.comp
    (fkIsingSquareWiredExpandedIntPosition_injective n hn)
  vertex_not_strictly_between := by
    intro dart v _ _
    obtain ⟨a, ha⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega dart.adj
    change ¬Sbtw Real
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn dart.fst))
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn v))
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn dart.snd))
    rw [ha]
    exact fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
      (fkIsingSquareWiredExpandedIntPosition n hn dart.fst)
      (fkIsingSquareWiredExpandedIntPosition n hn v) a
  edgeInteriors_disjoint := by
    intro dart next hedge
    apply Set.disjoint_left.2
    intro z hzd hzn
    apply hedge
    apply fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq
      n hn omega dart.adj next.adj
    obtain ⟨a, ha⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega dart.adj
    obtain ⟨b, hb⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega next.adj
    change
      fkIsingSquareWiredExpandedIntPosition n hn dart.fst +
          fkIsingSquareWiredExpandedIntPosition n hn dart.snd =
        fkIsingSquareWiredExpandedIntPosition n hn next.fst +
          fkIsingSquareWiredExpandedIntPosition n hn next.snd
    rw [ha, hb]
    exact fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
      (fkIsingSquareWiredExpandedIntPosition n hn dart.fst)
      (fkIsingSquareWiredExpandedIntPosition n hn next.fst)
      a b z (by simpa [ha] using hzd) (by simpa [hb] using hzn)



theorem fkIsingSquareWiredExpandedCyclePhaseSign
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.KWStraightLineCyclePhaseSign
      (fkIsingSquareWiredExpandedGraph n hn omega)
      (fkIsingSquareWiredExpandedEmbedding n hn omega) :=
  StatMech.FrontierA.kwStraightLineCyclePhaseSign_adaptive
    (fkIsingSquareWiredExpandedEmbedding n hn omega)



theorem fkIsingSquareWiredExpandedCycle_phase_eq_neg_one
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    StatMech.FrontierA.kwLoopPhaseProduct
        (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase
        (StatMech.FrontierA.kwGraphCycleDartLoop p) = -1 :=
  fkIsingSquareWiredExpandedCyclePhaseSign n hn omega p hp



theorem fkIsingSquareWiredExpandedCycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) (turn : Int)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      Complex.exp
          (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) =
        StatMech.FrontierA.kwLoopPhaseProduct
          (fkIsingSquareWiredExpandedEmbedding n hn omega).turnPhase
          (StatMech.FrontierA.kwGraphCycleDartLoop p)) :
    turn ≡ 8 [ZMOD 16] := by
  apply int_eighth_turn_mod_sixteen_of_exp_eq_neg_one
  rw [hphase]
  exact fkIsingSquareWiredExpandedCycle_phase_eq_neg_one n hn omega p hp




theorem fkIsingSquareWired_one_visit_west_carrierCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            (.dart (e, .east)) (.dart (e, .north)))
    (hr : r.IsPath) :
    ∃ p : (fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).Walk (.dart (e, .east)) (.dart (e, .east)),
      p.IsCycle ∧ p.support =
        (.dart (e, .east) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let removed : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
      s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}
  have hEN : H.Adj (.dart (e, .east)) (.dart (e, .north)) := by
    exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate])
  let q : H.Walk (.dart (e, .north)) (.dart (e, .east)) :=
    r.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
  let p : H.Walk (.dart (e, .east)) (.dart (e, .east)) :=
    SimpleGraph.Walk.cons hEN q
  refine ⟨p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · exact hr.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
    · intro hedge
      have hedge' : s((.dart (e, .east) : FKIsingSquareWiredCarrier n),
          .dart (e, .north)) ∈ r.reverse.edges := by
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
      have hdeleted := r.reverse.edges_subset_edgeSet hedge'
      rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
      exact hdeleted.2 (by simp [removed])
  · simp [p, q, SimpleGraph.Walk.support_mapLe_eq_support]




theorem fkIsingSquareWired_one_visit_east_carrierCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            (.dart (e, .west)) (.dart (e, .south)))
    (hr : r.IsPath) :
    ∃ p : (fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).Walk (.dart (e, .west)) (.dart (e, .west)),
      p.IsCycle ∧ p.support =
        (.dart (e, .west) : FKIsingSquareWiredCarrier n) :: r.reverse.support := by
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let removed : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
      s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}
  have hWS : H.Adj (.dart (e, .west)) (.dart (e, .south)) := by
    exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate])
  let q : H.Walk (.dart (e, .south)) (.dart (e, .west)) :=
    r.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
  let p : H.Walk (.dart (e, .west)) (.dart (e, .west)) :=
    SimpleGraph.Walk.cons hWS q
  refine ⟨p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · exact hr.reverse.mapLe (SimpleGraph.deleteEdges_le removed)
    · intro hedge
      have hedge' : s((.dart (e, .west) : FKIsingSquareWiredCarrier n),
          .dart (e, .south)) ∈ r.reverse.edges := by
        simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hedge
      have hdeleted := r.reverse.edges_subset_edgeSet hedge'
      rw [SimpleGraph.edgeSet_deleteEdges] at hdeleted
      exact hdeleted.2 (by simp [removed])
  · simp [p, q, SimpleGraph.Walk.support_mapLe_eq_support]



def fkIsingSquareWiredBlackOfDart (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  match d with
  | ⟨e, .west⟩ => ⟨.dart (e, .west), rfl⟩
  | ⟨e, .east⟩ => ⟨.dart (e, .east), rfl⟩
  | ⟨e, .south⟩ => ⟨.bond (e, .south), rfl⟩
  | ⟨e, .north⟩ => ⟨.bond (e, .north), rfl⟩



abbrev FKIsingSquareWiredPhysicalBlackCarrier (n : Nat) :=
  {x : FKIsingSquareWiredBlackCarrier n //
    x.1 ≠ (.terminal : FKIsingSquareWiredCarrier n)}

def fkIsingSquareWiredPhysicalBlackOfDart (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredPhysicalBlackCarrier n :=
  ⟨fkIsingSquareWiredBlackOfDart n d, by
    rcases d with ⟨e, side⟩
    cases side <;>
      simp [fkIsingSquareWiredBlackOfDart]⟩

theorem fkIsingSquareWiredPhysicalBlackOfDart_bijective (n : Nat) :
    Function.Bijective (fkIsingSquareWiredPhysicalBlackOfDart n) := by
  constructor
  · intro d f h
    rcases d with ⟨e, side⟩
    rcases f with ⟨f, side'⟩
    have hval := congrArg (fun x : FKIsingSquareWiredPhysicalBlackCarrier n =>
      x.1.1) h
    cases side <;> cases side' <;>
      simpa [fkIsingSquareWiredPhysicalBlackOfDart,
        fkIsingSquareWiredBlackOfDart] using hval
  · rintro ⟨⟨x, hblack⟩, hterminal⟩
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierColor] at hblack
    | terminal =>
        exact False.elim (hterminal rfl)
    | dart d =>
        rcases d with ⟨e, side⟩
        cases side with
        | west =>
            refine ⟨(e, .west), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | east =>
            refine ⟨(e, .east), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | south =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredDartSideColor] at hblack
        | north =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredDartSideColor] at hblack
    | bond d =>
        rcases d with ⟨e, side⟩
        cases side with
        | west =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner] at hblack
        | east =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner] at hblack
        | south =>
            refine ⟨(e, .south), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | north =>
            refine ⟨(e, .north), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl

theorem fkIsingSquareWiredBlackOfDart_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredBlackOfDart n) := by
  intro d f h
  apply (fkIsingSquareWiredPhysicalBlackOfDart_bijective n).1
  apply Subtype.ext
  exact h


noncomputable def fkIsingSquareWiredDartPhysicalBlackEquiv (n : Nat) :
    FKIsingMedialDart (fkSquareBoxPlanar n) ≃
      FKIsingSquareWiredPhysicalBlackCarrier n :=
  Equiv.ofBijective (fkIsingSquareWiredPhysicalBlackOfDart n)
    (fkIsingSquareWiredPhysicalBlackOfDart_bijective n)


noncomputable def fkIsingSquareWiredPhysicalBlackPortIntPosition (n : Nat) :
    FKIsingSquareWiredPhysicalBlackCarrier n → Int × Int :=
  fkIsingSquareWiredPortIntPosition n ∘
    (fkIsingSquareWiredDartPhysicalBlackEquiv n).symm

theorem fkIsingSquareWiredPhysicalBlackPortIntPosition_injective (n : Nat) :
    Function.Injective
      (fkIsingSquareWiredPhysicalBlackPortIntPosition n) :=
  (fkIsingSquareWiredPortIntPosition_injective n).comp
    (fkIsingSquareWiredDartPhysicalBlackEquiv n).symm.injective



def fkIsingSquareWiredPortNext
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  match d with
  | ⟨e, .west⟩ => FKIsingMedialDart.localMate omega (e, .west)
  | ⟨e, .east⟩ => FKIsingMedialDart.localMate omega (e, .east)
  | ⟨e, .south⟩ => fkIsingSquareWiredBondMate n hn (e, .south)
  | ⟨e, .north⟩ => fkIsingSquareWiredBondMate n hn (e, .north)

theorem fkIsingSquareWiredPortNext_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortNext n hn omega d ≠ d := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      exact FKIsingMedialDart.localMate_ne omega (e, .west)
  | east =>
      exact FKIsingMedialDart.localMate_ne omega (e, .east)
  | south =>
      exact fkIsingSquareWiredBondMate_ne n hn (e, .south)
  | north =>
      exact fkIsingSquareWiredBondMate_ne n hn (e, .north)


def fkIsingSquareWiredUnitDiagonalTangentCode : Fin 4 → Int :=
  ![5, 3, 7, 1]

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_zero :
    fkIsingSquareWiredUnitDiagonalTangentCode 0 = 5 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_one :
    fkIsingSquareWiredUnitDiagonalTangentCode 1 = 3 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_two :
    fkIsingSquareWiredUnitDiagonalTangentCode 2 = 7 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalTangentCode_three :
    fkIsingSquareWiredUnitDiagonalTangentCode 3 = 1 := rfl


def fkIsingSquareWiredUnitDiagonalAxis : Fin 4 → Fin 4 :=
  ![2, 1, 3, 0]

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_zero :
    fkIsingSquareWiredUnitDiagonalAxis 0 = 2 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_one :
    fkIsingSquareWiredUnitDiagonalAxis 1 = 1 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_two :
    fkIsingSquareWiredUnitDiagonalAxis 2 = 3 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_three :
    fkIsingSquareWiredUnitDiagonalAxis 3 = 0 := rfl

theorem fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis
    (a : Fin 4) :
    fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a) =
      (1 + Complex.I) *
        StatMech.FrontierA.kwRectilinearVector
          (fkIsingSquareWiredUnitDiagonalAxis a) := by
  fin_cases a <;> apply Complex.ext <;>
    norm_num [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      fkIsingSquareWiredUnitDiagonalAxis,
      StatMech.FrontierA.kwRectilinearVector,
      StatMech.Onsager.BaseCase.stepOf]

private theorem fkIsingSquareWired_kwVectorTurnPhase_common_mul
    (z x y : Complex) (hz : z ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    StatMech.FrontierA.kwVectorTurnPhase (z * x) (z * y) =
      StatMech.FrontierA.kwVectorTurnPhase x y := by
  have hang :
      ((Complex.arg (z * y) : Real.Angle) -
          (Complex.arg (z * x) : Real.Angle)) =
        (Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hz hx,
      Complex.arg_mul_coe_angle hz hy]
    abel
  unfold StatMech.FrontierA.kwVectorTurnPhase
    StatMech.FrontierA.kwAngleTurnPhase
  rw [hang]


theorem fkIsingSquareWiredUnitDiagonal_turnPhase
    (a b : Fin 4)
    (hnu : fkIsingSquareWiredUnitDiagonalAxis b ≠
      fkIsingSquareWiredUnitDiagonalAxis a + 2) :
    StatMech.FrontierA.kwVectorTurnPhase
        (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a))
        (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep b)) =
      Complex.exp
        (((((fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode a)
          (fkIsingSquareWiredUnitDiagonalTangentCode b) : Int) : Real) *
            (Real.pi / 8) : Real) : Complex) * Complex.I) := by
  have hfac : (1 + Complex.I : Complex) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  rw [fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis,
    fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis]
  rw [fkIsingSquareWired_kwVectorTurnPhase_common_mul _ _ _ hfac
    (StatMech.FrontierA.kwRectilinearVector_ne_zero _)
    (StatMech.FrontierA.kwRectilinearVector_ne_zero _)]
  rw [StatMech.FrontierA.kwVectorTurnPhase_rectilinear _ _ hnu]
  fin_cases a <;> fin_cases b <;>
    norm_num [fkIsingSquareWiredUnitDiagonalAxis] at hnu
  all_goals simp [Fin.add_def, Fin.ext_iff] at hnu ⊢
  all_goals simp [
      fkIsingSquareSignedEighthTurn,
      StatMech.Onsager.ons_turnW,
      StatMech.Onsager.ons_turnRoot,
      Complex.exp_neg, div_eq_mul_inv, Fin.add_def,
      Fin.ext_iff] at hnu ⊢
  all_goals congr 1 <;> ring


noncomputable def fkIsingSquareWiredExpandedDartStepIndex
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart) : Fin 4 :=
  Classical.choose (fkIsingSquareWiredExpandedGraph_step n hn omega d.adj)

theorem fkIsingSquareWiredExpandedDartStepIndex_spec
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart) :
    fkIsingSquareWiredExpandedIntPosition n hn d.snd =
      fkIsingSquareWiredExpandedIntPosition n hn d.fst +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega d) :=
  Classical.choose_spec
    (fkIsingSquareWiredExpandedGraph_step n hn omega d.adj)

theorem fkIsingSquareWiredExpandedDart_vector_eq_step
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : (fkIsingSquareWiredExpandedGraph n hn omega).Dart) :
    (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.snd -
        (fkIsingSquareWiredExpandedEmbedding n hn omega).vertex d.fst =
      fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega d)) := by
  change fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn d.snd) -
      fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn d.fst) = _
  rw [fkIsingSquareWiredExpandedDartStepIndex_spec]
  simp [fkIsingSquareWiredExpandedEmbedding,
    fkIsingSquareWiredIntPoint, Function.comp_apply]
  ring

theorem fkIsingSquareWiredUnitDiagonalAxis_opposite_step
    (a b : Fin 4)
    (h : fkIsingSquareWiredUnitDiagonalAxis b =
      fkIsingSquareWiredUnitDiagonalAxis a + 2) :
    fkIsingSquareWiredUnitDiagonalStep b =
      -fkIsingSquareWiredUnitDiagonalStep a := by
  fin_cases a <;> fin_cases b <;>
    simp_all [fkIsingSquareWiredUnitDiagonalAxis,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def,
      Fin.ext_iff, Prod.ext_iff]



theorem fkIsingSquareWiredExpandedCycle_step_not_opposite
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∀ k : Fin p.darts.length,
      fkIsingSquareWiredUnitDiagonalAxis
          (fkIsingSquareWiredExpandedDartStepIndex n hn omega
            (StatMech.FrontierA.kwGraphCycleDartLoop p (k + 1))) ≠
        fkIsingSquareWiredUnitDiagonalAxis
            (fkIsingSquareWiredExpandedDartStepIndex n hn omega
              (StatMech.FrontierA.kwGraphCycleDartLoop p k)) + 2 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k hopposite
  let d := StatMech.FrontierA.kwGraphCycleDartLoop p k
  let e := StatMech.FrontierA.kwGraphCycleDartLoop p (k + 1)
  have hadj := StatMech.FrontierA.kwGraphCycleDartLoop_valid p hp k
  have hstepD := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega d
  have hstepE := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega e
  have hopen := fkIsingSquareWiredUnitDiagonalAxis_opposite_step
    (fkIsingSquareWiredExpandedDartStepIndex n hn omega d)
    (fkIsingSquareWiredExpandedDartStepIndex n hn omega e) hopposite
  have hend : e.snd = d.fst := by
    apply (fkIsingSquareWiredExpandedIntPosition_injective n hn)
    rw [hstepE, ← hadj, hstepD, hopen]
    simp
  have hedge : e.edge = d.edge := by
    apply Sym2.eq_iff.mpr
    exact Or.inr ⟨hadj.symm, hend⟩
  exact (StatMech.FrontierA.kwGraphCycleDartLoop_nonbacktracking
    (fkIsingSquareWiredExpandedGraph n hn omega) p hp k).2 hedge.symm



theorem fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {root : FKIsingSquareWiredExpandedCarrier n}
    (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root)
    (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
    let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
    (∑ k : Fin p.darts.length,
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop k)))
        (fkIsingSquareWiredUnitDiagonalTangentCode
          (direction (loop (k + 1))))) ≡ 8 [ZMOD 16] := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  dsimp only
  let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
  let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
  let turn : Fin p.darts.length → Int := fun k =>
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop k)))
      (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop (k + 1))))
  apply fkIsingSquareWiredExpandedCycle_turn_mod_sixteen
    n hn omega p hp (∑ k, turn k)
  have hexponent :
      ((((((∑ k, turn k) : Int) : Real) * (Real.pi / 8) : Real) : Complex) *
          Complex.I) =
        ∑ k, (((((turn k : Int) : Real) * (Real.pi / 8) : Real) : Complex) *
          Complex.I) := by
    push_cast
    simpa [mul_assoc] using
      (Finset.sum_mul Finset.univ
        (fun k => ((turn k : Int) : Complex))
        ((((Real.pi / 8 : Real) : Complex)) * Complex.I))
  rw [hexponent, Complex.exp_sum]
  unfold StatMech.FrontierA.kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  rw [← (fkIsingSquareWiredExpandedEmbedding n hn omega).vectorTurnPhase_eq_turnPhase]
  rw [fkIsingSquareWiredExpandedDart_vector_eq_step,
    fkIsingSquareWiredExpandedDart_vector_eq_step]
  exact (fkIsingSquareWiredUnitDiagonal_turnPhase _ _
    (fkIsingSquareWiredExpandedCycle_step_not_opposite n hn omega p hp k)).symm


def fkIsingSquareWiredLocalStepIndex
    {n : Nat} (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Fin 4 :=
  match omega d.1.1, d.2 with
  | false, .west => 2
  | false, .south => 1
  | false, .east => 1
  | false, .north => 2
  | true, .west => 3
  | true, .south => 3
  | true, .east => 0
  | true, .north => 0

theorem fkIsingSquareWiredPortIntPosition_localMate_exact_step
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortIntPosition n
        (FKIsingMedialDart.localMate omega d) =
      fkIsingSquareWiredPortIntPosition n d +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredLocalStepIndex omega d) := by
  rcases d with ⟨e, side⟩
  cases homega : omega e.1 <;> cases side
  all_goals simp only [FKIsingMedialDart.localMate, homega]
  all_goals
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
      simp [fkIsingSquareWiredLocalStepIndex,
        fkIsingSquareWiredPortIntPosition, homega, haxis,
        fkIsingSquareWiredUnitDiagonalStep, Prod.ext_iff] <;> omega

def fkIsingSquareWiredMacroIncomingCode
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  fkIsingSquareWiredDirectedTangentCode n hn
    (fkIsingSquareWiredBlackOfDart n d).1 + 2
































































def fkIsingSquareWiredRingStepIndex : Fin 8 → Fin 4 :=
  ![3, 1, 1, 1, 0, 2, 2, 2]

@[simp] theorem fkIsingSquareWiredRingStepIndex_zero :
    fkIsingSquareWiredRingStepIndex 0 = 3 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_one :
    fkIsingSquareWiredRingStepIndex 1 = 1 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_two :
    fkIsingSquareWiredRingStepIndex 2 = 1 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_three :
    fkIsingSquareWiredRingStepIndex 3 = 1 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_four :
    fkIsingSquareWiredRingStepIndex 4 = 0 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_five :
    fkIsingSquareWiredRingStepIndex 5 = 2 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_six :
    fkIsingSquareWiredRingStepIndex 6 = 2 := rfl
@[simp] theorem fkIsingSquareWiredRingStepIndex_seven :
    fkIsingSquareWiredRingStepIndex 7 = 2 := rfl

def fkIsingSquareWiredBondArcBase
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then d
  else fkIsingSquareBondMate n hn d

def fkIsingSquareWiredForwardRingStepWord
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : List (Fin 4) :=
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  List.ofFn fun j : Fin L.val =>
    fkIsingSquareWiredRingStepIndex
      (start + ⟨j.val, lt_trans j.isLt L.isLt⟩)

def fkIsingSquareWiredOrdinaryBondStepWord
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : List (Fin 4) :=
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
    List.ofFn fun j : Fin L.val =>
      fkIsingSquareWiredRingStepIndex
        (start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
  else
    List.ofFn fun j : Fin L.val =>
      fkIsingSquareWiredUnitDiagonalReverse
        (fkIsingSquareWiredRingStepIndex
          (start + ⟨L.val - 1 - j.val, by omega⟩))

theorem fkIsingSquareWiredForwardRingStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredForwardRingStepWord n hn d ≠ [] := by
  have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n
    (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d))
    (fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d))
  intro hnil
  have hlen := congrArg List.length hnil
  simp [fkIsingSquareWiredForwardRingStepWord] at hlen
  rcases hcases with h | h | h <;> simp [h] at hlen

theorem fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredOrdinaryBondStepWord n hn d ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
    List.length_ofFn] at hlen
  split at hlen <;>
    have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n
      (fkIsingSquareDartEndpoint n (fkIsingSquareWiredBondArcBase n hn d))
      (fkIsingSquareDartDirection n (fkIsingSquareWiredBondArcBase n hn d)) <;>
    rcases hcases with h | h | h <;> simp [h] at hlen



def fkIsingSquareWiredBulgeReverseStepWord : List (Fin 4) := [1, 0, 2]

noncomputable def fkIsingSquareWiredPortMacroStepWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : List (Fin 4) :=
  match d.2 with
  | .west | .east => [fkIsingSquareWiredLocalStepIndex omega d]
  | .south => fkIsingSquareWiredOrdinaryBondStepWord n hn d
  | .north =>
      if d ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) then
        fkIsingSquareWiredBulgeReverseStepWord
      else fkIsingSquareWiredOrdinaryBondStepWord n hn d

private theorem fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .south) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .south) = fkIsingSquareWiredSourceDart n hn := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom => simpa [fkIsingSquareWiredSourceDart] using hi.symm
  | west k | north k | top =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs

private theorem fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .north) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .north) = fkIsingSquareWiredTerminalDart n hn ∨
      ∃ k : Fin (2 * n),
        (e, .north) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k => exact Or.inr ⟨k, hi.symm⟩
  | top => exact Or.inl (by
      simpa [fkIsingSquareWiredTerminalDart] using hi.symm)

theorem fkIsingSquareWiredPortMacroStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPortMacroStepWord n hn omega d ≠ [] := by
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp [fkIsingSquareWiredPortMacroStepWord]
  | east => simp [fkIsingSquareWiredPortMacroStepWord]
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early n hn e h)
      have hword := fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
        n hn (e, .south)
      simpa [fkIsingSquareWiredPortMacroStepWord] using hword
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have he := congrArg Prod.fst hk
          simp only at he
          subst e
          have hrange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hrange
          simp [fkIsingSquareWiredPortMacroStepWord,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide, hrange,
            fkIsingSquareWiredBulgeReverseStepWord]
      ·
        have hword := fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
          n hn (e, .north)
        simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using hword

def fkIsingSquareWiredPortMacroCodeWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : List Int :=
  (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
    fkIsingSquareWiredUnitDiagonalTangentCode

theorem fkIsingSquareSignedEighthTurn_congr
    {a b c d : Int} (ha : a ≡ b [ZMOD 8]) (hc : c ≡ d [ZMOD 8]) :
    fkIsingSquareSignedEighthTurn a c =
      fkIsingSquareSignedEighthTurn b d := by
  have h := (hc.sub ha).add (Int.ModEq.refl 4)
  unfold Int.ModEq at h
  unfold fkIsingSquareSignedEighthTurn
  rw [h]

private theorem carrierAdjacentSum_flatMap
    {A B : Type*} (turn : B → B → Int)
    (code : A → List B) (hcode : ∀ a, code a ≠ []) (l : List A) :
    carrierAdjacentSum turn (l.flatMap code) =
      carrierAdjacentSum
          (fun a b => turn ((code a).getLast (hcode a))
            ((code b).head (hcode b))) l +
        (l.map fun a => carrierAdjacentSum turn (code a)).sum := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          have hrest : (code b ++ tail.flatMap code) ≠ [] := by
            exact List.append_ne_nil_of_left_ne_nil (hcode b) _
          change carrierAdjacentSum turn
              (code a ++ (code b ++ tail.flatMap code)) = _
          rw [carrierAdjacentSum_append turn (code a)
            (code b ++ tail.flatMap code) (hcode a) hrest]
          have ih' :
              carrierAdjacentSum turn (code b ++ tail.flatMap code) =
                carrierAdjacentSum
                    (fun a b => turn ((code a).getLast (hcode a))
                      ((code b).head (hcode b))) (b :: tail) +
                  ((b :: tail).map fun a =>
                    carrierAdjacentSum turn (code a)).sum := by
            simpa only [List.flatMap_cons] using ih
          rw [ih']
          simp only [List.map_cons, List.sum_cons,
            carrierAdjacentSum_cons_cons]
          have hhead : (code b ++ tail.flatMap code).head hrest =
              (code b).head (hcode b) := by
            simp [List.head_append, hcode b]
          rw [hhead]
          omega

private theorem carrierAdjacentSum_chain_congr
    {A : Type*} (left right : A → A → Int) (l : List A)
    (hchain : l.Chain' fun a b => left a b = right a b) :
    carrierAdjacentSum left l = carrierAdjacentSum right l := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons, carrierAdjacentSum_cons_cons]
          rw [hchain.rel]
          rw [ih hchain.tail]

private theorem carrierAdjacentSum_snd_add_head_eq_sum
    {A : Type*} (value : A → Int) (l : List A) (hl : l ≠ []) :
    carrierAdjacentSum (fun _ b => value b) l + value (l.head hl) =
      (l.map value).sum := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons]
          simp only [List.head_cons, List.map_cons, List.sum_cons]
          have hne : b :: tail ≠ [] := by simp
          have hi := ih hne
          simp only [List.head_cons, List.map_cons, List.sum_cons] at hi
          omega

private theorem carrierAdjacentSum_fst_add_last_eq_sum
    {A : Type*} (value : A → Int) (l : List A) (hl : l ≠ []) :
    carrierAdjacentSum (fun a _ => value a) l + value (l.getLast hl) =
      (l.map value).sum := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons]
          have hne : b :: tail ≠ [] := by simp
          rw [List.getLast_cons hne]
          simp only [List.map_cons, List.sum_cons]
          have hi := ih hne
          simp only [List.map_cons, List.sum_cons] at hi
          omega

private theorem List.sum_map_modEq
    {A : Type*} {f g : A → Int} (l : List A) (m : Int)
    (h : ∀ a ∈ l, f a ≡ g a [ZMOD m]) :
    (l.map f).sum ≡ (l.map g).sum [ZMOD m] := by
  induction l with
  | nil => exact Int.ModEq.refl 0
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (h a (by simp)).add (ih (fun b hb => h b (by simp [hb])))

private theorem List.sum_map_add_sub
    {A : Type*} (l : List A) (f g h : A → Int) :
    (l.map fun a => f a + g a - h a).sum =
      (l.map f).sum + (l.map g).sum - (l.map h).sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem List.chain'_iterate
    {A : Type*} (f : A → A) (d : A) (k : Nat) :
    (List.iterate f d k).Chain' fun q r => r = f q := by
  induction k generalizing d with
  | zero => exact List.IsChain.nil
  | succ k ih =>
      cases k with
      | zero => exact List.IsChain.singleton d
      | succ k => exact List.IsChain.cons_cons rfl (ih (f d))

def fkIsingSquareWiredRingArcContains
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) (i : Fin 8) : Prop :=
  ∃ j : Fin (fkIsingSquareWiredBondArcLength n u d).val,
    i = fkIsingSquareWiredPortSlot d .counterclockwise +
      ⟨j.val, lt_trans j.isLt
        (fkIsingSquareWiredBondArcLength n u d).isLt⟩



def fkIsingSquareWiredForwardRingSlotWord
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    List (FKIsingSquareWiredSlotCarrier n) :=
  let L := fkIsingSquareWiredBondArcLength n u d
  let start := fkIsingSquareWiredPortSlot d .counterclockwise
  List.ofFn fun j : Fin (L.val + 1) =>
    (u, start + ⟨j.val, by omega⟩)

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_length
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).length =
      (fkIsingSquareWiredBondArcLength n u d).val + 1 := by
  simp [fkIsingSquareWiredForwardRingSlotWord]

theorem fkIsingSquareWiredRingArcContains_active
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    {i : Fin 8}
    (hi : fkIsingSquareWiredRingArcContains n u d i) :
    fkIsingSquareWiredSlotRingActive n (u, i) := by
  classical
  rcases hi with ⟨j, rfl⟩
  have hj := j.isLt
  have hj5 : j.val < 5 := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
        hL | hL | hL <;>
      have hLv := congrArg Fin.val hL <;>
      norm_num at hLv <;>
      omega
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨
      j.val = 3 ∨ j.val = 4 := by omega
  rcases hjcases with hjv | hjv | hjv | hjv | hjv
  all_goals
    cases d <;>
      by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
      simp [fkIsingSquareWiredSlotRingActive,
        fkIsingSquareWiredSlotAvailable,
        fkIsingSquareWiredPortSlotTurn,
        fkIsingSquareWiredPortSlotDirection,
        fkIsingSquareWiredPortSlot,
        fkIsingSquareWiredBondArcLength,
        he, hnorth, hw, hs, hjv] at hd hj ⊢ <;>
      omega

theorem fkIsingSquareWiredForwardRingSlotWord_isChain
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    List.IsChain (fkIsingSquareWiredSlotRingGraph n).Adj
      (fkIsingSquareWiredForwardRingSlotWord n u d) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hi
  simp only [fkIsingSquareWiredForwardRingSlotWord,
    List.getElem_ofFn]
  have hstep :
      (fkIsingSquareWiredPortSlot d .counterclockwise +
          (⟨i, by omega⟩ : Fin 8)) + 1 =
        fkIsingSquareWiredPortSlot d .counterclockwise +
          (⟨i + 1, by omega⟩ : Fin 8) := by
    rw [add_assoc]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  rw [← hstep]
  apply fkIsingSquareWiredSlotRingGraph_adj_succ
  apply fkIsingSquareWiredRingArcContains_active n u d hd
  exact ⟨⟨i, by omega⟩, rfl⟩

theorem fkIsingSquareWiredForwardRingSlotWord_nodup
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hi8 : i.val < 8 := by
    have hi := i.isLt
    have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
    simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hi
    omega
  have hj8 : j.val < 8 := by
    have hj := j.isLt
    have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
    simp only [fkIsingSquareWiredForwardRingSlotWord_length] at hj
    omega
  have hslot := congrArg Fin.val (congrArg Prod.snd hij)
  simp only [fkIsingSquareWiredForwardRingSlotWord,
    List.getElem_ofFn] at hslot
  have hoff : (⟨i.val, hi8⟩ : Fin 8) = ⟨j.val, hj8⟩ := by
    apply add_left_cancel
    apply Fin.ext
    exact hslot
  have hv : i.val = j.val := congrArg (@Fin.val 8) hoff
  exact Fin.ext hv

theorem fkIsingSquareWiredForwardRingSlotWord_ne_nil
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    fkIsingSquareWiredForwardRingSlotWord n u d ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen

theorem fkIsingSquareWiredSlotIntPosition_succ_step
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8) :
    fkIsingSquareWiredSlotIntPosition n (u, i + 1) =
      fkIsingSquareWiredSlotIntPosition n (u, i) +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredRingStepIndex i) := by
  fin_cases i <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def, Prod.ext_iff] <;>
    omega

theorem fkIsingSquareWiredSlotIntPosition_pred_reverse_step
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8) :
    fkIsingSquareWiredSlotIntPosition n (u, i) =
      fkIsingSquareWiredSlotIntPosition n (u, i + 1) +
        fkIsingSquareWiredUnitDiagonalStep
          (fkIsingSquareWiredUnitDiagonalReverse
            (fkIsingSquareWiredRingStepIndex i)) := by
  fin_cases i <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredUnitDiagonalStep, Fin.add_def, Prod.ext_iff] <;>
    omega


theorem fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (u, fkIsingSquareWiredPortSlot d .counterclockwise)
        (u, fkIsingSquareWiredPortSlot
          (fkIsingSquareNextDirection n u d) .clockwise),
      p.IsPath ∧
        p.support = fkIsingSquareWiredForwardRingSlotWord n u d := by
  let word := fkIsingSquareWiredForwardRingSlotWord n u d
  have hne : word ≠ [] :=
    fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d
  have hchain : List.IsChain (fkIsingSquareWiredSlotRingGraph n).Adj word :=
    fkIsingSquareWiredForwardRingSlotWord_isChain n u d hd
  let p := SimpleGraph.Walk.ofSupport word hne hchain
  have hsupport : p.support = word :=
    SimpleGraph.Walk.support_ofSupport hne hchain
  have hhead : word.head hne =
      (u, fkIsingSquareWiredPortSlot d .counterclockwise) := by
    simp [word, fkIsingSquareWiredForwardRingSlotWord]
  have hlast : word.getLast hne =
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
    have hslot := fkIsingSquareWiredPortSlot_nextDirection n u d
    simp only [word, fkIsingSquareWiredForwardRingSlotWord]
    rw [List.getLast_ofFn_succ]
    exact congrArg (fun slot => (u, slot)) hslot.symm
  let q := p.copy hhead hlast
  refine ⟨q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simpa [q, hsupport] using
      fkIsingSquareWiredForwardRingSlotWord_nodup n u d
  · simpa [q, hsupport, word]



def fkIsingSquareWiredOrdinaryBondSlotVertexWord
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    List (FKIsingSquareWiredSlotCarrier n) :=
  let base := fkIsingSquareWiredBondArcBase n hn d
  let L := fkIsingSquareWiredBondArcLength n
    (fkIsingSquareDartEndpoint n base)
    (fkIsingSquareDartDirection n base)
  let start := (fkIsingSquareWiredDartSlot n base).2
  if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
    List.ofFn fun j : Fin L.val =>
      (fkIsingSquareDartEndpoint n base,
        start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
  else
    List.ofFn fun j : Fin L.val =>
      (fkIsingSquareDartEndpoint n base,
        start + ⟨L.val - j.val, by omega⟩)

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_length
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length =
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d).length := by
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredOrdinaryBondStepWord, hturn]
  · simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredOrdinaryBondStepWord, hturn]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [fkIsingSquareWiredOrdinaryBondSlotVertexWord_length] at hlen
  apply fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn d
  exact List.eq_nil_of_length_eq_zero (by simpa using hlen)

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).Nodup := by
  unfold fkIsingSquareWiredOrdinaryBondSlotVertexWord
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [if_pos hturn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hoff := add_left_cancel (Prod.mk.inj hij).2
    exact Fin.ext (congrArg (@Fin.val 8) hoff)
  · rw [if_neg hturn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hoff := add_left_cancel (Prod.mk.inj hij).2
    have hv := congrArg (@Fin.val 8) hoff
    apply Fin.ext
    simp only at hv
    omega

private theorem List.head_dropLast_eq_head_of_one_lt_length
    {A : Type*} (l : List A) (h : 1 < l.length) :
    (l.dropLast).head (by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega) =
      l.head (by
        intro hnil
        subst l
        simp at h) := by
  cases l with
  | nil => simp at h
  | cons a tail =>
      cases tail with
      | nil => simp at h
      | cons b rest => simp

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_dropLast_head
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).dropLast.head (by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      have hcases :=
        fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d
      rcases hcases with h | h | h <;> simp [h] at hlen) =
      (u, fkIsingSquareWiredPortSlot d .counterclockwise) := by
  have hpos : 0 < (fkIsingSquareWiredBondArcLength n u d).val := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
      h | h | h <;>
      have hv := congrArg Fin.val h <;>
      norm_num at hv <;>
      omega
  have hlen : 1 < (fkIsingSquareWiredForwardRingSlotWord n u d).length := by
    simp only [fkIsingSquareWiredForwardRingSlotWord_length]
    omega
  rw [List.head_dropLast_eq_head_of_one_lt_length _ hlen]
  simp [fkIsingSquareWiredForwardRingSlotWord]

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_getLast
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).getLast
        (fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d) =
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
  have hslot := fkIsingSquareWiredPortSlot_nextDirection n u d
  simp only [fkIsingSquareWiredForwardRingSlotWord]
  rw [List.getLast_ofFn_succ]
  exact congrArg (fun slot => (u, slot)) hslot.symm

theorem fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise) :
    (fkIsingSquareWiredForwardRingSlotWord n
        (fkIsingSquareDartEndpoint n d)
        (fkIsingSquareDartDirection n d)).getLast
        (fkIsingSquareWiredForwardRingSlotWord_ne_nil n
          (fkIsingSquareDartEndpoint n d)
          (fkIsingSquareDartDirection n d)) =
      fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) := by
  rw [fkIsingSquareWiredForwardRingSlotWord_getLast]
  simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hturn]

set_option maxHeartbeats 4000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_head
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).head
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil n hn d) =
      fkIsingSquareWiredDartSlot n d := by
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredBondArcBase, hturn, if_pos]
    rw [List.head_ofFn]
    simp [fkIsingSquareWiredDartSlot]
  · let base := fkIsingSquareWiredBondArcBase n hn d
    have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      cases hx : (fkIsingSquareSideCorner d.2).2 <;> simp_all
    have hbaseccw :
        (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases hx : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
    have hend := fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate
      n hn base hbaseccw
    have hbaseMate : fkIsingSquareBondMate n hn base = d := by
      simpa [base, fkIsingSquareWiredBondArcBase, hturn] using
        fkIsingSquareBondMate_involutive n hn d
    rw [hbaseMate] at hend
    simp only [fkIsingSquareWiredForwardRingSlotWord] at hend
    rw [List.getLast_ofFn_succ] at hend
    simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      hturn, if_false]
    rw [List.head_ofFn]
    simpa [base, fkIsingSquareWiredDartSlot, hbaseccw] using hend

set_option maxHeartbeats 8000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_step
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (i : Nat)
    (hi : i < (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length) :
    let word := fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d
    let next := if h : i + 1 < word.length then word[i + 1]
      else fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)
    fkIsingSquareWiredSlotIntPosition n next =
        fkIsingSquareWiredSlotIntPosition n word[i] +
        fkIsingSquareWiredUnitDiagonalStep
          (getElem (fkIsingSquareWiredOrdinaryBondStepWord n hn d) i (by
            rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_length]
            exact hi)) := by
  dsimp only
  have hturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with h | h <;> rw [h] <;> rfl
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  have hiL : i < L.val := by
    simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hturn] using hi
  have hiStep : i <
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d).length := by
    rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_length]
    exact hi
  let current : Fin 8 := start + ⟨L.val - i, by omega⟩
  let previous : Fin 8 := start + ⟨L.val - 1 - i, by omega⟩
  have hsucc : previous + 1 = current := by
    apply Fin.ext
    simp [previous, current, Fin.add_def]
    omega
  have hcurrent :
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)[i] =
        (u, current) := by
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hturn, current]
  have hstep :
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d)[i]'hiStep =
        fkIsingSquareWiredUnitDiagonalReverse
          (fkIsingSquareWiredRingStepIndex previous) := by
    simp [fkIsingSquareWiredOrdinaryBondStepWord,
      base, u, dir, start, L, hturn, previous]
  have hnext :
      (if h : i + 1 <
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length then
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)[i + 1]
      else fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)) =
        (u, previous) := by
    by_cases h : i + 1 <
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length
    · rw [dif_pos h]
      simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
        base, u, dir, start, L, hturn, previous]
      omega
    · rw [dif_neg h]
      have hiLast : i + 1 = L.val := by
        have hlen :
            (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length =
              L.val := by
          simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
            base, u, dir, start, L, hturn]
        omega
      have hbase : base = fkIsingSquareBondMate n hn d := by
        simp [base, fkIsingSquareWiredBondArcBase, hturn]
      rw [← hbase]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp [previous, start, hiLast, Fin.add_def]
        rw [Nat.mod_eq_of_lt (fkIsingSquareWiredDartSlot n base).2.isLt]
  rw [hnext, hcurrent, hstep, ← hsucc]
  exact fkIsingSquareWiredSlotIntPosition_pred_reverse_step n u previous



theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      [fkIsingSquareWiredDartSlot n d] := by
  let u := fkIsingSquareDartEndpoint n d
  have hu0 : u.1 0 = -(n : Int) := hleft
  have hb0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have hb1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have havail := fkIsingSquareDartDirection_available n d
  cases hdir : fkIsingSquareDartDirection n d with
  | east =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · have hne :
            (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
          rw [hclockwise]
          decide
        have havailEast : fkIsingSquareDirectionAvailable n u .east := by
          simpa [u, hdir] using havail
        have hbaseEndpoint : fkIsingSquareDartEndpoint n
            (fkIsingSquareBondMate n hn d) = u := by
          simp [fkIsingSquareBondMate, hclockwise, u]
        have hbaseDirection : fkIsingSquareDartDirection n
            (fkIsingSquareBondMate n hn d) = .south := by
          simp [fkIsingSquareBondMate, hclockwise, u, hdir,
            fkIsingSquarePreviousDirection, hs]
        have hbaseTurn : (fkIsingSquareSideCorner
            (fkIsingSquareBondMate n hn d).2).2 = .counterclockwise := by
          simp [fkIsingSquareBondMate, hclockwise]
        have hL : fkIsingSquareWiredBondArcLength n u .south = 1 := by
          simp [fkIsingSquareWiredBondArcLength, havailEast]
        simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          fkIsingSquareWiredBondArcBase, hne, if_false, hbaseEndpoint,
          hbaseDirection]
        simp [fkIsingSquareWiredDartSlot, hbaseEndpoint, hbaseDirection,
          hbaseTurn, hL, u, hdir, hclockwise,
          fkIsingSquareWiredPortSlot]
      · have hu1 : u.1 1 = -(n : Int) := by
          simp [fkIsingSquareDirectionAvailable] at hs
          omega
        have hu : u = fkIsingSquareMarkedA n := by
          apply Subtype.ext
          funext i
          fin_cases i
          · simpa [fkIsingSquareMarkedA] using hu0
          · simpa [fkIsingSquareMarkedA] using hu1
        apply False.elim
        apply hboundary
        refine ⟨.bottom, ?_⟩
        rw [← fkIsingSquareDirectionDart_reconstruct n d]
        simp [fkIsingSquareWiredBoundaryEmbedding,
          fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]
  | north =>
      have he : fkIsingSquareDirectionAvailable n u .east := by
        simp [fkIsingSquareDirectionAvailable, hu0]
        omega
      have hne :
          (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
        rw [hclockwise]
        decide
      have havailNorth : fkIsingSquareDirectionAvailable n u .north := by
        simpa [u, hdir] using havail
      have hbaseEndpoint : fkIsingSquareDartEndpoint n
          (fkIsingSquareBondMate n hn d) = u := by
        simp [fkIsingSquareBondMate, hclockwise, u]
      have hbaseDirection : fkIsingSquareDartDirection n
          (fkIsingSquareBondMate n hn d) = .east := by
        simp [fkIsingSquareBondMate, hclockwise, u, hdir,
          fkIsingSquarePreviousDirection, he]
      have hbaseTurn : (fkIsingSquareSideCorner
          (fkIsingSquareBondMate n hn d).2).2 = .counterclockwise := by
        simp [fkIsingSquareBondMate, hclockwise]
      have hL : fkIsingSquareWiredBondArcLength n u .east = 1 := by
        simp [fkIsingSquareWiredBondArcLength, havailNorth]
      simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
        fkIsingSquareWiredBondArcBase, hne, if_false, hbaseEndpoint,
        hbaseDirection]
      simp [fkIsingSquareWiredDartSlot, hbaseEndpoint, hbaseDirection,
        hbaseTurn, hL, u, hdir, hclockwise,
        fkIsingSquareWiredPortSlot]
  | west =>
      exfalso
      simp [fkIsingSquareDirectionAvailable, u, hu0, hdir] at havail
  | south =>
      have hsouth : -(n : Int) < u.1 1 := by
        simpa [fkIsingSquareDirectionAvailable, u, hdir] using havail
      let kval : Int := u.1 1 + (n : Int) - 1
      have hk0 : 0 ≤ kval := by simp [kval]; omega
      have hklt : kval < 2 * (n : Int) := by simp [kval]; omega
      let k : Fin (2 * n) := ⟨kval.toNat, by
        have hcast : (kval.toNat : Int) < (2 * n : Nat) := by
          rw [Int.toNat_of_nonneg hk0]
          exact_mod_cast hklt
        exact_mod_cast hcast⟩
      have hkcast : (k.val : Int) = kval := by
        simp [k, Int.toNat_of_nonneg hk0]
      have hu : u = fkIsingSquareLeftVerticalUpper n hn k := by
        apply Subtype.ext
        funext i
        fin_cases i
        · simp [fkIsingSquareLeftVerticalUpper, hu0]
        · simp [fkIsingSquareLeftVerticalUpper, hkcast, kval]
          omega
      apply False.elim
      apply hboundary
      refine ⟨.north k, ?_⟩
      rw [← fkIsingSquareDirectionDart_reconstruct n d]
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]

private theorem fkList_reverse_ofFn
    {A : Type*} {m : Nat} (f : Fin m → A) :
    (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega

theorem fkIsingSquareWiredForwardRingSlotWord_reverse
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (dir : FKIsingSquareDirection) :
    let L := fkIsingSquareWiredBondArcLength n u dir
    let start := fkIsingSquareWiredPortSlot dir .counterclockwise
    (fkIsingSquareWiredForwardRingSlotWord n u dir).reverse =
      List.ofFn (fun j : Fin L.val =>
        (u, start + ⟨L.val - j.val, by omega⟩)) ++ [(u, start)] := by
  simp only [fkIsingSquareWiredForwardRingSlotWord]
  rw [fkList_reverse_ofFn]
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [Fin.val_rev]
  · congr 1
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [Fin.val_rev]


theorem fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        p.support =
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map
              (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++
            [.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn d))] := by
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  have havail : fkIsingSquareDirectionAvailable n u dir := by
    exact fkIsingSquareDartDirection_available n base
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact
      n hn u dir havail
  by_cases hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int)
  · have hclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      rcases hside with hs | hs <;> rw [hs] <;>
        simp [fkIsingSquareSideCorner]
    obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
      fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
        n hn omega d hleft hclock hboundary
    have hedge : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))) := by
      rw [ha, hb]
      exact Or.inr (Or.inl ⟨a, b, rfl, rfl, hkeepA, hkeepB, hab⟩)
    let p := SimpleGraph.Walk.cons hedge SimpleGraph.Walk.nil
    have hp : p.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [p, hedge.ne]
    refine ⟨p, hp, ?_⟩
    rw [fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
      n hn d hleft hclock hboundary]
    simp [p]
  · by_cases hccw : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · have hbaseEndpoint : fkIsingSquareDartEndpoint n base =
        fkIsingSquareDartEndpoint n d := by
        simp [base, fkIsingSquareWiredBondArcBase, fkIsingSquareBondMate, hccw]
      have hbaseLeft : u.1 0 ≠ -(n : Int) := by
        intro hu
        apply hleft
        rw [← hbaseEndpoint]
        simpa [u] using hu
      obtain ⟨p, hp, _, hpSupport, _⟩ :=
        fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
          n hn omega q hq hbaseLeft
      let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
          (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))) :=
        p.copy (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
          (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
            fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
      refine ⟨p', ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
        simpa [p'] using hp
      · rw [hqSupport] at hpSupport
        simp only [fkIsingSquareWiredForwardRingSlotWord] at hpSupport
        rw [List.ofFn_succ'] at hpSupport
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          fkIsingSquareWiredPortSlot_nextDirection,
          List.map_append, p'] using hpSupport
    · have hclock :
          (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases hx : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hbaseEndpoint : fkIsingSquareDartEndpoint n base =
          fkIsingSquareDartEndpoint n d := by
        simp [base, fkIsingSquareWiredBondArcBase, fkIsingSquareBondMate,
          hccw, hclock]
      have hbaseLeft : u.1 0 ≠ -(n : Int) := by
        intro hu
        apply hleft
        rw [← hbaseEndpoint]
        simpa [u] using hu
      obtain ⟨p, hp, _, hpSupport, _⟩ :=
        fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
          n hn omega q.reverse hq.reverse hbaseLeft
      have hnextPrev := fkIsingSquareNextDirection_previous n hn
        (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
        (fkIsingSquareDartDirection_available n d)
      let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
          (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))) :=
        p.copy (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, hclock,
          u, dir, fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          hnextPrev])
          (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, hclock,
            u, dir, fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
      refine ⟨p', ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
        simpa [p'] using hp
      · rw [SimpleGraph.Walk.support_reverse, hqSupport] at hpSupport
        rw [fkIsingSquareWiredForwardRingSlotWord_reverse] at hpSupport
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          base, fkIsingSquareWiredBondArcBase, hccw, hclock, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          List.map_append, p'] using hpSupport


theorem fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
      p.support =
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map
            (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++
          [.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        fkIsingSquareWiredOrdinaryBondStepWord n hn d := by
  obtain ⟨p, hp, hsupport⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact
      n hn omega d hside hboundary
  refine ⟨p, hp, hsupport, ?_⟩
  let word := fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d
  let steps := fkIsingSquareWiredOrdinaryBondStepWord n hn d
  have hlen : p.darts.length = word.length := by
    have h := p.length_support
    rw [hsupport] at h
    simp [word] at h ⊢
    omega
  have hsteps : steps.length = word.length := by
    simpa [steps, word] using
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord_length n hn d).symm
  apply List.ext_getElem
  · simp only [List.length_map]
    change p.darts.length = steps.length
    exact hlen.trans hsteps.symm
  · intro i hiLeft hiRight
    rw [List.getElem_map]
    apply fkIsingSquareWiredUnitDiagonalStep_injective
    have hiDarts : i < p.darts.length := by simpa using hiLeft
    have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega
      (getElem p.darts i hiDarts)
    have htable := fkIsingSquareWiredOrdinaryBondSlotVertexWord_step
      n hn d hside i (by simpa [← hlen, word] using hiLeft)
    have hfst : (getElem p.darts i hiDarts).fst = .inl word[i] := by
      rw [SimpleGraph.Walk.fst_darts_getElem hiDarts]
      simp [hsupport, word]
    have hsnd : (getElem p.darts i hiDarts).snd =
        .inl (if h : i + 1 < word.length then word[i + 1]
          else fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d)) := by
      rw [SimpleGraph.Walk.snd_darts_getElem hiDarts]
      by_cases hnext : i + 1 < word.length
      · simp [hsupport, word, hnext]
      · have hilast : i + 1 = word.length := by
          have hiw : i < word.length := by simpa [← hlen] using hiLeft
          omega
        simp [hsupport, word, hnext, hilast]
    rw [hfst, hsnd] at hspec
    simpa [fkIsingSquareWiredExpandedIntPosition, steps, word] using
      hspec.symm.trans htable


noncomputable def fkIsingSquareWiredBoundaryNorthIndex
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Option (Fin (2 * n)) :=
  if h : ∃ k : Fin (2 * n),
      d = fkIsingSquareWiredBoundaryDart n hn (.north k) then
    some (Classical.choose h)
  else none

@[simp] theorem fkIsingSquareWiredBoundaryNorthIndex_boundaryDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryNorthIndex n hn
      (fkIsingSquareWiredBoundaryDart n hn (.north k)) = some k := by
  have hex : ∃ l : Fin (2 * n),
      fkIsingSquareWiredBoundaryDart n hn (.north k) =
        fkIsingSquareWiredBoundaryDart n hn (.north l) := ⟨k, rfl⟩
  simp only [fkIsingSquareWiredBoundaryNorthIndex, dif_pos hex]
  congr 1
  have hchoose := Classical.choose_spec hex
  exact Fin.ext (congrArg (fun d => match d with
    | FKIsingSquareWiredBoundaryDartIndex.north l => l.val
    | _ => 0) (fkIsingSquareWiredBoundaryDart_injective n hn hchoose)).symm

theorem fkIsingSquareWiredBoundaryNorthIndex_eq_some
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Fin (2 * n))
    (h : fkIsingSquareWiredBoundaryNorthIndex n hn d = some k) :
    d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  unfold fkIsingSquareWiredBoundaryNorthIndex at h
  split at h
  · have hchoose := Classical.choose_spec ‹∃ l, _›
    have hk : Classical.choose ‹∃ l, _› = k := Option.some.inj h
    simpa [hk] using hchoose
  · simp at h


noncomputable def fkIsingSquareWiredPortMacroVertexWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    List (FKIsingSquareWiredExpandedCarrier n) :=
  match d.2 with
  | .west | .east => [.inl (fkIsingSquareWiredDartSlot n d)]
  | .south =>
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map Sum.inl
  | .north =>
      match fkIsingSquareWiredBoundaryNorthIndex n hn d with
      | some k => [fkIsingSquareWiredExpandedEnd n hn k,
          fkIsingSquareWiredExpandedMiddle n hn k, .inr k]
      | none =>
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map Sum.inl

theorem fkIsingSquareWiredPortMacroVertexWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortMacroVertexWord n hn omega d ≠ [] := by
  rcases d with ⟨e, side⟩
  cases side <;>
    simp [fkIsingSquareWiredPortMacroVertexWord,
      fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil]
  split <;> simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil]

theorem fkIsingSquareWiredPortMacroVertexWord_head
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredPortMacroVertexWord n hn omega d).head
        (fkIsingSquareWiredPortMacroVertexWord_ne_nil n hn omega d) =
      .inl (fkIsingSquareWiredDartSlot n d) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east => rfl
  | south =>
      simp [fkIsingSquareWiredPortMacroVertexWord,
        fkIsingSquareWiredOrdinaryBondSlotVertexWord_head]
  | north =>
      cases hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) with
      | none =>
          simp [fkIsingSquareWiredPortMacroVertexWord, hi,
            fkIsingSquareWiredOrdinaryBondSlotVertexWord_head]
      | some k =>
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          simp only [fkIsingSquareWiredPortMacroVertexWord, hi,
            List.head_cons]
          rw [hd]
          simp [fkIsingSquareWiredExpandedEnd,
            fkIsingSquareWiredDartSlot,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareWiredPortSlot]



theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧
      p.support = fkIsingSquareWiredPortMacroVertexWord n hn omega d ++
        [.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        fkIsingSquareWiredPortMacroStepWord n hn omega d := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      let hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl,
          ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩⟩
      have hslotNe : fkIsingSquareWiredDartSlot n (e, .west) ≠
          fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)) := by
        intro h
        apply FKIsingMedialDart.localMate_ne omega (e, .west)
        exact (fkIsingSquareWiredDartSlot_injective n h).symm
      let p := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      refine ⟨p, ?_, by
        simp [p, fkIsingSquareWiredPortMacroVertexWord,
          fkIsingSquareWiredPortNext], ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
        rw [List.nodup_cons]
        constructor
        · simpa only [List.mem_singleton] using
            (show (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
                .inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega (e, .west))) from
              fun h => hslotNe (Sum.inl.inj h))
        · exact List.nodup_singleton _
      change [fkIsingSquareWiredExpandedDartStepIndex n hn omega {
          fst := (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n)
          snd := .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))
          adj := hadj }] =
        [fkIsingSquareWiredLocalStepIndex omega (e, .west)]
      congr 1
      apply fkIsingSquareWiredUnitDiagonalStep_injective
      have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega {
        fst := (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n)
        snd := .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .west)))
        adj := hadj }
      have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) =
          fkIsingSquareWiredExpandedIntPosition n hn
            (.inl (fkIsingSquareWiredDartSlot n (e, .west))) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredLocalStepIndex omega (e, .west)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition,
          fkIsingSquareWiredSlotIntPosition_dartSlot] using
          fkIsingSquareWiredPortIntPosition_localMate_exact_step
            n omega (e, .west)
      exact add_left_cancel (hspec.symm.trans hlocal)
  | east =>
      let hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl,
          ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩⟩
      have hslotNe : fkIsingSquareWiredDartSlot n (e, .east) ≠
          fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)) := by
        intro h
        apply FKIsingMedialDart.localMate_ne omega (e, .east)
        exact (fkIsingSquareWiredDartSlot_injective n h).symm
      let p := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      refine ⟨p, ?_, by
        simp [p, fkIsingSquareWiredPortMacroVertexWord,
          fkIsingSquareWiredPortNext], ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
        rw [List.nodup_cons]
        constructor
        · simpa only [List.mem_singleton] using
            (show (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
                .inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega (e, .east))) from
              fun h => hslotNe (Sum.inl.inj h))
        · exact List.nodup_singleton _
      change [fkIsingSquareWiredExpandedDartStepIndex n hn omega {
          fst := (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n)
          snd := .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))
          adj := hadj }] =
        [fkIsingSquareWiredLocalStepIndex omega (e, .east)]
      congr 1
      apply fkIsingSquareWiredUnitDiagonalStep_injective
      have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega {
        fst := (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n)
        snd := .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .east)))
        adj := hadj }
      have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) =
          fkIsingSquareWiredExpandedIntPosition n hn
            (.inl (fkIsingSquareWiredDartSlot n (e, .east))) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredLocalStepIndex omega (e, .east)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition,
          fkIsingSquareWiredSlotIntPosition_dartSlot] using
          fkIsingSquareWiredPortIntPosition_localMate_exact_step
            n omega (e, .east)
      exact add_left_cancel (hspec.symm.trans hlocal)
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
          n hn e h)
      obtain ⟨p, hp, hsupp, hdir⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
          n hn omega (e, .south) (Or.inl rfl) hboundary
      rw [fkIsingSquareWiredPortNext,
        fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn (e, .south) hboundary]
      exact ⟨p, hp, by simpa [fkIsingSquareWiredPortMacroVertexWord] using hsupp,
        by simpa [fkIsingSquareWiredPortMacroStepWord] using hdir⟩
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext := fkIsingSquareWiredBondMate_north n hn k
          let h2raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedMiddle n hn k)
              (fkIsingSquareWiredExpandedEnd n hn k) :=
            Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
          let h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedEnd n hn k)
              (fkIsingSquareWiredExpandedMiddle n hn k) :=
            h2raw.symm
          let h1raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
            Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
          let h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedMiddle n hn k) (.inr k) :=
            h1raw.symm
          let h0raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
            Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
          let h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (.inr k) (fkIsingSquareWiredExpandedStart n hn k) :=
            h0raw.symm
          let p := SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h1
            (SimpleGraph.Walk.cons h0 SimpleGraph.Walk.nil))
          have hd2 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h2⟩ = 1 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h2⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
                (fkIsingSquareWiredExpandedMiddle n hn k) =
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedEnd n hn k) +
                  fkIsingSquareWiredUnitDiagonalStep 1 := by
              simp [fkIsingSquareWiredExpandedEnd,
                fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalUpper, Prod.ext_iff]
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hd1 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h1⟩ = 0 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h1⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn (.inr k) =
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedMiddle n hn k) +
                  fkIsingSquareWiredUnitDiagonalStep 0 := by
              simp [fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalLower,
                fkIsingSquareLeftVerticalUpper, Prod.ext_iff]
              omega
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hd0 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h0⟩ = 2 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h0⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
                (fkIsingSquareWiredExpandedStart n hn k) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inr k) +
                  fkIsingSquareWiredUnitDiagonalStep 2 := by
              simp [fkIsingSquareWiredExpandedStart,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalLower, Prod.ext_iff]
              omega
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedMiddle,
              fkIsingSquareWiredExpandedEnd]
          let bd := fkIsingSquareWiredBoundaryDart n hn (.north k)
          have hsideNorth : bd.2 = .north := by
            simp [bd, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hbd : bd = (bd.1, .north) := by
            exact Prod.ext rfl hsideNorth
          have hportNext : fkIsingSquareWiredPortNext n hn omega bd =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            calc
              fkIsingSquareWiredPortNext n hn omega bd =
                  fkIsingSquareWiredPortNext n hn omega (bd.1, .north) :=
                congrArg (fkIsingSquareWiredPortNext n hn omega) hbd
              _ = fkIsingSquareWiredBondMate n hn (bd.1, .north) := rfl
              _ = fkIsingSquareWiredBondMate n hn bd :=
                congrArg (fkIsingSquareWiredBondMate n hn) hbd.symm
              _ = fkIsingSquareWiredBoundaryDart n hn (.west k) := by
                simpa [bd] using hnext
          have hportNext' : fkIsingSquareWiredPortNext n hn omega
                (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa [bd] using hportNext
          have hindex : fkIsingSquareWiredBoundaryNorthIndex n hn bd = some k := by
            simpa [bd] using
              fkIsingSquareWiredBoundaryNorthIndex_boundaryDart n hn k
          have hmacro : fkIsingSquareWiredPortMacroVertexWord n hn omega bd =
              [fkIsingSquareWiredExpandedEnd n hn k,
                fkIsingSquareWiredExpandedMiddle n hn k, .inr k] := by
            simp [fkIsingSquareWiredPortMacroVertexWord, hsideNorth, hindex]
          have hbdRange : bd ∈ Set.range
              (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          have hsteps : fkIsingSquareWiredPortMacroStepWord n hn omega bd =
              [1, 0, 2] := by
            simp only [fkIsingSquareWiredPortMacroStepWord, hsideNorth,
              if_pos hbdRange, fkIsingSquareWiredBulgeReverseStepWord]
          have hterminalSlot :
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega bd)) :
                  FKIsingSquareWiredExpandedCarrier n) =
                fkIsingSquareWiredExpandedStart n hn k := by
            rw [hportNext]
            simp [fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot]
          let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredBoundaryDart n hn (.north k))))
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega
                  (fkIsingSquareWiredBoundaryDart n hn (.north k))))) :=
            p.copy (by simp [fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot])
            (by
              rw [hportNext']
              simp [
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot])
          refine ⟨p', ?_, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
            simpa [p'] using hp
          · change p'.support =
              fkIsingSquareWiredPortMacroVertexWord n hn omega bd ++
                [.inl (fkIsingSquareWiredDartSlot n
                  (fkIsingSquareWiredPortNext n hn omega bd))]
            rw [hmacro]
            calc
              p'.support = p.support := by
                simp only [p', SimpleGraph.Walk.support_copy]
              _ = [fkIsingSquareWiredExpandedEnd n hn k,
                  fkIsingSquareWiredExpandedMiddle n hn k, .inr k,
                  fkIsingSquareWiredExpandedStart n hn k] := by simp [p]
              _ = [fkIsingSquareWiredExpandedEnd n hn k,
                    fkIsingSquareWiredExpandedMiddle n hn k, .inr k] ++
                  [.inl (fkIsingSquareWiredDartSlot n
                    (fkIsingSquareWiredPortNext n hn omega bd))] := by
                exact congrArg (fun z => [fkIsingSquareWiredExpandedEnd n hn k,
                  fkIsingSquareWiredExpandedMiddle n hn k, (.inr k), z])
                  hterminalSlot.symm
          · change p'.darts.map
                (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
              fkIsingSquareWiredPortMacroStepWord n hn omega bd
            rw [hsteps]
            simp only [p', SimpleGraph.Walk.darts_copy, p,
              SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
              List.map_cons, List.map_nil,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredExpandedMiddle,
              fkIsingSquareWiredExpandedStart, hd2, hd1, hd0]
      · have hindex : fkIsingSquareWiredBoundaryNorthIndex n hn
            (e, .north) = none := by
          have hnot : ¬ ∃ k : Fin (2 * n),
              (e, .north) =
                fkIsingSquareWiredBoundaryDart n hn (.north k) := by
            rintro ⟨k, hk⟩
            exact hboundary ⟨.north k, hk.symm⟩
          simp only [fkIsingSquareWiredBoundaryNorthIndex, dif_neg hnot]
        obtain ⟨p, hp, hsupp, hdir⟩ :=
          fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
            n hn omega (e, .north) (Or.inr rfl) hboundary
        rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        exact ⟨p, hp, by simpa [fkIsingSquareWiredPortMacroVertexWord,
          hindex] using hsupp,
          by simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using hdir⟩

theorem fkIsingSquareWiredPortMacroVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredPortMacroVertexWord n hn omega d).Nodup := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east => simp [fkIsingSquareWiredPortMacroVertexWord]
  | south =>
      simpa [fkIsingSquareWiredPortMacroVertexWord] using
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
          n hn (e, .south)).map Sum.inl_injective
  | north =>
      simp only [fkIsingSquareWiredPortMacroVertexWord]
      split
      · simp [fkIsingSquareWiredExpandedEnd,
          fkIsingSquareWiredExpandedMiddle]
      · simpa using
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
            n hn (e, .north)).map Sum.inl_injective

private theorem fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (j : Fin ((fkIsingSquareWiredBondArcLength n u d).val + 1)) :
    fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot d .counterclockwise +
          ⟨j.val, by
            have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
            omega⟩) ↔
      j.val = 0 ∨
        j.val = (fkIsingSquareWiredBondArcLength n u d).val := by
  have hj := j.isLt
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨
      j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
      hL | hL | hL <;>
      have hLv := congrArg Fin.val hL <;>
      norm_num at hLv <;>
      omega
  have hnext := fkIsingSquareNextDirection_available n hn u d hd
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hnorth] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hnorth,
              if_pos hw] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hnorth,
              if_neg hw] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hw] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hw,
              if_pos hs] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hw,
              if_neg hs] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hs] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hs,
              if_pos he] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hs,
              if_neg he] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · simp only [fkIsingSquareWiredBondArcLength, if_pos he] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · simp only [fkIsingSquareWiredBondArcLength, if_neg he,
              if_pos hnorth] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg he,
              if_neg hnorth] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
    (havail : fkIsingSquareWiredSlotAvailable n x) :
    x = fkIsingSquareWiredDartSlot n d := by
  rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d]
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let L := fkIsingSquareWiredBondArcLength n u dir
  let start := (fkIsingSquareWiredDartSlot n base).2
  have hbaseccw : (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
    by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · simp [base, fkIsingSquareWiredBondArcBase, hturn]
    · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases h : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases h : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
  have hstart : start = fkIsingSquareWiredPortSlot dir .counterclockwise := by
    simp [start, dir, fkIsingSquareWiredDartSlot, hbaseccw]
  have hd : fkIsingSquareDirectionAvailable n u dir := by
    exact fkIsingSquareDartDirection_available n base
  have hword : fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
      else
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨L.val - j.val, by omega⟩) := by
    rfl
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [hword, if_pos hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    let jp : Fin (L.val + 1) := ⟨j.val, by omega⟩
    have havjp : fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot dir .counterclockwise +
          ⟨jp.val, by have hL := L.isLt; omega⟩) := by
      rw [← hstart]
      simpa [jp] using hxi.symm ▸ havail
    have hjEnds := (fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
      n hn u dir hd jp).mp havjp
    have hj0 : j.val = 0 := by
      rcases hjEnds with hj0 | hjL
      · simpa [jp] using hj0
      · have hj := j.isLt
        dsimp [jp] at hjL
        omega
    rw [← hxi]
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
      base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
      List.head_ofFn]
    rw [Nat.mod_eq_of_lt (fkIsingSquareWiredDartSlot n base).2.isLt]
  · rw [hword, if_neg hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    let jp : Fin (L.val + 1) := ⟨L.val - j.val, by omega⟩
    have havjp : fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot dir .counterclockwise +
          ⟨jp.val, by have hL := L.isLt; omega⟩) := by
      rw [← hstart]
      simpa [jp] using hxi.symm ▸ havail
    have hjEnds := (fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
      n hn u dir hd jp).mp havjp
    have hj0 : j.val = 0 := by
      rcases hjEnds with hjzero | hjL
      · have hj := j.isLt
        dsimp [jp] at hjzero
        omega
      · dsimp [jp] at hjL
        omega
    rw [← hxi]
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
      base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
      List.head_ofFn]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
    (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
    x.1 = fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn d) ∧
      fkIsingSquareWiredRingArcContains n x.1
        (fkIsingSquareDartDirection n
          (fkIsingSquareWiredBondArcBase n hn d)) x.2 := by
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let L := fkIsingSquareWiredBondArcLength n u dir
  let start := (fkIsingSquareWiredDartSlot n base).2
  have hbaseccw : (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
    by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · simp [base, fkIsingSquareWiredBondArcBase, hturn]
    · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases h : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases h : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
  have hstart : start = fkIsingSquareWiredPortSlot dir .counterclockwise := by
    simp [start, dir, fkIsingSquareWiredDartSlot, hbaseccw]
  have hword : fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
      else
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨L.val - j.val, by omega⟩) := by
    rfl
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [hword, if_pos hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    rw [← hxi]
    refine ⟨rfl, ?_⟩
    refine ⟨j, ?_⟩
    rw [hstart]
  · rw [hword, if_neg hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    have hjne : j.val ≠ 0 := by
      intro hj0
      apply hunavailable
      have hxstart : x = fkIsingSquareWiredDartSlot n d := by
        rw [← hxi]
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
          base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
          List.head_ofFn] using
          fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d
      rw [hxstart]
      simpa [fkIsingSquareWiredSlotAvailable,
        fkIsingSquareWiredDartSlot] using
        fkIsingSquareDartDirection_available n d
    let k : Fin L.val := ⟨L.val - j.val, by omega⟩
    rw [← hxi]
    refine ⟨rfl, ?_⟩
    refine ⟨k, ?_⟩
    rw [hstart]

theorem fkIsingSquareWiredPortMacroVertexWord_available_eq_start
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d)
    (havail : fkIsingSquareWiredSlotAvailable n x) :
    x = fkIsingSquareWiredDartSlot n d := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east =>
      simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
  | south =>
      simp only [fkIsingSquareWiredPortMacroVertexWord,
        List.mem_map, Sum.inl.injEq] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
        n hn (e, .south) hy havail
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at hx
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at hx
      cases oi with
      | none =>
          simp only [List.mem_map, Sum.inl.injEq] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
            n hn (e, .north) hy havail
      | some k =>
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          rw [hd] at hx ⊢
          have hfirst := List.mem_cons.mp hx
          cases hfirst with
          | inl hEnd =>
            simpa [fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredPortSlot] using Sum.inl.inj hEnd
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle =>
              have hslot := Sum.inl.inj hMiddle
              subst x
              simp [fkIsingSquareWiredSlotAvailable,
                fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredPortSlotDirection,
                fkIsingSquareDirectionAvailable,
                fkIsingSquareLeftVerticalUpper] at havail
            | inr hlast =>
              have hInr := List.mem_singleton.mp hlast
              cases hInr

set_option maxHeartbeats 8000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (k : Fin (2 * n)) :
    (fkIsingSquareLeftVerticalUpper n hn k, 6) ∉
      fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d := by
  intro hx
  have hclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with hs | hnorth
    · rw [hs]
      rfl
    · rw [hnorth]
      rfl
  have hturn : ¬(fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hclock]
    decide
  have hx0 := hx
  simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
    if_false, List.mem_ofFn] at hx0
  rcases hx0 with ⟨j, hxj⟩
  have hxslot := congrArg Prod.snd hxj
  have hxvertex := congrArg Prod.fst hxj
  have hu : fkIsingSquareDartEndpoint n d =
      fkIsingSquareLeftVerticalUpper n hn k := by
    simpa [fkIsingSquareWiredBondArcBase, hturn,
      fkIsingSquareBondMate, hclock] using hxvertex
  have hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int) := by
    rw [hu]
    simp [fkIsingSquareLeftVerticalUpper]
  have hsingleton :=
    fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
      n hn d hleft hclock hboundary
  rw [hsingleton] at hx
  have hxeq : (fkIsingSquareLeftVerticalUpper n hn k, 6) =
      fkIsingSquareWiredDartSlot n d := by
    simpa using hx
  have hturnEq := congrArg
    (fun z : FKIsingSquareWiredSlotCarrier n =>
      fkIsingSquareWiredPortSlotTurn z.2) hxeq
  simp only [fkIsingSquareWiredDartSlot, hclock,
    fkIsingSquareWiredPortSlotTurn_slot] at hturnEq
  simpa [fkIsingSquareWiredPortSlotTurn] using hturnEq

theorem fkIsingSquareWiredSlotAvailable_dartSlot
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredSlotAvailable n
      (fkIsingSquareWiredDartSlot n d) := by
  simpa only [fkIsingSquareWiredSlotAvailable,
    fkIsingSquareWiredDartSlot,
    fkIsingSquareWiredPortSlotDirection_slot] using
    fkIsingSquareDartDirection_available n d

theorem fkIsingSquareWiredPortMacroVertexWord_inr
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n))
    (h : (.inr k : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d) :
    d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east | south =>
      simp [fkIsingSquareWiredPortMacroVertexWord] at h
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at h
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at h
      cases oi with
      | none => simp at h
      | some l =>
          have hfirst := List.mem_cons.mp h
          cases hfirst with
          | inl hEnd => cases hEnd
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle => cases hMiddle
            | inr hlast =>
              have hkl : k = l := Sum.inr.inj
                (List.mem_singleton.mp hlast)
              subst l
              exact fkIsingSquareWiredBoundaryNorthIndex_eq_some
                n hn (e, .north) k hi

theorem fkIsingSquareWiredPortMacroVertexWord_unavailable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d)
    (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
    (d.2 = .south ∨ d.2 = .north) ∧
        d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) ∧
        x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ∨
      ∃ k : Fin (2 * n),
        d = fkIsingSquareWiredBoundaryDart n hn (.north k) ∧
        x = (fkIsingSquareLeftVerticalUpper n hn k, 6) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hx' : x = fkIsingSquareWiredDartSlot n (e, .west) := by
        simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
      exact False.elim (hunavailable
        (hx' ▸ fkIsingSquareWiredSlotAvailable_dartSlot n (e, .west)))
  | east =>
      have hx' : x = fkIsingSquareWiredDartSlot n (e, .east) := by
        simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
      exact False.elim (hunavailable
        (hx' ▸ fkIsingSquareWiredSlotAvailable_dartSlot n (e, .east)))
  | south =>
      left
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · intro hboundary
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
            n hn e hboundary)
      · simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at hx
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at hx
      cases oi with
      | none =>
          left
          refine ⟨Or.inr rfl, ?_, ?_⟩
          · intro hboundary
            rcases
              fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
                n hn e hboundary with hterm | ⟨k, hk⟩
            · exact hterminal hterm
            · rw [hk, fkIsingSquareWiredBoundaryNorthIndex_boundaryDart] at hi
              cases hi
          · simp only [List.mem_map, Sum.inl.injEq] at hx
            rcases hx with ⟨a, ha, rfl⟩
            exact ha
      | some k =>
          right
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          refine ⟨k, hd, ?_⟩
          rw [hd] at hx
          have hfirst := List.mem_cons.mp hx
          cases hfirst with
          | inl hEnd =>
            have hx' := Sum.inl.inj hEnd
            subst x
            exact False.elim (hunavailable (by
              simp [fkIsingSquareWiredSlotAvailable,
                fkIsingSquareWiredExpandedEnd,
                fkIsingSquareWiredPortSlotDirection,
                fkIsingSquareDirectionAvailable,
                fkIsingSquareLeftVerticalUpper]))
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle =>
              simpa [fkIsingSquareWiredExpandedMiddle] using
                Sum.inl.inj hMiddle
            | inr hlast =>
              have hInr := List.mem_singleton.mp hlast
              cases hInr

theorem fkIsingSquareWiredBondArcBase_corner
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBondArcBase n hn d).2).2 = .counterclockwise := by
  unfold fkIsingSquareWiredBondArcBase
  split
  · assumption
  · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      cases hd : (fkIsingSquareSideCorner d.2).2 <;> simp_all
    simp [fkIsingSquareBondMate, hdclock]

theorem fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction
    (n : Nat) (hn : 0 < n)
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hendpoint : fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn d) =
      fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn e))
    (hdirection : fkIsingSquareDartDirection n
        (fkIsingSquareWiredBondArcBase n hn d) =
      fkIsingSquareDartDirection n
        (fkIsingSquareWiredBondArcBase n hn e)) :
    fkIsingSquareWiredBondArcBase n hn d =
      fkIsingSquareWiredBondArcBase n hn e := by
  let bd := fkIsingSquareWiredBondArcBase n hn d
  let be := fkIsingSquareWiredBondArcBase n hn e
  have hd := fkIsingSquareDirectionDart_reconstruct n bd
  have he := fkIsingSquareDirectionDart_reconstruct n be
  have hturnD : (fkIsingSquareSideCorner bd.2).2 = .counterclockwise :=
    fkIsingSquareWiredBondArcBase_corner n hn d
  have hturnE : (fkIsingSquareSideCorner be.2).2 = .counterclockwise :=
    fkIsingSquareWiredBondArcBase_corner n hn e
  rw [hturnD] at hd
  rw [hturnE] at he
  apply Eq.symm
  calc
    be = fkIsingSquareDirectionDart n
        (fkIsingSquareDartEndpoint n be)
        (fkIsingSquareDartDirection n be)
        (fkIsingSquareDartDirection_available n be) .counterclockwise := he.symm
    _ = fkIsingSquareDirectionDart n
        (fkIsingSquareDartEndpoint n bd)
        (fkIsingSquareDartDirection n bd)
        (fkIsingSquareDartDirection_available n bd) .counterclockwise := by
      have hbeAtBd : fkIsingSquareDirectionAvailable n
          (fkIsingSquareDartEndpoint n bd)
          (fkIsingSquareDartDirection n be) := by
        rw [hendpoint]
        exact fkIsingSquareDartDirection_available n be
      calc
        fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n be)
            (fkIsingSquareDartDirection n be)
            (fkIsingSquareDartDirection_available n be) .counterclockwise =
          fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n bd)
            (fkIsingSquareDartDirection n be) hbeAtBd .counterclockwise :=
          fkIsingSquareDirectionDart_endpoint_congr n hendpoint.symm
            (fkIsingSquareDartDirection n be)
            (fkIsingSquareDartDirection_available n be) hbeAtBd _
        _ = fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n bd)
            (fkIsingSquareDartDirection n bd)
            (fkIsingSquareDartDirection_available n bd) .counterclockwise :=
          fkIsingSquareDirectionDart_congr n _ hdirection.symm hbeAtBd
            (fkIsingSquareDartDirection_available n bd) _
    _ = bd := hd

private theorem fkIsingSquareWired_not_source_terminal_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    d ≠ fkIsingSquareWiredSourceDart n hn ∧
      d ≠ fkIsingSquareWiredTerminalDart n hn := by
  constructor
  · intro h
    apply hboundary
    exact ⟨.bottom, by simpa [fkIsingSquareWiredSourceDart] using h.symm⟩
  · intro h
    apply hboundary
    exact ⟨.top, by simpa [fkIsingSquareWiredTerminalDart] using h.symm⟩

theorem fkIsingSquareWiredBondArcBase_injective_black
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdside : d.2 = .south ∨ d.2 = .north)
    (heside : e.2 = .south ∨ e.2 = .north)
    (hdboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (heboundary : e ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hbase : fkIsingSquareWiredBondArcBase n hn d =
      fkIsingSquareWiredBondArcBase n hn e) :
    d = e := by
  have hdcut := fkIsingSquareWired_not_source_terminal_of_not_boundary
    n hn d hdboundary
  have hecut := fkIsingSquareWired_not_source_terminal_of_not_boundary
    n hn e heboundary
  have hdwire := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d hdboundary
  have hewire := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn e heboundary
  cases hdturn : (fkIsingSquareSideCorner d.2).2 <;>
    cases heturn : (fkIsingSquareSideCorner e.2).2
  · simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
  · have hde : d = fkIsingSquareBondMate n hn e := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
    have hc := fkIsingSquareWiredCarrierColor_transition_ne
      n hn omega (.bond e)
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega (.bond e)) ≠
      fkIsingSquareWiredCarrierColor n (.bond e) at hc
    rw [show fkIsingSquareWiredTransitionMate n hn omega (.bond e) =
        .bond d by
      simp [fkIsingSquareWiredTransitionMate, hecut.1, hecut.2,
        hewire, hde]] at hc
    rcases hdside with hds | hdn
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hen] at hc
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hen] at hc
  · have hed : e = fkIsingSquareBondMate n hn d := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase.symm
    have hc := fkIsingSquareWiredCarrierColor_transition_ne
      n hn omega (.bond d)
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega (.bond d)) ≠
      fkIsingSquareWiredCarrierColor n (.bond d) at hc
    rw [show fkIsingSquareWiredTransitionMate n hn omega (.bond d) =
        .bond e by
      simp [fkIsingSquareWiredTransitionMate, hdcut.1, hdcut.2,
        hdwire, hed]] at hc
    rcases hdside with hds | hdn
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hen] at hc
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hen] at hc
  · have hmate : fkIsingSquareBondMate n hn d =
        fkIsingSquareBondMate n hn e := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
    exact (fkIsingSquareBondMate_involutive n hn d).symm.trans
      ((congrArg (fkIsingSquareBondMate n hn) hmate).trans
        (fkIsingSquareBondMate_involutive n hn e))

set_option maxHeartbeats 2000000 in
theorem fkIsingSquareWiredRingArcContains_direction_injective
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    {i : Fin 8}
    (hdi : fkIsingSquareWiredRingArcContains n u d i)
    (hei : fkIsingSquareWiredRingArcContains n u e i) :
    d = e := by
  classical
  rcases hdi with ⟨j, hj⟩
  rcases hei with ⟨k, hk⟩
  cases d <;> cases e <;>
    by_cases ha : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hb : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hc : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hd' : fkIsingSquareDirectionAvailable n u .south <;>
    have hjlt := j.isLt <;>
    have hklt := k.isLt <;>
    simp [fkIsingSquareWiredBondArcLength, ha, hb, hc, hd'] at hjlt hklt <;>
    simp [fkIsingSquareWiredRingArcContains,
      fkIsingSquareWiredBondArcLength,
      fkIsingSquareWiredPortSlot, ha, hb, hc, hd',
      Fin.ext_iff, Fin.add_def] at hd he hj hk ⊢ <;>
    omega



theorem fkIsingSquareWiredPortMacroVertexWord_disjoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hesource : e ≠ fkIsingSquareWiredSourceDart n hn)
    (heterminal : e ≠ fkIsingSquareWiredTerminalDart n hn)
    (hne : d ≠ e) :
    List.Disjoint
      (fkIsingSquareWiredPortMacroVertexWord n hn omega d)
      (fkIsingSquareWiredPortMacroVertexWord n hn omega e) := by
  apply List.disjoint_left.2
  intro v hvd hve
  cases v with
  | inr k =>
      apply hne
      exact (fkIsingSquareWiredPortMacroVertexWord_inr
        n hn omega d k hvd).trans
        (fkIsingSquareWiredPortMacroVertexWord_inr
          n hn omega e k hve).symm
  | inl x =>
      by_cases havail : fkIsingSquareWiredSlotAvailable n x
      · have hd := fkIsingSquareWiredPortMacroVertexWord_available_eq_start
          n hn omega d hdsource hdterminal hvd havail
        have he := fkIsingSquareWiredPortMacroVertexWord_available_eq_start
          n hn omega e hesource heterminal hve havail
        apply hne
        exact fkIsingSquareWiredDartSlot_injective n (hd.symm.trans he)
      · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
          n hn omega d hdsource hdterminal hvd havail with hd | hd
        · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
            n hn omega e hesource heterminal hve havail with he | he
          · obtain ⟨hdu, hdarc⟩ :=
              fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
                n hn d hd.2.2 havail
            obtain ⟨heu, hearc⟩ :=
              fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
                n hn e he.2.2 havail
            have hdavail := fkIsingSquareDartDirection_available n
              (fkIsingSquareWiredBondArcBase n hn d)
            have heavail := fkIsingSquareDartDirection_available n
              (fkIsingSquareWiredBondArcBase n hn e)
            have hdir : fkIsingSquareDartDirection n
                (fkIsingSquareWiredBondArcBase n hn d) =
              fkIsingSquareDartDirection n
                (fkIsingSquareWiredBondArcBase n hn e) := by
              apply fkIsingSquareWiredRingArcContains_direction_injective
                n x.1 _ _
              · simpa [hdu] using hdavail
              · simpa [heu] using heavail
              · simpa [hdu] using hdarc
              · simpa [heu] using hearc
            have hbase := fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction
              n hn d e (hdu.symm.trans heu) hdir
            exact hne (fkIsingSquareWiredBondArcBase_injective_black
              n hn omega d e hd.1 he.1 hd.2.1 he.2.1 hbase)
          · obtain ⟨k, hek, hex⟩ := he
            subst x
            exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
              n hn d hd.1 hd.2.1 k hd.2.2
        · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
            n hn omega e hesource heterminal hve havail with he | he
          · obtain ⟨k, hdk, hdx⟩ := hd
            subst x
            exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
              n hn e he.1 he.2.1 k he.2.2
          · obtain ⟨k, hdk, hdx⟩ := hd
            obtain ⟨l, hel, hex⟩ := he
            have hkl : k = l := by
              have hpos := congrArg (fun z => z.1.1 1) (hdx.symm.trans hex)
              simp [fkIsingSquareLeftVerticalUpper] at hpos
              exact Fin.ext (by omega)
            subst l
            exact hne (hdk.trans hel.symm)



theorem fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d))),
      let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
      p.support = darts.flatMap
          (fkIsingSquareWiredPortMacroVertexWord n hn omega) ++
        [.inl (fkIsingSquareWiredDartSlot n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  induction k generalizing d with
  | zero =>
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      obtain ⟨p, _hpPath, hp, hpdir⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction
          n hn omega d (hsource 0 (by omega)) (hterminal 0 (by omega))
      obtain ⟨q, hq, hqdir⟩ := ih (f d)
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hsource (i + 1) (by omega))
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hterminal (i + 1) (by omega))
      let r := p.append q
      have hend : f^[k] (f d) = f^[k + 1] d := by
        simpa only [Function.iterate_succ_apply] using
          (Function.Commute.iterate_right (Function.Commute.refl f) k d)
      have hendSlot :
          (.inl (fkIsingSquareWiredDartSlot n (f^[k] (f d))) :
              FKIsingSquareWiredExpandedCarrier n) =
            .inl (fkIsingSquareWiredDartSlot n (f^[k + 1] d)) :=
        congrArg (fun z => (.inl (fkIsingSquareWiredDartSlot n z) :
          FKIsingSquareWiredExpandedCarrier n)) hend
      refine ⟨r.copy rfl (by simpa only [f] using hendSlot), ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_append, r]
        rw [hp, hq]
        cases k with
        | zero => simp [f]
        | succ k =>
            have hblock := fkIsingSquareWiredPortMacroVertexWord_ne_nil
              n hn omega (f d)
            have hhead := fkIsingSquareWiredPortMacroVertexWord_head
              n hn omega (f d)
              (hsource 1 (by omega)) (hterminal 1 (by omega))
            simp [f, hend, hblock, hhead]
            rw [← hhead]
            change (((fkIsingSquareWiredPortMacroVertexWord n hn omega
              (f d)).head hblock ::
                (fkIsingSquareWiredPortMacroVertexWord n hn omega
                  (f d)).tail) ++ _) =
              fkIsingSquareWiredPortMacroVertexWord n hn omega (f d) ++ _
            rw [List.cons_head_tail hblock]
      · simp only [SimpleGraph.Walk.darts_copy,
          SimpleGraph.Walk.darts_append, List.map_append, r]
        rw [hpdir, hqdir]
        rfl

private theorem List.length_le_flatMap_of_ne_nil
    {A B : Type*} (l : List A) (g : A → List B)
    (hg : ∀ a ∈ l, g a ≠ []) :
    l.length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have ha : 0 < (g a).length :=
        List.length_pos_of_ne_nil (hg a (by simp))
      have ht := ih (fun b hb => hg b (by simp [hb]))
      omega


theorem fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hfsource : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredSourceDart n hn)
    (hfterminal : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hclose : (fkIsingSquareWiredPortNext n hn omega)^[2] d = d) :
    (fkIsingSquareWiredPortMacroStepWord n hn omega d).length +
      (fkIsingSquareWiredPortMacroStepWord n hn omega
        (fkIsingSquareWiredPortNext n hn omega d)).length ≠ 2 := by
  let f := fkIsingSquareWiredPortNext n hn omega
  intro hlen
  rcases d with ⟨e, side⟩
  let savedSide := side
  let d0 : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, savedSide)
  cases side with
  | west | east =>
      cases homega : omega e.1 <;>
        simp only [f, fkIsingSquareWiredPortNext,
          FKIsingMedialDart.localMate, homega,
          Function.iterate_succ_apply, Function.iterate_zero_apply] at hclose
      all_goals
        let q := FKIsingMedialDart.localMate omega d0
        have hq : f d0 = q := by
          simp [f, q, fkIsingSquareWiredPortNext, d0, savedSide]
        by_cases hboundary : q ∈
            Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
        · rcases q with ⟨qe, qs⟩
          cases qs with
          | west | east =>
              simp [f, fkIsingSquareWiredPortNext, d0, savedSide,
                FKIsingMedialDart.localMate, homega] at hq
          | south =>
              exact hfsource (hq.trans
                (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
                  n hn qe hboundary))
          | north =>
              rcases
                fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
                  n hn qe hboundary with hterm | ⟨k, hk⟩
              · exact hfterminal (hq.trans hterm)
              · rw [hk] at hq hboundary
                have hsideNorth :
                    (fkIsingSquareWiredBoundaryDart n hn (.north k)).2 =
                      .north := by
                  simp [fkIsingSquareWiredBoundaryDart,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hbdRange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
                    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
                  ⟨.north k, rfl⟩
                have hsteps : fkIsingSquareWiredPortMacroStepWord n hn omega
                    (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
                      [1, 0, 2] := by
                  simp only [fkIsingSquareWiredPortMacroStepWord, hsideNorth,
                    if_pos hbdRange, fkIsingSquareWiredBulgeReverseStepWord]
                change 1 + (fkIsingSquareWiredPortMacroStepWord
                  n hn omega (f d0)).length = 2 at hlen
                rw [hq] at hlen
                rw [hsteps] at hlen
                simp at hlen
        · have hmate := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn q hboundary
          have hlocal : FKIsingMedialDart.localMate omega q = d0 := by
            simpa only [q] using
              FKIsingMedialDart.localMate_involutive omega d0
          have hB : fkIsingSquareBondMate n hn q = d0 := by
            calc
              fkIsingSquareBondMate n hn q =
                  fkIsingSquareWiredBondMate n hn q := hmate.symm
              _ = d0 := by
                simpa [q, d0, savedSide, FKIsingMedialDart.localMate,
                  homega] using hclose
          exact fkIsingSquareBondMate_ne_localMate n hn omega q
            (hB.trans hlocal.symm)
  | south | north =>
      let q : FKIsingMedialDart (fkSquareBoxPlanar n) := d0
      have hside : savedSide = .south ∨ savedSide = .north := by
        simp [savedSide]
      by_cases hboundary : q ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases hside with hside | hside
        · simp [savedSide] at hside
          all_goals
            exact hdsource
              (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
                n hn e hboundary)
        · simp [savedSide] at hside
          all_goals
            have hfirst : (fkIsingSquareWiredPortMacroStepWord
                n hn omega d0).length = 3 := by
              simp [fkIsingSquareWiredPortMacroStepWord, d0, q, savedSide,
                hboundary, fkIsingSquareWiredBulgeReverseStepWord]
            change (fkIsingSquareWiredPortMacroStepWord n hn omega d0).length +
                (fkIsingSquareWiredPortMacroStepWord n hn omega (f d0)).length =
              2 at hlen
            rw [hfirst] at hlen
            omega
      · have hmate := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn q hboundary
        let b := fkIsingSquareBondMate n hn q
        have hqb : f q = b := by
          simpa [f, fkIsingSquareWiredPortNext, q, d0, savedSide, b]
            using hmate
        have hbside : b.2 = .west ∨ b.2 = .east := by
          have hc : (fkIsingSquareSideCorner b.2).2 ≠
              (fkIsingSquareSideCorner q.2).2 := by
            simpa [b] using fkIsingSquareBondMate_cornerTurn_ne n hn q
          cases hbs : b.2 <;>
            simp_all [q, d0, savedSide, fkIsingSquareSideCorner]
        have hlocal : FKIsingMedialDart.localMate omega b = q := by
          have hc := hclose
          simp only [Function.iterate_succ_apply,
            Function.iterate_zero_apply] at hc
          change f (f q) = q at hc
          rw [hqb] at hc
          rcases b with ⟨be, bs⟩
          rcases hbside with rfl | rfl <;>
            simpa [f, fkIsingSquareWiredPortNext] using hc
        have hB : fkIsingSquareBondMate n hn b = q := by
          simpa [b] using fkIsingSquareBondMate_involutive n hn q
        exact fkIsingSquareBondMate_ne_localMate n hn omega b
          (hB.trans hlocal.symm)

private theorem fkIsingSquareWiredBoundaryForward_asymm
    (n : Nat) (hn : 0 < n)
    {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
    (hdf : fkIsingSquareWiredBoundaryForward n hn d f) :
    ¬ fkIsingSquareWiredBoundaryForward n hn f d := by
  intro hfd
  rcases hdf with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · rcases hfd with ⟨h, _⟩ | ⟨l, h, _⟩
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredTerminalDart] using h)
      cases hi
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredTerminalDart] using h)
      cases hi
  · rcases hfd with ⟨h, _⟩ | ⟨l, h, _⟩
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredSourceDart] using h)
      cases hi
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi

private theorem fkIsingSquareOrientedPrincipalBondTurn_add_swap_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hturn : (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2) :
    fkIsingSquareOrientedPrincipalBondTurn n hn d f +
        fkIsingSquareOrientedPrincipalBondTurn n hn f d ≡ 0 [ZMOD 16] := by
  cases hd : fkIsingSquareDartDirection n d <;>
    cases hf : fkIsingSquareDartDirection n f <;>
    cases htd : (fkIsingSquareSideCorner d.2).2 <;>
    cases htf : (fkIsingSquareSideCorner f.2).2
  all_goals
    simp [htd, htf] at hturn
  all_goals
    norm_num [fkIsingSquareOrientedPrincipalBondTurn,
        fkIsingSquareWiredCarrierTangentCode,
        fkIsingSquareCornerTangentCode,
        fkIsingSquareSignedEighthTurn,
        FKIsingSquareDirection.eighthTurn,
        hd, hf, htd, htf, Int.ModEq]
  all_goals simp

private theorem fkIsingSquareWiredBondTurn_add_mate_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondTurn n hn d
        (fkIsingSquareWiredBondMate n hn d) +
      fkIsingSquareWiredBondTurn n hn
        (fkIsingSquareWiredBondMate n hn d) d ≡ 0 [ZMOD 16] := by
  let f := fkIsingSquareWiredBondMate n hn d
  have hturn : (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
    simpa [f] using fkIsingSquareWiredBondMate_turn_ne n hn d
  by_cases hdf : fkIsingSquareWiredBoundaryForward n hn d f
  · have hfd : ¬ fkIsingSquareWiredBoundaryForward n hn f d :=
      fkIsingSquareWiredBoundaryForward_asymm n hn hdf
    norm_num [fkIsingSquareWiredBondTurn,
      fkIsingSquareWiredBoundaryReverse, hdf, hfd, f, Int.ModEq]
  · by_cases hfd : fkIsingSquareWiredBoundaryForward n hn f d
    · norm_num [fkIsingSquareWiredBondTurn,
        fkIsingSquareWiredBoundaryReverse, hdf, hfd, f, Int.ModEq]
    · simpa [fkIsingSquareWiredBondTurn,
        fkIsingSquareWiredBoundaryReverse, hdf, hfd, f] using
        fkIsingSquareOrientedPrincipalBondTurn_add_swap_mod_sixteen
          n hn d f hturn

set_option maxHeartbeats 4000000 in


theorem fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredTransitionTurn n hn omega x y +
        fkIsingSquareWiredTransitionTurn n hn omega y x ≡ 0 [ZMOD 16] := by
  rcases hxy with ⟨hsource, hterminal, rfl⟩ | rfl
  · cases x <;>
      simp_all [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredTransitionTurn]
  · cases x with
    | source => simp [fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredTransitionTurn]
    | terminal => simp [fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredTransitionTurn]
    | dart d =>
        rcases d with ⟨e, side⟩
        cases homega : omega e.1 <;> cases side <;>
          cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
          norm_num [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredCarrierTangentCode,
            fkIsingSquareCornerTangentCode,
            fkIsingSquareSignedEighthTurn,
            FKIsingMedialDart.localMate,
            fkIsingSquareDartDirection,
            fkIsingSquareSideCorner,
            FKIsingSquareDirection.eighthTurn,
            homega, haxis, Int.ModEq]
    | bond d =>
        by_cases ha : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredSourceDart]
        by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          have hne : fkIsingSquareWiredBoundaryDart n hn .top ≠
              fkIsingSquareWiredSourceDart n hn := by
            simpa [fkIsingSquareWiredTerminalDart] using ha
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredTerminalDart, hne]
        simp only [fkIsingSquareWiredTransitionMate, if_neg ha, if_neg hb]
        simpa only [fkIsingSquareWiredTransitionTurn] using
          fkIsingSquareWiredBondTurn_add_mate_mod_sixteen n hn d

private theorem carrierAdjacentSum_reverse
    {A : Type*} (turn : A → A → Int) (l : List A) :
    carrierAdjacentSum turn l.reverse =
      carrierAdjacentSum (fun x y => turn y x) l := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          have hne : (b :: tail).reverse ≠ [] := by simp
          rw [List.reverse_cons,
            carrierAdjacentSum_append turn (b :: tail).reverse [a] hne (by simp)]
          rw [ih]
          simp only [List.getLast_reverse, List.head_cons,
            carrierAdjacentSum_singleton, add_zero,
            carrierAdjacentSum_cons_cons]
          omega



theorem fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support +
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.reverse.support ≡ 0 [ZMOD 16] := by
  rw [p.support_reverse, carrierAdjacentSum_reverse]
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      cases p with
      | nil =>
          simpa using
            fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
              n hn omega hxz
      | @cons z w y hzw rest =>
          simp only [SimpleGraph.Walk.support_cons,
            carrierAdjacentSum_cons_cons]
          simpa only [zero_add, add_zero, add_assoc, add_left_comm, add_comm]
            using (fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
              n hn omega hxz).add ih

theorem fkIsingSquareWiredPortMacroCodeWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortMacroCodeWord n hn omega d ≠ [] := by
  simp only [fkIsingSquareWiredPortMacroCodeWord, ne_eq,
    List.map_eq_nil_iff]
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp [fkIsingSquareWiredPortMacroStepWord]
  | east => simp [fkIsingSquareWiredPortMacroStepWord]
  | south =>
      simpa [fkIsingSquareWiredPortMacroStepWord] using
        fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn (e, .south)
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · simp [fkIsingSquareWiredPortMacroStepWord, hboundary,
          fkIsingSquareWiredBulgeReverseStepWord]
      · simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using
          fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn (e, .north)

private theorem fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north) :
    (fkIsingSquareWiredOrdinaryBondStepWord n hn d).head
        (fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn d) =
      match (fkIsingSquareOrientedEdge n d.1).axis, d.2 with
      | .horizontal, .south => 0
      | .vertical, .south => 2
      | .horizontal, .north => 3
      | .vertical, .north => 1
      | _, _ => 0 := by
  have hturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with h | h <;> simp [h, fkIsingSquareSideCorner]
  have hnot : (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
    rw [hturn]
    decide
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  have hLpos : 0 < L.val := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u dir with
      h | h | h <;> have hv := congrArg Fin.val h <;> norm_num at hv <;> omega
  have hhead := fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d
  have hslot : start + L = (fkIsingSquareWiredDartSlot n d).2 := by
    have hsnd := congrArg Prod.snd hhead
    simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hnot, if_false] at hsnd
    rw [List.head_ofFn] at hsnd
    simpa using hsnd
  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
    base, u, dir, start, L, hnot, if_false]
  rw [List.head_ofFn]
  simp only [Fin.val_zero, Nat.sub_zero]
  have hpred : (⟨L.val - 1, by omega⟩ : Fin 8) = L - 1 := by
    apply Fin.ext
    simp [Fin.sub_def]
    omega
  rw [hpred, ← add_sub_assoc, hslot]
  rcases d with ⟨e, side⟩
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;> cases side <;>
    simp_all [fkIsingSquareWiredDartSlot, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareWiredPortSlot,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.sub_def, Fin.add_def]

private theorem fkIsingSquareWiredPortMacroCodeWord_head_vertical
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredPortMacroCodeWord n hn omega d).head
        (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d) =
      match (fkIsingSquareOrientedEdge n d.1).axis, d.2 with
      | .horizontal, .south => 5
      | .vertical, .south => 7
      | .horizontal, .north => 1
      | .vertical, .north => 3
      | _, _ => 5 := by
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp at hside
  | east => simp at hside
  | south =>
      have h := congrArg fkIsingSquareWiredUnitDiagonalTangentCode
        (fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
          n hn (e, .south) (Or.inl rfl))
      cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
        simpa [fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredUnitDiagonalTangentCode, haxis] using h
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hrange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hrange
          simp [fkIsingSquareWiredPortMacroCodeWord,
            fkIsingSquareWiredPortMacroStepWord,
            fkIsingSquareWiredBulgeReverseStepWord,
            fkIsingSquareWiredUnitDiagonalTangentCode,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide, hrange]
      · simpa [fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord, hboundary,
          fkIsingSquareWiredUnitDiagonalTangentCode] using (by
            have h := congrArg fkIsingSquareWiredUnitDiagonalTangentCode
              (fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
                n hn (e, .north) (Or.inr rfl))
            cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
              simpa [haxis, fkIsingSquareWiredUnitDiagonalTangentCode] using h)

private def fkIsingSquareWiredMacroGauge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega d
  let raw := fkIsingSquareSignedEighthTurn
    (fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n d).1)
    (code.head (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
  if 0 < raw then raw + 8 else raw

private def fkIsingSquareWiredMacroTurnCoboundaryAt
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let f := fkIsingSquareWiredPortNext n hn omega
  carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d) +
      fkIsingSquareSignedEighthTurn
        ((code d).getLast
          (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
        ((code (f d)).head
          (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (f d))) ≡
    fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) +
      fkIsingSquareWiredMacroGauge n hn omega (f d) -
      fkIsingSquareWiredMacroGauge n hn omega d [ZMOD 16]

macro "south_coboundary_simp" : tactic =>
  `(tactic| simp_all (config := { maxSteps := 1000000 })
    [fkIsingSquareWiredMacroTurnCoboundaryAt,
      fkIsingSquareWiredMacroGauge,
      fkIsingSquareWiredPortMacroCodeWord,
      fkIsingSquareWiredPortMacroStepWord,
      fkIsingSquareWiredOrdinaryBondStepWord,
      fkIsingSquareWiredBondArcBase,
      fkIsingSquareWiredBondArcLength,
      fkIsingSquareBondMate,
      fkIsingSquarePreviousDirection,
      fkIsingSquareNextDirection,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareWiredDartSlot,
      fkIsingSquareWiredPortSlot,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredLocalStepIndex,
      fkIsingSquareWiredUnitDiagonalTangentCode,
      fkIsingSquareWiredPortNext,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredTransitionMate,
      fkIsingSquareWiredTransitionTurn,
      fkIsingSquareWiredBondTurn,
      fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection,
      fkIsingSquareSideCorner,
      FKIsingMedialDart.localMate,
      FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn,
      carrierAdjacentSum,
      Fin.add_def,
      Int.ModEq])

section SouthCoboundaryLeaves

variable (n : Nat) (hn : 0 < n)
variable (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
variable (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
variable (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)
variable (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)
variable (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
  fkIsingSquareWiredSourceDart n hn)
variable (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
  fkIsingSquareWiredTerminalDart n hn)
variable (hboundary : (e, .south) ∉
  Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
variable (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
  fkIsingSquareBondMate n hn (e, .south))
variable (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
  (fkIsingSquareBondMate n hn (e, .south)))
variable (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
  (fkIsingSquareBondMate n hn (e, .south)))

include hsource hterminal hsourceNext hterminalNext hboundary hwired hfwd hrev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_horizontal_south_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .south := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_pos hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .south := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .south hs := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have heast : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    rw [show fkIsingSquareDartEndpoint n q =
        fkIsingSquareDartEndpoint n d by
      simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d]
    simpa [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] using
      fkIsingSquareDartDirection_available n d
  have hlength : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) (fkIsingSquareDartDirection n q) = 1 := by
    simp [hqdirection, fkIsingSquareWiredBondArcLength, heast]
  have hlengthSouth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .south = 1 := by
    simpa [hqdirection] using hlength
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [0] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthSouth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [5] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d = [0] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hddirection, hdturn,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_horizontal_west_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (hw : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .west)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .west := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg hs, if_pos hw]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .west hw := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have heastQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthWest : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .west = 3 := by
    simp [fkIsingSquareWiredBondArcLength, hsQ, heastQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [0, 1, 1] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthWest, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [5, 3, 3] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5, 3, 3]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [0, 1, 1] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hddirection, hdturn,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_horizontal_north_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (hw : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .west)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .north := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg hs, if_neg hw]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .north := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hnorthAvailable : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d) .north := by
    have h := fkIsingSquarePreviousDirection_available n hn
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
      (fkIsingSquareDartDirection_available n d)
    simpa [hprevious] using h
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .north hnorthAvailable := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hwQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .west := by
    simpa [hendpoint] using hw
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have hlengthNorth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .north = 5 := by
    simp [fkIsingSquareWiredBondArcLength, hwQ, hsQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
      [0, 1, 1, 1, 3] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthNorth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
      [5, 3, 3, 3, 1] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5, 3, 3, 3, 1]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [0, 1, 1, 1, 3] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
    have hprincipal : fkIsingSquareOrientedPrincipalBondTurn n hn d q = -4 := by
      simp only [fkIsingSquareOrientedPrincipalBondTurn, hdnotturn,
        and_false, if_false]
      norm_num [
        fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
        hddirection, hdturn, hqdirection, hqturn,
        FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    simp [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, hprincipal]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [7] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [7]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [2] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [1] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [1]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [3] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_vertical_east_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .east := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_pos he]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .east he := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hnorthQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .north := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthEast : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .east = 1 := by
    simp [fkIsingSquareWiredBondArcLength, hnorthQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [2] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthEast, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [7] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d = [2] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hddirection, hdturn, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [7] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [7]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [2] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [1] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [1]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [3] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_vertical_south_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .south := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg he, if_pos hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .south := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .south hs := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have heQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    simpa [hendpoint] using he
  have hnorthQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .north := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthSouth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .south = 3 := by
    simp [fkIsingSquareWiredBondArcLength, heQ, hnorthQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [2, 2, 0] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthSouth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [7, 7, 5] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7, 7, 5]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [2, 2, 0] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hddirection, hdturn, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
private theorem fkIsingSquareWired_south_vertical_west_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .west := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg he, if_neg hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hwestAvailable : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d) .west := by
    have h := fkIsingSquarePreviousDirection_available n hn
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
      (fkIsingSquareDartDirection_available n d)
    simpa [hprevious] using h
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .west hwestAvailable := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have heQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    simpa [hendpoint] using he
  have hlengthWest : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .west = 5 := by
    simp [fkIsingSquareWiredBondArcLength, hsQ, heQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
      [2, 2, 0, 1, 1] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthWest, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
      [7, 7, 5, 3, 3] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7, 7, 5, 3, 3]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [2, 2, 0, 1, 1] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
    have hprincipal : fkIsingSquareOrientedPrincipalBondTurn n hn d q = -4 := by
      simp only [fkIsingSquareOrientedPrincipalBondTurn, hdnotturn,
        and_false, if_false]
      norm_num [
        fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
        hddirection, hdturn, hqdirection, hqturn,
        FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    simp [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, hprincipal]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

end SouthCoboundaryLeaves

set_option maxHeartbeats 4000000 in
private theorem fkIsingSquareWired_macro_turn_coboundary_south_horizontal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hboundary : (e, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
      fkIsingSquareBondMate n hn (e, .south))
    (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code (e, .south)) +
        fkIsingSquareSignedEighthTurn
          ((code (e, .south)).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (e, .south)))
          ((code (f (e, .south))).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
              (f (e, .south)))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n (e, .south)).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n (e, .south)).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f (e, .south)) -
        fkIsingSquareWiredMacroGauge n hn omega (e, .south) [ZMOD 16] := by
  change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south)
  let u := fkIsingSquareDartEndpoint n (e, .south)
  have he : fkIsingSquareDirectionAvailable n u .east := by
    simpa [u, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .south)
  by_cases hs : fkIsingSquareDirectionAvailable n u .south
  · generalize hstate : omega
        (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
    exact fkIsingSquareWired_south_horizontal_south_leaf
      n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
      hwired hfwd hrev haxis hs state hstate
  · by_cases hw : fkIsingSquareDirectionAvailable n u .west
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_horizontal_west_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis hs hw state hstate
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_horizontal_north_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis hs hw state hstate

set_option maxHeartbeats 4000000 in
private theorem fkIsingSquareWired_macro_turn_coboundary_south_vertical
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hboundary : (e, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
      fkIsingSquareBondMate n hn (e, .south))
    (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code (e, .south)) +
        fkIsingSquareSignedEighthTurn
          ((code (e, .south)).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (e, .south)))
          ((code (f (e, .south))).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
              (f (e, .south)))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n (e, .south)).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n (e, .south)).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f (e, .south)) -
        fkIsingSquareWiredMacroGauge n hn omega (e, .south) [ZMOD 16] := by
  change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south)
  let u := fkIsingSquareDartEndpoint n (e, .south)
  have hnorth : fkIsingSquareDirectionAvailable n u .north := by
    simpa [u, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .south)
  by_cases he : fkIsingSquareDirectionAvailable n u .east
  · generalize hstate : omega
        (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
    exact fkIsingSquareWired_south_vertical_east_leaf
      n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
      hwired hfwd hrev haxis he state hstate
  · by_cases hs : fkIsingSquareDirectionAvailable n u .south
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_vertical_south_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis he hs state hstate
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_vertical_west_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis he hs state hstate

set_option maxHeartbeats 4000000 in

theorem fkIsingSquareWired_macro_turn_coboundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredTerminalDart n hn) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d) +
        fkIsingSquareSignedEighthTurn
          ((code d).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
          ((code (f d)).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (f d))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f d) -
        fkIsingSquareWiredMacroGauge n hn omega d [ZMOD 16] := by
  dsimp only
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      cases homega : omega e.1 <;>
        cases haxis : (fkIsingSquareOrientedEdge n e).axis
      all_goals
        first
        | have hbMate : FKIsingMedialDart.localMate omega (e, .west) =
              (e, .south) := by
            simp [FKIsingMedialDart.localMate, homega]
        | have hbMate : FKIsingMedialDart.localMate omega (e, .west) =
              (e, .north) := by
            simp [FKIsingMedialDart.localMate, homega]
        have hbSide : (FKIsingMedialDart.localMate omega (e, .west)).2 =
            .south ∨ (FKIsingMedialDart.localMate omega (e, .west)).2 =
              .north := by
          rw [hbMate]
          simp
        have hbHead := fkIsingSquareWiredPortMacroCodeWord_head_vertical
          n hn omega (FKIsingMedialDart.localMate omega (e, .west)) hbSide
          hsourceNext hterminalNext
        have hbFst : (FKIsingMedialDart.localMate omega (e, .west)).1 = e :=
          congrArg Prod.fst hbMate
        simp only [hbMate] at hbHead
        rw [hbFst, haxis] at hbHead
        simp only [fkIsingSquareWiredPortNext, hbMate]
        simp only [fkIsingSquareWiredMacroGauge]
        rw [hbHead]
        simp [
          fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredLocalStepIndex,
          fkIsingSquareWiredUnitDiagonalTangentCode,
          fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection,
          fkIsingSquareWiredCarrierTangentCode,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareCornerTangentCode,
          fkIsingSquareDartDirection,
          fkIsingSquareSideCorner,
          FKIsingSquareDirection.eighthTurn,
          fkIsingSquareSignedEighthTurn,
          carrierAdjacentSum, homega, haxis, hbMate, hbHead, Int.ModEq]
  | east =>
      cases homega : omega e.1 <;>
        cases haxis : (fkIsingSquareOrientedEdge n e).axis
      all_goals
        first
        | have hbMate : FKIsingMedialDart.localMate omega (e, .east) =
              (e, .south) := by
            simp [FKIsingMedialDart.localMate, homega]
        | have hbMate : FKIsingMedialDart.localMate omega (e, .east) =
              (e, .north) := by
            simp [FKIsingMedialDart.localMate, homega]
        have hbSide : (FKIsingMedialDart.localMate omega (e, .east)).2 =
            .south ∨ (FKIsingMedialDart.localMate omega (e, .east)).2 =
              .north := by
          rw [hbMate]
          simp
        have hbHead := fkIsingSquareWiredPortMacroCodeWord_head_vertical
          n hn omega (FKIsingMedialDart.localMate omega (e, .east)) hbSide
          hsourceNext hterminalNext
        have hbFst : (FKIsingMedialDart.localMate omega (e, .east)).1 = e :=
          congrArg Prod.fst hbMate
        simp only [hbMate] at hbHead
        rw [hbFst, haxis] at hbHead
        simp only [fkIsingSquareWiredPortNext, hbMate]
        simp only [fkIsingSquareWiredMacroGauge]
        rw [hbHead]
        simp [
          fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredLocalStepIndex,
          fkIsingSquareWiredUnitDiagonalTangentCode,
          fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection,
          fkIsingSquareWiredCarrierTangentCode,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareCornerTangentCode,
          fkIsingSquareDartDirection,
          fkIsingSquareSideCorner,
          FKIsingSquareDirection.eighthTurn,
          fkIsingSquareSignedEighthTurn,
          carrierAdjacentSum, homega, haxis, hbMate, hbHead, Int.ModEq]
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early n hn e h)
      have hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
          fkIsingSquareBondMate n hn (e, .south) :=
        fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn (e, .south) hboundary
      have hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
          (fkIsingSquareBondMate n hn (e, .south)) := by
        rintro (⟨hd, _⟩ | ⟨k, hd, _⟩)
        · exact hsource hd
        · have hs := congrArg Prod.snd hd
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hs
      have hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
          (fkIsingSquareBondMate n hn (e, .south)) := by
        rw [fkIsingSquareWiredBoundaryReverse]
        rintro (⟨_, hd⟩ | ⟨k, _, hd⟩)
        · exact hterminal hd
        · have hs := congrArg Prod.snd hd
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hs
      cases haxis : (fkIsingSquareOrientedEdge n e).axis
      · exact fkIsingSquareWired_macro_turn_coboundary_south_horizontal
          n hn omega e hsource hterminal hsourceNext hterminalNext
          hboundary hwired hfwd hrev haxis
      · exact fkIsingSquareWired_macro_turn_coboundary_south_vertical
          n hn omega e hsource hterminal hsourceNext hterminalNext
          hboundary hwired hfwd hrev haxis
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          let d := fkIsingSquareWiredBoundaryDart n hn (.north k)
          let q := fkIsingSquareWiredBoundaryDart n hn (.west k)
          change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega d
          have hdsource : d ≠ fkIsingSquareWiredSourceDart n hn := by
            intro h
            exact hsource (hk.trans h)
          have hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
            intro h
            exact hterminal (hk.trans h)
          have hdside : d.2 = .north := by
            simp [d, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hqside : q.2 = .west := by
            simp [q, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hdRange : d ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
            change fkIsingSquareWiredBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
                fkIsingSquareWiredBoundaryDart n hn (.west k)
            exact fkIsingSquareWiredBondMate_north n hn k
          have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
              [3, 5, 7] := by
            simp [d, fkIsingSquareWiredPortMacroCodeWord,
              fkIsingSquareWiredPortMacroStepWord,
              hdside, hdRange,
              fkIsingSquareWiredBulgeReverseStepWord,
              fkIsingSquareWiredUnitDiagonalTangentCode]
          have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d q := by
            apply fkIsingSquareWiredBoundaryForward_asymm n hn
            exact (show fkIsingSquareWiredBoundaryForward n hn q d from
              Or.inr ⟨k, rfl, rfl⟩)
          have hrev : fkIsingSquareWiredBoundaryReverse n hn d q := by
            simpa [fkIsingSquareWiredBoundaryReverse] using
              (show fkIsingSquareWiredBoundaryForward n hn q d from
                Or.inr ⟨k, rfl, rfl⟩)
          have htransition : fkIsingSquareWiredTransitionTurn n hn omega
              (fkIsingSquareWiredBlackOfDart n d).1
              (fkIsingSquareWiredTransitionMate n hn omega
                (fkIsingSquareWiredBlackOfDart n d).1) = 6 := by
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              rcases d with ⟨de, side⟩
              cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
            have hmate : fkIsingSquareWiredTransitionMate n hn omega
                (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
              rw [hblackD]
              simp [fkIsingSquareWiredTransitionMate, hdsource, hdterminal,
                d, q]
            rw [hmate, hblackD]
            simp [fkIsingSquareWiredTransitionTurn,
              fkIsingSquareWiredBondTurn, hfwd, hrev]
          have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
            rcases d with ⟨de, side⟩
            cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
          have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
              (fkIsingSquareWiredBlackOfDart n d).1 = 15 := by
            rw [hblackD]
            simpa [d] using
              fkIsingSquareWiredDirectedTangentCode_boundaryDart n hn (.north k)
          have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
            simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
              fkIsingSquareSignedEighthTurn]
          have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
            rcases q with ⟨qe, side⟩
            cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
          have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
              (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
            rw [hblackQ]
            simp [q,
              fkIsingSquareWiredDirectedTangentCode,
              fkIsingSquareWiredObservationCorrection,
              fkIsingSquareWiredCarrierTangentCode,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareCornerTangentCode,
              FKIsingSquareDirection.eighthTurn]
          generalize hstate : omega q.1.1 = state
          cases state with
          | false =>
              have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q =
                  [7] := by
                simp [q, fkIsingSquareWiredPortMacroCodeWord,
                  fkIsingSquareWiredPortMacroStepWord,
                  hqside, fkIsingSquareWiredLocalStepIndex, hstate,
                  fkIsingSquareWiredUnitDiagonalTangentCode]
              have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                  fkIsingSquareSignedEighthTurn]
              simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
                hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                fkIsingSquareSignedEighthTurn, Int.ModEq]
          | true =>
              have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q =
                  [1] := by
                simp [q, fkIsingSquareWiredPortMacroCodeWord,
                  fkIsingSquareWiredPortMacroStepWord,
                  hqside, fkIsingSquareWiredLocalStepIndex, hstate,
                  fkIsingSquareWiredUnitDiagonalTangentCode]
              have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                  fkIsingSquareSignedEighthTurn]
              simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
                hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                fkIsingSquareSignedEighthTurn, Int.ModEq]
      · let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .north)
        change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega d
        set q := fkIsingSquareBondMate n hn d with hqdef
        have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
          simp [d, fkIsingSquareSideCorner]
        have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 =
            .counterclockwise := by
          rw [hdturn]
          decide
        have hqturn : (fkIsingSquareSideCorner q.2).2 =
            .counterclockwise := by
          simp [hqdef, fkIsingSquareBondMate, hdturn]
        have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
          simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
        have hendpoint : fkIsingSquareDartEndpoint n q =
            fkIsingSquareDartEndpoint n d := by
          simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
        have hwired : fkIsingSquareWiredBondMate n hn d = q := by
          calc
            _ = fkIsingSquareBondMate n hn d :=
              fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
                n hn d (by simpa [d] using hboundary)
            _ = q := hqdef.symm
        have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
          simp [d, fkIsingSquareWiredPortNext, hwired]
        have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d q := by
          rintro (⟨hd, _⟩ | ⟨k, hd, _⟩)
          · exact hsource (by simpa [d] using hd)
          · have hs := congrArg Prod.snd hd
            simp [d, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d q := by
          rw [fkIsingSquareWiredBoundaryReverse]
          rintro (⟨_, hd⟩ | ⟨k, _, hd⟩)
          · exact hterminal (by simpa [d] using hd)
          · apply hboundary
            exact ⟨.north k, by simpa [d] using hd.symm⟩
        have hmate : fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
          simp [d, fkIsingSquareWiredBlackOfDart,
            fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
        cases haxis : (fkIsingSquareOrientedEdge n e).axis with
        | horizontal =>
            have hddirection : fkIsingSquareDartDirection n d = .west := by
              simp [d, fkIsingSquareDartDirection,
                fkIsingSquareSideCorner, haxis]
            have hwest : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .west := by
              simpa [hddirection] using fkIsingSquareDartDirection_available n d
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              simp [d, fkIsingSquareWiredBlackOfDart]
            have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
                (fkIsingSquareWiredBlackOfDart n d).1 = 13 := by
              rw [hblackD]
              norm_num [fkIsingSquareWiredDirectedTangentCode,
                fkIsingSquareWiredObservationCorrection,
                fkIsingSquareWiredCarrierTangentCode,
                fkIsingSquareCornerTangentCode, hddirection, hdturn,
                FKIsingSquareDirection.eighthTurn]
            by_cases hnorth : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .north
            · have hprevious : fkIsingSquarePreviousDirection n
                  (fkIsingSquareDartEndpoint n d)
                    (fkIsingSquareDartDirection n d) = .north := by
                simp [hddirection, fkIsingSquarePreviousDirection, hnorth]
              have hqdirection : fkIsingSquareDartDirection n q = .north := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
              have hqside : q.2 = .west := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                  fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
                  fkIsingSquareCornerSide]
              have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
                simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                  fkIsingSquareWiredPortSlot]
              have hwestQ : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n q) .west := by
                simpa [hendpoint] using hwest
              have hlength : fkIsingSquareWiredBondArcLength n
                  (fkIsingSquareDartEndpoint n q) .north = 1 := by
                simp [fkIsingSquareWiredBondArcLength, hwestQ]
              have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                  [3] := by
                simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                  hbase, hqdirection, hqslot, hdnotturn, if_false]
                simp [hlength, List.ofFn_succ,
                  fkIsingSquareWiredRingStepIndex,
                  fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
              have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                  [1] := by
                change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                  fkIsingSquareWiredUnitDiagonalTangentCode = [1]
                have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                    [3] := by
                  simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                    using hstepD
                rw [hm]
                rfl
              have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                  fkIsingSquareSignedEighthTurn]
              have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
                rcases q with ⟨qe, side⟩
                cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
              have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                  (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
                rw [hblackQ]
                norm_num [fkIsingSquareWiredDirectedTangentCode,
                  fkIsingSquareWiredObservationCorrection,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                  FKIsingSquareDirection.eighthTurn]
              have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                  (fkIsingSquareWiredBlackOfDart n d).1
                  (fkIsingSquareWiredTransitionMate n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
                rw [hmate, hblackD]
                norm_num [fkIsingSquareWiredTransitionTurn,
                  fkIsingSquareWiredBondTurn, hfwd, hrev,
                  fkIsingSquareOrientedPrincipalBondTurn,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hddirection, hdturn,
                  hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                  fkIsingSquareSignedEighthTurn]
              clear hqdef
              generalize hstate : omega q.1.1 = state
              cases state with
              | false =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [7] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      10 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
              | true =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [1] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -4 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
            · by_cases heast : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n d) .east
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .east := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hnorth, heast]
                have hqdirection : fkIsingSquareDartDirection n q = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hwestQ : fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .east = 3 := by
                  simp [fkIsingSquareWiredBondArcLength, hnorthQ, hwestQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [3, 2, 2] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [1, 7, 7] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [1, 7, 7]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [3, 2, 2] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
                  rw [hmate, hblackD]
                  norm_num [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev,
                    fkIsingSquareOrientedPrincipalBondTurn,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hddirection, hdturn,
                    hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                    fkIsingSquareSignedEighthTurn]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -2 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .south := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hnorth, heast]
                have hqdirection : fkIsingSquareDartDirection n q = .south := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have heastQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .east := by
                  simpa [hendpoint] using heast
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .south = 5 := by
                  simp [fkIsingSquareWiredBondArcLength, heastQ, hnorthQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [3, 2, 2, 2, 0] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [1, 7, 7, 7, 5] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [1, 7, 7, 7, 5]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [3, 2, 2, 2, 0] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
                  have hprincipal : fkIsingSquareOrientedPrincipalBondTurn
                      n hn d q = -4 := by
                    simp only [fkIsingSquareOrientedPrincipalBondTurn,
                      hdnotturn, and_false, if_false]
                    norm_num [fkIsingSquareWiredCarrierTangentCode,
                      fkIsingSquareCornerTangentCode, hddirection, hdturn,
                      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                      fkIsingSquareSignedEighthTurn]
                  rw [hmate, hblackD]
                  simp [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev, hprincipal]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [3] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        10 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [5] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
        | vertical =>
            have hddirection : fkIsingSquareDartDirection n d = .south := by
              simp [d, fkIsingSquareDartDirection,
                fkIsingSquareSideCorner, haxis]
            have hsouth : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .south := by
              simpa [hddirection] using fkIsingSquareDartDirection_available n d
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              simp [d, fkIsingSquareWiredBlackOfDart]
            have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
                (fkIsingSquareWiredBlackOfDart n d).1 = 15 := by
              rw [hblackD]
              norm_num [fkIsingSquareWiredDirectedTangentCode,
                fkIsingSquareWiredObservationCorrection,
                fkIsingSquareWiredCarrierTangentCode,
                fkIsingSquareCornerTangentCode, hddirection, hdturn,
                FKIsingSquareDirection.eighthTurn]
            by_cases hwest : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .west
            · have hprevious : fkIsingSquarePreviousDirection n
                  (fkIsingSquareDartEndpoint n d)
                    (fkIsingSquareDartDirection n d) = .west := by
                simp [hddirection, fkIsingSquarePreviousDirection, hwest]
              have hqdirection : fkIsingSquareDartDirection n q = .west := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
              have hqside : q.2 = .east := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                  fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
                  fkIsingSquareCornerSide]
              have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
                simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                  fkIsingSquareWiredPortSlot]
              have hsouthQ : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n q) .south := by
                simpa [hendpoint] using hsouth
              have hlength : fkIsingSquareWiredBondArcLength n
                  (fkIsingSquareDartEndpoint n q) .west = 1 := by
                simp [fkIsingSquareWiredBondArcLength, hsouthQ]
              have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                  [1] := by
                simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                  hbase, hqdirection, hqslot, hdnotturn, if_false]
                simp [hlength, List.ofFn_succ,
                  fkIsingSquareWiredRingStepIndex,
                  fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
              have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                  [3] := by
                change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                  fkIsingSquareWiredUnitDiagonalTangentCode = [3]
                have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                    [1] := by
                  simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                    using hstepD
                rw [hm]
                rfl
              have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                  fkIsingSquareSignedEighthTurn]
              have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
                rcases q with ⟨qe, side⟩
                cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
              have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                  (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
                rw [hblackQ]
                norm_num [fkIsingSquareWiredDirectedTangentCode,
                  fkIsingSquareWiredObservationCorrection,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                  FKIsingSquareDirection.eighthTurn]
              have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                  (fkIsingSquareWiredBlackOfDart n d).1
                  (fkIsingSquareWiredTransitionMate n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
                rw [hmate, hblackD]
                norm_num [fkIsingSquareWiredTransitionTurn,
                  fkIsingSquareWiredBondTurn, hfwd, hrev,
                  fkIsingSquareOrientedPrincipalBondTurn,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hddirection, hdturn,
                  hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                  fkIsingSquareSignedEighthTurn]
              clear hqdef
              generalize hstate : omega q.1.1 = state
              cases state with
              | false =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [3] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -4 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
              | true =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [5] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -2 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
            · by_cases hnorth : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n d) .north
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .north := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hwest, hnorth]
                have hqdirection : fkIsingSquareDartDirection n q = .north := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hwestQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hsouthQ : fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .south := by
                  simpa [hendpoint] using hsouth
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .north = 3 := by
                  simp [fkIsingSquareWiredBondArcLength, hwestQ, hsouthQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [1, 1, 3] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [3, 3, 1] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [3, 3, 1]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [1, 1, 3] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
                  rw [hmate, hblackD]
                  norm_num [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev,
                    fkIsingSquareOrientedPrincipalBondTurn,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hddirection, hdturn,
                    hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                    fkIsingSquareSignedEighthTurn]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        10 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .east := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hwest, hnorth]
                have hqdirection : fkIsingSquareDartDirection n q = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hwestQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .east = 5 := by
                  simp [fkIsingSquareWiredBondArcLength, hnorthQ, hwestQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [1, 1, 3, 2, 2] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [3, 3, 1, 7, 7] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [3, 3, 1, 7, 7]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [1, 1, 3, 2, 2] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
                  have hprincipal : fkIsingSquareOrientedPrincipalBondTurn
                      n hn d q = -4 := by
                    simp only [fkIsingSquareOrientedPrincipalBondTurn,
                      hdnotturn, and_false, if_false]
                    norm_num [fkIsingSquareWiredCarrierTangentCode,
                      fkIsingSquareCornerTangentCode, hddirection, hdturn,
                      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                      fkIsingSquareSignedEighthTurn]
                  rw [hmate, hblackD]
                  simp [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev, hprincipal]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -2 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]

private theorem List.head_flatMap_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    (l.flatMap code).head (by
      cases l <;> simp_all [hcode]) = (code (l.head hl)).head (hcode _) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a tail => simp [List.head_append, hcode]

private theorem List.getLast_flatMap_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    (l.flatMap code).getLast (by
      cases l <;> simp_all [hcode]) =
      (code (l.getLast hl)).getLast (hcode _) := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp [hcode]
      | cons b tail =>
          have htail : b :: tail ≠ [] := by simp
          have hright : (b :: tail).flatMap code ≠ [] := by
            simp [hcode]
          calc
            ((a :: b :: tail).flatMap code).getLast _ =
                ((b :: tail).flatMap code).getLast hright := by
              simpa only [List.flatMap_cons] using
                List.getLast_append_of_right_ne_nil (code a)
                  ((b :: tail).flatMap code) hright
            _ = (code ((a :: b :: tail).getLast hl)).getLast (hcode _) := by
              simpa using ih htail

private theorem List.flatMap_ne_nil_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    l.flatMap code ≠ [] := by
  intro hnil
  rw [List.flatMap_eq_nil_iff] at hnil
  exact hcode (l.head hl) (hnil _ (List.head_mem hl))




theorem fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (darts : List (FKIsingMedialDart (fkSquareBoxPlanar n)))
    (hdarts : darts ≠ [])
    (hsource : ∀ d ∈ darts, d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ d ∈ darts, d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : ∀ d ∈ darts,
      fkIsingSquareWiredPortNext n hn omega d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : ∀ d ∈ darts,
      fkIsingSquareWiredPortNext n hn omega d ≠
        fkIsingSquareWiredTerminalDart n hn)
    (hchain : darts.Chain' fun d e =>
      e = fkIsingSquareWiredPortNext n hn omega d)
    (hclose : fkIsingSquareWiredPortNext n hn omega
        (darts.getLast hdarts) = darts.head hdarts) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let word := darts.flatMap code
    carrierAdjacentSum fkIsingSquareSignedEighthTurn word +
        fkIsingSquareSignedEighthTurn
          (word.getLast (List.flatMap_ne_nil_of_ne_nil code
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
            darts hdarts))
          (word.head (List.flatMap_ne_nil_of_ne_nil code
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
            darts hdarts)) ≡
      (darts.map fun d => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1)).sum [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let internal := fun d =>
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d)
  let boundary := fun d e => fkIsingSquareSignedEighthTurn
    ((code d).getLast (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
    ((code e).head (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega e))
  let transition := fun d => fkIsingSquareWiredTransitionTurn n hn omega
    (fkIsingSquareWiredBlackOfDart n d).1
    (fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1)
  let gauge := fkIsingSquareWiredMacroGauge n hn omega
  let block := fun d => internal d + boundary d (f d)
  let rhs := fun d => transition d + gauge (f d) - gauge d
  have hcode : ∀ d, code d ≠ [] :=
    fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
  have hflat := carrierAdjacentSum_flatMap
    fkIsingSquareSignedEighthTurn code hcode darts
  change carrierAdjacentSum fkIsingSquareSignedEighthTurn
      (darts.flatMap code) = carrierAdjacentSum boundary darts +
        (darts.map internal).sum at hflat
  have hhead := List.head_flatMap_of_ne_nil code hcode darts hdarts
  have hlast := List.getLast_flatMap_of_ne_nil code hcode darts hdarts
  have hboundaryChain : darts.Chain' fun d e =>
      boundary d e = boundary d (f d) := by
    apply hchain.imp
    intro d e he
    subst e
    rfl
  have hboundaryCarrier :
      carrierAdjacentSum boundary darts =
        carrierAdjacentSum (fun d _ => boundary d (f d)) darts :=
    carrierAdjacentSum_chain_congr boundary
      (fun d _ => boundary d (f d)) darts hboundaryChain
  have hboundarySum :
      carrierAdjacentSum boundary darts +
          boundary (darts.getLast hdarts) (darts.head hdarts) =
        (darts.map fun d => boundary d (f d)).sum := by
    rw [hboundaryCarrier]
    have h := carrierAdjacentSum_fst_add_last_eq_sum
      (fun d => boundary d (f d)) darts hdarts
    simpa [f, hclose] using h
  have hblockSplit :
      (darts.map block).sum =
        (darts.map internal).sum +
          (darts.map fun d => boundary d (f d)).sum := by
    simpa [block] using
      (List.sum_map_add (l := darts) (f := internal)
        (g := fun d => boundary d (f d)))
  have hcyclic :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast
            (List.flatMap_ne_nil_of_ne_nil code hcode darts hdarts))
          ((darts.flatMap code).head
            (List.flatMap_ne_nil_of_ne_nil code hcode darts hdarts)) =
        (darts.map block).sum := by
    rw [hflat, hhead, hlast, hblockSplit, ← hboundarySum]
    simp only [boundary]
    omega
  have hblock (d) (hd : d ∈ darts) : block d ≡ rhs d [ZMOD 16] := by
    simpa [block, rhs, internal, boundary, transition, gauge, f, code]
      using fkIsingSquareWired_macro_turn_coboundary n hn omega d
        (hsource d hd) (hterminal d hd)
        (hsourceNext d hd) (hterminalNext d hd)
  have hblocks : (darts.map block).sum ≡
      (darts.map rhs).sum [ZMOD 16] :=
    List.sum_map_modEq darts 16 hblock
  have hgaugeChain : darts.Chain' fun d e => gauge (f d) = gauge e := by
    apply hchain.imp
    intro d e he
    subst e
    rfl
  have hgaugeCarrier :
      carrierAdjacentSum (fun d _ => gauge (f d)) darts =
        carrierAdjacentSum (fun _ e => gauge e) darts :=
    carrierAdjacentSum_chain_congr (fun d _ => gauge (f d))
      (fun _ e => gauge e) darts hgaugeChain
  have hgaugeSum : (darts.map fun d => gauge (f d)).sum =
      (darts.map gauge).sum := by
    calc
      _ = carrierAdjacentSum (fun d _ => gauge (f d)) darts +
          gauge (f (darts.getLast hdarts)) :=
        (carrierAdjacentSum_fst_add_last_eq_sum
          (fun d => gauge (f d)) darts hdarts).symm
      _ = carrierAdjacentSum (fun _ e => gauge e) darts +
          gauge (darts.head hdarts) := by
        rw [hgaugeCarrier]
        rw [show f (darts.getLast hdarts) = darts.head hdarts by
          simpa [f] using hclose]
      _ = _ := carrierAdjacentSum_snd_add_head_eq_sum gauge darts hdarts
  have hrhsSplit : (darts.map rhs).sum =
      (darts.map transition).sum +
        (darts.map fun d => gauge (f d)).sum -
          (darts.map gauge).sum := by
    simpa [rhs] using List.sum_map_add_sub darts transition
      (fun d => gauge (f d)) gauge
  have hrhs : (darts.map rhs).sum = (darts.map transition).sum := by
    rw [hrhsSplit, hgaugeSum]
    omega
  calc
    _ = (darts.map block).sum := hcyclic
    _ ≡ (darts.map rhs).sum [ZMOD 16] := hblocks
    _ = (darts.map transition).sum := hrhs


theorem fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat) (hk : 0 < k)
    (hclose : (fkIsingSquareWiredPortNext n hn omega)^[k] d = d)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let word := darts.flatMap code
    carrierAdjacentSum fkIsingSquareSignedEighthTurn word +
        fkIsingSquareSignedEighthTurn
          (word.getLast (by
            exact List.flatMap_ne_nil_of_ne_nil code
              (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
              darts (by simp [darts, hk.ne'])))
          (word.head (by
            exact List.flatMap_ne_nil_of_ne_nil code
              (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
              darts (by simp [darts, hk.ne']))) ≡
      (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1)).sum [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let darts := List.iterate f d k
  have hdarts : darts ≠ [] := by simp [darts, hk.ne']
  have hsourceMem : ∀ q ∈ darts,
      q ≠ fkIsingSquareWiredSourceDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    exact hsource i (by simpa [darts] using hi)
  have hterminalMem : ∀ q ∈ darts,
      q ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    exact hterminal i (by simpa [darts] using hi)
  have hsourceNextMem : ∀ q ∈ darts,
      f q ≠ fkIsingSquareWiredSourceDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    rw [show f (f^[i] d) = f^[i + 1] d by
      simpa [Function.iterate_succ_apply']]
    by_cases hnext : i + 1 < k
    · exact hsource (i + 1) hnext
    · have hik : i + 1 = k := by
        have hi' : i < k := by simpa [darts] using hi
        omega
      rw [hik, hclose]
      exact hsource 0 hk
  have hterminalNextMem : ∀ q ∈ darts,
      f q ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    rw [show f (f^[i] d) = f^[i + 1] d by
      simpa [Function.iterate_succ_apply']]
    by_cases hnext : i + 1 < k
    · exact hterminal (i + 1) hnext
    · have hik : i + 1 = k := by
        have hi' : i < k := by simpa [darts] using hi
        omega
      rw [hik, hclose]
      exact hterminal 0 hk
  have hchain : darts.Chain' fun q r => r = f q := by
    exact List.chain'_iterate f d k
  have hlast : f (darts.getLast hdarts) = darts.head hdarts := by
    have hgetLast : darts.getLast hdarts = f^[k - 1] d := by
      dsimp only [darts]
      rw [List.getLast_eq_getElem, List.getElem_iterate]
      simp
    have hhead : darts.head hdarts = d := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rfl
    rw [hgetLast, hhead]
    have hkEq : 1 + (k - 1) = k := by omega
    calc
      f (f^[k - 1] d) = f^[1] (f^[k - 1] d) := rfl
      _ = f^[1 + (k - 1)] d :=
        (Function.iterate_add_apply f 1 (k - 1) d).symm
      _ = f^[k] d := by rw [hkEq]
      _ = d := hclose
  exact fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen n hn omega
    darts hdarts hsourceMem hterminalMem hsourceNextMem hterminalNextMem
    hchain hlast




















































































































































































private theorem carrierAdjacentSum_ofFn
    {A : Type*} (turn : A → A → Int)
    {m : Nat} (a : Fin (m + 1) → A) :
    carrierAdjacentSum turn (List.ofFn a) =
      ∑ i : Fin m, turn (a i.castSucc) (a ⟨i.val + 1, by omega⟩) := by
  unfold carrierAdjacentSum
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    cases i <;> simp [List.getElem_zipWith]


private theorem carrierAdjacentSum_add_closing_eq_fin_sum
    {A : Type*} (turn : A → A → Int)
    {m : Nat} [NeZero m] (a : Fin m → A) :
    carrierAdjacentSum turn (List.ofFn a) +
        turn ((List.ofFn a).getLast (by simpa using (NeZero.ne m)))
          ((List.ofFn a).head (by simpa using (NeZero.ne m))) =
      ∑ i : Fin m, turn (a i) (a (i + 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  rw [Fin.sum_univ_castSucc, carrierAdjacentSum_ofFn,
    List.getLast_ofFn_succ]
  simp
  apply Finset.sum_congr rfl
  intro i _
  congr 2

theorem fkIsingSquareWiredBoundaryEmbedding_south_eq_source
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .south) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .south) = fkIsingSquareWiredSourceDart n hn := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom =>
      simpa [fkIsingSquareWiredSourceDart] using hi.symm
  | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | top =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs

theorem fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .north) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .north) = fkIsingSquareWiredTerminalDart n hn ∨
      ∃ k : Fin (2 * n),
        (e, .north) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k =>
      exact Or.inr ⟨k, hi.symm⟩
  | top =>
      exact Or.inl (by
        simpa [fkIsingSquareWiredTerminalDart] using hi.symm)




theorem fkIsingSquareWiredExpandedGraph_reachable_portNext
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareWiredPortNext n hn omega d))) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      exact (show (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) from
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩).reachable
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      exact (show (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) from
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩).reachable
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · obtain ⟨i, hi⟩ := hboundary
        cases i with
        | bottom =>
            exact False.elim (hsource (by simpa
              [fkIsingSquareWiredSourceDart] using hi.symm))
        | west k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | north k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | top =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
            n hn omega (e, .south) hleft (by simp [fkIsingSquareSideCorner])
              hboundary
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
            n hn omega (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · obtain ⟨i, hi⟩ := hboundary
        cases i with
        | bottom =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | west k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | north k =>
            rw [← hi]
            change (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredBoundaryDart n hn (.north k))))
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega
                  (fkIsingSquareWiredBoundaryDart n hn (.north k)))))
            have hnext : fkIsingSquareWiredPortNext n hn omega
                (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
              simpa only [fkIsingSquareWiredPortNext,
                fkIsingSquareWiredBoundaryDart,
                fkIsingSquareDirectionDart,
                fkIsingSquareEndpointForDirection,
                fkIsingSquareCornerSide] using
                  fkIsingSquareWiredBondMate_north n hn k
            rw [hnext]
            simpa [
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot] using
                (fkIsingSquareWiredExpandedGraph_reachable_bulge
                  n hn omega k).symm
        | top =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
            n hn omega (e, .north) hleft (by simp [fkIsingSquareSideCorner])
              hboundary
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
            n hn omega (e, .north) hleft




theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧ ¬p.Nil := by
  obtain ⟨w⟩ := fkIsingSquareWiredExpandedGraph_reachable_portNext
    n hn omega d hsource hterminal
  refine ⟨w.toPath, w.toPath.isPath, ?_⟩
  intro hnil
  have hend :
      (.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n) =
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d)) := hnil.eq
  have hslot := Sum.inl.inj hend
  have hd := fkIsingSquareWiredDartSlot_injective n hslot
  exact fkIsingSquareWiredPortNext_ne n hn omega d hd.symm


theorem fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .west)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, Or.inl rfl⟩
      rw [SimpleGraph.Walk.isPath_def]
      change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
      simp [hne, hne.symm]
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .east)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, Or.inl rfl⟩
      rw [SimpleGraph.Walk.isPath_def]
      change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
      simp [hne, hne.symm]
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · exact False.elim (hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source
            n hn e hboundary))
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · let h :=
            fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
              n hn omega (e, .south) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
          let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
          have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .south)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
              .inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareBondMate n hn (e, .south))) := by
            intro heq
            exact fkIsingSquareBondMate_ne n hn (e, .south)
              (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
          refine ⟨p, ?_, Or.inl rfl⟩
          rw [SimpleGraph.Walk.isPath_def]
          change [(.inl (fkIsingSquareWiredDartSlot n (e, .south)) :
              FKIsingSquareWiredExpandedCarrier n),
            .inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn (e, .south)))].Nodup
          simp [hne, hne.symm]
        · exact fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
            n hn omega (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext : fkIsingSquareWiredPortNext n hn omega
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
            fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa only [fkIsingSquareWiredPortNext,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] using
                fkIsingSquareWiredBondMate_north n hn k
          obtain ⟨p, hp, hlen, _, _⟩ :=
            fkIsingSquareWiredExpandedGraph_exists_path_bulge n hn omega k
          rw [hnext]
          have hstart : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.north k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedEnd n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          have hend : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.west k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedStart n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          let q := p.reverse.copy hstart.symm hend.symm
          exact ⟨q, by simpa [q] using hp.reverse, by simp [q, hlen]⟩
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · let h :=
            fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
              n hn omega (e, .north) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
          let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
          have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .north)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
              .inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareBondMate n hn (e, .north))) := by
            intro heq
            exact fkIsingSquareBondMate_ne n hn (e, .north)
              (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
          refine ⟨p, ?_, Or.inl rfl⟩
          rw [SimpleGraph.Walk.isPath_def]
          change [(.inl (fkIsingSquareWiredDartSlot n (e, .north)) :
              FKIsingSquareWiredExpandedCarrier n),
            .inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn (e, .north)))].Nodup
          simp [hne, hne.symm]
        · exact fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
            n hn omega (e, .north) hleft



theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hdifferent : d.2 = .west ∨ d.2 = .east →
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) ≠
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d)))) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .west)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
        simp [hne, hne.symm]
      simpa [p, fkIsingSquareWiredPortNext] using
        hdifferent (Or.inl rfl)
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .east)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
        simp [hne, hne.symm]
      simpa [p, fkIsingSquareWiredPortNext] using
        hdifferent (Or.inr rfl)
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · exact False.elim (hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source
            n hn e hboundary))
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
              n hn omega localDart (e, .south) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
              n hn omega localDart (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext : fkIsingSquareWiredPortNext n hn omega
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
            fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa only [fkIsingSquareWiredPortNext,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] using
                fkIsingSquareWiredBondMate_north n hn k
          obtain ⟨p, hp, hav⟩ :=
            fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local
              n hn omega localDart k
          rw [hnext]
          have hstart : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.north k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedEnd n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          have hend : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.west k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedStart n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          let q := p.reverse.copy hstart.symm hend.symm
          exact ⟨q, by simpa [q] using hp.reverse, by simpa [q] using hav⟩
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
              n hn omega localDart (e, .north) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
              n hn omega localDart (e, .north) hleft

theorem fkIsingSquareWired_local_edge_eq_iff_start_or_mate
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d localDart : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)))) :
    d = localDart ∨ d = FKIsingMedialDart.localMate omega localDart := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · left
    apply fkIsingSquareWiredDartSlot_injective n
    exact Sum.inl.inj h.1.symm
  · right
    apply fkIsingSquareWiredDartSlot_injective n
    exact Sum.inl.inj h.2.symm



theorem fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d))),
      k ≤ p.length := by
  let f := fkIsingSquareWiredPortNext n hn omega
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n (f^[k] d))), k ≤ p.length
  induction k generalizing d with
  | zero =>
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      obtain ⟨m, _, hmLen⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path
          n hn omega d hdSource hdTerminal
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      obtain ⟨q, hqLen⟩ := ih (f d) hsource' hterminal'
      have hmPos : 1 ≤ m.length := by
        rcases hmLen with h | h | h <;> omega
      refine ⟨m.append q, ?_⟩
      rw [SimpleGraph.Walk.length_append]
      calc
        Nat.succ k = k + 1 := by omega
        _ ≤ q.length + 1 := Nat.add_le_add_right hqLen 1
        _ ≤ q.length + m.length := Nat.add_le_add_left hmPos q.length
        _ = m.length + q.length := Nat.add_comm _ _



theorem fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn)
    (hdifferent : ∀ i < k,
      let q := (fkIsingSquareWiredPortNext n hn omega)^[i] d
      (q.2 = .west ∨ q.2 = .east) →
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ≠
        s((.inl (fkIsingSquareWiredDartSlot n q) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareWiredPortNext n hn omega q)))) :
    ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges
      {s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart)))}).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        ((fkIsingSquareWiredPortNext n hn omega)^[k] d))) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let c : Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
    s(.inl (fkIsingSquareWiredDartSlot n localDart),
      .inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega localDart)))
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change ∀ i < k, let q := f^[i] d
    (q.2 = .west ∨ q.2 = .east) → c ≠
      s(.inl (fkIsingSquareWiredDartSlot n q),
        .inl (fkIsingSquareWiredDartSlot n (f q))) at hdifferent
  change ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges {c}).Reachable
    (.inl (fkIsingSquareWiredDartSlot n d))
    (.inl (fkIsingSquareWiredDartSlot n (f^[k] d)))
  induction k generalizing d with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      obtain ⟨p, _, hpAvoid⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local
          n hn omega localDart d hdSource hdTerminal
            (hdifferent 0 (Nat.zero_lt_succ k))
      have hpDelete : ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges
          {c}).Walk (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n (f d))) :=
        p.toDeleteEdges {c} (by
          intro edge hedge hedgeC
          simp only [Set.mem_singleton_iff] at hedgeC
          subst edge
          exact hpAvoid hedge)
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      have hdifferent' : ∀ i < k, let q := f^[i] (f d)
          (q.2 = .west ∨ q.2 = .east) → c ≠
            s(.inl (fkIsingSquareWiredDartSlot n q),
              .inl (fkIsingSquareWiredDartSlot n (f q))) := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hdifferent (i + 1) (by omega)
      exact hpDelete.reachable.trans
        (ih (f d) hsource' hterminal' hdifferent')



theorem fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredBlackBoundaryPerm n hn omega
        (fkIsingSquareWiredBlackOfDart n d) =
      fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredPortNext n hn omega d) := by
  apply Subtype.ext
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      cases homega : omega e.1 <;>
        simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredPortNext, FKIsingMedialDart.localMate, homega]
  | east =>
      cases homega : omega e.1 <;>
        simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredPortNext, FKIsingMedialDart.localMate, homega]
  | south =>
      generalize hmate : fkIsingSquareWiredBondMate n hn (e, .south) = f
      have hturn := fkIsingSquareWiredBondMate_turn_ne n hn (e, .south)
      rw [hmate] at hturn
      rcases f with ⟨f, side⟩
      cases side
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareSideCorner] at hturn
      · simp [fkIsingSquareSideCorner] at hturn
  | north =>
      generalize hmate : fkIsingSquareWiredBondMate n hn (e, .north) = f
      have hturn := fkIsingSquareWiredBondMate_turn_ne n hn (e, .north)
      rw [hmate] at hturn
      rcases f with ⟨f, side⟩
      cases side
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareSideCorner] at hturn
      · simp [fkIsingSquareSideCorner] at hturn



theorem fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega ^ k)
        (fkIsingSquareWiredBlackOfDart n d) =
      fkIsingSquareWiredBlackOfDart n
        ((fkIsingSquareWiredPortNext n hn omega)^[k] d) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change (sigma ^ k) (fkIsingSquareWiredBlackOfDart n d) =
    fkIsingSquareWiredBlackOfDart n (f^[k] d)
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      rw [pow_succ]
      change (sigma ^ k) (sigma (fkIsingSquareWiredBlackOfDart n d)) = _
      rw [show sigma (fkIsingSquareWiredBlackOfDart n d) =
          fkIsingSquareWiredBlackOfDart n (f d) from
        fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
          n hn omega d hdSource hdTerminal]
      simpa [Function.iterate_succ_apply] using ih (f d) hsource' hterminal'



theorem fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    ∀ i,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
          fkIsingSquareWiredSourceDart n hn ∧
        (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
          fkIsingSquareWiredTerminalDart n hn := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  have hsourceToCarrier :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredSourceDart n hn)).1 .source := by
    have hblack : (fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredSourceDart n hn)).1 =
        .bond (fkIsingSquareWiredSourceDart n hn) := by
      simp [fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide]
    apply SimpleGraph.Adj.reachable
    rw [hblack]
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    left
    simp [fkIsingSquareWiredTransitionEquiv,
      fkIsingSquareWiredTransitionMate]
  have hterminalToSource :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredTerminalDart n hn)).1 .source := by
    have hblack : (fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredTerminalDart n hn)).1 =
        .dart (fkIsingSquareWiredTerminalDart n hn) := by
      simp [fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTerminalDart,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide]
    have hincidence :
        (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (fkIsingSquareWiredBlackOfDart n
            (fkIsingSquareWiredTerminalDart n hn)).1
          (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
      rw [hblack]
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      exact Or.inr rfl
    have hterminal :
        (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (.bond (fkIsingSquareWiredTerminalDart n hn)) .terminal := by
      have hne : fkIsingSquareWiredTerminalDart n hn ≠
          fkIsingSquareWiredSourceDart n hn :=
        (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      left
      simp [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, hne]
    have hcut : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
        (.terminal : FKIsingSquareWiredCarrier n) .source := by
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      exact Or.inr rfl
    exact hincidence.reachable.trans (hterminal.reachable.trans hcut.reachable)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have hprevSource : ∀ j < i, f^[j] d ≠
          fkIsingSquareWiredSourceDart n hn := by
        intro j hj
        exact (ih j hj).1
      have hprevTerminal : ∀ j < i, f^[j] d ≠
          fkIsingSquareWiredTerminalDart n hn := by
        intro j hj
        exact (ih j hj).2
      have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
        n hn omega d i hprevSource hprevTerminal
      change (sigma ^ i) x = fkIsingSquareWiredBlackOfDart n (f^[i] d) at hconj
      have hsame : sigma.SameCycle x ((sigma ^ i) x) := by
        exact Equiv.Perm.sameCycle_pow_right.mpr
          Equiv.Perm.SameCycle.rfl
      have hreach :
          (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
            x.1 ((sigma ^ i) x).1 :=
        fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
          n hn omega x ((sigma ^ i) x) hsame
      constructor
      · intro hcut
        have htoSource :
            (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
              ((sigma ^ i) x).1 .source := by
          rw [hconj, hcut]
          exact hsourceToCarrier
        exact hroot (hreach.trans htoSource)
      · intro hcut
        have htoSource :
            (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
              ((sigma ^ i) x).1 .source := by
          rw [hconj, hcut]
          exact hterminalToSource
        exact hroot (hreach.trans htoSource)



theorem fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hmove : fkIsingSquareWiredBlackBoundaryPerm n hn omega
        (fkIsingSquareWiredBlackOfDart n d) ≠
      fkIsingSquareWiredBlackOfDart n d)
    (hsource : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf
          (fkIsingSquareWiredBlackOfDart n d)).support.card,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf
          (fkIsingSquareWiredBlackOfDart n d)).support.card,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n d)),
      ¬p.Nil := by
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  change sigma x ≠ x at hmove
  change ∀ i < k,
    (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
      fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k,
    (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
      fkIsingSquareWiredTerminalDart n hn at hterminal
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k hsource hterminal
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n
    ((fkIsingSquareWiredPortNext n hn omega)^[k] d) at hconj
  have hclose :
      (fkIsingSquareWiredPortNext n hn omega)^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  obtain ⟨p, hpLen⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk
      n hn omega d k hsource hterminal
  let q : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n d)) :=
    p.copy rfl (congrArg (fun z =>
      (.inl (fkIsingSquareWiredDartSlot n z) :
        FKIsingSquareWiredExpandedCarrier n)) hclose)
  refine ⟨q, ?_⟩
  rw [SimpleGraph.Walk.not_nil_iff_lt_length]
  simpa [q] using (lt_of_lt_of_le (by omega : 0 < k) hpLen)



theorem fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdside : d.2 = .west ∨ d.2 = .east)
    (hmateWest : (FKIsingMedialDart.localMate omega d).2 ≠ .west)
    (hmateEast : (FKIsingMedialDart.localMate omega d).2 ≠ .east)
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root).edges := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let c : Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
    s(.inl (fkIsingSquareWiredDartSlot n d),
      .inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)))
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hfirst : f d = FKIsingMedialDart.localMate omega d := by
    rcases d with ⟨e, side⟩
    cases side <;> simp_all [f, fkIsingSquareWiredPortNext]
  have hnoRepeat : ∀ j, 0 < j → j < k → f^[j] d ≠ d := by
    intro j hj0 hjk hrepeat
    have hconjJ := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
    change (sigma ^ j) x = fkIsingSquareWiredBlackOfDart n (f^[j] d) at hconjJ
    rw [hrepeat] at hconjJ
    have hc : (sigma.cycleOf x).IsCycle :=
      Equiv.Perm.isCycle_cycleOf sigma hmove
    have hxCycle : x ∈ (sigma.cycleOf x).support := by
      rw [Equiv.Perm.mem_support_cycleOf_iff]
      exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
    have hsupport := hc.support_pow_of_pos_of_lt_orderOf hj0 (by
      rw [hc.orderOf]
      exact hjk)
    have hxPow : x ∈ (sigma.cycleOf x ^ j).support := by
      rw [hsupport]
      exact hxCycle
    rw [Equiv.Perm.mem_support] at hxPow
    apply hxPow
    rw [Equiv.Perm.cycleOf_pow_apply_self]
    exact hconjJ
  let m := k - 1
  have hmSucc : m + 1 = k := by
    simp [m]
    omega
  have hsourceRest : ∀ i < m, f^[i] (f d) ≠
      fkIsingSquareWiredSourceDart n hn := by
    intro i hi
    simpa [Function.iterate_succ_apply] using (havoid (i + 1)).1
  have hterminalRest : ∀ i < m, f^[i] (f d) ≠
      fkIsingSquareWiredTerminalDart n hn := by
    intro i hi
    simpa [Function.iterate_succ_apply] using (havoid (i + 1)).2
  have hdifferentRest : ∀ i < m, let q := f^[i] (f d)
      (q.2 = .west ∨ q.2 = .east) → c ≠
        s(.inl (fkIsingSquareWiredDartSlot n q),
          .inl (fkIsingSquareWiredDartSlot n (f q))) := by
    intro i hi
    dsimp only
    let q := f^[i] (f d)
    change (q.2 = .west ∨ q.2 = .east) → c ≠
      s(.inl (fkIsingSquareWiredDartSlot n q),
        .inl (fkIsingSquareWiredDartSlot n (f q)))
    intro hqside hedge
    have hqIter : q = f^[i + 1] d := by
      simp [q, Function.iterate_succ_apply]
    have hqLocal : f q = FKIsingMedialDart.localMate omega q := by
      rcases q with ⟨qe, qs⟩
      change qs = .west ∨ qs = .east at hqside
      rcases hqside with hqwest | hqeast
      · subst qs
        simp [f, fkIsingSquareWiredPortNext]
      · subst qs
        simp [f, fkIsingSquareWiredPortNext]
    have hedgeLocal :
        s((.inl (fkIsingSquareWiredDartSlot n d) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega d))) =
        s((.inl (fkIsingSquareWiredDartSlot n q) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega q))) := by
      simpa [c, hqLocal] using hedge
    rcases fkIsingSquareWired_local_edge_eq_iff_start_or_mate
      n omega q d hedgeLocal with hqd | hqd
    · exact hnoRepeat (i + 1) (by omega) (by omega)
        (hqIter.symm.trans hqd)
    · rcases hqside with hqwest | hqeast
      · exact hmateWest (hqd ▸ hqwest)
      · exact hmateEast (hqd ▸ hqeast)
  have hreachDelete :=
    fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local
      n hn omega d (f d) m hsourceRest hterminalRest hdifferentRest
  have hend : f^[m] (f d) = d := by
    rw [← Function.iterate_succ_apply]
    rw [Nat.succ_eq_add_one, hmSucc, hclose]
  rw [hend] at hreachDelete
  have hlocalAdj : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
      (fkIsingSquareWiredDartSlot n d)
      (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)) :=
    ⟨d, Or.inl ⟨rfl, rfl⟩⟩
  have hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d))) :=
    Or.inl ⟨_, _, rfl, rfl, hlocalAdj⟩
  rw [← hfirst] at hadj
  rw [← hfirst] at hreachDelete
  obtain ⟨root, p, hp, hedge⟩ :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
      ⟨hadj, hreachDelete.symm⟩)
  exact ⟨root, p, hp, by simpa [c, hfirst] using hedge⟩

set_option maxHeartbeats 1000000 in


theorem fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n d)),
      p.IsCycle ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let block := fkIsingSquareWiredPortMacroVertexWord n hn omega
  let steps := fkIsingSquareWiredPortMacroStepWord n hn omega
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hxCycle : x ∈ (sigma.cycleOf x).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hdartsNodup : darts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hij' : f^[i.1] d = f^[j.1] d := by
      simpa [darts, List.getElem_iterate] using hij
    have hiConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d i.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    have hjConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    change (sigma ^ i.1) x = fkIsingSquareWiredBlackOfDart n (f^[i.1] d)
      at hiConj
    change (sigma ^ j.1) x = fkIsingSquareWiredBlackOfDart n (f^[j.1] d)
      at hjConj
    have hpows : (sigma ^ i.1) x = (sigma ^ j.1) x := by
      rw [hiConj, hjConj, hij']
    have hcycleOn := Equiv.Perm.isCycleOn_support_cycleOf sigma x
    have hmod := (hcycleOn.pow_apply_eq_pow_apply hxCycle).mp hpows
    change i.1 % k = j.1 % k at hmod
    rw [Nat.mod_eq_of_lt (by simpa [darts] using i.isLt),
      Nat.mod_eq_of_lt (by simpa [darts] using j.isLt)] at hmod
    exact Fin.ext hmod
  have hverticesNodup : (darts.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro q hq
      exact fkIsingSquareWiredPortMacroVertexWord_nodup n hn omega q
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      apply fkIsingSquareWiredPortMacroVertexWord_disjoint n hn omega
      · simpa [darts, List.getElem_iterate] using (havoid i).1
      · simpa [darts, List.getElem_iterate] using (havoid i).2
      · simpa [darts, List.getElem_iterate] using (havoid j).1
      · simpa [darts, List.getElem_iterate] using (havoid j).2
      · intro heq
        exact (Nat.ne_of_lt hij) (hdartsNodup.getElem_inj_iff.mp heq)
  obtain ⟨r, hrSupport, hrDir⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction
      n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  let p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n d)) :=
    r.copy rfl (congrArg (fun z =>
      (.inl (fkIsingSquareWiredDartSlot n z) :
        FKIsingSquareWiredExpandedCarrier n)) hclose)
  have hpSupport : p.support = darts.flatMap block ++
      [.inl (fkIsingSquareWiredDartSlot n d)] := by
    simpa [p, darts, block, f, hclose] using hrSupport
  have hpDir : p.darts.map
      (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
      darts.flatMap steps := by
    simpa [p, darts, steps, f] using hrDir
  have hverticesNe : darts.flatMap block ≠ [] := by
    have hdartsNe : darts ≠ [] := by
      intro h
      have hlen : k = 0 := by
        simpa [darts] using congrArg List.length h
      omega
    obtain ⟨q, qs, hdarts⟩ := List.exists_cons_of_ne_nil hdartsNe
    rw [hdarts]
    simp [block, fkIsingSquareWiredPortMacroVertexWord_ne_nil]
  have hheadVertices : (darts.flatMap block).head hverticesNe =
      .inl (fkIsingSquareWiredDartSlot n d) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [darts, block, hm,
      fkIsingSquareWiredPortMacroVertexWord_ne_nil]
    exact fkIsingSquareWiredPortMacroVertexWord_head n hn omega d
      (havoid 0).1 (havoid 0).2
  have htailNodup : p.support.tail.Nodup := by
    obtain ⟨a, tail, hvertices⟩ := List.exists_cons_of_ne_nil hverticesNe
    have ha : a = .inl (fkIsingSquareWiredDartSlot n d) := by
      simpa [hvertices] using hheadVertices
    subst a
    rw [hpSupport, hvertices]
    simp only [List.cons_append, List.tail_cons]
    rw [List.nodup_append]
    have hv := hverticesNodup
    rw [hvertices, List.nodup_cons] at hv
    refine ⟨hv.2, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    apply hv.1
    rw [← hb, ← hab]
    exact ha
  have hpLength : 2 < p.length := by
    by_contra hle
    have hpDirLen := congrArg List.length hpDir
    simp only [List.length_map, SimpleGraph.Walk.length_darts] at hpDirLen
    have hkLe : k ≤ (darts.flatMap steps).length := by
      have hle' := List.length_le_flatMap_of_ne_nil darts steps
        (fun q hq => by
          rw [List.mem_iterate] at hq
          obtain ⟨i, hi, rfl⟩ := hq
          exact fkIsingSquareWiredPortMacroStepWord_ne_nil n hn omega _
            (havoid i).1 (havoid i).2)
      simpa [darts] using hle'
    have hkEq : k = 2 := by omega
    have hpLenEq : p.length = 2 := by omega
    have hlenTwo : (steps d).length + (steps (f d)).length = 2 := by
      calc
        _ = p.length := by
          simpa [darts, steps, hkEq] using hpDirLen.symm
        _ = 2 := hpLenEq
    exact fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two
      n hn omega d (havoid 0).1 (havoid 0).2
      (havoid 1).1 (havoid 1).2
      (by simpa [f, hkEq] using hclose) hlenTwo
  have hpNotNil : p ≠ SimpleGraph.Walk.nil := by
    intro h
    have hlen : p.length = 0 := by
      simpa using congrArg SimpleGraph.Walk.length h
    omega
  have hpNotNilPred : ¬p.Nil := fun hnil => hpNotNil hnil.eq_nil
  have htailPath : p.tail.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [p.support_tail_of_not_nil hpNotNilPred]
    exact htailNodup)
  have hpCycle : p.IsCycle := by
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨htailPath, by omega⟩
  exact ⟨p, hpCycle, hpDir⟩


theorem fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n q).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1)).sum ≡ 8 [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let step := fkIsingSquareWiredPortMacroStepWord n hn omega
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let transition := fun q => fkIsingSquareWiredTransitionTurn n hn omega
    (fkIsingSquareWiredBlackOfDart n q).1
    (fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n q).1)
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hk : 0 < k := by
    change 0 < (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact (Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem).trans_lt'
      (by omega)
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  obtain ⟨p, hp, hpDir⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit
      n hn omega d hroot
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
  let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
  have hdirList : List.ofFn (fun i => direction (loop i)) =
      darts.flatMap step := by
    rw [List.ofFn_comp', StatMech.FrontierA.kwGraphCycleDartLoop_ofFn]
    simpa [direction, step, darts, f] using hpDir
  have hcodeList : List.ofFn (fun i =>
      fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i))) =
      darts.flatMap code := by
    calc
      _ = List.map fkIsingSquareWiredUnitDiagonalTangentCode
          (List.ofFn (fun i => direction (loop i))) := by
        rw [List.ofFn_comp']
      _ = List.map fkIsingSquareWiredUnitDiagonalTangentCode
          (darts.flatMap step) := congrArg
        (List.map fkIsingSquareWiredUnitDiagonalTangentCode) hdirList
      _ = darts.flatMap code := by
        rw [List.map_flatMap]
        rfl
  have hwordNe : darts.flatMap code ≠ [] :=
    List.flatMap_ne_nil_of_ne_nil code
      (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
      darts (by simp [darts, hk.ne'])
  have hcyclic :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast hwordNe)
          ((darts.flatMap code).head hwordNe) =
        ∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
          (fkIsingSquareWiredUnitDiagonalTangentCode
            (direction (loop (i + 1)))) := by
    have h := carrierAdjacentSum_add_closing_eq_fin_sum
      fkIsingSquareSignedEighthTurn
      (fun i => fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
    simpa only [← hcodeList] using h
  have hmacro :=
    fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen
    n hn omega d k hk (by simpa [f] using hclose)
    (fun i hi => (havoid i).1) (fun i hi => (havoid i).2)
  change carrierAdjacentSum fkIsingSquareSignedEighthTurn
        (darts.flatMap code) +
      fkIsingSquareSignedEighthTurn
        ((darts.flatMap code).getLast _)
        ((darts.flatMap code).head _) ≡
      (darts.map transition).sum [ZMOD 16] at hmacro
  have hcycle :
      (∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
        (fkIsingSquareWiredUnitDiagonalTangentCode
          (direction (loop (i + 1))))) ≡ 8 [ZMOD 16] :=
    fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen
      n hn omega p hp
  have hcyclicMod :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast hwordNe)
          ((darts.flatMap code).head hwordNe) ≡
        ∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
          (fkIsingSquareWiredUnitDiagonalTangentCode
            (direction (loop (i + 1)))) [ZMOD 16] := by
    rw [hcyclic]
  exact hmacro.symm.trans (hcyclicMod.trans hcycle)

private theorem walk_eq_of_isCycles_of_isPath_of_avoids_previous
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {previous start finish : V} (hprevious : G.Adj previous start)
    (p q : G.Walk start finish)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpPrevious : s(previous, start) ∉ p.edges)
    (hqPrevious : s(previous, start) ∉ q.edges) :
    p = q := by
  induction p generalizing previous with
  | nil =>
      exact ((SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq).symm
  | @cons _ next _ hstartNext ptail ih =>
      cases q with
      | nil =>
          have hnil := (SimpleGraph.Walk.isPath_iff_eq_nil
            (SimpleGraph.Walk.cons hstartNext ptail)).mp hp
          contradiction
      | @cons _ next' _ hstartNext' qtail =>
          have hnextPrevious : next ≠ previous := by
            intro heq
            subst next
            exact hpPrevious (by simp [Sym2.eq_swap])
          have hnextPrevious' : next' ≠ previous := by
            intro heq
            subst next'
            exact hqPrevious (by simp [Sym2.eq_swap])
          obtain ⟨other, _, hunique⟩ :=
            hcycles.existsUnique_ne_adj hprevious.symm
          have hnext : next = other := hunique next
            ⟨hnextPrevious.symm, hstartNext⟩
          have hnext' : next' = other := hunique next'
            ⟨hnextPrevious'.symm, hstartNext'⟩
          subst next
          subst next'
          congr 1
          exact ih hstartNext qtail hp.of_cons hq.of_cons
            ((SimpleGraph.Walk.isTrail_cons hstartNext ptail).mp hp.isTrail).2
            ((SimpleGraph.Walk.isTrail_cons hstartNext' qtail).mp hq.isTrail).2

private theorem isCycle_eq_of_isCycles_of_snd_eq
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {root : V} (p q : G.Walk root root)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hsnd : p.snd = q.snd) :
    p = q := by
  cases p with
  | nil => exact False.elim (hp.not_nil SimpleGraph.Walk.Nil.nil)
  | @cons _ pnext _ hpedge ptail =>
      cases q with
      | nil => exact False.elim (hq.not_nil SimpleGraph.Walk.Nil.nil)
      | @cons _ qnext _ hqedge qtail =>
          simp only [SimpleGraph.Walk.snd_cons] at hsnd
          subst qnext
          have htails : ptail = qtail :=
            walk_eq_of_isCycles_of_isPath_of_avoids_previous
              hcycles hpedge ptail qtail
              (by simpa using hp.isPath_tail)
              (by simpa using hq.isPath_tail)
              ((SimpleGraph.Walk.cons_isCycle_iff ptail hpedge).mp hp).2
              ((SimpleGraph.Walk.cons_isCycle_iff qtail hqedge).mp hq).2
          subst qtail
          rfl

def fkIsingSquareWiredCarrierMacroVertexWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    List (FKIsingSquareWiredCarrier n) :=
  [(fkIsingSquareWiredBlackOfDart n d).1,
    fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1]

theorem fkIsingSquareWiredTransitionTurn_completedIncidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredTransitionTurn n hn omega x
      (fkIsingSquareWiredCompletedIncidenceEquiv n x) = 0 := by
  cases x <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredTransitionTurn]

theorem fkIsingSquareWiredCarrierMacroVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d).Nodup := by
  simp [fkIsingSquareWiredCarrierMacroVertexWord]
  exact (fkIsingSquareWiredTransitionMate_ne n hn omega _).symm

theorem fkIsingSquareWiredCarrierMacroVertexWord_disjoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hne : d ≠ e) :
    List.Disjoint
      (fkIsingSquareWiredCarrierMacroVertexWord n hn omega d)
      (fkIsingSquareWiredCarrierMacroVertexWord n hn omega e) := by
  apply List.disjoint_left.2
  intro z hzd hze
  simp only [fkIsingSquareWiredCarrierMacroVertexWord,
    List.mem_cons, List.not_mem_nil, or_false] at hzd hze
  rcases hzd with hzd | hzd <;> rcases hze with hze | hze
  · exact hne (fkIsingSquareWiredBlackOfDart_injective n
      (Subtype.ext (hzd.symm.trans hze)))
  · have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega
      (fkIsingSquareWiredBlackOfDart n e).1
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n e).1) ≠
      fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBlackOfDart n e).1 at hc
    rw [← hze, hzd] at hc
    exact hc ((fkIsingSquareWiredBlackOfDart n d).2.trans
      (fkIsingSquareWiredBlackOfDart n e).2.symm)
  · have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) ≠
      fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBlackOfDart n d).1 at hc
    rw [← hzd, hze] at hc
    exact hc ((fkIsingSquareWiredBlackOfDart n e).2.trans
      (fkIsingSquareWiredBlackOfDart n d).2.symm)
  · have hb : (fkIsingSquareWiredBlackOfDart n d).1 =
        (fkIsingSquareWiredBlackOfDart n e).1 := by
      apply (fkIsingSquareWiredTransitionMate_involutive n hn omega).injective
      exact hzd.symm.trans hze
    exact hne (fkIsingSquareWiredBlackOfDart_injective n (Subtype.ext hb))


theorem fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredPortNext n hn omega d)).1,
      p.IsPath ∧
      p.support = fkIsingSquareWiredCarrierMacroVertexWord n hn omega d ++
        [(fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredPortNext n hn omega d)).1] ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1) := by
  let b := (fkIsingSquareWiredBlackOfDart n d).1
  let t := fkIsingSquareWiredTransitionMate n hn omega b
  let bn := (fkIsingSquareWiredBlackOfDart n
    (fkIsingSquareWiredPortNext n hn omega d)).1
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d hsource hterminal
  have hvalue := congrArg (fun z : FKIsingSquareWiredBlackCarrier n => z.1) hstep
  have hboundary : fkIsingSquareWiredBoundaryStep n hn omega b = bn := by
    simpa [b, bn] using hvalue
  have hbt : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj b t :=
    (fkIsingSquareWiredCompletedLoopGraph_adj_iff n hn omega b t).mpr
      (Or.inl rfl)
  have htbn : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj t bn :=
    (fkIsingSquareWiredCompletedLoopGraph_adj_iff n hn omega t bn).mpr
      (Or.inr (by simpa [fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply, t] using hboundary.symm))
  let p := SimpleGraph.Walk.cons hbt
    (SimpleGraph.Walk.cons htbn SimpleGraph.Walk.nil)
  refine ⟨p, ?_, ?_, ?_⟩
  · simp [p, SimpleGraph.Walk.isPath_def]
    constructor
    · constructor
      · exact (fkIsingSquareWiredTransitionMate_ne n hn omega b).symm
      · have hne := fkIsingSquareWiredPortNext_ne n hn omega d
        exact fun h => hne (fkIsingSquareWiredBlackOfDart_injective n
          (Subtype.ext h.symm))
    · intro h
      have hc := fkIsingSquareWiredCarrierColor_transition_ne n hn omega b
      change fkIsingSquareWiredCarrierColor n t ≠
        fkIsingSquareWiredCarrierColor n b at hc
      rw [h] at hc
      exact hc ((fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredPortNext n hn omega d)).2.trans
        (fkIsingSquareWiredBlackOfDart n d).2.symm)
  · simp [p, fkIsingSquareWiredCarrierMacroVertexWord, b, t, bn]
  · have hincidence : fkIsingSquareWiredCompletedIncidenceEquiv n t = bn := by
      simpa [fkIsingSquareWiredBoundaryStep, Equiv.trans_apply, t]
        using hboundary
    have hsecond : fkIsingSquareWiredTransitionTurn n hn omega t bn = 0 := by
      rw [← hincidence]
      exact fkIsingSquareWiredTransitionTurn_completedIncidence n hn omega t
    simp [p, carrierAdjacentSum, b, t, bn, hsecond]

private theorem carrierAdjacentSum_append_tail_eq_add
    {A : Type*} (g : A → A → Int) (l r : List A)
    (hl : l ≠ []) (hr : r ≠ [])
    (hjoin : l.getLast hl = r.head hr) :
    carrierAdjacentSum g (l ++ r.tail) =
      carrierAdjacentSum g l + carrierAdjacentSum g r := by
  cases r with
  | nil => exact False.elim (hr rfl)
  | cons a tail =>
      cases tail with
      | nil => simp
      | cons b tail =>
          have htail : b :: tail ≠ [] := by simp
          change carrierAdjacentSum g (l ++ b :: tail) =
            carrierAdjacentSum g l + carrierAdjacentSum g (a :: b :: tail)
          rw [carrierAdjacentSum_append g l (b :: tail) hl htail]
          simp only [List.tail_cons, carrierAdjacentSum_cons_cons]
          have hab : l.getLast hl = a := by simpa using hjoin
          have hbhead : (b :: tail).head htail = b := by simp
          rw [hab, hbhead]
          omega

theorem fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1,
      let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
      p.support = darts.flatMap
          (fkIsingSquareWiredCarrierMacroVertexWord n hn omega) ++
        [(fkIsingSquareWiredBlackOfDart n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d)).1] ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
  let f := fkIsingSquareWiredPortNext n hn omega
  induction k generalizing d with
  | zero => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      obtain ⟨p, hpPath, hp, hpTurn⟩ :=
        fkIsingSquareWiredCompletedGraph_exists_portNext_carrier_path
          n hn omega d (hsource 0 (by omega)) (hterminal 0 (by omega))
      obtain ⟨q, hq, hqTurn⟩ := ih (f d)
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hsource (i + 1) (by omega))
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hterminal (i + 1) (by omega))
      let r := p.append q
      have hend : f^[k] (f d) = f^[k + 1] d := by
        simpa only [Function.iterate_succ_apply] using
          (Function.Commute.iterate_right (Function.Commute.refl f) k d)
      have hendCarrier : (fkIsingSquareWiredBlackOfDart n
          (f^[k] (f d))).1 =
          (fkIsingSquareWiredBlackOfDart n (f^[k + 1] d)).1 :=
        congrArg (fun z => (fkIsingSquareWiredBlackOfDart n z).1) hend
      let s := r.copy rfl hendCarrier
      refine ⟨s, ?_, ?_⟩
      · have hqCons := q.cons_tail_support
        rw [hq] at hqCons
        simp only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_append, s, r]
        rw [hp, hq]
        simp [List.iterate,
          fkIsingSquareWiredCarrierMacroVertexWord, hend]
        simpa only [f] using hqCons
      · have hpNe : p.support ≠ [] := SimpleGraph.Walk.support_ne_nil p
        have hqNe : q.support ≠ [] := SimpleGraph.Walk.support_ne_nil q
        have hjoin : p.support.getLast hpNe = q.support.head hqNe := by
          calc
            p.support.getLast hpNe =
                (fkIsingSquareWiredBlackOfDart n (f d)).1 := by
              simpa only [f] using SimpleGraph.Walk.getLast_support p
            _ = q.support.head hqNe := by
              simpa only [f] using (SimpleGraph.Walk.head_support q).symm
        calc
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
              s.support =
              carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                (p.support ++ q.support.tail) := by
                exact congrArg
                  (carrierAdjacentSum
                    (fkIsingSquareWiredTransitionTurn n hn omega))
                  (by simpa only [s, SimpleGraph.Walk.support_copy, r] using
                    SimpleGraph.Walk.support_append p q)
          _ = carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                p.support +
              carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
                q.support :=
            carrierAdjacentSum_append_tail_eq_add _ _ _ hpNe hqNe hjoin
          _ = _ := by
            rw [hpTurn, hqTurn]
            change _ +
                (List.map _ (List.iterate f (f d) k)).sum =
              (List.map _ (List.iterate f d (k + 1))).sum
            rw [show k + 1 = Nat.succ k by omega, List.iterate]
            simp

theorem fkIsingSquareWiredCompletedLoopGraph_isCycles
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).IsCycles := by
  intro v _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    SimpleGraph.card_neighborSet_eq_degree]
  simpa only using
    fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v


theorem fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    ∃ p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredBlackOfDart n d).1,
      p.IsCycle ∧
      p.snd = fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 ∧
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.support =
        (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let block := fkIsingSquareWiredCarrierMacroVertexWord n hn omega
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hxCycle : x ∈ (sigma.cycleOf x).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hdartsNodup : darts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hij' : f^[i.1] d = f^[j.1] d := by
      simpa [darts, List.getElem_iterate] using hij
    have hiConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d i.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    have hjConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    change (sigma ^ i.1) x = fkIsingSquareWiredBlackOfDart n (f^[i.1] d)
      at hiConj
    change (sigma ^ j.1) x = fkIsingSquareWiredBlackOfDart n (f^[j.1] d)
      at hjConj
    have hpows : (sigma ^ i.1) x = (sigma ^ j.1) x := by
      rw [hiConj, hjConj, hij']
    have hcycleOn := Equiv.Perm.isCycleOn_support_cycleOf sigma x
    have hmod := (hcycleOn.pow_apply_eq_pow_apply hxCycle).mp hpows
    change i.1 % k = j.1 % k at hmod
    rw [Nat.mod_eq_of_lt (by simpa [darts] using i.isLt),
      Nat.mod_eq_of_lt (by simpa [darts] using j.isLt)] at hmod
    exact Fin.ext hmod
  have hverticesNodup : (darts.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro q _
      exact fkIsingSquareWiredCarrierMacroVertexWord_nodup n hn omega q
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      apply fkIsingSquareWiredCarrierMacroVertexWord_disjoint n hn omega
      intro heq
      exact (Nat.ne_of_lt hij) (hdartsNodup.getElem_inj_iff.mp heq)
  obtain ⟨r, hrSupport, hrTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_portNext_iterate_carrier_walk
      n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  let p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk x.1 x.1 :=
    r.copy rfl (congrArg (fun z =>
      (fkIsingSquareWiredBlackOfDart n z).1) hclose)
  have hpSupport : p.support = darts.flatMap block ++ [x.1] := by
    simpa [p, darts, block, x, f, hclose] using hrSupport
  have hpTurn : carrierAdjacentSum
      (fkIsingSquareWiredTransitionTurn n hn omega) p.support =
      (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1)).sum := by
    simpa [p, darts, f] using hrTurn
  have hverticesNe : darts.flatMap block ≠ [] := by
    exact List.flatMap_ne_nil_of_ne_nil block
      (fun q => by simp [block, fkIsingSquareWiredCarrierMacroVertexWord])
      darts (by simp [darts]; omega)
  have hheadVertices : (darts.flatMap block).head hverticesNe = x.1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [darts, block, x, hm, fkIsingSquareWiredCarrierMacroVertexWord]
  have htailNodup : p.support.tail.Nodup := by
    obtain ⟨a, tail, hvertices⟩ := List.exists_cons_of_ne_nil hverticesNe
    have ha : a = x.1 := by simpa [hvertices] using hheadVertices
    subst a
    rw [hpSupport, hvertices]
    simp only [List.cons_append, List.tail_cons]
    rw [List.nodup_append]
    have hv := hverticesNodup
    rw [hvertices, List.nodup_cons] at hv
    refine ⟨hv.2, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    apply hv.1
    rw [← hb, ← hab]
    exact ha
  have hpLength : 2 < p.length := by
    have hlen := p.length_support
    rw [hpSupport] at hlen
    simp [darts, block, fkIsingSquareWiredCarrierMacroVertexWord] at hlen
    omega
  have hpNotNil : p ≠ SimpleGraph.Walk.nil := by
    intro h
    have hlen : p.length = 0 := by
      simpa using congrArg SimpleGraph.Walk.length h
    omega
  have hpNotNilPred : ¬p.Nil := fun hnil => hpNotNil hnil.eq_nil
  have htailPath : p.tail.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [p.support_tail_of_not_nil hpNotNilPred]
    exact htailNodup)
  have hpCycle : p.IsCycle := by
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨htailPath, by omega⟩
  have hpSnd : p.snd = fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1 := by
    have hsnd := p.snd_eq_support_getElem_one hpNotNilPred
    have h1 : 1 < p.support.length := by
      rw [p.length_support]
      omega
    have hsndOpt : p.support[1]? = some p.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hpSupport
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have htarget : p.support[1]? = some
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) := by
      simpa [darts, block, x, hm,
        fkIsingSquareWiredCarrierMacroVertexWord] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  exact ⟨p, hpCycle, hpSnd, hpTurn⟩

private theorem fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    {a b : FKIsingSquareWiredCarrier n}
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            a b) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support =
      carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)) r.support := by
  apply carrierAdjacentSum_chain_congr
  exact r.isChain_adj_support.imp (by
    intro x y hxy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side hx side' hy
    subst x
    subst y
    cases side <;> cases side' <;>
      simp [SimpleGraph.deleteEdges_adj,
        fkIsingSquareWiredLoopGraph,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredIncidenceMate,
        FKIsingMedialDart.localMate, setClosed] at hxy)

private theorem fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local_comm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    {a b : FKIsingSquareWiredCarrier n}
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            a b) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support =
      carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)) r.support := by
  apply carrierAdjacentSum_chain_congr
  exact r.isChain_adj_support.imp (by
    intro x y hxy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side hx side' hy
    subst x
    subst y
    cases side <;> cases side' <;>
      simp [SimpleGraph.deleteEdges_adj,
        fkIsingSquareWiredLoopGraph,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredIncidenceMate,
        FKIsingMedialDart.localMate, setClosed] at hxy)


theorem fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)),
          s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk
            (.dart (e, .east)) (.dart (e, .north)))
    (hr : r.IsPath) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
        (.dart (e, .north)) (.dart (e, .east)) ≡ 8 [ZMOD 16] := by
  let closed := setClosed e.1 omega
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn closed d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn closed d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWired_one_visit_west_carrierCycle
      n hn omega e r hr
  let qC := q.mapLe (show fkIsingSquareWiredLoopGraph n hn closed ≤
      fkIsingSquareWiredCompletedLoopGraph n hn closed from le_sup_left)
  have hqC : qC.IsCycle := hq.mapLe _
  have hqCSupport : qC.support = E :: r.reverse.support := by
    calc
      qC.support = q.support := by
        exact SimpleGraph.Walk.support_mapLe_eq_support _ q
      _ = E :: r.reverse.support := by simpa [E] using hqSupport
  have hqCSnd : qC.snd = N := by
    have hsnd := qC.snd_eq_support_getElem_one hqC.not_nil
    have h1 : 1 < qC.support.length := by
      have hlen := hqC.three_le_length
      rw [qC.length_support]
      omega
    have hsndOpt : qC.support[1]? = some qC.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hqCSupport
    have htarget : qC.support[1]? = some N := by
      simpa [N] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  have hcSnd' : c.snd = N := by
    simpa [closed, d, N, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setClosed_self] using hcSnd
  have hcEq : c = qC := isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn closed)
    c qC hc hqC (hcSnd'.trans hqCSnd.symm)
  have hrrev : r.reverse.support = N :: r.reverse.support.tail := by
    simpa [N] using r.reverse.cons_tail_support.symm
  have htotal :
      fkIsingSquareWiredTransitionTurn n hn closed E N +
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn closed) r.reverse.support ≡
        8 [ZMOD 16] := by
    rw [hcEq] at hcMod
    have hsumEq : carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn closed) qC.support =
        fkIsingSquareWiredTransitionTurn n hn closed E N +
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support := by
      rw [hqCSupport, hrrev, carrierAdjacentSum_cons_cons]
    have hsumMod :
        fkIsingSquareWiredTransitionTurn n hn closed E N +
            carrierAdjacentSum
              (fkIsingSquareWiredTransitionTurn n hn closed)
              r.reverse.support ≡
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed) qC.support
          [ZMOD 16] := by
      rw [hsumEq]
    exact hsumMod.trans hcMod
  let rH := r.mapLe (SimpleGraph.deleteEdges_le _)
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed rH
  have hEN : (fkIsingSquareWiredLoopGraph n hn closed).Adj E N := by
    exact Or.inr (by simp [closed, E, N,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setClosed_self])
  have hlocal := fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    n hn closed hEN
  have hsum :
      (carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed N E) +
        (fkIsingSquareWiredTransitionTurn n hn closed E N +
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support) ≡ 0 [ZMOD 16] := by
    have := hreverse.add hlocal
    simp only [rH, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_reverse] at this
    rw [← SimpleGraph.Walk.support_reverse r] at this
    convert this using 1 <;> ring
  have hclosed :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed N E ≡ 8 [ZMOD 16] := by
    have hneg := hsum.sub htotal
    have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
    convert hneg.trans hminus using 1 <;> ring
  rw [fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local
    n hn omega e r]
  simpa [closed, N, E] using hclosed

set_option maxHeartbeats 1000000 in

theorem fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)),
          s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk
            (.dart (e, .west)) (.dart (e, .south)))
    (hr : r.IsPath) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support +
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
        (.dart (e, .south)) (.dart (e, .west)) ≡ 8 [ZMOD 16] := by
  let closed := setClosed e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn closed d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn closed d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWired_one_visit_east_carrierCycle
      n hn omega e r hr
  let qC := q.mapLe (show fkIsingSquareWiredLoopGraph n hn closed ≤
      fkIsingSquareWiredCompletedLoopGraph n hn closed from le_sup_left)
  have hqC : qC.IsCycle := hq.mapLe _
  have hqCSupport : qC.support = W :: r.reverse.support := by
    calc
      qC.support = q.support := by
        exact SimpleGraph.Walk.support_mapLe_eq_support _ q
      _ = W :: r.reverse.support := by simpa [W] using hqSupport
  have hqCSnd : qC.snd = S := by
    have hsnd := qC.snd_eq_support_getElem_one hqC.not_nil
    have h1 : 1 < qC.support.length := by
      have hlen := hqC.three_le_length
      rw [qC.length_support]
      omega
    have hsndOpt : qC.support[1]? = some qC.snd := by
      rw [List.getElem?_eq_getElem h1, ← hsnd]
    have hsupportOpt := congrArg (fun l => l[1]?) hqCSupport
    have htarget : qC.support[1]? = some S := by
      simpa [S] using hsupportOpt
    exact Option.some_inj.mp (hsndOpt.symm.trans htarget)
  have hcSnd' : c.snd = S := by
    simpa [closed, d, S, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setClosed_self] using hcSnd
  have hcEq : c = qC := isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn closed)
    c qC hc hqC (hcSnd'.trans hqCSnd.symm)
  have hrrev : r.reverse.support = S :: r.reverse.support.tail := by
    simpa [S] using r.reverse.cons_tail_support.symm
  have htotal :
      fkIsingSquareWiredTransitionTurn n hn closed W S +
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn closed) r.reverse.support ≡
        8 [ZMOD 16] := by
    rw [hcEq] at hcMod
    have hsumEq : carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn closed) qC.support =
        fkIsingSquareWiredTransitionTurn n hn closed W S +
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support := by
      rw [hqCSupport, hrrev, carrierAdjacentSum_cons_cons]
    have hsumMod :
        fkIsingSquareWiredTransitionTurn n hn closed W S +
            carrierAdjacentSum
              (fkIsingSquareWiredTransitionTurn n hn closed)
              r.reverse.support ≡
          carrierAdjacentSum
            (fkIsingSquareWiredTransitionTurn n hn closed) qC.support
          [ZMOD 16] := by
      rw [hsumEq]
    exact hsumMod.trans hcMod
  let rH := r.mapLe (SimpleGraph.deleteEdges_le _)
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed rH
  have hWS : (fkIsingSquareWiredLoopGraph n hn closed).Adj W S := by
    exact Or.inr (by simp [closed, W, S,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setClosed_self])
  have hlocal := fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    n hn closed hWS
  have hsum :
      (carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed S W) +
        (fkIsingSquareWiredTransitionTurn n hn closed W S +
          carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
            r.reverse.support) ≡ 0 [ZMOD 16] := by
    have := hreverse.add hlocal
    simp only [rH, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_reverse] at this
    rw [← SimpleGraph.Walk.support_reverse r] at this
    convert this using 1 <;> ring
  have hclosed :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed) r.support +
          fkIsingSquareWiredTransitionTurn n hn closed S W ≡ 8 [ZMOD 16] := by
    have hneg := hsum.sub htotal
    have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
    convert hneg.trans hminus using 1 <;> ring
  have hopenClosed :=
    fkIsingSquareWired_carrierAdjacentSum_open_eq_closed_of_deleted_local_comm
      n hn omega e r
  rw [hopenClosed]
  simpa [closed, S, W] using hclosed



theorem fkIsingSquareWired_one_visit_west_inserted_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) := by
  apply fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr _
  exact fkIsingSquareWired_one_visit_west_cycle_turn_mod_sixteen
    n hn omega e hwest heast r hr



theorem fkIsingSquareWired_one_visit_east_inserted_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) := by
  apply fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen
    n hn omega e hwest heast
  intro r hr _
  exact fkIsingSquareWired_one_visit_east_cycle_turn_mod_sixteen
    n hn omega e hwest heast r hr



theorem fkIsingSquareWired_one_visit_west_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn
        (setClosed e.1 omega)).Walk
        (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
        (.inl (fkIsingSquareWiredDartSlot n (e, .east))),
      ¬p.Nil := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn closed d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn closed d (havoid 0).1 (havoid 0).2
  have hmove : fkIsingSquareWiredBlackBoundaryPerm n hn closed
      (fkIsingSquareWiredBlackOfDart n d) ≠
        fkIsingSquareWiredBlackOfDart n d := by
    intro heq
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn closed d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  apply fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    n hn closed d hmove
  · intro i _
    exact (havoid i).1
  · intro i _
    exact (havoid i).2



theorem fkIsingSquareWired_one_visit_east_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn
        (setClosed e.1 omega)).Walk
        (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
        (.inl (fkIsingSquareWiredDartSlot n (e, .west))),
      ¬p.Nil := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn closed d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn closed d (havoid 0).1 (havoid 0).2
  have hmove : fkIsingSquareWiredBlackBoundaryPerm n hn closed
      (fkIsingSquareWiredBlackOfDart n d) ≠
        fkIsingSquareWiredBlackOfDart n d := by
    intro heq
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn closed d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  apply fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    n hn closed d hmove
  · intro i _
    exact (havoid i).1
  · intro i _
    exact (havoid i).2


theorem fkIsingSquareWired_one_visit_west_exists_expanded_cycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n (e, .north))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn
          (setClosed e.1 omega)).Walk root root).edges := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  simpa [closed, d, FKIsingMedialDart.localMate, setClosed_self] using
    (fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
      n hn closed d (Or.inr rfl)
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self])
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self]) hroot)


theorem fkIsingSquareWired_one_visit_east_exists_expanded_cycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n (e, .south))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn
          (setClosed e.1 omega)).Walk root root).edges := by
  let closed := setClosed e.1 omega
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn closed).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [closed, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
  simpa [closed, d, FKIsingMedialDart.localMate, setClosed_self] using
    (fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
      n hn closed d (Or.inl rfl)
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self])
        (by simp [closed, d, FKIsingMedialDart.localMate, setClosed_self]) hroot)

end

end StatMech.Universality
