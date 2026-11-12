/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusSquareDevelopment
import Code.FrontierD.IntegralSquareTorusIntersection










open scoped BigOperators

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section


abbrev FKRectIntegralSquareDart := (Int × Int) × Fin 4


def fkRectIntegralSquareDartEnd (d : FKRectIntegralSquareDart) : Int × Int :=
  (d.1.1 + ons_dirExponentX d.2,
    d.1.2 + ons_dirExponentY d.2)


def fkRectIntegralSquareDartMod (L : Nat) (d : FKRectIntegralSquareDart) :
    ons_Dart L :=
  (((d.1.1 : ZMod L), (d.1.2 : ZMod L)), d.2)

@[simp] theorem fkRectIntegralSquareDartMod_site
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).1 =
      ((d.1.1 : ZMod L), (d.1.2 : ZMod L)) :=
  rfl

theorem fkRectIntegralSquareDartMod_end
    (L : Nat) (d : FKRectIntegralSquareDart) :
    ons_dirStep L (fkRectIntegralSquareDartMod L d).2
        (fkRectIntegralSquareDartMod L d).1 =
      (((fkRectIntegralSquareDartEnd d).1 : ZMod L),
        ((fkRectIntegralSquareDartEnd d).2 : ZMod L)) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [fkRectIntegralSquareDartMod, fkRectIntegralSquareDartEnd,
      ons_dirStep, ons_dirExponentX, ons_dirExponentY] <;> ring



theorem FKRectSquareAxisStep.exists_direction
    {p q : Int × Int} (h : FKRectSquareAxisStep p q) :
    ∃ mu : Fin 4, fkRectIntegralSquareDartEnd (p, mu) = q := by
  rcases h with h | h | h | h
  · refine ⟨2, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨1, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨0, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega
  · refine ⟨3, ?_⟩
    apply Prod.ext <;>
      have := congrArg (fun z : Int × Int => z.1) h <;>
      have := congrArg (fun z : Int × Int => z.2) h <;>
      simp [fkRectIntegralSquareDartEnd, ons_dirExponentX,
        ons_dirExponentY] at * <;> omega


inductive FKRectIntegralSquareDartPath :
    (Int × Int) → (Int × Int) →
      List FKRectIntegralSquareDart → Prop
  | nil (p : Int × Int) : FKRectIntegralSquareDartPath p p []
  | cons (d : FKRectIntegralSquareDart) {q r l}
      (hend : fkRectIntegralSquareDartEnd d = q)
      (tail : FKRectIntegralSquareDartPath q r l) :
      FKRectIntegralSquareDartPath d.1 r (d :: l)



theorem FKRectSquareWalkLift.exists_integralDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      l.length = w.darts.length := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _, by simp⟩
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      obtain ⟨l, hl, hlen⟩ := ih
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      refine ⟨((fkRectSquareDevelopPoint p, mu) :: l),
        FKRectIntegralSquareDartPath.cons _ hmu hl, ?_⟩
      simp [hlen]


def fkRectIntegralSquareDartTranslate (u : Int × Int)
    (d : FKRectIntegralSquareDart) : FKRectIntegralSquareDart :=
  ((d.1.1 + u.1, d.1.2 + u.2), d.2)

theorem fkRectIntegralSquareDartEnd_translate
    (u : Int × Int) (d : FKRectIntegralSquareDart) :
    fkRectIntegralSquareDartEnd
        (fkRectIntegralSquareDartTranslate u d) =
      ((fkRectIntegralSquareDartEnd d).1 + u.1,
        (fkRectIntegralSquareDartEnd d).2 + u.2) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  apply Prod.ext <;>
    simp [fkRectIntegralSquareDartTranslate,
      fkRectIntegralSquareDartEnd] <;> ring


theorem FKRectIntegralSquareDartPath.translate
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (u : Int × Int) :
    FKRectIntegralSquareDartPath
      (p.1 + u.1, p.2 + u.2) (q.1 + u.1, q.2 + u.2)
      (l.map (fkRectIntegralSquareDartTranslate u)) := by
  induction h with
  | nil p =>
      exact FKRectIntegralSquareDartPath.nil _
  | @cons d q r l hend tail ih =>
      apply FKRectIntegralSquareDartPath.cons
        (fkRectIntegralSquareDartTranslate u d)
      · rw [fkRectIntegralSquareDartEnd_translate, hend]
      · exact ih


theorem FKRectIntegralSquareDartPath.append
    {p q r : Int × Int} {l k : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l)
    (g : FKRectIntegralSquareDartPath q r k) :
    FKRectIntegralSquareDartPath p r (l ++ k) := by
  induction h with
  | nil p => simpa using g
  | cons d hend tail ih =>
      exact FKRectIntegralSquareDartPath.cons d hend (ih g)



def fkRectNatScale (n : Nat) (u : Int × Int) : Int × Int :=
  ((n : Int) * u.1, (n : Int) * u.2)


def fkRectRepeatTranslatedDartPath
    (l : List FKRectIntegralSquareDart) (u : Int × Int) :
    Nat → List FKRectIntegralSquareDart
  | 0 => []
  | n + 1 =>
      fkRectRepeatTranslatedDartPath l u n ++
        l.map (fkRectIntegralSquareDartTranslate (fkRectNatScale n u))

theorem FKRectIntegralSquareDartPath.repeatTranslated
    {p u : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) (n : Nat) :
    FKRectIntegralSquareDartPath p
      (p.1 + (n : Int) * u.1, p.2 + (n : Int) * u.2)
      (fkRectRepeatTranslatedDartPath l u n) := by
  induction n with
  | zero =>
      simpa [fkRectRepeatTranslatedDartPath] using
        (FKRectIntegralSquareDartPath.nil p)
  | succ n ih =>
      have htranslate := h.translate (fkRectNatScale n u)
      have happend := ih.append htranslate
      have hend :
          ((p.1 + u.1, p.2 + u.2).1 + (fkRectNatScale n u).1,
              (p.1 + u.1, p.2 + u.2).2 + (fkRectNatScale n u).2) =
            (p.1 + ((n + 1 : Nat) : Int) * u.1,
              p.2 + ((n + 1 : Nat) : Int) * u.2) := by
        apply Prod.ext <;>
          simp [fkRectNatScale, Nat.cast_add, Nat.cast_one] <;> ring
      rw [hend] at happend
      rw [fkRectRepeatTranslatedDartPath]
      exact happend



def fkRectIntegralSquarePointMod (L : Nat) (p : Int × Int) :
    ZMod L × ZMod L :=
  ((p.1 : ZMod L), (p.2 : ZMod L))

@[simp] theorem fkRectIntegralSquareDartMod_site_eq_pointMod
    (L : Nat) (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartMod L d).1 =
      fkRectIntegralSquarePointMod L d.1 :=
  rfl



theorem FKRectIntegralSquareDartPath.pointMass_telescope
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (L : Nat)
    (z : ZMod L × ZMod L) :
    ((l.map (fkRectIntegralSquareDartMod L)).map
        (fun d => IntegralSquareTorusCycle.pointMass d.1 z)).sum -
      ((l.map (fkRectIntegralSquareDartMod L)).map
        (fun d => IntegralSquareTorusCycle.pointMass
          (ons_dirStep L d.2 d.1) z)).sum =
    IntegralSquareTorusCycle.pointMass
        (fkRectIntegralSquarePointMod L p) z -
      IntegralSquareTorusCycle.pointMass
        (fkRectIntegralSquarePointMod L q) z := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [fkRectIntegralSquareDartMod_end, hend]
      change IntegralSquareTorusCycle.pointMass
            (fkRectIntegralSquarePointMod L d.1) z +
            ((l.map (fkRectIntegralSquareDartMod L)).map
              (fun d => IntegralSquareTorusCycle.pointMass d.1 z)).sum -
          (IntegralSquareTorusCycle.pointMass
              (fkRectIntegralSquarePointMod L q) z +
            ((l.map (fkRectIntegralSquareDartMod L)).map
              (fun d => IntegralSquareTorusCycle.pointMass
                (ons_dirStep L d.2 d.1) z)).sum) = _
      linear_combination ih



theorem FKRectIntegralSquareDartPath.dartListBalanced_of_pointMod_eq
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) (L : Nat)
    (hend : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L q) :
    IntegralSquareTorusCycle.DartListBalanced
      (l.map (fkRectIntegralSquareDartMod L)) := by
  intro z
  have htelescope := h.pointMass_telescope L z
  rw [hend, sub_self] at htelescope
  exact sub_eq_zero.mp htelescope

section Wrap

variable {L : Nat} [Fact (2 < L)]

theorem fkRectIntegralSquareDart_displacement_x
    (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartEnd d).1 - d.1.1 =
      (((fkRectIntegralSquarePointMod L
          (fkRectIntegralSquareDartEnd d)).1.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L d.1).1.val : Nat) : Int) +
        (L : Int) * ons_xWrapSign (fkRectIntegralSquareDartMod L d) := by
  have h := ons_dirExponentX_eq_val_diff_add_wrap
    (fkRectIntegralSquareDartMod L d)
  rw [fkRectIntegralSquareDartMod_end] at h
  calc
    (fkRectIntegralSquareDartEnd d).1 - d.1.1 =
        ons_dirExponentX d.2 := by
          simp [fkRectIntegralSquareDartEnd]
    _ = _ := h

theorem fkRectIntegralSquareDart_displacement_y
    (d : FKRectIntegralSquareDart) :
    (fkRectIntegralSquareDartEnd d).2 - d.1.2 =
      (((fkRectIntegralSquarePointMod L
          (fkRectIntegralSquareDartEnd d)).2.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L d.1).2.val : Nat) : Int) +
        (L : Int) * ons_yWrapSign (fkRectIntegralSquareDartMod L d) := by
  have h := ons_dirExponentY_eq_val_diff_add_wrap
    (fkRectIntegralSquareDartMod L d)
  rw [fkRectIntegralSquareDartMod_end] at h
  calc
    (fkRectIntegralSquareDartEnd d).2 - d.1.2 =
        ons_dirExponentY d.2 := by
          simp [fkRectIntegralSquareDartEnd]
    _ = _ := h



theorem FKRectIntegralSquareDartPath.displacement_x_eq_wrap
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    q.1 - p.1 =
      (((fkRectIntegralSquarePointMod L q).1.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L p).1.val : Nat) : Int) +
        (L : Int) *
          ((l.map (fkRectIntegralSquareDartMod L)).map
            ons_xWrapSign).sum := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      have hd := fkRectIntegralSquareDart_displacement_x (L := L) d
      rw [hend] at hd
      simp only [List.map_cons, List.sum_cons]
      linear_combination hd + ih


theorem FKRectIntegralSquareDartPath.displacement_y_eq_wrap
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    q.2 - p.2 =
      (((fkRectIntegralSquarePointMod L q).2.val : Nat) : Int) -
        (((fkRectIntegralSquarePointMod L p).2.val : Nat) : Int) +
        (L : Int) *
          ((l.map (fkRectIntegralSquareDartMod L)).map
            ons_yWrapSign).sum := by
  induction h with
  | nil p => simp
  | @cons d q r l hend tail ih =>
      have hd := fkRectIntegralSquareDart_displacement_y (L := L) d
      rw [hend] at hd
      simp only [List.map_cons, List.sum_cons]
      linear_combination hd + ih

end Wrap



def fkRectSquareCoverSide (R : FKRectTorus) : Nat :=
  R.width * R.height

theorem fkRectSquareCoverSide_gt_two (R : FKRectTorus) :
    2 < fkRectSquareCoverSide R := by
  exact lt_of_lt_of_le R.width_gt_two
    (Nat.le_mul_of_pos_right R.width R.height_pos)

instance fkRectSquareCoverSide_neZero (R : FKRectTorus) :
    NeZero (fkRectSquareCoverSide R) :=
  ⟨ne_of_gt (lt_trans (by norm_num : 0 < 2)
    (fkRectSquareCoverSide_gt_two R))⟩

instance fkRectSquareCoverSide_fact (R : FKRectTorus) :
    Fact (2 < fkRectSquareCoverSide R) :=
  ⟨fkRectSquareCoverSide_gt_two R⟩


structure FKRectSquareCoverCycleWitness (R : FKRectTorus)
    (u : Int × Int) where
  cycle : IntegralSquareTorusCycle (fkRectSquareCoverSide R)
  xFlux_eq : cycle.xFlux (-1) = u.1
  yFlux_eq : cycle.yFlux (-1) = u.2




theorem FKRectIntegralSquareDartPath.exists_squareCoverCycleWitness
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    Nonempty (FKRectSquareCoverCycleWitness R u) := by
  let L := fkRectSquareCoverSide R
  letI : Fact (2 < L) := ⟨fkRectSquareCoverSide_gt_two R⟩
  let repeated := fkRectRepeatTranslatedDartPath l u L
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) repeated :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  let darts := repeated.map (fkRectIntegralSquareDartMod L)
  have hbalanced : IntegralSquareTorusCycle.DartListBalanced darts := by
    exact hrepeated.dartListBalanced_of_pointMod_eq L hpointMod
  have hxEquation := hrepeated.displacement_x_eq_wrap (L := L)
  have hyEquation := hrepeated.displacement_y_eq_wrap (L := L)
  rw [hpointMod] at hxEquation hyEquation
  simp only [sub_self, zero_add] at hxEquation hyEquation
  rw [add_sub_cancel_left] at hxEquation hyEquation
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  have hxWrap :
      (darts.map ons_xWrapSign).sum = u.1 := by
    have hxScaled : (L : Int) * (darts.map ons_xWrapSign).sum =
        (L : Int) * u.1 := by
      dsimp [darts]
      exact hxEquation.symm
    exact mul_left_cancel₀ hL hxScaled
  have hyWrap :
      (darts.map ons_yWrapSign).sum = u.2 := by
    have hyScaled : (L : Int) * (darts.map ons_yWrapSign).sum =
        (L : Int) * u.2 := by
      dsimp [darts]
      exact hyEquation.symm
    exact mul_left_cancel₀ hL hyScaled
  let C := IntegralSquareTorusCycle.ofDartList darts hbalanced
  refine ⟨⟨C, ?_, ?_⟩⟩
  · rw [IntegralSquareTorusCycle.ofDartList_xFlux, hxWrap]
  · rw [IntegralSquareTorusCycle.ofDartList_yFlux, hyWrap]



theorem FKRectSquareWalkLift.exists_squareCoverCycleWitness
    (R : FKRectTorus) {G : SimpleGraph R.Vertex} {x : R.Vertex}
    {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    Nonempty (FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)) := by
  obtain ⟨l, hl, hlen⟩ := h.exists_integralDartPath R
  have hend : fkRectSquareDevelopPoint q =
      ((fkRectSquareDevelopPoint p).1 +
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
        (fkRectSquareDevelopPoint p).2 +
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2) := by
    apply Prod.ext <;> simp
  rw [hend] at hl
  exact hl.exists_squareCoverCycleWitness R




theorem FKRectSquareCoverCycleWitness.not_independent_of_locallyDisjoint
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverCycleWitness R u)
    (D : FKRectSquareCoverCycleWitness R v)
    (hdisj : C.cycle.LocallyDisjoint D.cycle) :
    ¬ FKRectWindingIndependent u v := by
  intro hind
  apply hind
  have hdet :=
    IntegralSquareTorusCycle.flux_det_eq_zero_of_locallyDisjoint hdisj
  rw [C.xFlux_eq, C.yFlux_eq, D.xFlux_eq, D.yFlux_eq] at hdet
  exact hdet




theorem FKRectSquareWalkLift.not_windingIndependent_of_locallyDisjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (C : FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p))
    (D : FKRectSquareCoverCycleWitness R
      (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a))
    (hdisj : C.cycle.LocallyDisjoint D.cycle) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  intro hind
  apply C.not_independent_of_locallyDisjoint D hdisj
  exact (hw.closed_developedIndependent_iff R hz).mpr hind

end

end StatMech.FrontierD
