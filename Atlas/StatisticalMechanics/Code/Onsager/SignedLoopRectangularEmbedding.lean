/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopRectangularDualPath
import Code.FrontierA.TriangularIsingTorusCycleHolonomy





open Set SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section


def ons_rectDualIntPoint {M N : Nat} (p : ons_RectDualVertex M N) : Int × Int :=
  (p.1.val, p.2.val)

theorem ons_rectDualIntPoint_injective {M N : Nat} :
    Function.Injective (ons_rectDualIntPoint : ons_RectDualVertex M N -> Int × Int) := by
  intro p q h
  unfold ons_rectDualIntPoint at h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg Prod.fst h
    exact Int.ofNat_inj.mp hx
  · have hy := congrArg Prod.snd h
    exact Int.ofNat_inj.mp hy


def ons_rectDualComplexPoint {M N : Nat}
    (p : ons_RectDualVertex M N) : Complex :=
  triangularIntPoint (ons_rectDualIntPoint p)

theorem ons_rectDualComplexPoint_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualComplexPoint : ons_RectDualVertex M N -> Complex) :=
  triangularIntPoint_injective.comp ons_rectDualIntPoint_injective



def ons_rectDualDartDirection {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) : Fin 6 :=
  if dart.snd.1.val < dart.fst.1.val then 0
  else if dart.fst.1.val < dart.snd.1.val then 1
  else if dart.snd.2.val < dart.fst.2.val then 2 else 3


theorem ons_rectDualIntPoint_snd_eq_add_step {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualIntPoint dart.snd =
      ons_rectDualIntPoint dart.fst +
        triangularIntStep (ons_rectDualDartDirection dart) := by
  have hadj : ons_rectDualAdj M N dart.fst dart.snd := dart.adj
  rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hne : dart.fst.1.val ≠ dart.snd.1.val := by
      intro h
      simp [h] at hx
    by_cases hlt : dart.snd.1.val < dart.fst.1.val
    · have hval : dart.fst.1.val = dart.snd.1.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hx
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection, hlt,
        triangularIntStep, hy, Prod.ext_iff]
      omega
    · have hlt' : dart.fst.1.val < dart.snd.1.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne
      have hval : dart.snd.1.val = dart.fst.1.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt')] at hx
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection, hlt, hlt',
        triangularIntStep, hy, Prod.ext_iff]
      omega
  · have hne : dart.fst.2.val ≠ dart.snd.2.val := by
      intro h
      simp [h] at hy
    have hxVal : dart.fst.1.val = dart.snd.1.val :=
      congrArg Fin.val hx
    by_cases hlt : dart.snd.2.val < dart.fst.2.val
    · have hval : dart.fst.2.val = dart.snd.2.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hy
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection,
        hlt, triangularIntStep, hxVal, Prod.ext_iff]
      omega
    · have hlt' : dart.fst.2.val < dart.snd.2.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne
      have hval : dart.snd.2.val = dart.fst.2.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt')] at hy
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection,
        hlt, triangularIntStep, hxVal, Prod.ext_iff]
      omega



def ons_rectDualStraightLineEmbedding (M N : Nat) :
    KWStraightLineEmbedding (ons_rectDualGraph M N) where
  vertex := ons_rectDualComplexPoint
  vertex_injective := ons_rectDualComplexPoint_injective
  vertex_not_strictly_between := by
    intro dart v hvfst hvsnd hbetween
    let a := ons_rectDualDartDirection dart
    have ha : ons_rectDualIntPoint dart.snd =
        ons_rectDualIntPoint dart.fst + triangularIntStep a :=
      ons_rectDualIntPoint_snd_eq_add_step dart
    apply triangularIntPoint_not_strictly_between_step
      (ons_rectDualIntPoint dart.fst) (ons_rectDualIntPoint v) a
    · intro h
      exact hvfst (ons_rectDualIntPoint_injective h)
    · intro h
      apply hvsnd
      apply ons_rectDualIntPoint_injective
      exact h.trans ha.symm
    · simpa only [ons_rectDualComplexPoint, ← ha] using hbetween
  edgeInteriors_disjoint := by
    intro dart next hedge
    rw [Set.disjoint_left]
    intro z hz hz'
    have hzStep : Sbtw Real
        (triangularIntPoint (ons_rectDualIntPoint dart.fst)) z
        (triangularIntPoint (ons_rectDualIntPoint dart.fst +
          triangularIntStep (ons_rectDualDartDirection dart))) := by
      rw [← ons_rectDualIntPoint_snd_eq_add_step]
      exact hz
    have hzStep' : Sbtw Real
        (triangularIntPoint (ons_rectDualIntPoint next.fst)) z
        (triangularIntPoint (ons_rectDualIntPoint next.fst +
          triangularIntStep (ons_rectDualDartDirection next))) := by
      rw [← ons_rectDualIntPoint_snd_eq_add_step]
      exact hz'
    have hedgeInt := triangular_open_intersection_edge_eq
      (ons_rectDualIntPoint dart.fst) (ons_rectDualIntPoint next.fst)
      (ons_rectDualDartDirection dart) (ons_rectDualDartDirection next)
      z hzStep hzStep'
    rw [← ons_rectDualIntPoint_snd_eq_add_step,
      ← ons_rectDualIntPoint_snd_eq_add_step, Sym2.eq_iff] at hedgeInt
    apply hedge
    change s(dart.fst, dart.snd) = s(next.fst, next.snd)
    rw [Sym2.eq_iff]
    rcases hedgeInt with h | h
    · exact Or.inl ⟨ons_rectDualIntPoint_injective h.1,
        ons_rectDualIntPoint_injective h.2⟩
    · exact Or.inr ⟨ons_rectDualIntPoint_injective h.1,
        ons_rectDualIntPoint_injective h.2⟩


def ons_rectDualPathCanonicalDefectKWDet {M N : Nat}
    (path : ons_RectDualPath M N) (x : Real) : Complex :=
  ons_rectDualPathDefectKWDet (ons_rectDualStraightLineEmbedding M N) path x


def ons_rectDualCanonicalKWDet (M N : Nat) (x : Real) : Complex :=
  ons_rectDualKWDet (ons_rectDualStraightLineEmbedding M N) x

theorem coe_ons_rectDual_X_sq_eq_canonicalKWDet
    (M N : Nat) (x : Real) :
    (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 =
      ons_rectDualCanonicalKWDet M N x :=
  coe_ons_rectDual_X_sq_eq_kwDet
    (ons_rectDualStraightLineEmbedding M N) x

theorem coe_ons_rectDualPath_sourceX_sq_eq_canonicalDefectKWDet
    {M N : Nat} (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    (ons_sourceX (ons_rectDualGraph M N)
        {path.source, path.target} x : Complex) ^ 2 =
      (x : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path x :=
  coe_ons_rectDualPath_sourceX_sq_eq_defect_kwDet
    (ons_rectDualStraightLineEmbedding M N) path hx

theorem ons_rectDualPath_canonicalDefectKWDet_eq_signedLoopObservable
    {M N : Nat} (path : ons_RectDualPath M N) {x : Real} (hx : x ≠ 0) :
    ons_rectDualPathCanonicalDefectKWDet path x =
      ons_rectDualPathSignedLoopObservable path x :=
  ons_rectDualPath_defectKWDet_eq_signedLoopObservable
    (ons_rectDualStraightLineEmbedding M N) path hx

theorem coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
    {M N : Nat} (path : ons_RectDualPath M N)
    {beta : Real} (hbeta : 0 < beta) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((Real.tanh beta : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path (Real.tanh beta)) /
        ons_rectDualCanonicalKWDet M N (Real.tanh beta) :=
  coe_ons_rectDualPath_finiteTwoPoint_sq_eq_kwDet_ratio
    (ons_rectDualStraightLineEmbedding M N) path hbeta

theorem coe_ons_rectDualPath_criticalTwoPoint_sq_eq_canonicalKWDet_ratio
    {M N : Nat} (path : ons_RectDualPath M N) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) ons_betaC 0
        (fun spin => StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ((ons_signedLoopCriticalWeight : Complex) ^
          (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path
          ons_signedLoopCriticalWeight) /
        ons_rectDualCanonicalKWDet M N ons_signedLoopCriticalWeight :=
  coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
    (ons_rectDualStraightLineEmbedding M N) path

end

end StatMech.Onsager
