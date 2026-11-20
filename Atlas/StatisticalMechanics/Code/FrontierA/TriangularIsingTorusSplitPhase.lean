/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSplitEmbedding
import Code.FrontierA.TriangularIsingTorusFacePrimitive





namespace StatMech.FrontierA

open SimpleGraph



def triangularTorusSplitIncreasingDirection : Fin 6 -> Fin 6 :=
  ![0, 3, 5, 4, 1, 0]


def triangularTorusSplitInternalDirection (a b : Fin 6) : Fin 6 :=
  if (triangularTorusDirectionRank a).val <
      (triangularTorusDirectionRank b).val then
    triangularTorusSplitIncreasingDirection a
  else
    triangularTorusDirectionReverse
      (triangularTorusSplitIncreasingDirection b)


noncomputable def triangularTorusSplitDartDirection
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) : Fin 6 :=
  if kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm then
    triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.fst)
  else
    triangularTorusSplitInternalDirection
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst))
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd))

theorem triangularTorusSplitEmbedHom_mapDart_direction
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) :
    triangularTorusGraphDartDirection (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d) =
      triangularTorusSplitDartDirection L d := by
  classical
  by_cases hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · calc
      triangularTorusGraphDartDirection (3 * L)
          ((triangularTorusSplitEmbedHom L).mapDart d) =
          triangularTorusGraphDartDirection (3 * L)
            (triangularTorusDartEquiv (3 * L)
              (triangularTorusSplitEmbedVertex L d.fst,
                triangularTorusGraphDartDirection L
                  (kwDartOfPort (triangularTorusGraph L) d.fst))) := by
            rw [triangularTorusSplitEmbedHom_mapDart_of_matching L d hmatching]
      _ = triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst) :=
        triangularTorusGraphDartDirection_dartEquiv _ _
      _ = triangularTorusSplitDartDirection L d := by
        simp [triangularTorusSplitDartDirection, hmatching]
  · have hint := (kwOrderedDartPortSplitGraph_adj
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
        d.fst d.snd).mp d.adj |>.resolve_left hmatching
    generalize ha : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.fst) = a
    generalize hb : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) d.snd) = b
    let c := triangularTorusSplitInternalDirection a b
    have hembed : triangularTorusSplitEmbedVertex L d.snd =
        triangularTorusSplitEmbedVertex L d.fst +
          (((triangularIntStep c).1 : ZMod (3 * L)),
            ((triangularIntStep c).2 : ZMod (3 * L))) := by
      have howner : d.fst.1 = d.snd.1 := hint.1
      have hrank : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hint.2
      rw [triangularTorusSplitEmbedVertex_eq_cast,
        triangularTorusSplitEmbedVertex_eq_cast, ← howner]
      rw [ha, hb]
      apply Prod.ext
      · change (3 : ZMod (3 * L)) * ZMod.cast d.fst.1.1 +
            ((triangularTorusSplitOffset b).1 : ZMod (3 * L)) =
          ((3 : ZMod (3 * L)) * ZMod.cast d.fst.1.1 +
            ((triangularTorusSplitOffset a).1 : ZMod (3 * L))) +
              ((triangularIntStep c).1 : ZMod (3 * L))
        rcases hrank with hrank | hrank <;>
          fin_cases a <;> fin_cases b <;>
          simp [triangularTorusDirectionRank,
            triangularTorusSplitInternalDirection,
            triangularTorusSplitIncreasingDirection,
            triangularTorusSplitOffset, triangularTorusDirectionReverse,
            triangularIntStep, c] at hrank ⊢ <;> ring
      · change (3 : ZMod (3 * L)) * ZMod.cast d.fst.1.2 +
            ((triangularTorusSplitOffset b).2 : ZMod (3 * L)) =
          ((3 : ZMod (3 * L)) * ZMod.cast d.fst.1.2 +
            ((triangularTorusSplitOffset a).2 : ZMod (3 * L))) +
              ((triangularIntStep c).2 : ZMod (3 * L))
        rcases hrank with hrank | hrank <;>
          fin_cases a <;> fin_cases b <;>
          simp [triangularTorusDirectionRank,
            triangularTorusSplitInternalDirection,
            triangularTorusSplitIncreasingDirection,
            triangularTorusSplitOffset, triangularTorusDirectionReverse,
            triangularIntStep, c] at hrank ⊢ <;> ring
    have hdart : (triangularTorusSplitEmbedHom L).mapDart d =
        triangularTorusDartEquiv (3 * L)
          (triangularTorusSplitEmbedVertex L d.fst, c) := by
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · rfl
      · change triangularTorusSplitEmbedVertex L d.snd = _
        rw [hembed]
        have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep
          (3 * L) (triangularTorusDartEquiv (3 * L)
            (triangularTorusSplitEmbedVertex L d.fst, c))
        rw [triangularTorusGraphDartDirection_dartEquiv] at hsnd
        exact hsnd.symm
    rw [hdart, triangularTorusGraphDartDirection_dartEquiv]
    simp [triangularTorusSplitDartDirection, hmatching, c, ha, hb]



def triangularTorusSplitIncreasingGaugeExponent : Fin 6 -> Nat :=
  ![0, 2, 1, 5, 0, 4]


def triangularTorusSplitDecreasingGaugeExponent : Fin 6 -> Nat :=
  ![1, 13, 12, 0, 0, 14]


noncomputable def triangularTorusSplitInternalGauge
    (rho : Complex) (a b : Fin 6) : Complex :=
  if (triangularTorusDirectionRank a).val <
      (triangularTorusDirectionRank b).val then
    rho ^ triangularTorusSplitIncreasingGaugeExponent a
  else
    rho ^ triangularTorusSplitDecreasingGaugeExponent a

theorem triangularSplit_entry_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b : Fin 6)
    (hadj : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val) :
    triangularKacWardTurnMatrix rho (triangularTorusDirectionReverse a)
        (triangularTorusSplitInternalDirection a b) =
      (if (triangularTorusDirectionRank a).val <
          (triangularTorusDirectionRank b).val then
        -Complex.I *
          (rho ^ triangularTorusDirectionSignedAngle a)⁻¹
      else
        Complex.I *
          (rho ^ triangularTorusDirectionSignedAngle a)⁻¹) *
        triangularTorusSplitInternalGauge rho a b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hadj ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

theorem triangularSplit_exit_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b : Fin 6)
    (hadj : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val) :
    triangularKacWardTurnMatrix rho
        (triangularTorusSplitInternalDirection a b) b =
      (triangularTorusSplitInternalGauge rho a b)⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hadj ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

theorem triangularSplit_internal_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b c : Fin 6)
    (hab : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val)
    (hbc : (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank c).val ∨
        (triangularTorusDirectionRank c).val + 1 =
          (triangularTorusDirectionRank b).val)
    (hmono : ((triangularTorusDirectionRank a).val <
          (triangularTorusDirectionRank b).val ∧
        (triangularTorusDirectionRank b).val <
          (triangularTorusDirectionRank c).val) ∨
      ((triangularTorusDirectionRank b).val <
          (triangularTorusDirectionRank a).val ∧
        (triangularTorusDirectionRank c).val <
          (triangularTorusDirectionRank b).val)) :
    triangularKacWardTurnMatrix rho
        (triangularTorusSplitInternalDirection a b)
        (triangularTorusSplitInternalDirection b c) =
      (triangularTorusSplitInternalGauge rho a b)⁻¹ *
        triangularTorusSplitInternalGauge rho b c := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [triangularTorusDirectionRank,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hab hbc hmono ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

noncomputable def triangularTorusSplitPhaseGauge
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) : Complex :=
  if kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm then 1
  else
    triangularTorusSplitInternalGauge rho
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst))
      (triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd))

theorem triangularTorusSplitPhaseGauge_ne_zero
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) :
    triangularTorusSplitPhaseGauge L rho d ≠ 0 := by
  unfold triangularTorusSplitPhaseGauge
  split
  · norm_num
  · unfold triangularTorusSplitInternalGauge
    split <;> exact pow_ne_zero _ (triangularTorusTurnRoot_ne_zero rho hrho)

theorem triangularTorusSplit_embedPhase_eq_phaseGauge
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    triangularTorusGraphPhase (3 * L) rho 1 1
        ((triangularTorusSplitEmbedHom L).mapDart d)
        ((triangularTorusSplitEmbedHom L).mapDart e) =
      kwPhaseGauge (triangularTorusSplitPhaseGauge L rho)
        (kwLocalAngularSplitPhase
          (triangularTorusLocalAngularData L rho hrho)) d e := by
  classical
  rw [triangularTorusGraphPhase_one_one_apply,
    triangularTorusSplitEmbedHom_mapDart_direction,
    triangularTorusSplitEmbedHom_mapDart_direction]
  unfold kwPhaseGauge
  by_cases hd : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective (triangularTorusGraph L)
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        exact Prod.ext hconnect.symm hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · have einfo := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          e.fst e.snd).mp e.adj |>.resolve_left he
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.snd) = b
      have hadj : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using einfo.2
      have hdir : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst) =
          triangularTorusDirectionReverse a := by
        have harev : a = triangularTorusDirectionReverse
            (triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) d.fst)) := by
          calc
            a = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) e.fst) := ha.symm
            _ = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) d.snd) := by
              rw [hconnect]
            _ = triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) d.fst).symm := by
              rw [hd]
            _ = triangularTorusDirectionReverse
                (triangularTorusGraphDartDirection L
                  (kwDartOfPort (triangularTorusGraph L) d.fst)) :=
              triangularTorusGraphDartDirection_symm L _
        let z := triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) d.fst)
        calc
          z = triangularTorusDirectionReverse
              (triangularTorusDirectionReverse z) := by
            exact (triangularOppositeDirection_reverse z).symm
          _ = triangularTorusDirectionReverse a :=
            (congrArg triangularTorusDirectionReverse harev).symm
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, triangularTorusLocalPortRoot,
        triangularTorusLocalPortOrder_rank,
        hd, he, ha, hb, hdir] using
        (triangularSplit_entry_phase rho hrho a b hadj)
  · by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · have dinfo := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          d.fst d.snd).mp d.adj |>.resolve_left hd
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd) = b
      have hadj : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [triangularTorusLocalPortOrder_rank, ha, hb] using dinfo.2
      have hedir : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) e.fst) = b := by
        rw [← hconnect, hb]
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, triangularTorusLocalPortRoot,
        hd, he, ha, hb, hedir] using
        (triangularSplit_exit_phase rho hrho a b hadj)
    · let di : KWOrderedInternalSplitDart (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep (triangularTorusGraph L)
          (triangularTorusLocalPortOrder L) di ei := ⟨hconnect, hne⟩
      have dinfo := kwOrderedInternalSplitDart_adj_data
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L) di
      have einfo := kwOrderedInternalSplitDart_adj_data
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L) ei
      generalize ha : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.fst) = a
      generalize hb : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) d.snd) = b
      generalize hc : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) e.snd) = c
      have hefst : triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) e.fst) = b := by
        rw [← hconnect, hb]
      have hab : (triangularTorusDirectionRank a).val + 1 =
            (triangularTorusDirectionRank b).val ∨
          (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank a).val := by
        simpa [di, triangularTorusLocalPortOrder_rank, ha, hb] using dinfo.2
      have hbc : (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank c).val ∨
          (triangularTorusDirectionRank c).val + 1 =
            (triangularTorusDirectionRank b).val := by
        simpa [ei, triangularTorusLocalPortOrder_rank, hefst, hc] using einfo.2
      have hmono : ((triangularTorusDirectionRank a).val <
            (triangularTorusDirectionRank b).val ∧
          (triangularTorusDirectionRank b).val <
            (triangularTorusDirectionRank c).val) ∨
        ((triangularTorusDirectionRank b).val <
            (triangularTorusDirectionRank a).val ∧
          (triangularTorusDirectionRank c).val <
            (triangularTorusDirectionRank b).val) := by
        by_cases hinc : kwOrderedPortRank (triangularTorusLocalPortOrder L)
            d.fst < kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd
        · left
          refine ⟨?_, ?_⟩
          · simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hinc
          · have heinc := kwOrderedInternalDartStep_rank_lt
              (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
              hstep hinc
            simpa [di, ei, triangularTorusLocalPortOrder_rank,
              hefst, hc] using heinc
        · right
          have hdec : kwOrderedPortRank (triangularTorusLocalPortOrder L)
              d.snd < kwOrderedPortRank (triangularTorusLocalPortOrder L)
                d.fst := by
            have dranks :
                kwOrderedPortRank (triangularTorusLocalPortOrder L) d.fst + 1 =
                    kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd ∨
                  kwOrderedPortRank (triangularTorusLocalPortOrder L) d.snd + 1 =
                    kwOrderedPortRank (triangularTorusLocalPortOrder L) d.fst := by
              simpa [di] using dinfo.2
            rcases dranks with h | h <;> omega
          refine ⟨?_, ?_⟩
          · simpa [triangularTorusLocalPortOrder_rank, ha, hb] using hdec
          · have hedec := kwOrderedInternalDartStep_rank_gt
              (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
              hstep hdec
            simpa [di, ei, triangularTorusLocalPortOrder_rank,
              hefst, hc] using hedec
      simpa [triangularTorusSplitDartDirection,
        triangularTorusSplitPhaseGauge, kwLocalAngularSplitPhase,
        triangularTorusLocalAngularData, hd, he, ha, hb, hefst, hc] using
        (triangularSplit_internal_phase rho hrho a b c hab hbc hmono)

end StatMech.FrontierA
