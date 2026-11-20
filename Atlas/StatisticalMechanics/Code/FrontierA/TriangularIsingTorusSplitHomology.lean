/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSplitEmbedding
import Code.FrontierA.TriangularIsingTorusSeamHomology









namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

theorem triangular_three_valCoord_eq_zero_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    ((3 * z.val + c : Nat) : ZMod (3 * L)) = 0 ↔ z = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_zero] at hv
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (triangularTorusSplitEmbedCoord_lt L z c hc)] at hv
    constructor
    · apply ZMod.val_injective
      rw [ZMod.val_zero]
      omega
    · omega
  · rintro ⟨rfl, rfl⟩
    simp

theorem triangular_three_valCoord_eq_neg_one_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    ((3 * z.val + c : Nat) : ZMod (3 * L)) = -1 ↔ z = -1 ∧ c = 2 := by
  letI : NeZero L := ⟨by have := (Fact.out : 2 < L); omega⟩
  letI : NeZero (3 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (triangularTorusSplitEmbedCoord_lt L z c hc),
      StatMech.Onsager.ons_zmod_val_neg_one] at hv
    have hzval := z.val_lt
    constructor
    · apply ZMod.val_injective
      rw [StatMech.Onsager.ons_zmod_val_neg_one]
      omega
    · omega
  · rintro ⟨rfl, rfl⟩
    have hL := (Fact.out : 2 < L)
    apply ZMod.val_injective
    rw [ZMod.val_natCast,
      Nat.mod_eq_of_lt (triangularTorusSplitEmbedCoord_lt L (-1) 2 (by omega)),
      StatMech.Onsager.ons_zmod_val_neg_one,
      StatMech.Onsager.ons_zmod_val_neg_one]
    omega

theorem triangular_three_zmodCast_eq_zero_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    (3 : ZMod (3 * L)) * ZMod.cast z = 0 ↔ z = 0 := by
  have heq : (3 : ZMod (3 * L)) * ZMod.cast z =
      ((3 * z.val + 0 : Nat) : ZMod (3 * L)) := by
    rw [ZMod.cast_eq_val]
    push_cast
    ring
  rw [heq, triangular_three_valCoord_eq_zero_iff L z 0 (by omega)]
  simp

theorem triangular_three_zmodCast_add_two_eq_neg_one_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    (3 : ZMod (3 * L)) * ZMod.cast z + 2 = -1 ↔ z = -1 := by
  have heq : (3 : ZMod (3 * L)) * ZMod.cast z + 2 =
      ((3 * z.val + 2 : Nat) : ZMod (3 * L)) := by
    rw [ZMod.cast_eq_val]
    push_cast
    ring
  rw [heq, triangular_three_valCoord_eq_neg_one_iff L z 2 (by omega)]
  simp

theorem triangular_three_zmodCast_add_eq_zero_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    (3 : ZMod (3 * L)) * ZMod.cast z + c = 0 ↔ z = 0 ∧ c = 0 := by
  have heq : (3 : ZMod (3 * L)) * ZMod.cast z + c =
      ((3 * z.val + c : Nat) : ZMod (3 * L)) := by
    rw [ZMod.cast_eq_val]
    push_cast
    ring
  rw [heq, triangular_three_valCoord_eq_zero_iff L z c hc]

theorem triangular_three_zmodCast_add_eq_neg_one_iff
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    (3 : ZMod (3 * L)) * ZMod.cast z + c = -1 ↔ z = -1 ∧ c = 2 := by
  have heq : (3 : ZMod (3 * L)) * ZMod.cast z + c =
      ((3 * z.val + c : Nat) : ZMod (3 * L)) := by
    rw [ZMod.cast_eq_val]
    push_cast
    ring
  rw [heq, triangular_three_valCoord_eq_neg_one_iff L z c hc]

theorem triangularTorusSplitEmbed_matching_xWrap_iff
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    let a := triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p)
    ons_xWrap (triangularTorusXMovementDart (3 * L)
      (triangularTorusSplitEmbedVertex L p, a)) ↔
      ons_xWrap (triangularTorusXMovementDart L (p.1, a)) := by
  generalize hpa : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p) = a
  fin_cases a <;>
    simp [triangularTorusXMovementDart,
      triangularTorusXMovementDirection, ons_xWrap,
      triangularTorusSplitEmbedVertex, hpa,
      triangularTorusSplitOffset,
      triangular_three_zmodCast_eq_zero_iff,
      triangular_three_zmodCast_add_two_eq_neg_one_iff]

theorem triangularTorusSplitEmbed_matching_yWrap_iff
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    let a := triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p)
    ons_yWrap (triangularTorusYMovementDart (3 * L)
      (triangularTorusSplitEmbedVertex L p, a)) ↔
      ons_yWrap (triangularTorusYMovementDart L (p.1, a)) := by
  generalize hpa : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p) = a
  fin_cases a <;>
    simp [triangularTorusYMovementDart,
      triangularTorusYMovementDirection, ons_yWrap,
      triangularTorusSplitEmbedVertex, hpa,
      triangularTorusSplitOffset,
      triangular_three_zmodCast_eq_zero_iff,
      triangular_three_zmodCast_add_two_eq_neg_one_iff]

theorem triangularTorusDartEquiv_portDirection
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    triangularTorusDartEquiv L
      (p.1, triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) p)) =
      kwDartOfPort (triangularTorusGraph L) p := by
  apply triangularTorusGraphDartDirection_fst_injective L
  · simp [triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart]
  · rw [triangularTorusGraphDartDirection_dartEquiv]

theorem triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    kwOrderedSplitEdgeProjection d.edge =
      (kwDartOfPort (triangularTorusGraph L) d.fst).edge := by
  have hprod := kwDartOfPort_toProd_of_external
    (triangularTorusGraph L) hmatching
  unfold SimpleGraph.Dart.edge
  rw [kwOrderedSplitEdgeProjection_mk]
  exact (congrArg (fun z => s(z.1, z.2)) hprod).symm

theorem triangularTorusSplitEmbed_matching_xSeam_iff
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    triangularTorusXSeamEdge (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔
      triangularTorusXSeamEdge L (kwOrderedSplitEdgeProjection d.edge) := by
  let a := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) d.fst)
  have hmap := triangularTorusSplitEmbedHom_mapDart_of_matching
    L d hmatching
  change (triangularTorusSplitEmbedHom L).mapDart d =
    triangularTorusDartEquiv (3 * L)
      (triangularTorusSplitEmbedVertex L d.fst, a) at hmap
  have hport := triangularTorusDartEquiv_portDirection L d.fst
  change triangularTorusDartEquiv L (d.fst.1, a) =
    kwDartOfPort (triangularTorusGraph L) d.fst at hport
  calc
    triangularTorusXSeamEdge (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔
        ons_xWrap (triangularTorusXMovementDart (3 * L)
          (triangularTorusSplitEmbedVertex L d.fst, a)) := by
      rw [hmap, triangularTorusXSeamEdge_dart_iff]
    _ ↔ ons_xWrap (triangularTorusXMovementDart L (d.fst.1, a)) :=
      triangularTorusSplitEmbed_matching_xWrap_iff L d.fst
    _ ↔ triangularTorusXSeamEdge L
        (triangularTorusDartEquiv L (d.fst.1, a)).edge :=
      (triangularTorusXSeamEdge_dart_iff L _).symm
    _ ↔ triangularTorusXSeamEdge L
        (kwOrderedSplitEdgeProjection d.edge) := by
      rw [hport,
        triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching
          L d hmatching]

theorem triangularTorusSplitEmbed_matching_ySeam_iff
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    triangularTorusYSeamEdge (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔
      triangularTorusYSeamEdge L (kwOrderedSplitEdgeProjection d.edge) := by
  let a := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) d.fst)
  have hmap := triangularTorusSplitEmbedHom_mapDart_of_matching
    L d hmatching
  change (triangularTorusSplitEmbedHom L).mapDart d =
    triangularTorusDartEquiv (3 * L)
      (triangularTorusSplitEmbedVertex L d.fst, a) at hmap
  have hport := triangularTorusDartEquiv_portDirection L d.fst
  change triangularTorusDartEquiv L (d.fst.1, a) =
    kwDartOfPort (triangularTorusGraph L) d.fst at hport
  calc
    triangularTorusYSeamEdge (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔
        ons_yWrap (triangularTorusYMovementDart (3 * L)
          (triangularTorusSplitEmbedVertex L d.fst, a)) := by
      rw [hmap, triangularTorusYSeamEdge_dart_iff]
    _ ↔ ons_yWrap (triangularTorusYMovementDart L (d.fst.1, a)) :=
      triangularTorusSplitEmbed_matching_yWrap_iff L d.fst
    _ ↔ triangularTorusYSeamEdge L
        (triangularTorusDartEquiv L (d.fst.1, a)).edge :=
      (triangularTorusYSeamEdge_dart_iff L _).symm
    _ ↔ triangularTorusYSeamEdge L
        (kwOrderedSplitEdgeProjection d.edge) := by
      rw [hport,
        triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching
          L d hmatching]

theorem triangularTorusSplitEmbed_matching_edgeClass
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    triangularTorusSurfaceEdgeClass (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge =
      kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
  unfold triangularTorusSurfaceEdgeClass kwOrderedSplitEdgeClass
  apply Prod.ext <;> funext i <;> fin_cases i
  · rw [if_congr (triangularTorusSplitEmbed_matching_xSeam_iff
      L d hmatching) rfl rfl]
  · rw [if_congr (triangularTorusSplitEmbed_matching_ySeam_iff
      L d hmatching) rfl rfl]

theorem triangularTorusSplitEmbed_sameCenter_not_xSeam
    (L : Nat) [Fact (2 < L)]
    (p q : KWDartPort (triangularTorusGraph L)) (hcenter : p.1 = q.1) :
    ¬triangularTorusXSeamEdge (3 * L)
      s(triangularTorusSplitEmbedVertex L p,
        triangularTorusSplitEmbedVertex L q) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hne : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hnod (y z : ZMod (3 * L))
      (h : s(triangularTorusSplitEmbedVertex L p,
          triangularTorusSplitEmbedVertex L q) = s(((0 : ZMod (3 * L)), y), (-1, z))) : False := by
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · have hp0 := congrArg Prod.fst h.1
      have hqm := congrArg Prod.fst h.2
      rw [triangularTorusSplitEmbedVertex_eq_cast] at hp0 hqm
      have hpcenter := (triangular_three_zmodCast_add_eq_zero_iff
        L p.1.1 _ (triangularTorusSplitOffset_fst_lt_three _)).mp hp0 |>.1
      have hqcenter := (triangular_three_zmodCast_add_eq_neg_one_iff
        L q.1.1 _ (triangularTorusSplitOffset_fst_lt_three _)).mp hqm |>.1
      have hc := congrArg Prod.fst hcenter
      rw [hpcenter, hqcenter] at hc
      exact hne hc.symm
    · have hpm := congrArg Prod.fst h.1
      have hq0 := congrArg Prod.fst h.2
      rw [triangularTorusSplitEmbedVertex_eq_cast] at hpm hq0
      have hpcenter := (triangular_three_zmodCast_add_eq_neg_one_iff
        L p.1.1 _ (triangularTorusSplitOffset_fst_lt_three _)).mp hpm |>.1
      have hqcenter := (triangular_three_zmodCast_add_eq_zero_iff
        L q.1.1 _ (triangularTorusSplitOffset_fst_lt_three _)).mp hq0 |>.1
      have hc := congrArg Prod.fst hcenter
      rw [hpcenter, hqcenter] at hc
      exact hne hc
  rintro (hx | hx)
  · rcases hx with ⟨y, hy⟩
    exact hnod y y hy
  · rcases hx with ⟨y, hy⟩
    exact hnod y (y - 1) hy

theorem triangularTorusSplitEmbed_sameCenter_not_ySeam
    (L : Nat) [Fact (2 < L)]
    (p q : KWDartPort (triangularTorusGraph L)) (hcenter : p.1 = q.1) :
    ¬ triangularTorusYSeamEdge (3 * L)
      s(triangularTorusSplitEmbedVertex L p,
        triangularTorusSplitEmbedVertex L q) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hne : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hnod (x z : ZMod (3 * L))
      (h : s(triangularTorusSplitEmbedVertex L p,
          triangularTorusSplitEmbedVertex L q) = s((x, (0 : ZMod (3 * L))), (z, -1))) : False := by
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · have hp0 := congrArg Prod.snd h.1
      have hqm := congrArg Prod.snd h.2
      rw [triangularTorusSplitEmbedVertex_eq_cast] at hp0 hqm
      have hpcenter := (triangular_three_zmodCast_add_eq_zero_iff
        L p.1.2 _ (triangularTorusSplitOffset_snd_lt_three _)).mp hp0 |>.1
      have hqcenter := (triangular_three_zmodCast_add_eq_neg_one_iff
        L q.1.2 _ (triangularTorusSplitOffset_snd_lt_three _)).mp hqm |>.1
      have hc := congrArg Prod.snd hcenter
      rw [hpcenter, hqcenter] at hc
      exact hne hc.symm
    · have hpm := congrArg Prod.snd h.1
      have hq0 := congrArg Prod.snd h.2
      rw [triangularTorusSplitEmbedVertex_eq_cast] at hpm hq0
      have hpcenter := (triangular_three_zmodCast_add_eq_neg_one_iff
        L p.1.2 _ (triangularTorusSplitOffset_snd_lt_three _)).mp hpm |>.1
      have hqcenter := (triangular_three_zmodCast_add_eq_zero_iff
        L q.1.2 _ (triangularTorusSplitOffset_snd_lt_three _)).mp hq0 |>.1
      have hc := congrArg Prod.snd hcenter
      rw [hpcenter, hqcenter] at hc
      exact hne hc
  rintro (hy | hy)
  · rcases hy with ⟨x, hx⟩
    exact hnod x x hx
  · rcases hy with ⟨x, hx⟩
    exact hnod x (x - 1) hx

theorem triangularTorusSplitEmbed_internal_edgeClass
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hinternal : ¬kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    triangularTorusSurfaceEdgeClass (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge =
      kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
  have hadj := d.adj
  rw [kwOrderedDartPortSplitGraph_adj] at hadj
  have hcenter := (hadj.resolve_left hinternal).1
  have hx : ¬ triangularTorusXSeamEdge (3 * L)
      ((triangularTorusSplitEmbedHom L).mapDart d).edge := by
    change ¬ triangularTorusXSeamEdge (3 * L)
      s(triangularTorusSplitEmbedVertex L d.fst,
        triangularTorusSplitEmbedVertex L d.snd)
    exact triangularTorusSplitEmbed_sameCenter_not_xSeam
      L d.fst d.snd hcenter
  have hy : ¬ triangularTorusYSeamEdge (3 * L)
      ((triangularTorusSplitEmbedHom L).mapDart d).edge := by
    change ¬ triangularTorusYSeamEdge (3 * L)
      s(triangularTorusSplitEmbedVertex L d.fst,
        triangularTorusSplitEmbedVertex L d.snd)
    exact triangularTorusSplitEmbed_sameCenter_not_ySeam
      L d.fst d.snd hcenter
  have hproj : kwOrderedSplitEdgeProjection d.edge = s(d.fst.1, d.fst.1) := by
    unfold SimpleGraph.Dart.edge
    rw [kwOrderedSplitEdgeProjection_mk, hcenter]
  rw [kwOrderedSplitEdgeClass, hproj,
    triangularTorusSurfaceEdgeClass_diag]
  change
    (fun _ => if triangularTorusXSeamEdge (3 * L)
          ((triangularTorusSplitEmbedHom L).mapDart d).edge then 1 else 0,
      fun _ => if triangularTorusYSeamEdge (3 * L)
          ((triangularTorusSplitEmbedHom L).mapDart d).edge then 1 else 0) = 0
  rw [if_neg hx, if_neg hy]
  rfl



theorem triangularTorusSplitEmbed_edgeClass
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart) :
    triangularTorusSurfaceEdgeClass (3 * L)
        ((triangularTorusSplitEmbedHom L).mapDart d).edge =
      kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
  by_cases hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · exact triangularTorusSplitEmbed_matching_edgeClass L d hmatching
  · exact triangularTorusSplitEmbed_internal_edgeClass L d hmatching



theorem triangularTorusSplitEmbedWalk_surfaceHomology
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass (3 * L))
        (triangularTorusSplitEmbedWalk L p).edges.toFinset =
      surfaceSubgraphHomology
        (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
        p.edges.toFinset := by
  classical
  have hedges : (triangularTorusSplitEmbedWalk L p).edges.toFinset =
      p.edges.toFinset.image (Sym2.map (triangularTorusSplitEmbedHom L)) := by
    ext edge
    simp [triangularTorusSplitEmbedWalk_edges]
  rw [hedges]
  unfold surfaceSubgraphHomology
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro edge hedge
    rw [List.mem_toFinset, SimpleGraph.Walk.edges, List.mem_map] at hedge
    rcases hedge with ⟨d, hd, rfl⟩
    simpa using triangularTorusSplitEmbed_edgeClass L d
  · intro edge _ edge' _ heq
    exact Sym2.map.injective (triangularTorusSplitEmbedVertex_injective L) heq

end StatMech.FrontierA
