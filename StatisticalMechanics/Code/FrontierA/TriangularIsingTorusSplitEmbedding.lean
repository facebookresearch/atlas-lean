/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusLocalAngularSplit










namespace StatMech.FrontierA

open SimpleGraph

instance triangularTorusTriple_fact
    (L : Nat) [Fact (2 < L)] : Fact (2 < 3 * L) :=
  ⟨by have := (Fact.out : 2 < L); omega⟩



def triangularTorusSplitOffset : Fin 6 -> Nat × Nat :=
  ![(0, 1), (2, 1), (1, 0), (1, 2), (0, 0), (2, 2)]

theorem triangularTorusSplitOffset_injective :
    Function.Injective triangularTorusSplitOffset := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusSplitOffset] at h ⊢

@[simp] theorem triangularTorusSplitOffset_fst_lt_three (a : Fin 6) :
    (triangularTorusSplitOffset a).1 < 3 := by
  fin_cases a <;> decide

@[simp] theorem triangularTorusSplitOffset_snd_lt_three (a : Fin 6) :
    (triangularTorusSplitOffset a).2 < 3 := by
  fin_cases a <;> decide

theorem triangularTorusSplitEmbedCoord_lt
    (L : Nat) [Fact (2 < L)] (z : ZMod L) (c : Nat) (hc : c < 3) :
    3 * z.val + c < 3 * L := by
  have hz := z.val_lt
  omega


noncomputable def triangularTorusSplitEmbedVertex
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    ZMod (3 * L) × ZMod (3 * L) :=
  let a := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p)
  ((3 * p.1.1.val + (triangularTorusSplitOffset a).1 : Nat),
    (3 * p.1.2.val + (triangularTorusSplitOffset a).2 : Nat))

@[simp] theorem triangularTorusSplitEmbedVertex_fst_val
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    (triangularTorusSplitEmbedVertex L p).1.val =
      3 * p.1.1.val +
        (triangularTorusSplitOffset
          (triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) p))).1 := by
  unfold triangularTorusSplitEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (triangularTorusSplitEmbedCoord_lt L _ _
    (triangularTorusSplitOffset_fst_lt_three _))

@[simp] theorem triangularTorusSplitEmbedVertex_snd_val
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    (triangularTorusSplitEmbedVertex L p).2.val =
      3 * p.1.2.val +
        (triangularTorusSplitOffset
          (triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) p))).2 := by
  unfold triangularTorusSplitEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (triangularTorusSplitEmbedCoord_lt L _ _
    (triangularTorusSplitOffset_snd_lt_three _))

theorem triangularTorusGraphDartDirection_fst_injective
    (L : Nat) [Fact (2 < L)]
    {d e : (triangularTorusGraph L).Dart}
    (hfst : d.fst = e.fst)
    (hdir : triangularTorusGraphDartDirection L d =
      triangularTorusGraphDartDirection L e) : d = e := by
  apply (triangularTorusDartEquiv L).symm.injective
  apply Prod.ext
  · have hd := congrArg (fun z : (triangularTorusGraph L).Dart => z.fst)
      ((triangularTorusDartEquiv L).apply_symm_apply d)
    have he := congrArg (fun z : (triangularTorusGraph L).Dart => z.fst)
      ((triangularTorusDartEquiv L).apply_symm_apply e)
    exact hd.trans (hfst.trans he.symm)
  · exact hdir


theorem triangularTorusSplitEmbedVertex_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (triangularTorusSplitEmbedVertex L) := by
  intro p q hpq
  let a := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p)
  let b := triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) q)
  have hx := congrArg (fun z => z.1.val) hpq
  have hy := congrArg (fun z => z.2.val) hpq
  simp only [triangularTorusSplitEmbedVertex_fst_val,
    triangularTorusSplitEmbedVertex_snd_val] at hx hy
  change 3 * p.1.1.val + (triangularTorusSplitOffset a).1 =
    3 * q.1.1.val + (triangularTorusSplitOffset b).1 at hx
  change 3 * p.1.2.val + (triangularTorusSplitOffset a).2 =
    3 * q.1.2.val + (triangularTorusSplitOffset b).2 at hy
  have hxmod := congrArg (fun n : Nat => n % 3) hx
  have hymod := congrArg (fun n : Nat => n % 3) hy
  simp [Nat.add_mod, Nat.mul_mod,
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_fst_lt_three a),
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_fst_lt_three b)] at hxmod
  simp [Nat.add_mod, Nat.mul_mod,
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_snd_lt_three a),
    Nat.mod_eq_of_lt (triangularTorusSplitOffset_snd_lt_three b)] at hymod
  have hab : a = b := triangularTorusSplitOffset_injective
    (Prod.ext hxmod hymod)
  subst b
  have hcenter : p.1 = q.1 := by
    apply Prod.ext <;> apply ZMod.val_injective <;> omega
  apply kwDartOfPort_injective (triangularTorusGraph L)
  apply triangularTorusGraphDartDirection_fst_injective L
  · simpa using hcenter
  · exact hab

theorem triangular_three_zmodCast_add_one
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    (3 : ZMod (3 * L)) * ZMod.cast z + 3 =
      3 * ZMod.cast (z + 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = -1
  · rw [hz, neg_add_cancel, ZMod.cast_zero, mul_zero]
    rw [ZMod.cast_eq_val, StatMech.Onsager.ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (3 : ZMod (3 * L)) * (L : ZMod (3 * L)) = 0 := by
      calc
        (3 : ZMod (3 * L)) * (L : ZMod (3 * L)) =
            ((3 * L : Nat) : ZMod (3 * L)) := (Nat.cast_mul 3 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination hmod
  · have hv : z.val + 1 < L := by
      have hne : z.val ≠ L - 1 := by
        intro h
        apply hz
        apply ZMod.val_injective
        rw [h, StatMech.Onsager.ons_zmod_val_neg_one]
      have hzlt := z.val_lt
      omega
    have hval : (z + 1).val = z.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    ring

theorem triangular_three_zmodCast_sub_one
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    (3 : ZMod (3 * L)) * ZMod.cast z - 3 =
      3 * ZMod.cast (z - 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = 0
  · rw [hz, zero_sub, ZMod.cast_zero, mul_zero, zero_sub]
    rw [ZMod.cast_eq_val, StatMech.Onsager.ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (3 : ZMod (3 * L)) * (L : ZMod (3 * L)) = 0 := by
      calc
        (3 : ZMod (3 * L)) * (L : ZMod (3 * L)) =
            ((3 * L : Nat) : ZMod (3 * L)) := (Nat.cast_mul 3 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination -hmod
  · have hzval : 1 ≤ z.val := by
      have : z.val ≠ 0 := by
        intro h
        exact hz ((ZMod.val_eq_zero z).mp h)
      omega
    have hval : (z - 1).val = z.val - 1 := by
      have hone : (1 : ZMod L).val ≤ z.val := by
        rw [ZMod.val_one]
        exact hzval
      rw [ZMod.val_sub hone, ZMod.val_one]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    rw [Nat.cast_sub hzval]
    ring

theorem triangular_three_zmodCast_add_one_rearranged
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    (ZMod.cast (1 + z) : ZMod (3 * L)) * 3 =
      3 + ZMod.cast z * 3 := by
  calc
    (ZMod.cast (1 + z) : ZMod (3 * L)) * 3 =
        3 * ZMod.cast (z + 1) := by
          rw [add_comm 1 z]
          exact mul_comm _ _
    _ = 3 * ZMod.cast z + 3 := (triangular_three_zmodCast_add_one L z).symm
    _ = 3 + ZMod.cast z * 3 := by ring

theorem triangular_three_zmodCast_sub_one_rearranged
    (L : Nat) [Fact (2 < L)] (z : ZMod L) :
    2 + (ZMod.cast (-1 + z) : ZMod (3 * L)) * 3 =
      -1 + ZMod.cast z * 3 := by
  calc
    2 + (ZMod.cast (-1 + z) : ZMod (3 * L)) * 3 =
        2 + 3 * ZMod.cast (z - 1) := by
          rw [show -1 + z = z - 1 by ring]
          congr 1
          exact mul_comm _ _
    _ = 2 + (3 * ZMod.cast z - 3) := by
      rw [← triangular_three_zmodCast_sub_one L z]
    _ = -1 + ZMod.cast z * 3 := by ring

theorem triangularTorusSplitEmbedVertex_eq_cast
    (L : Nat) [Fact (2 < L)]
    (p : KWDartPort (triangularTorusGraph L)) :
    triangularTorusSplitEmbedVertex L p =
      ((3 : ZMod (3 * L)) * ZMod.cast p.1.1 +
          (triangularTorusSplitOffset
            (triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) p))).1,
        (3 : ZMod (3 * L)) * ZMod.cast p.1.2 +
          (triangularTorusSplitOffset
            (triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) p))).2) := by
  unfold triangularTorusSplitEmbedVertex
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val]
  push_cast
  apply Prod.ext <;> ring

theorem triangularTorusDirectionStep_add_intStep
    (L : Nat) (a : Fin 6) :
    triangularTorusDirectionStep L a +
        (((triangularIntStep a).1 : ZMod L),
          ((triangularIntStep a).2 : ZMod L)) = 0 := by
  fin_cases a <;>
    simp [triangularTorusDirectionStep, triangularIntStep] <;> ring

@[simp] theorem triangularTorusGraphDartDirection_dartEquiv
    (L : Nat) [Fact (2 < L)] (a : triangularTorusDart L) :
    triangularTorusGraphDartDirection L (triangularTorusDartEquiv L a) = a.2 := by
  unfold triangularTorusGraphDartDirection
  rw [Equiv.symm_apply_apply]

theorem triangularTorusGraphDart_snd_eq_fst_add_intStep
    (L : Nat) [Fact (2 < L)]
    (d : (triangularTorusGraph L).Dart) :
    d.snd = d.fst +
      (((triangularIntStep
          (triangularTorusGraphDartDirection L d)).1 : ZMod L),
        ((triangularIntStep
          (triangularTorusGraphDartDirection L d)).2 : ZMod L)) := by
  let a := (triangularTorusDartEquiv L).symm d
  have hd : triangularTorusDartEquiv L a = d :=
    (triangularTorusDartEquiv L).apply_symm_apply d
  rw [← hd]
  unfold triangularTorusGraphDartDirection
  rw [Equiv.symm_apply_apply, triangularTorusDartEquiv_apply]
  change a.1 - triangularTorusDirectionStep L a.2 =
    a.1 + (((triangularIntStep a.2).1 : ZMod L),
      ((triangularIntStep a.2).2 : ZMod L))
  have hstep := triangularTorusDirectionStep_add_intStep L a.2
  rw [sub_eq_add_neg]
  congr 1
  exact neg_eq_iff_add_eq_zero.mpr hstep

theorem triangularTorusAdj_add_intStep
    (N : Nat) [Fact (2 < N)]
    (z : ZMod N × ZMod N) (a : Fin 6) :
    (triangularTorusGraph N).Adj z
      (z + (((triangularIntStep a).1 : ZMod N),
        ((triangularIntStep a).2 : ZMod N))) := by
  rcases z with ⟨x, y⟩
  fin_cases a <;>
    simp [triangularTorusGraph, triangularTorusAdj,
      StatMech.Onsager.onsTorusAdj, triangularIntStep] <;> ring

theorem triangularTorusSplitOffset_adj_of_rank
    (N : Nat) [Fact (2 < N)] (z : ZMod N × ZMod N)
    (a b : Fin 6)
    (hrank : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val) :
    (triangularTorusGraph N).Adj
      (z + (((triangularTorusSplitOffset a).1 : ZMod N),
        ((triangularTorusSplitOffset a).2 : ZMod N)))
      (z + (((triangularTorusSplitOffset b).1 : ZMod N),
        ((triangularTorusSplitOffset b).2 : ZMod N))) := by
  rcases z with ⟨x, y⟩
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank] at hrank ⊢ <;>
    simp [triangularTorusSplitOffset, triangularTorusGraph,
      triangularTorusAdj, StatMech.Onsager.onsTorusAdj] <;>
    ring_nf <;> tauto



theorem triangularTorusSplitEmbedVertex_matching
    (L : Nat) [Fact (2 < L)]
    {p q : KWDartPort (triangularTorusGraph L)}
    (hmatch : kwDartOfPort (triangularTorusGraph L) q =
      (kwDartOfPort (triangularTorusGraph L) p).symm) :
    triangularTorusSplitEmbedVertex L q =
      triangularTorusSplitEmbedVertex L p +
        (((triangularIntStep
          (triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) p))).1 : ZMod (3 * L)),
         ((triangularIntStep
          (triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) p))).2 : ZMod (3 * L))) := by
  generalize hpa : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) p) = a
  have hcenter : q.1 = p.1 +
      (((triangularIntStep a).1 : ZMod L),
        ((triangularIntStep a).2 : ZMod L)) := by
    have hfst : q.1 =
        (kwDartOfPort (triangularTorusGraph L) p).snd := by
      calc
        q.1 = (kwDartOfPort (triangularTorusGraph L) q).fst :=
          (kwDartOfPort_fst (triangularTorusGraph L) q).symm
        _ = ((kwDartOfPort (triangularTorusGraph L) p).symm).fst :=
          congrArg (fun d : (triangularTorusGraph L).Dart => d.fst) hmatch
        _ = (kwDartOfPort (triangularTorusGraph L) p).snd := rfl
    have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep L
      (kwDartOfPort (triangularTorusGraph L) p)
    simpa [hpa] using hfst.trans hsnd
  have hdir : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) q) =
      triangularTorusDirectionReverse a := by
    calc
      triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) q) =
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) p).symm :=
        congrArg (triangularTorusGraphDartDirection L) hmatch
      _ = triangularTorusDirectionReverse
            (triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) p)) :=
        triangularTorusGraphDartDirection_symm L _
      _ = triangularTorusDirectionReverse a := congrArg _ hpa
  rw [triangularTorusSplitEmbedVertex_eq_cast,
    triangularTorusSplitEmbedVertex_eq_cast, hcenter]
  fin_cases a
  all_goals simp [hpa, hdir, triangularTorusSplitOffset,
    triangularTorusDirectionReverse, triangularIntStep]
  · rw [show p.1.1 + -1 = p.1.1 - 1 by ring,
      ← triangular_three_zmodCast_sub_one L p.1.1]
    ring
  · rw [← triangular_three_zmodCast_add_one L p.1.1]
    ring
  · rw [show p.1.2 + -1 = p.1.2 - 1 by ring,
      ← triangular_three_zmodCast_sub_one L p.1.2]
    ring
  · rw [← triangular_three_zmodCast_add_one L p.1.2]
    ring
  · constructor
    · rw [show p.1.1 + -1 = p.1.1 - 1 by ring,
        ← triangular_three_zmodCast_sub_one L p.1.1]
      ring
    · rw [show p.1.2 + -1 = p.1.2 - 1 by ring,
        ← triangular_three_zmodCast_sub_one L p.1.2]
      ring
  · constructor
    · rw [← triangular_three_zmodCast_add_one L p.1.1]
      ring
    · rw [← triangular_three_zmodCast_add_one L p.1.2]
      ring



theorem triangularTorusSplitEmbedVertex_adj
    (L : Nat) [Fact (2 < L)]
    {p q : KWDartPort (triangularTorusGraph L)}
    (hpq : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Adj p q) :
    (triangularTorusGraph (3 * L)).Adj
      (triangularTorusSplitEmbedVertex L p)
      (triangularTorusSplitEmbedVertex L q) := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  rcases hpq with hmatch | hint
  · generalize hpa : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p) = a
    have hcenter : q.1 = p.1 +
        (((triangularIntStep a).1 : ZMod L),
          ((triangularIntStep a).2 : ZMod L)) := by
      have hfst : q.1 =
          (kwDartOfPort (triangularTorusGraph L) p).snd := by
        calc
          q.1 = (kwDartOfPort (triangularTorusGraph L) q).fst :=
            (kwDartOfPort_fst (triangularTorusGraph L) q).symm
          _ = ((kwDartOfPort (triangularTorusGraph L) p).symm).fst :=
            congrArg (fun d : (triangularTorusGraph L).Dart => d.fst) hmatch
          _ = (kwDartOfPort (triangularTorusGraph L) p).snd := rfl
      have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep L
        (kwDartOfPort (triangularTorusGraph L) p)
      simpa [hpa] using hfst.trans hsnd
    have hdir : triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) q) =
        triangularTorusDirectionReverse a := by
      calc
        triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) q) =
            triangularTorusGraphDartDirection L
              (kwDartOfPort (triangularTorusGraph L) p).symm :=
          congrArg (triangularTorusGraphDartDirection L) hmatch
        _ = triangularTorusDirectionReverse
              (triangularTorusGraphDartDirection L
                (kwDartOfPort (triangularTorusGraph L) p)) :=
          triangularTorusGraphDartDirection_symm L _
        _ = triangularTorusDirectionReverse a := congrArg _ hpa
    have hembed : triangularTorusSplitEmbedVertex L q =
        triangularTorusSplitEmbedVertex L p +
          (((triangularIntStep a).1 : ZMod (3 * L)),
            ((triangularIntStep a).2 : ZMod (3 * L))) := by
      rw [triangularTorusSplitEmbedVertex_eq_cast,
        triangularTorusSplitEmbedVertex_eq_cast, hcenter]
      fin_cases a
      all_goals simp [hpa, hdir, triangularTorusSplitOffset,
        triangularTorusDirectionReverse, triangularIntStep]
      · rw [show p.1.1 + -1 = p.1.1 - 1 by ring,
          ← triangular_three_zmodCast_sub_one L p.1.1]
        ring
      · rw [← triangular_three_zmodCast_add_one L p.1.1]
        ring
      · rw [show p.1.2 + -1 = p.1.2 - 1 by ring,
          ← triangular_three_zmodCast_sub_one L p.1.2]
        ring
      · rw [← triangular_three_zmodCast_add_one L p.1.2]
        ring
      · constructor
        · rw [show p.1.1 + -1 = p.1.1 - 1 by ring,
            ← triangular_three_zmodCast_sub_one L p.1.1]
          ring
        · rw [show p.1.2 + -1 = p.1.2 - 1 by ring,
            ← triangular_three_zmodCast_sub_one L p.1.2]
          ring
      · constructor
        · rw [← triangular_three_zmodCast_add_one L p.1.1]
          ring
        · rw [← triangular_three_zmodCast_add_one L p.1.2]
          ring
    rw [hembed]
    exact triangularTorusAdj_add_intStep (3 * L)
      (triangularTorusSplitEmbedVertex L p) a
  · generalize hpa : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p) = a
    generalize hqa : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) q) = b
    have hrank : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val := by
      simpa [triangularTorusLocalPortOrder_rank, hpa, hqa] using hint.2
    have hcenter : p.1 = q.1 := hint.1
    rw [triangularTorusSplitEmbedVertex_eq_cast,
      triangularTorusSplitEmbedVertex_eq_cast, ← hcenter, hpa, hqa]
    apply triangularTorusSplitOffset_adj_of_rank (3 * L)
      ((3 * ZMod.cast p.1.1, 3 * ZMod.cast p.1.2)) a b hrank


noncomputable def triangularTorusSplitEmbedHom
    (L : Nat) [Fact (2 < L)] :
    kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L) →g
      triangularTorusGraph (3 * L) where
  toFun := triangularTorusSplitEmbedVertex L
  map_rel' := @triangularTorusSplitEmbedVertex_adj L _



theorem triangularTorusSplitEmbedHom_mapDart_of_matching
    (L : Nat) [Fact (2 < L)]
    (d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
    (triangularTorusSplitEmbedHom L).mapDart d =
      triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst)) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change triangularTorusSplitEmbedVertex L d.snd = _
    rw [triangularTorusSplitEmbedVertex_matching L hmatching]
    have hsnd := triangularTorusGraphDart_snd_eq_fst_add_intStep
      (3 * L) (triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst)))
    change (triangularTorusDartEquiv (3 * L)
        (triangularTorusSplitEmbedVertex L d.fst,
          triangularTorusGraphDartDirection L
            (kwDartOfPort (triangularTorusGraph L) d.fst))).snd = _ at hsnd
    rw [triangularTorusGraphDartDirection_dartEquiv] at hsnd
    exact hsnd.symm


noncomputable def triangularTorusSplitEmbedWalk
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusGraph (3 * L)).Walk
      (triangularTorusSplitEmbedVertex L u)
      (triangularTorusSplitEmbedVertex L v) :=
  p.map (triangularTorusSplitEmbedHom L)

@[simp] theorem triangularTorusSplitEmbedWalk_support
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusSplitEmbedWalk L p).support =
      p.support.map (triangularTorusSplitEmbedVertex L) := by
  exact SimpleGraph.Walk.support_map _ _

@[simp] theorem triangularTorusSplitEmbedWalk_edges
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u v) :
    (triangularTorusSplitEmbedWalk L p).edges =
      p.edges.map (Sym2.map (triangularTorusSplitEmbedHom L)) := by
  exact SimpleGraph.Walk.edges_map _ _


theorem triangularTorusSplitEmbedWalk_isCycle
    (L : Nat) [Fact (2 < L)]
    {u : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u u)
    (hp : p.IsCycle) :
    (triangularTorusSplitEmbedWalk L p).IsCycle := by
  exact hp.map (triangularTorusSplitEmbedVertex_injective L)


theorem triangularTorusSplitEmbedWalk_verts_disjoint
    (L : Nat) [Fact (2 < L)]
    {u v : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk u u)
    (q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk v v)
    (hdisjoint : Disjoint p.toSubgraph.verts q.toSubgraph.verts) :
    Disjoint (triangularTorusSplitEmbedWalk L p).toSubgraph.verts
      (triangularTorusSplitEmbedWalk L q).toSubgraph.verts := by
  apply Set.disjoint_left.mpr
  intro z hzp hzq
  have hzp' : z ∈ (triangularTorusSplitEmbedWalk L p).support :=
    (SimpleGraph.Walk.mem_verts_toSubgraph _).mp hzp
  have hzq' : z ∈ (triangularTorusSplitEmbedWalk L q).support :=
    (SimpleGraph.Walk.mem_verts_toSubgraph _).mp hzq
  rw [triangularTorusSplitEmbedWalk_support, List.mem_map] at hzp' hzq'
  rcases hzp' with ⟨x, hx, rfl⟩
  rcases hzq' with ⟨y, hy, hxy⟩
  have : x = y := triangularTorusSplitEmbedVertex_injective L hxy.symm
  subst y
  exact Set.disjoint_left.1 hdisjoint
    ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hx)
    ((SimpleGraph.Walk.mem_verts_toSubgraph _).mpr hy)

end StatMech.FrontierA
