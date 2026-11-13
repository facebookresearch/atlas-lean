/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Code.FrontierA.KacWardAdaptiveClosure










open scoped BigOperators

namespace StatMech.FrontierA

open scoped Affine



def triangularIntStep : Fin 6 -> Int × Int :=
  ![(-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1)]


def triangularIntPos {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6) (k : Fin n) : Int × Int :=
  ∑ i ∈ Finset.univ.filter (· < k), triangularIntStep (direction i)

@[simp] theorem triangularIntPos_zero {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6) :
    triangularIntPos direction 0 = 0 := by
  have hzero : Finset.univ.filter (· < (0 : Fin n)) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro i _
    exact Fin.not_lt_zero i
  rw [triangularIntPos, hzero, Finset.sum_empty]



theorem triangularIntPos_succ {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (k : Fin n) :
    triangularIntPos direction (k + 1) =
      triangularIntPos direction k + triangularIntStep (direction k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases hk : k = Fin.last m
  · have hzero : (k + 1 : Fin (m + 1)) = 0 := by
      apply Fin.ext
      rw [Fin.val_add_one, if_pos hk]
      rfl
    have hfilter : Finset.univ.filter (· < k) =
        Finset.univ.erase k := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · exact fun hi => ne_of_lt hi
      · intro hne
        have hik : i ≤ k := by
          rw [hk]
          exact Fin.le_last i
        exact lt_of_le_of_ne hik hne
    rw [hzero, triangularIntPos_zero]
    have hpos : triangularIntPos direction k =
        ∑ i ∈ Finset.univ.erase k,
          triangularIntStep (direction i) := by
      rw [triangularIntPos, hfilter]
    rw [hpos, add_comm]
    rw [Finset.add_sum_erase Finset.univ
      (fun i => triangularIntStep (direction i))
      (Finset.mem_univ k)]
    exact hclosed.symm
  · have hval : ((k + 1 : Fin (m + 1)) : Nat) = k.val + 1 := by
      rw [Fin.val_add_one, if_neg hk]
    have hfilter : Finset.univ.filter (· < (k + 1)) =
        insert k (Finset.univ.filter (· < k)) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        rw [Fin.lt_def, hval] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
        · exact Or.inr (Fin.lt_def.2 hlt)
        · exact Or.inl (Fin.ext heq)
      · intro hi
        rw [Fin.lt_def, hval]
        rcases hi with rfl | hlt
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Fin.lt_def.1 hlt)
    have hnotmem : k ∉ Finset.univ.filter (· < k) := by
      simp [Finset.mem_filter]
    rw [triangularIntPos, hfilter, Finset.sum_insert hnotmem, add_comm]
    rw [triangularIntPos]


def triangularIntPoint (p : Int × Int) : Complex :=
  (p.1 : Real) + (p.2 : Real) * Complex.I

theorem triangularIntPoint_injective :
    Function.Injective triangularIntPoint := by
  rintro ⟨px, py⟩ ⟨qx, qy⟩ h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [triangularIntPoint] at hre him
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast him



theorem triangularIntPoint_not_strictly_between_step
    (p q : Int × Int) (a : Fin 6)
    (hqp : q ≠ p) (hqend : q ≠ p + triangularIntStep a) :
    ¬Sbtw Real (triangularIntPoint p) (triangularIntPoint q)
      (triangularIntPoint (p + triangularIntStep a)) := by
  intro hbetween
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := hbetween.mem_image_Ioo
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  have hre := congrArg Complex.re ht
  have him := congrArg Complex.im ht
  fin_cases a <;>
    simp [triangularIntPoint, triangularIntStep,
      AffineMap.lineMap_apply, Prod.ext_iff] at hre him hqp hqend
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
  · have hloR : (-1 : Real) < (qy : Real) - py := by linarith
    have hhiR : (qy : Real) - py < 0 := by linarith
    have hlo : (-1 : Int) < qy - py := by exact_mod_cast hloR
    have hhi : qy - py < 0 := by exact_mod_cast hhiR
    omega
  · have hloR : (0 : Real) < (qy : Real) - py := by linarith
    have hhiR : (qy : Real) - py < 1 := by linarith
    have hlo : (0 : Int) < qy - py := by exact_mod_cast hloR
    have hhi : qy - py < 1 := by exact_mod_cast hhiR
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

private def triangularCanonicalStep : Fin 3 -> Int × Int :=
  ![(1, 0), (0, 1), (1, 1)]

private def triangularCanonicalKind : Fin 6 -> Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

private def triangularCanonicalBase
    (p : Int × Int) : Fin 6 -> Int × Int :=
  ![p + (-1, 0), p, p + (0, -1), p, p + (-1, -1), p]

private theorem triangular_edge_eq_canonical
    (p : Int × Int) (a : Fin 6) :
    s(p, p + triangularIntStep a) =
      s(triangularCanonicalBase p a,
        triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a)) := by
  fin_cases a <;>
    simp [triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, Prod.ext_iff]

private theorem triangular_sbtw_canonical_iff
    (p : Int × Int) (a : Fin 6) (z : Complex) :
    Sbtw Real (triangularIntPoint p) z
        (triangularIntPoint (p + triangularIntStep a)) ↔
      Sbtw Real (triangularIntPoint (triangularCanonicalBase p a)) z
        (triangularIntPoint (triangularCanonicalBase p a +
          triangularCanonicalStep (triangularCanonicalKind a))) := by
  fin_cases a <;>
    simp [triangularIntPoint, triangularIntStep, triangularCanonicalBase,
      triangularCanonicalStep, triangularCanonicalKind, sbtw_comm]

private theorem triangular_canonical_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 3) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularCanonicalStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularCanonicalStep b))) :
    s(p, p + triangularCanonicalStep a) =
      s(q, q + triangularCanonicalStep b) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  obtain ⟨t, ⟨ht0, ht1⟩, htz⟩ := hp.mem_image_Ioo
  obtain ⟨u, ⟨hu0, hu1⟩, huz⟩ := hq.mem_image_Ioo
  have heq : AffineMap.lineMap (triangularIntPoint (px, py))
        (triangularIntPoint ((px, py) + triangularCanonicalStep a)) t =
      AffineMap.lineMap (triangularIntPoint (qx, qy))
        (triangularIntPoint ((qx, qy) + triangularCanonicalStep b)) u :=
    htz.trans huz.symm
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  fin_cases a <;> fin_cases b <;>
    simp [triangularIntPoint, triangularCanonicalStep,
      AffineMap.lineMap_apply] at hre him ⊢
  all_goals
    try have hreCast : (px : Real) = (qx : Real) := by exact_mod_cast hre
    try have himCast : (py : Real) = (qy : Real) := by exact_mod_cast him
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
      | (exfalso; linarith)
      | omega



theorem triangular_open_intersection_edge_eq
    (p q : Int × Int) (a b : Fin 6) (z : Complex)
    (hp : Sbtw Real (triangularIntPoint p) z
      (triangularIntPoint (p + triangularIntStep a)))
    (hq : Sbtw Real (triangularIntPoint q) z
      (triangularIntPoint (q + triangularIntStep b))) :
    s(p, p + triangularIntStep a) =
      s(q, q + triangularIntStep b) := by
  rw [triangular_edge_eq_canonical p a,
    triangular_edge_eq_canonical q b]
  exact triangular_canonical_open_intersection_edge_eq
    (triangularCanonicalBase p a) (triangularCanonicalBase q b)
    (triangularCanonicalKind a) (triangularCanonicalKind b) z
    ((triangular_sbtw_canonical_iff p a z).mp hp)
    ((triangular_sbtw_canonical_iff q b z).mp hq)

private theorem triangular_fin_add_two_ne_self
    {n : Nat} [NeZero n] (hn : 3 ≤ n) (i : Fin n) :
    i + 2 ≠ i := by
  intro h
  have htwo : (2 : Fin n) ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
  apply htwo
  calc
    (2 : Fin n) = (i + 2) - i := by abel
    _ = i - i := by rw [h]
    _ = 0 := sub_self i

theorem triangularIntPos_vertex_not_strictly_between
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hinjective : Function.Injective (triangularIntPos direction))
    (i j : Fin n) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    ¬Sbtw Real
      (triangularIntPoint (triangularIntPos direction i))
      (triangularIntPoint (triangularIntPos direction j))
      (triangularIntPoint (triangularIntPos direction (i + 1))) := by
  rw [triangularIntPos_succ direction hclosed i]
  apply triangularIntPoint_not_strictly_between_step
  · intro hpos
    exact hji (hinjective hpos)
  · intro hpos
    apply hjnext
    apply hinjective
    calc
      triangularIntPos direction j =
          triangularIntPos direction i +
            triangularIntStep (direction i) := hpos
      _ = triangularIntPos direction (i + 1) :=
        (triangularIntPos_succ direction hclosed i).symm

theorem triangularIntPos_edgeInteriors_disjoint
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 ≤ n) (hinjective : Function.Injective (triangularIntPos direction))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint
      {z : Complex | Sbtw Real
        (triangularIntPoint (triangularIntPos direction i)) z
        (triangularIntPoint (triangularIntPos direction (i + 1)))}
      {z : Complex | Sbtw Real
        (triangularIntPoint (triangularIntPos direction j)) z
        (triangularIntPoint (triangularIntPos direction (j + 1)))} := by
  apply Set.disjoint_left.2
  intro z hzi hzj
  have hedge := triangular_open_intersection_edge_eq
    (triangularIntPos direction i) (triangularIntPos direction j)
    (direction i) (direction j) z
    (by simpa [triangularIntPos_succ direction hclosed i] using hzi)
    (by simpa [triangularIntPos_succ direction hclosed j] using hzj)
  rw [Sym2.eq_iff] at hedge
  rcases hedge with hsame | hswap
  · exact hij (hinjective hsame.1)
  · have hfirst : i = j + 1 := by
      apply hinjective
      calc
        triangularIntPos direction i =
            triangularIntPos direction j +
              triangularIntStep (direction j) := hswap.1
        _ = triangularIntPos direction (j + 1) :=
          (triangularIntPos_succ direction hclosed j).symm
    have hsecond : i + 1 = j := by
      apply hinjective
      calc
        triangularIntPos direction (i + 1) =
            triangularIntPos direction i +
              triangularIntStep (direction i) :=
          triangularIntPos_succ direction hclosed i
        _ = triangularIntPos direction j := hswap.2
    apply triangular_fin_add_two_ne_self hn i
    calc
      i + 2 = (i + 1) + 1 := by
        rw [show (2 : Fin n) = 1 + 1 by
          apply Fin.ext
          simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n),
            Nat.mod_eq_of_lt (by omega : 2 < n)], add_assoc]
      _ = j + 1 := by rw [hsecond]
      _ = i := hfirst.symm



noncomputable def triangularIntSimplePolygon
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (hn : 3 ≤ n) (hinjective : Function.Injective (triangularIntPos direction)) :
    KWFiniteSimplePolygon n where
  vertex := fun i => triangularIntPoint (triangularIntPos direction i)
  three_le := hn
  vertex_injective := triangularIntPoint_injective.comp hinjective
  vertex_not_strictly_between :=
    triangularIntPos_vertex_not_strictly_between direction hclosed hinjective
  edgeInteriors_disjoint :=
    triangularIntPos_edgeInteriors_disjoint direction hclosed hn hinjective



noncomputable def triangularTorusGraphDartDirection
    (L : Nat) [Fact (2 < L)]
    (d : (triangularTorusGraph L).Dart) : Fin 6 :=
  ((triangularTorusDartEquiv L).symm d).2



theorem triangularTorusGraphPhase_one_one_apply
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (d e : (triangularTorusGraph L).Dart) :
    triangularTorusGraphPhase L rho 1 1 d e =
      triangularKacWardTurnMatrix rho
        (triangularTorusGraphDartDirection L d)
        (triangularTorusGraphDartDirection L e) := by
  unfold triangularTorusGraphPhase triangularTorusGraphDartDirection
  simp



theorem triangularTorus_cycleDirection_nonbacktracking
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k,
      triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularTorusGraphDartDirection L
            (kwGraphCycleDartLoop p k)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k hreverse
  let d := (triangularTorusDartEquiv L).symm (kwGraphCycleDartLoop p k)
  let e := (triangularTorusDartEquiv L).symm
    (kwGraphCycleDartLoop p (k + 1))
  have hadj := kwGraphCycleDartLoop_valid p hp k
  have hconsecutive : (triangularTorusDartEquiv L d).snd =
      (triangularTorusDartEquiv L e).fst := by
    simpa [d, e] using hadj
  have hnative :=
    (triangularTorusDartEquiv_consecutive_iff L d e).mp hconsecutive
  have heq : e = triangularTorusDartReverse L d := by
    apply Prod.ext
    · change e.1 = d.1 - triangularTorusDirectionStep L d.2
      rw [eq_sub_iff_add_eq]
      calc
        e.1 + triangularTorusDirectionStep L d.2 =
            triangularTorusDirectionStep L d.2 + e.1 := add_comm _ _
        _ = d.1 := (sub_eq_iff_eq_add.mp hnative).symm
    · exact hreverse
  have hedge : (kwGraphCycleDartLoop p k).edge =
      (kwGraphCycleDartLoop p (k + 1)).edge := by
    rw [show kwGraphCycleDartLoop p k = triangularTorusDartEquiv L d by
          simp [d],
      show kwGraphCycleDartLoop p (k + 1) =
          triangularTorusDartEquiv L e by simp [e],
      heq, triangularTorusDartEquiv_reverse,
      SimpleGraph.Dart.edge_symm]
  exact (kwGraphCycleDartLoop_nonbacktracking
    (triangularTorusGraph L) p hp k).2 hedge



theorem triangularTorus_cyclePhaseProduct_eq_turnProduct
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) =
      ∏ k, triangularKacWardTurnMatrix rho
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
        (triangularTorusGraphDartDirection L
          (kwGraphCycleDartLoop p (k + 1))) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  exact triangularTorusGraphPhase_one_one_apply L rho _ _




def triangularTorusTurnExponent : Fin 6 -> Fin 6 -> Int :=
  !![0, 0, 2, -2, 1, -3;
     0, 0, -2, 2, -3, 1;
     -2, 2, 0, 0, -1, 3;
     2, -2, 0, 0, 3, -1;
     -1, 3, 1, -3, 0, 0;
     3, -1, -3, 1, 0, 0]


def triangularTorusDirectionAngleClass : Fin 6 -> ZMod 8 :=
  ![4, 0, 6, 2, 5, 1]



theorem triangularTorusTurnExponent_cast_eq_angleClass_sub
    (a b : Fin 6)
    (hne : b ≠ triangularTorusDirectionReverse a) :
    (triangularTorusTurnExponent a b : ZMod 8) =
      triangularTorusDirectionAngleClass b -
        triangularTorusDirectionAngleClass a := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse,
      triangularTorusTurnExponent,
      triangularTorusDirectionAngleClass] at hne ⊢ <;>
    decide



theorem exists_triangularTorusTurnExponent_sum_eq_eight_mul
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k)) :
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * m := by
  have hshift :
      (∑ k, triangularTorusDirectionAngleClass (direction (k + 1))) =
        ∑ k, triangularTorusDirectionAngleClass (direction k) := by
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
      (fun k => triangularTorusDirectionAngleClass (direction k))
  have hcastSum :
      (∑ k, (triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : ZMod 8)) = 0 := by
    rw [show (∑ k, (triangularTorusTurnExponent
        (direction k) (direction (k + 1)) : ZMod 8)) =
        ∑ k, (triangularTorusDirectionAngleClass (direction (k + 1)) -
          triangularTorusDirectionAngleClass (direction k)) by
      apply Finset.sum_congr rfl
      intro k _
      exact triangularTorusTurnExponent_cast_eq_angleClass_sub _ _
        (hnonbacktracking k)]
    rw [Finset.sum_sub_distrib, hshift, sub_self]
  have hmap := map_sum (Int.castAddHom (ZMod 8))
    (fun k : Fin n => triangularTorusTurnExponent
      (direction k) (direction (k + 1))) Finset.univ
  have hcast : (Int.castAddHom (ZMod 8))
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 0 :=
    hmap.trans hcastSum
  have hdvd : (8 : Int) ∣ ∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hcast
  rcases hdvd with ⟨m, hm⟩
  exact ⟨m, hm⟩



theorem exists_triangularTorus_cycleTurnSum_eq_eight_mul
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
        (triangularTorusGraphDartDirection L
          (kwGraphCycleDartLoop p (k + 1)))) = 8 * m := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  exact exists_triangularTorusTurnExponent_sum_eq_eight_mul _
    (triangularTorus_cycleDirection_nonbacktracking L p hp)

theorem triangularTorusTurnRoot_pow_eight
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) :
    rho ^ 8 = -1 := by
  calc
    rho ^ 8 = (rho ^ 4) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [hrho]
    _ = -1 := by norm_num

theorem triangularTorusTurnRoot_ne_zero
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) : rho ≠ 0 := by
  intro hz
  rw [hz] at hrho
  have hzero : (0 : Complex) ^ 4 = 0 := by norm_num
  rw [hzero] at hrho
  exact Complex.I_ne_zero hrho.symm



theorem triangularKacWardTurnMatrix_eq_zpow
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularKacWardTurnMatrix rho a b =
      rho ^ triangularTorusTurnExponent a b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse, triangularTorusTurnExponent,
      triangularKacWardTurnMatrix] at hne ⊢ <;>
    field_simp <;>
    rw [hrho8] <;> norm_num



theorem prod_triangularKacWardTurnMatrix_eq_zpow_sum
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) =
      rho ^ (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) := by
  rw [show (∏ k, triangularKacWardTurnMatrix rho
      (direction k) (direction (k + 1))) =
      ∏ k, rho ^ triangularTorusTurnExponent
        (direction k) (direction (k + 1)) by
    apply Finset.prod_congr rfl
    intro k _
    exact triangularKacWardTurnMatrix_eq_zpow rho hrho _ _
      (hnonbacktracking k)]
  exact StatMech.Onsager.ons_prod_zpow rho
    (triangularTorusTurnRoot_ne_zero rho hrho) _ _


theorem triangularTorusTurnRoot_zpow_even_revolutions
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (m : Int) :
    rho ^ (8 * (2 * m)) = 1 := by
  have hrho8 : rho ^ (8 : Int) = -1 := by
    simpa [zpow_ofNat] using
      triangularTorusTurnRoot_pow_eight rho hrho
  rw [_root_.zpow_mul, _root_.zpow_mul]
  rw [hrho8]
  norm_num


theorem triangularTorusTurnRoot_zpow_odd_revolutions
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (m : Int) :
    rho ^ (8 * (2 * m + 1)) = -1 := by
  have hrho8 : rho ^ (8 : Int) = -1 := by
    simpa [zpow_ofNat] using
      triangularTorusTurnRoot_pow_eight rho hrho
  rw [_root_.zpow_mul, zpow_add₀]
  · rw [_root_.zpow_mul]
    rw [hrho8]
    norm_num
  · exact pow_ne_zero 8 (triangularTorusTurnRoot_ne_zero rho hrho)



theorem prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k))
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1))) = 8 * (2 * m)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) = 1 := by
  rw [prod_triangularKacWardTurnMatrix_eq_zpow_sum rho hrho direction
    hnonbacktracking, hturn]
  exact triangularTorusTurnRoot_zpow_even_revolutions rho hrho m



theorem prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions
    {n : Nat} [NeZero n]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (direction : Fin n -> Fin 6)
    (hnonbacktracking : forall k,
      direction (k + 1) ≠
        triangularTorusDirectionReverse (direction k))
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (direction k) (direction (k + 1))) = 8 * (2 * m + 1)) :
    (∏ k, triangularKacWardTurnMatrix rho
        (direction k) (direction (k + 1))) = -1 := by
  rw [prod_triangularKacWardTurnMatrix_eq_zpow_sum rho hrho direction
    hnonbacktracking, hturn]
  exact triangularTorusTurnRoot_zpow_odd_revolutions rho hrho m



theorem triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    [NeZero p.darts.length]
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
      (triangularTorusGraphDartDirection L
        (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m)) :
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = 1 := by
  rw [triangularTorus_cyclePhaseProduct_eq_turnProduct L rho p hp]
  exact prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions
    rho hrho _ (triangularTorus_cycleDirection_nonbacktracking L p hp) m hturn



theorem triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    [NeZero p.darts.length]
    (m : Int)
    (hturn : (∑ k, triangularTorusTurnExponent
      (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
      (triangularTorusGraphDartDirection L
        (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1)) :
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = -1 := by
  rw [triangularTorus_cyclePhaseProduct_eq_turnProduct L rho p hp]
  exact prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions
    rho hrho _ (triangularTorus_cycleDirection_nonbacktracking L p hp) m hturn

end StatMech.FrontierA
