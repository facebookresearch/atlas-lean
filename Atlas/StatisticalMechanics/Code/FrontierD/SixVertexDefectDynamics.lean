/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBethePerronContinuation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected










open Finset

namespace StatMech.FrontierD

noncomputable section

noncomputable instance sixVertexNoAdjacentSectorFintype (N n : Nat) :
    Fintype (SixVertexNoAdjacentSector N n) :=
  Fintype.ofFinite _


def sixVertexDefectWeight {n : Nat} (d : Fin n → Nat) : Nat :=
  ∑ i, i.val * d i


def sixVertexDefectPile {n : Nat} (hn : 0 < n) (D : Nat) : Fin n → Nat :=
  fun i => if i.val = 0 then D else 0


def sixVertexDefectLower {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) : Fin n → Nat :=
  let p : Fin n := ⟨i.val - 1, by omega⟩
  Function.update (Function.update d i (d i - 1)) p (d p + 1)



def SixVertexDefectLowerStep {n : Nat} (d e : Fin n → Nat) : Prop :=
  ∃ (i : Fin n) (hi : 0 < i.val), 0 < d i ∧
    e = sixVertexDefectLower d i hi

private theorem sum_update_add_old
    {n : Nat} (f : Fin n → Nat) (i : Fin n) (b : Nat) :
    (∑ j, Function.update f i b j) + f i = (∑ j, f j) + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  omega

private theorem weighted_sum_update_add_old
    {n : Nat} (f : Fin n → Nat) (w : Fin n → Nat)
    (i : Fin n) (b : Nat) :
    (∑ j, w j * Function.update f i b j) + w i * f i =
      (∑ j, w j * f j) + w i * b := by
  have hfun : (fun j => w j * Function.update f i b j) =
      Function.update (fun j => w j * f j) i (w i * b) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  rw [hfun]
  exact sum_update_add_old (fun j => w j * f j) i (w i * b)

@[simp] theorem sixVertexDefectLower_apply_self
    {n : Nat} (d : Fin n → Nat) (i : Fin n) (hi : 0 < i.val) :
    sixVertexDefectLower d i hi i = d i - 1 := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hip : i ≠ p := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  change Function.update (Function.update d i (d i - 1)) p
      (d p + 1) i = d i - 1
  rw [Function.update_of_ne hip, Function.update_self]

@[simp] theorem sixVertexDefectLower_apply_pred
    {n : Nat} (d : Fin n → Nat) (i : Fin n) (hi : 0 < i.val) :
    sixVertexDefectLower d i hi ⟨i.val - 1, by omega⟩ =
      d ⟨i.val - 1, by omega⟩ + 1 := by
  simp [sixVertexDefectLower]

theorem sum_sixVertexDefectLower
    {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) (hd : 0 < d i) :
    ∑ j, sixVertexDefectLower d i hi j = ∑ j, d j := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let f := Function.update d i (d i - 1)
  have hpi : p ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  have hfi : f p = d p := by
    simp [f, Function.update_of_ne hpi]
  have hfirst := sum_update_add_old d i (d i - 1)
  have hsecond := sum_update_add_old f p (d p + 1)
  change (∑ j, f j) + d i = (∑ j, d j) + (d i - 1) at hfirst
  change (∑ j, Function.update f p (d p + 1) j) + f p =
    (∑ j, f j) + (d p + 1) at hsecond
  rw [hfi] at hsecond
  have hfirst' : (∑ j, f j) + 1 = ∑ j, d j := by omega
  have hsecond' :
      (∑ j, Function.update f p (d p + 1) j) =
        (∑ j, f j) + 1 := by omega
  change (∑ j, Function.update f p (d p + 1) j) = ∑ j, d j
  rw [hsecond', hfirst']

theorem sixVertexDefectWeight_lower_add_one
    {n : Nat} (d : Fin n → Nat) (i : Fin n)
    (hi : 0 < i.val) (hd : 0 < d i) :
    sixVertexDefectWeight (sixVertexDefectLower d i hi) + 1 =
      sixVertexDefectWeight d := by
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let f := Function.update d i (d i - 1)
  have hpi : p ≠ i := by
    intro h
    have := congrArg Fin.val h
    dsimp [p] at this
    omega
  have hfi : f p = d p := by
    simp [f, Function.update_of_ne hpi]
  have hfirst := weighted_sum_update_add_old d (fun j => j.val) i (d i - 1)
  have hsecond := weighted_sum_update_add_old f (fun j => j.val) p (d p + 1)
  change (∑ j, j.val * f j) + i.val * d i =
    (∑ j, j.val * d j) + i.val * (d i - 1) at hfirst
  change (∑ j, j.val * Function.update f p (d p + 1) j) + p.val * f p =
    (∑ j, j.val * f j) + p.val * (d p + 1) at hsecond
  rw [hfi] at hsecond
  have hdi : d i = d i - 1 + 1 := by omega
  have hmulI : i.val * d i = i.val * (d i - 1) + i.val := by
    calc
      i.val * d i = i.val * (d i - 1 + 1) :=
        congrArg (fun q => i.val * q) hdi
      _ = i.val * (d i - 1) + i.val := by rw [Nat.mul_add, Nat.mul_one]
  have hmulP : p.val * (d p + 1) = p.val * d p + p.val := by
    rw [Nat.mul_add, Nat.mul_one]
  have hpval : p.val + 1 = i.val := by
    dsimp [p]
    omega
  have hfirst' : (∑ j, j.val * f j) + i.val =
      ∑ j, j.val * d j := by omega
  have hsecond' :
      (∑ j, j.val * Function.update f p (d p + 1) j) =
        (∑ j, j.val * f j) + p.val := by omega
  change (∑ j, j.val * Function.update f p (d p + 1) j) + 1 =
    ∑ j, j.val * d j
  omega

theorem sixVertexDefectWeight_eq_zero_iff
    {n : Nat} (d : Fin n → Nat) :
    sixVertexDefectWeight d = 0 ↔ ∀ i, 0 < i.val → d i = 0 := by
  rw [sixVertexDefectWeight, Finset.sum_eq_zero_iff]
  constructor
  · intro h i hi
    have := h i (Finset.mem_univ i)
    rcases Nat.mul_eq_zero.mp this with hival | hdi
    · exact False.elim (Nat.ne_of_gt hi hival)
    · exact hdi
  · intro h i _
    by_cases hi : i.val = 0
    · simp [hi]
    · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
      rw [h i hipos, mul_zero]

theorem sixVertexDefectPile_sum
    {n : Nat} (hn : 0 < n) (D : Nat) :
    ∑ i, sixVertexDefectPile hn D i = D := by
  let z : Fin n := ⟨0, hn⟩
  rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ z)]
  · simp [sixVertexDefectPile, z]
  · intro i _ hiz
    have hi : i.val ≠ 0 := by
      intro h
      apply hiz
      exact Fin.ext h
    simp [sixVertexDefectPile, hi]

theorem sixVertexDefect_eq_pile_of_weight_eq_zero
    {n : Nat} (hn : 0 < n) (d : Fin n → Nat)
    (hweight : sixVertexDefectWeight d = 0) :
    d = sixVertexDefectPile hn (∑ i, d i) := by
  have hoff := (sixVertexDefectWeight_eq_zero_iff d).mp hweight
  let z : Fin n := ⟨0, hn⟩
  have hsum : (∑ i, d i) = d z := by
    apply Finset.sum_eq_single_of_mem z (Finset.mem_univ z)
    intro i _ hiz
    have hi : 0 < i.val := by
      have hine : i.val ≠ 0 := by
        intro h
        apply hiz
        exact Fin.ext h
      omega
    exact hoff i hi
  funext i
  by_cases hi : i.val = 0
  · have hiz : i = z := Fin.ext hi
    subst i
    simp [sixVertexDefectPile, z, hsum]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    rw [hoff i hipos]
    simp [sixVertexDefectPile, hi]



theorem sixVertexDefectLowerStep_reaches_pile
    {n : Nat} (hn : 0 < n) (d : Fin n → Nat) :
    Relation.ReflTransGen SixVertexDefectLowerStep d
      (sixVertexDefectPile hn (∑ i, d i)) := by
  by_cases hw0 : sixVertexDefectWeight d = 0
  · have hd := sixVertexDefect_eq_pile_of_weight_eq_zero hn d hw0
    rw [hd, sixVertexDefectPile_sum]
  · have hwpos : 0 < sixVertexDefectWeight d := Nat.pos_of_ne_zero hw0
    rw [sixVertexDefectWeight] at hwpos
    obtain ⟨i, _, hiweight⟩ := Finset.sum_pos_iff.mp hwpos
    have hi : 0 < i.val := Nat.pos_of_mul_pos_right hiweight
    have hd : 0 < d i := Nat.pos_of_mul_pos_left hiweight
    let e := sixVertexDefectLower d i hi
    have hstep : SixVertexDefectLowerStep d e := ⟨i, hi, hd, rfl⟩
    have hreach := sixVertexDefectLowerStep_reaches_pile hn e
    have hsum := sum_sixVertexDefectLower d i hi hd
    exact (Relation.ReflTransGen.single hstep).trans (by
      simpa only [e, hsum] using hreach)
termination_by sixVertexDefectWeight d
decreasing_by
  have hweight := sixVertexDefectWeight_lower_add_one d i hi hd
  omega

theorem SixVertexDefectLowerStep.sum_eq
    {n : Nat} {d e : Fin n → Nat} (h : SixVertexDefectLowerStep d e) :
    ∑ i, e i = ∑ i, d i := by
  obtain ⟨i, hi, hd, rfl⟩ := h
  exact sum_sixVertexDefectLower d i hi hd

theorem SixVertexDefectLowerStep.weight_add_one
    {n : Nat} {d e : Fin n → Nat} (h : SixVertexDefectLowerStep d e) :
    sixVertexDefectWeight e + 1 = sixVertexDefectWeight d := by
  obtain ⟨i, hi, hd, rfl⟩ := h
  exact sixVertexDefectWeight_lower_add_one d i hi hd


def SixVertexDefectState (n D : Nat) :=
  {d : Fin n → Nat // ∑ i, d i = D}


def sixVertexDefectLowerGraph (n D : Nat) :
    SimpleGraph (SixVertexDefectState n D) where
  Adj d e := SixVertexDefectLowerStep d.1 e.1 ∨
    SixVertexDefectLowerStep e.1 d.1
  symm := by
    intro d e h
    exact h.symm
  loopless := by
    refine ⟨?_⟩
    intro d h
    rcases h with h | h
    · have hw := h.weight_add_one
      omega
    · have hw := h.weight_add_one
      omega

noncomputable instance sixVertexDefectLowerGraph_adjDecidable (n D : Nat) :
    DecidableRel (sixVertexDefectLowerGraph n D).Adj :=
  Classical.decRel _

private theorem sixVertexDefectLowerStep_lift_reflTransGen
    {n D : Nat} {d e : Fin n → Nat}
    (h : Relation.ReflTransGen SixVertexDefectLowerStep d e)
    (hd : ∑ i, d i = D) :
    ∃ he : ∑ i, e i = D,
      Relation.ReflTransGen (sixVertexDefectLowerGraph n D).Adj
        ⟨d, hd⟩ ⟨e, he⟩ := by
  induction h with
  | refl => exact ⟨hd, Relation.ReflTransGen.refl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨hb, hreach⟩ := ih
      have hc : ∑ i, c i = D := hbc.sum_eq.trans hb
      refine ⟨hc, hreach.tail ?_⟩
      exact Or.inl hbc


theorem sixVertexDefectLowerGraph_reachable_pile
    {n D : Nat} (hn : 0 < n) (d : SixVertexDefectState n D) :
    (sixVertexDefectLowerGraph n D).Reachable d
      ⟨sixVertexDefectPile hn D, sixVertexDefectPile_sum hn D⟩ := by
  have hfun := sixVertexDefectLowerStep_reaches_pile hn d.1
  obtain ⟨hpile, hlift⟩ :=
    sixVertexDefectLowerStep_lift_reflTransGen hfun d.2
  have hpileEq : sixVertexDefectPile hn (∑ i, d.1 i) =
      sixVertexDefectPile hn D := by rw [d.2]
  apply (SimpleGraph.reachable_iff_reflTransGen _ _).mpr
  simpa only [hpileEq, Subtype.mk.injEq] using hlift


theorem sixVertexDefectLowerGraph_preconnected
    {n D : Nat} (hn : 0 < n) :
    (sixVertexDefectLowerGraph n D).Preconnected := by
  intro d e
  exact (sixVertexDefectLowerGraph_reachable_pile hn d).trans
    (sixVertexDefectLowerGraph_reachable_pile hn e).symm


def sixVertexSectorDefectState
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n) :
    SixVertexDefectState n (N - 2 * n) :=
  ⟨sixVertexSectorGapDefects x, sum_sixVertexSectorGapDefects x hx hn⟩



def sixVertexFixedChargeSectorDefectState
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    SixVertexDefectState (sixVertexFixedChargeBetheParticleCount r k) (2 * r) :=
  ⟨sixVertexSectorGapDefects x, by
    rw [sum_sixVertexSectorGapDefects x hx,
      sixVertexFixedChargeBetheParticleCount_eq]
    · unfold sixVertexFourWidth
      omega
    · exact sixVertexFixedChargeBetheParticleCount_pos r k⟩

theorem sixVertexFixedChargeSectorDefectState_reachable_pile
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k))
    (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexDefectLowerGraph
      (sixVertexFixedChargeBetheParticleCount r k) (2 * r)).Reachable
      (sixVertexFixedChargeSectorDefectState r k x hx)
      ⟨sixVertexDefectPile
          (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r),
        sixVertexDefectPile_sum
          (sixVertexFixedChargeBetheParticleCount_pos r k) (2 * r)⟩ := by
  exact sixVertexDefectLowerGraph_reachable_pile
    (sixVertexFixedChargeBetheParticleCount_pos r k) _

private def sixVertexForwardMoveEmbedding
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    Fin n ↪o Fin N :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(sixVertexSectorPosition x i).val + a i, hbound i⟩)
    (by
      intro i j hij
      exact hmono i j hij)


def sixVertexForwardMoveSector
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexForwardMoveEmbedding x a hbound hmono)

@[simp] theorem sixVertexSectorPosition_forwardMoveSector
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    sixVertexSectorPosition
      (sixVertexForwardMoveSector x a hbound hmono) =
        sixVertexForwardMoveEmbedding x a hbound hmono := by
  change Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofFinEmbEquiv
        (sixVertexForwardMoveEmbedding x a hbound hmono)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_forwardMoveSector_apply_val
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j)
    (i : Fin n) :
    (sixVertexSectorPosition
      (sixVertexForwardMoveSector x a hbound hmono) i).val =
        (sixVertexSectorPosition x i).val + a i := by
  rw [sixVertexSectorPosition_forwardMoveSector]
  rfl

theorem sixVertexInfinityGraph_adj_forwardMoveSector
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j)
    (hpos : ∀ i, 0 < a i)
    (hbetween : ∀ (k : Nat) (hk : k + 1 < n),
      (sixVertexSectorPosition x ⟨k, by omega⟩).val +
          a ⟨k, by omega⟩ <
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexForwardMoveSector x a hbound hmono) := by
  let y := sixVertexForwardMoveSector x a hbound hmono
  have hypos (i : Fin n) :
      (sixVertexSectorPosition y i).val =
        (sixVertexSectorPosition x i).val + a i := by
    exact sixVertexSectorPosition_forwardMoveSector_apply_val
      x a hbound hmono i
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      exact_mod_cast (show (sixVertexSectorPosition x i).val ≤
        (sixVertexSectorPosition y i).val by rw [hypos]; omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition y ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val by
          rw [hypos]
          exact (hbetween k hk).le)
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    let j : Fin n := (x.val.orderIsoOfFin x.prop).symm ⟨z, hzx⟩
    let i : Fin n := (y.val.orderIsoOfFin y.prop).symm ⟨z, hzy⟩
    have hj : sixVertexSectorPosition x j = z := by
      exact congrArg Subtype.val
        ((x.val.orderIsoOfFin x.prop).apply_symm_apply ⟨z, hzx⟩)
    have hi : sixVertexSectorPosition y i = z := by
      exact congrArg Subtype.val
        ((y.val.orderIsoOfFin y.prop).apply_symm_apply ⟨z, hzy⟩)
    have heq : sixVertexSectorPosition x j =
        sixVertexSectorPosition y i := hj.trans hi.symm
    by_cases hji : j ≤ i
    · have hxle : (sixVertexSectorPosition x j).val ≤
          (sixVertexSectorPosition x i).val := by
        exact_mod_cast (sixVertexSectorPosition x).monotone hji
      have hygt : (sixVertexSectorPosition x i).val <
          (sixVertexSectorPosition y i).val := by
        rw [hypos i]
        exact Nat.lt_add_of_pos_right (hpos i)
      have := congrArg Fin.val heq
      omega
    · have hij : i < j := lt_of_not_ge hji
      have hik : i.val + 1 < n := by omega
      have hmid := hbetween i.val hik
      have hi0 : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
      rw [hi0] at hmid
      have hnextle :
          (sixVertexSectorPosition x ⟨i.val + 1, hik⟩).val ≤
            (sixVertexSectorPosition x j).val := by
        exact_mod_cast (sixVertexSectorPosition x).monotone (by
          change i.val + 1 ≤ j.val
          omega)
      have := congrArg Fin.val heq
      rw [hypos] at this
      omega
  exact (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mpr
    (Or.inl ⟨hforward, hdisj⟩)

theorem sixVertexSectorCyclicNext_pred
    {n : Nat} (i : Fin n) (hi : 0 < i.val) :
    sixVertexSectorCyclicNext ⟨i.val - 1, by omega⟩ = i := by
  rw [sixVertexSectorCyclicNext]
  split_ifs with hnext
  · apply Fin.ext
    change (i.val - 1) + 1 = i.val
    omega
  · exfalso
    apply hnext
    change (i.val - 1) + 1 < n
    omega

theorem sixVertexSectorCyclicNext_eq_iff_eq_pred
    {n : Nat} (i j : Fin n) (hi : 0 < i.val) :
    sixVertexSectorCyclicNext j = i ↔
      j = ⟨i.val - 1, by omega⟩ := by
  constructor
  · intro h
    rw [sixVertexSectorCyclicNext] at h
    split_ifs at h with hnext
    · apply Fin.ext
      have hv := congrArg Fin.val h
      change j.val + 1 = i.val at hv
      change j.val = i.val - 1
      omega
    · have hv := congrArg Fin.val h
      change 0 = i.val at hv
      omega
  · rintro rfl
    exact sixVertexSectorCyclicNext_pred i hi


def sixVertexDefectLowerAdvance {n : Nat} (i : Fin n) : Fin n → Nat :=
  fun j => if j = i then 2 else 1

theorem sixVertexDefectLowerAdvance_pos
    {n : Nat} (i j : Fin n) :
    0 < sixVertexDefectLowerAdvance i j := by
  by_cases hji : j = i <;> simp [sixVertexDefectLowerAdvance, hji]

theorem sixVertexDefectLowerAdvance_sub_one
    {n : Nat} (i j : Fin n) :
    sixVertexDefectLowerAdvance i j - 1 = if j = i then 1 else 0 := by
  by_cases hji : j = i <;> simp [sixVertexDefectLowerAdvance, hji]

theorem sixVertexDefectLowerMove_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    ∀ j, (sixVertexSectorPosition x j).val +
      sixVertexDefectLowerAdvance i j < N := by
  intro j
  by_cases hnext : j.val + 1 < n
  · have hj : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
    by_cases hji : j = i
    · subst j
      simp only [sixVertexDefectLowerAdvance, if_pos]
      rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd
      simp only [dif_pos hnext] at hd
      have hnextN := (sixVertexSectorPosition x
        ⟨i.val + 1, hnext⟩).isLt
      omega
    · rw [sixVertexDefectLowerAdvance]
      simp only [if_neg hji]
      have hgap := hx.1 j.val hnext
      rw [hj] at hgap
      have hnextN := (sixVertexSectorPosition x
        ⟨j.val + 1, hnext⟩).isLt
      omega
  · have hjlast : j = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      change j.val = n - 1
      omega
    simpa only [hjlast] using hlast

theorem sixVertexDefectLowerMove_between
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (k : Nat) (hk : k + 1 < n) :
    (sixVertexSectorPosition x ⟨k, by omega⟩).val +
        sixVertexDefectLowerAdvance i ⟨k, by omega⟩ <
      (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
  by_cases hki : (⟨k, by omega⟩ : Fin n) = i
  · rw [sixVertexDefectLowerAdvance, if_pos hki]
    rw [← hki] at hd
    rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd
    simp only [dif_pos hk] at hd
    omega
  · rw [sixVertexDefectLowerAdvance]
    simp only [if_neg hki]
    exact hx.1 k hk

theorem sixVertexDefectLowerMove_mono
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i) :
    ∀ j k : Fin n, j < k →
      (sixVertexSectorPosition x j).val + sixVertexDefectLowerAdvance i j <
        (sixVertexSectorPosition x k).val + sixVertexDefectLowerAdvance i k := by
  intro j k hjk
  have hjnext : j.val + 1 < n := by omega
  have hbetween := sixVertexDefectLowerMove_between
    x hx i hd j.val hjnext
  have hj0 : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
  rw [hj0] at hbetween
  have hnextle :
      (sixVertexSectorPosition x ⟨j.val + 1, hjnext⟩).val ≤
        (sixVertexSectorPosition x k).val := by
    exact_mod_cast (sixVertexSectorPosition x).monotone (by
      change j.val + 1 ≤ k.val
      omega)
  have hkpos := sixVertexDefectLowerAdvance_pos i k
  omega


def sixVertexDefectLowerMoveSector
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    SixVertexSector N n :=
  sixVertexForwardMoveSector x (sixVertexDefectLowerAdvance i)
    (sixVertexDefectLowerMove_bound x hx hn i hd hlast)
    (sixVertexDefectLowerMove_mono x hx i hd)

@[simp] theorem sixVertexSectorPosition_defectLowerMoveSector_apply_val
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N)
    (j : Fin n) :
    (sixVertexSectorPosition
      (sixVertexDefectLowerMoveSector x hx hn i hd hlast) j).val =
        (sixVertexSectorPosition x j).val +
          sixVertexDefectLowerAdvance i j := by
  exact sixVertexSectorPosition_forwardMoveSector_apply_val _ _ _ _ _

theorem sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexDefectLowerMoveSector x hx hn i hd hlast) := by
  apply sixVertexInfinityGraph_adj_forwardMoveSector hn
  · exact sixVertexDefectLowerAdvance_pos i
  · exact sixVertexDefectLowerMove_between x hx i hd

theorem sixVertexDefectLowerMoveSector_gapDefects
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    sixVertexSectorGapDefects
        (sixVertexDefectLowerMoveSector x hx hn i hd hlast) =
      sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
  let y := sixVertexDefectLowerMoveSector x hx hn i hd hlast
  have hypos (j : Fin n) :
      (sixVertexSectorPosition y j).val =
        (sixVertexSectorPosition x j).val +
          sixVertexDefectLowerAdvance i j := by
    exact sixVertexSectorPosition_defectLowerMoveSector_apply_val
      x hx hn i hd hlast j
  have hadj : (sixVertexInfinityGraph N n).Adj x y :=
    sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
      x hx hn i hi hd hlast
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    have hdata := (sixVertexInfinityGraph_adj_iff N n x y).mp hadj
    exact (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n x y).mp
      hdata.2.2
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro j
      exact_mod_cast (show (sixVertexSectorPosition x j).val ≤
        (sixVertexSectorPosition y j).val by
          rw [hypos]
          omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition y ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val by
          rw [hypos]
          exact (sixVertexDefectLowerMove_between x hx i hd k hk).le)
  have hadv (j : Fin n) : sixVertexSectorAdvance x y j =
      sixVertexDefectLowerAdvance i j := by
    rw [sixVertexSectorAdvance, hypos]
    omega
  have hb (j : Fin n) : sixVertexSectorAdvanceDefects x y j =
      if j = i then 1 else 0 := by
    rw [sixVertexSectorAdvanceDefects, hadv,
      sixVertexDefectLowerAdvance_sub_one]
  have htransport (j : Fin n) :=
    sixVertexSectorGapDefects_transport_of_forward_disjoint
      x y hforward hdisj j
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hpi : p ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    omega
  funext j
  by_cases hji : j = i
  · subst j
    have hnextNe : sixVertexSectorCyclicNext i ≠ i := by
      intro h
      have hip := (sixVertexSectorCyclicNext_eq_iff_eq_pred i i hi).mp h
      exact hpi hip.symm
    have ht := htransport i
    rw [hb i, if_pos rfl, hb, if_neg hnextNe] at ht
    change sixVertexSectorGapDefects y i =
      sixVertexDefectLower (sixVertexSectorGapDefects x) i hi i
    rw [sixVertexDefectLower_apply_self]
    omega
  · by_cases hjp : j = p
    · subst j
      have hnext : sixVertexSectorCyclicNext p = i := by
        exact sixVertexSectorCyclicNext_pred i hi
      have ht := htransport p
      rw [hb p, if_neg hpi, hb, hnext, if_pos rfl] at ht
      change sixVertexSectorGapDefects y p =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi p
      rw [sixVertexDefectLower_apply_pred]
      omega
    · have hnextNe : sixVertexSectorCyclicNext j ≠ i := by
        intro h
        have := (sixVertexSectorCyclicNext_eq_iff_eq_pred i j hi).mp h
        exact hjp this
      have ht := htransport j
      rw [hb j, if_neg hji, hb, if_neg hnextNe] at ht
      change sixVertexSectorGapDefects y j =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi j
      rw [sixVertexDefectLower]
      have hjp' : j ≠ p := hjp
      rw [Function.update_of_ne hjp']
      rw [Function.update_of_ne hji]
      exact ht

private def sixVertexShiftLeftEmbedding
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    Fin n ↪o Fin N := by
  let f : Fin n → Fin N := fun i =>
    ⟨(sixVertexSectorPosition x i).val - 1, by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (sixVertexSectorPosition x i).isLt⟩
  exact OrderEmbedding.ofStrictMono f (by
    intro i j hij
    change (sixVertexSectorPosition x i).val - 1 <
      (sixVertexSectorPosition x j).val - 1
    have hmono := (sixVertexSectorPosition x).strictMono hij
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega)


def sixVertexShiftLeftSector
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv
    (sixVertexShiftLeftEmbedding x hn hfirst)

@[simp] theorem sixVertexSectorPosition_shiftLeftSector_apply_val
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val)
    (i : Fin n) :
    (sixVertexSectorPosition (sixVertexShiftLeftSector x hn hfirst) i).val =
      (sixVertexSectorPosition x i).val - 1 := by
  change (Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexShiftLeftEmbedding x hn hfirst)) i).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem sixVertexShiftLeftSector_noAdjacent
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    SixVertexSectorNoAdjacent (sixVertexShiftLeftSector x hn hfirst) := by
  constructor
  · intro k hk
    rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hgap := hx.1 k hk
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x ⟨k, by omega⟩).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega
  · intro _
    rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hwrap := hx.2 hn
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega

theorem sixVertexShiftLeftSector_gapDefects
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    sixVertexSectorGapDefects (sixVertexShiftLeftSector x hn hfirst) =
      sixVertexSectorGapDefects x := by
  funext i
  rw [sixVertexSectorGapDefects, sixVertexSectorGapDefects,
    sixVertexSectorGap, sixVertexSectorGap]
  split_ifs with hnext
  · rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    have hilt : i < (⟨i.val + 1, hnext⟩ : Fin n) := by
      change i.val < i.val + 1
      omega
    have hmono := Fin.lt_iff_val_lt_val.mp
      ((sixVertexSectorPosition x).strictMono hilt)
    omega
  · rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega

theorem sixVertexInfinityGraph_adj_shiftLeftSector
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexShiftLeftSector x hn hfirst) := by
  let y := sixVertexShiftLeftSector x hn hfirst
  have hypos (i : Fin n) : (sixVertexSectorPosition y i).val =
      (sixVertexSectorPosition x i).val - 1 :=
    sixVertexSectorPosition_shiftLeftSector_apply_val x hn hfirst i
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      exact_mod_cast (show (sixVertexSectorPosition y i).val ≤
        (sixVertexSectorPosition x i).val by rw [hypos]; omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition x ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition y ⟨k + 1, hk⟩).val by
          rw [hypos]
          have hgap := hx.1 k hk
          have hfirstLe :
              (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
                (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
            exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
              ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
          omega)
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    let j : Fin n := (x.val.orderIsoOfFin x.prop).symm ⟨z, hzx⟩
    let i : Fin n := (y.val.orderIsoOfFin y.prop).symm ⟨z, hzy⟩
    have hj : sixVertexSectorPosition x j = z := by
      exact congrArg Subtype.val
        ((x.val.orderIsoOfFin x.prop).apply_symm_apply ⟨z, hzx⟩)
    have hi : sixVertexSectorPosition y i = z := by
      exact congrArg Subtype.val
        ((y.val.orderIsoOfFin y.prop).apply_symm_apply ⟨z, hzy⟩)
    have heq : sixVertexSectorPosition x j =
        sixVertexSectorPosition y i := hj.trans hi.symm
    by_cases hij : i ≤ j
    · have hxle : (sixVertexSectorPosition x i).val ≤
          (sixVertexSectorPosition x j).val := by
        exact Fin.le_iff_val_le_val.mp
          ((sixVertexSectorPosition x).monotone hij)
      have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
          (sixVertexSectorPosition x i).val := by
        exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
          ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
      have hv := congrArg Fin.val heq
      rw [hypos] at hv
      omega
    · have hji : j < i := lt_of_not_ge hij
      have hjnext : j.val + 1 < n := by omega
      have hgap := hx.1 j.val hjnext
      have hj0 : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
      rw [hj0] at hgap
      have hnextle :
          (sixVertexSectorPosition x ⟨j.val + 1, hjnext⟩).val ≤
            (sixVertexSectorPosition x i).val := by
        apply Fin.le_iff_val_le_val.mp
        apply (sixVertexSectorPosition x).monotone
        apply Fin.le_iff_val_le_val.mpr
        change j.val + 1 ≤ i.val
        exact Nat.succ_le_iff.mpr (Fin.lt_iff_val_lt_val.mp hji)
      have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
          (sixVertexSectorPosition x i).val := by
        exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
          ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
      have hv := congrArg Fin.val heq
      rw [hypos] at hv
      omega
  exact (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mpr
    (Or.inr ⟨hforward, hdisj⟩)

theorem sixVertexDefectLowerMove_first_pos_of_not_last_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hbound : ¬((sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N)) :
    0 < (sixVertexSectorPosition x ⟨0, hn⟩).val := by
  by_contra hfirst
  have hfirst0 : (sixVertexSectorPosition x ⟨0, hn⟩).val = 0 := by
    omega
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hilast : last = i
  · have hd' : 0 < sixVertexSectorGapDefects x last := by
      rw [hilast]
      exact hd
    have hnext : ¬(last.val + 1 < n) := by
      dsimp [last]
      omega
    rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd'
    simp only [dif_neg hnext] at hd'
    have hbound' : ¬((sixVertexSectorPosition x last).val +
        sixVertexDefectLowerAdvance last last < N) := by
      simpa only [last, hilast] using hbound
    simp only [sixVertexDefectLowerAdvance, if_pos rfl] at hbound'
    have hlastN := (sixVertexSectorPosition x last).isLt
    dsimp [last] at hbound' hd' hlastN
    omega
  · have hbound' : ¬((sixVertexSectorPosition x last).val +
        sixVertexDefectLowerAdvance i last < N) := by
      simpa only [last] using hbound
    simp only [sixVertexDefectLowerAdvance, if_neg hilast] at hbound'
    have hwrap := hx.2 hn
    change (sixVertexSectorPosition x last).val + 1 <
      N + (sixVertexSectorPosition x ⟨0, hn⟩).val at hwrap
    omega




theorem sixVertexInfinityGraph_reachable_defectLower
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hbound : (sixVertexSectorPosition x last).val +
      sixVertexDefectLowerAdvance i last < N
  · let y := sixVertexDefectLowerMoveSector x hx hn i hd hbound
    have hadj := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
      x hx hn i hi hd hbound
    refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent hadj).2,
      hadj.reachable, ?_⟩
    exact sixVertexDefectLowerMoveSector_gapDefects
      x hx hn i hi hd hbound
  · have hfirst := sixVertexDefectLowerMove_first_pos_of_not_last_bound
      x hx hn i hd hbound
    let x1 := sixVertexShiftLeftSector x hn hfirst
    have hx1 : SixVertexSectorNoAdjacent x1 :=
      sixVertexShiftLeftSector_noAdjacent x hx hn hfirst
    have hx1gap : sixVertexSectorGapDefects x1 =
        sixVertexSectorGapDefects x :=
      sixVertexShiftLeftSector_gapDefects x hn hfirst
    have hd1 : 0 < sixVertexSectorGapDefects x1 i := by
      rw [hx1gap]
      exact hd
    have hxx1 : (sixVertexInfinityGraph N n).Adj x x1 :=
      sixVertexInfinityGraph_adj_shiftLeftSector x hx hn hfirst
    by_cases hbound1 : (sixVertexSectorPosition x1 last).val +
        sixVertexDefectLowerAdvance i last < N
    · let y := sixVertexDefectLowerMoveSector x1 hx1 hn i hd1 hbound1
      have h1y := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
        x1 hx1 hn i hi hd1 hbound1
      refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent h1y).2,
        hxx1.reachable.trans h1y.reachable, ?_⟩
      rw [sixVertexDefectLowerMoveSector_gapDefects
        x1 hx1 hn i hi hd1 hbound1, hx1gap]
    · have hfirst1 := sixVertexDefectLowerMove_first_pos_of_not_last_bound
        x1 hx1 hn i hd1 hbound1
      let x2 := sixVertexShiftLeftSector x1 hn hfirst1
      have hx2 : SixVertexSectorNoAdjacent x2 :=
        sixVertexShiftLeftSector_noAdjacent x1 hx1 hn hfirst1
      have hx2gap : sixVertexSectorGapDefects x2 =
          sixVertexSectorGapDefects x1 :=
        sixVertexShiftLeftSector_gapDefects x1 hn hfirst1
      have hd2 : 0 < sixVertexSectorGapDefects x2 i := by
        rw [hx2gap, hx1gap]
        exact hd
      have hx1x2 : (sixVertexInfinityGraph N n).Adj x1 x2 :=
        sixVertexInfinityGraph_adj_shiftLeftSector x1 hx1 hn hfirst1
      have hlastPos : 0 < (sixVertexSectorPosition x last).val := by
        have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
            (sixVertexSectorPosition x last).val := by
          exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
            ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
        omega
      have hlast1Pos : 0 < (sixVertexSectorPosition x1 last).val := by
        have hfirstLe : (sixVertexSectorPosition x1 ⟨0, hn⟩).val ≤
            (sixVertexSectorPosition x1 last).val := by
          exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x1).monotone
            ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
        omega
      have haLe : sixVertexDefectLowerAdvance i last ≤ 2 := by
        by_cases hli : last = i <;>
          simp [sixVertexDefectLowerAdvance, hli]
      have hbound2 : (sixVertexSectorPosition x2 last).val +
          sixVertexDefectLowerAdvance i last < N := by
        have hlast1eq : (sixVertexSectorPosition x1 last).val =
            (sixVertexSectorPosition x last).val - 1 := by
          exact sixVertexSectorPosition_shiftLeftSector_apply_val
            x hn hfirst last
        rw [hlast1eq] at hlast1Pos
        rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
          sixVertexSectorPosition_shiftLeftSector_apply_val]
        have hlastN := (sixVertexSectorPosition x last).isLt
        omega
      let y := sixVertexDefectLowerMoveSector x2 hx2 hn i hd2 hbound2
      have h2y := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
        x2 hx2 hn i hi hd2 hbound2
      refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent h2y).2,
        (hxx1.reachable.trans hx1x2.reachable).trans h2y.reachable, ?_⟩
      rw [sixVertexDefectLowerMoveSector_gapDefects
        x2 hx2 hn i hi hd2 hbound2, hx2gap, hx1gap]

theorem sixVertexInfinityGraph_reachable_of_defectLowerSteps
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) {d : Fin n → Nat}
    (hsteps : Relation.ReflTransGen SixVertexDefectLowerStep
      (sixVertexSectorGapDefects x) d) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y = d := by
  induction hsteps with
  | refl => exact ⟨x, hx, SimpleGraph.Reachable.rfl, rfl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨z, hz, hxz, hzgap⟩ := ih
      obtain ⟨i, hi, hd, rfl⟩ := hbc
      have hd' : 0 < sixVertexSectorGapDefects z i := by
        rw [hzgap]
        exact hd
      obtain ⟨y, hy, hzy, hygap⟩ :=
        sixVertexInfinityGraph_reachable_defectLower z hz hn i hi hd'
      refine ⟨y, hy, hxz.trans hzy, ?_⟩
      rw [hygap, hzgap]



theorem sixVertexInfinityGraph_reachable_first_zero
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y = sixVertexSectorGapDefects x ∧
      (sixVertexSectorPosition y ⟨0, hn⟩).val = 0 := by
  by_cases hzero : (sixVertexSectorPosition x ⟨0, hn⟩).val = 0
  · exact ⟨x, hx, SimpleGraph.Reachable.rfl, rfl, hzero⟩
  · have hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val :=
      Nat.pos_of_ne_zero hzero
    let x1 := sixVertexShiftLeftSector x hn hfirst
    have hx1 := sixVertexShiftLeftSector_noAdjacent x hx hn hfirst
    have hxx1 := sixVertexInfinityGraph_adj_shiftLeftSector x hx hn hfirst
    obtain ⟨y, hy, h1y, hygap, hyzero⟩ :=
      sixVertexInfinityGraph_reachable_first_zero hn x1 hx1
    refine ⟨y, hy, hxx1.reachable.trans h1y, ?_, hyzero⟩
    rw [hygap, sixVertexShiftLeftSector_gapDefects x hn hfirst]
termination_by (sixVertexSectorPosition x ⟨0, hn⟩).val
decreasing_by
  have hpos := sixVertexSectorPosition_shiftLeftSector_apply_val
    x hn hfirst (⟨0, hn⟩ : Fin n)
  change (sixVertexSectorPosition x1 ⟨0, hn⟩).val <
    (sixVertexSectorPosition x ⟨0, hn⟩).val
  rw [hpos]
  omega

theorem sixVertexSector_eq_of_gapDefects_eq_of_first_eq
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hy : SixVertexSectorNoAdjacent y)
    (hgap : sixVertexSectorGapDefects x = sixVertexSectorGapDefects y)
    (hfirst : (sixVertexSectorPosition x ⟨0, hn⟩).val =
      (sixVertexSectorPosition y ⟨0, hn⟩).val) :
    x = y := by
  have hposNat : ∀ (k : Nat) (hk : k < n),
      (sixVertexSectorPosition x ⟨k, hk⟩).val =
        (sixVertexSectorPosition y ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa only using hfirst
    | succ k ih =>
        intro hk
        have hkprev : k < n := by omega
        have hkstep : k + 1 < n := by omega
        have hprev := ih hkprev
        have hgapk := congrFun hgap (⟨k, hkprev⟩ : Fin n)
        have hxadj := hx.1 k hkstep
        have hyadj := hy.1 k hkstep
        have hxrec :
            (sixVertexSectorPosition x ⟨k + 1, hkstep⟩).val =
              (sixVertexSectorPosition x ⟨k, hkprev⟩).val +
                sixVertexSectorGapDefects x ⟨k, hkprev⟩ + 2 := by
          rw [sixVertexSectorGapDefects, sixVertexSectorGap]
          simp only [dif_pos hkstep]
          omega
        have hyrec :
            (sixVertexSectorPosition y ⟨k + 1, hkstep⟩).val =
              (sixVertexSectorPosition y ⟨k, hkprev⟩).val +
                sixVertexSectorGapDefects y ⟨k, hkprev⟩ + 2 := by
          rw [sixVertexSectorGapDefects, sixVertexSectorGap]
          simp only [dif_pos hkstep]
          omega
        omega
  have hpos : sixVertexSectorPosition x = sixVertexSectorPosition y := by
    ext i
    exact hposNat i.val i.isLt
  exact Set.powersetCard.ofFinEmbEquiv.symm.injective hpos

theorem sixVertexNoAdjacentInfinityGraph_reachable_of_full
    {N n : Nat} (x y : SixVertexNoAdjacentSector N n)
    (h : (sixVertexInfinityGraph N n).Reachable x.1 y.1) :
    (sixVertexNoAdjacentInfinityGraph N n).Reachable x y := by
  classical
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  let f : SixVertexSector N n → SixVertexNoAdjacentSector N n := fun z =>
    if hz : SixVertexSectorNoAdjacent z then ⟨z, hz⟩ else x
  have hlift : Relation.ReflTransGen
      (sixVertexNoAdjacentInfinityGraph N n).Adj (f x.1) (f y.1) := h.lift f (by
    intro a b hab
    have hs := sixVertexInfinityGraph_adj_noAdjacent hab
    simp only [f, dif_pos hs.1, dif_pos hs.2]
    exact hab)
  have hfx : f x.1 = x := by
    apply Subtype.ext
    simp [f, x.2]
  have hfy : f y.1 = y := by
    apply Subtype.ext
    simp [f, y.2]
  simpa only [hfx, hfy] using hlift



theorem sixVertexNoAdjacentInfinityGraph_preconnected
    {N n : Nat} (hn : 0 < n) :
    (sixVertexNoAdjacentInfinityGraph N n).Preconnected := by
  intro x y
  have hxsteps := sixVertexDefectLowerStep_reaches_pile hn
    (sixVertexSectorGapDefects x.1)
  have hysteps := sixVertexDefectLowerStep_reaches_pile hn
    (sixVertexSectorGapDefects y.1)
  have hxsum := sum_sixVertexSectorGapDefects x.1 x.2 hn
  have hysum := sum_sixVertexSectorGapDefects y.1 y.2 hn
  rw [hxsum] at hxsteps
  rw [hysum] at hysteps
  obtain ⟨xp, hxp, hxxp, hxpgap⟩ :=
    sixVertexInfinityGraph_reachable_of_defectLowerSteps hn x.1 x.2 hxsteps
  obtain ⟨yp, hyp, hyyp, hypgap⟩ :=
    sixVertexInfinityGraph_reachable_of_defectLowerSteps hn y.1 y.2 hysteps
  obtain ⟨x0, hx0, hxpx0, hx0gap, hx0first⟩ :=
    sixVertexInfinityGraph_reachable_first_zero hn xp hxp
  obtain ⟨y0, hy0, hypy0, hy0gap, hy0first⟩ :=
    sixVertexInfinityGraph_reachable_first_zero hn yp hyp
  have hxy0 : x0 = y0 := by
    apply sixVertexSector_eq_of_gapDefects_eq_of_first_eq hn x0 y0 hx0 hy0
    · rw [hx0gap, hxpgap, hy0gap, hypgap]
    · rw [hx0first, hy0first]
  subst y0
  have hfull : (sixVertexInfinityGraph N n).Reachable x.1 y.1 :=
    (hxxp.trans hxpx0).trans ((hyyp.trans hypy0).symm)
  exact sixVertexNoAdjacentInfinityGraph_reachable_of_full x y hfull

theorem sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk
    (M N n : Nat) (x y : SixVertexNoAdjacentSector N n) :
    (sixVertexNoAdjacentTransferInfinity N n ^ M) x y =
      Fintype.card {w : (sixVertexNoAdjacentInfinityGraph N n).Walk x y |
        w.length = M} := by
  rw [← sixVertexNoAdjacentInfinityGraph_adjMatrix]
  exact (sixVertexNoAdjacentInfinityGraph N n).adjMatrix_pow_apply_eq_card_walk
    M x y



theorem sixVertexNoAdjacentTransferInfinity_isIrreducible
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexNoAdjacentTransferInfinity N n).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (sixVertexNoAdjacentTransferInfinity_nonneg N n)]
  intro x y
  let even := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let odd := sixVertexNoAdjacentAlternatingOdd N n hn hhalf
  have hconn := sixVertexNoAdjacentInfinityGraph_preconnected
    (N := N) hn
  let p := (hconn x even).some
  let q := (hconn odd y).some
  have heo : (sixVertexNoAdjacentInfinityGraph N n).Adj even odd :=
    sixVertexNoAdjacentInfinityGraph_adj_alternating hn hhalf
  let w : (sixVertexNoAdjacentInfinityGraph N n).Walk x y :=
    p.append (heo.toWalk.append q)
  have hwpos : 0 < w.length := by
    simp [w]
  refine ⟨w.length, hwpos, ?_⟩
  rw [sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk]
  have hnonempty : Nonempty
      {u : (sixVertexNoAdjacentInfinityGraph N n).Walk x y |
        u.length = w.length} := ⟨⟨w, rfl⟩⟩
  exact_mod_cast Fintype.card_pos_iff.mpr hnonempty

end

end StatMech.FrontierD
