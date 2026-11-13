/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBalancedBoundaryGluing
import Code.FrontierD.SixVertexFiniteTorus
import Code.FrontierD.SixVertexParticleHole

open Finset Matrix

namespace StatMech.FrontierD

def svRowPrefixCount {N : Nat} (x : SixVertexRow N) (k : Fin N) : Nat :=
  ∑ i ∈ Finset.Iic k, (x i).toNat

theorem svRowPrefixCount_zero {N : Nat} (x : SixVertexRow (N + 1)) :
    svRowPrefixCount x 0 = (x 0).toNat := by
  unfold svRowPrefixCount
  have hset : Finset.Iic (0 : Fin (N + 1)) = {0} := by
    ext i
    simp
  rw [hset]
  simp

theorem svRowPrefixCount_succ {N : Nat} (x : SixVertexRow (N + 1))
    (i : Fin N) :
    svRowPrefixCount x i.succ =
      svRowPrefixCount x i.castSucc + (x i.succ).toNat := by
  unfold svRowPrefixCount
  have hset : Finset.Iic i.succ = insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val,
      Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hset, Finset.sum_insert]
  · omega
  · simp

theorem svRowPrefixCount_last {N : Nat} (x : SixVertexRow (N + 1)) :
    svRowPrefixCount x (Fin.last N) = sixVertexUpCount x := by
  unfold svRowPrefixCount sixVertexUpCount
  have hset : Finset.Iic (Fin.last N) = Finset.univ := by
    exact Finset.eq_univ_of_forall fun i => Finset.mem_Iic.mpr (Fin.le_last i)
  rw [hset, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> simp

def svHorizontalIncomingCount {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) (i : Fin N) : Nat :=
  (x i).toNat + (!y i).toNat +
    (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat

def svHorizontalIce {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) : Prop :=
  ∀ i, svHorizontalIncomingCount hN x y h i = 2

def svFinLast {N : Nat} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (by omega)⟩

theorem svHorizontalIce_step {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) :
    (h i).toNat + (y i).toNat =
      (h (SixVertexArrows.cyclicPred hN i)).toNat + (x i).toNat := by
  have hi := hice i
  unfold svHorizontalIncomingCount at hi
  cases hx : x i <;> cases hy : y i <;>
    cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
    cases hh : h i <;> simp [hx, hy, hp, hh] at hi ⊢

theorem svHorizontalIce_prefix {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (k : Fin N) :
    (h k).toNat + svRowPrefixCount y k =
      (h (svFinLast hN)).toNat + svRowPrefixCount x k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  induction k using Fin.induction with
  | zero =>
      rw [svRowPrefixCount_zero, svRowPrefixCount_zero]
      have hs := svHorizontalIce_step (Nat.succ_pos m) hice (0 : Fin (m + 1))
      simpa [SixVertexArrows.cyclicPred] using hs
  | succ i ih =>
      rw [svRowPrefixCount_succ, svRowPrefixCount_succ]
      have hs := svHorizontalIce_step (Nat.succ_pos m) hice i.succ
      have hpred : SixVertexArrows.cyclicPred (Nat.succ_pos m) i.succ =
          i.castSucc := by
        ext
        simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
        rw [show i.val + 1 + (m + 1) - 1 = (m + 1) + i.val by omega,
          Nat.add_mod_left,
          Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self m))]
      rw [hpred] at hs
      omega

def svRowPrefixForward {N : Nat} (x y : SixVertexRow N) : Prop :=
  ∀ k, svRowPrefixCount y k ≤ svRowPrefixCount x k ∧
    svRowPrefixCount x k ≤ svRowPrefixCount y k + 1

def svRowSectorAt {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) : SixVertexSector N n :=
  ⟨({i | x i} : Finset (Fin N)), hx⟩

@[simp] theorem svRowSectorAt_row {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) :
    sixVertexSectorRow (svRowSectorAt x hx) = x := by
  funext i
  simp [svRowSectorAt, sixVertexSectorRow]

theorem svRowPrefixCount_eq_sector {N n : Nat} (x : SixVertexRow N)
    (hx : sixVertexUpCount x = n) (k : Fin N) :
    svRowPrefixCount x k =
      sixVertexSectorPrefixCount (svRowSectorAt x hx) k := by
  unfold svRowPrefixCount sixVertexSectorPrefixCount
  have hsum :
      (∑ i ∈ Finset.Iic k, (x i).toNat) =
        ((Finset.Iic k).filter fun i => x i = true).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases x i <;> simp
  rw [hsum]
  congr 1
  ext i
  simp [svRowSectorAt, and_comm]

theorem svForwardInterlaced_iff_prefix {N : Nat}
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    SixVertexForwardInterlaced x y ↔ svRowPrefixForward x y := by
  let xs := svRowSectorAt x rfl
  let ys := svRowSectorAt y hcount.symm
  have hysrow : sixVertexSectorRow ys = y := svRowSectorAt_row y hcount.symm
  have hxsrow : sixVertexSectorRow xs = x := svRowSectorAt_row x rfl
  constructor
  · intro h
    have hpos := sixVertexPositionsForwardInterlaced_of_forward xs ys
      (by simpa [hxsrow, hysrow] using h)
    have hpref := sixVertexSectorPrefixForward_of_positions xs ys hpos
    intro k
    have hk := hpref k
    simpa [svRowPrefixCount_eq_sector, xs, ys, hxsrow, hysrow] using hk
  · intro h
    have hpref : SixVertexSectorPrefixForward xs ys := by
      intro k
      have hk := h k
      simpa [svRowPrefixCount_eq_sector, xs, ys, hxsrow, hysrow] using hk
    have hpos := sixVertexPositionsForwardInterlaced_of_prefix xs ys hpref
    simpa [hxsrow, hysrow] using sixVertexForwardInterlaced_of_positions xs ys hpos

def svHorizontalPrefixRelation {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) : Prop :=
  ∀ k, (h k).toNat + svRowPrefixCount y k =
    (h (svFinLast hN)).toNat + svRowPrefixCount x k

theorem svCyclicPred_zero {N : Nat} (hN : 0 < N) :
    SixVertexArrows.cyclicPred hN (⟨0, hN⟩ : Fin N) = svFinLast hN := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  ext
  simp [SixVertexArrows.cyclicPred, svFinLast]

theorem svCyclicPred_succ {N : Nat} (i : Fin N) :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) i.succ = i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
  rw [show i.val + 1 + (N + 1) - 1 = (N + 1) + i.val by omega,
    Nat.add_mod_left,
    Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self N))]

theorem svHorizontalIce_iff_prefixRelation {N : Nat} (hN : 0 < N)
    (x y h : SixVertexRow N) :
    svHorizontalIce hN x y h ↔ svHorizontalPrefixRelation hN x y h := by
  constructor
  · intro hice
    exact svHorizontalIce_prefix hN hice
  · intro hrel i
    have hstep : (h i).toNat + (y i).toNat =
        (h (SixVertexArrows.cyclicPred hN i)).toNat + (x i).toNat := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      induction i using Fin.induction with
      | zero =>
          have h0 := hrel (0 : Fin (m + 1))
          rw [svRowPrefixCount_zero, svRowPrefixCount_zero] at h0
          have hpred : SixVertexArrows.cyclicPred hN (0 : Fin (m + 1)) =
              svFinLast hN := by
            ext
            simp [SixVertexArrows.cyclicPred, svFinLast]
          rw [hpred]
          exact h0
      | succ i ih =>
          have hsucc := hrel i.succ
          have hprev := hrel i.castSucc
          rw [svRowPrefixCount_succ, svRowPrefixCount_succ] at hsucc
          rw [svCyclicPred_succ]
          omega
    unfold svHorizontalIncomingCount
    cases hx : x i <;> cases hy : y i <;>
      cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
      cases hh : h i <;> simp [hx, hy, hp, hh] at hstep ⊢

def svForwardHorizontal {N : Nat} (x y : SixVertexRow N) : SixVertexRow N :=
  fun k => decide (svRowPrefixCount y k < svRowPrefixCount x k)

def svBackwardHorizontal {N : Nat} (x y : SixVertexRow N) : SixVertexRow N :=
  fun k => decide (svRowPrefixCount y k ≤ svRowPrefixCount x k)

theorem svForwardHorizontal_relation {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward x y) :
    svHorizontalPrefixRelation hN x y (svForwardHorizontal x y) := by
  have hlast : svForwardHorizontal x y (svFinLast hN) = false := by
    unfold svForwardHorizontal
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hlastEq : svFinLast hN = Fin.last m := by
      ext
      simp [svFinLast]
    rw [hlastEq]
    have hx := svRowPrefixCount_last x
    have hy := svRowPrefixCount_last y
    rw [hx, hy, hcount]
    simp
  intro k
  have hk := hpref k
  rw [hlast]
  simp only [Bool.toNat_false, zero_add]
  unfold svForwardHorizontal
  by_cases hlt : svRowPrefixCount y k < svRowPrefixCount x k
  · simp [hlt]
    omega
  · simp [hlt]
    omega

theorem svBackwardHorizontal_relation {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward y x) :
    svHorizontalPrefixRelation hN x y (svBackwardHorizontal x y) := by
  have hlast : svBackwardHorizontal x y (svFinLast hN) = true := by
    unfold svBackwardHorizontal
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hlastEq : svFinLast hN = Fin.last m := by
      ext
      simp [svFinLast]
    rw [hlastEq]
    have hx := svRowPrefixCount_last x
    have hy := svRowPrefixCount_last y
    rw [hx, hy, hcount]
    simp
  intro k
  have hk := hpref k
  rw [hlast]
  simp only [Bool.toNat_true]
  unfold svBackwardHorizontal
  by_cases hle : svRowPrefixCount y k ≤ svRowPrefixCount x k
  · simp [hle]
    omega
  · simp [hle]
    omega

theorem svForwardHorizontal_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward x y) :
    svHorizontalIce hN x y (svForwardHorizontal x y) :=
  (svHorizontalIce_iff_prefixRelation hN x y _).2
    (svForwardHorizontal_relation hN x y hcount hpref)

theorem svBackwardHorizontal_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward y x) :
    svHorizontalIce hN x y (svBackwardHorizontal x y) :=
  (svHorizontalIce_iff_prefixRelation hN x y _).2
    (svBackwardHorizontal_relation hN x y hcount hpref)

theorem svRowPrefixCount_finLast {N : Nat} (hN : 0 < N)
    (x : SixVertexRow N) :
    svRowPrefixCount x (svFinLast hN) = sixVertexUpCount x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hlastEq : svFinLast hN = Fin.last m := by
    ext
    simp [svFinLast]
  rw [hlastEq]
  exact svRowPrefixCount_last x

theorem svHorizontalIce_upCount_eq {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    sixVertexUpCount x = sixVertexUpCount y := by
  have hrel := (svHorizontalIce_iff_prefixRelation hN x y h).1 hice
  have hlast := hrel (svFinLast hN)
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y] at hlast
  omega

theorem svHorizontalIce_cases {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    (h (svFinLast hN) = false ∧ svRowPrefixForward x y ∧
        h = svForwardHorizontal x y) ∨
      (h (svFinLast hN) = true ∧ svRowPrefixForward y x ∧
        h = svBackwardHorizontal x y) := by
  have hrel := (svHorizontalIce_iff_prefixRelation hN x y h).1 hice
  have hcount := svHorizontalIce_upCount_eq hN hice
  cases hlast : h (svFinLast hN) with
  | false =>
      left
      have hpref : svRowPrefixForward x y := by
        intro k
        have hk := hrel k
        rw [hlast] at hk
        simp only [Bool.toNat_false, zero_add] at hk
        have hb : (h k).toNat ≤ 1 := by cases h k <;> simp
        constructor <;> omega
      refine ⟨rfl, hpref, ?_⟩
      funext k
      have hk := hrel k
      rw [hlast] at hk
      simp only [Bool.toNat_false, zero_add] at hk
      unfold svForwardHorizontal
      by_cases hlt : svRowPrefixCount y k < svRowPrefixCount x k
      · have hone : h k = true := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hlt, hone]
      · have hzero : h k = false := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hlt, hzero]
  | true =>
      right
      have hpref : svRowPrefixForward y x := by
        intro k
        have hk := hrel k
        rw [hlast] at hk
        simp only [Bool.toNat_true] at hk
        have hb : (h k).toNat ≤ 1 := by cases h k <;> simp
        constructor <;> omega
      refine ⟨rfl, hpref, ?_⟩
      funext k
      have hk := hrel k
      rw [hlast] at hk
      simp only [Bool.toNat_true] at hk
      unfold svBackwardHorizontal
      by_cases hle : svRowPrefixCount y k ≤ svRowPrefixCount x k
      · have hone : h k = true := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hle, hone]
      · have hzero : h k = false := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hle, hzero]

theorem svRow_eq_of_prefixCount_eq {N : Nat} {x y : SixVertexRow N}
    (hprefix : ∀ k, svRowPrefixCount x k = svRowPrefixCount y k) : x = y := by
  funext k
  cases N with
  | zero => exact Fin.elim0 k
  | succ m =>
      induction k using Fin.induction with
      | zero =>
          have h0 := hprefix (0 : Fin (m + 1))
          rw [svRowPrefixCount_zero, svRowPrefixCount_zero] at h0
          cases hx : x 0 <;> cases hy : y 0 <;> simp [hx, hy] at h0 ⊢
      | succ i ih =>
          have hs := hprefix i.succ
          have hp := hprefix i.castSucc
          rw [svRowPrefixCount_succ, svRowPrefixCount_succ, hp] at hs
          cases hx : x i.succ <;> cases hy : y i.succ <;> simp [hx, hy] at hs ⊢

theorem svRowPrefixForward_antisymm {N : Nat} {x y : SixVertexRow N}
    (hxy : svRowPrefixForward x y) (hyx : svRowPrefixForward y x) : x = y := by
  apply svRow_eq_of_prefixCount_eq
  intro k
  exact Nat.le_antisymm (hyx k).1 (hxy k).1

theorem svForwardHorizontal_last {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    svForwardHorizontal x y (svFinLast hN) = false := by
  unfold svForwardHorizontal
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y, hcount]
  simp

theorem svBackwardHorizontal_last {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    svBackwardHorizontal x y (svFinLast hN) = true := by
  unfold svBackwardHorizontal
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y, hcount]
  simp

def svHorizontalOfBool {N : Nat} (x y : SixVertexRow N) (b : Bool) :
    SixVertexRow N :=
  if b then svBackwardHorizontal x y else svForwardHorizontal x y

theorem svHorizontalOfBool_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (b : Bool)
    (hb : if b then svRowPrefixForward y x else svRowPrefixForward x y) :
    svHorizontalIce hN x y (svHorizontalOfBool x y b) := by
  cases b with
  | false =>
      exact svForwardHorizontal_ice hN x y hcount (by simpa using hb)
  | true =>
      exact svBackwardHorizontal_ice hN x y hcount (by simpa using hb)

def svHorizontalIceEquivBool {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    {h : SixVertexRow N // svHorizontalIce hN x y h} ≃
      {b : Bool // if b then svRowPrefixForward y x else svRowPrefixForward x y} where
  toFun h := by
    refine ⟨h.1 (svFinLast hN), ?_⟩
    obtain hcase | hcase := svHorizontalIce_cases hN h.2
    · rw [hcase.1]
      exact hcase.2.1
    · rw [hcase.1]
      exact hcase.2.1
  invFun b := ⟨svHorizontalOfBool x y b.1,
    svHorizontalOfBool_ice hN x y hcount b.1 b.2⟩
  left_inv h := by
    apply Subtype.ext
    obtain hcase | hcase := svHorizontalIce_cases hN h.2
    · rw [hcase.2.2]
      simp [svHorizontalOfBool, hcase.1]
    · rw [hcase.2.2]
      simp [svHorizontalOfBool, hcase.1]
  right_inv b := by
    apply Subtype.ext
    cases hb : b.1 with
    | false =>
        simpa [svHorizontalOfBool, hb] using
          svForwardHorizontal_last hN x y hcount
    | true =>
        simpa [svHorizontalOfBool, hb] using
          svBackwardHorizontal_last hN x y hcount

def svHorizontalIsC {N : Nat} (hN : 0 < N)
    (h : SixVertexRow N) (i : Fin N) : Prop :=
  (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat = 0 ∨
    (h (SixVertexArrows.cyclicPred hN i)).toNat + (!h i).toNat = 2

noncomputable def svHorizontalLocalWeight {N : Nat} (hN : 0 < N)
    (c : Real) (x y h : SixVertexRow N) (i : Fin N) : Real := by
  classical
  exact if svHorizontalIncomingCount hN x y h i = 2 then
    if svHorizontalIsC hN h i then c else 1
  else 0

noncomputable def svHorizontalRowWeight {N : Nat} (hN : 0 < N)
    (c : Real) (x y h : SixVertexRow N) : Real :=
  ∏ i, svHorizontalLocalWeight hN c x y h i

theorem svHorizontalIsC_iff_ne {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) : svHorizontalIsC hN h i ↔ x i ≠ y i := by
  have hs := svHorizontalIce_step hN hice i
  unfold svHorizontalIsC
  cases hx : x i <;> cases hy : y i <;>
    cases hp : h (SixVertexArrows.cyclicPred hN i) <;>
    cases hh : h i <;> simp [hx, hy, hp, hh] at hs ⊢

theorem svHorizontalLocalWeight_of_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h)
    (i : Fin N) :
    svHorizontalLocalWeight hN c x y h i = if x i ≠ y i then c else 1 := by
  classical
  unfold svHorizontalLocalWeight
  rw [if_pos (hice i)]
  rw [if_congr (svHorizontalIsC_iff_ne hN hice i) rfl rfl]

theorem svHorizontalRowWeight_of_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    svHorizontalRowWeight hN c x y h = c ^ sixVertexRowDistance x y := by
  unfold svHorizontalRowWeight sixVertexRowDistance
  simp_rw [svHorizontalLocalWeight_of_ice hN c hice]
  rw [Finset.prod_ite]
  simp

theorem svHorizontalRowWeight_eq_zero_of_not_ice {N : Nat} (hN : 0 < N)
    (c : Real) {x y h : SixVertexRow N} (hice : ¬svHorizontalIce hN x y h) :
    svHorizontalRowWeight hN c x y h = 0 := by
  simp only [svHorizontalIce, not_forall] at hice
  obtain ⟨i, hi⟩ := hice
  unfold svHorizontalRowWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold svHorizontalLocalWeight
  rw [if_neg hi]

open Classical in
theorem svHorizontalRowWeight_sum_formula {N : Nat} (hN : 0 < N)
    (c : Real) (x y : SixVertexRow N)
    (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) =
      (if svRowPrefixForward x y then c ^ sixVertexRowDistance x y else 0) +
      (if svRowPrefixForward y x then c ^ sixVertexRowDistance x y else 0) := by
  classical
  let P : Bool → Prop := fun b =>
    if b then svRowPrefixForward y x else svRowPrefixForward x y
  letI : Fintype {b : Bool // P b} := Fintype.ofFinite _
  let e := svHorizontalIceEquivBool hN x y hcount
  have hfilter :
      (∑ h : {h : SixVertexRow N // svHorizontalIce hN x y h},
        svHorizontalRowWeight hN c x y h.1) =
      ∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun h : SixVertexRow N => svHorizontalIce hN x y h)
      (by simp)]
    apply Finset.sum_filter_of_ne
    intro h _ hweight
    by_contra hnot
    exact hweight (svHorizontalRowWeight_eq_zero_of_not_ice hN c hnot)
  rw [← hfilter]
  calc
    (∑ h : {h : SixVertexRow N // svHorizontalIce hN x y h},
        svHorizontalRowWeight hN c x y h.1) =
      ∑ b : {b : Bool // P b},
        svHorizontalRowWeight hN c x y (e.symm b).1 := by
          exact (e.symm.sum_comp _).symm
    _ = ∑ _b : {b : Bool // P b}, c ^ sixVertexRowDistance x y := by
      apply Fintype.sum_congr
      intro b
      exact svHorizontalRowWeight_of_ice hN c (e.symm b).2
    _ = (if svRowPrefixForward x y then c ^ sixVertexRowDistance x y else 0) +
        (if svRowPrefixForward y x then c ^ sixVertexRowDistance x y else 0) := by
      have hsub := Finset.sum_subtype (p := P) (F := inferInstance)
        (Finset.univ.filter P)
        (by intro b; simp [P])
        (fun _b : Bool => c ^ sixVertexRowDistance x y)
      rw [← hsub]
      have hcardFalse :
          #{b ∈ (Finset.univ : Finset Bool) | b = false} = 1 := by
        rw [show ({b ∈ (Finset.univ : Finset Bool) | b = false}) = {false} by
          ext b
          cases b <;> simp]
        simp
      have hcardTrue :
          #{b ∈ (Finset.univ : Finset Bool) | b = true} = 1 := by
        rw [show ({b ∈ (Finset.univ : Finset Bool) | b = true}) = {true} by
          ext b
          cases b <;> simp]
        simp
      have htf : ({true, false} : Finset Bool) = Finset.univ := by
        ext b
        cases b <;> simp
      have hcardFalse' :
          #{b ∈ ({true, false} : Finset Bool) | b = false} = 1 := by
        rw [htf]
        exact hcardFalse
      have hcardTrue' :
          #{b ∈ ({true, false} : Finset Bool) | b = true} = 1 := by
        rw [htf]
        exact hcardTrue
      by_cases hxy : svRowPrefixForward x y <;>
        by_cases hyx : svRowPrefixForward y x <;>
        norm_num [P, hxy, hyx, hcardFalse, hcardTrue,
          hcardFalse', hcardTrue']; ring

theorem svRowPrefixForward_self {N : Nat} (x : SixVertexRow N) :
    svRowPrefixForward x x := by
  intro k
  omega

theorem svHorizontalRowWeight_sum_eq_transfer {N : Nat} (hN : 0 < N)
    (c : Real) (x y : SixVertexRow N) :
    (∑ h : SixVertexRow N, svHorizontalRowWeight hN c x y h) =
      sixVertexTransfer N c x y := by
  classical
  by_cases hcount : sixVertexUpCount x = sixVertexUpCount y
  · rw [svHorizontalRowWeight_sum_formula hN c x y hcount]
    by_cases hxy : x = y
    · subst y
      simp [sixVertexTransfer, svRowPrefixForward_self, sixVertexRowDistance]
      norm_num
    · by_cases hinter : SixVertexInterlaced x y
      · rcases hinter with hforward | hbackward
        · have hpref : svRowPrefixForward x y :=
            (svForwardInterlaced_iff_prefix x y hcount).1 hforward
          have hinter' : SixVertexInterlaced x y := Or.inl hforward
          have hnback : ¬svRowPrefixForward y x := by
            intro hback
            exact hxy (svRowPrefixForward_antisymm hpref hback)
          simp [sixVertexTransfer, hxy, hinter', hpref, hnback]
        · have hpref : svRowPrefixForward y x :=
            (svForwardInterlaced_iff_prefix y x hcount.symm).1 hbackward
          have hinter' : SixVertexInterlaced x y := Or.inr hbackward
          have hnforward : ¬svRowPrefixForward x y := by
            intro hfor
            exact hxy (svRowPrefixForward_antisymm hfor hpref)
          simp [sixVertexTransfer, hxy, hinter', hpref, hnforward]
      · have hnforward : ¬svRowPrefixForward x y := by
          intro hpref
          apply hinter
          exact Or.inl ((svForwardInterlaced_iff_prefix x y hcount).2 hpref)
        have hnback : ¬svRowPrefixForward y x := by
          intro hpref
          apply hinter
          exact Or.inr ((svForwardInterlaced_iff_prefix y x hcount.symm).2 hpref)
        simp [sixVertexTransfer, hxy, hinter, hnforward, hnback]
  · have hzero (h : SixVertexRow N) :
        svHorizontalRowWeight hN c x y h = 0 := by
      apply svHorizontalRowWeight_eq_zero_of_not_ice
      intro hice
      exact hcount (svHorizontalIce_upCount_eq hN hice)
    simp_rw [hzero]
    simp [sixVertexTransfer_eq_zero_of_upCount_ne c hcount]

theorem svFinitePeriodicSucc_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (finitePeriodicSucc hN) := by
  intro i j hij
  apply Fin.ext
  have hijv := congrArg Fin.val hij
  change (i.val + 1) % N = (j.val + 1) % N at hijv
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi] at hijv
    by_cases hj : j.val + 1 < N
    · rw [Nat.mod_eq_of_lt hj] at hijv
      omega
    · have hjeq : j.val + 1 = N := by omega
      rw [hjeq, Nat.mod_self] at hijv
      omega
  · have hieq : i.val + 1 = N := by omega
    rw [hieq, Nat.mod_self] at hijv
    by_cases hj : j.val + 1 < N
    · rw [Nat.mod_eq_of_lt hj] at hijv
      omega
    · omega

noncomputable def svFinitePeriodicSuccEquiv {N : Nat} (hN : 0 < N) :
    Fin N ≃ Fin N :=
  Equiv.ofBijective (finitePeriodicSucc hN)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨svFinitePeriodicSucc_injective hN, rfl⟩)

@[simp] theorem svFinitePeriodicSuccEquiv_apply {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    svFinitePeriodicSuccEquiv hN i = finitePeriodicSucc hN i := rfl

def svTorusHorizontalRows (T : EvenTorus) (omega : SixVertexArrows T) :
    Fin T.height → SixVertexRow T.width :=
  fun j i => omega.horizontal (i, j)

def svTorusVerticalRows (T : EvenTorus) (omega : SixVertexArrows T) :
    Fin T.height → SixVertexRow T.width :=
  fun j i => omega.vertical (i, j)

def svTorusRowsEquiv (T : EvenTorus) :
    SixVertexArrows T ≃
      (Fin T.height → SixVertexRow T.width) ×
        (Fin T.height → SixVertexRow T.width) where
  toFun omega := (svTorusHorizontalRows T omega, svTorusVerticalRows T omega)
  invFun rows :=
    { horizontal := fun ij => rows.1 ij.2 ij.1
      vertical := fun ij => rows.2 ij.2 ij.1 }
  left_inv omega := by
    apply SixVertexArrows.ext <;> funext ij <;> rfl
  right_inv rows := by
    apply Prod.ext <;> funext j i <;> rfl

theorem svHorizontalLocalWeight_eq_torusLocalWeight
    (T : EvenTorus) (c : Real) (omega : SixVertexArrows T)
    (i : Fin T.width) (j : Fin T.height) :
    svHorizontalLocalWeight T.width_pos c
        (svTorusVerticalRows T omega
          (SixVertexArrows.cyclicPred T.height_pos j))
        (svTorusVerticalRows T omega j)
        (svTorusHorizontalRows T omega j) i =
      omega.localWeight c (i, j) := by
  classical
  unfold svHorizontalLocalWeight SixVertexArrows.localWeight
  simp only [svHorizontalIncomingCount, svHorizontalIsC,
    svTorusVerticalRows, svTorusHorizontalRows,
    SixVertexArrows.incomingCount, SixVertexArrows.IsCType]
  apply if_congr
  · omega
  · rfl
  · rfl

theorem svTorusWeight_eq_product_rowWeights
    (T : EvenTorus) (c : Real) (omega : SixVertexArrows T) :
    omega.weight c =
      ∏ j : Fin T.height,
        svHorizontalRowWeight T.width_pos c
          (svTorusVerticalRows T omega
            (SixVertexArrows.cyclicPred T.height_pos j))
          (svTorusVerticalRows T omega j)
          (svTorusHorizontalRows T omega j) := by
  rw [SixVertexArrows.weight, Fintype.prod_prod_type]
  unfold svHorizontalRowWeight
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro i hi
  exact (svHorizontalLocalWeight_eq_torusLocalWeight T c omega i j).symm

noncomputable def svTorusBalancedArrowPartitionSum
    (T : EvenTorus) (c : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0

theorem svTorusSeam_balanced_iff_lastRow
    (T : EvenTorus) (omega : SixVertexArrows T) :
    (sixVertexTorusSeam T omega).Balanced ↔
      sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = T.width / 2 := by
  rfl

theorem svTorusBalancedArrowPartitionSum_eq_rowSum
    (T : EvenTorus) (c : Real) :
    svTorusBalancedArrowPartitionSum T c =
      ∑ vrows : Fin T.height → SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
  classical
  rw [svTorusBalancedArrowPartitionSum]
  calc
    (∑ omega : SixVertexArrows T,
      if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0) =
        ∑ rows : (Fin T.height → SixVertexRow T.width) ×
            (Fin T.height → SixVertexRow T.width),
          if sixVertexUpCount (rows.2 (svFinLast T.height_pos)) = T.width / 2 then
            ∏ j : Fin T.height,
              svHorizontalRowWeight T.width_pos c
                (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
                (rows.2 j) (rows.1 j)
          else 0 := by
      apply Fintype.sum_equiv (svTorusRowsEquiv T)
      intro omega
      apply if_congr
      · exact svTorusSeam_balanced_iff_lastRow T omega
      · exact svTorusWeight_eq_product_rowWeights T c omega
      · rfl
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
          ∑ hrows : Fin T.height → SixVertexRow T.width,
            if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
              ∏ j : Fin T.height,
                svHorizontalRowWeight T.width_pos c
                  (vrows (SixVertexArrows.cyclicPred T.height_pos j))
                  (vrows j) (hrows j)
            else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2 then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
      apply Finset.sum_congr rfl
      intro vrows hvrows
      by_cases hbal :
          sixVertexUpCount (vrows (svFinLast T.height_pos)) = T.width / 2
      · simp only [if_pos hbal]
        rw [← Fintype.prod_sum]
        apply Finset.prod_congr rfl
        intro j hj
        exact svHorizontalRowWeight_sum_eq_transfer T.width_pos c _ _
      · simp [hbal]

theorem svCyclicPred_finitePeriodicSucc {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    SixVertexArrows.cyclicPred hN (finitePeriodicSucc hN i) = i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [finitePeriodicSucc_last]
    ext
    simp [SixVertexArrows.cyclicPred]
  · rw [finitePeriodicSucc_castSucc, svCyclicPred_succ]

theorem svPredTransferProduct_eq_matrixCycleWeight
    {N M : Nat} (hM : 0 < M) (c : Real)
    (vrows : Fin M → SixVertexRow N) :
    (∏ j : Fin M, sixVertexTransfer N c
        (vrows (SixVertexArrows.cyclicPred hM j)) (vrows j)) =
      matrixCycleWeight hM (sixVertexTransfer N c) vrows := by
  unfold matrixCycleWeight
  let e := svFinitePeriodicSuccEquiv hM
  have he := e.prod_comp (fun j : Fin M =>
    sixVertexTransfer N c
      (vrows (SixVertexArrows.cyclicPred hM j)) (vrows j))
  rw [show (fun i : Fin M =>
      sixVertexTransfer N c
        (vrows (SixVertexArrows.cyclicPred hM (e i))) (vrows (e i))) =
      (fun i : Fin M => sixVertexTransfer N c
        (vrows i) (vrows (finitePeriodicSucc hM i))) by
    funext i
    rw [svFinitePeriodicSuccEquiv_apply,
      svCyclicPred_finitePeriodicSucc]] at he
  exact he.symm

theorem svPeriodicRowsFixedSectorEquiv_weight
    (N M : Nat) (hM : 0 < M) (c : Real) (n : Fin (N + 1))
    (x : SixVertexPeriodicRowsInSector N M hM c n) :
    sixVertexPeriodicRowWeight hM c x.1 =
      matrixCycleWeight hM (sixVertexSectorTransfer N n c)
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n x) := by
  rw [sixVertexPeriodicRowWeight, matrixCycleWeight, matrixCycleWeight]
  apply Finset.prod_congr rfl
  intro i hi
  change sixVertexTransfer N c (x.1.1 i)
    (x.1.1 (finitePeriodicSucc hM i)) = _
  simp [sixVertexPeriodicRowsFixedSectorEquiv, sixVertexSectorTransfer]

theorem svPeriodicRowsInSector_sum_eq_trace
    (N M : Nat) (hM : 0 < M) (c : Real) (n : Fin (N + 1)) :
    (∑ x : SixVertexPeriodicRowsInSector N M hM c n,
      sixVertexPeriodicRowWeight hM c x.1) =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  calc
    (∑ x : SixVertexPeriodicRowsInSector N M hM c n,
      sixVertexPeriodicRowWeight hM c x.1) =
        ∑ y : MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c),
          matrixCycleWeight hM (sixVertexSectorTransfer N n c) y := by
      apply Fintype.sum_equiv
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n)
      exact svPeriodicRowsFixedSectorEquiv_weight N M hM c n
    _ = matrixCompatibleCycleSum hM (sixVertexSectorTransfer N n c) := rfl
    _ = Matrix.trace (sixVertexSectorTransfer N n c ^ M) :=
      matrixCompatibleCycleSum_eq_trace_pow hM _

theorem svTorusBalancedArrowPartitionSum_eq_sectorTrace
    (T : EvenTorus) (c : Real) :
    svTorusBalancedArrowPartitionSum T c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
  classical
  rw [svTorusBalancedArrowPartitionSum_eq_rowSum]
  simp_rw [svPredTransferProduct_eq_matrixCycleWeight T.height_pos c]
  let A := sixVertexTransfer T.width c
  let n : Fin (T.width + 1) := ⟨T.width / 2,
    Nat.lt_succ_of_le (Nat.div_le_self T.width 2)⟩
  let f : (Fin T.height → SixVertexRow T.width) → Real := fun vrows =>
    if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
      matrixCycleWeight T.height_pos A vrows
    else 0
  have hfiltered :
      (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) =
        ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
    calc
      (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) =
          ∑ vrows ∈ Finset.univ.filter (fun vrows =>
            ∀ i, A (vrows i) (vrows (finitePeriodicSucc T.height_pos i)) ≠ 0),
            f vrows := by
        symm
        apply Finset.sum_filter_of_ne
        intro vrows _ hf i
        have hprod : matrixCycleWeight T.height_pos A vrows ≠ 0 := by
          intro hzero
          apply hf
          unfold f
          rw [hzero]
          split_ifs <;> simp
        intro hzero
        apply hprod
        unfold matrixCycleWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
      _ = ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
        exact Finset.sum_subtype _ (by simp [A]) f
  change (∑ vrows : Fin T.height → SixVertexRow T.width, f vrows) = _
  rw [hfiltered]
  have hbalance (x : SixVertexPeriodicRows T.width T.height T.height_pos c) :
      sixVertexUpCount (x.1 (svFinLast T.height_pos)) = n.val ↔
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val := by
    rw [sixVertexPeriodicRows_upCount_eq T.height_pos c x
      (svFinLast T.height_pos)]
  have hsector :
      (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c, f x.1) =
        ∑ x : SixVertexPeriodicRowsInSector
          T.width T.height T.height_pos c n,
          sixVertexPeriodicRowWeight T.height_pos c x.1 := by
    unfold f
    simp_rw [hbalance]
    rw [show (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
        if sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val then
          matrixCycleWeight T.height_pos A x.1 else 0) =
        ∑ x ∈ Finset.univ.filter (fun x :
          SixVertexPeriodicRows T.width T.height T.height_pos c =>
            sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val),
          matrixCycleWeight T.height_pos A x.1 by
            rw [Finset.sum_filter]]
    rw [Finset.sum_subtype (p := fun x :
      SixVertexPeriodicRows T.width T.height T.height_pos c =>
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (Finset.univ.filter fun x :
        SixVertexPeriodicRows T.width T.height T.height_pos c =>
          sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (by simp)]
    rfl
  rw [hsector]
  exact svPeriodicRowsInSector_sum_eq_trace
    T.width T.height T.height_pos c n

set_option maxHeartbeats 800000 in

theorem sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow
    (T : EvenTorus) (c : Real) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c =
      svTorusBalancedArrowPartitionSum T c := by
  classical
  rw [sixVertexRectangleBalancedPartitionSum,
    svTorusBalancedArrowPartitionSum]
  calc
    (∑ xi : SixVertexToroidalBoundary T.width T.height,
      if xi.Balanced then
        sixVertexRectangleBoundaryPartitionSum T.width T.height c
          (sixVertexToroidalRectangleBoundary xi)
      else 0) =
        ∑ xi : SixVertexToroidalBoundary T.width T.height,
          ∑ omega : {omega : SixVertexRectangleArrows T.width T.height //
            sixVertexRectangleBoundary omega =
              sixVertexToroidalRectangleBoundary xi},
            if xi.Balanced then omega.1.weight c else 0 := by
      apply Finset.sum_congr rfl
      intro xi hxi
      by_cases hbal : xi.Balanced
      · simp only [if_pos hbal]
        exact sixVertexRectangleBoundaryPartitionSum_eq_fiberSum
          T.width T.height c (sixVertexToroidalRectangleBoundary xi)
      · simp [hbal]
    _ = ∑ xiomega : SixVertexCutRectangles T,
          if xiomega.1.Balanced then xiomega.2.1.weight c else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ omega : SixVertexArrows T,
          if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0 := by
      symm
      calc
        (∑ omega : SixVertexArrows T,
          if (sixVertexTorusSeam T omega).Balanced then omega.weight c else 0) =
            ∑ omega : SixVertexArrows T,
              (fun xiomega : SixVertexCutRectangles T =>
                if xiomega.1.Balanced then xiomega.2.1.weight c else 0)
                (sixVertexTorusCutEquiv T omega) := by
          apply Finset.sum_congr rfl
          intro omega homega
          change (if (sixVertexTorusSeam T omega).Balanced then
              omega.weight c else 0) =
            if (sixVertexTorusSeam T omega).Balanced then
              (sixVertexCutTorusArrows T omega).weight c else 0
          rw [sixVertexCutTorusArrows_weight]
        _ = ∑ xiomega : SixVertexCutRectangles T,
              if xiomega.1.Balanced then xiomega.2.1.weight c else 0 :=
          (sixVertexTorusCutEquiv T).sum_comp
            (fun xiomega : SixVertexCutRectangles T =>
              if xiomega.1.Balanced then xiomega.2.1.weight c else 0)

theorem sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace
    (T : EvenTorus) (c : Real) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2) c ^ T.height) := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_torusBalancedArrow]
  exact svTorusBalancedArrowPartitionSum_eq_sectorTrace T c

end StatMech.FrontierD
