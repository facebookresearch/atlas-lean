/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt.PollakPartialParking



/-- On the circle `ZMod (t+1)`, the clockwise ray from `a` always hits a spot
outside `occ` when `occ` is not full. -/
private theorem ray_free_exists (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : ∃ j : ℕ, a + ((j : ℕ) : ZMod (t + 1)) ∉ occ := by
  have hinj : Function.Injective
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1))) := by
    intro j1 j2 h12
    have hcast : (((j1.val : ℕ)) : ZMod (t + 1)) = (((j2.val : ℕ)) : ZMod (t + 1)) :=
      add_left_cancel h12
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    have heq := hcast.eq_of_lt_of_lt j1.isLt j2.isLt
    exact Fin.ext heq
  have hcard : (Finset.univ.image
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1)))).card = t + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnot : ¬ (Finset.univ.image
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1)))) ⊆ occ := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnot
  obtain ⟨x, hximg, hxnocc⟩ := hnot
  rw [Finset.mem_image] at hximg
  obtain ⟨j, _, rfl⟩ := hximg
  exact ⟨j.val, hxnocc⟩

/-- First free spot clockwise from `a`: deterministic choice. -/
private noncomputable def firstFree (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : ZMod (t + 1) :=
  a + ((((Nat.find (ray_free_exists t occ a h)) : ℕ)) : ZMod (t + 1))

private theorem firstFree_not_mem (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : firstFree t occ a h ∉ occ :=
  Nat.find_spec (ray_free_exists t occ a h)

private theorem firstFree_is_ray (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) :
    ∃ j : ℕ, firstFree t occ a h = a + (((j : ℕ)) : ZMod (t + 1)) :=
  ⟨_, rfl⟩

private theorem firstFree_min (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) (j : ℕ)
    (hj : j < Nat.find (ray_free_exists t occ a h)) :
    a + (((j : ℕ)) : ZMod (t + 1)) ∈ occ := by
  by_contra hcon
  have hle := Nat.find_min' (ray_free_exists t occ a h) hcon
  omega

/-- Occupied spots after the first `n` cars park on the circle. Carries the
cardinality invariant. -/
private noncomputable def parkOccAux (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (n : ℕ) → { occ : Finset (ZMod (t + 1)) // occ.card ≤ n }
  | 0 => ⟨∅, by simp⟩
  | n + 1 =>
    if h : n < s then
      let occ := parkOccAux s t g hst n
      have hle : occ.val.card ≤ n := occ.property
      have hc : occ.val.card < t + 1 := by omega
      ⟨insert (firstFree t occ.val (g ⟨n, h⟩) hc) occ.val,
        by
          have hci :=
            Finset.card_insert_le (firstFree t occ.val (g ⟨n, h⟩) hc) occ.val
          omega⟩
    else
      ⟨(parkOccAux s t g hst n).val,
        le_trans (parkOccAux s t g hst n).property (Nat.le_succ n)⟩

/-- Occupied spots after the first `n` cars park on the circle. -/
private noncomputable def parkOcc (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : Finset (ZMod (t + 1)) :=
  (parkOccAux s t g hst n).val

private theorem card_parkOcc_le (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : (parkOcc s t g hst n).card ≤ n :=
  (parkOccAux s t g hst n).property

/-- Spot taken by car `n`. -/
private noncomputable def parkAssign (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) : ZMod (t + 1) :=
  firstFree t (parkOcc s t g hst n) (g ⟨n, h⟩)
    (lt_of_le_of_lt (card_parkOcc_le s t g hst n) (by omega))

private theorem parkOcc_succ_of_lt (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) :
    parkOcc s t g hst (n + 1) =
      insert (parkAssign s t g hst n h) (parkOcc s t g hst n) := by
  simp only [parkOcc, parkOccAux]
  split_ifs
  rfl

private theorem parkOcc_succ_of_ge (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : ¬ n < s) :
    parkOcc s t g hst (n + 1) = parkOcc s t g hst n := by
  simp only [parkOcc, parkOccAux]
  split_ifs
  rfl

private theorem parkOcc_subset_succ (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) : parkOcc s t g hst n ⊆ parkOcc s t g hst (n + 1) := by
  by_cases h : n < s
  · rw [parkOcc_succ_of_lt s t g hst n h]
    exact Finset.subset_insert _ _
  · rw [parkOcc_succ_of_ge s t g hst n h]

private theorem parkOcc_mono (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    Monotone (parkOcc s t g hst) :=
  monotone_nat_of_le_succ (parkOcc_subset_succ s t g hst)

private theorem parkAssign_mem (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (n : ℕ) (h : n < s) :
    parkAssign s t g hst n h ∈ parkOcc s t g hst (n + 1) := by
  rw [parkOcc_succ_of_lt s t g hst n h]
  exact Finset.mem_insert_self _ _

private theorem parkAssign_mem_of_le (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (a b : ℕ) (ha : a < s) (hab : a + 1 ≤ b) :
    parkAssign s t g hst a ha ∈ parkOcc s t g hst b :=
  parkOcc_mono s t g hst hab (parkAssign_mem s t g hst a ha)

private theorem parkAssign_inj (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (a b : ℕ) (ha : a < s) (hb : b < s) (hne : a ≠ b) :
    parkAssign s t g hst a ha ≠ parkAssign s t g hst b hb := by
  rcases lt_trichotomy a b with hab | hab | hab
  · intro heq
    have hmem : parkAssign s t g hst b hb ∈ parkOcc s t g hst b := by
      rw [← heq]
      exact parkAssign_mem_of_le s t g hst a b ha (by omega)
    exact firstFree_not_mem t (parkOcc s t g hst b) (g ⟨b, hb⟩) _ hmem
  · exact absurd hab hne
  · intro heq
    have hmem : parkAssign s t g hst a ha ∈ parkOcc s t g hst a := by
      rw [heq]
      exact parkAssign_mem_of_le s t g hst b a hb (by omega)
    exact firstFree_not_mem t (parkOcc s t g hst a) (g ⟨a, ha⟩) _ hmem

private theorem card_parkOcc_self (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (parkOcc s t g hst s).card = s := by
  apply le_antisymm (card_parkOcc_le s t g hst s)
  have hinj : Function.Injective
      (fun k : Fin s => parkAssign s t g hst k.val k.isLt) := by
    intro k1 k2 h12
    simp only at h12
    by_cases hne : k1.val ≠ k2.val
    · exact absurd h12 (parkAssign_inj s t g hst k1.val k2.val k1.isLt k2.isLt hne)
    · exact Fin.ext (not_not.mp hne)
  have hsub : Finset.univ.image (fun k : Fin s => parkAssign s t g hst k.val k.isLt)
      ⊆ parkOcc s t g hst s := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact parkAssign_mem_of_le s t g hst k.val s k.isLt (by omega)
  have hle := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin] at hle

/-- Empty spots after circular parking. -/
private noncomputable def parkEmpty (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    Finset (ZMod (t + 1)) :=
  Finset.univ \ parkOcc s t g hst s

private theorem card_parkEmpty (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (parkEmpty s t g hst).card = t + 1 - s := by
  unfold parkEmpty
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card,
    card_parkOcc_self s t g hst]

private theorem firstFree_translate (t : ℕ) (occ : Finset (ZMod (t + 1)))
    (a c : ZMod (t + 1)) (h : occ.card < t + 1)
    (h' : (Finset.image (fun x => x + c) occ).card < t + 1) :
    firstFree t (Finset.image (fun x => x + c) occ) (a + c) h' =
      firstFree t occ a h + c := by
  have hPQ : ∀ j : ℕ,
      ((a + c) + (((j : ℕ)) : ZMod (t + 1))
        ∉ Finset.image (fun x => x + c) occ) ↔
      (a + (((j : ℕ)) : ZMod (t + 1)) ∉ occ) := by
    intro j
    have hshift : (a + c) + (((j : ℕ)) : ZMod (t + 1))
        = (a + (((j : ℕ)) : ZMod (t + 1))) + c := by ring
    rw [hshift]
    constructor
    · intro hcon hmem
      apply hcon
      rw [Finset.mem_image]
      exact ⟨_, hmem, rfl⟩
    · intro hcon hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨x, hxmem, hxeq⟩ := hmem
      apply hcon
      have hx : x = a + (((j : ℕ)) : ZMod (t + 1)) := add_right_cancel hxeq
      rwa [hx] at hxmem
  have HP := ray_free_exists t occ a h
  have HQ := ray_free_exists t (Finset.image (fun x => x + c) occ) (a + c) h'
  have h1 : Nat.find HP ≤ Nat.find HQ :=
    Nat.find_min' HP ((hPQ _).mp (Nat.find_spec HQ))
  have h2 : Nat.find HQ ≤ Nat.find HP :=
    Nat.find_min' HQ ((hPQ _).mpr (Nat.find_spec HP))
  have hfind : Nat.find HP = Nat.find HQ := le_antisymm h1 h2
  unfold firstFree
  rw [hfind]
  ring

private theorem parkOcc_translate (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (c : ZMod (t + 1)) (n : ℕ) :
    parkOcc s t (fun i => g i + c) hst n =
      Finset.image (fun x => x + c) (parkOcc s t g hst n) := by
  induction n with
  | zero =>
    simp only [parkOcc, parkOccAux, Finset.image_empty]
  | succ n ih =>
    by_cases h : n < s
    · have hassign : parkAssign s t (fun i => g i + c) hst n h =
          parkAssign s t g hst n h + c := by
        unfold parkAssign
        simp only [ih]
        exact firstFree_translate t (parkOcc s t g hst n) (g ⟨n, h⟩) c _ _
      rw [parkOcc_succ_of_lt s t (fun i => g i + c) hst n h,
        parkOcc_succ_of_lt s t g hst n h, Finset.image_insert, ih, hassign]
    · rw [parkOcc_succ_of_ge s t (fun i => g i + c) hst n h,
        parkOcc_succ_of_ge s t g hst n h, ih]

private theorem parkEmpty_translate (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (c : ZMod (t + 1)) :
    parkEmpty s t (fun i => g i + c) hst =
      Finset.image (fun x => x + c) (parkEmpty s t g hst) := by
  have hinj : Function.Injective (fun x : ZMod (t + 1) => x + c) :=
    fun a b hab => add_right_cancel hab
  have hsurj : Function.Surjective (fun x : ZMod (t + 1) => x + c) :=
    fun y => ⟨y - c, by ring⟩
  unfold parkEmpty
  rw [parkOcc_translate s t g hst c s]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hsurj x
    subst hy
    rw [Finset.mem_image]
    refine ⟨y, ?_, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hyocc
    exact hx (Finset.mem_image_of_mem _ hyocc)
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hyocc, hyeq⟩ := hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hyocc
    intro hximg
    rw [Finset.mem_image] at hximg
    obtain ⟨z, hzocc, hzeq⟩ := hximg
    have hyz : y = z := hinj (hyeq.trans hzeq.symm)
    rw [← hyz] at hzocc
    exact hyocc hzocc




/-- First free spot at or after `a` in the linear lot, if any. -/
private noncomputable def linFirstFree (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) :
    Option (Fin t) :=
  if h : (Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).Nonempty then
    some ((Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h)
  else none

private theorem linFirstFree_mem (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) (x : Fin t)
    (hx : linFirstFree t occ a = some x) : a ≤ x.val ∧ x ∉ occ := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case pos =>
    have hxeq : (Finset.univ.filter
          (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h = x :=
          Option.some_inj.mp hx
    have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    rw [← hxeq]
    exact hmem.2

private theorem linFirstFree_le (t : ℕ) (occ : Finset (Fin t)) (a : ℕ) (x : Fin t)
    (hx : linFirstFree t occ a = some x) (y : Fin t)
    (hy1 : a ≤ y.val) (hy2 : y ∉ occ) : x.val ≤ y.val := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case pos =>
    have hxeq : (Finset.univ.filter
          (fun k : Fin t => a ≤ k.val ∧ k ∉ occ)).min' h = x :=
          Option.some_inj.mp hx
    subst hxeq
    have hmem : y ∈ Finset.univ.filter (fun k : Fin t => a ≤ k.val ∧ k ∉ occ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy1, hy2⟩
    have hle := Finset.min'_le _ y hmem
    exact Fin.le_def.mp hle

private theorem linFirstFree_none (t : ℕ) (occ : Finset (Fin t)) (a : ℕ)
    (hx : linFirstFree t occ a = none) (y : Fin t) (hy1 : a ≤ y.val) :
    y ∈ occ := by
  unfold linFirstFree at hx
  split_ifs at hx with h
  case neg =>
    by_contra hycon
    apply h
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy1, hycon⟩⟩

/-- Occupied spots after the first `n` cars park in the linear lot, if all
succeeded. Carries the cardinality invariant; `none` on failure. -/
private noncomputable def linOccAux (s t : ℕ) (f : Fin s → Fin t) :
    (n : ℕ) → Option { occ : Finset (Fin t) // occ.card ≤ n }
  | 0 => some ⟨∅, by simp⟩
  | n + 1 =>
    match linOccAux s t f n with
    | none => none
    | some occ =>
      if h : n < s then
        match linFirstFree t occ.val (f ⟨n, h⟩).val with
        | some x =>
          some ⟨insert x occ.val, by
            have hle : occ.val.card ≤ n := occ.property
            have hci := Finset.card_insert_le x occ.val
            omega⟩
        | none => none
      else some ⟨occ.val, le_trans occ.property (Nat.le_succ n)⟩

/-- Successful parking of all cars. -/
private def LinSuccess (s t : ℕ) (f : Fin s → Fin t) : Prop :=
  (linOccAux s t f s).isSome

private theorem linOccAux_zero (s t : ℕ) (f : Fin s → Fin t) :
    linOccAux s t f 0 = some ⟨∅, by simp⟩ := rfl

private theorem linOccAux_succ_some (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) (h : n < s) (x : Fin t)
    (hff : linFirstFree t occ.val (f ⟨n, h⟩).val = some x) :
    linOccAux s t f (n + 1) = some ⟨insert x occ.val, by
      have _hle : occ.val.card ≤ n := occ.property
      have hci := Finset.card_insert_le x occ.val
      omega⟩ := by
  simp only [linOccAux, hm, h, hff, dite_true]

private theorem linOccAux_succ_none_take (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) (h : n < s)
    (hff : linFirstFree t occ.val (f ⟨n, h⟩).val = none) :
    linOccAux s t f (n + 1) = none := by
  simp only [linOccAux, hm, h, hff, dite_true]

private theorem linOccAux_succ_failed (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (hm : linOccAux s t f n = none) :
    linOccAux s t f (n + 1) = none := by
  simp only [linOccAux, hm]

private theorem linOccAux_succ_ge (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) (h : ¬ n < s) :
    linOccAux s t f (n + 1) = some ⟨occ.val, le_trans occ.property (Nat.le_succ n)⟩ := by
  simp only [linOccAux, hm, h, dite_false]

/-- Spot taken by car `n`, if the process got that far and found one. -/
private noncomputable def linTake (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (h : n < s) :
    Option (Fin t) :=
  match linOccAux s t f n with
  | none => none
  | some occ => linFirstFree t occ.val (f ⟨n, h⟩).val

private theorem linTake_eq (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (h : n < s)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) :
    linTake s t f n h = linFirstFree t occ.val (f ⟨n, h⟩).val := by
  unfold linTake
  rw [hm]

/-- Success propagates backward: if step `n+1` succeeded, so did `n`. -/
private theorem linOccAux_some_of_succ (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (h : (linOccAux s t f (n + 1)).isSome) : (linOccAux s t f n).isSome := by
  match hm : linOccAux s t f n with
  | none =>
    rw [linOccAux_succ_failed s t f n hm] at h
    simp at h
  | some _ => exact Option.isSome_some

private theorem linOccAux_none_of_le (s t : ℕ) (f : Fin s → Fin t) (m k : ℕ)
    (hle : m ≤ k) (hm : linOccAux s t f m = none) :
    linOccAux s t f k = none :=
  Nat.le_induction (P := fun n _ => linOccAux s t f n = none) hm
    (fun n _ ih => linOccAux_succ_failed s t f n ih) k hle

private theorem linOccAux_some_of_le (s t : ℕ) (f : Fin s → Fin t) (m : ℕ)
    (hle : m ≤ s) (hsucc : LinSuccess s t f) : (linOccAux s t f m).isSome := by
  unfold LinSuccess at hsucc
  match hm : linOccAux s t f m with
  | none =>
    rw [linOccAux_none_of_le s t f m s hle hm] at hsucc
    simp at hsucc
  | some _ => exact Option.isSome_some

private theorem linOccAux_eq_some_of_isSome (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (h : (linOccAux s t f n).isSome) :
    ∃ occ, linOccAux s t f n = some occ :=
  Option.isSome_iff_exists.mp h

private theorem linOcc_val_subset_step (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (hns : n < s)
    (oa : { occ : Finset (Fin t) // occ.card ≤ n })
    (oa' : { occ : Finset (Fin t) // occ.card ≤ n + 1 })
    (ha : linOccAux s t f n = some oa)
    (ha' : linOccAux s t f (n + 1) = some oa') :
    oa.val ⊆ oa'.val := by
  match hff : linFirstFree t oa.val (f ⟨n, hns⟩).val with
  | none =>
    rw [linOccAux_succ_none_take s t f n oa ha hns hff] at ha'
    simp at ha'
  | some x =>
    rw [linOccAux_succ_some s t f n oa ha hns x hff] at ha'
    have heq : oa'.val = insert x oa.val :=
      (congrArg Subtype.val (Option.some_inj.mp ha')).symm
    rw [heq]
    exact Finset.subset_insert x oa.val

private theorem linOcc_val_subset (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (hab : a ≤ b) (hbs : b ≤ s) (_hsucc : LinSuccess s t f)
    (oa : { occ : Finset (Fin t) // occ.card ≤ a })
    (ob : { occ : Finset (Fin t) // occ.card ≤ b })
    (ha : linOccAux s t f a = some oa) (hb : linOccAux s t f b = some ob) :
    oa.val ⊆ ob.val := by
  have key : ∀ n (hmn : a ≤ n), n ≤ b →
      ∀ (on : { occ : Finset (Fin t) // occ.card ≤ n }),
        linOccAux s t f n = some on → oa.val ⊆ on.val := by
    intro n
    exact Nat.le_induction
      (P := fun n _ => n ≤ b →
        ∀ (on : { occ : Finset (Fin t) // occ.card ≤ n }),
          linOccAux s t f n = some on → oa.val ⊆ on.val)
      (fun hnb on hon => by
        have heq : oa = on := Option.some_inj.mp (ha.symm.trans hon)
        rw [heq])
      (fun n hmn ih hnb on' hon' => by
        have hns : n < s := by omega
        have hs1 : (linOccAux s t f (n + 1)).isSome := hon'.symm ▸ Option.isSome_some
        have hs0 := linOccAux_some_of_succ s t f n hs1
        obtain ⟨on, hon⟩ := linOccAux_eq_some_of_isSome s t f n hs0
        exact Finset.Subset.trans (ih (by omega) on hon)
          (linOcc_val_subset_step s t f n hns on on' hon hon'))
      n
  exact key b hab (le_refl b) ob hb

private theorem linTake_some_of_success (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : ℕ) (hj : j < s) :
    ∃ x, linTake s t f j hj = some x := by
  have h1 := linOccAux_some_of_le s t f (j + 1) (by omega) hsucc
  have h0 := linOccAux_some_of_le s t f j (by omega) hsucc
  obtain ⟨occ, hocc⟩ := linOccAux_eq_some_of_isSome s t f j h0
  match hffm : linFirstFree t occ.val (f ⟨j, hj⟩).val with
  | none =>
    obtain ⟨occ', hocc'⟩ := linOccAux_eq_some_of_isSome s t f (j + 1) h1
    rw [linOccAux_succ_none_take s t f j occ hocc hj hffm] at hocc'
    simp at hocc'
  | some x => exact ⟨x, by rw [linTake_eq s t f j hj occ hocc, hffm]⟩

/-- The parking assignment extracted from a successful run. -/
private noncomputable def linAssign (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) : Fin s → Fin t :=
  fun j => (linTake_some_of_success s t f hsucc j.val j.isLt).choose

private theorem linAssign_spec (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : Fin s) :
    linTake s t f j.val j.isLt = some (linAssign s t f hsucc j) :=
  (linTake_some_of_success s t f hsucc j.val j.isLt).choose_spec

private theorem linAssign_ge (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : Fin s) : f j ≤ linAssign s t f hsucc j := by
  have htake := linAssign_spec s t f hsucc j
  have h0 := linOccAux_some_of_le s t f j.val (by omega) hsucc
  obtain ⟨occ, hocc⟩ := linOccAux_eq_some_of_isSome s t f j.val h0
  rw [linTake_eq s t f j.val j.isLt occ hocc] at htake
  have hmem := linFirstFree_mem t occ.val (f ⟨j.val, j.isLt⟩).val _ htake
  exact Fin.le_def.mpr hmem.1

private theorem linAssign_ne_of_lt (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (i j : Fin s) (hlt : i.val < j.val)
    (heq : linAssign s t f hsucc i = linAssign s t f hsucc j) : False := by
  have hi := linAssign_spec s t f hsucc i
  have hj := linAssign_spec s t f hsucc j
  rw [heq] at hi
  have h0i := linOccAux_some_of_le s t f i.val (by omega) hsucc
  obtain ⟨occi, hocci⟩ := linOccAux_eq_some_of_isSome s t f i.val h0i
  rw [linTake_eq s t f i.val i.isLt occi hocci] at hi
  have h1i := linOccAux_some_of_le s t f (i.val + 1) (by omega) hsucc
  obtain ⟨occi', hocci'⟩ := linOccAux_eq_some_of_isSome s t f (i.val + 1) h1i
  have hstep := linOccAux_succ_some s t f i.val occi hocci i.isLt _ hi
  have heq2 : occi'.val = insert (linAssign s t f hsucc j) occi.val := by
    have hcomb := hstep.symm.trans hocci'
    have hsub := Option.some_inj.mp hcomb
    exact (congrArg Subtype.val hsub).symm
  have hmem1 : linAssign s t f hsucc j ∈ occi'.val := by
    rw [heq2]
    exact Finset.mem_insert_self _ _
  have h0j := linOccAux_some_of_le s t f j.val (by omega) hsucc
  obtain ⟨occj, hoccj⟩ := linOccAux_eq_some_of_isSome s t f j.val h0j
  have hsub := linOcc_val_subset s t f (i.val + 1) j.val (by omega) (by omega)
    hsucc occi' occj hocci' hoccj
  have hmem2 : linAssign s t f hsucc j ∈ occj.val := hsub hmem1
  rw [linTake_eq s t f j.val j.isLt occj hoccj] at hj
  have hnot := linFirstFree_mem t occj.val (f ⟨j.val, j.isLt⟩).val _ hj
  exact hnot.2 hmem2

private theorem linAssign_injective (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) :
    Function.Injective (linAssign s t f hsucc) := by
  intro i j heq
  by_contra hne
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact linAssign_ne_of_lt s t f hsucc i j h heq
  · exact hne (Fin.ext h)
  · exact linAssign_ne_of_lt s t f hsucc j i h heq.symm

private theorem linUpperSpots_card (t : ℕ) (k : Fin t) :
    (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)).card = t - k.val := by
  have h1 : Finset.image Fin.val
      (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)) = Finset.Ico k.val t := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨x, hkx, rfl⟩
      exact ⟨hkx, x.isLt⟩
    · rintro ⟨hky, hyt⟩
      exact ⟨⟨y, hyt⟩, hky, rfl⟩
  have h2 : (Finset.image Fin.val
      (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val))).card
      = (Finset.univ.filter (fun x : Fin t => k.val ≤ x.val)).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [h1, Nat.card_Ico] at h2
  omega

private theorem linSuccess_imp_threshold (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) :
    IsPartialParkingFunction s t f := by
  intro k
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i : Fin s => k ≤ f i),
      linAssign s t f hsucc i ∈
        Finset.univ.filter (fun x : Fin t => k.val ≤ x.val) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hge := linAssign_ge s t f hsucc i
    have hle : k ≤ linAssign s t f hsucc i := hi.trans hge
    exact Fin.le_def.mp hle
  have hinj : Set.InjOn (linAssign s t f hsucc)
      ↑(Finset.univ.filter (fun i : Fin s => k ≤ f i)) :=
    (linAssign_injective s t f hsucc).injOn
  have hle := Finset.card_le_card_of_injOn
    (linAssign s t f hsucc)
    (fun i hi => hmaps i hi)
    hinj
  rw [linUpperSpots_card t k] at hle
  exact hle


/-- Backward success on a partial path. -/
private theorem linOccAux_isSome_of_le (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (hb : (linOccAux s t f b).isSome) (hab : a ≤ b) :
    (linOccAux s t f a).isSome := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero =>
    simpa using hb
  | succ k ih =>
    have hbk : a + (k + 1) = (a + k) + 1 := by omega
    have h1 : (linOccAux s t f (a + k)).isSome :=
      linOccAux_some_of_succ s t f (a + k) (hbk ▸ hb)
    exact ih h1

/-- A car parked at or after `c` prefers at or after `c`, provided a free
spot strictly below `c` witnesses minimality. -/
private theorem linTake_pref_ge (s t : ℕ) (f : Fin s → Fin t) (j : ℕ) (hj : j < s)
    (x : Fin t) (hx : linTake s t f j hj = some x)
    (occ : { occ : Finset (Fin t) // occ.card ≤ j })
    (hm : linOccAux s t f j = some occ)
    (c : ℕ) (hc : c ≤ x.val) (z : Fin t) (hz : z.val + 1 = c)
    (hzfree : z ∉ occ.val) :
    c ≤ (f ⟨j, hj⟩).val := by
  rw [linTake_eq s t f j hj occ hm] at hx
  by_contra hcon
  have hcon' : (f ⟨j, hj⟩).val < c := by omega
  have h1 : (f ⟨j, hj⟩).val ≤ z.val := by omega
  have hle := linFirstFree_le t occ.val (f ⟨j, hj⟩).val x hx z h1 hzfree
  omega

/-- Partial-path monotonicity with an explicit upper bound. -/
private theorem linOcc_val_subset_of_some (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (oa : { occ : Finset (Fin t) // occ.card ≤ a })
    (ob : { occ : Finset (Fin t) // occ.card ≤ b })
    (ha : linOccAux s t f a = some oa) (hb : linOccAux s t f b = some ob)
    (hab : a ≤ b) (hbs : b ≤ s) : oa.val ⊆ ob.val := by
  exact Nat.le_induction
    (P := fun m _ => m ≤ b →
      ∀ om : { occ : Finset (Fin t) // occ.card ≤ m },
        linOccAux s t f m = some om → oa.val ⊆ om.val)
    (fun _ om hom => by
      have e := Option.some_inj.mp (ha.symm.trans hom)
      subst e
      exact Finset.Subset.rfl)
    (fun m _ ih hmb om' hom' => by
      have hms : m < s := by omega
      have hprev : (linOccAux s t f m).isSome :=
        linOccAux_some_of_succ s t f m (hom'.symm ▸ Option.isSome_some)
      obtain ⟨om0, hom0⟩ := Option.isSome_iff_exists.mp hprev
      exact Finset.Subset.trans (ih (by omega) om0 hom0)
        (linOcc_val_subset_step s t f m hms om0 om' hom0 hom'))
    b hab (le_refl b) ob hb

/-- The occupied set is the image of the chosen takes. -/
private theorem linOcc_image (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (hn : n < s)
    (car : ∀ j : ℕ, j < n → Fin t)
    (hcar : ∀ j (hj : j < n),
      linTake s t f j (Nat.lt_trans hj hn) = some (car j hj))
    (_tpos : 0 < t) (F : Fin s → Fin t)
    (hF : ∀ i : Fin s, ∀ h : i.val < n, F i = car i.val h) :
    ∀ m : ℕ, ∀ _hmn : m ≤ n, ∀ om : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some om →
      om.val = (Finset.univ.filter (fun i : Fin s => i.val < m)).image F := by
  intro m
  induction m with
  | zero =>
    intro hmn om hom
    have hempty : Finset.univ.filter (fun i : Fin s => i.val < 0) = ∅ :=
      Finset.eq_empty_of_forall_notMem (by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        omega)
    have h0 : linOccAux s t f 0 =
        some (⟨∅, by simp⟩ : { occ : Finset (Fin t) // occ.card ≤ 0 }) := rfl
    have hom0 : (⟨∅, by simp⟩ : { occ : Finset (Fin t) // occ.card ≤ 0 }) = om :=
      Option.some_inj.mp (h0.symm.trans hom)
    have hval : om.val = ∅ := (congrArg Subtype.val hom0).symm
    rw [hempty, Finset.image_empty, hval]
  | succ m ih =>
    intro hmn om hom
    have hms : m < s := lt_of_le_of_lt (by omega) hn
    have hmltn : m < n := by omega
    have hprev := linOccAux_isSome_of_le s t f m (m + 1)
      (hom.symm ▸ Option.isSome_some) (Nat.le_succ m)
    obtain ⟨oprev, hprev'⟩ := Option.isSome_iff_exists.mp hprev
    have ih' := ih (by omega) oprev hprev'
    have htake : linFirstFree t oprev.val (f ⟨m, hms⟩).val = some (car m hmltn) := by
      have h1 := hcar m hmltn
      rw [linTake_eq s t f m _ oprev hprev'] at h1
      exact h1
    have hsucc := linOccAux_succ_some s t f m oprev hprev' hms (car m hmltn) htake
    have hval_eq : om.val = (⟨insert (car m hmltn) oprev.val, by
        have hle := oprev.property
        have hci := Finset.card_insert_le (car m hmltn) oprev.val
        omega⟩ : { occ : Finset (Fin t) // occ.card ≤ m + 1 }).val :=
      congrArg Subtype.val (Option.some_inj.mp (hom.symm.trans hsucc))
    have hfilter : Finset.univ.filter (fun i : Fin s => i.val < m + 1) =
        insert ⟨m, hms⟩ (Finset.univ.filter (fun i : Fin s => i.val < m)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        by_cases h : i.val < m
        · exact Or.inr h
        · left
          have hiv : i.val = m := by omega
          exact Fin.ext hiv
      · rintro (rfl | h)
        · change m < m + 1
          exact Nat.lt_succ_self m
        · omega
    rw [hval_eq]
    change insert (car m hmltn) oprev.val =
      (Finset.univ.filter (fun i : Fin s => i.val < m + 1)).image F
    rw [hfilter, Finset.image_insert, ← ih', hF ⟨m, hms⟩ hmltn]

/-- Threshold implies greedy success, via the cluster argument. -/
private theorem threshold_imp_linSuccess (s t : ℕ) (f : Fin s → Fin t)
    (h : IsPartialParkingFunction s t f) (_hst : s ≤ t) :
    LinSuccess s t f := by
  by_contra hfail
  have hnone : linOccAux s t f s = none :=
    Option.not_isSome_iff_eq_none.mp hfail
  -- First failure triple.
  have triple : ∃ n : ℕ, ∃ _ : n < s, ∃ occ : { occ : Finset (Fin t) // occ.card ≤ n },
      linOccAux s t f n = some occ ∧
        linFirstFree t occ.val (f ⟨n, ‹n < s›⟩).val = none := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hall : ∀ m : ℕ, m ≤ s → (linOccAux s t f m).isSome := by
      intro m hm
      induction m with
      | zero =>
        rw [linOccAux_zero]
        exact Option.isSome_some
      | succ m ih =>
        have hms : m ≤ s := by omega
        have ih' := ih hms
        obtain ⟨occ, hocc⟩ := Option.isSome_iff_exists.mp ih'
        have hms' : m < s := by omega
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp (hcon m hms' occ hocc)
        rw [linOccAux_succ_some s t f m occ hocc hms' x hx.symm]
        exact Option.isSome_some
    have hs := hall s (le_refl s)
    rw [hnone] at hs
    simp at hs
  obtain ⟨n, hn, occ, hm, hff⟩ := triple
  -- Every spot at or after the failed preference is occupied.
  have allocc : ∀ y : Fin t, (f ⟨n, hn⟩).val ≤ y.val → y ∈ occ.val :=
    fun y hy => linFirstFree_none t occ.val _ hff y hy
  -- The cluster base: least `c` with `[c, t)` fully occupied.
  have hex : ∃ c : ℕ, ∀ y : Fin t, c ≤ y.val → y ∈ occ.val := by
    refine ⟨t, fun y hy => absurd hy (by have := y.isLt; omega)⟩
  have : DecidablePred (fun c : ℕ => ∀ y : Fin t, c ≤ y.val → y ∈ occ.val) :=
    fun c => inferInstance
  set cstar := Nat.find hex with hcstar
  have hPstar : ∀ y : Fin t, cstar ≤ y.val → y ∈ occ.val :=
    Nat.find_spec hex
  have hlea : cstar ≤ (f ⟨n, hn⟩).val :=
    Nat.find_min' hex allocc
  have hlt : cstar < t :=
    lt_of_le_of_lt hlea (f ⟨n, hn⟩).isLt
  -- A free spot at `cstar - 1` (unless `cstar = 0`).
  have hfree : cstar = 0 ∨ ∃ z : Fin t, z.val + 1 = cstar ∧ z ∉ occ.val := by
    by_cases hc0 : cstar = 0
    · exact Or.inl hc0
    · right
      have hpos : 0 < cstar := Nat.pos_of_ne_zero hc0
      have hmin := Nat.find_min hex (show cstar - 1 < cstar by omega)
      rw [not_forall] at hmin
      obtain ⟨y, hy⟩ := hmin
      obtain ⟨hle_y, hfree_y⟩ := not_imp.mp hy
      have hylt : y.val < cstar :=
        lt_of_not_ge (fun hcon => hfree_y (hPstar y hcon))
      have hyeq : y.val + 1 = cstar := by omega
      exact ⟨y, hyeq, hfree_y⟩
  -- Takes succeed for every earlier car.
  have take_some : ∀ j : ℕ, ∀ hj : j < n, ∃ x : Fin t,
      linTake s t f j (Nat.lt_trans hj hn) = some x := by
    intro j hj
    have hjn : j < s := Nat.lt_trans hj hn
    have hjs := linOccAux_isSome_of_le s t f j n (hm.symm ▸ Option.isSome_some)
      (Nat.le_of_lt hj)
    obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.mp hjs
    match hffj : linFirstFree t oj.val (f ⟨j, hjn⟩).val with
    | none =>
      exfalso
      have hsucc := linOccAux_succ_none_take s t f j oj hoj hjn hffj
      have hnone2 := linOccAux_none_of_le s t f (j + 1) n (by omega) hsucc
      rw [hm] at hnone2
      simp at hnone2
    | some x =>
      exact ⟨x, by
        have hbase : linTake s t f j (Nat.lt_trans hj hn) =
            linFirstFree t oj.val (f ⟨j, hjn⟩).val := by
          unfold linTake
          rw [hoj]
        rw [hbase, hffj]⟩
  -- The chosen car for each earlier index.
  choose car hcar using take_some
  have tpos : 0 < t := by omega
  set carAll : Fin s → Fin t :=
    fun i => if h : i.val < n then car i.val h else (⟨0, tpos⟩ : Fin t) with hcarAlldef
  have hcarAll : ∀ i : Fin s, ∀ h : i.val < n, carAll i = car i.val h :=
    fun i h => dite_eq_left h
  have htakeAll : ∀ i : Fin s, ∀ h : i.val < n,
      linTake s t f i.val (Nat.lt_trans h hn) = some (carAll i) := by
    intro i h
    rw [hcarAll i h]
    exact hcar i.val h
  have himg : occ.val = (Finset.univ.filter (fun i : Fin s => i.val < n)).image carAll :=
    linOcc_image s t f n hn car hcar tpos carAll hcarAll n (le_refl n) occ hm
  -- The cluster threshold and its spots.
  set k : Fin t := ⟨cstar, hlt⟩ with hkdef
  have hkval : k.val = cstar := rfl
  have hth := h k
  rw [hkval] at hth
  set Spots : Finset (Fin t) :=
    Finset.univ.filter (fun y : Fin t => cstar ≤ y.val) with hSpotsdef
  have hspots : Spots.card = t - cstar := linUpperSpots_card t ⟨cstar, hlt⟩
  -- Every cluster spot is taken by an earlier car preferring at/after `cstar`.
  have ycar : ∀ y : Fin t, y ∈ Spots → ∃ i : Fin s,
      i.val < n ∧ carAll i = y ∧ k ≤ f i := by
    intro y hy
    simp only [hSpotsdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hyocc : y ∈ occ.val := hPstar y hy
    rw [himg] at hyocc
    rw [Finset.mem_image] at hyocc
    obtain ⟨i, hi_mem, hi_eq⟩ := hyocc
    have himem' : i.val < n := (Finset.mem_filter.mp hi_mem).2
    have htake : linTake s t f i.val (Nat.lt_trans himem' hn) = some y := by
      have h1 := htakeAll i himem'
      rwa [hi_eq] at h1
    have hOj := linOccAux_isSome_of_le s t f i.val n
      (hm.symm ▸ Option.isSome_some) (Nat.le_of_lt himem')
    obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.mp hOj
    have hsuboj := linOcc_val_subset_of_some s t f i.val n oj occ hoj hm
      (Nat.le_of_lt himem') (Nat.le_of_lt hn)
    have hpref : k ≤ f i := by
      rcases hfree with hc0 | ⟨z, hz, hzfree⟩
      · have hk0 : k.val = 0 := hc0
        have h0 : (0 : ℕ) ≤ (f i).val := Nat.zero_le _
        rw [← hk0] at h0
        exact Fin.le_def.mpr h0
      · have hzfree' : z ∉ oj.val := fun hmem => hzfree (hsuboj hmem)
        have hle := linTake_pref_ge s t f i.val _ y htake oj hoj cstar hy z hz hzfree'
        exact Fin.le_def.mpr hle
    exact ⟨i, himem', hi_eq, hpref⟩
  choose icar hicarn hicar_eq hicar_pref using ycar
  -- The witnessing cars, plus the failed car, violate the threshold.
  set Cars0 : Finset (Fin s) :=
    Spots.attach.image (fun y => icar y.val y.property) with hCars0def
  have hinj0 : Function.Injective
      (fun y : ↥Spots => icar y.val y.property) := by
    intro a b hab
    simp only at hab
    have e1 := hicar_eq a.val a.property
    have e2 := hicar_eq b.val b.property
    have hval : a.val = b.val := by rw [← e1, ← e2, hab]
    exact Subtype.ext hval
  have hcard0 : Cars0.card = Spots.card := by
    rw [hCars0def, Finset.card_image_of_injective _ hinj0, Finset.card_attach]
  have hsub0 : Cars0 ⊆ Finset.univ.filter (fun i : Fin s => k ≤ f i) := by
    intro i hi
    rw [hCars0def, Finset.mem_image] at hi
    obtain ⟨y, _, rfl⟩ := hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hicar_pref y.val y.property
  set Cars : Finset (Fin s) := insert ⟨n, hn⟩ Cars0 with hCarsdef
  have hnotin : (⟨n, hn⟩ : Fin s) ∉ Cars0 := by
    intro hmem
    rw [hCars0def, Finset.mem_image] at hmem
    obtain ⟨y, _, hy⟩ := hmem
    have hlt_y := hicarn y.val y.property
    rw [hy] at hlt_y
    simp at hlt_y
  have hcardCars : Cars.card = t - cstar + 1 := by
    rw [hCarsdef, Finset.card_insert_of_notMem hnotin, hcard0, hspots]
  have hsub : Cars ⊆ Finset.univ.filter (fun i : Fin s => k ≤ f i) := by
    intro i hi
    rw [hCarsdef, Finset.mem_insert] at hi
    rcases hi with rfl | h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_def.mpr hlea
    · exact hsub0 h
  have hle := Finset.card_le_card hsub
  rw [hcardCars] at hle
  omega

/-- Embedding of linear spots into the circle. -/
private def emb (t : ℕ) (x : Fin t) : ZMod (t + 1) := ((x.val : ℕ) : ZMod (t + 1))

/-- The extra spot on the circle. -/
private def extra (t : ℕ) : ZMod (t + 1) := ((t : ℕ) : ZMod (t + 1))

/-- Lifting linear preferences to the circle. -/
private def lift (s t : ℕ) (f : Fin s → Fin t) : Fin s → ZMod (t + 1) :=
  fun i => emb t (f i)

private theorem emb_val (t : ℕ) (x : Fin t) : (emb t x).val = x.val :=
  ZMod.val_natCast_of_lt (by have := x.isLt; omega)

private theorem extra_val (t : ℕ) : (extra t).val = t :=
  ZMod.val_natCast_of_lt (Nat.lt_succ_self t)

private theorem emb_injective (t : ℕ) : Function.Injective (emb t) := by
  intro x y hxy
  have h := congrArg ZMod.val hxy
  rw [emb_val, emb_val] at h
  exact Fin.ext h

private theorem emb_ne_extra (t : ℕ) (x : Fin t) : emb t x ≠ extra t := by
  intro hcon
  have h := congrArg ZMod.val hcon
  rw [emb_val, extra_val] at h
  omega

/-- Circle parking from a linear-range spot finds the linear take. -/
private theorem bridge_some (t : ℕ) (ol : Finset (Fin t)) (a b : Fin t)
    (occ : Finset (ZMod (t + 1))) (himg : occ = ol.image (emb t))
    (hc : occ.card < t + 1)
    (hff : linFirstFree t ol a.val = some b) :
    firstFree t occ (emb t a) hc = emb t b := by
  have hmem := linFirstFree_mem t ol a.val b hff
  have hle_ab : a.val ≤ b.val := hmem.1
  have hbn : b ∉ ol := hmem.2
  have hQ : ∃ j : ℕ, emb t a + ((j : ℕ) : ZMod (t + 1)) ∉ occ :=
    ray_free_exists t occ (emb t a) hc
  set d := b.val - a.val with hd
  have hray : emb t a + ((d : ℕ) : ZMod (t + 1)) = emb t b := by
    unfold emb
    rw [← Nat.cast_add]
    congr 1
    omega
  have hmem_at : ∀ j : ℕ, j < d → emb t a + ((j : ℕ) : ZMod (t + 1)) ∈ occ := by
    intro j hj
    have hjlt : a.val + j < t := by
      have hblt := b.isLt
      omega
    have hmem_ol : (⟨a.val + j, hjlt⟩ : Fin t) ∈ ol := by
      by_contra hcon
      have hle := linFirstFree_le t ol a.val b hff _ (Nat.le_add_right _ _) hcon
      have hle' : b.val ≤ a.val + j := hle
      omega
    have hray_j : emb t a + ((j : ℕ) : ZMod (t + 1)) =
        emb t (⟨a.val + j, hjlt⟩ : Fin t) := by
      unfold emb
      rw [← Nat.cast_add]
    rw [hray_j, himg, Finset.mem_image]
    exact ⟨_, hmem_ol, rfl⟩
  have hfind : Nat.find hQ = d := by
    apply le_antisymm
    · apply Nat.find_min' hQ
      rw [hray, himg]
      intro hcon
      rw [Finset.mem_image] at hcon
      obtain ⟨y, hy, hye⟩ := hcon
      have heq : y = b := emb_injective t hye
      rw [heq] at hy
      exact hbn hy
    · by_contra hcon
      have hlt : Nat.find hQ < d := lt_of_not_ge hcon
      exact (Nat.find_spec hQ) (hmem_at _ hlt)
  have hfirst : firstFree t occ (emb t a) hc =
      emb t a + (((Nat.find hQ : ℕ)) : ZMod (t + 1)) := rfl
  rw [hfirst, hfind, hray]

/-- Circle parking fails into the extra spot exactly when linear parking fails. -/
private theorem bridge_none (t : ℕ) (ol : Finset (Fin t)) (a : Fin t)
    (occ : Finset (ZMod (t + 1))) (himg : occ = ol.image (emb t))
    (hc : occ.card < t + 1) (hce : extra t ∉ occ)
    (hff : linFirstFree t ol a.val = none) :
    firstFree t occ (emb t a) hc = extra t := by
  have hQ : ∃ j : ℕ, emb t a + ((j : ℕ) : ZMod (t + 1)) ∉ occ :=
    ray_free_exists t occ (emb t a) hc
  set d := t - a.val with hd
  have hmem_at : ∀ j : ℕ, j < d → emb t a + ((j : ℕ) : ZMod (t + 1)) ∈ occ := by
    intro j hj
    have hjlt : a.val + j < t := by
      have halt := a.isLt
      omega
    have hmem_ol : (⟨a.val + j, hjlt⟩ : Fin t) ∈ ol :=
      linFirstFree_none t ol a.val hff _ (Nat.le_add_right _ _)
    have hray_j : emb t a + ((j : ℕ) : ZMod (t + 1)) =
        emb t (⟨a.val + j, hjlt⟩ : Fin t) := by
      unfold emb
      rw [← Nat.cast_add]
    rw [hray_j, himg, Finset.mem_image]
    exact ⟨_, hmem_ol, rfl⟩
  have hray_d : emb t a + ((d : ℕ) : ZMod (t + 1)) = extra t := by
    unfold emb extra
    rw [← Nat.cast_add]
    congr 1
    have halt := a.isLt
    omega
  have hQd : emb t a + ((d : ℕ) : ZMod (t + 1)) ∉ occ := by
    rwa [hray_d]
  have hfind : Nat.find hQ = d := by
    apply le_antisymm
    · exact Nat.find_min' hQ hQd
    · by_contra hcon
      have hlt : Nat.find hQ < d := lt_of_not_ge hcon
      exact (Nat.find_spec hQ) (hmem_at _ hlt)
  have hfirst : firstFree t occ (emb t a) hc =
      emb t a + (((Nat.find hQ : ℕ)) : ZMod (t + 1)) := rfl
  rw [hfirst, hfind, hray_d]

/-- Circle-occupied card bound. -/
private theorem circle_card_lt (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (m : ℕ) (hm : m ≤ s) : (parkOcc s t g hst m).card < t + 1 := by
  have hle := card_parkOcc_le s t g hst m
  omega

/-- Empty extra spot implies linear success. -/
private theorem circle_empty_imp_linSuccess (s t : ℕ) (f : Fin s → Fin t)
    (hst : s ≤ t)
    (hmem : extra t ∈ parkEmpty s t (lift s t f) hst) :
    LinSuccess s t f := by
  have hnot : extra t ∉ parkOcc s t (lift s t f) hst s := by
    have h := hmem
    unfold parkEmpty at h
    exact (Finset.mem_sdiff.mp h).2
  have key : ∀ m : ℕ, m ≤ s → ∃ ol : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some ol ∧
        parkOcc s t (lift s t f) hst m = ol.val.image (emb t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⟨∅, by simp⟩, linOccAux_zero s t f, ?_⟩
      change parkOcc s t (lift s t f) hst 0 = (∅ : Finset (Fin t)).image (emb t)
      simp only [parkOcc, parkOccAux, Finset.image_empty]
    | succ m ih =>
      intro hms1
      have hms : m ≤ s := by omega
      obtain ⟨ol, hol, hcir⟩ := ih hms
      have hmlt : m < s := by omega
      match hff : linFirstFree t ol.val (f ⟨m, hmlt⟩).val with
      | none =>
        exfalso
        have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
        have hsub := parkOcc_mono s t (lift s t f) hst (by omega : m ≤ s)
        have hce : extra t ∉ parkOcc s t (lift s t f) hst m :=
          fun hcon => hnot (hsub hcon)
        have hbridge := bridge_none t ol.val (f ⟨m, hmlt⟩)
          (parkOcc s t (lift s t f) hst m) hcir hcard hce hff
        have hstep := parkOcc_succ_of_lt s t (lift s t f) hst m hmlt
        have hass : parkAssign s t (lift s t f) hst m hmlt = extra t :=
          hbridge
        have hmem1 : extra t ∈ parkOcc s t (lift s t f) hst (m + 1) := by
          rw [hstep, hass]
          exact Finset.mem_insert_self _ _
        have hsub2 := parkOcc_mono s t (lift s t f) hst (by omega : m + 1 ≤ s)
        exact hnot (hsub2 hmem1)
      | some b =>
        have hsucc2 := linOccAux_succ_some s t f m ol hol hmlt b hff
        have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
        have hbridge := bridge_some t ol.val (f ⟨m, hmlt⟩) b
          (parkOcc s t (lift s t f) hst m) hcir hcard hff
        have hass : parkAssign s t (lift s t f) hst m hmlt = emb t b :=
          hbridge
        refine ⟨⟨insert b ol.val, ?_⟩, hsucc2, ?_⟩
        · have hle := ol.property
          have hmem := linFirstFree_mem t ol.val (f ⟨m, hmlt⟩).val b hff
          have hci := Finset.card_insert_le b ol.val
          omega
        · rw [parkOcc_succ_of_lt s t (lift s t f) hst m hmlt, hass,
            Finset.image_insert, hcir]
  obtain ⟨ol, hol, _⟩ := key s (le_refl s)
  unfold LinSuccess
  exact hol.symm ▸ Option.isSome_some

/-- Linear success keeps the extra spot empty. -/
private theorem linSuccess_imp_circle_empty (s t : ℕ) (f : Fin s → Fin t)
    (hst : s ≤ t) (hsucc : LinSuccess s t f) :
    extra t ∈ parkEmpty s t (lift s t f) hst := by
  have key : ∀ m : ℕ, m ≤ s → ∃ ol : { occ : Finset (Fin t) // occ.card ≤ m },
      linOccAux s t f m = some ol ∧
        parkOcc s t (lift s t f) hst m = ol.val.image (emb t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⟨∅, by simp⟩, linOccAux_zero s t f, ?_⟩
      change parkOcc s t (lift s t f) hst 0 = (∅ : Finset (Fin t)).image (emb t)
      simp only [parkOcc, parkOccAux, Finset.image_empty]
    | succ m ih =>
      intro hms1
      have hms : m ≤ s := by omega
      obtain ⟨ol, hol, hcir⟩ := ih hms
      have hmlt : m < s := by omega
      obtain ⟨b, hb⟩ := linTake_some_of_success s t f hsucc m hmlt
      have hff : linFirstFree t ol.val (f ⟨m, hmlt⟩).val = some b := by
        have h1 : linTake s t f m hmlt = linFirstFree t ol.val (f ⟨m, hmlt⟩).val :=
          linTake_eq s t f m hmlt ol hol
        rwa [h1] at hb
      have hsucc2 := linOccAux_succ_some s t f m ol hol hmlt b hff
      have hcard := circle_card_lt s t (lift s t f) hst m (by omega)
      have hbridge := bridge_some t ol.val (f ⟨m, hmlt⟩) b
        (parkOcc s t (lift s t f) hst m) hcir hcard hff
      have hass : parkAssign s t (lift s t f) hst m hmlt = emb t b :=
        hbridge
      refine ⟨⟨insert b ol.val, ?_⟩, hsucc2, ?_⟩
      · have hle := ol.property
        have hmem := linFirstFree_mem t ol.val (f ⟨m, hmlt⟩).val b hff
        have hci := Finset.card_insert_le b ol.val
        omega
      · rw [parkOcc_succ_of_lt s t (lift s t f) hst m hmlt, hass,
          Finset.image_insert, hcir]
  obtain ⟨ol, hol, hcir⟩ := key s (le_refl s)
  have hne : extra t ∉ ol.val.image (emb t) := by
    intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨y, _, hye⟩ := hcon
    exact emb_ne_extra t y hye
  rw [← hcir] at hne
  change extra t ∈ Finset.univ \ parkOcc s t (lift s t f) hst s
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, hne⟩

/-- A circle function leaving the extra spot empty never prefers it. -/
private theorem circle_empty_avoids (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (hst : s ≤ t) (hmem : extra t ∈ parkEmpty s t g hst)
    (i : Fin s) : g i ≠ extra t := by
  have hmemE : extra t ∉ parkOcc s t g hst s := by
    have h := hmem
    unfold parkEmpty at h
    exact (Finset.mem_sdiff.mp h).2
  intro hcon
  by_cases h : extra t ∈ parkOcc s t g hst i.val
  · exact hmemE (parkOcc_mono s t g hst (by have := i.isLt; omega) h)
  · have hcard : (parkOcc s t g hst i.val).card < t + 1 :=
      circle_card_lt s t g hst i.val (by have := i.isLt; omega)
    have hQ0 : extra t + ((0 : ℕ) : ZMod (t + 1)) ∉ parkOcc s t g hst i.val := by
      simpa using h
    have hfind : Nat.find (ray_free_exists t (parkOcc s t g hst i.val) (extra t) hcard) = 0 :=
      Nat.le_zero.mp (Nat.find_min' _ hQ0)
    have hass : parkAssign s t g hst i.val i.isLt = extra t := by
      have hgi : g ⟨i.val, i.isLt⟩ = extra t := hcon
      have hbase : firstFree t (parkOcc s t g hst i.val) (extra t) hcard = extra t := by
        have hfirst : firstFree t (parkOcc s t g hst i.val) (extra t) hcard =
            extra t + (((Nat.find (ray_free_exists t (parkOcc s t g hst i.val) (extra t) hcard) :
                ℕ)) : ZMod (t + 1)) := rfl
        rw [hfirst, hfind]
        simp
      unfold parkAssign
      rw [hgi]
      exact hbase
    have hmem1 : extra t ∈ parkOcc s t g hst (i.val + 1) := by
      rw [parkOcc_succ_of_lt s t g hst i.val i.isLt, hass]
      exact Finset.mem_insert_self _ _
    exact hmemE (parkOcc_mono s t g hst (by have := i.isLt; omega) hmem1)

/-- Translation of circle preferences. -/
private def transPerm (s t : ℕ) (c : ZMod (t + 1)) :
    (Fin s → ZMod (t + 1)) ≃ (Fin s → ZMod (t + 1)) :=
  { toFun := fun g i => g i + c,
    invFun := fun g i => g i - c,
    left_inv := by
      intro g
      funext i
      change (g i + c) - c = g i
      abel,
    right_inv := by
      intro g
      funext i
      change (g i - c) + c = g i
      abel }

/-- All fibers over circle spots have the same cardinality. -/
private def fiberEquiv (s t : ℕ) (hst : s ≤ t) (x : ZMod (t + 1)) :
    {g : Fin s → ZMod (t + 1) // x ∈ parkEmpty s t g hst} ≃
    {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
  (transPerm s t (extra t - x)).subtypeEquiv (by
    intro g
    change (x ∈ parkEmpty s t g hst) ↔
      (extra t ∈ parkEmpty s t (fun i => g i + (extra t - x)) hst)
    constructor
    · intro h
      have himg := parkEmpty_translate s t g hst (extra t - x)
      have hx : x + (extra t - x) = extra t := by abel
      rw [himg]
      exact Finset.mem_image.mpr ⟨x, h, hx⟩
    · intro h
      have hfun : (fun i => (g i + (extra t - x)) + (-(extra t - x))) = g := by
        funext i
        abel
      have himg2 := parkEmpty_translate s t (fun i => g i + (extra t - x)) hst
        (-(extra t - x))
      rw [hfun] at himg2
      rw [himg2]
      have hx : extra t + (-(extra t - x)) = x := by abel
      exact Finset.mem_image.mpr ⟨extra t, h, hx⟩)

/-- Pairs as a sigma type. -/
private def StoSigma (s t : ℕ) (hst : s ≤ t) :
    {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
      p.2 ∈ parkEmpty s t p.1 hst} ≃
    Σ _g : (Fin s → ZMod (t + 1)), ↥(parkEmpty s t _g hst) :=
  { toFun := fun ⟨⟨g, x⟩, h⟩ => ⟨g, ⟨x, h⟩⟩,
    invFun := fun ⟨g, ⟨x, h⟩⟩ => ⟨⟨g, x⟩, h⟩,
    left_inv := fun ⟨⟨_g, _x⟩, _h⟩ => rfl,
    right_inv := fun ⟨_g, ⟨_x, _h⟩⟩ => rfl }

/-- Fibers as a sigma type. -/
private def TtoSigma (s t : ℕ) (hst : s ≤ t) :
    {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
      p.1 ∈ parkEmpty s t p.2 hst} ≃
    Σ _x : ZMod (t + 1), {g : Fin s → ZMod (t + 1) //
      _x ∈ parkEmpty s t g hst} :=
  { toFun := fun ⟨⟨x, g⟩, h⟩ => ⟨x, ⟨g, h⟩⟩,
    invFun := fun ⟨x, ⟨g, h⟩⟩ => ⟨⟨x, g⟩, h⟩,
    left_inv := fun ⟨⟨_x, _g⟩, _h⟩ => rfl,
    right_inv := fun ⟨_x, ⟨_g, _h⟩⟩ => rfl }

/-- Restricting a circle function avoiding the extra spot to linear spots. -/
private def restrict (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (h : ∀ i, g i ≠ extra t) : Fin s → Fin t :=
  fun i => ⟨(g i).val, by
    have : NeZero (t + 1) := ⟨by omega⟩
    have hlt := ZMod.val_lt (g i)
    by_contra hcon
    have heq : (g i).val = t := by omega
    apply h i
    have h1 : (((g i).val : ℕ) : ZMod (t + 1)) = g i := by
      have h2 := ZMod.natCast_val (R := ZMod (t + 1)) (g i)
      rwa [ZMod.cast_id] at h2
    rw [heq] at h1
    exact h1.symm⟩

private theorem lift_restrict (s t : ℕ) (g : Fin s → ZMod (t + 1))
    (h : ∀ i, g i ≠ extra t) :
    lift s t (restrict s t g h) = g := by
  have : NeZero (t + 1) := ⟨by omega⟩
  funext i
  change (((g i).val : ℕ) : ZMod (t + 1)) = g i
  have h2 := ZMod.natCast_val (R := ZMod (t + 1)) (g i)
  rwa [ZMod.cast_id] at h2

private theorem restrict_lift (s t : ℕ) (f : Fin s → Fin t)
    (h : ∀ i, lift s t f i ≠ extra t) :
    restrict s t (lift s t f) h = f := by
  funext i
  apply Fin.ext
  change (lift s t f i).val = (f i).val
  rw [show lift s t f i = emb t (f i) from rfl]
  exact emb_val t (f i)

/-- Partial parking functions correspond to circle functions leaving the
extra spot empty. -/
private def PfEquiv (s t : ℕ) (hst : s ≤ t) :
    {f : Fin s → Fin t // IsPartialParkingFunction s t f} ≃
    {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
  { toFun := fun ⟨f, hf⟩ => ⟨lift s t f,
      linSuccess_imp_circle_empty s t f hst
        (threshold_imp_linSuccess s t f hf hst)⟩,
    invFun := fun ⟨g, hg⟩ =>
      let hav : ∀ i, g i ≠ extra t :=
        fun i => circle_empty_avoids s t g hst hg i
      ⟨restrict s t g hav, by
        have hmem : extra t ∈
            parkEmpty s t (lift s t (restrict s t g hav)) hst := by
          have e := lift_restrict s t g hav
          rwa [e]
        have hsucc :=
          circle_empty_imp_linSuccess s t (restrict s t g hav) hst hmem
        exact linSuccess_imp_threshold s t (restrict s t g hav) hsucc⟩,
    left_inv := fun ⟨f, hf⟩ => Subtype.ext (restrict_lift s t f
      (fun i => circle_empty_avoids s t (lift s t f) hst
        (linSuccess_imp_circle_empty s t f hst
          (threshold_imp_linSuccess s t f hf hst)) i)),
    right_inv := fun ⟨g, hg⟩ => Subtype.ext (lift_restrict s t g
      (fun i => circle_empty_avoids s t g hst hg i)) }

/-- Double count, grouped by preference function. -/
private theorem card_circle_pairs (s t : ℕ) (hst : s ≤ t) :
    Fintype.card {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
      p.2 ∈ parkEmpty s t p.1 hst} = (t + 1 - s) * (t + 1) ^ s := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have hdom : Fintype.card (Fin s → ZMod (t + 1)) = (t + 1) ^ s := by
    rw [Fintype.card_pi_const, ZMod.card]
  have e := Fintype.card_congr (StoSigma s t hst)
  rw [e, Fintype.card_sigma]
  have hsum : (∑ g : (Fin s → ZMod (t + 1)),
        Fintype.card ↥(parkEmpty s t g hst)) =
      ∑ _g : (Fin s → ZMod (t + 1)), (t + 1 - s) :=
    Finset.sum_congr rfl (fun g _ => by
      rw [Fintype.card_coe, card_parkEmpty s t g hst])
  rw [hsum, Finset.sum_const, Finset.card_univ, hdom, smul_eq_mul]
  ring

/-- Double count, grouped by empty spot. -/
private theorem card_circle_fibers (s t : ℕ) (hst : s ≤ t) :
    Fintype.card {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
      p.1 ∈ parkEmpty s t p.2 hst} =
    (t + 1) * Fintype.card
      {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have e := Fintype.card_congr (TtoSigma s t hst)
  rw [e, Fintype.card_sigma]
  have hsum : (∑ x : ZMod (t + 1),
        Fintype.card {g : Fin s → ZMod (t + 1) // x ∈ parkEmpty s t g hst}) =
      ∑ _x : ZMod (t + 1), Fintype.card
        {g : Fin s → ZMod (t + 1) // extra t ∈ parkEmpty s t g hst} :=
    Finset.sum_congr rfl (fun x _ => Fintype.card_congr (fiberEquiv s t hst x))
  rw [hsum, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]


/-- **Number of partial parking functions.** Let $s$ and $t$ be natural numbers with
$0 < s \le t$. A partial parking function with $s$ cars and $t$ spots is a map
$f : \{0, \dots, s - 1\} \to \{0, \dots, t - 1\}$ such that for every spot
$k \in \{0, \dots, t - 1\}$ at most $t - k$ cars $i$ have $f(i) \ge k$. The number of partial
parking functions with $s$ cars and $t$ spots is $(t + 1 - s)(t + 1)^{s - 1}$.

The proof is Pollak's circle argument.

Proves `Wanted` entry `pollak_partial_parking_functions_card`.

Source: Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
“Lucky Cars and Lucky Spots in Parking Functions”, Journal of Integer Sequences 29 (2026),
Article 26.1.1, proposition at lines 330–332 of
https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex (independently verified; full source
SHA-256 d166e7759bfd986aebf8bd5632479d9f5e4f11b28f5250ed1e5290851a8d6139, normalized
no-final-newline proposition-span SHA-256
58e90130ad683625acf4a657d5bbbf145f2700065e2991cfd7084425783cc1fe).
-/
theorem pollak_partial_parking_functions_card
    (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) :
    Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
    (t + 1 - s) * (t + 1) ^ (s - 1) := by
  have : NeZero (t + 1) := ⟨by omega⟩
  have hPf : Nat.card {f : Fin s → Fin t // IsPartialParkingFunction s t f} =
      Nat.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} :=
    Nat.card_congr (PfEquiv s t hst)
  have hS := card_circle_pairs s t hst
  have hT := card_circle_fibers s t hst
  have hST : Fintype.card {p : (Fin s → ZMod (t + 1)) × ZMod (t + 1) //
        p.2 ∈ parkEmpty s t p.1 hst} =
      Fintype.card {p : ZMod (t + 1) × (Fin s → ZMod (t + 1)) //
        p.1 ∈ parkEmpty s t p.2 hst} :=
    Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv (fun _ => Iff.rfl))
  have hG : Nat.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} =
      Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} :=
    Nat.card_eq_fintype_card
  rw [hPf, hG]
  have heq : (t + 1) * Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} = (t + 1 - s) * (t + 1) ^ s := by
    rw [← hT, ← hS]
    exact hST.symm
  have hpow : (t + 1) ^ s = (t + 1) * (t + 1) ^ (s - 1) := by
    have hs1 : s = (s - 1) + 1 := by omega
    conv_lhs => rw [hs1, pow_succ]
    exact mul_comm _ _
  have hfin : Fintype.card {g : Fin s → ZMod (t + 1) //
        extra t ∈ parkEmpty s t g hst} = (t + 1 - s) * (t + 1) ^ (s - 1) := by
    have h := heq
    rw [hpow] at h
    have hassoc : (t + 1 - s) * ((t + 1) * (t + 1) ^ (s - 1)) =
        (t + 1) * ((t + 1 - s) * (t + 1) ^ (s - 1)) := by ring
    rw [hassoc] at h
    exact Nat.mul_left_cancel (Nat.succ_pos t) h
  exact hfin

end MetaMathlibExt.PollakPartialParking
