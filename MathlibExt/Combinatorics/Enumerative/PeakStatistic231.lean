/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

section
namespace MetaMathlibExt

namespace Peak231

private abbrev Avoids231 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)

private abbrev IsPeakAt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ iPrev iNext : Fin n,
    iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
    σ iPrev < σ i ∧ σ iNext < σ i

private abbrev peakCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => IsPeakAt σ i)).card

private def avoidCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    Avoids231 σ ∧ peakCount σ = k)).card

-- bridge: Wanted LHS is avoidCount by rfl
example (n k : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
    avoidCount n k := rfl

private def peakConv (F : ℕ → ℕ → ℕ) (a b k : ℕ) : ℕ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, F a p.1 * F b p.2

private def peakRec (F : ℕ → ℕ → ℕ) (n k : ℕ) : ℕ :=
  ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
    (if q.1 = 0 ∨ q.2 = 0 then peakConv F q.1 q.2 k
     else (if k = 0 then 0 else peakConv F q.1 q.2 (k - 1)))

private def peakV (n p : ℕ) : ℕ :=
  if n = 0 then 0 else 2 ^ (n - p - 1) * Nat.choose (n - 1) p

private def peakT (n k : ℕ) : ℕ :=
  2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k

private def peakU : PowerSeries ℕ :=
  PowerSeries.mk fun m => if m = 0 then 0 else 2 ^ (m - 1)

-- N1
private def joinMaxFun {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Fin (a + b + 1) → Fin (a + b + 1) :=
  fun i =>
    if h1 : i.val < a then ⟨(α ⟨i.val, h1⟩).val, by have h2 := (α ⟨i.val, h1⟩).isLt; omega⟩
    else if _h2 : i.val = a then Fin.last (a + b)
    else ⟨a + (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).val,
      by have h4 := (β ⟨i.val - a - 1, by have h3 := i.isLt; omega⟩).isLt
         have h3 := i.isLt; omega⟩

private theorem joinMaxFun_inj {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Function.Injective (joinMaxFun α β) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  simp only [joinMaxFun] at hval
  have hi1 : i.val < a + b + 1 := i.isLt
  have hj1 : j.val < a + b + 1 := j.isLt
  have hlast : (Fin.last (a + b)).val = a + b := Fin.val_last _
  by_cases hiL : i.val < a <;> by_cases hiM : i.val = a <;>
    by_cases hjL : j.val < a <;> by_cases hjM : j.val = a
  · omega  -- TTTT contra
  · omega  -- TTTF contra
  · omega  -- TTFT contra
  · omega  -- TTFF contra
  · omega  -- TFTT contra j
  · -- TFTF left,left
    simp only [dite_eq_left hiL, dite_eq_left hjL] at hval
    have ha : (⟨i.val, hiL⟩ : Fin a) = ⟨j.val, hjL⟩ :=
      α.injective (Fin.ext hval)
    have hvv := congrArg Fin.val ha
    exact Fin.ext hvv
  · -- TFFT left,mid
    simp only [dite_eq_left hiL, dite_eq_right hjL, dite_eq_left hjM] at hval
    exfalso
    have hα : (α ⟨i.val, hiL⟩).val < a := (α ⟨i.val, hiL⟩).isLt
    omega
  · -- TFFF left,right
    simp only [dite_eq_left hiL, dite_eq_right hjL, dite_eq_right hjM] at hval
    exfalso
    have hα : (α ⟨i.val, hiL⟩).val < a := (α ⟨i.val, hiL⟩).isLt
    have hβ : (β ⟨j.val - a - 1, by omega⟩).val < b :=
      (β ⟨j.val - a - 1, by omega⟩).isLt
    omega
  · omega  -- FTTT contra j
  · -- FTTF mid,left
    simp only [dite_eq_right hiL, dite_eq_left hiM, dite_eq_left hjL] at hval
    exfalso
    have hα : (α ⟨j.val, hjL⟩).val < a := (α ⟨j.val, hjL⟩).isLt
    omega
  · -- FTFT mid,mid
    simp only [dite_eq_right hiL, dite_eq_left hiM,
      dite_eq_right hjL, dite_eq_left hjM] at hval
    have hv : i.val = j.val := by omega
    exact Fin.ext hv
  · -- FTFF mid,right
    simp only [dite_eq_right hiL, dite_eq_left hiM,
      dite_eq_right hjL, dite_eq_right hjM] at hval
    exfalso
    have hβ : (β ⟨j.val - a - 1, by omega⟩).val < b :=
      (β ⟨j.val - a - 1, by omega⟩).isLt
    omega
  · omega  -- FFTT contra j
  · -- FFTF right,left
    simp only [dite_eq_right hiL, dite_eq_right hiM, dite_eq_left hjL] at hval
    exfalso
    have hα : (α ⟨j.val, hjL⟩).val < a := (α ⟨j.val, hjL⟩).isLt
    have hβ : (β ⟨i.val - a - 1, by omega⟩).val < b :=
      (β ⟨i.val - a - 1, by omega⟩).isLt
    omega
  · -- FFFT right,mid
    simp only [dite_eq_right hiL, dite_eq_right hiM,
      dite_eq_right hjL, dite_eq_left hjM] at hval
    exfalso
    have hβ : (β ⟨i.val - a - 1, by omega⟩).val < b :=
      (β ⟨i.val - a - 1, by omega⟩).isLt
    omega
  · -- FFFF right,right
    simp only [dite_eq_right hiL, dite_eq_right hiM,
      dite_eq_right hjL, dite_eq_right hjM] at hval
    have hb : (⟨i.val - a - 1, by omega⟩ : Fin b) = ⟨j.val - a - 1, by omega⟩ := by
      apply β.injective
      apply Fin.ext
      omega
    have hv : i.val - a - 1 = j.val - a - 1 := by exact congrArg Fin.val hb
    have hv2 : i.val = j.val := by omega
    exact Fin.ext hv2

private noncomputable def joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Equiv.Perm (Fin (a + b + 1)) :=
  Equiv.ofBijective (joinMaxFun α β) (Finite.injective_iff_bijective.mp (joinMaxFun_inj α β))

private theorem joinMax_apply_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {i : Fin (a + b + 1)} (h : i.val < a) :
    (joinMax α β i).val = (α ⟨i.val, h⟩).val := by
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun, dite_eq_left h]

private theorem joinMax_apply_eq {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    joinMax α β ⟨a, by omega⟩ = Fin.last (a + b) := by
  have hneg : ¬ (⟨a, by omega⟩ : Fin (a + b + 1)).val < a := by
    change ¬ a < a
    exact lt_irrefl _
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun]
  rw [dite_eq_right hneg]
  simp

private theorem joinMax_apply_gt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {i : Fin (a + b + 1)} (h : a < i.val) :
    (joinMax α β i).val = a + (β ⟨i.val - a - 1, by omega⟩).val := by
  simp only [joinMax, Equiv.ofBijective_apply, joinMaxFun,
    dite_eq_right (by omega : ¬ i.val < a), dite_eq_right (by omega : ¬ i.val = a)]

private theorem joinMax_symm_last {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    (joinMax α β).symm (Fin.last (a + b)) = ⟨a, by omega⟩ := by
  rw [Equiv.symm_apply_eq]
  exact (joinMax_apply_eq α β).symm

private theorem joinMax_inj {a b : ℕ} {α α' : Equiv.Perm (Fin a)} {β β' : Equiv.Perm (Fin b)}
    (h : joinMax α β = joinMax α' β') : α = α' ∧ β = β' := by
  have hα : α = α' := by
    apply Equiv.ext
    intro j
    set pos : Fin (a + b + 1) := ⟨j.val, by have hj := j.isLt; omega⟩ with hpos_def
    have hpos : pos.val < a := j.isLt
    have h2 := congrArg (fun e : Equiv.Perm (Fin (a + b + 1)) => e pos) h
    have h2v := congrArg Fin.val h2
    have e1 := joinMax_apply_lt α β (i := pos) hpos
    have e2 := joinMax_apply_lt α' β' (i := pos) hpos
    rw [e1, e2] at h2v
    have e : (⟨pos.val, hpos⟩ : Fin a) = j := by
      apply Fin.ext
      change pos.val = j.val
      rw [hpos_def]
    rw [e] at h2v
    exact Fin.ext h2v
  have hβ : β = β' := by
    apply Equiv.ext
    intro j
    set pos : Fin (a + b + 1) := ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩ with hpos_def
    have hpos : a < pos.val := by
      change a < a + 1 + j.val
      omega
    have h2 := congrArg (fun e : Equiv.Perm (Fin (a + b + 1)) => e pos) h
    have h2v := congrArg Fin.val h2
    have e1 := joinMax_apply_gt α β (i := pos) hpos
    have e2 := joinMax_apply_gt α' β' (i := pos) hpos
    rw [e1, e2] at h2v
    have hsub : pos.val - a - 1 = j.val := by
      have : pos.val = a + 1 + j.val := by rw [hpos_def]
      omega
    -- canonical re-ascription (proof irrelevance makes this defeq to h2v)
    have h2c : (β ⟨pos.val - a - 1, by have hj := j.isLt; omega⟩).val =
        (β' ⟨pos.val - a - 1, by have hj := j.isLt; omega⟩).val :=
      add_left_cancel_iff.mp (by exact h2v)
    have eB : (⟨pos.val - a - 1, by have hj := j.isLt; omega⟩ : Fin b) = j := by
      apply Fin.ext
      change pos.val - a - 1 = j.val
      exact hsub
    rw [eB] at h2c
    exact Fin.ext h2c
  exact ⟨hα, hβ⟩

-- N2 helpers
private theorem joinMax_val_lt_of_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {p : Fin (a + b + 1)} (h : p.val < a) : (joinMax α β p).val < a := by
  rw [joinMax_apply_lt α β h]
  exact (α ⟨p.val, h⟩).isLt

private theorem joinMax_ge_of_gt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {p : Fin (a + b + 1)} (h : a < p.val) : a ≤ (joinMax α β p).val := by
  rw [joinMax_apply_gt α β h]
  omega

private theorem joinMax_val_of_eq {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {p : Fin (a + b + 1)} (h : p.val = a) : (joinMax α β p).val = a + b := by
  have hp : p = ⟨a, Nat.lt_succ_of_le (Nat.le_add_right a b)⟩ := Fin.ext h
  rw [hp]
  exact congrArg Fin.val (joinMax_apply_eq α β)

private theorem joinMax_pos_lt_of_val_lt {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (p : Fin (a + b + 1)) (h : (joinMax α β p).val < a) : p.val < a := by
  rcases lt_or_ge p.val a with hlt | hge
  · exact hlt
  · exfalso
    rcases eq_or_lt_of_le hge with he | hgt
    · have hv : (joinMax α β p).val = a + b := joinMax_val_of_eq α β he.symm
      omega
    · have hv : a ≤ (joinMax α β p).val := joinMax_ge_of_gt α β hgt
      omega

private theorem joinMax_val_left {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (x : Fin a) : (joinMax α β ⟨x.val, by have hx := x.isLt; omega⟩).val = (α x).val := by
  have h : (⟨x.val, by have hx := x.isLt; omega⟩ : Fin (a + b + 1)).val < a := x.isLt
  exact joinMax_apply_lt α β h

private theorem joinMax_val_right {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (y : Fin b) :
    (joinMax α β ⟨a + 1 + y.val, by have hy := y.isLt; omega⟩).val = a + (β y).val := by
  have h : a < (⟨a + 1 + y.val, by have hy := y.isLt; omega⟩ : Fin (a + b + 1)).val := by
    change a < a + 1 + y.val
    omega
  have e := joinMax_apply_gt α β h
  have hU : (⟨(⟨a + 1 + y.val, by have hy := y.isLt; omega⟩ : Fin (a + b + 1)).val - a - 1,
      by have hy := y.isLt; omega⟩ : Fin b) = y := by
    apply Fin.ext
    change a + 1 + y.val - a - 1 = y.val
    omega
  conv_rhs => rw [← hU]
  exact e

private theorem avoids231_joinMax_iff {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    Avoids231 (joinMax α β) ↔ Avoids231 α ∧ Avoids231 β := by
  constructor
  · intro hAv
    refine ⟨?_, ?_⟩
    · intro i j l hij hjl h231
      obtain ⟨h1, h2⟩ := h231
      have hvij : i.val < j.val := Fin.lt_def.mp hij
      have hvjl : j.val < l.val := Fin.lt_def.mp hjl
      have h1v : (α l).val < (α i).val := Fin.lt_def.mp h1
      have h2v : (α i).val < (α j).val := Fin.lt_def.mp h2
      set I : Fin (a + b + 1) := ⟨i.val, by have hi := i.isLt; omega⟩ with hIdef
      set J : Fin (a + b + 1) := ⟨j.val, by have hj := j.isLt; omega⟩ with hJdef
      set L : Fin (a + b + 1) := ⟨l.val, by have hl := l.isLt; omega⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = i.val := by rw [hIdef]
        have eJ : J.val = j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = j.val := by rw [hJdef]
        have eL : L.val = l.val := by rw [hLdef]
        omega)
      have vI : ((joinMax α β) I).val = (α i).val := joinMax_val_left α β i
      have vJ : ((joinMax α β) J).val = (α j).val := joinMax_val_left α β j
      have vL : ((joinMax α β) L).val = (α l).val := joinMax_val_left α β l
      have g1 : (joinMax α β) L < (joinMax α β) I := Fin.lt_def.mpr (by omega)
      have g2 : (joinMax α β) I < (joinMax α β) J := Fin.lt_def.mpr (by omega)
      exact hAv I J L oIJ oJL ⟨g1, g2⟩
    · intro i j l hij hjl h231
      obtain ⟨h1, h2⟩ := h231
      have hvij : i.val < j.val := Fin.lt_def.mp hij
      have hvjl : j.val < l.val := Fin.lt_def.mp hjl
      have h1v : (β l).val < (β i).val := Fin.lt_def.mp h1
      have h2v : (β i).val < (β j).val := Fin.lt_def.mp h2
      set I : Fin (a + b + 1) := ⟨a + 1 + i.val, by have hi := i.isLt; omega⟩ with hIdef
      set J : Fin (a + b + 1) := ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩ with hJdef
      set L : Fin (a + b + 1) := ⟨a + 1 + l.val, by have hl := l.isLt; omega⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = a + 1 + i.val := by rw [hIdef]
        have eJ : J.val = a + 1 + j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = a + 1 + j.val := by rw [hJdef]
        have eL : L.val = a + 1 + l.val := by rw [hLdef]
        omega)
      have vI : ((joinMax α β) I).val = a + (β i).val := joinMax_val_right α β i
      have vJ : ((joinMax α β) J).val = a + (β j).val := joinMax_val_right α β j
      have vL : ((joinMax α β) L).val = a + (β l).val := joinMax_val_right α β l
      have g1 : (joinMax α β) L < (joinMax α β) I := Fin.lt_def.mpr (by omega)
      have g2 : (joinMax α β) I < (joinMax α β) J := Fin.lt_def.mpr (by omega)
      exact hAv I J L oIJ oJL ⟨g1, g2⟩
  · intro hAB i j l hij hjl h231
    obtain ⟨hα, hβ⟩ := hAB
    obtain ⟨h1, h2⟩ := h231
    have v1 : ((joinMax α β) l).val < ((joinMax α β) i).val := Fin.lt_def.mp h1
    have v2 : ((joinMax α β) i).val < ((joinMax α β) j).val := Fin.lt_def.mp h2
    have hvij : i.val < j.val := Fin.lt_def.mp hij
    have hvjl : j.val < l.val := Fin.lt_def.mp hjl
    rcases lt_or_ge i.val a with hiA | hiA
    · have hva : ((joinMax α β) i).val < a := joinMax_val_lt_of_lt α β hiA
      have hla : l.val < a := by
        have hlt : ((joinMax α β) l).val < a := by omega
        exact joinMax_pos_lt_of_val_lt α β l hlt
      have hja : j.val < a := by omega
      set I : Fin a := ⟨i.val, hiA⟩ with hIdef
      set J : Fin a := ⟨j.val, hja⟩ with hJdef
      set L : Fin a := ⟨l.val, hla⟩ with hLdef
      have oIJ : I < J := Fin.lt_def.mpr (by
        have eI : I.val = i.val := by rw [hIdef]
        have eJ : J.val = j.val := by rw [hJdef]
        omega)
      have oJL : J < L := Fin.lt_def.mpr (by
        have eJ : J.val = j.val := by rw [hJdef]
        have eL : L.val = l.val := by rw [hLdef]
        omega)
      have wI : (α I).val = ((joinMax α β) i).val := (joinMax_val_left α β I).symm
      have wJ : (α J).val = ((joinMax α β) j).val := (joinMax_val_left α β J).symm
      have wL : (α L).val = ((joinMax α β) l).val := (joinMax_val_left α β L).symm
      have g1 : α L < α I := Fin.lt_def.mpr (by omega)
      have g2 : α I < α J := Fin.lt_def.mpr (by omega)
      exact hα I J L oIJ oJL ⟨g1, g2⟩
    · rcases eq_or_lt_of_le hiA with he | hgt
      · have hv : ((joinMax α β) i).val = a + b := joinMax_val_of_eq α β he.symm
        have hjb : ((joinMax α β) j).val < a + b + 1 := (joinMax α β j).isLt
        omega
      · have hja : a < j.val := by omega
        have hla : a < l.val := by omega
        set I : Fin b := ⟨i.val - a - 1, by have hii := i.isLt; omega⟩ with hIdef
        set J : Fin b := ⟨j.val - a - 1, by have hjj := j.isLt; omega⟩ with hJdef
        set L : Fin b := ⟨l.val - a - 1, by have hll := l.isLt; omega⟩ with hLdef
        have oIJ : I < J := Fin.lt_def.mpr (by
          have eI : I.val = i.val - a - 1 := by rw [hIdef]
          have eJ : J.val = j.val - a - 1 := by rw [hJdef]
          omega)
        have oJL : J < L := Fin.lt_def.mpr (by
          have eJ : J.val = j.val - a - 1 := by rw [hJdef]
          have eL : L.val = l.val - a - 1 := by rw [hLdef]
          omega)
        have hIlt : a < i.val := hgt
        have hJlt : a < j.val := hja
        have hLlt : a < l.val := hla
        have eI := joinMax_apply_gt α β (i := i) hIlt
        have eJ := joinMax_apply_gt α β (i := j) hJlt
        have eL := joinMax_apply_gt α β (i := l) hLlt
        have wI : ((joinMax α β) i).val = a + (β I).val := eI
        have wJ : ((joinMax α β) j).val = a + (β J).val := eJ
        have wL : ((joinMax α β) l).val = a + (β L).val := eL
        have g1 : β L < β I := Fin.lt_def.mpr (by omega)
        have g2 : β I < β J := Fin.lt_def.mpr (by omega)
        exact hβ I J L oIJ oJL ⟨g1, g2⟩

-- N3 helper: right-block value through a rescribed index
private theorem joinMax_val_gt_of {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    {p : Fin (a + b + 1)} (h : a < p.val) (y : Fin b) (hy : y.val = p.val - a - 1) :
    ((joinMax α β) p).val = a + (β y).val := by
  have e := joinMax_apply_gt α β (i := p) h
  have hh : (⟨p.val - a - 1, by have hii := p.isLt; omega⟩ : Fin b) = y := by
    apply Fin.ext
    change p.val - a - 1 = y.val
    omega
  rw [e, hh]

-- N3
private theorem isPeakAt_joinMax_left {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (i : ℕ) (h : i < a) :
    IsPeakAt (joinMax α β) ⟨i, by omega⟩ ↔ IsPeakAt α ⟨i, h⟩ := by
  set I : Fin (a + b + 1) := ⟨i, by omega⟩ with hIdef
  change IsPeakAt (joinMax α β) I ↔ IsPeakAt α ⟨i, h⟩
  have eI : I.val = i := by rw [hIdef]
  have hIa : I.val < a := h
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, g1, g2⟩
    have h1' : pPrev.val + 1 = i := h1
    have h2' : i + 1 = pNext.val := h2
    have hva : ((joinMax α β) I).val < a := joinMax_val_lt_of_lt α β hIa
    have g1v : ((joinMax α β) pPrev).val < ((joinMax α β) I).val := Fin.lt_def.mp g1
    have g2v : ((joinMax α β) pNext).val < ((joinMax α β) I).val := Fin.lt_def.mp g2
    rcases lt_or_ge pNext.val a with hnA | hnA
    · have hpA : pPrev.val < a := by omega
      set qPrev : Fin a := ⟨pPrev.val, hpA⟩ with hqPdef
      set qNext : Fin a := ⟨pNext.val, hnA⟩ with hqNdef
      have eP : qPrev.val = pPrev.val := by rw [hqPdef]
      have eN : qNext.val = pNext.val := by rw [hqNdef]
      have wP : (α qPrev).val = ((joinMax α β) pPrev).val :=
        (joinMax_val_left α β qPrev).symm
      have wN : (α qNext).val = ((joinMax α β) pNext).val :=
        (joinMax_val_left α β qNext).symm
      have wI : (α ⟨i, h⟩).val = ((joinMax α β) I).val :=
        (joinMax_val_left α β ⟨i, h⟩).symm
      refine ⟨qPrev, qNext, ?_, ?_, ?_, ?_⟩
      · show qPrev.val + 1 = (⟨i, h⟩ : Fin a).val
        omega
      · show (⟨i, h⟩ : Fin a).val + 1 = qNext.val
        omega
      · exact Fin.lt_def.mpr (by omega)
      · exact Fin.lt_def.mpr (by omega)
    · have heq : pNext.val = a := by omega
      have hv : ((joinMax α β) pNext).val = a + b := joinMax_val_of_eq α β heq
      omega
  · rintro ⟨qPrev, qNext, h1, h2, g1, g2⟩
    have h1' : qPrev.val + 1 = i := h1
    have h2' : i + 1 = qNext.val := h2
    have g1v : (α qPrev).val < (α ⟨i, h⟩).val := Fin.lt_def.mp g1
    have g2v : (α qNext).val < (α ⟨i, h⟩).val := Fin.lt_def.mp g2
    set P : Fin (a + b + 1) := ⟨qPrev.val, by have hq := qPrev.isLt; omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨qNext.val, by have hq := qNext.isLt; omega⟩ with hQdef
    have eP : P.val = qPrev.val := by rw [hPdef]
    have eQ : Q.val = qNext.val := by rw [hQdef]
    have wP : ((joinMax α β) P).val = (α qPrev).val := joinMax_val_left α β qPrev
    have wQ : ((joinMax α β) Q).val = (α qNext).val := joinMax_val_left α β qNext
    have wI : ((joinMax α β) I).val = (α ⟨i, h⟩).val := joinMax_val_left α β ⟨i, h⟩
    refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
    · show P.val + 1 = I.val
      omega
    · show I.val + 1 = Q.val
      omega
    · exact Fin.lt_def.mpr (by omega)
    · exact Fin.lt_def.mpr (by omega)

private theorem isPeakAt_joinMax_mid {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    IsPeakAt (joinMax α β) ⟨a, by omega⟩ ↔ ¬ (a = 0 ∨ b = 0) := by
  set M : Fin (a + b + 1) := ⟨a, by omega⟩ with hMdef
  change IsPeakAt (joinMax α β) M ↔ ¬ (a = 0 ∨ b = 0)
  have eM : M.val = a := by rw [hMdef]
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, _, _⟩
    intro hcon
    rcases hcon with rfl | rfl
    · omega
    · have hPlt : pNext.val < a + 0 + 1 := pNext.isLt
      omega
  · intro hne
    have ha : a ≠ 0 := fun hz => hne (Or.inl hz)
    have hb : b ≠ 0 := fun hz => hne (Or.inr hz)
    set P : Fin (a + b + 1) := ⟨a - 1, by omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨a + 1, by omega⟩ with hQdef
    have eP : P.val = a - 1 := by rw [hPdef]
    have eQ : Q.val = a + 1 := by rw [hQdef]
    have hMlast : joinMax α β M = Fin.last (a + b) := joinMax_apply_eq α β
    have g1 : (joinMax α β) P < (joinMax α β) M := by
      rw [hMlast, Fin.lt_last_iff_ne_last]
      intro hcon
      have hPM : P = M := by
        apply (joinMax α β).injective
        rw [hMlast]
        exact hcon
      have hval := congrArg Fin.val hPM
      omega
    have g2 : (joinMax α β) Q < (joinMax α β) M := by
      rw [hMlast, Fin.lt_last_iff_ne_last]
      intro hcon
      have hQM : Q = M := by
        apply (joinMax α β).injective
        rw [hMlast]
        exact hcon
      have hval := congrArg Fin.val hQM
      omega
    refine ⟨P, Q, ?_, ?_, g1, g2⟩
    · show P.val + 1 = M.val
      omega
    · show M.val + 1 = Q.val
      omega

private theorem isPeakAt_joinMax_right {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (j : ℕ) (h : j < b) :
    IsPeakAt (joinMax α β) ⟨a + 1 + j, by omega⟩ ↔ IsPeakAt β ⟨j, h⟩ := by
  set R : Fin (a + b + 1) := ⟨a + 1 + j, by omega⟩ with hRdef
  change IsPeakAt (joinMax α β) R ↔ IsPeakAt β ⟨j, h⟩
  have eR : R.val = a + 1 + j := by rw [hRdef]
  have hRa : a < R.val := by omega
  constructor
  · rintro ⟨pPrev, pNext, h1, h2, g1, g2⟩
    have h1' : pPrev.val + 1 = a + 1 + j := by omega
    have h2' : a + 1 + j + 1 = pNext.val := by omega
    have g1v : ((joinMax α β) pPrev).val < ((joinMax α β) R).val := Fin.lt_def.mp g1
    have g2v : ((joinMax α β) pNext).val < ((joinMax α β) R).val := Fin.lt_def.mp g2
    have hRtop : ((joinMax α β) R).val < a + b + 1 := (joinMax α β R).isLt
    rcases lt_or_ge a pPrev.val with hpA | hpA
    · have hnA : pNext.val < a + b + 1 := pNext.isLt
      have hpB : pPrev.val - a - 1 < b := by omega
      have hnB : pNext.val - a - 1 < b := by omega
      obtain ⟨qPrev, eP⟩ : ∃ q : Fin b, q.val = pPrev.val - a - 1 :=
        ⟨⟨pPrev.val - a - 1, hpB⟩, rfl⟩
      obtain ⟨qNext, eN⟩ : ∃ q : Fin b, q.val = pNext.val - a - 1 :=
        ⟨⟨pNext.val - a - 1, hnB⟩, rfl⟩
      have hplt : a < pNext.val := by omega
      have wP : ((joinMax α β) pPrev).val = a + (β qPrev).val :=
        joinMax_val_gt_of α β hpA qPrev eP
      have wN : ((joinMax α β) pNext).val = a + (β qNext).val :=
        joinMax_val_gt_of α β hplt qNext eN
      have wR : ((joinMax α β) R).val = a + (β ⟨j, h⟩).val := joinMax_val_right α β ⟨j, h⟩
      refine ⟨qPrev, qNext, ?_, ?_, ?_, ?_⟩
      · change qPrev.val + 1 = j
        omega
      · change j + 1 = qNext.val
        omega
      · exact Fin.lt_def.mpr (by omega)
      · exact Fin.lt_def.mpr (by omega)
    · have heq : pPrev.val = a := by omega
      have hv : ((joinMax α β) pPrev).val = a + b := joinMax_val_of_eq α β heq
      omega
  · rintro ⟨qPrev, qNext, h1, h2, g1, g2⟩
    have h1' : qPrev.val + 1 = j := h1
    have h2' : j + 1 = qNext.val := h2
    have g1v : (β qPrev).val < (β ⟨j, h⟩).val := Fin.lt_def.mp g1
    have g2v : (β qNext).val < (β ⟨j, h⟩).val := Fin.lt_def.mp g2
    set P : Fin (a + b + 1) := ⟨a + 1 + qPrev.val, by have hq := qPrev.isLt; omega⟩ with hPdef
    set Q : Fin (a + b + 1) := ⟨a + 1 + qNext.val, by have hq := qNext.isLt; omega⟩ with hQdef
    have eP : P.val = a + 1 + qPrev.val := by rw [hPdef]
    have eQ : Q.val = a + 1 + qNext.val := by rw [hQdef]
    have hPgt : a < P.val := by omega
    have hQgt : a < Q.val := by omega
    have wP : ((joinMax α β) P).val = a + (β qPrev).val :=
      joinMax_val_gt_of α β hPgt qPrev (by omega)
    have wQ : ((joinMax α β) Q).val = a + (β qNext).val :=
      joinMax_val_gt_of α β hQgt qNext (by omega)
    have wR : ((joinMax α β) R).val = a + (β ⟨j, h⟩).val := joinMax_val_right α β ⟨j, h⟩
    refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
    · show P.val + 1 = R.val
      omega
    · show R.val + 1 = Q.val
      omega
    · exact Fin.lt_def.mpr (by omega)
    · exact Fin.lt_def.mpr (by omega)

-- N4
private theorem peakCount_joinMax {a b : ℕ} (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b)) :
    peakCount (joinMax α β) = peakCount α + peakCount β + (if a = 0 ∨ b = 0 then 0 else 1) := by
  have hcard : ∀ {m : ℕ} (σ : Equiv.Perm (Fin m)),
      peakCount σ = ∑ i ∈ Finset.range m,
        (if h : i < m then (if IsPeakAt σ ⟨i, h⟩ then (1:ℕ) else 0) else 0) := by
    intro m σ
    unfold peakCount
    rw [Finset.card_filter, Finset.sum_fin_eq_sum_range]
  simp only [hcard]
  have hrange : Finset.range (a + b + 1) = Finset.range (a + (b + 1)) := by
    have heq : a + b + 1 = a + (b + 1) := by omega
    rw [heq]
  rw [hrange, Finset.sum_range_add _ a (b + 1), Finset.sum_range_succ' _ b]
  have e1 : (∑ x ∈ Finset.range a,
      (if h : x < a + b + 1 then
        (if IsPeakAt (joinMax α β) ⟨x, h⟩ then (1 : ℕ) else 0) else 0)) =
      ∑ x ∈ Finset.range a,
      (if h : x < a then (if IsPeakAt α ⟨x, h⟩ then (1 : ℕ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hii : i < a := Finset.mem_range.mp hi
    have hbound : i < a + b + 1 := by omega
    rw [dite_eq_left hbound, dite_eq_left hii]
    have key := isPeakAt_joinMax_left α β i hii
    by_cases hpk : IsPeakAt α ⟨i, hii⟩
    · have h1 : IsPeakAt (joinMax α β) ⟨i, hbound⟩ := key.mpr hpk
      simp only [h1, hpk, ite_true]
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨i, hbound⟩ := fun h => hpk (key.mp h)
      simp only [h1, hpk, ite_false]
  have e2 : (∑ k ∈ Finset.range b,
      (if h : a + (k + 1) < a + b + 1 then
        (if IsPeakAt (joinMax α β) ⟨a + (k + 1), h⟩ then (1 : ℕ) else 0) else 0)) =
      ∑ x ∈ Finset.range b,
      (if h : x < b then (if IsPeakAt β ⟨x, h⟩ then (1 : ℕ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hii : i < b := Finset.mem_range.mp hi
    have key := isPeakAt_joinMax_right α β i hii
    have hbound : a + (i + 1) < a + b + 1 := by omega
    rw [dite_eq_left hbound, dite_eq_left hii]
    have peq : (⟨a + (i + 1), hbound⟩ : Fin (a + b + 1)) = ⟨a + 1 + i, by omega⟩ := by
      apply Fin.ext
      change a + (i + 1) = a + 1 + i
      omega
    rw [peq]
    by_cases hpk : IsPeakAt β ⟨i, hii⟩
    · have h1 : IsPeakAt (joinMax α β) ⟨a + 1 + i, by omega⟩ := key.mpr hpk
      simp only [h1, hpk, ite_true]
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨a + 1 + i, by omega⟩ :=
        fun h => hpk (key.mp h)
      simp only [h1, hpk, ite_false]
  have e3 : (if h : a + 0 < a + b + 1 then
      (if IsPeakAt (joinMax α β) ⟨a + 0, h⟩ then (1 : ℕ) else 0) else 0) =
      (if a = 0 ∨ b = 0 then 0 else 1) := by
    have hbound : a + 0 < a + b + 1 := by omega
    rw [dite_eq_left hbound]
    have key := isPeakAt_joinMax_mid α β
    by_cases h0 : a = 0 ∨ b = 0
    · have h1 : ¬ IsPeakAt (joinMax α β) ⟨a + 0, hbound⟩ := fun h => (key.mp h) h0
      simp only [h1, ite_false, h0, ite_true]
    · have h1 : IsPeakAt (joinMax α β) ⟨a + 0, hbound⟩ := key.mpr h0
      simp only [h1, ite_true, h0, ite_false]
  omega

-- N8
private theorem card_filter_add_eq_sum_antidiagonal {X Y : Type*} (s : Finset X) (t : Finset Y)
    (f : X → ℕ) (g : Y → ℕ) (k : ℕ) :
    ((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)).card =
    ∑ q ∈ Finset.HasAntidiagonal.antidiagonal k,
      (s.filter (fun x => f x = q.1)).card * (t.filter (fun y => g y = q.2)).card := by
  have hmaps : Set.MapsTo (fun p : X × Y => (f p.1, g p.2))
      (((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)) : Set (X × Y))
      (Finset.HasAntidiagonal.antidiagonal k) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hp.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro q hq
  have hmem : q.1 + q.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  have hfib : Finset.filter (fun p : X × Y => (f p.1, g p.2) = q)
        ((s ×ˢ t).filter (fun p => f p.1 + g p.2 = k)) =
      (s.filter (fun x => f x = q.1)) ×ˢ (t.filter (fun y => g y = q.2)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hs, ht⟩, -⟩, hpair⟩
      have h1 : f p.1 = q.1 := congrArg Prod.fst hpair
      have h2 : g p.2 = q.2 := congrArg Prod.snd hpair
      exact ⟨⟨hs, h1⟩, ht, h2⟩
    · rintro ⟨⟨hs, h1⟩, ht, h2⟩
      refine ⟨⟨⟨hs, ht⟩, ?_⟩, ?_⟩
      · omega
      · exact Prod.ext h1 h2
  rw [hfib, Finset.card_product]

-- N5
private theorem joinMax_lt_of_avoids_aux {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {i l : Fin (a + b + 1)} (hi : i.val < a) (hl : a < l.val) : σ i < σ l := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  set last : Fin (a + b + 1) := Fin.last (a + b) with hlast
  have hsymm : σ.symm last = pos := Fin.ext hmax
  have htop : σ pos = last := by rw [← hsymm, Equiv.apply_symm_apply]
  have hne_i : σ i ≠ last := by
    intro hcon
    have hi2 : i = pos := σ.injective (by rw [hcon, htop])
    have hv : i.val = a := congrArg Fin.val hi2
    omega
  have hne_i' : σ i ≠ Fin.last (a + b) := by rwa [hlast] at hne_i
  have hi_lt : σ i < σ pos := by
    rw [htop, hlast]
    exact Fin.lt_last_iff_ne_last.mpr hne_i'
  have o1 : i < pos := by
    rw [hpos]
    exact Fin.lt_def.mpr hi
  have o2 : pos < l := by
    rw [hpos]
    exact Fin.lt_def.mpr hl
  have hnot := hAv i pos l o1 o2
  have hle : σ i ≤ σ l := le_of_not_gt (fun hcon => hnot ⟨hcon, hi_lt⟩)
  have hne : σ i ≠ σ l := by
    intro hcon
    have h2 : i = l := σ.injective hcon
    have hv : i.val = l.val := congrArg Fin.val h2
    omega
  exact lt_of_le_of_ne hle hne

private theorem joinMax_val_lt_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {i : Fin (a + b + 1)} (hi : i.val < a) : (σ i).val < a := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  set last : Fin (a + b + 1) := Fin.last (a + b) with hlast
  have hposv : pos.val = a := by rw [hpos]
  have hlastv : last.val = a + b := by
    rw [hlast]
    exact Fin.val_last _
  have hsymm : σ.symm last = pos := Fin.ext hmax
  have htop : σ pos = last := by rw [← hsymm, Equiv.apply_symm_apply]
  have hne_last : ∀ x : Fin (a + b + 1), x.val ≠ a → σ x ≠ last := by
    intro x hx hcon
    have hx2 : x = pos := σ.injective (by rw [hcon, htop])
    have hv : x.val = a := congrArg Fin.val hx2
    exact hx hv
  have hlt_top : (σ i).val < a + b := by
    have h := (σ i).isLt
    have hne : (σ i).val ≠ a + b := by
      intro hcon
      apply hne_last i (by omega)
      apply Fin.ext
      rw [hlastv]
      exact hcon
    omega
  have hs : (Finset.Ioi pos).card = b := by
    have h : (Finset.Ioi pos).card = (a + b + 1) - 1 - pos.val := Fin.card_Ioi pos
    omega
  have ht : (Finset.Ioo (σ i) last).card = last.val - (σ i).val - 1 :=
    Fin.card_Ioo (σ i) last
  have hmaps : Set.MapsTo σ (↑(Finset.Ioi pos)) (↑(Finset.Ioo (σ i) last)) := by
    intro l hl
    rw [Finset.mem_coe, Finset.mem_Ioi] at hl
    rw [Finset.mem_coe, Finset.mem_Ioo]
    have hlv : a < l.val := by
      have h := Fin.lt_def.mp hl
      omega
    have h1 : σ i < σ l := joinMax_lt_of_avoids_aux σ hAv hmax hi hlv
    have hne_l : σ l ≠ last := hne_last l (by omega)
    have h2 : σ l < last := by
      rw [hlast]
      apply Fin.lt_last_iff_ne_last.mpr
      rwa [hlast] at hne_l
    exact ⟨h1, h2⟩
  have hinj : Set.InjOn σ (↑(Finset.Ioi pos)) := fun _ _ _ _ h => σ.injective h
  have hle := Finset.card_le_card_of_injOn σ hmaps hinj
  omega

private theorem joinMax_le_of_avoids {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    {l : Fin (a + b + 1)} (hl : a < l.val) : a ≤ (σ l).val := by
  set pos : Fin (a + b + 1) := ⟨a, by omega⟩ with hpos
  have hposv : pos.val = a := by rw [hpos]
  have hs : (Finset.Iio pos).card = a := by
    have h : (Finset.Iio pos).card = pos.val := Fin.card_Iio pos
    omega
  have ht : (Finset.Iio (σ l)).card = (σ l).val := Fin.card_Iio (σ l)
  have hmaps : Set.MapsTo σ (↑(Finset.Iio pos)) (↑(Finset.Iio (σ l))) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_Iio] at hi
    rw [Finset.mem_coe, Finset.mem_Iio]
    have hiv : i.val < a := by
      have h := Fin.lt_def.mp hi
      omega
    exact joinMax_lt_of_avoids_aux σ hAv hmax hiv hl
  have hinj : Set.InjOn σ (↑(Finset.Iio pos)) := fun _ _ _ _ h => σ.injective h
  have hle := Finset.card_le_card_of_injOn σ hmaps hinj
  omega

-- N6
private noncomputable def leftPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    Equiv.Perm (Fin a) :=
  Equiv.ofBijective (fun j : Fin a =>
    (⟨(σ ⟨j.val, by have hj := j.isLt; omega⟩).val,
      joinMax_val_lt_of_avoids σ hAv hmax j.isLt⟩ : Fin a))
    (Finite.injective_iff_bijective.mp (by
      intro j1 j2 h12
      have hcon := congrArg Fin.val h12
      have hv : (σ ⟨j1.val, by have hj := j1.isLt; omega⟩).val =
          (σ ⟨j2.val, by have hj := j2.isLt; omega⟩).val := hcon
      have hpos : (⟨j1.val, by have hj := j1.isLt; omega⟩ : Fin (a + b + 1)) =
          ⟨j2.val, by have hj := j2.isLt; omega⟩ :=
        σ.injective (Fin.ext hv)
      have hcon2 := congrArg Fin.val hpos
      have hv2 : j1.val = j2.val := hcon2
      exact Fin.ext hv2))

private theorem leftPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin a) :
    (leftPerm σ hAv hmax j).val = (σ ⟨j.val, by have hj := j.isLt; omega⟩).val := by
  have h : leftPerm σ hAv hmax j =
      (⟨(σ ⟨j.val, by have hj := j.isLt; omega⟩).val,
        joinMax_val_lt_of_avoids σ hAv hmax j.isLt⟩ : Fin a) := by
    simp only [leftPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

private theorem rightPerm_bound {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a)
    (j : Fin b) (p : Fin (a + b + 1)) (hp : p.val = a + 1 + j.val) :
    (σ p).val - a < b := by
  have hlt := (σ p).isLt
  have hge : a ≤ (σ p).val :=
    joinMax_le_of_avoids (l := p) σ hAv hmax (by omega)
  have hne : (σ p).val ≠ a + b := by
    intro hcon
    have hsymm : σ.symm (Fin.last (a + b)) = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
      Fin.ext hmax
    have htop : σ (⟨a, by omega⟩ : Fin (a + b + 1)) = Fin.last (a + b) := by
      have h := Equiv.apply_symm_apply σ (Fin.last (a + b))
      rwa [hsymm] at h
    have hpeq : p = (⟨a, by omega⟩ : Fin (a + b + 1)) := by
      apply σ.injective
      rw [htop]
      apply Fin.ext
      rw [Fin.val_last]
      exact hcon
    have hv : p.val = a := congrArg Fin.val hpeq
    omega
  omega

private noncomputable def rightPerm {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    Equiv.Perm (Fin b) :=
  Equiv.ofBijective (fun j : Fin b =>
    (⟨(σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a,
      rightPerm_bound σ hAv hmax j ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩
        rfl⟩ : Fin b))
    (Finite.injective_iff_bijective.mp (by
      intro j1 j2 h12
      have hcon := congrArg Fin.val h12
      set p1 : Fin (a + b + 1) := ⟨a + 1 + j1.val, by have hj := j1.isLt; omega⟩ with hp1def
      set p2 : Fin (a + b + 1) := ⟨a + 1 + j2.val, by have hj := j2.isLt; omega⟩ with hp2def
      have hp1v : p1.val = a + 1 + j1.val := rfl
      have hp2v : p2.val = a + 1 + j2.val := rfl
      have hv : (σ p1).val - a = (σ p2).val - a := hcon
      have hg1 : a ≤ (σ p1).val :=
        joinMax_le_of_avoids (l := p1) σ hAv hmax (by omega)
      have hg2 : a ≤ (σ p2).val :=
        joinMax_le_of_avoids (l := p2) σ hAv hmax (by omega)
      have hv' : (σ p1).val = (σ p2).val := by omega
      have hpos : p1 = p2 := σ.injective (Fin.ext hv')
      have hcon2 := congrArg Fin.val hpos
      have hv2 : j1.val = j2.val := by omega
      exact Fin.ext hv2))

private theorem rightPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin b) :
    (rightPerm σ hAv hmax j).val =
      (σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a := by
  have h : rightPerm σ hAv hmax j =
      (⟨(σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a,
        rightPerm_bound σ hAv hmax j ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩
          rfl⟩ : Fin b) := by
    simp only [rightPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

private theorem exists_joinMax_eq {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    ∃ α β, joinMax α β = σ := by
  refine ⟨leftPerm σ hAv hmax, rightPerm σ hAv hmax, ?_⟩
  apply Equiv.ext
  intro p
  apply Fin.ext
  by_cases hlt : p.val < a
  · have e1 := joinMax_apply_lt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
      (i := p) hlt
    rw [e1]
    have e2 := leftPerm_val σ hAv hmax ⟨p.val, hlt⟩
    rw [e2]
  · by_cases heq : p.val = a
    · have e1 := joinMax_val_of_eq (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (p := p) heq
      rw [e1]
      have hsymm : σ.symm (Fin.last (a + b)) = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
        Fin.ext hmax
      have htop : σ (⟨a, by omega⟩ : Fin (a + b + 1)) = Fin.last (a + b) := by
        have h := Equiv.apply_symm_apply σ (Fin.last (a + b))
        rwa [hsymm] at h
      have hp : p = ⟨a, by omega⟩ := Fin.ext heq
      rw [hp, htop, Fin.val_last]
    · have hgt : a < p.val := by omega
      have e1 := joinMax_apply_gt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (i := p) hgt
      rw [e1]
      have e2 := rightPerm_val σ hAv hmax
        ⟨p.val - a - 1, by have hp := p.isLt; omega⟩
      rw [e2]
      have hpp : (⟨a + 1 + (⟨p.val - a - 1, by have hp := p.isLt; omega⟩ : Fin b).val,
          by have hp := p.isLt; omega⟩ : Fin (a + b + 1)) = p := by
        apply Fin.ext
        change a + 1 + (p.val - a - 1) = p.val
        omega
      rw [hpp]
      have hge := joinMax_le_of_avoids (l := p) σ hAv hmax hgt
      omega

-- N7
private theorem card_fiber_joinMax {a b n k : ℕ} (hab : a + b = n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
      ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = a))).card =
    (((Finset.univ.filter (fun α : Equiv.Perm (Fin a) => Avoids231 α)) ×ˢ
      (Finset.univ.filter (fun β : Equiv.Perm (Fin b) => Avoids231 β))).filter
      (fun p =>
        peakCount p.1 + peakCount p.2 + (if a = 0 ∨ b = 0 then 0 else 1) = k)).card := by
  subst hab
  symm
  refine Finset.card_bij (fun (p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) _ =>
    joinMax p.1 p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hα, hβ⟩, hpk⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (avoids231_joinMax_iff p.1 p.2).mpr ⟨hα, hβ⟩
    · rw [peakCount_joinMax]
      exact hpk
    · have h := joinMax_symm_last p.1 p.2
      have hv : ((joinMax p.1 p.2).symm (Fin.last (a + b))).val = a :=
        congrArg Fin.val h
      exact hv
  · intro p1 hp1 p2 hp2 heq
    have heq' : joinMax p1.1 p1.2 = joinMax p2.1 p2.2 := heq
    have h := joinMax_inj heq'
    exact Prod.ext h.1 h.2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨⟨hAv, hpk⟩, hmax⟩ := hσ
    obtain ⟨α, β, rfl⟩ := exists_joinMax_eq σ hAv hmax
    have hAB := (avoids231_joinMax_iff α β).mp hAv
    refine ⟨(α, β), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    refine ⟨hAB, ?_⟩
    rw [peakCount_joinMax α β] at hpk
    exact hpk
-- N10
private theorem peakV_zero (x : ℕ) : peakV 0 x = 0 := by
  unfold peakV
  simp

private theorem peakV_succ_eq (n p : ℕ) :
    peakV (n + 1) p = 2 ^ (n + 1 - p - 1) * Nat.choose n p := by
  unfold peakV
  have h1 : n + 1 ≠ 0 := by omega
  simp only [h1, ite_false, Nat.add_sub_cancel]

private theorem peakV_succ_add (n p : ℕ) :
    peakV (n + 1) (p + 1) = 2 * peakV n (p + 1) + peakV n p := by
  by_cases hn : n = 0
  · subst hn
    rw [peakV_succ_eq 0 (p + 1)]
    have hC : Nat.choose 0 (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hC, mul_zero, peakV_zero (p + 1), peakV_zero p, mul_zero, add_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [peakV_succ_eq (m + 1) (p + 1), peakV_succ_eq m (p + 1), peakV_succ_eq m p]
    have e1 : m + 1 + 1 - (p + 1) - 1 = m - p := by omega
    have e2 : m + 1 - (p + 1) - 1 = m - p - 1 := by omega
    have e3 : m + 1 - p - 1 = m - p := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ' m p, mul_add]
    by_cases hpm : p + 1 ≤ m
    · have hpow : (2 : ℕ) ^ (m - p) = 2 * 2 ^ (m - p - 1) := by
        obtain ⟨t, ht⟩ : ∃ t, m - p = t + 1 := ⟨m - p - 1, by omega⟩
        rw [ht, pow_succ, Nat.add_sub_cancel]
        ring
      rw [hpow]
      ring
    · have hC0 : Nat.choose m (p + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hC0]
      ring

private theorem peakV_succ_zero (n : ℕ) :
    peakV (n + 1) 0 = 2 * peakV n 0 + (if n = 0 then 1 else 0) := by
  by_cases hn : n = 0
  · subst hn
    rw [peakV_succ_eq 0 0, show (0 : ℕ) + 1 - 0 - 1 = 0 by omega,
      pow_zero, Nat.choose_zero_right, one_mul, peakV_zero 0]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [peakV_succ_eq (m + 1) 0, peakV_succ_eq m 0]
    have e1 : m + 1 + 1 - 0 - 1 = m + 1 := by omega
    have e2 : m + 1 - 0 - 1 = m := by omega
    have hn1 : m + 1 ≠ 0 := by omega
    rw [e1, e2]
    simp only [hn1, ite_false, Nat.choose_zero_right, mul_one, add_zero]
    rw [pow_succ]
    ring

-- N11
private theorem peakU_eq : peakU = PowerSeries.X * (1 + peakU + peakU) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul]
      unfold peakU
      rw [PowerSeries.coeff_mk]
      simp
  | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, map_add, map_add, PowerSeries.coeff_one]
      unfold peakU
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      by_cases hm : m = 0
      · subst hm
        simp
      · have hm1 : m + 1 ≠ 0 := by omega
        have hpow : (2 : ℕ) ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
          obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ]
          ring
        simp only [hm1, hm, ite_false, Nat.add_sub_cancel, zero_add]
        exact hpow

private theorem coeff_peakU_succ (n : ℕ) :
    PowerSeries.coeff (n + 1) peakU = 2 ^ n := by
  unfold peakU
  rw [PowerSeries.coeff_mk]
  have hn1 : n + 1 ≠ 0 := by omega
  have e2 : n + 1 - 1 = n := by omega
  simp only [hn1, ite_false]
  rw [e2]

private theorem coeff_peakU_pow (n p : ℕ) :
    PowerSeries.coeff n (peakU ^ (p + 1)) = peakV n p := by
  induction n generalizing p with
  | zero =>
      have h0 : PowerSeries.coeff 0 peakU = 0 := by
        unfold peakU
        rw [PowerSeries.coeff_mk]
        simp
      have hc : PowerSeries.constantCoeff peakU = 0 := by
        rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
      rw [peakV_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hc]
      exact zero_pow (by omega)
  | succ n ih =>
      cases p with
      | zero =>
          rw [pow_one, coeff_peakU_succ n, peakV_succ_eq n 0]
          have e : n + 1 - 0 - 1 = n := by omega
          rw [e, Nat.choose_zero_right, mul_one]
      | succ q =>
          have h1 : ∀ v : PowerSeries ℕ,
              v * peakU = v * (PowerSeries.X * (1 + peakU + peakU)) := by
            intro v
            conv_lhs => rw [peakU_eq]
          rw [pow_succ peakU (q + 1), h1]
          have hexpand : peakU ^ (q + 1) * (PowerSeries.X * (1 + peakU + peakU)) =
              PowerSeries.X * peakU ^ (q + 1) + PowerSeries.X * peakU ^ (q + 1 + 1) +
              PowerSeries.X * peakU ^ (q + 1 + 1) := by
            rw [pow_succ peakU (q + 1)]
            ring
          rw [hexpand]
          simp only [map_add, PowerSeries.coeff_succ_X_mul, ih q, ih (q + 1)]
          rw [peakV_succ_add n q]
          ring

private theorem sum_antidiagonal_peakV_mul (n a b : ℕ) :
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, peakV q.1 a * peakV q.2 b) =
    peakV n (a + b + 1) := by
  have h1 : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      peakV q.1 a * peakV q.2 b =
      PowerSeries.coeff q.1 (peakU ^ (a + 1)) *
        PowerSeries.coeff q.2 (peakU ^ (b + 1)) := by
    intro q _
    rw [coeff_peakU_pow, coeff_peakU_pow]
  have hsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, peakV q.1 a * peakV q.2 b) =
      (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff q.1 (peakU ^ (a + 1)) *
          PowerSeries.coeff q.2 (peakU ^ (b + 1))) :=
    Finset.sum_congr rfl h1
  rw [hsum, ← PowerSeries.coeff_mul, ← pow_add]
  have hexp : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
  rw [hexp, coeff_peakU_pow]

-- N12
private theorem sum_peakV_catalan_conv (n k' : ℕ) :
    (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
      (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
    peakV n (2 * k' + 1) * catalan (k' + 1) := by
  have hinner : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k',
      (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
      (catalan p.1 * catalan p.2) * peakV n (2 * k' + 1) := by
    intro p hp
    have hmem : p.1 + p.2 = k' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hstep : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
          (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
        (catalan p.1 * catalan p.2) *
          (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
            peakV q.1 (2 * p.1) * peakV q.2 (2 * p.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hV : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        peakV q.1 (2 * p.1) * peakV q.2 (2 * p.2)) = peakV n (2 * k' + 1) := by
      have h := sum_antidiagonal_peakV_mul n (2 * p.1) (2 * p.2)
      have hexp : 2 * p.1 + 2 * p.2 + 1 = 2 * k' + 1 := by omega
      rwa [hexp] at h
    rw [hstep, hV]
  have hsum : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
        ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) =
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k',
        (catalan p.1 * catalan p.2) * peakV n (2 * k' + 1)) :=
    Finset.sum_congr rfl hinner
  have hcat : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k', catalan p.1 * catalan p.2) =
      catalan (k' + 1) := (catalan_succ' k').symm
  rw [Finset.sum_comm, hsum, ← Finset.sum_mul, hcat]
  ring

-- N9
private theorem sum_range_fiber_eq_sum_antidiagonal (n : ℕ) (F : ℕ → ℕ) :
    (∑ b ∈ Finset.range n.succ, F b) =
    ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, F q.1 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem avoidCount_succ (n k : ℕ) :
    avoidCount (n + 1) k = peakRec avoidCount n k := by
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin (n + 1)) => (σ.symm (Fin.last n)).val)
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)) : Set (Equiv.Perm (Fin (n + 1))))
      (Finset.range n.succ) := by
    intro σ _
    apply Finset.mem_coe.mpr
    exact Finset.mem_range.mpr (σ.symm (Fin.last n)).isLt
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hav : ∀ (m j : ℕ),
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j)).card = avoidCount m j := by
    intro m j
    have hfl : (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j) =
        Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ ∧ peakCount σ = j) := by
      rw [Finset.filter_filter]
    rw [hfl]
    rfl
  have hstep : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)).filter
        (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
      (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
        else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) := by
    intro q hq
    have hmem : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    have hN7 := card_fiber_joinMax (a := q.1) (b := q.2) (n := n) (k := k) hmem
    have hbridge : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          Avoids231 σ ∧ peakCount σ = k)).filter
          (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = q.1))).card := by
      apply congrArg Finset.card
      rw [Finset.filter_filter]
    rw [hbridge, hN7]
    by_cases he : q.1 = 0 ∨ q.2 = 0
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          peakConv avoidCount q.1 q.2 k := ite_eq_left he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 0 := ite_eq_left he
      have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k)) := by
        apply Finset.filter_congr
        intro p _
        simp only [hoff, add_zero]
      rw [hfc]
      have hN8 := card_filter_add_eq_sum_antidiagonal
        (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
        (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
        peakCount peakCount k
      rw [hN8]
      unfold peakConv
      apply Finset.sum_congr rfl
      intro r hr
      rw [hav q.1 r.1, hav q.2 r.2]
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1)) :=
        ite_eq_right he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 1 := ite_eq_right he
      by_cases hk : k = 0
      · subst hk
        have hempty : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = 0)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p _
          omega
        rw [hempty, Finset.card_empty]
        exact (ite_eq_left rfl).symm
      · have hkif : (if k = 0 then (0:ℕ) else peakConv avoidCount q.1 q.2 (k - 1)) =
            peakConv avoidCount q.1 q.2 (k - 1) := ite_eq_right hk
        rw [hkif]
        have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k - 1)) := by
          apply Finset.filter_congr
          intro p _
          simp only [hoff]
          constructor <;> intro h <;> omega
        rw [hfc]
        have hN8 := card_filter_add_eq_sum_antidiagonal
          (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
          (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
          peakCount peakCount (k - 1)
        rw [hN8]
        unfold peakConv
        apply Finset.sum_congr rfl
        intro r hr
        rw [hav q.1 r.1, hav q.2 r.2]
  conv_lhs => unfold avoidCount
  rw [hfib, sum_range_fiber_eq_sum_antidiagonal]
  unfold peakRec
  apply Finset.sum_congr rfl
  intro q hq
  exact hstep q hq

-- N13
private theorem peakT_succ (n k : ℕ) : peakT (n + 1) k = peakRec peakT n k := by
  have hT0 : ∀ j : ℕ, peakT 0 j = (if j = 0 then 1 else 0) := by
    intro j
    unfold peakT
    by_cases hj : j = 0
    · subst hj
      simp
    · have hC : Nat.choose (0 - 1) (2 * j) = 0 := by
        have h1 : (0:ℕ) - 1 = 0 := by omega
        rw [h1]
        apply Nat.choose_eq_zero_of_lt
        omega
      rw [hC]
      simp only [mul_zero, zero_mul, hj, ite_false]
  have hTV : ∀ m j : ℕ, m ≠ 0 → peakT m j = peakV m (2 * j) * catalan j := by
    intro m j hm
    unfold peakT peakV
    simp only [hm, ite_false]
  have hV0 : ∀ x : ℕ, peakV 0 x = 0 := by
    intro x
    unfold peakV
    simp only [ite_true]
  have edgeConvL : ∀ b k : ℕ, peakConv peakT 0 b k = peakT b k := by
    intro b k
    unfold peakConv
    have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        peakT 0 p.1 * peakT b p.2 = (if p = (0, k) then peakT b k else 0) := by
      intro p hp
      have hmem : p.1 + p.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases he : p = (0, k)
      · simp only [he, ite_true]
        have e0 : peakT 0 (0, k).1 = 1 := by
          rw [hT0]
          have c0 : (0, k).1 = 0 := rfl
          rw [c0]
          simp only [ite_true]
        have e1 : peakT b (0, k).2 = peakT b k := rfl
        rw [e0, e1, one_mul]
      · have h1 : p.1 ≠ 0 := by
          intro h1
          apply he
          have h2 : p.2 = k := by omega
          exact Prod.ext h1 h2
        simp only [he, ite_false]
        have e0 : peakT 0 p.1 = 0 := by
          simp only [hT0, h1, ite_false]
        rw [e0, zero_mul]
    have h2 : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        peakT 0 p.1 * peakT b p.2) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        (if p = (0, k) then peakT b k else 0) :=
      Finset.sum_congr rfl h1
    rw [h2]
    have hmem' : (0, k) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (0:ℕ) + k = k; omega)
    rw [Finset.sum_ite_eq' _ (0, k) (fun _ => peakT b k), ite_eq_left hmem']
  have edgeConvR : ∀ a k : ℕ, peakConv peakT a 0 k = peakT a k := by
    intro a k
    unfold peakConv
    have h1 : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        peakT a p.1 * peakT 0 p.2 = (if p = (k, 0) then peakT a k else 0) := by
      intro p hp
      have hmem : p.1 + p.2 = k :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases he : p = (k, 0)
      · simp only [he, ite_true]
        have e0 : peakT 0 (k, 0).2 = 1 := by
          rw [hT0]
          have c0 : (k, 0).2 = 0 := rfl
          rw [c0]
          simp only [ite_true]
        have e1 : peakT a (k, 0).1 = peakT a k := rfl
        rw [e0, e1, mul_one]
      · have h2 : p.2 ≠ 0 := by
          intro h2
          apply he
          have h1 : p.1 = k := by omega
          exact Prod.ext h1 h2
        simp only [he, ite_false]
        have e0 : peakT 0 p.2 = 0 := by
          simp only [hT0, h2, ite_false]
        rw [e0, mul_zero]
    have h2 : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        peakT a p.1 * peakT 0 p.2) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        (if p = (k, 0) then peakT a k else 0) :=
      Finset.sum_congr rfl h1
    rw [h2]
    have hmem' : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change k + (0:ℕ) = k; omega)
    rw [Finset.sum_ite_eq' _ (k, 0) (fun _ => peakT a k), ite_eq_left hmem']
  by_cases hn0 : n = 0
  · subst hn0
    have hL : peakT 1 k = (if k = 0 then 1 else 0) := by
      unfold peakT
      by_cases hk : k = 0
      · subst hk
        simp
      · have hC : Nat.choose (1 - 1) (2 * k) = 0 := by
          have h1 : (1:ℕ) - 1 = 0 := by omega
          rw [h1]
          apply Nat.choose_eq_zero_of_lt
          omega
        rw [hC]
        simp only [mul_zero, zero_mul, hk, ite_false]
    have h00 : peakRec peakT 0 k = peakConv peakT 0 0 k := by
      unfold peakRec
      rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      have hc : ((0, 0).1 = 0 ∨ (0, 0).2 = 0) := Or.inl rfl
      exact ite_eq_left hc
    have hR : peakRec peakT 0 k = (if k = 0 then 1 else 0) := by
      rw [h00, edgeConvL 0 k]
      exact hT0 k
    rw [hL, hR]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hSEM : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k
          else (if k = 0 then 0 else peakConv peakT q.1 q.2 (k - 1))) =
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) +
        (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
          (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))) := by
      intro q hq
      by_cases he : q.1 = 0 ∨ q.2 = 0
      · have hM0 : (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
            (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))) = 0 := by
          by_cases hk : k = 0
          · simp only [hk, ite_true]
          · simp only [hk, ite_false]
            apply Finset.sum_eq_zero
            intro p _
            rcases he with h10 | h20
            · rw [h10]
              simp only [hV0, zero_mul]
            · rw [h20]
              simp only [hV0, zero_mul, mul_zero]
        simp only [he, ite_true]
        rw [hM0, add_zero]
      · have hmid : ¬(q.1 = 0 ∨ q.2 = 0) := he
        have hqpair := not_or.mp hmid
        have hAB : peakConv peakT q.1 q.2 (k - 1) =
            (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
            (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)) := by
          unfold peakConv
          apply Finset.sum_congr rfl
          intro p _
          rw [hTV q.1 p.1 hqpair.1, hTV q.2 p.2 hqpair.2]
        simp only [hmid, ite_false]
        rw [hAB, zero_add]
    have hEsplit : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) =
        (if q = (0, m + 1) then peakT (m + 1) k else 0) +
        (if q = (m + 1, 0) then peakT (m + 1) k else 0) := by
      intro q hq
      have hmem : q.1 + q.2 = m + 1 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      by_cases h10 : q = (0, m + 1)
      · by_cases h20 : q = (m + 1, 0)
        · have hcon2 : (0:ℕ) = m + 1 := congrArg Prod.fst (h10.symm.trans h20)
          omega
        · have hq1 : q.1 = 0 := congrArg Prod.fst h10
          have hq2 : q.2 = m + 1 := by omega
          have hc : q.1 = 0 ∨ q.2 = 0 := Or.inl hq1
          have eE : peakConv peakT q.1 q.2 k = peakT (m + 1) k := by
            rw [hq1, hq2]
            exact edgeConvL (m + 1) k
          simp only [hc, ite_true]
          rw [eE]
          have hneq : (0, m + 1) ≠ (m + 1, 0) := by
            intro hcon
            have hfst : (0:ℕ) = m + 1 := congrArg Prod.fst hcon
            omega
          simp only [h10, ite_true, hneq, ite_false, add_zero]
      · by_cases h20 : q = (m + 1, 0)
        · have hq2 : q.2 = 0 := congrArg Prod.snd h20
          have hq1 : q.1 = m + 1 := by omega
          have hc : q.1 = 0 ∨ q.2 = 0 := Or.inr hq2
          have eE : peakConv peakT q.1 q.2 k = peakT (m + 1) k := by
            rw [hq1, hq2]
            exact edgeConvR (m + 1) k
          simp only [hc, ite_true]
          rw [eE]
          have hneq : (m + 1, 0) ≠ (0, m + 1) := by
            intro hcon
            have hfst : m + 1 = (0:ℕ) := congrArg Prod.fst hcon
            omega
          simp only [h20, hneq, ite_false, ite_true, zero_add]
        · have hne : ¬(q.1 = 0 ∨ q.2 = 0) := by
            rintro (h1 | h2)
            · apply h10
              have h2' : q.2 = m + 1 := by omega
              exact Prod.ext h1 h2'
            · apply h20
              have h1' : q.1 = m + 1 := by omega
              exact Prod.ext h1' h2
          simp only [hne, ite_false, h10, ite_false, h20, ite_false, add_zero]
    have hEsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0)) =
        peakT (m + 1) k + peakT (m + 1) k := by
      have h1 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
          (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0)) =
          ∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
          ((if q = (0, m + 1) then peakT (m + 1) k else 0) +
          (if q = (m + 1, 0) then peakT (m + 1) k else 0)) :=
        Finset.sum_congr rfl hEsplit
      rw [h1, Finset.sum_add_distrib]
      have hmem1 : (0, m + 1) ∈ Finset.HasAntidiagonal.antidiagonal (m + 1) :=
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (0:ℕ) + (m + 1) = m + 1; omega)
      have s1 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
          (if q = (0, m + 1) then peakT (m + 1) k else 0)) = peakT (m + 1) k := by
        rw [Finset.sum_ite_eq' _ (0, m + 1) (fun _ => peakT (m + 1) k), ite_eq_left hmem1]
      have hmem2 : (m + 1, 0) ∈ Finset.HasAntidiagonal.antidiagonal (m + 1) :=
        Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change (m + 1) + (0:ℕ) = m + 1; omega)
      have s2 : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
          (if q = (m + 1, 0) then peakT (m + 1) k else 0)) = peakT (m + 1) k := by
        rw [Finset.sum_ite_eq' _ (m + 1, 0) (fun _ => peakT (m + 1) k), ite_eq_left hmem2]
      rw [s1, s2]
    have hMsum : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
          (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2)))) =
        (if k = 0 then 0 else peakV (m + 1) (2 * (k - 1) + 1) * catalan ((k - 1) + 1)) := by
      by_cases hk : k = 0
      · simp only [hk, ite_true, Finset.sum_const_zero]
      · simp only [hk, ite_false]
        rw [sum_peakV_catalan_conv]
    have hSE : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        (if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k
          else (if k = 0 then 0 else peakConv peakT q.1 q.2 (k - 1)))) =
        (∑ q ∈ Finset.HasAntidiagonal.antidiagonal (m + 1),
        ((if q.1 = 0 ∨ q.2 = 0 then peakConv peakT q.1 q.2 k else 0) +
        (if k = 0 then 0 else (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k - 1),
          (peakV q.1 (2 * p.1) * catalan p.1) * (peakV q.2 (2 * p.2) * catalan p.2))))) :=
      Finset.sum_congr rfl hSEM
    unfold peakRec
    rw [hSE, Finset.sum_add_distrib, hEsum, hMsum]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true, add_zero]
      rw [hTV (m + 1 + 1) 0 (by omega), hTV (m + 1) 0 (by omega)]
      simp only [catalan_zero, mul_one]
      have hN10 := peakV_succ_zero (m + 1)
      rw [hN10]
      have hm1 : ¬(m:ℕ) + 1 = 0 := by omega
      simp only [hm1, ite_false, add_zero]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj1 : ¬(j:ℕ) + 1 = 0 := by omega
      have hj2 : j + 1 - 1 = j := by omega
      rw [ite_eq_right hj1, hj2]
      rw [hTV (m + 1 + 1) (j + 1) (by omega), hTV (m + 1) (j + 1) (by omega)]
      have hidx : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [hidx]
      have hN10 := peakV_succ_add (m + 1) (2 * j + 1)
      rw [hN10]
      ring

-- N14
private theorem avoidCount_eq_peakT (n k : ℕ) : avoidCount n k = peakT n k := by
  revert k
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    by_cases hn : n = 0
    · subst hn
      have hA : ∀ σ : Equiv.Perm (Fin 0), Avoids231 σ := by
        intro σ i j l _ _ _
        exact Fin.elim0 i
      have hpc : ∀ σ : Equiv.Perm (Fin 0), peakCount σ = 0 := by
        intro σ
        unfold peakCount
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact Fin.elim0 x
      have hset : (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin 0) => Avoids231 σ ∧ peakCount σ = k)) =
          (if k = 0 then Finset.univ else ∅) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.mem_univ]
          rw [hpc σ]
          exact iff_true_intro ⟨hA σ, rfl⟩
        · have hk0 : peakCount σ ≠ k := by rw [hpc σ]; omega
          simp only [hk, ite_false, Finset.notMem_empty]
          exact iff_false_intro (fun h => hk0 h.2)
      have hcard : avoidCount 0 k = (if k = 0 then 1 else 0) := by
        unfold avoidCount
        rw [hset]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, Nat.factorial_zero]
        · simp only [hk, ite_false, Finset.card_empty]
      have hT : peakT 0 k = (if k = 0 then 1 else 0) := by
        unfold peakT
        by_cases hk : k = 0
        · subst hk
          simp
        · have hC : Nat.choose (0 - 1) (2 * k) = 0 := by
            have h1 : (0:ℕ) - 1 = 0 := by omega
            rw [h1]
            apply Nat.choose_eq_zero_of_lt
            omega
          rw [hC]
          simp only [mul_zero, zero_mul, hk, ite_false]
      rw [hcard, hT]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hEq : ∀ a : ℕ, a ≤ m → ∀ j : ℕ, avoidCount a j = peakT a j := by
        intro a ha j
        exact ih a (by omega) j
      rw [avoidCount_succ, peakT_succ]
      unfold peakRec peakConv
      apply Finset.sum_congr rfl
      intro q hq
      have hmem : q.1 + q.2 = m :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have ha1 : q.1 ≤ m := by omega
      have ha2 : q.2 ≤ m := by omega
      by_cases he : q.1 = 0 ∨ q.2 = 0
      · simp only [he, ite_true]
        apply Finset.sum_congr rfl
        intro p _
        rw [hEq q.1 ha1, hEq q.2 ha2]
      · simp only [he, ite_false]
        by_cases hk : k = 0
        · simp only [hk, ite_true]
        · simp only [hk, ite_false]
          apply Finset.sum_congr rfl
          intro p _
          rw [hEq q.1 ha1, hEq q.2 ha2]

end Peak231

-- N15
/--
**Peaks of 231-avoiding permutations.** Let $n \ge 1$ and $k$ be natural numbers. A permutation
$\sigma$ of $\{0, \dots, n-1\}$ avoids $231$ if there are no positions $i < j < l$ with
$\sigma(l) < \sigma(i) < \sigma(j)$, and $\sigma$ has a peak at a position $i$ with
$0 < i < n - 1$ if $\sigma(i-1) < \sigma(i)$ and $\sigma(i+1) < \sigma(i)$. The number of
231-avoiding permutations of $\{0, \dots, n-1\}$ with exactly $k$ peaks is
$2^{n-2k-1} \binom{n-1}{2k} \binom{2k}{k} / (k+1)$, computed in the natural numbers: the
exponent $n - 2k - 1$ is truncated at $0$ and the division rounds down.

Proves `Wanted` entry `card_permutations_avoiding_231_with_peak_count`.

Source: Lara Pudwell, Jacob Roth, and Teresa Wheeland, "Distributions of Statistics
over Pattern-Avoiding Permutations", Journal of Integer Sequences 22 (2019),
Article 19.2.6, Theorem `T:pk231`, line 228,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Pudwell/pudwell6.tex>.
-/
theorem card_permutations_avoiding_231_with_peak_count
    (n k : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * Nat.choose (2 * k) k /
        (k + 1) := by
  have _ : 1 ≤ n := hn
  have hCat : (k + 1) * catalan k = Nat.choose (2 * k) k := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have hRHS : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
      Nat.choose (2 * k) k / (k + 1) =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k := by
    have hC : Nat.choose (2 * k) k = (k + 1) * catalan k := hCat.symm
    conv_lhs => rw [hC]
    have hring : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
        ((k + 1) * catalan k) =
        (2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k) *
        (k + 1) := by ring
    rw [hring, Nat.mul_div_cancel _ (Nat.succ_pos k)]
  have hBridge : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      Peak231.avoidCount n k := rfl
  rw [hBridge, Peak231.avoidCount_eq_peakT]
  unfold Peak231.peakT
  exact hRHS.symm

end MetaMathlibExt
end
