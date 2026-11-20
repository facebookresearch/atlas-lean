/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Mathlib
import Code.Onsager.WalkCrossing
import Code.Onsager.UmlaufsatzStrip

namespace StatMech.Onsager.TopRow

open Finset
open Fin.NatCast
open StatMech.Onsager.BaseCase
open StatMech.Onsager.NoDoubleWind
open StatMech.Onsager.WalkCrossing

variable {n : ℕ} [NeZero n]








theorem top_out_ne_N (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    {M v : Fin n} (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hv : (pos d v).2 = (pos d M).2) :
    d v ≠ 1 := by
  intro hN
  have hy : (pos d (v + 1)).2 = (pos d v).2 + 1 := by
    rw [snd_step d hclosed v, hN]; simp [stepOf]
  have := hmax (v + 1)
  omega



theorem top_in_ne_S (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    {M v : Fin n} (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hv : (pos d v).2 = (pos d M).2) :
    d (v - 1) ≠ 3 := by
  intro hS
  have hpred := pos_pred d hclosed v
  rw [hS] at hpred
  have hstep : stepOf (3 : Fin 4) = (0, -1) := rfl
  rw [hstep] at hpred
  
  have hy : (pos d (v - 1)).2 = (pos d v).2 + 1 := by
    have := congrArg Prod.snd hpred
    simp only [Prod.snd_add] at this
    omega
  have := hmax (v - 1)
  omega











theorem forward_west_run (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (M : Fin n)
    (j : ℕ) (hj : ∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2) :
    pos d (M + (Nat.cast j : Fin n)) = ((pos d M).1 - (j : ℤ), (pos d M).2) := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hstepcast : (Nat.cast (k + 1) : Fin n) = (Nat.cast k : Fin n) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have hidx : M + (Nat.cast (k + 1) : Fin n) = (M + (Nat.cast k : Fin n)) + 1 := by
      rw [hstepcast, add_assoc]
    have ihk : pos d (M + (Nat.cast k : Fin n)) = ((pos d M).1 - (k : ℤ), (pos d M).2) :=
      ih (fun i hi => hj i (Nat.lt_succ_of_lt hi))
    have hdk : d (M + (Nat.cast k : Fin n)) = 2 := hj k (Nat.lt_succ_self k)
    rw [hidx, pos_succ d hclosed (M + (Nat.cast k : Fin n)), ihk, hdk]
    have hstep : stepOf (2 : Fin 4) = (-1, 0) := rfl
    rw [hstep]
    ext
    · simp; ring
    · simp















def SingleTopRun (d : Fin n → Fin 4) (M : Fin n) : Prop :=
  ∀ v : Fin n, (pos d v).2 = (pos d M).2 →
    ∃ j : ℕ, (∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2) ∧
      (pos d v).1 = (pos d M).1 - (j : ℤ)




theorem topRowContiguous_of_singleTopRun (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    {M : Fin n} (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
    (hrun : SingleTopRun d M) :
    StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
  refine ⟨M, hmax, ?_⟩
  intro a b ha hb x hax hxb
  
  obtain ⟨ja, hja, hxa⟩ := hrun a ha
  obtain ⟨jb, hjb, hxb'⟩ := hrun b hb
  
  set xM : ℤ := (pos d M).1 with hxM
  
  have hx_le_xM : x ≤ xM := le_trans hxb (by rw [hxb']; omega)
  set j : ℕ := (xM - x).toNat with hjdef
  have hjcast : (j : ℤ) = xM - x := by rw [hjdef]; omega
  
  have hj_le_ja : j ≤ ja := by
    have h1 : (j : ℤ) ≤ (ja : ℤ) := by rw [hjcast]; omega
    exact_mod_cast h1
  have hjprefix : ∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2 :=
    fun i hi => hja i (lt_of_lt_of_le hi hj_le_ja)
  
  refine ⟨M + (Nat.cast j : Fin n), ?_⟩
  rw [forward_west_run d hclosed M j hjprefix]
  ext
  · show (pos d M).1 - (j : ℤ) = x; rw [hjcast]; ring
  · rfl











theorem topRowContiguous_of_residue (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hres : ∀ M : Fin n, d (M - 1) = 1 → d M = 2 →
      (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) → SingleTopRun d M) :
    StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
  obtain ⟨M, hin, hout, hmax, _hright⟩ :=
    StatMech.Onsager.UmlaufsatzStrip.ymax_NW_corner d hclosed hreflexfree
  exact topRowContiguous_of_singleTopRun d hclosed hmax (hres M hin hout hmax)

end StatMech.Onsager.TopRow
