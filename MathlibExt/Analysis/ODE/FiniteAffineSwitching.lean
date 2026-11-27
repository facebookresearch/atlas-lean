/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.Duhamel
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite affine switching

For a bounded linear operator with forcing continuous on each
piece of a finite time partition, the Duhamel solutions patch
into the unique continuous piecewise-C1 trajectory through the
initial state, satisfying the integral equation across switch
boundaries. A two-level forcing fixture is worked out, and a
state reset at the switch is shown to solve the ODE on both open
pieces while failing continuity and the integral equation.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Analysis.ODE.FiniteAffineSwitching

/-- A continuous, piecewise-differentiable trajectory of `x' = A x + b` through `x₀` for the
partition `τ`: the switch times are strictly increasing, the trajectory starts at `x₀`, is
continuous on the whole horizon (no state reset at switch times), and solves the ODE at every
interior point of every piece. -/
def IsSwitchedTrajectory {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (A : E →L[ℝ] E) (b : ℝ → E) (τ : Fin (n + 1) → ℝ) (x₀ : E) (x : ℝ → E) : Prop :=
  StrictMono τ ∧ x (τ 0) = x₀ ∧ ContinuousOn x (Icc (τ 0) (τ (Fin.last n))) ∧
    ∀ k : Fin n, ∀ t ∈ Ioo (τ k.castSucc) (τ k.succ), HasDerivAt x (A (x t) + b t) t

open Filter Topology

-- Helpers for `switchedTrajectory_exists_unique` (not part of the pin).

private lemma val_castSucc {n : ℕ} (i : Fin n) : (i.castSucc).val = i.val := by
  obtain ⟨v, hv⟩ := i
  rfl

private lemma mk_castSucc_eq {n : ℕ} (k : Fin n) :
    (⟨k.val, by have h := k.isLt; omega⟩ : Fin (n + 1)) = k.castSucc := by
  obtain ⟨v, hv⟩ := k
  rfl

private lemma mk_succ_eq {n : ℕ} (k : Fin n) :
    (⟨k.val + 1, by have h := k.isLt; omega⟩ : Fin (n + 1)) = k.succ := by
  apply Fin.ext
  have hvs : (k.succ).val = k.val + 1 := Fin.val_succ _
  rw [hvs]

private lemma mk_val_eq {n : ℕ} (k : Fin n) : (⟨k.val, k.isLt⟩ : Fin n) = k := by
  obtain ⟨v, hv⟩ := k
  rfl

private lemma le_last' {n : ℕ} (i : Fin (n + 1)) : i ≤ Fin.last n := by
  have h1 : i.val ≤ n := by have h := i.isLt; omega
  have h2 : (Fin.last n).val = n := Fin.val_last _
  have h3 : i.val ≤ (Fin.last n).val := by omega
  exact Fin.le_iff_val_le_val.mpr h3

-- Constant extension of the piece forcing `g k` to a globally continuous function.
private noncomputable def extG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (τ : Fin (n + 1) → ℝ) (g : Fin n → ℝ → E) (k : Fin n) (t : ℝ) : E :=
  g k (min (max t (τ k.castSucc)) (τ k.succ))

private lemma continuous_extG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (k : Fin n) :
    Continuous (extG τ g k) := by
  have hle : τ k.castSucc ≤ τ k.succ := (hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
  have hclamp : Continuous fun t : ℝ => min (max t (τ k.castSucc)) (τ k.succ) :=
    (continuous_id.max continuous_const).min continuous_const
  have hmaps : Set.MapsTo (fun t : ℝ => min (max t (τ k.castSucc)) (τ k.succ)) Set.univ
      (Icc (τ k.castSucc) (τ k.succ)) := by
    intro t _
    show τ k.castSucc ≤ min (max t (τ k.castSucc)) (τ k.succ) ∧
      min (max t (τ k.castSucc)) (τ k.succ) ≤ τ k.succ
    constructor
    · simp only [le_min_iff, le_max_iff, le_refl, or_true, true_and]
      exact hle
    · simp only [min_le_iff, le_refl, or_true]
  exact continuousOn_univ.mp ((hg k).comp hclamp.continuousOn hmaps)

private lemma extG_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (τ : Fin (n + 1) → ℝ) (g : Fin n → ℝ → E) (k : Fin n)
    (t : ℝ) (ht : t ∈ Icc (τ k.castSucc) (τ k.succ)) : extG τ g k t = g k t := by
  show g k (min (max t (τ k.castSucc)) (τ k.succ)) = g k t
  congr 1
  simp only [max_eq_left ht.1, min_eq_left ht.2]

private lemma extG_eq_b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (τ : Fin (n + 1) → ℝ) (b : ℝ → E) (g : Fin n → ℝ → E)
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (k : Fin n)
    (s : ℝ) (hs : s ∈ Ioo (τ k.castSucc) (τ k.succ)) : extG τ g k s = b s := by
  rw [extG_eq τ g k s (Ioo_subset_Icc_self hs)]
  exact (hbg k hs).symm

-- The global Duhamel solution for piece `k` with initial value `v` at its left endpoint.
private noncomputable def pieceW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) : ℝ → E :=
  Classical.choose (MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
    A (extG τ g k) (τ k.castSucc) v (continuous_extG τ hτ g hg k))

private lemma pieceW_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) :
    (pieceW A τ hτ g hg k v) (τ k.castSucc) = v ∧
      (∀ t, pieceW A τ hτ g hg k v t = (NormedSpace.exp ((t - τ k.castSucc) • A)) v +
        ∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (extG τ g k s)) ∧
      (∀ t, HasDerivAt (pieceW A τ hτ g hg k v)
        (A (pieceW A τ hτ g hg k v t) + extG τ g k t) t) ∧
      ∀ y : ℝ → E, y (τ k.castSucc) = v →
        (∀ t, HasDerivAt y (A (y t) + extG τ g k t) t) → y = pieceW A τ hτ g hg k v :=
  Classical.choose_spec (MathlibExt.Analysis.ODE.DuhamelWanted.duhamel_variation_of_constants
    A (extG τ g k) (τ k.castSucc) v (continuous_extG τ hτ g hg k))

private lemma pieceW_init {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) : pieceW A τ hτ g hg k v (τ k.castSucc) = v :=
  (pieceW_spec A τ hτ g hg k v).1

private lemma pieceW_form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) (t : ℝ) :
    pieceW A τ hτ g hg k v t = (NormedSpace.exp ((t - τ k.castSucc) • A)) v +
      ∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (extG τ g k s) :=
  (pieceW_spec A τ hτ g hg k v).2.1 t

private lemma pieceW_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) (t : ℝ) :
    HasDerivAt (pieceW A τ hτ g hg k v)
      (A (pieceW A τ hτ g hg k v t) + extG τ g k t) t :=
  (pieceW_spec A τ hτ g hg k v).2.2.1 t

private lemma pieceW_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (k : Fin n) (v : E) : Continuous (pieceW A τ hτ g hg k v) :=
  continuous_iff_continuousAt.mpr fun t => (pieceW_deriv A τ hτ g hg k v t).continuousAt

-- States and solutions by recursion on the piece index.
private noncomputable def XW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    ℕ → E × (ℝ → E)
  | 0 => (x₀, fun _ => x₀)
  | m + 1 =>
      if h : m < n then
        let w := pieceW A τ hτ g hg ⟨m, h⟩ (XW A τ hτ g hg x₀ m).1
        (w (τ ⟨m + 1, by omega⟩), w)
      else XW A τ hτ g hg x₀ m

private lemma XW_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    XW A τ hτ g hg x₀ 0 = (x₀, fun _ => x₀) := rfl

private lemma XW_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (m : ℕ) (h : m < n) :
    XW A τ hτ g hg x₀ (m + 1) =
      let w := pieceW A τ hτ g hg ⟨m, h⟩ (XW A τ hτ g hg x₀ m).1
      (w (τ ⟨m + 1, by omega⟩), w) := by
  rw [XW, dite_eq_left_of_eq_true (eq_true h)]

-- State at switch time `j`.
private noncomputable def swXst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (j : Fin (n + 1)) : E :=
  (XW A τ hτ g hg x₀ j.val).1

-- Piece-`k` solution.
private noncomputable def swW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) : ℝ → E :=
  (XW A τ hτ g hg x₀ (k.val + 1)).2

private lemma swXst_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    swXst A τ hτ g hg x₀ 0 = x₀ := by
  have h0 : ((0 : Fin (n + 1)).val) = 0 := Fin.val_zero _
  show (XW A τ hτ g hg x₀ ((0 : Fin (n + 1)).val)).1 = x₀
  rw [h0, XW_zero]

private lemma swXst_castSucc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) :
    swXst A τ hτ g hg x₀ k.castSucc = (XW A τ hτ g hg x₀ k.val).1 := by
  show (XW A τ hτ g hg x₀ (k.castSucc).val).1 = _
  rw [val_castSucc]

private lemma swW_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) :
    swW A τ hτ g hg x₀ k =
      pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (swXst A τ hτ g hg x₀ k.castSucc) := by
  have hXW := XW_succ A τ hτ g hg x₀ k.val k.isLt
  have hcast : (XW A τ hτ g hg x₀ k.val).1 = swXst A τ hτ g hg x₀ k.castSucc :=
    (swXst_castSucc A τ hτ g hg x₀ k).symm
  show (XW A τ hτ g hg x₀ (k.val + 1)).2 =
    pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (swXst A τ hτ g hg x₀ k.castSucc)
  rw [hXW]
  show pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (XW A τ hτ g hg x₀ k.val).1 = _
  rw [hcast]

private lemma swW_init {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) :
    swW A τ hτ g hg x₀ k (τ k.castSucc) = swXst A τ hτ g hg x₀ k.castSucc := by
  rw [swW_eq, mk_val_eq k]
  exact pieceW_init A τ hτ g hg k _

private lemma swXst_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) :
    swXst A τ hτ g hg x₀ k.succ = swW A τ hτ g hg x₀ k (τ k.succ) := by
  have hXW := XW_succ A τ hτ g hg x₀ k.val k.isLt
  have hval : (k.succ).val = k.val + 1 := Fin.val_succ _
  have hcast : (XW A τ hτ g hg x₀ k.val).1 = swXst A τ hτ g hg x₀ k.castSucc :=
    (swXst_castSucc A τ hτ g hg x₀ k).symm
  show (XW A τ hτ g hg x₀ (k.succ).val).1 = swW A τ hτ g hg x₀ k (τ k.succ)
  rw [hval, hXW, swW_eq, hcast, ← mk_succ_eq k]

private lemma swW_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) : Continuous (swW A τ hτ g hg x₀ k) := by
  have hWk := (swW_eq A τ hτ g hg x₀ k).symm
  rw [← hWk]
  exact pieceW_cont A τ hτ g hg ⟨k.val, k.isLt⟩ _

-- The patched trajectory: piece solutions glued at the switch times.
private noncomputable def swX {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (t : ℝ) : E :=
  if h : ∃ k : Fin n, t ∈ Icc (τ k.castSucc) (τ k.succ) then swW A τ hτ g hg x₀ h.choose t
  else x₀

-- Agreement of piece solutions on overlaps.
private lemma swW_overlap_of_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (j k : Fin n) (hlt : j < k) (t : ℝ) (hj : t ∈ Icc (τ j.castSucc) (τ j.succ))
    (hk : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    swW A τ hτ g hg x₀ j t = swW A τ hτ g hg x₀ k t := by
  have hle : (j.succ : Fin (n + 1)) ≤ k.castSucc := by
    have h1 : (j.succ).val ≤ (k.castSucc).val := by
      have hv1 : (j.succ).val = j.val + 1 := Fin.val_succ _
      have hv2 : (k.castSucc).val = k.val := val_castSucc k
      have hlt' : j.val < k.val := Fin.lt_def.mp hlt
      omega
    exact Fin.le_iff_val_le_val.mpr h1
  have hτle : τ j.succ ≤ τ k.castSucc := hτ.monotone hle
  have htj : t = τ j.succ := le_antisymm hj.2 (hτle.trans hk.1)
  have htk : t = τ k.castSucc := le_antisymm (hj.2.trans hτle) hk.1
  have hidx : j.succ = k.castSucc := hτ.injective (htj.symm.trans htk)
  calc swW A τ hτ g hg x₀ j t = swW A τ hτ g hg x₀ j (τ j.succ) := by rw [htj]
    _ = swXst A τ hτ g hg x₀ j.succ := (swXst_succ A τ hτ g hg x₀ j).symm
    _ = swXst A τ hτ g hg x₀ k.castSucc := by rw [hidx]
    _ = swW A τ hτ g hg x₀ k (τ k.castSucc) := (swW_init A τ hτ g hg x₀ k).symm
    _ = swW A τ hτ g hg x₀ k t := by rw [htk]

private lemma swW_overlap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (j k : Fin n) (t : ℝ) (hj : t ∈ Icc (τ j.castSucc) (τ j.succ))
    (hk : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    swW A τ hτ g hg x₀ j t = swW A τ hτ g hg x₀ k t := by
  by_cases heq : j = k
  · subst heq
    rfl
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · exact swW_overlap_of_lt A τ hτ g hg x₀ j k hlt t hj hk
    · exact (swW_overlap_of_lt A τ hτ g hg x₀ k j hgt t hk hj).symm

private lemma swX_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) (t : ℝ) (ht : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    swX A τ hτ g hg x₀ t = swW A τ hτ g hg x₀ k t := by
  have hex : ∃ j : Fin n, t ∈ Icc (τ j.castSucc) (τ j.succ) := ⟨k, ht⟩
  have hunfold : swX A τ hτ g hg x₀ t =
      dite (∃ j : Fin n, t ∈ Icc (τ j.castSucc) (τ j.succ))
        (fun h => swW A τ hτ g hg x₀ h.choose t) (fun _ => x₀) := rfl
  rw [hunfold, dite_eq_left_of_eq_true (eq_true hex)]
  exact swW_overlap A τ hτ g hg x₀ hex.choose k t hex.choose_spec ht

private lemma swX_init {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    swX A τ hτ g hg x₀ (τ 0) = x₀ := by
  by_cases hex : ∃ k : Fin n, τ 0 ∈ Icc (τ k.castSucc) (τ k.succ)
  · obtain ⟨j, hj⟩ := hex
    have h0le : τ 0 ≤ τ j.castSucc := hτ.monotone (Fin.zero_le _)
    have heq : τ j.castSucc = τ 0 := le_antisymm hj.1 h0le
    have hidx : j.castSucc = 0 := hτ.injective heq
    have hxj : swX A τ hτ g hg x₀ (τ 0) = swW A τ hτ g hg x₀ j (τ 0) :=
      swX_eq A τ hτ g hg x₀ j (τ 0) hj
    rw [hxj]
    have hW : swW A τ hτ g hg x₀ j (τ 0) = swXst A τ hτ g hg x₀ j.castSucc := by
      have h := swW_init A τ hτ g hg x₀ j
      rwa [heq] at h
    rw [hW, hidx]
    exact swXst_zero A τ hτ g hg x₀
  · have hunfold : swX A τ hτ g hg x₀ (τ 0) =
        dite (∃ k : Fin n, τ 0 ∈ Icc (τ k.castSucc) (τ k.succ))
          (fun h => swW A τ hτ g hg x₀ h.choose (τ 0)) (fun _ => x₀) := rfl
    rw [hunfold, dite_eq_right_of_eq_false (eq_false hex)]

private lemma swX_cont_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) :
    ContinuousOn (swX A τ hτ g hg x₀) (Icc (τ k.castSucc) (τ k.succ)) := by
  have hWcont : Continuous (swW A τ hτ g hg x₀ k) := by
    have hW := swW_eq A τ hτ g hg x₀ k
    rw [hW]
    exact pieceW_cont A τ hτ g hg ⟨k.val, k.isLt⟩ _
  exact hWcont.continuousOn.congr (fun t ht => swX_eq A τ hτ g hg x₀ k t ht)

private lemma swX_derivWithin_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) (t : ℝ) (ht : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    HasDerivWithinAt (swX A τ hτ g hg x₀)
      (A (swX A τ hτ g hg x₀ t) + g k t) (Icc (τ k.castSucc) (τ k.succ)) t := by
  have heq : EqOn (swX A τ hτ g hg x₀) (swW A τ hτ g hg x₀ k)
      (Icc (τ k.castSucc) (τ k.succ)) := fun s hs => swX_eq A τ hτ g hg x₀ k s hs
  have hW := pieceW_deriv A τ hτ g hg ⟨k.val, k.isLt⟩
    (swXst A τ hτ g hg x₀ k.castSucc) t
  have hWk : pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (swXst A τ hτ g hg x₀ k.castSucc)
      = swW A τ hτ g hg x₀ k := (swW_eq A τ hτ g hg x₀ k).symm
  rw [hWk] at hW
  have hWwithin := hW.hasDerivWithinAt (s := Icc (τ k.castSucc) (τ k.succ))
  have hev : (swX A τ hτ g hg x₀) =ᶠ[𝓝[Icc (τ k.castSucc) (τ k.succ)] t]
      (swW A τ hτ g hg x₀ k) := heq.eventuallyEq_of_mem self_mem_nhdsWithin
  have hcongr := hWwithin.congr_of_eventuallyEq hev (heq ht)
  have hderiv_eq : A (swW A τ hτ g hg x₀ k t) + extG τ g k t
      = A (swX A τ hτ g hg x₀ t) + g k t := by
    have h1 : swW A τ hτ g hg x₀ k t = swX A τ hτ g hg x₀ t := (heq ht).symm
    have h2 : extG τ g k t = g k t := extG_eq τ g k t ht
    rw [h1, h2]
  rwa [hderiv_eq] at hcongr

private lemma swX_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) (t : ℝ) (ht : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    swX A τ hτ g hg x₀ t = (NormedSpace.exp ((t - τ k.castSucc) • A))
        (swX A τ hτ g hg x₀ (τ k.castSucc)) +
      ∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (b s) := by
  have hxt : swX A τ hτ g hg x₀ t = swW A τ hτ g hg x₀ k t :=
    swX_eq A τ hτ g hg x₀ k t ht
  have hmem : τ k.castSucc ∈ Icc (τ k.castSucc) (τ k.succ) :=
    ⟨le_rfl, (hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le⟩
  have hxc : swX A τ hτ g hg x₀ (τ k.castSucc) = swW A τ hτ g hg x₀ k (τ k.castSucc) :=
    swX_eq A τ hτ g hg x₀ k _ hmem
  have hWc : swW A τ hτ g hg x₀ k (τ k.castSucc) = swXst A τ hτ g hg x₀ k.castSucc :=
    swW_init A τ hτ g hg x₀ k
  have hform := pieceW_form A τ hτ g hg ⟨k.val, k.isLt⟩
    (swXst A τ hτ g hg x₀ k.castSucc) t
  have hWk : pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (swXst A τ hτ g hg x₀ k.castSucc)
      = swW A τ hτ g hg x₀ k := (swW_eq A τ hτ g hg x₀ k).symm
  rw [hWk] at hform
  have hcongr : (∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (extG τ g k s))
      = ∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (b s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hs' : s ∈ Ioo (τ k.castSucc) (τ k.succ) := Ioo_subset_Ioo le_rfl ht.2 hs
    show (NormedSpace.exp ((t - s) • A)) (extG τ g k s) = (NormedSpace.exp ((t - s) • A)) (b s)
    rw [extG_eq_b τ b g hbg k s hs']
  rw [hxt, hxc, hWc, hform, hcongr]

private lemma swX_piece_inteq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) (t : ℝ) (ht : t ∈ Icc (τ k.castSucc) (τ k.succ)) :
    swX A τ hτ g hg x₀ t - swX A τ hτ g hg x₀ (τ k.castSucc)
      = ∫ s in τ k.castSucc..t, (A (swX A τ hτ g hg x₀ s) + b s) := by
  have hWk : pieceW A τ hτ g hg ⟨k.val, k.isLt⟩ (swXst A τ hτ g hg x₀ k.castSucc)
      = swW A τ hτ g hg x₀ k := (swW_eq A τ hτ g hg x₀ k).symm
  have hderivW : ∀ s ∈ Set.uIcc (τ k.castSucc) t,
      HasDerivAt (swW A τ hτ g hg x₀ k)
        (A (swW A τ hτ g hg x₀ k s) + extG τ g k s) s := by
    intro s _
    have h := pieceW_deriv A τ hτ g hg ⟨k.val, k.isLt⟩
      (swXst A τ hτ g hg x₀ k.castSucc) s
    rwa [hWk] at h
  have hcontW : Continuous fun s => A (swW A τ hτ g hg x₀ k s) + extG τ g k s :=
    (A.continuous.comp (swW_cont A τ hτ g hg x₀ k)).add
      (continuous_extG τ hτ g hg k)
  have hintW : IntervalIntegrable (fun s => A (swW A τ hτ g hg x₀ k s) + extG τ g k s)
      volume (τ k.castSucc) t :=
    Continuous.intervalIntegrable hcontW _ _
  have hFTC : (∫ s in τ k.castSucc..t, (A (swW A τ hτ g hg x₀ k s) + extG τ g k s))
      = swW A τ hτ g hg x₀ k t - swW A τ hτ g hg x₀ k (τ k.castSucc) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivW hintW
  have hxt : swX A τ hτ g hg x₀ t = swW A τ hτ g hg x₀ k t :=
    swX_eq A τ hτ g hg x₀ k t ht
  have hmem : τ k.castSucc ∈ Icc (τ k.castSucc) (τ k.succ) :=
    ⟨le_rfl, (hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le⟩
  have hxc : swX A τ hτ g hg x₀ (τ k.castSucc) = swW A τ hτ g hg x₀ k (τ k.castSucc) :=
    swX_eq A τ hτ g hg x₀ k _ hmem
  have hcongr : (∫ s in τ k.castSucc..t, (A (swW A τ hτ g hg x₀ k s) + extG τ g k s))
      = ∫ s in τ k.castSucc..t, (A (swX A τ hτ g hg x₀ s) + b s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hs' : s ∈ Ioo (τ k.castSucc) (τ k.succ) := Ioo_subset_Ioo le_rfl ht.2 hs
    have hs'' : s ∈ Icc (τ k.castSucc) (τ k.succ) := Ioo_subset_Icc_self hs'
    have e1 : swW A τ hτ g hg x₀ k s = swX A τ hτ g hg x₀ s :=
      (swX_eq A τ hτ g hg x₀ k s hs'').symm
    have e2 : extG τ g k s = b s := extG_eq_b τ b g hbg k s hs'
    show A (swW A τ hτ g hg x₀ k s) + extG τ g k s
      = A (swX A τ hτ g hg x₀ s) + b s
    rw [e1, e2]
  rw [hxt, hxc, ← hFTC]
  exact hcongr

private lemma swX_integ_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (k : Fin n) (u v : ℝ) (hu : τ k.castSucc ≤ u) (huv : u ≤ v) (hv : v ≤ τ k.succ) :
    IntervalIntegrable (fun s => A (swX A τ hτ g hg x₀ s) + b s) volume u v := by
  have hFc : ContinuousOn (fun s => A (swX A τ hτ g hg x₀ s) + g k s) (Icc u v) := by
    have hx : ContinuousOn (swX A τ hτ g hg x₀) (Icc u v) :=
      (swX_cont_piece A τ hτ g hg x₀ k).mono (Icc_subset_Icc hu hv)
    have hgk : ContinuousOn (g k) (Icc u v) := (hg k).mono (Icc_subset_Icc hu hv)
    exact (A.continuous.comp_continuousOn hx).add hgk
  have hbase := hFc.intervalIntegrable_of_Icc (μ := volume) huv
  have hEq : EqOn (fun s => A (swX A τ hτ g hg x₀ s) + g k s)
      (fun s => A (swX A τ hτ g hg x₀ s) + b s) (Set.uIoo u v) := by
    intro s hs
    have hs' : s ∈ Ioo (τ k.castSucc) (τ k.succ) := by
      have h1 : s ∈ Ioo u v := by
        have huo : Set.uIoo u v = Ioo u v := uIoo_of_le huv
        rwa [huo] at hs
      exact Ioo_subset_Ioo hu hv h1
    simp only [hbg k hs']
  exact hbase.congr_uIoo hEq

-- Uniqueness on one closed piece, via Gronwall with a one-sided limit argument.
private lemma swX_unique_piece {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (y : ℝ → E) (hy : IsSwitchedTrajectory A b τ x₀ y) (k : Fin n)
    (hinit : y (τ k.castSucc) = swX A τ hτ g hg x₀ (τ k.castSucc)) :
    EqOn y (swX A τ hτ g hg x₀) (Icc (τ k.castSucc) (τ k.succ)) := by
  have hcd : τ k.castSucc < τ k.succ := hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)
  have hyc : ContinuousOn y (Icc (τ k.castSucc) (τ k.succ)) := by
    apply hy.2.2.1.mono
    apply Icc_subset_Icc
    · exact hτ.monotone (Fin.zero_le _)
    · exact hτ.monotone (le_last' _)
  have hxc : ContinuousOn (swX A τ hτ g hg x₀) (Icc (τ k.castSucc) (τ k.succ)) :=
    swX_cont_piece A τ hτ g hg x₀ k
  have hzcont : ∀ u v : ℝ, τ k.castSucc ≤ u → v ≤ τ k.succ →
      ContinuousOn (fun t => y t - swX A τ hτ g hg x₀ t) (Icc u v) := by
    intro u v hu hv
    exact (hyc.mono (Icc_subset_Icc hu hv)).sub (hxc.mono (Icc_subset_Icc hu hv))
  have hzderiv : ∀ t ∈ Ioo (τ k.castSucc) (τ k.succ),
      HasDerivAt (fun s => y s - swX A τ hτ g hg x₀ s)
        (A (y t - swX A τ hτ g hg x₀ t)) t := by
    intro t ht
    have hy' := hy.2.2.2 k t ht
    have hx' : HasDerivAt (swX A τ hτ g hg x₀)
        (A (swX A τ hτ g hg x₀ t) + b t) t := by
      have hwithin := swX_derivWithin_piece A τ hτ g hg x₀ k t
        (Ioo_subset_Icc_self ht)
      have hmem : Icc (τ k.castSucc) (τ k.succ) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have hat := hwithin.hasDerivAt hmem
      have hgb : g k t = b t := (hbg k ht).symm
      rwa [hgb] at hat
    have hsub := hy'.sub hx'
    have hval : (A (y t) + b t) - (A (swX A τ hτ g hg x₀ t) + b t)
        = A (y t - swX A τ hτ g hg x₀ t) := by
      rw [map_sub]
      abel
    rwa [hval] at hsub
  intro t ht
  by_cases htc : t = τ k.castSucc
  · subst htc
    exact hinit
  · have hct : τ k.castSucc < t := lt_of_le_of_ne ht.1 (Ne.symm htc)
    have hz0 : y (τ k.castSucc) - swX A τ hτ g hg x₀ (τ k.castSucc) = 0 :=
      sub_eq_zero.mpr hinit
    have hctend : Tendsto (fun δ : ℝ => τ k.castSucc + δ) (𝓝[>] 0)
        (𝓝 (τ k.castSucc)) := by
      have h : Continuous fun δ : ℝ => τ k.castSucc + δ :=
        continuous_const.add continuous_id
      have htend := h.tendsto 0
      simpa using htend.mono_left nhdsWithin_le_nhds
    have hz_within : ContinuousWithinAt (fun s => y s - swX A τ hτ g hg x₀ s)
        (Icc (τ k.castSucc) (τ k.succ)) (τ k.castSucc) :=
      (hzcont _ _ le_rfl le_rfl).continuousWithinAt ⟨le_rfl, hcd.le⟩
    have hzcomp : Tendsto
        (fun δ : ℝ => y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ))
        (𝓝[>] 0) (𝓝 (y (τ k.castSucc) - swX A τ hτ g hg x₀ (τ k.castSucc))) := by
      have h1 : Tendsto (fun δ : ℝ => τ k.castSucc + δ) (𝓝[>] 0)
          (𝓝[Icc (τ k.castSucc) (τ k.succ)] (τ k.castSucc)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · exact hctend
        · have hev1 : ∀ᶠ δ in 𝓝 (0:ℝ), δ < τ k.succ - τ k.castSucc :=
            eventually_lt_nhds (sub_pos.mpr hcd)
          have hev1' : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < τ k.succ - τ k.castSucc :=
            hev1.filter_mono nhdsWithin_le_nhds
          have hev0 : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := self_mem_nhdsWithin
          filter_upwards [hev1', hev0] with δ hδ1 hδ0
          constructor <;> linarith
      exact Filter.Tendsto.comp hz_within h1
    have hFlim : Tendsto (fun δ : ℝ => Real.exp (‖A‖ * (τ k.succ - τ k.castSucc)) *
        ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖)
        (𝓝[>] 0) (𝓝 0) := by
      have hnorm : Tendsto
          (fun δ : ℝ => ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖)
          (𝓝[>] 0) (𝓝 0) := by
        have h := hzcomp.norm
        rw [hz0, norm_zero] at h
        exact h
      have hmul := (tendsto_const_nhds (x := Real.exp (‖A‖ * (τ k.succ - τ k.castSucc)))
        (f := 𝓝[>] (0:ℝ))).mul hnorm
      simpa using hmul
    have hbound : ∀ᶠ δ in 𝓝[>] (0:ℝ),
        ‖y t - swX A τ hτ g hg x₀ t‖ ≤ Real.exp (‖A‖ * (τ k.succ - τ k.castSucc)) *
          ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖ := by
      have hev1 : ∀ᶠ δ in 𝓝 (0:ℝ), δ < t - τ k.castSucc :=
        eventually_lt_nhds (sub_pos.mpr hct)
      have hev1' : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < t - τ k.castSucc :=
        hev1.filter_mono nhdsWithin_le_nhds
      have hev0 : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := self_mem_nhdsWithin
      filter_upwards [hev1', hev0] with δ hδ1 hδ0
      have ht2 : t ≤ τ k.succ := ht.2
      have hcdδ : τ k.castSucc + δ ≤ τ k.succ := by linarith
      have hmem_t : t ∈ Icc (τ k.castSucc + δ) (τ k.succ) := ⟨by linarith, ht.2⟩
      have hG := norm_le_gronwallBound_of_norm_deriv_right_le
        (f := fun s => y s - swX A τ hτ g hg x₀ s)
        (f' := fun s => A (y s - swX A τ hτ g hg x₀ s))
        (δ := ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖)
        (K := ‖A‖) (ε := 0) (a := τ k.castSucc + δ) (b := τ k.succ)
        (hzcont (τ k.castSucc + δ) (τ k.succ) (by linarith) le_rfl)
        (fun x hx => by
          have hx1 : τ k.castSucc + δ ≤ x := hx.1
          have hx' : x ∈ Ioo (τ k.castSucc) (τ k.succ) := ⟨by linarith, hx.2⟩
          exact (hzderiv x hx').hasDerivWithinAt)
        le_rfl
        (fun x _ => by
          rw [add_zero]
          exact A.le_opNorm _)
      have hGbound := hG t hmem_t
      rw [gronwallBound_ε0] at hGbound
      have hexp : Real.exp (‖A‖ * (t - (τ k.castSucc + δ)))
          ≤ Real.exp (‖A‖ * (τ k.succ - τ k.castSucc)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        linarith
      calc ‖y t - swX A τ hτ g hg x₀ t‖
          ≤ ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖ *
            Real.exp (‖A‖ * (t - (τ k.castSucc + δ))) := hGbound
        _ ≤ Real.exp (‖A‖ * (τ k.succ - τ k.castSucc)) *
            ‖y (τ k.castSucc + δ) - swX A τ hτ g hg x₀ (τ k.castSucc + δ)‖ := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    have hfinal : ‖y t - swX A τ hτ g hg x₀ t‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hFlim hbound
    have hz0' : y t - swX A τ hτ g hg x₀ t = 0 := norm_le_zero_iff.mp hfinal
    exact sub_eq_zero.mp hz0'

private lemma swX_cont_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    ∀ j : Fin (n + 1), ContinuousOn (swX A τ hτ g hg x₀) (Icc (τ 0) (τ j)) := by
  intro j
  refine Fin.induction ?_ ?_ j
  · show ContinuousOn (swX A τ hτ g hg x₀) (Icc (τ 0) (τ (0 : Fin (n + 1))))
    have hself : Icc (τ 0) (τ (0 : Fin (n + 1))) = {τ 0} := Icc_self _
    rw [hself]
    exact continuousOn_singleton _ _
  · intro k ih
    have h01 : τ 0 ≤ τ k.castSucc := hτ.monotone (Fin.zero_le _)
    have h12 : τ k.castSucc ≤ τ k.succ := (hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
    have hunion : Icc (τ 0) (τ k.succ)
        = Icc (τ 0) (τ k.castSucc) ∪ Icc (τ k.castSucc) (τ k.succ) :=
      (Icc_union_Icc_eq_Icc h01 h12).symm
    rw [hunion]
    exact ih.union_of_isClosed (swX_cont_piece A τ hτ g hg x₀ k) isClosed_Icc isClosed_Icc

private lemma swX_integ_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    ∀ j : Fin (n + 1),
      IntervalIntegrable (fun s => A (swX A τ hτ g hg x₀ s) + b s) volume (τ 0) (τ j) := by
  intro j
  refine Fin.induction ?_ ?_ j
  · exact IntervalIntegrable.refl
  · intro k ih
    exact ih.trans (swX_integ_piece A τ hτ b g hg hbg x₀ k (τ k.castSucc) (τ k.succ)
      le_rfl (hτ (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le le_rfl)

private lemma swX_inteq_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    ∀ j : Fin (n + 1), ∀ t ∈ Icc (τ 0) (τ j),
      swX A τ hτ g hg x₀ t
        = x₀ + ∫ s in τ 0..t, (A (swX A τ hτ g hg x₀ s) + b s) := by
  intro j
  refine Fin.induction ?_ ?_ j
  · intro t ht
    have hteq : t = τ 0 := le_antisymm ht.2 ht.1
    subst hteq
    rw [swX_init A τ hτ g hg x₀, intervalIntegral.integral_same, add_zero]
  · intro k ih t ht
    by_cases hle : t ≤ τ k.castSucc
    · exact ih t ⟨ht.1, hle⟩
    · have hct : τ k.castSucc < t := lt_of_not_ge hle
      have hmem : t ∈ Icc (τ k.castSucc) (τ k.succ) := ⟨le_of_lt hct, ht.2⟩
      have hmemc : τ k.castSucc ∈ Icc (τ 0) (τ k.castSucc) :=
        ⟨hτ.monotone (Fin.zero_le _), le_rfl⟩
      have hIH := ih (τ k.castSucc) hmemc
      have hpiece := swX_piece_inteq A τ hτ b g hg hbg x₀ k t hmem
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (swX_integ_prefix A τ hτ b g hg hbg x₀ k.castSucc)
        (swX_integ_piece A τ hτ b g hg hbg x₀ k (τ k.castSucc) t le_rfl hct.le ht.2)
      have hsub : swX A τ hτ g hg x₀ t = swX A τ hτ g hg x₀ (τ k.castSucc) +
          ∫ s in τ k.castSucc..t, (A (swX A τ hτ g hg x₀ s) + b s) :=
        (sub_eq_iff_eq_add.mp hpiece).trans (add_comm _ _)
      rw [hsub, hIH, add_assoc, hadd]

private lemma swX_unique_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E)
    (y : ℝ → E) (hy : IsSwitchedTrajectory A b τ x₀ y) :
    ∀ j : Fin (n + 1), EqOn y (swX A τ hτ g hg x₀) (Icc (τ 0) (τ j)) := by
  intro j
  refine Fin.induction ?_ ?_ j
  · intro t ht
    have hteq : t = τ 0 := le_antisymm ht.2 ht.1
    subst hteq
    show y (τ 0) = swX A τ hτ g hg x₀ (τ 0)
    rw [hy.2.1, swX_init A τ hτ g hg x₀]
  · intro k ih t ht
    by_cases hle : t ≤ τ k.castSucc
    · exact ih ⟨ht.1, hle⟩
    · have hmem : t ∈ Icc (τ k.castSucc) (τ k.succ) := ⟨(lt_of_not_ge hle).le, ht.2⟩
      have hinit : y (τ k.castSucc) = swX A τ hτ g hg x₀ (τ k.castSucc) :=
        ih ⟨hτ.monotone (Fin.zero_le _), le_rfl⟩
      exact swX_unique_piece A τ hτ b g hg hbg x₀ y hy k hinit hmem

/-- **Finite affine switching: patched Duhamel trajectory.** For a constant bounded linear `A` on
a real Banach space, a finite partition `τ` of the horizon, and forcing `b` that is
continuous on each open piece with a continuous extension `g k` to the closed piece, there is a
trajectory `x` through `x₀` that
* is a continuous piecewise solution (`IsSwitchedTrajectory`);
* is given on each closed piece by Duhamel's formula from its value at the left switch time;
* is C¹ on each closed piece, with one-sided derivative `A (x t) + g k t`;
* satisfies the integral equation `x t = x₀ + ∫ s in τ 0..t, (A (x s) + b s)` on the horizon,
  across the switch times, with an interval-integrable integrand;
* agrees on the horizon with every continuous piecewise solution through `x₀`. -/
theorem switchedTrajectory_exists_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) {n : ℕ} (τ : Fin (n + 1) → ℝ) (hτ : StrictMono τ)
    (b : ℝ → E) (g : Fin n → ℝ → E)
    (hg : ∀ k : Fin n, ContinuousOn (g k) (Icc (τ k.castSucc) (τ k.succ)))
    (hbg : ∀ k : Fin n, EqOn b (g k) (Ioo (τ k.castSucc) (τ k.succ))) (x₀ : E) :
    ∃ x : ℝ → E, IsSwitchedTrajectory A b τ x₀ x ∧
      (∀ k : Fin n, ∀ t ∈ Icc (τ k.castSucc) (τ k.succ),
        x t = (NormedSpace.exp ((t - τ k.castSucc) • A)) (x (τ k.castSucc)) +
          ∫ s in τ k.castSucc..t, (NormedSpace.exp ((t - s) • A)) (b s)) ∧
      (∀ k : Fin n, ∀ t ∈ Icc (τ k.castSucc) (τ k.succ),
        HasDerivWithinAt x (A (x t) + g k t) (Icc (τ k.castSucc) (τ k.succ)) t) ∧
      IntervalIntegrable (fun s => A (x s) + b s) volume (τ 0) (τ (Fin.last n)) ∧
      (∀ t ∈ Icc (τ 0) (τ (Fin.last n)), x t = x₀ + ∫ s in τ 0..t, (A (x s) + b s)) ∧
      ∀ y : ℝ → E, IsSwitchedTrajectory A b τ x₀ y → EqOn y x (Icc (τ 0) (τ (Fin.last n))) := by
  refine ⟨swX A τ hτ g hg x₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hτ, swX_init A τ hτ g hg x₀, ?_, ?_⟩
    · exact swX_cont_prefix A τ hτ g hg x₀ (Fin.last n)
    · intro k t ht
      have hwithin := swX_derivWithin_piece A τ hτ g hg x₀ k t
        (Ioo_subset_Icc_self ht)
      have hmem : Icc (τ k.castSucc) (τ k.succ) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have hat := hwithin.hasDerivAt hmem
      have hgb : g k t = b t := (hbg k ht).symm
      rwa [hgb] at hat
  · intro k t ht
    exact swX_formula A τ hτ b g hg hbg x₀ k t ht
  · intro k t ht
    exact swX_derivWithin_piece A τ hτ g hg x₀ k t ht
  · exact swX_integ_prefix A τ hτ b g hg hbg x₀ (Fin.last n)
  · intro t ht
    exact swX_inteq_prefix A τ hτ b g hg hbg x₀ (Fin.last n) t ht
  · intro y hy
    exact swX_unique_prefix A τ hτ b g hg hbg x₀ y hy (Fin.last n)

/-! ### Validation: two forcing levels, one interior switch, and a state reset -/

/-- Scalar fixture dynamics `x' = -x + u` (an RC-type averaged converter state). -/
noncomputable def twoLevelA : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ

/-- Switch times `0 < 1 < 2`. -/
noncomputable def twoLevelTimes : Fin 3 → ℝ := ![0, 1, 2]

/-- Two forcing levels: `u = 1` before the switch at `t = 1`, `u = 0` after it. -/
noncomputable def twoLevelForcing (t : ℝ) : ℝ := if t < 1 then 1 else 0

/-- The patched trajectory from `0`: charge `1 - e^{-t}`, then discharge from `1 - e^{-1}`. -/
noncomputable def twoLevelTrajectory (t : ℝ) : ℝ :=
  if t ≤ 1 then 1 - Real.exp (-t) else (1 - Real.exp (-1)) * Real.exp (-(t - 1))

-- Helpers for the validation theorems (not part of the pin).

private lemma times_zero : twoLevelTimes 0 = (0 : ℝ) := by simp [twoLevelTimes]

private lemma times_one : twoLevelTimes 1 = (1 : ℝ) := by simp [twoLevelTimes]

private lemma times_two : twoLevelTimes 2 = (2 : ℝ) := by
  simp [twoLevelTimes, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

private lemma last_two : Fin.last 2 = (2 : Fin 3) := by decide

private lemma twoLevelTimes_strictMono : StrictMono twoLevelTimes := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  fin_cases i
  · change twoLevelTimes 0 < twoLevelTimes 1
    rw [times_zero, times_one]
    norm_num
  · change twoLevelTimes 1 < twoLevelTimes 2
    rw [times_one, times_two]
    norm_num

private lemma expneg_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * -1) t :=
  (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id' t).neg

private lemma branch1_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) (Real.exp (-t)) t := by
  have hsub : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s))
      ((0:ℝ) - Real.exp (-t) * -1) t :=
    (hasDerivAt_const t 1).sub (expneg_hasDerivAt t)
  have hval : (0:ℝ) - Real.exp (-t) * -1 = Real.exp (-t) := by ring
  exact hsub.congr_deriv hval

private lemma twoLevel_ode0 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt twoLevelTrajectory
      (twoLevelA (twoLevelTrajectory t) + twoLevelForcing t) t := by
  have h1 := branch1_hasDerivAt t
  have hev : twoLevelTrajectory =ᶠ[𝓝 t] (fun s : ℝ => 1 - Real.exp (-s)) := by
    have h : ∀ᶠ s in 𝓝 t, s < 1 := eventually_lt_nhds ht.2
    filter_upwards [h] with s hs
    simp [twoLevelTrajectory, le_of_lt hs]
  have htraj : twoLevelTrajectory t = 1 - Real.exp (-t) := by
    simp [twoLevelTrajectory, le_of_lt ht.2]
  have hu : twoLevelForcing t = 1 := by simp [twoLevelForcing, ht.2]
  have hA : twoLevelA (twoLevelTrajectory t) = -(1 - Real.exp (-t)) := by
    simp [twoLevelA, htraj, ContinuousLinearMap.id_apply]
  have hval : Real.exp (-t)
      = twoLevelA (twoLevelTrajectory t) + twoLevelForcing t := by
    rw [hA, hu]
    ring
  exact (h1.congr_of_eventuallyEq hev).congr_deriv hval

private lemma twoLevel_ode1 (t : ℝ) (ht : t ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt twoLevelTrajectory
      (twoLevelA (twoLevelTrajectory t) + twoLevelForcing t) t := by
  have hinner : HasDerivAt (fun s : ℝ => -(s - 1)) (-1) t := by
    have hsub : HasDerivAt (fun s : ℝ => s - 1) ((1:ℝ) - 0) t :=
      (hasDerivAt_id' t).sub (hasDerivAt_const t 1)
    have hval : (-((1:ℝ) - 0)) = (-1:ℝ) := by norm_num
    have hneg : HasDerivAt (fun s : ℝ => -(s - 1)) (-((1:ℝ) - 0)) t := hsub.neg
    exact hneg.congr_deriv hval
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(s - 1)))
      (Real.exp (-(t - 1)) * -1) t :=
    hinner.exp
  have hmul : HasDerivAt (fun s : ℝ => (1 - Real.exp (-1)) * Real.exp (-(s - 1)))
      ((1 - Real.exp (-1)) * (Real.exp (-(t - 1)) * -1)) t :=
    HasDerivAt.const_mul _ hexp
  have hev : twoLevelTrajectory
      =ᶠ[𝓝 t] (fun s : ℝ => (1 - Real.exp (-1)) * Real.exp (-(s - 1))) := by
    have h : ∀ᶠ s in 𝓝 t, (1:ℝ) < s := eventually_gt_nhds ht.1
    filter_upwards [h] with s hs
    simp [twoLevelTrajectory, not_le.mpr hs]
  have htraj : twoLevelTrajectory t
      = (1 - Real.exp (-1)) * Real.exp (-(t - 1)) := by
    simp [twoLevelTrajectory, not_le.mpr ht.1]
  have hu : twoLevelForcing t = 0 := by
    simp [twoLevelForcing, not_lt.mpr (le_of_lt ht.1)]
  have hA : twoLevelA (twoLevelTrajectory t)
      = -((1 - Real.exp (-1)) * Real.exp (-(t - 1))) := by
    simp [twoLevelA, htraj, ContinuousLinearMap.id_apply]
  have hval : (1 - Real.exp (-1)) * (Real.exp (-(t - 1)) * -1)
      = twoLevelA (twoLevelTrajectory t) + twoLevelForcing t := by
    rw [hA, hu, add_zero]
    ring
  exact (hmul.congr_of_eventuallyEq hev).congr_deriv hval

private lemma twoLevel_cont : ContinuousOn twoLevelTrajectory (Icc (0:ℝ) 2) := by
  have h01 : ContinuousOn twoLevelTrajectory (Icc (0:ℝ) 1) := by
    have hbr : Continuous fun t : ℝ => 1 - Real.exp (-t) :=
      continuous_const.sub (Real.continuous_exp.comp (continuous_id.neg))
    exact hbr.continuousOn.congr (fun t ht => by simp [twoLevelTrajectory, ht.2])
  have h12 : ContinuousOn twoLevelTrajectory (Icc (1:ℝ) 2) := by
    have hbr : Continuous fun t : ℝ => (1 - Real.exp (-1)) * Real.exp (-(t - 1)) := by
      apply Continuous.mul continuous_const
      exact Real.continuous_exp.comp ((continuous_id.sub continuous_const).neg)
    exact hbr.continuousOn.congr (fun t ht => by
      by_cases h1 : t = 1
      · subst h1
        simp [twoLevelTrajectory, sub_self, neg_zero, Real.exp_zero]
      · have hlt : (1:ℝ) < t := lt_of_le_of_ne ht.1 (Ne.symm h1)
        simp [twoLevelTrajectory, not_le.mpr hlt])
  have hunion : Icc (0:ℝ) 2 = Icc 0 1 ∪ Icc 1 2 :=
    (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  rw [hunion]
  exact h01.union_of_isClosed h12 isClosed_Icc isClosed_Icc

/-- The two-level fixture is a continuous piecewise solution through `0`. -/
theorem twoLevel_isSwitchedTrajectory :
    IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 twoLevelTrajectory := by
  refine ⟨twoLevelTimes_strictMono, ?_, ?_, ?_⟩
  · have h0 : twoLevelTimes 0 = (0:ℝ) := times_zero
    rw [h0]
    show twoLevelTrajectory 0 = 0
    simp [twoLevelTrajectory, (by norm_num : (0:ℝ) ≤ 1), neg_zero, Real.exp_zero]
  · have h0 : twoLevelTimes 0 = (0:ℝ) := times_zero
    have h2 : twoLevelTimes (Fin.last 2) = (2:ℝ) := by rw [last_two]; exact times_two
    rw [h0, h2]
    exact twoLevel_cont
  · intro k t ht
    fin_cases k
    · change t ∈ Ioo (twoLevelTimes 0) (twoLevelTimes 1) at ht
      rw [times_zero, times_one] at ht
      exact twoLevel_ode0 t ht
    · change t ∈ Ioo (twoLevelTimes 1) (twoLevelTimes 2) at ht
      rw [times_one, times_two] at ht
      exact twoLevel_ode1 t ht

-- FTC on one piece `[u, v]` where the forcing is the constant `c`.
private lemma twoLevel_ftc_piece (u v c : ℝ) (huv : u ≤ v)
    (hcont : ContinuousOn twoLevelTrajectory (Icc u v))
    (hforce : ∀ s ∈ Ioo u v, twoLevelForcing s = c)
    (hderiv : ∀ s ∈ Ioo u v, HasDerivAt twoLevelTrajectory
      (twoLevelA (twoLevelTrajectory s) + twoLevelForcing s) s) :
    IntervalIntegrable (fun s => twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        volume u v ∧
      ∫ s in u..v, (twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        = twoLevelTrajectory v - twoLevelTrajectory u := by
  have hgc : ContinuousOn (fun s => twoLevelA (twoLevelTrajectory s) + c) (Icc u v) :=
    (twoLevelA.continuous.comp_continuousOn hcont).add continuousOn_const
  have hEq : EqOn (fun s => twoLevelA (twoLevelTrajectory s) + c)
      (fun s => twoLevelA (twoLevelTrajectory s) + twoLevelForcing s) (Set.uIoo u v) := by
    intro s hs
    rw [uIoo_of_le huv] at hs
    simp only [hforce s hs]
  have hint := (hgc.intervalIntegrable_of_Icc (μ := volume) huv).congr_uIoo hEq
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv hcont
    (fun s hs => (hderiv s hs).hasDerivWithinAt) hint⟩

private lemma twoLevelTrajectory_zero : twoLevelTrajectory 0 = 0 := by
  simp [twoLevelTrajectory, (by norm_num : (0:ℝ) ≤ 1), neg_zero, Real.exp_zero]

private lemma twoLevel_piece0 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntervalIntegrable (fun s => twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        volume 0 t ∧
      ∫ s in (0:ℝ)..t, (twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        = twoLevelTrajectory t - twoLevelTrajectory 0 := by
  apply twoLevel_ftc_piece 0 t 1 ht0
  · exact twoLevel_cont.mono (Icc_subset_Icc le_rfl (by linarith))
  · intro s hs
    have hs1 : s < 1 := lt_of_lt_of_le hs.2 ht1
    simp [twoLevelForcing, hs1]
  · intro s hs
    exact twoLevel_ode0 s ⟨hs.1, lt_of_lt_of_le hs.2 ht1⟩

private lemma twoLevel_piece1 (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    IntervalIntegrable (fun s => twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        volume 1 t ∧
      ∫ s in (1:ℝ)..t, (twoLevelA (twoLevelTrajectory s) + twoLevelForcing s)
        = twoLevelTrajectory t - twoLevelTrajectory 1 := by
  apply twoLevel_ftc_piece 1 t 0 ht1
  · exact twoLevel_cont.mono (Icc_subset_Icc (by norm_num) ht2)
  · intro s hs
    simp [twoLevelForcing, not_lt.mpr (le_of_lt hs.1)]
  · intro s hs
    exact twoLevel_ode1 s ⟨hs.1, lt_of_lt_of_le hs.2 ht2⟩

/-- The two-level fixture satisfies the integral equation across the interior switch. -/
theorem twoLevel_integral_equation :
    ∀ t ∈ Icc (0 : ℝ) 2, twoLevelTrajectory t =
      0 + ∫ s in (0 : ℝ)..t, (twoLevelA (twoLevelTrajectory s) + twoLevelForcing s) := by
  intro t ht
  by_cases hle : t ≤ 1
  · rw [(twoLevel_piece0 t ht.1 hle).2, twoLevelTrajectory_zero]
    ring
  · have h1t : 1 ≤ t := le_of_lt (lt_of_not_ge hle)
    have hA := twoLevel_piece0 1 (by norm_num) le_rfl
    have hB := twoLevel_piece1 t h1t ht.2
    rw [← intervalIntegral.integral_add_adjacent_intervals hA.1 hB.1, hA.2, hB.2,
      twoLevelTrajectory_zero]
    ring

/-- A state reset to `0` at the switch time: it follows the fixture before `t = 1` and the
unforced decay from `0` (identically `0`) after it. -/
noncomputable def resetTrajectory (t : ℝ) : ℝ :=
  if t < 1 then 1 - Real.exp (-t) else 0

/-- The reset trajectory solves the ODE on both open pieces but is not continuous on the
horizon, so it is not a switched trajectory. -/
theorem reset_not_continuousOn :
    (∀ k : Fin 2, ∀ t ∈ Ioo (twoLevelTimes k.castSucc) (twoLevelTimes k.succ),
        HasDerivAt resetTrajectory (twoLevelA (resetTrajectory t) + twoLevelForcing t) t) ∧
      ¬ ContinuousOn resetTrajectory (Icc 0 2) ∧
      ¬ IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 resetTrajectory := by
  have hode : ∀ k : Fin 2, ∀ t ∈ Ioo (twoLevelTimes k.castSucc) (twoLevelTimes k.succ),
      HasDerivAt resetTrajectory (twoLevelA (resetTrajectory t) + twoLevelForcing t) t := by
    intro k t ht
    fin_cases k
    · change t ∈ Ioo (twoLevelTimes 0) (twoLevelTimes 1) at ht
      rw [times_zero, times_one] at ht
      have h1 := branch1_hasDerivAt t
      have hev : resetTrajectory =ᶠ[𝓝 t] (fun s : ℝ => 1 - Real.exp (-s)) := by
        have h : ∀ᶠ s in 𝓝 t, s < 1 := eventually_lt_nhds ht.2
        filter_upwards [h] with s hs
        simp [resetTrajectory, hs]
      have hreset : resetTrajectory t = 1 - Real.exp (-t) := by
        simp [resetTrajectory, ht.2]
      have hu : twoLevelForcing t = 1 := by simp [twoLevelForcing, ht.2]
      have hA : twoLevelA (resetTrajectory t) = -(1 - Real.exp (-t)) := by
        simp [twoLevelA, hreset,
          ContinuousLinearMap.id_apply]
      have hval : Real.exp (-t)
          = twoLevelA (resetTrajectory t) + twoLevelForcing t := by
        rw [hA, hu]
        ring
      exact (h1.congr_of_eventuallyEq hev).congr_deriv hval
    · change t ∈ Ioo (twoLevelTimes 1) (twoLevelTimes 2) at ht
      rw [times_one, times_two] at ht
      have hconst : HasDerivAt (fun _ : ℝ => (0:ℝ)) (0:ℝ) t := hasDerivAt_const t 0
      have hev : resetTrajectory =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        have h : ∀ᶠ s in 𝓝 t, (1:ℝ) < s := eventually_gt_nhds ht.1
        filter_upwards [h] with s hs
        simp [resetTrajectory, not_lt.mpr (le_of_lt hs)]
      have hreset : resetTrajectory t = 0 := by
        simp [resetTrajectory, not_lt.mpr (le_of_lt ht.1)]
      have hu : twoLevelForcing t = 0 := by
        simp [twoLevelForcing, not_lt.mpr (le_of_lt ht.1)]
      have hA : twoLevelA (resetTrajectory t) = 0 := by
        simp [twoLevelA, hreset,
          ContinuousLinearMap.id_apply]
      have hval : (0:ℝ) = twoLevelA (resetTrajectory t) + twoLevelForcing t := by
        rw [hA, hu, add_zero]
      exact (hconst.congr_of_eventuallyEq hev).congr_deriv hval
  have hnc : ¬ ContinuousOn resetTrajectory (Icc 0 2) := by
    intro hcont
    have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 2 := ⟨by norm_num, by norm_num⟩
    have hwithin : ContinuousWithinAt resetTrajectory (Icc (0:ℝ) 2) 1 :=
      hcont.continuousWithinAt h1mem
    have hle : 𝓝[<] (1:ℝ) ≤ 𝓝[Icc (0:ℝ) 2] 1 := by
      show 𝓝[<] (1:ℝ) ≤ 𝓝 1 ⊓ 𝓟 (Icc (0:ℝ) 2)
      apply le_inf nhdsWithin_le_nhds
      rw [Filter.le_principal_iff]
      exact mem_nhdsWithin_of_mem_nhds
        (Icc_mem_nhds (by norm_num) (by norm_num))
    have htend1 : Tendsto resetTrajectory (𝓝[<] (1:ℝ)) (𝓝 (resetTrajectory 1)) :=
      Filter.Tendsto.mono_left hwithin hle
    have hbranch : Tendsto (fun t : ℝ => 1 - Real.exp (-t)) (𝓝[<] (1:ℝ))
        (𝓝 (1 - Real.exp (-1))) := by
      have hcont' : Continuous fun t : ℝ => 1 - Real.exp (-t) :=
        continuous_const.sub (Real.continuous_exp.comp (continuous_id.neg))
      exact Filter.Tendsto.mono_left (hcont'.tendsto 1) nhdsWithin_le_nhds
    have hev : resetTrajectory =ᶠ[𝓝[<] (1:ℝ)] (fun t : ℝ => 1 - Real.exp (-t)) := by
      have hmem : Set.Iio (1:ℝ) ∈ 𝓝[<] (1:ℝ) := self_mem_nhdsWithin
      filter_upwards [hmem] with s hs
      have hs' : s < 1 := hs
      simp [resetTrajectory, hs']
    have heq := tendsto_nhds_unique_of_eventuallyEq htend1 hbranch hev
    have hr1 : resetTrajectory 1 = 0 := by simp [resetTrajectory]
    rw [hr1] at heq
    have hexp1 : Real.exp (-1 : ℝ) = 1 := by linarith [heq]
    have hexp1' : Real.exp (1 : ℝ) = 1 := by
      have h : (Real.exp 1)⁻¹ = 1 := by
        have h := hexp1
        rwa [Real.exp_neg] at h
      exact inv_eq_one.mp h
    have hge := Real.add_one_le_exp (1 : ℝ)
    rw [hexp1'] at hge
    norm_num at hge
  exact ⟨hode, hnc, fun hswitch => hnc hswitch.2.2.1⟩

/-- The reset violates the integral equation across the switch boundary. -/
theorem reset_not_integral_equation :
    ¬ ∀ t ∈ Icc (0 : ℝ) 2, resetTrajectory t =
      0 + ∫ s in (0 : ℝ)..t, (twoLevelA (resetTrajectory s) + twoLevelForcing s) := by
  intro hall
  have h1 := hall 1 ⟨by norm_num, by norm_num⟩
  have hr1 : resetTrajectory 1 = 0 := by simp [resetTrajectory]
  rw [hr1, zero_add] at h1
  have hcongr : (∫ s in (0:ℝ)..1, (twoLevelA (resetTrajectory s) + twoLevelForcing s))
      = ∫ s in (0:ℝ)..1, Real.exp (-s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro s hs
    have hrs : resetTrajectory s = 1 - Real.exp (-s) := by simp [resetTrajectory, hs.2]
    have hu : twoLevelForcing s = 1 := by simp [twoLevelForcing, hs.2]
    have hA : twoLevelA (resetTrajectory s) = -(1 - Real.exp (-s)) := by
      simp [twoLevelA, hrs]
    show twoLevelA (resetTrajectory s) + twoLevelForcing s = Real.exp (-s)
    rw [hA, hu]
    ring
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => -(Real.exp (-r))) (Real.exp (-s)) s := by
    intro s _
    have h := (expneg_hasDerivAt s).neg
    have hval : -(Real.exp (-s) * -1) = Real.exp (-s) := by ring
    have h2 : HasDerivAt (fun r : ℝ => -(Real.exp (-r))) (-(Real.exp (-s) * -1)) s := h
    exact h2.congr_deriv hval
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-s)) volume (0:ℝ) 1 :=
    Continuous.intervalIntegrable
      (Real.continuous_exp.comp (continuous_id.neg)) 0 1
  have hFTC : (∫ s in (0:ℝ)..1, Real.exp (-s)) = (-(Real.exp (-1))) - (-(Real.exp (-0))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (f := fun s : ℝ => -(Real.exp (-s))) (f' := fun s : ℝ => Real.exp (-s)) hderiv hint
  have hval : (∫ s in (0:ℝ)..1, Real.exp (-s)) = 1 - Real.exp (-1) := by
    rw [show (-(0:ℝ)) = 0 from neg_zero, Real.exp_zero] at hFTC
    have hrr : (-(Real.exp (-1))) - (-1) = 1 - Real.exp (-1) := by ring
    rwa [hrr] at hFTC
  rw [hcongr, hval] at h1
  have hexp1 : Real.exp (-1 : ℝ) = 1 := by linarith [h1]
  have hexp1' : Real.exp (1 : ℝ) = 1 := by
    have h : (Real.exp 1)⁻¹ = 1 := by
      have h := hexp1
      rwa [Real.exp_neg] at h
    exact inv_eq_one.mp h
  have hge := Real.add_one_le_exp (1 : ℝ)
  rw [hexp1'] at hge
  norm_num at hge

end MathlibExt.Analysis.ODE.FiniteAffineSwitching
