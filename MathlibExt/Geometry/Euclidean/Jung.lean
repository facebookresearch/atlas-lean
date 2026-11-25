/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import MathlibExt.Analysis.Convex.Straszewicz

@[expose] public section

namespace MathlibExt.Geometry.Euclidean.JungWanted

open Finset BigOperators InnerProductSpace

-- Helper (proved): for weights summing to 1, sum of squares is at least 1/card.
-- Used to bound 1 - ∑ wᵢ² ≤ (m-1)/m in Jung's estimate.
private lemma weight_sq_sum_ge {ι : Type*} (t : Finset ι) (w : ι → ℝ) (hw : ∑ i ∈ t, w i = 1) :
    (1 : ℝ) / (t.card : ℝ) ≤ ∑ i ∈ t, (w i) ^ 2 := by
  have h : (∑ i ∈ t, w i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ t, (w i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hw, one_pow] at h
  have hne : t.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    simp at hw
  have hpos : (0 : ℝ) < (t.card : ℝ) := by
    have : 0 < t.card := Finset.card_pos.mpr hne
    exact_mod_cast this
  rw [div_le_iff₀ hpos]
  linarith [h]

-- Helper (proved): variance identity for a weighted barycenter.
private lemma variance_identity {ι : Type*} {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Finset ι) (w : ι → ℝ) (x : ι → E) (hw : ∑ i ∈ t, w i = 1) :
    let c := ∑ i ∈ t, w i • x i
    ∑ i ∈ t, w i * (‖x i - c‖ ^ 2) = ∑ i ∈ t, w i * (‖x i‖ ^ 2) - ‖c‖ ^ 2 := by
  intro c
  have hexpand : ∀ i ∈ t, w i * (‖x i - c‖ ^ 2)
      = w i * (‖x i‖ ^ 2) - w i * (2 * ⟪x i, c⟫_ℝ) + w i * (‖c‖ ^ 2) := by
    intro i _
    have hnorm : ‖x i - c‖ ^ 2 = ‖x i‖ ^ 2 - 2 * ⟪x i, c⟫_ℝ + ‖c‖ ^ 2 :=
      norm_sub_sq_real (x i) c
    rw [hnorm]
    ring
  have hsplit : ∑ i ∈ t, (w i * (‖x i‖ ^ 2) - w i * (2 * ⟪x i, c⟫_ℝ) + w i * (‖c‖ ^ 2))
      = (∑ i ∈ t, w i * (‖x i‖ ^ 2) - ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ))
        + ∑ i ∈ t, w i * (‖c‖ ^ 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hinner : ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ) = 2 * (‖c‖ ^ 2) := by
    have hbase : ∑ i ∈ t, w i * ⟪x i, c⟫_ℝ = ⟪c, c⟫_ℝ := by
      have h1 : ⟪c, c⟫_ℝ = ∑ i ∈ t, ⟪w i • x i, c⟫_ℝ := by
        rw [sum_inner]
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_smul_left]
      simp
    have h2 : ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ)
        = 2 * ∑ i ∈ t, w i * ⟪x i, c⟫_ℝ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2, hbase, real_inner_self_eq_norm_sq]
  have hnormc : ∑ i ∈ t, w i * (‖c‖ ^ 2) = ‖c‖ ^ 2 := by
    rw [← Finset.sum_mul, hw, one_mul]
  calc ∑ i ∈ t, w i * (‖x i - c‖ ^ 2)
      = ∑ i ∈ t, (w i * (‖x i‖ ^ 2) - w i * (2 * ⟪x i, c⟫_ℝ) + w i * (‖c‖ ^ 2)) :=
        Finset.sum_congr rfl hexpand
    _ = (∑ i ∈ t, w i * (‖x i‖ ^ 2) - ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ))
        + ∑ i ∈ t, w i * (‖c‖ ^ 2) := hsplit
    _ = ∑ i ∈ t, w i * (‖x i‖ ^ 2) - ‖c‖ ^ 2 := by rw [hinner, hnormc]; ring

-- Helper (proved): pairwise double-sum identity for a weighted barycenter.
private lemma pairwise_identity {ι : Type*} {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : Finset ι) (w : ι → ℝ) (x : ι → E) (hw : ∑ i ∈ t, w i = 1) :
    let c := ∑ i ∈ t, w i • x i
    ∑ i ∈ t, w i * (‖x i‖ ^ 2) - ‖c‖ ^ 2
      = (1/2) * ∑ i ∈ t, ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2) := by
  intro c
  have hexpand : ∀ i ∈ t, ∀ j ∈ t,
      w i * w j * (‖x i - x j‖ ^ 2)
      = (w i * w j * (‖x i‖ ^ 2)) - (w i * w j * (2 * ⟪x i, x j⟫_ℝ))
        + (w i * w j * (‖x j‖ ^ 2)) := by
    intro i _ j _
    have hnorm : ‖x i - x j‖ ^ 2 = ‖x i‖ ^ 2 - 2 * ⟪x i, x j⟫_ℝ + ‖x j‖ ^ 2 :=
      norm_sub_sq_real (x i) (x j)
    rw [hnorm]
    ring
  have step1 : ∀ i ∈ t, ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2)
      = ((∑ j ∈ t, w i * w j * (‖x i‖ ^ 2)) - (∑ j ∈ t, w i * w j * (2 * ⟪x i, x j⟫_ℝ)))
        + (∑ j ∈ t, w i * w j * (‖x j‖ ^ 2)) := by
    intro i hi
    have hcongr : ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2)
        = ∑ j ∈ t, ((w i * w j * (‖x i‖ ^ 2)) - (w i * w j * (2 * ⟪x i, x j⟫_ℝ))
          + (w i * w j * (‖x j‖ ^ 2))) :=
      Finset.sum_congr rfl (fun j hj => hexpand i hi j hj)
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have stepA : ∀ i ∈ t, (∑ j ∈ t, w i * w j * (‖x i‖ ^ 2)) = w i * (‖x i‖ ^ 2) := by
    intro i _
    have hfac : (w i * (‖x i‖ ^ 2)) * (∑ j ∈ t, w j) = (∑ j ∈ t, w i * w j * (‖x i‖ ^ 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hw, mul_one] at hfac
    exact hfac.symm
  have stepB : ∀ i ∈ t, (∑ j ∈ t, w i * w j * (2 * ⟪x i, x j⟫_ℝ)) = w i * (2 * ⟪x i, c⟫_ℝ) := by
    intro i _
    have hfac : w i * (∑ j ∈ t, w j * (2 * ⟪x i, x j⟫_ℝ)) = (∑ j ∈ t, w i * w j * (2 * ⟪x i, x j⟫_ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [← hfac]
    congr 1
    have hinner : (∑ j ∈ t, w j * (2 * ⟪x i, x j⟫_ℝ)) = 2 * ⟪x i, c⟫_ℝ := by
      have hbase : (∑ j ∈ t, w j * ⟪x i, x j⟫_ℝ) = ⟪x i, c⟫_ℝ := by
        have h1 : ⟪x i, c⟫_ℝ = ∑ j ∈ t, ⟪x i, w j • x j⟫_ℝ := by
          rw [inner_sum]
        rw [h1]
        apply Finset.sum_congr rfl
        intro j _
        rw [inner_smul_right]
      have h2 : (∑ j ∈ t, w j * (2 * ⟪x i, x j⟫_ℝ)) = 2 * (∑ j ∈ t, w j * ⟪x i, x j⟫_ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h2, hbase]
    exact hinner
  set S := ∑ j ∈ t, w j * (‖x j‖ ^ 2) with hS
  have stepC : ∀ i ∈ t, (∑ j ∈ t, w i * w j * (‖x j‖ ^ 2)) = w i * S := by
    intro i _
    have hfac : w i * S = (∑ j ∈ t, w i * w j * (‖x j‖ ^ 2)) := by
      rw [hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact hfac.symm
  have inner_eq : ∀ i ∈ t, ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2)
      = w i * (‖x i‖ ^ 2) - w i * (2 * ⟪x i, c⟫_ℝ) + w i * S := by
    intro i hi
    rw [step1 i hi, stepA i hi, stepB i hi, stepC i hi]
  have outer : ∑ i ∈ t, ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2)
      = S + S - 2 * ⟪c, c⟫_ℝ := by
    have hcongr : ∑ i ∈ t, ∑ j ∈ t, w i * w j * (‖x i - x j‖ ^ 2)
        = ∑ i ∈ t, (w i * (‖x i‖ ^ 2) - w i * (2 * ⟪x i, c⟫_ℝ) + w i * S) :=
      Finset.sum_congr rfl (fun i hi => inner_eq i hi)
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hS1 : ∑ i ∈ t, w i * (‖x i‖ ^ 2) = S := rfl
    have hS2 : ∑ i ∈ t, w i * S = S := by
      rw [← Finset.sum_mul, hw, one_mul]
    have hmid : ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ) = 2 * ⟪c, c⟫_ℝ := by
      have hbase : ∑ i ∈ t, w i * ⟪x i, c⟫_ℝ = ⟪c, c⟫_ℝ := by
        have h1 : ⟪c, c⟫_ℝ = ∑ i ∈ t, ⟪w i • x i, c⟫_ℝ := by
          rw [sum_inner]
        rw [h1]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_smul_left]
        simp
      have h2 : ∑ i ∈ t, w i * (2 * ⟪x i, c⟫_ℝ) = 2 * ∑ i ∈ t, w i * ⟪x i, c⟫_ℝ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h2, hbase]
    rw [hS1, hS2, hmid]
    ring
  rw [outer, real_inner_self_eq_norm_sq]
  ring

-- Carathéodory's theorem in `EuclideanSpace ℝ (Fin n)`: every point of the convex hull
-- of `s` is a convex combination of a `Finset` of at most `n+1` points of `s`.
private lemma caratheodory {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ convexHull ℝ s) :
    ∃ (t : Finset (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n) → ℝ),
      ↑t ⊆ s ∧ (∀ y ∈ t, 0 ≤ w y) ∧ ∑ y ∈ t, w y = 1 ∧ (∑ y ∈ t, w y • y) = x ∧
      t.card ≤ n + 1 := by
  classical
  -- Step 0: normalize a `convexHull_eq` representation to weights on a `Finset E`.
  rw [_root_.convexHull_eq] at hx
  obtain ⟨ι, t₀, w₀, z, h0, h1, hmem, hcm⟩ := hx
  rw [Finset.centerMass_eq_of_sum_1 t₀ z h1] at hcm
  -- Pushforward weights onto the image `F₀ = t₀.image z`.
  set F₀ : Finset (EuclideanSpace ℝ (Fin n)) := t₀.image z with hF₀
  set wF : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => ∑ i ∈ t₀.filter (fun j => z j = y), w₀ i with hwF
  have hwF0 : ∀ y ∈ F₀, 0 ≤ wF y := by
    intro y _
    apply Finset.sum_nonneg
    intro i hi
    exact h0 i (Finset.mem_of_mem_filter i hi)
  have hfib : ∀ {M : Type} [AddCommMonoid M] (f : ι → M),
      ∑ y ∈ F₀, ∑ i ∈ t₀.filter (fun j => z j = y), f i = ∑ i ∈ t₀, f i := by
    intro M _ f
    have h := Finset.sum_fiberwise_of_maps_to (s := t₀) (t := F₀) (g := z)
      (fun i hi => hF₀ ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩) f
    simpa using h
  have hwF1 : ∑ y ∈ F₀, wF y = 1 := by
    have h := hfib w₀
    rwa [h1] at h
  have hwFb : (∑ y ∈ F₀, wF y • y) = x := by
    have h := hfib (fun i => w₀ i • z i)
    rw [hcm] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  have hF₀s : ↑F₀ ⊆ s := by
    intro y hy
    rw [hF₀] at hy
    rw [Finset.coe_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hmem i hi
  -- Step 1: choose a representation with minimal support cardinality.
  set P : ℕ → Prop := fun k => ∃ (F : Finset (EuclideanSpace ℝ (Fin n))) (w : _ → ℝ),
    ↑F ⊆ s ∧ (∀ y ∈ F, 0 ≤ w y) ∧ ∑ y ∈ F, w y = 1 ∧ (∑ y ∈ F, w y • y) = x ∧ F.card = k with hP
  have hex : ∃ k, P k := ⟨F₀.card, F₀, wF, hF₀s, hwF0, hwF1, hwFb, rfl⟩
  set k := Nat.find hex with hk
  obtain ⟨F, w, hFs, hw0, hw1, hbx, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ m, P m → k ≤ m := fun m hm => Nat.find_min' hex hm
  have hFne : F.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    simp at hw1
  -- Step 2: the support has at most `n+1` points, else affine dependence.
  have hle : F.card ≤ n + 1 := by
    by_contra hcon
    push Not at hcon
    -- Lifted vectors `(y, 1)` in `E × ℝ` are linearly dependent by cardinality.
    set v : ↥F → (EuclideanSpace ℝ (Fin n) × ℝ) := fun i => ((i : EuclideanSpace ℝ (Fin n)), 1) with hv
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) = n + 1 := by
      rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin, Module.finrank_self]
    have hdep : ¬ LinearIndependent ℝ v := by
      intro hLI
      have h := hLI.fintype_card_le_finrank
      rw [hfr, Fintype.card_coe] at h
      omega
    obtain ⟨c, hcsum, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hdep
    -- The relation gives `∑ c = 0` and `∑ c • y = 0`.
    have hcsnd : ∑ i : ↥F, c i = 0 := by
      have h : (LinearMap.snd ℝ _ _) (∑ i, c i • v i) = ∑ i, c i := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [hv]
      rw [hcsum, map_zero] at h
      exact h.symm
    have hcfst : ∑ i : ↥F, c i • (i : EuclideanSpace ℝ (Fin n)) = 0 := by
      have h : (LinearMap.fst ℝ _ _) (∑ i, c i • v i) = ∑ i, c i • (i : EuclideanSpace ℝ (Fin n)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp [hv]
      rw [hcsum, map_zero] at h
      exact h.symm
    -- Some coefficient is positive (they sum to zero but are not all zero).
    have hpos : ∃ i : ↥F, 0 < c i := by
      by_contra hall
      push Not at hall
      have hall0 : ∀ i : ↥F, c i = 0 := by
        have hneg : ∑ i : ↥F, c i = 0 := hcsnd
        have := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (f := fun i => -(c i))
          (fun i _ => by linarith [hall i])).mp (by simpa using hneg)
        intro i
        have := this i (Finset.mem_univ i)
        linarith
      exact hj (hall0 j)
    -- Ratio trick: subtract a multiple of `c` to kill one weight, keeping the rest ≥ 0.
    set S := Finset.univ.filter (fun i : ↥F => 0 < c i) with hS
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ := hpos
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    set r : ↥F → ℝ := fun i => w i / c i with hr
    set μ : ℝ := (S.image r).min' (Finset.image_nonempty.mpr hSne) with hμ
    obtain ⟨j₀, hj₀S, hj₀r⟩ : ∃ j₀ ∈ S, r j₀ = μ := by
      have := Finset.min'_mem (S.image r) (Finset.image_nonempty.mpr hSne)
      rw [Finset.mem_image] at this
      obtain ⟨j₀, hj₀S, hj₀r⟩ := this
      exact ⟨j₀, hj₀S, hj₀r⟩
    have hj₀c : 0 < c j₀ := (Finset.mem_filter.mp hj₀S).2
    have hj₀F : (j₀ : EuclideanSpace ℝ (Fin n)) ∈ F := j₀.2
    have hμnn : 0 ≤ μ := by
      rw [← hj₀r, hr]
      apply div_nonneg (hw0 _ hj₀F) (le_of_lt hj₀c)
    have hwj₀ : w j₀ = μ * c j₀ := by
      rw [← hj₀r, hr, div_mul_cancel₀ _ (ne_of_gt hj₀c)]
    -- New weights on `F.erase j₀`.
    set w' : ↥F → ℝ := fun i => w i - μ * c i with hw'
    have hw'j₀ : w' j₀ = 0 := by simp [hw', hwj₀, sub_eq_zero.mpr]
    have hsumw' : ∑ i : ↥F, w' i = 1 := by
      have e1 : ∀ i : ↥F, w' i = w i - μ * c i := fun i => by rw [hw']
      have hstep : ∑ i : ↥F, w' i = (∑ i : ↥F, w i) - μ * (∑ i : ↥F, c i) := by
        trans ∑ i : ↥F, (w i - μ * c i)
        · exact Finset.sum_congr rfl (fun i _ => e1 i)
        · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hstep, hcsnd, mul_zero, sub_zero]
      have hww : ∑ i : ↥F, w i = 1 := by
        have h := Finset.sum_attach F w
        rw [← Finset.univ_eq_attach] at h
        rw [h]
        exact hw1
      exact hww
    have hbaryw' : ∑ i : ↥F, w' i • (i : EuclideanSpace ℝ (Fin n)) = x := by
      have e1 : ∀ i : ↥F, w' i • (i : EuclideanSpace ℝ (Fin n))
          = w i • (i : EuclideanSpace ℝ (Fin n)) - μ • (c i • (i : EuclideanSpace ℝ (Fin n))) := by
        intro i
        rw [hw', sub_smul, mul_smul]
      have hstep : ∑ i : ↥F, w' i • (i : EuclideanSpace ℝ (Fin n))
          = (∑ i : ↥F, w i • (i : EuclideanSpace ℝ (Fin n)))
            - μ • (∑ i : ↥F, c i • (i : EuclideanSpace ℝ (Fin n))) := by
        trans ∑ i : ↥F, (w i • (i : EuclideanSpace ℝ (Fin n)) - μ • (c i • (i : EuclideanSpace ℝ (Fin n))))
        · exact Finset.sum_congr rfl (fun i _ => e1 i)
        · rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [hstep, hcfst, smul_zero, sub_zero]
      have hbb : ∑ i : ↥F, w i • (i : EuclideanSpace ℝ (Fin n)) = x := by
        have h := Finset.sum_attach F (fun y => w y • y)
        rw [← Finset.univ_eq_attach] at h
        rw [h]
        exact hbx
      exact hbb
    -- Assemble the smaller valid representation.
    set F' : Finset (EuclideanSpace ℝ (Fin n)) := F.erase (j₀ : EuclideanSpace ℝ (Fin n)) with hF'
    set W' : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun y => if h : y ∈ F then w' ⟨y, h⟩ else 0 with hW'
    have hW'sub : ↑F' ⊆ s := Set.Subset.trans (Finset.coe_subset.mpr (Finset.erase_subset _ _)) hFs
    have hW'0 : ∀ y ∈ F', 0 ≤ W' y := by
      intro y hy
      have hyF : y ∈ F := Finset.mem_of_mem_erase hy
      have heq : W' y = w' ⟨y, hyF⟩ := by simp [hW', hyF]
      rw [heq]
      show 0 ≤ w' ⟨y, hyF⟩
      by_cases hci : c ⟨y, hyF⟩ ≤ 0
      · have := hw0 y hyF
        simp [hw']
        linarith [mul_nonpos_of_nonneg_of_nonpos hμnn hci]
      · push Not at hci
        have hmem : ⟨y, hyF⟩ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩
        have hmemS : r ⟨y, hyF⟩ ∈ S.image r :=
          Finset.mem_image.mpr ⟨⟨y, hyF⟩, hmem, rfl⟩
        have hle2 : μ ≤ w y / c ⟨y, hyF⟩ :=
          Finset.min'_le (S.image r) (r ⟨y, hyF⟩) hmemS
        have hcy : w y - μ * c ⟨y, hyF⟩ ≥ 0 := by
          have hle3 := (le_div_iff₀ hci).mp hle2
          linarith
        simpa [hw'] using hcy
    -- Sum/barycenter transfer: `W'` agrees with `w'` on `F`, vanishes outside.
    have hUF : ∑ y ∈ F, W' y = ∑ i : ↥F, w' i := by
      have h := Finset.sum_attach F (fun y => W' y)
      rw [← Finset.univ_eq_attach] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro a _
      have hea : W' (↑a) = w' a := by simp [hW', a.2]
      rw [hea]
    have hUbF : (∑ y ∈ F, W' y • y) = ∑ i : ↥F, w' i • (i : EuclideanSpace ℝ (Fin n)) := by
      have h := Finset.sum_attach F (fun y => W' y • y)
      rw [← Finset.univ_eq_attach] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro a _
      have hea : W' (↑a) = w' a := by simp [hW', a.2]
      rw [hea]
    have hW'j₀ : W' (j₀ : EuclideanSpace ℝ (Fin n)) = 0 := by
      simp [hW', hj₀F, hw'j₀]
    have hW'1 : ∑ y ∈ F', W' y = 1 := by
      have h := Finset.sum_erase_add F W' hj₀F
      rw [hW'j₀, add_zero, hUF, hsumw'] at h
      rw [hF']
      exact h
    have hW'b : (∑ y ∈ F', W' y • y) = x := by
      have h := Finset.sum_erase_add F (fun y => W' y • y) hj₀F
      have hzero : W' (j₀ : EuclideanSpace ℝ (Fin n)) • (j₀ : EuclideanSpace ℝ (Fin n)) = 0 := by
        rw [hW'j₀, zero_smul]
      rw [hzero, add_zero, hUbF, hbaryw'] at h
      rw [hF']
      exact h
    have hcard' : F'.card = F.card - 1 := Finset.card_erase_of_mem hj₀F
    have hP' : P F'.card := ⟨F', W', hW'sub, hW'0, hW'1, hW'b, rfl⟩
    have hkle : k ≤ F'.card := hmin _ hP'
    have hFpos : 1 ≤ F.card := Finset.card_pos.mpr hFne
    have hkk : k = F.card := hk.trans hcard.symm
    omega
  -- The minimal representation already has at most `n+1` points.
  exact ⟨F, w, hFs, hw0, hw1, hbx, hle⟩

-- The farthest-distance values over a compact set are bounded above.
private lemma sup_dist_bdd {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hne : K.Nonempty) (c : EuclideanSpace ℝ (Fin n)) :
    BddAbove (Set.range (fun x : K => dist (x : EuclideanSpace ℝ (Fin n)) c)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hKb : Bornology.IsBounded K := hK.isBounded
  refine ⟨Metric.diam K + dist x₀ c, ?_⟩
  rintro _ ⟨x, rfl⟩
  calc dist (x : EuclideanSpace ℝ (Fin n)) c
      ≤ dist (x : EuclideanSpace ℝ (Fin n)) x₀ + dist x₀ c := dist_triangle _ _ _
    _ ≤ Metric.diam K + dist x₀ c := by
        have h := Metric.dist_le_diam_of_mem hKb x.2 hx₀
        linarith

-- The farthest-distance function `c ↦ ⨆ x : K, dist x c` is 1-Lipschitz.
private lemma lipschitz_sup_dist {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hne : K.Nonempty) :
    LipschitzWith 1 (fun c => ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c) := by
  haveI := hne.to_subtype
  have key : ∀ a b : EuclideanSpace ℝ (Fin n),
      (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) a)
        - (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) b) ≤ dist a b := by
    intro a b
    rw [sub_le_iff_le_add, add_comm (dist a b)]
    apply ciSup_le
    intro x
    calc dist (x : EuclideanSpace ℝ (Fin n)) a
        ≤ dist (x : EuclideanSpace ℝ (Fin n)) b + dist b a := dist_triangle _ _ _
      _ = dist (x : EuclideanSpace ℝ (Fin n)) b + dist a b := by rw [dist_comm b a]
      _ ≤ (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) b) + dist a b := by
          gcongr
          exact le_ciSup (sup_dist_bdd hK hne b) x
  rw [lipschitzWith_iff_dist_le_mul]
  intro c₁ c₂
  simp only [NNReal.coe_one, one_mul]
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨key c₁ c₂, by rw [dist_comm c₁ c₂]; exact key c₂ c₁⟩

-- Existence of a global minimizer of the farthest-distance function:
-- the centre of a minimal enclosing ball.
private lemma exists_min_ball {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ cstar : EuclideanSpace ℝ (Fin n),
      ∀ c : EuclideanSpace ℝ (Fin n),
        (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar)
          ≤ ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c := by
  have ⟨x₀, hx₀⟩ := hne
  have hcont : Continuous (fun c => ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c) :=
    (lipschitz_sup_dist hK hne).continuous
  set M := Metric.diam K + 1 with hM
  have hDnn : (0 : ℝ) ≤ Metric.diam K := Metric.diam_nonneg
  have hx₀mem : x₀ ∈ Metric.closedBall x₀ M := by
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hfx₀ : (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) x₀) ≤ Metric.diam K := by
    haveI := hne.to_subtype
    apply ciSup_le
    intro x
    exact Metric.dist_le_diam_of_mem hK.isBounded x.2 hx₀
  obtain ⟨cstar, _, hmin⟩ := IsCompact.exists_isMinOn
    (isCompact_closedBall x₀ M) ⟨x₀, hx₀mem⟩ hcont.continuousOn
  refine ⟨cstar, fun c => ?_⟩
  by_cases hc : c ∈ Metric.closedBall x₀ M
  · exact hmin hc
  · have hdc : M < dist x₀ c := by
      have h : ¬ dist c x₀ ≤ M := fun hle => hc (Metric.mem_closedBall.mpr hle)
      rw [dist_comm]
      exact lt_of_not_ge h
    have hlt : (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar)
        < ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c := calc
      (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar)
        ≤ ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) x₀ := hmin hx₀mem
      _ ≤ Metric.diam K := hfx₀
      _ < M := by rw [hM]; linarith
      _ ≤ dist x₀ c := hdc.le
      _ ≤ ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c :=
          le_ciSup (sup_dist_bdd hK hne c) ⟨x₀, hx₀⟩
    exact hlt.le

-- The minimal radius is attained at a contact point.
private lemma contact_attained {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hne : K.Nonempty) (cstar : EuclideanSpace ℝ (Fin n)) :
    ∃ xstar : EuclideanSpace ℝ (Fin n), xstar ∈ K ∧
      dist xstar cstar = ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar := by
  have hcont : ContinuousOn (fun x => dist x cstar) K :=
    (continuous_id.dist continuous_const).continuousOn
  obtain ⟨xstar, hxstar, hmax⟩ := IsCompact.exists_isMaxOn hK hne hcont
  refine ⟨xstar, hxstar, ?_⟩
  apply le_antisymm
  · exact le_ciSup (sup_dist_bdd hK hne cstar) ⟨xstar, hxstar⟩
  · haveI := hne.to_subtype
    apply ciSup_le
    intro x
    exact hmax x.2

-- Strict separation of an exterior centre from the convex hull of contact points
-- yields a uniform gap direction.
private lemma sep_gap {n : ℕ} {T : Set (EuclideanSpace ℝ (Fin n))}
    (hT : IsCompact T) {cstar : EuclideanSpace ℝ (Fin n)}
    (hnotin : cstar ∉ convexHull ℝ T) :
    ∃ w : EuclideanSpace ℝ (Fin n), ∃ ε : ℝ,
      0 < ε ∧ ∀ y ∈ T, ε ≤ ⟪y - cstar, w⟫_ℝ := by
  have hDconv : Convex ℝ (convexHull ℝ T) := convex_convexHull ℝ T
  have hDclosed : IsClosed (convexHull ℝ T) :=
    (MathlibExt.Analysis.Convex.Straszewicz.IsCompact.convexHull_of_compact hT).isClosed
  obtain ⟨f, u, hfu, hf⟩ := geometric_hahn_banach_point_closed hDconv hDclosed hnotin
  set w : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ _).symm f with hw
  refine ⟨w, u - f cstar, sub_pos.mpr hfu, fun y hy => ?_⟩
  have hyD : y ∈ convexHull ℝ T := subset_convexHull ℝ T hy
  have hlt : u < f y := hf y hyD
  have hinner : ⟪y - cstar, w⟫_ℝ = f y - f cstar := by
    rw [real_inner_comm, ← map_sub]
    exact InnerProductSpace.toDual_symm_apply
  rw [hinner]
  linarith

-- Improvement step: a uniform gap direction lets us move the centre and shrink the
-- maximal distance, contradicting minimality. Hence the minimal centre lies in the
-- convex hull of the contact set.
private lemma improve_contra {n : ℕ} {K T : Set (EuclideanSpace ℝ (Fin n))}
    {cstar : EuclideanSpace ℝ (Fin n)} {rstar : ℝ}
    (hK : IsCompact K) (hneK : K.Nonempty)
    (hneT : T.Nonempty)
    (hmax : ∀ y ∈ K, dist y cstar ≤ rstar)
    (hrstar : ∀ c, (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar)
      ≤ ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) c)
    (hrdef : rstar = ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar)
    (hr : ∀ y ∈ T, dist y cstar = rstar)
    (hmemT : ∀ y ∈ K, dist y cstar = rstar → y ∈ T)
    (w : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ y ∈ T, ε ≤ ⟪y - cstar, w⟫_ℝ) : False := by
  have ⟨y₀, hy₀⟩ := hneT
  -- The direction is nonzero and the radius is nonnegative.
  have hwne : w ≠ 0 := by
    intro hz
    have hle := hgap y₀ hy₀
    rw [hz, inner_zero_right] at hle
    linarith
  have hU : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
  have hU2 : (0 : ℝ) < ‖w‖ ^ 2 := by
    rw [pow_two]
    exact mul_pos hU hU
  have hrnn : 0 ≤ rstar := by
    have h := hr y₀ hy₀
    rw [← h]
    exact dist_nonneg
  -- Cauchy–Schwarz in the needed form.
  have hCS : ∀ a : EuclideanSpace ℝ (Fin n), ⟪a, w⟫_ℝ ≤ ‖a‖ * ‖w‖ := by
    intro a
    calc ⟪a, w⟫_ℝ ≤ |⟪a, w⟫_ℝ| := le_abs_self _
      _ = ‖⟪a, w⟫_ℝ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖a‖ * ‖w‖ := norm_inner_le_norm _ _
  set ρ : ℝ := ε / (2 * ‖w‖) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact div_pos hε (mul_pos two_pos hU)
  -- Points close to `T` still see a positive gap.
  have claim1 : ∀ x ∈ K, Metric.infDist x T < ρ → ε / 2 < ⟪x - cstar, w⟫_ℝ := by
    intro x hxK hdist
    by_contra hcon
    push Not at hcon
    have hfar : ∀ y ∈ T, ρ ≤ dist x y := by
      intro y hy
      have hsplit : ⟪y - x, w⟫_ℝ = ⟪y - cstar, w⟫_ℝ - ⟪x - cstar, w⟫_ℝ := by
        simp only [inner_sub_left]
        ring
      have hge : ε / 2 ≤ ⟪y - x, w⟫_ℝ := by
        rw [hsplit]
        have hgy := hgap y hy
        linarith
      have hnorm : ‖y - x‖ = dist x y := by
        rw [dist_eq_norm, norm_sub_rev]
      have hle : ε ≤ dist x y * (2 * ‖w‖) := by
        have h1 : ε / 2 ≤ ‖y - x‖ * ‖w‖ := le_trans hge (hCS _)
        rw [hnorm] at h1
        linarith
      rw [hρ, div_le_iff₀ (mul_pos two_pos hU)]
      exact hle
    have hle : ρ ≤ Metric.infDist x T :=
      (Metric.le_infDist hneT).mpr (fun y hy => hfar y hy)
    exact (not_le_of_gt hdist) hle
  -- Points far from `T` stay uniformly below the maximal squared distance.
  have claim2 : ∃ η : ℝ, 0 < η ∧ ∀ x ∈ K,
      rstar ^ 2 - ‖x - cstar‖ ^ 2 < η → Metric.infDist x T < ρ := by
    set Sρ : Set (EuclideanSpace ℝ (Fin n)) := {x ∈ K | ρ ≤ Metric.infDist x T} with hSρ
    have hSρc : IsCompact Sρ :=
      hK.inter_right (isClosed_le continuous_const (Metric.continuous_infDist_pt T))
    set g : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => rstar ^ 2 - ‖x - cstar‖ ^ 2 with hg
    have hgcont : ContinuousOn g Sρ := by
      apply Continuous.continuousOn
      simp only [hg]
      apply Continuous.sub continuous_const
      apply Continuous.pow
      apply Continuous.norm
      exact continuous_id.sub continuous_const
    by_cases hSρe : Sρ.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := IsCompact.exists_isMinOn hSρc hSρe hgcont
      have hx₀K : x₀ ∈ K := hx₀.1
      have hx₀ρ : ρ ≤ Metric.infDist x₀ T := hx₀.2
      have hstrict : ‖x₀ - cstar‖ < rstar := by
        have hle : ‖x₀ - cstar‖ ≤ rstar := by
          have h := hmax x₀ hx₀K
          rwa [dist_eq_norm] at h
        by_contra hcon
        push Not at hcon
        have heq : ‖x₀ - cstar‖ = rstar := le_antisymm hle hcon
        have hx₀d : dist x₀ cstar = rstar := by
          rw [dist_eq_norm]
          exact heq
        have hx₀T : x₀ ∈ T := hmemT x₀ hx₀K hx₀d
        have hzero : Metric.infDist x₀ T = 0 :=
          le_antisymm (by simpa using Metric.infDist_le_dist_of_mem (x := x₀) hx₀T)
            Metric.infDist_nonneg
        linarith
      have h1 : ‖x₀ - cstar‖ ^ 2 < rstar ^ 2 := by
        rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrnn]
        exact hstrict
      have hμpos : 0 < g x₀ := by
        have hgx : g x₀ = rstar ^ 2 - ‖x₀ - cstar‖ ^ 2 := rfl
        rw [hgx]
        linarith
      refine ⟨g x₀, hμpos, fun x hxK hlt => ?_⟩
      by_contra hcon2
      push Not at hcon2
      have hmem : x ∈ Sρ := ⟨hxK, hcon2⟩
      have hge : g x₀ ≤ g x := hmin hmem
      have hlt' : g x < g x₀ := hlt
      linarith
    · have hempty : Sρ = ∅ := Set.not_nonempty_iff_eq_empty.mp hSρe
      refine ⟨1, one_pos, fun x hxK hlt => ?_⟩
      have hmem : x ∉ Sρ := by
        simp [hempty]
      by_contra hcon2
      push Not at hcon2
      exact hmem ⟨hxK, hcon2⟩
  obtain ⟨η, hηpos, hη⟩ := claim2
  -- Moving `cstar` a little along `w` strictly decreases every squared distance.
  set M' : ℝ := 2 * rstar * ‖w‖ + ‖w‖ ^ 2 with hM'
  have hM'pos : 0 < M' := by
    rw [hM']
    have h1 : (0 : ℝ) ≤ 2 * rstar * ‖w‖ :=
      mul_nonneg (mul_nonneg zero_le_two hrnn) (norm_nonneg _)
    linarith [h1, hU2]
  set t : ℝ := min (min (η / M') (ε / ‖w‖ ^ 2)) 1 / 2 with ht
  have hmin1 : min (min (η / M') (ε / ‖w‖ ^ 2)) 1 ≤ η / M' :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : min (min (η / M') (ε / ‖w‖ ^ 2)) 1 ≤ ε / ‖w‖ ^ 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hm0 : 0 < min (min (η / M') (ε / ‖w‖ ^ 2)) 1 :=
    lt_min (lt_min (div_pos hηpos hM'pos) (div_pos hε hU2)) zero_lt_one
  have hηM : 0 < η / M' := div_pos hηpos hM'pos
  have hεU : 0 < ε / ‖w‖ ^ 2 := div_pos hε hU2
  have ht0 : 0 < t := by
    rw [ht]
    linarith [hm0]
  have htM : t < η / M' := by
    rw [ht]
    linarith [hmin1, hηM]
  have htE : t < ε / ‖w‖ ^ 2 := by
    rw [ht]
    linarith [hmin2, hεU]
  have ht1 : t ≤ 1 := by
    rw [ht]
    linarith [min_le_right (min (η / M') (ε / ‖w‖ ^ 2)) 1, hm0]
  have hexpand : ∀ x : EuclideanSpace ℝ (Fin n), ‖x - (cstar + t • w)‖ ^ 2
      = ‖x - cstar‖ ^ 2 - 2 * t * ⟪x - cstar, w⟫_ℝ + (t * ‖w‖) ^ 2 := by
    intro x
    have h1 : x - (cstar + t • w) = (x - cstar) - t • w := by abel
    rw [h1, norm_sub_sq_real]
    have h2 : ⟪x - cstar, t • w⟫_ℝ = t * ⟪x - cstar, w⟫_ℝ := inner_smul_right _ _ _
    have h3 : ‖t • w‖ = t * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rw [h2, h3]
    ring
  have hclose : ∀ x ∈ K, ‖x - (cstar + t • w)‖ ^ 2 < rstar ^ 2 := by
    intro x hxK
    rw [hexpand x]
    have hQ : ‖x - cstar‖ ^ 2 ≤ rstar ^ 2 := by
      have h := hmax x hxK
      rw [dist_eq_norm] at h
      exact sq_le_sq' (by linarith [hrnn, norm_nonneg (x - cstar)]) h
    by_cases hA : rstar ^ 2 - ‖x - cstar‖ ^ 2 < η
    · have hmem : Metric.infDist x T < ρ := hη x hxK hA
      have hJ : ε / 2 < ⟪x - cstar, w⟫_ℝ := claim1 x hxK hmem
      have he1 : t * ε < 2 * t * ⟪x - cstar, w⟫_ℝ := by
        have h := mul_lt_mul_of_pos_left (show ε < 2 * ⟪x - cstar, w⟫_ℝ by linarith) ht0
        have h' : t * (2 * ⟪x - cstar, w⟫_ℝ) = 2 * t * ⟪x - cstar, w⟫_ℝ := by ring
        linarith [h, h']
      have he2 : (t * ‖w‖) ^ 2 < t * ε := by
        have h1 : t * ‖w‖ ^ 2 < ε := (lt_div_iff₀ hU2).mp htE
        have h2 := mul_lt_mul_of_pos_left h1 ht0
        have h3 : (t * ‖w‖) ^ 2 = t * (t * ‖w‖ ^ 2) := by ring
        linarith [h2, h3]
      linarith [hQ, he1, he2]
    · push Not at hA
      have hj1 : -⟪x - cstar, w⟫_ℝ ≤ rstar * ‖w‖ := by
        have h1 : -⟪x - cstar, w⟫_ℝ ≤ |⟪x - cstar, w⟫_ℝ| := by
          rw [← abs_neg]
          exact le_abs_self _
        have hab : |⟪x - cstar, w⟫_ℝ| ≤ ‖x - cstar‖ * ‖w‖ := by
          calc |⟪x - cstar, w⟫_ℝ| = ‖⟪x - cstar, w⟫_ℝ‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖x - cstar‖ * ‖w‖ := norm_inner_le_norm _ _
        have hq : ‖x - cstar‖ ≤ rstar := by
          have h := hmax x hxK
          rwa [dist_eq_norm] at h
        have h2 : |⟪x - cstar, w⟫_ℝ| ≤ rstar * ‖w‖ :=
          le_trans hab (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
        linarith [h1, h2]
      have h2t : -(2 * t * ⟪x - cstar, w⟫_ℝ) ≤ 2 * t * (rstar * ‖w‖) := by
        have h2t0 : (0 : ℝ) ≤ 2 * t := by linarith [ht0]
        have h := mul_le_mul_of_nonneg_left hj1 h2t0
        have e1 : (2 * t) * (-⟪x - cstar, w⟫_ℝ) = -(2 * t * ⟪x - cstar, w⟫_ℝ) := by ring
        have e2 : (2 * t) * (rstar * ‖w‖) = 2 * t * (rstar * ‖w‖) := by ring
        linarith [h, e1, e2]
      have htu : (t * ‖w‖) ^ 2 ≤ t * ‖w‖ ^ 2 := by
        have ht2 : t ^ 2 ≤ t := by
          have h := mul_le_mul_of_nonneg_left ht1 ht0.le
          rw [mul_one] at h
          rw [pow_two]
          exact h
        calc (t * ‖w‖) ^ 2 = t ^ 2 * ‖w‖ ^ 2 := by ring
          _ ≤ t * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right ht2 (sq_nonneg _)
      have htM' : t * M' < η := (lt_div_iff₀ hM'pos).mp htM
      have eM : t * M' = 2 * t * (rstar * ‖w‖) + t * ‖w‖ ^ 2 := by
        rw [hM']
        ring
      linarith [hQ, hA, h2t, htu, htM', eM]
  -- The improved centre contradicts minimality.
  have hcont_g : Continuous (fun x => ‖x - (cstar + t • w)‖ ^ 2) :=
    (((continuous_id.sub continuous_const).norm).pow 2)
  obtain ⟨xhat, hxhatK, hmaxG⟩ := IsCompact.exists_isMaxOn hK hneK hcont_g.continuousOn
  have hG : ‖xhat - (cstar + t • w)‖ ^ 2 < rstar ^ 2 := hclose xhat hxhatK
  have hdist : ∀ x ∈ K, dist x (cstar + t • w)
      ≤ Real.sqrt (‖xhat - (cstar + t • w)‖ ^ 2) := by
    intro x hxK
    have hle : ‖x - (cstar + t • w)‖ ^ 2 ≤ ‖xhat - (cstar + t • w)‖ ^ 2 := hmaxG hxK
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (x - (cstar + t • w)))]
    exact Real.sqrt_le_sqrt hle
  have hsup : (⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) (cstar + t • w))
      ≤ Real.sqrt (‖xhat - (cstar + t • w)‖ ^ 2) := by
    haveI := hneK.to_subtype
    apply ciSup_le
    intro x
    exact hdist x x.2
  have hsqrt : Real.sqrt (‖xhat - (cstar + t • w)‖ ^ 2) < rstar :=
    calc Real.sqrt (‖xhat - (cstar + t • w)‖ ^ 2)
        < Real.sqrt (rstar ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) hG
      _ = rstar := Real.sqrt_sq hrnn
  have hmin2 := hrstar (cstar + t • w)
  rw [← hrdef] at hmin2
  linarith [hmin2, hsup, hsqrt]

/--
**Jung's theorem.** Let $n \ge 1$ and let $s$ be a bounded subset of the Euclidean space
$\mathbb{R}^n$ with diameter $\operatorname{diam} s$. Then there is a point $c \in \mathbb{R}^n$
such that $s$ is contained in the closed ball with center $c$ and radius
$\sqrt{n / (2(n + 1))} \cdot \operatorname{diam} s$.

Source: H. Jung, Über die kleinste Kugel, die eine räumliche Figur einschließt, J. Reine Angew.
Math. 123 (1901) 241–257 original theorem; D. Gale sharp Euclidean formulation; standard modern
reference M. Berger, Geometry I & II.
Proves `Wanted` entry `jung`.
-/
theorem jung
    {n : ℕ} (hn : 0 < n)
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (hs : Bornology.IsBounded s) :
    ∃ c : EuclideanSpace ℝ (Fin n),
      s ⊆ Metric.closedBall c (Real.sqrt ((n : ℝ) / (2 * ((n : ℝ) + 1))) * Metric.diam s) := by
  -- Degenerate cases are handled directly; the general case chains the algebraic
  -- identities above with a minimal enclosing ball whose centre is a convex
  -- combination of at most n+1 boundary points (via Carathéodory).
  by_cases hempty : s = ∅
  · exact ⟨0, by simp [hempty]⟩
  · by_cases hsub : s.Subsingleton
    · -- diam s = 0; any point of s is a valid centre with radius 0.
      have hdiam : Metric.diam s = 0 := Metric.diam_subsingleton hsub
      have ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      refine ⟨x, ?_⟩
      intro y hy
      have hsub' : y = x := hsub hy hx
      subst hsub'
      rw [Metric.mem_closedBall, dist_self, hdiam, mul_zero]
    · -- General bounded non-degenerate case.
      have hne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
      -- Work with the compact closure `K`.
      set K : Set (EuclideanSpace ℝ (Fin n)) := closure s with hKdef
      have hKb : Bornology.IsBounded K := hs.closure
      have hKc : IsCompact K := hs.isCompact_closure
      have hneK : K.Nonempty := hne.mono subset_closure
      have ⟨x₀K, hx₀K⟩ := hneK
      -- Minimal enclosing ball centre and radius.
      obtain ⟨cstar, hmin⟩ := exists_min_ball hKc hneK
      set rstar : ℝ := ⨆ x : K, dist (x : EuclideanSpace ℝ (Fin n)) cstar with hrdef
      have hrnnK : 0 ≤ rstar :=
        le_trans dist_nonneg (le_ciSup (sup_dist_bdd hKc hneK cstar) ⟨x₀K, hx₀K⟩)
      have hcover : K ⊆ Metric.closedBall cstar rstar :=
        fun y hy => Metric.mem_closedBall.mpr
          (le_ciSup (sup_dist_bdd hKc hneK cstar) ⟨y, hy⟩)
      have hmax : ∀ y ∈ K, dist y cstar ≤ rstar :=
        fun y hy => Metric.mem_closedBall.mp (hcover hy)
      -- Contact set.
      set T : Set (EuclideanSpace ℝ (Fin n)) :=
        K ∩ {x | dist x cstar = rstar} with hTdef
      have hTne : T.Nonempty := by
        obtain ⟨xstar, hxstar, hdist⟩ := contact_attained hKc hneK cstar
        exact ⟨xstar, hxstar, hdist⟩
      have hTc : IsCompact T := by
        have h : IsCompact (K ∩ {x : EuclideanSpace ℝ (Fin n) | dist x cstar = rstar}) :=
          hKc.inter_right
            (isClosed_eq (continuous_id.dist continuous_const) continuous_const)
        exact h
      have hr : ∀ y ∈ T, dist y cstar = rstar := fun y hy => hy.2
      have hmemT : ∀ y ∈ K, dist y cstar = rstar → y ∈ T :=
        fun y hyK hd => ⟨hyK, hd⟩
      -- The centre is a convex combination of contact points.
      have hmem : cstar ∈ convexHull ℝ T := by
        by_contra hcon
        obtain ⟨w, ε, hε, hgap⟩ := sep_gap hTc hcon
        exact improve_contra hKc hneK hTne hmax hmin rfl hr hmemT w ε hε hgap
      obtain ⟨F, wgt, hFs, hw0, hw1, hbx, hle⟩ := caratheodory hmem
      have hFne : F.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        subst hemp
        simp at hw1
      have hcard_pos : (0 : ℝ) < (F.card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr hFne)
      -- Every support point is at distance exactly `rstar` from the centre.
      have hyc : ∀ y ∈ F, ‖y - cstar‖ = rstar := by
        intro y hy
        have hyT : y ∈ T := hFs hy
        have hd : dist y cstar = rstar := hr y hyT
        rwa [dist_eq_norm] at hd
      -- Left-hand side of the variance identity equals `rstar ^ 2`.
      have eLHS : (∑ y ∈ F, wgt y * (‖y - cstar‖ ^ 2)) = rstar ^ 2 := by
        have e : ∀ y ∈ F, wgt y * (‖y - cstar‖ ^ 2) = wgt y * rstar ^ 2 := by
          intro y hy
          rw [hyc y hy]
        rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hw1, one_mul]
      -- Variance + pairwise identities with the barycentre rewritten to `cstar`.
      have hbx' : (∑ i ∈ F, wgt i • (fun a : EuclideanSpace ℝ (Fin n) => a) i)
          = cstar := hbx
      have hvar0 := variance_identity F wgt (fun y : EuclideanSpace ℝ (Fin n) => y) hw1
      have hvar1 : (∑ y ∈ F, wgt y * (‖y - (∑ i ∈ F, wgt i • (fun a : EuclideanSpace ℝ (Fin n) => a) i)‖ ^ 2))
          = (∑ y ∈ F, wgt y * (‖y‖ ^ 2))
            - ‖(∑ i ∈ F, wgt i • (fun a : EuclideanSpace ℝ (Fin n) => a) i)‖ ^ 2 := hvar0
      rw [hbx'] at hvar1
      have hpair0 := pairwise_identity F wgt (fun y : EuclideanSpace ℝ (Fin n) => y) hw1
      have hpair1 : (∑ y ∈ F, wgt y * (‖y‖ ^ 2))
            - ‖(∑ i ∈ F, wgt i • (fun a : EuclideanSpace ℝ (Fin n) => a) i)‖ ^ 2
          = (1 / 2) * ∑ i ∈ F, ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2) := hpair0
      rw [hbx'] at hpair1
      -- The double sum is bounded by `D ^ 2 * (1 - ∑ w ^ 2)`.
      have hper : ∀ i ∈ F, ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2)
          ≤ wgt i * (Metric.diam K) ^ 2 * (1 - wgt i) := by
        intro i hi
        have hdiag : wgt i * wgt i * (‖i - i‖ ^ 2) = 0 := by simp
        have hsplit : ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2)
            = ∑ j ∈ F.erase i, wgt i * wgt j * (‖i - j‖ ^ 2) := by
          have h := Finset.sum_erase_add F (fun j => wgt i * wgt j * (‖i - j‖ ^ 2)) hi
          rw [hdiag, add_zero] at h
          exact h.symm
        rw [hsplit]
        have hterm : ∀ j ∈ F.erase i,
            wgt i * wgt j * (‖i - j‖ ^ 2) ≤ wgt i * wgt j * (Metric.diam K) ^ 2 := by
          intro j hj
          have hjF : j ∈ F := Finset.mem_of_mem_erase hj
          have hnn : 0 ≤ wgt i * wgt j := mul_nonneg (hw0 i hi) (hw0 j hjF)
          have hd : ‖i - j‖ ^ 2 ≤ (Metric.diam K) ^ 2 := by
            have hiK : i ∈ K := (hFs hi).1
            have hjK : j ∈ K := (hFs hjF).1
            have h1 : dist i j ≤ Metric.diam K :=
              Metric.dist_le_diam_of_mem hKb hiK hjK
            rw [dist_eq_norm] at h1
            have h2 : (0 : ℝ) ≤ ‖i - j‖ := norm_nonneg _
            have h3 : (0 : ℝ) ≤ Metric.diam K := Metric.diam_nonneg
            nlinarith [h1, h2, h3, mul_nonneg h2 h3, mul_nonneg (sub_nonneg.mpr h1) (add_nonneg h3 h2)]
          exact mul_le_mul_of_nonneg_left hd hnn
        have hle2 : ∑ j ∈ F.erase i, wgt i * wgt j * (‖i - j‖ ^ 2)
            ≤ ∑ j ∈ F.erase i, wgt i * wgt j * (Metric.diam K) ^ 2 :=
          Finset.sum_le_sum hterm
        have hfac : (∑ j ∈ F.erase i, wgt i * wgt j * (Metric.diam K) ^ 2)
            = wgt i * (Metric.diam K) ^ 2 * (∑ j ∈ F.erase i, wgt j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        have hsum1 : (∑ j ∈ F.erase i, wgt j) = 1 - wgt i := by
          have h := Finset.sum_erase_add F wgt hi
          rw [hw1] at h
          linarith [h]
        calc ∑ j ∈ F.erase i, wgt i * wgt j * (‖i - j‖ ^ 2)
            ≤ ∑ j ∈ F.erase i, wgt i * wgt j * (Metric.diam K) ^ 2 := hle2
          _ = wgt i * (Metric.diam K) ^ 2 * (∑ j ∈ F.erase i, wgt j) := hfac
          _ = wgt i * (Metric.diam K) ^ 2 * (1 - wgt i) := by rw [hsum1]
      have htotal : (∑ i ∈ F, ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2))
          ≤ (Metric.diam K) ^ 2 * (1 - ∑ j ∈ F, (wgt j) ^ 2) := by
        have e : (∑ i ∈ F, wgt i * (Metric.diam K) ^ 2 * (1 - wgt i))
            = (Metric.diam K) ^ 2 * ∑ i ∈ F, (wgt i - (wgt i) ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        calc (∑ i ∈ F, ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2))
            ≤ ∑ i ∈ F, wgt i * (Metric.diam K) ^ 2 * (1 - wgt i) :=
              Finset.sum_le_sum hper
          _ = (Metric.diam K) ^ 2 * ∑ i ∈ F, (wgt i - (wgt i) ^ 2) := e
          _ = (Metric.diam K) ^ 2 * (1 - ∑ j ∈ F, (wgt j) ^ 2) := by
              rw [Finset.sum_sub_distrib, hw1]
      -- Chaining with `1 - ∑ w ^ 2 ≤ n / (n + 1)`.
      have hwbound : (1 : ℝ) / (F.card : ℝ) ≤ ∑ i ∈ F, (wgt i) ^ 2 :=
        weight_sq_sum_ge F wgt hw1
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
      have hleR : (F.card : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast hle
      have hfrac : (1 : ℝ) - ∑ i ∈ F, (wgt i) ^ 2 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
        have h1 : (1 : ℝ) - ∑ i ∈ F, (wgt i) ^ 2
            ≤ ((F.card : ℝ) - 1) / (F.card : ℝ) := by
          have hb : (1 : ℝ) ≤ (∑ i ∈ F, (wgt i) ^ 2) * (F.card : ℝ) := by
            have h := (div_le_iff₀ hcard_pos).mp hwbound
            linarith [h]
          have e : ((F.card : ℝ) - 1) / (F.card : ℝ) = 1 - 1 / (F.card : ℝ) := by
            field_simp
          rw [e]
          linarith [hb, hwbound]
        have h2 : ((F.card : ℝ) - 1) / (F.card : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by
          rw [div_le_div_iff₀ hcard_pos (by linarith [hnR])]
          have e : ((F.card : ℝ) - 1) * ((n : ℝ) + 1)
              = (n : ℝ) * (F.card : ℝ) + ((F.card : ℝ) - ((n : ℝ) + 1)) := by ring
          rw [e]
          linarith [hleR]
        linarith [h1, h2]
      have e1 : rstar ^ 2
          = (1 / 2) * ∑ i ∈ F, ∑ j ∈ F, wgt i * wgt j * (‖i - j‖ ^ 2) := by
        rw [← eLHS, hvar1, hpair1]
      have hstep1 : rstar ^ 2
          ≤ (1 / 2) * ((Metric.diam K) ^ 2 * (1 - ∑ i ∈ F, (wgt i) ^ 2)) := by
        rw [e1]
        exact mul_le_mul_of_nonneg_left htotal (by norm_num)
      have hstep2 : (1 / 2) * ((Metric.diam K) ^ 2 * (1 - ∑ i ∈ F, (wgt i) ^ 2))
          ≤ (1 / 2) * ((Metric.diam K) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfrac (sq_nonneg _)) (by norm_num)
      have hfinal : rstar ^ 2
          ≤ (1 / 2) * ((Metric.diam K) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1))) :=
        le_trans hstep1 hstep2
      -- Take square roots.
      have hX : (0 : ℝ) ≤ (n : ℝ) / (2 * ((n : ℝ) + 1)) :=
        div_nonneg hnR.le (by linarith [hnR])
      have hn1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by linarith [hnR])
      have key : ((n : ℝ) / (2 * ((n : ℝ) + 1))) * (Metric.diam K) ^ 2
          = (1 / 2) * ((Metric.diam K) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1))) := by
        field_simp
      have hsq : (Real.sqrt ((n : ℝ) / (2 * ((n : ℝ) + 1))) * Metric.diam K) ^ 2
          = (1 / 2) * ((Metric.diam K) ^ 2 * ((n : ℝ) / ((n : ℝ) + 1))) := by
        rw [mul_pow, Real.sq_sqrt hX]
        exact key
      have hfin : rstar ^ 2
          ≤ ((n : ℝ) / (2 * ((n : ℝ) + 1))) * (Metric.diam K) ^ 2 := by
        linarith [hfinal, key]
      have hr_le : rstar
          ≤ Real.sqrt ((n : ℝ) / (2 * ((n : ℝ) + 1))) * Metric.diam K := by
        have h := (Real.le_sqrt hrnnK (mul_nonneg hX (sq_nonneg _))).mpr hfin
        rwa [Real.sqrt_mul hX _, Real.sqrt_sq Metric.diam_nonneg] at h
      -- Transfer from `K` back to `s`.
      rw [hKdef, Metric.diam_closure] at hr_le
      refine ⟨cstar, fun y hy => ?_⟩
      have hyK : y ∈ K := subset_closure hy
      have h1 : y ∈ Metric.closedBall cstar rstar := hcover hyK
      exact Metric.closedBall_subset_closedBall hr_le h1

end MathlibExt.Geometry.Euclidean.JungWanted
