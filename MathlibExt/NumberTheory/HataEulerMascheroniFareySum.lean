/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathlibExt.NumberTheory.HataEulerMascheroniFarey
import MathlibExt.NumberTheory.HataEulerMascheroniFareyRiemannSum

/-!
# Summation over the Farey subintervals of a reciprocal interval

Mediant subdivision enumerates the Farey subintervals without repetition. The sum of the
mediant defects above a given depth is the root weight minus the sum of the weights at that
depth. The Riemann-sum error tends to zero as the mesh tends to zero.

## References

* Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the Euler-Mascheroni
  Constant*, INTEGERS 25 (2025), Article A90, pp. 1–6, §2, Lemmas 1–3.
-/

namespace MetaMathlibExt

open Filter Finset
open scoped BigOperators Topology

private abbrev Quad := ℕ × ℕ × ℕ × ℕ

private def InReciprocal (n : ℕ) : Quad → Prop
  | (a, b, c, d) => b * c = a * d + 1 ∧ b ≤ (n + 1) * a ∧ n * c ≤ d

private abbrev FareyNode (n : ℕ) := {q : Quad // InReciprocal n q}

private theorem numerators_pos {n a b c d : ℕ} (h : InReciprocal n (a, b, c, d)) :
    0 < a ∧ 0 < b ∧ 0 < c := by
  obtain ⟨hdet, hl, _⟩ := h
  have hbc : 0 < b * c := hdet ▸ Nat.succ_pos _
  have hb := Nat.pos_of_mul_pos_right hbc
  refine ⟨Nat.pos_of_mul_pos_left (hb.trans_le hl), hb, Nat.pos_of_mul_pos_left hbc⟩

private theorem right_den_pos {n a b c d : ℕ} (hn : 0 < n)
    (h : InReciprocal n (a, b, c, d)) : 0 < d :=
  (Nat.mul_pos hn (numerators_pos h).2.2).trans_le h.2.2

private theorem inner_bounds {n a b c d : ℕ} (h : InReciprocal n (a, b, c, d)) :
    n * a < b ∧ d < (n + 1) * c := by
  obtain ⟨hdet, hl, hr⟩ := h
  constructor
  · by_contra! hb
    have h₁ := Nat.mul_le_mul_right c hb
    have h₂ := Nat.mul_le_mul_left a hr
    have hcomm : n * a * c = a * (n * c) := by ac_rfl
    omega
  · by_contra! hd
    have h₁ := Nat.mul_le_mul_right c hl
    have h₂ := Nat.mul_le_mul_left a hd
    have hcomm : (n + 1) * a * c = a * ((n + 1) * c) := by ac_rfl
    omega

-- A fraction with numerator 1 cannot lie strictly between positive Farey neighbors.
private theorem not_straddling {a b c d k : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hdet : b * c = a * d + 1) (hl : k * a < b) (hr : d < k * c) : False := by
  have h₁ := Nat.mul_lt_mul_of_pos_right hl hc
  have h₂ := Nat.mul_lt_mul_of_pos_left hr ha
  have hcomm : k * a * c = a * (k * c) := by ac_rfl
  omega

private def root {n : ℕ} : FareyNode n :=
  ⟨(1, n + 1, 1, n), by simp [InReciprocal]⟩

private def leftChild {n : ℕ} (q : FareyNode n) : FareyNode n := by
  obtain ⟨⟨a, b, c, d⟩, h⟩ := q
  have ⟨hl', _⟩ := inner_bounds h
  obtain ⟨hdet, hl, hr⟩ := h
  refine ⟨(a, b, a + c, b + d), ?_⟩
  change b * (a + c) = a * (b + d) + 1 ∧ b ≤ (n + 1) * a ∧ n * (a + c) ≤ b + d
  rw [Nat.mul_add b, Nat.mul_add a, Nat.mul_add n, Nat.mul_comm b a]
  omega

private def rightChild {n : ℕ} (q : FareyNode n) : FareyNode n := by
  obtain ⟨⟨a, b, c, d⟩, h⟩ := q
  have ⟨_, hr'⟩ := inner_bounds h
  obtain ⟨hdet, hl, hr⟩ := h
  refine ⟨(a + c, b + d, c, d), ?_⟩
  change (b + d) * c = (a + c) * d + 1 ∧ b + d ≤ (n + 1) * (a + c) ∧ n * c ≤ d
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_add (n + 1), Nat.mul_comm d c]
  omega

private theorem leftChild_injective {n : ℕ} : Function.Injective (@leftChild n) := by
  rintro ⟨⟨a, b, c, d⟩, _⟩ ⟨⟨a', b', c', d'⟩, _⟩ h
  have hv := congrArg Subtype.val h
  change (a, b, a + c, b + d) = (a', b', a' + c', b' + d') at hv
  simp only [Prod.mk.injEq] at hv
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  omega

private theorem rightChild_injective {n : ℕ} : Function.Injective (@rightChild n) := by
  rintro ⟨⟨a, b, c, d⟩, _⟩ ⟨⟨a', b', c', d'⟩, _⟩ h
  have hv := congrArg Subtype.val h
  change (a + c, b + d, c, d) = (a' + c', b' + d', c', d') at hv
  simp only [Prod.mk.injEq] at hv
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  omega

private theorem leftChild_ne_rightChild {n : ℕ} (p q : FareyNode n) :
    leftChild p ≠ rightChild q := by
  obtain ⟨⟨a, b, c, d⟩, hp⟩ := p
  obtain ⟨⟨a', b', c', d'⟩, hq⟩ := q
  have hc := (numerators_pos hp).2.2
  have ha' := (numerators_pos hq).1
  intro h
  have hv := congrArg Subtype.val h
  change (a, b, a + c, b + d) = (a' + c', b' + d', c', d') at hv
  simp only [Prod.mk.injEq] at hv
  omega

private theorem root_ne_leftChild {n : ℕ} (q : FareyNode n) : root ≠ leftChild q := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  have hc := (numerators_pos hq).2.2
  intro h
  have hv := congrArg Subtype.val h
  change (1, n + 1, 1, n) = (a, b, a + c, b + d) at hv
  simp only [Prod.mk.injEq] at hv
  omega

private theorem root_ne_rightChild {n : ℕ} (q : FareyNode n) : root ≠ rightChild q := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  have ha := (numerators_pos hq).1
  intro h
  have hv := congrArg Subtype.val h
  change (1, n + 1, 1, n) = (a + c, b + d, c, d) at hv
  simp only [Prod.mk.injEq] at hv
  omega

private def height {n : ℕ} (q : FareyNode n) : ℕ := q.val.1 + q.val.2.2.1

-- Subtract the componentwise smaller endpoint to recover the parent. The two bounds survive
-- subtraction because neither reciprocal endpoint can lie strictly inside the parent.
private theorem root_or_parent {n : ℕ} (hn : 0 < n) (q : FareyNode n) :
    q = root ∨ ∃ p : FareyNode n, height p < height q ∧ (q = leftChild p ∨ q = rightChild p) := by
  obtain ⟨⟨a, b, c, d⟩, h⟩ := q
  obtain ⟨ha, hb, hc⟩ := numerators_pos h
  obtain ⟨hl', hr'⟩ := inner_bounds h
  obtain ⟨hdet, hl, hr⟩ := h
  have hb₂ : 2 ≤ b := by
    have := Nat.mul_pos hn ha
    omega
  rcases lt_trichotomy a c with hac | hac | hca
  · have hbd : b < d := by
      by_contra! hdb
      have h₁ := Nat.mul_le_mul_left b (show a + 1 ≤ c by omega)
      have h₂ := Nat.mul_le_mul_left a hdb
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm b a] at h₁
      omega
    have hpdet : b * (c - a) = a * (d - b) + 1 := by
      have h₁ : b * (c - a) + a * b = b * c := by
        rw [Nat.mul_comm a b, ← Nat.mul_add, Nat.sub_add_cancel hac.le]
      have h₂ : a * (d - b) + a * b = a * d := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hbd.le]
      omega
    have hpr : n * (c - a) ≤ d - b := by
      by_contra! hp
      exact not_straddling ha (by omega) hpdet hl' hp
    refine Or.inr ⟨⟨(a, b, c - a, d - b), hpdet, hl, hpr⟩, ?_, Or.inl ?_⟩
    · change a + (c - a) < a + c
      omega
    · apply Subtype.ext
      change (a, b, c, d) = (a, b, a + (c - a), b + (d - b))
      simp [Nat.add_sub_of_le hac.le, Nat.add_sub_of_le hbd.le]
  · subst c
    have hba : d < b := by
      by_contra! hbd
      have := Nat.mul_le_mul_right a hbd
      rw [Nat.mul_comm d a] at this
      omega
    have hprod : (b - d) * a = 1 := by
      rw [Nat.sub_mul, Nat.mul_comm d a, hdet, Nat.add_sub_cancel_left]
    have ha₁ : a = 1 := Nat.dvd_one.mp ⟨b - d, by simpa [Nat.mul_comm] using hprod.symm⟩
    subst a
    simp only [Nat.mul_one, Nat.one_mul] at hdet hl hr
    left
    apply Subtype.ext
    change (1, b, 1, d) = (1, n + 1, 1, n)
    simp only [Prod.mk.injEq, true_and]
    omega
  · have hdb : d < b := by
      by_contra! hbd
      have h₁ := Nat.mul_le_mul hbd hca.le
      rw [Nat.mul_comm d a] at h₁
      omega
    have hpdet : (b - d) * c = (a - c) * d + 1 := by
      have h₁ : (b - d) * c + c * d = b * c := by
        rw [Nat.mul_comm c d, ← Nat.add_mul, Nat.sub_add_cancel hdb.le]
      have h₂ : (a - c) * d + c * d = a * d := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hca.le]
      omega
    have hpl : b - d ≤ (n + 1) * (a - c) := by
      by_contra! hp
      exact not_straddling (by omega) hc hpdet hp hr'
    refine Or.inr ⟨⟨(a - c, b - d, c, d), hpdet, hpl, hr⟩, ?_, Or.inr ?_⟩
    · change (a - c) + c < a + c
      omega
    · apply Subtype.ext
      change (a, b, c, d) = ((a - c) + c, (b - d) + d, c, d)
      simp [Nat.sub_add_cancel hca.le, Nat.sub_add_cancel hdb.le]

private def leftEmb {n : ℕ} : FareyNode n ↪ FareyNode n := ⟨leftChild, leftChild_injective⟩
private def rightEmb {n : ℕ} : FareyNode n ↪ FareyNode n := ⟨rightChild, rightChild_injective⟩

private theorem children_disjoint {n : ℕ} (s t : Finset (FareyNode n)) :
    Disjoint (s.map leftEmb) (t.map rightEmb) := by
  refine Finset.disjoint_left.mpr fun q hl hr => ?_
  obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hl
  obtain ⟨p', _, hp'⟩ := Finset.mem_map.mp hr
  exact leftChild_ne_rightChild p p' (hp.trans hp'.symm)

private def layer (n : ℕ) : ℕ → Finset (FareyNode n)
  | 0 => {root}
  | k + 1 => (layer n k).map leftEmb ∪ (layer n k).map rightEmb

private theorem mem_layer_succ {n k : ℕ} {q : FareyNode n} :
    q ∈ layer n (k + 1) ↔ ∃ p ∈ layer n k, q = leftChild p ∨ q = rightChild p := by
  change q ∈ (layer n k).map leftEmb ∪ (layer n k).map rightEmb ↔ _
  simp only [Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, hp, Or.inl h.symm⟩
    · exact ⟨p, hp, Or.inr h.symm⟩
  · rintro ⟨p, hp, h | h⟩
    · exact Or.inl ⟨p, hp, h.symm⟩
    · exact Or.inr ⟨p, hp, h.symm⟩

private theorem sum_layer_succ {n : ℕ} (k : ℕ) (f : FareyNode n → ℝ) :
    ∑ q ∈ layer n (k + 1), f q = ∑ p ∈ layer n k, (f (leftChild p) + f (rightChild p)) := by
  rw [layer, Finset.sum_union (children_disjoint _ _), Finset.sum_map, Finset.sum_map,
    Finset.sum_add_distrib]
  rfl

private theorem layer_index_unique {n k l : ℕ} {q : FareyNode n}
    (hk : q ∈ layer n k) (hl : q ∈ layer n l) : k = l := by
  induction k generalizing l q with
  | zero =>
    cases l with
    | zero => rfl
    | succ l =>
      have hq : q = root := Finset.mem_singleton.mp hk
      obtain ⟨p, _, h | h⟩ := mem_layer_succ.mp hl
      · exact (root_ne_leftChild p (hq.symm.trans h)).elim
      · exact (root_ne_rightChild p (hq.symm.trans h)).elim
  | succ k ih =>
    obtain ⟨p, hp, h⟩ := mem_layer_succ.mp hk
    cases l with
    | zero =>
      have hq : q = root := Finset.mem_singleton.mp hl
      rcases h with h | h
      · exact (root_ne_leftChild p (hq.symm.trans h)).elim
      · exact (root_ne_rightChild p (hq.symm.trans h)).elim
    | succ l =>
      obtain ⟨p', hp', h'⟩ := mem_layer_succ.mp hl
      have heq := h.elim (fun h => h'.elim
        (fun h' => leftChild_injective (h.symm.trans h'))
        (fun h' => (leftChild_ne_rightChild p p' (h.symm.trans h')).elim))
        (fun h => h'.elim
          (fun h' => (leftChild_ne_rightChild p' p (h'.symm.trans h)).elim)
          (fun h' => rightChild_injective (h.symm.trans h')))
      exact congrArg Nat.succ (ih hp (heq ▸ hp'))

private theorem exists_mem_layer {n : ℕ} (hn : 0 < n) (q : FareyNode n) :
    ∃ k, q ∈ layer n k := by
  induction q using (measure height).wf.induction with
  | h q ih =>
    rcases root_or_parent hn q with rfl | ⟨p, hp, hq⟩
    · exact ⟨0, Finset.mem_singleton_self _⟩
    · obtain ⟨k, hk⟩ := ih p hp
      exact ⟨k + 1, mem_layer_succ.mpr ⟨p, hk, hq⟩⟩

private noncomputable def leftValue {n : ℕ} (q : FareyNode n) : ℝ :=
  (q.val.1 : ℝ) / q.val.2.1

private noncomputable def rightValue {n : ℕ} (q : FareyNode n) : ℝ :=
  (q.val.2.2.1 : ℝ) / q.val.2.2.2

private noncomputable def width {n : ℕ} (q : FareyNode n) : ℝ := rightValue q - leftValue q

private noncomputable def logMass {n : ℕ} (q : FareyNode n) : ℝ :=
  2 * (Real.log (rightValue q) - Real.log (leftValue q))

private noncomputable def weight {n : ℕ} (q : FareyNode n) : ℝ :=
  match q.val with
  | (a, b, c, d) => (a * d + b * c : ℝ) / (a * b * c * d)

private noncomputable def defect {n : ℕ} (q : FareyNode n) : ℝ :=
  match q.val with
  | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d))

private theorem defect_nonneg {n : ℕ} (q : FareyNode n) : 0 ≤ defect q := by
  obtain ⟨⟨a, b, c, d⟩, _⟩ := q
  unfold defect
  positivity

private theorem defect_eq_sub {n : ℕ} (hn : 0 < n) (q : FareyNode n) :
    defect q = weight q - weight (leftChild q) - weight (rightChild q) := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  obtain ⟨h₁, h₂⟩ := farey_interval_mediant_telescoping
    (numerators_pos hq).1 (right_den_pos hn hq) hq.1
  simpa only [defect, weight, leftChild, rightChild, Nat.cast_add] using (h₁.trans h₂).symm

private theorem width_eq {n : ℕ} (hn : 0 < n) (q : FareyNode n) :
    width q = (1 : ℝ) / (q.val.2.1 * q.val.2.2.2) := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  have hb : (0 : ℝ) < b := by exact_mod_cast (numerators_pos hq).2.1
  have hd : (0 : ℝ) < d := by exact_mod_cast right_den_pos hn hq
  have hdet : (b * c : ℝ) = a * d + 1 := by exact_mod_cast hq.1
  change (c : ℝ) / d - a / b = 1 / (b * d)
  rw [div_sub_div _ _ hd.ne' hb.ne', mul_comm (c : ℝ) b, mul_comm (d : ℝ) a, hdet,
    add_sub_cancel_left, mul_comm (d : ℝ) b]

private theorem den_prod_ge_depth {n k : ℕ} (hn : 0 < n) {q : FareyNode n} (hq : q ∈ layer n k) :
    k + 1 ≤ q.val.2.1 * q.val.2.2.2 := by
  induction k generalizing q with
  | zero =>
    obtain ⟨⟨a, b, c, d⟩, h⟩ := q
    exact Nat.mul_pos (numerators_pos h).2.1 (right_den_pos hn h)
  | succ k ih =>
    obtain ⟨p, hp, h⟩ := mem_layer_succ.mp hq
    have hprod := ih hp
    obtain ⟨⟨a, b, c, d⟩, h'⟩ := p
    change k + 1 ≤ b * d at hprod
    rcases h with rfl | rfl
    · change k + 1 + 1 ≤ b * (b + d)
      have := Nat.mul_pos (numerators_pos h').2.1 (numerators_pos h').2.1
      rw [Nat.mul_add]
      omega
    · change k + 1 + 1 ≤ (b + d) * d
      have := Nat.mul_pos (right_den_pos hn h') (right_den_pos hn h')
      rw [Nat.add_mul]
      omega

private theorem sum_layer_of_additive {n : ℕ} {f : FareyNode n → ℝ}
    (h : ∀ q, f (leftChild q) + f (rightChild q) = f q) (k : ℕ) :
    ∑ q ∈ layer n k, f q = f root := by
  induction k with
  | zero => simp [layer]
  | succ k ih => simpa only [sum_layer_succ, h] using ih

private theorem sum_width {n : ℕ} (k : ℕ) :
    ∑ q ∈ layer n k, width q = width (root : FareyNode n) := by
  apply sum_layer_of_additive
  rintro ⟨⟨a, b, c, d⟩, _⟩
  simp only [width, leftValue, rightValue, leftChild, rightChild]
  ring

private theorem sum_logMass {n : ℕ} (k : ℕ) :
    ∑ q ∈ layer n k, logMass q = logMass (root : FareyNode n) := by
  apply sum_layer_of_additive
  rintro ⟨⟨a, b, c, d⟩, _⟩
  simp only [logMass, leftValue, rightValue, leftChild, rightChild]
  ring

private theorem integral_eq_logMass {n : ℕ} (hn : 0 < n) (q : FareyNode n) :
    (∫ t in leftValue q..rightValue q, 2 / t) = logMass q := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  obtain ⟨ha, hb, hc⟩ := numerators_pos hq
  have hx : 0 < (a : ℝ) / b := by exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hy : 0 < (c : ℝ) / d := by
    exact div_pos (by exact_mod_cast hc) (by exact_mod_cast right_den_pos hn hq)
  change (∫ t in (a : ℝ) / b..(c : ℝ) / d, 2 / t) =
    2 * (Real.log ((c : ℝ) / d) - Real.log ((a : ℝ) / b))
  simp only [div_eq_mul_inv (2 : ℝ), intervalIntegral.integral_const_mul,
    integral_inv_of_pos hx hy, Real.log_div hy.ne' hx.ne']

private theorem abs_weight_sub_logMass_le {n : ℕ} (hn : 0 < n) (q : FareyNode n) {δ : ℝ}
    (hδ : width q ≤ δ) :
    |weight q - logMass q| ≤ width q * ((n : ℝ) + 1) ^ 2 * δ := by
  obtain ⟨⟨a, b, c, d⟩, hq⟩ := q
  have ha := (numerators_pos hq).1
  have hc := (numerators_pos hq).2.2
  have hcd : c ≤ d := (Nat.le_mul_of_pos_left _ hn).trans hq.2.2
  have hδ' : (1 : ℝ) / (b * d) ≤ δ := by
    rw [← width_eq hn (⟨(a, b, c, d), hq⟩ : FareyNode n)]
    exact hδ
  -- Apply the partition error bound to the one-interval partition.
  let A (i : ℕ) := if i = 1 then a else c
  let B (i : ℕ) := if i = 1 then b else d
  have hindex : Finset.Icc (1 : ℕ) (2 - 1) = {1} := by decide
  have h := abs_sum_farey_partition_sub_integral_le (m := 2) (A := A) (B := B)
    ha hq.1 hcd (by decide) (by simp [A]) (by simp [B]) (by simp [A]) (by simp [B])
    (by intro i hi; rw [hindex, Finset.mem_singleton] at hi; subst i; simpa [A, B] using hq.1)
    (by intro i hi; rw [hindex, Finset.mem_singleton] at hi; subst i; simpa [B] using hδ')
  have hlocal : |weight (⟨(a, b, c, d), hq⟩ : FareyNode n) - logMass ⟨(a, b, c, d), hq⟩| ≤
      ((c : ℝ) / d - a / b) * ((b : ℝ) ^ 2 / a ^ 2) * δ := by
    rw [← integral_eq_logMass hn]
    simpa [hindex, A, B, weight, leftValue, rightValue] using h
  have hw : 0 ≤ width (⟨(a, b, c, d), hq⟩ : FareyNode n) := by
    rw [width_eq hn]
    positivity
  have hdiv : (b : ℝ) / a ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a)]
    exact_mod_cast hq.2.1
  have hsquare : (b : ℝ) ^ 2 / a ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) hdiv 2
  exact hlocal.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hw) (hw.trans hδ))

private theorem tendsto_sum_weight {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k ↦ ∑ q ∈ layer n k, weight q) atTop (𝓝 (logMass (root : FareyNode n))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hmesh (k : ℕ) (q : FareyNode n) (hq : q ∈ layer n k) : width q ≤ 1 / ((k : ℝ) + 1) := by
    rw [width_eq hn]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast den_prod_ge_depth hn hq
  have hbound (k : ℕ) : dist (∑ q ∈ layer n k, weight q) (logMass (root : FareyNode n)) ≤
      width (root : FareyNode n) * ((n : ℝ) + 1) ^ 2 * (1 / ((k : ℝ) + 1)) := by
    rw [Real.dist_eq, ← sum_logMass k, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ q ∈ layer n k, |weight q - logMass q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ layer n k, width q * ((n : ℝ) + 1) ^ 2 * (1 / ((k : ℝ) + 1)) :=
        Finset.sum_le_sum fun q hq ↦ abs_weight_sub_logMass_le hn q (hmesh k q hq)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, sum_width]
  have hzero := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (width (root : FareyNode n) * ((n : ℝ) + 1) ^ 2)
  exact squeeze_zero (fun _ ↦ dist_nonneg) hbound (by simpa only [mul_zero] using hzero)

private def layersBelow (n k : ℕ) : Finset (FareyNode n) := (Finset.range k).biUnion (layer n)

private theorem layersBelow_succ {n k : ℕ} :
    layersBelow n (k + 1) = layer n k ∪ layersBelow n k := by
  simp only [layersBelow, Finset.range_add_one, Finset.biUnion_insert]

private theorem layer_disjoint_layersBelow {n k : ℕ} :
    Disjoint (layer n k) (layersBelow n k) := by
  refine Finset.disjoint_left.mpr fun q hq hbelow ↦ ?_
  obtain ⟨j, hj, hq'⟩ := Finset.mem_biUnion.mp hbelow
  exact (Finset.mem_range.mp hj).ne (layer_index_unique hq' hq)

private theorem tendsto_layersBelow {n : ℕ} (hn : 0 < n) :
    Tendsto (layersBelow n) atTop atTop := by
  classical
  refine tendsto_atTop.mpr fun s ↦ eventually_atTop.mpr ?_
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ ↦ Finset.empty_subset _⟩
  | @insert q s _ ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨j, hj⟩ := exists_mem_layer hn q
    refine ⟨max l (j + 1), fun k hk ↦ Finset.insert_subset_iff.mpr
      ⟨?_, hl k ((le_max_left l (j + 1)).trans hk)⟩⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr ((Nat.lt_succ_self j).trans_le
      ((le_max_right l (j + 1)).trans hk)), hj⟩

private theorem sum_defect {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∑ q ∈ layersBelow n k, defect q = weight (root : FareyNode n) - ∑ q ∈ layer n k, weight q := by
  induction k with
  | zero => simp [layersBelow, layer]
  | succ k ih =>
    rw [layersBelow_succ, Finset.sum_union layer_disjoint_layersBelow, ih, sum_layer_succ]
    simp only [defect_eq_sub hn, sub_sub, Finset.sum_sub_distrib]
    ring

private theorem hasSum_defect {n : ℕ} (hn : 0 < n) :
    HasSum (@defect n) (weight (root : FareyNode n) - logMass (root : FareyNode n)) := by
  have hlim : Tendsto (fun k ↦ ∑ q ∈ layersBelow n k, defect q) atTop
      (𝓝 (weight (root : FareyNode n) - logMass (root : FareyNode n))) := by
    simpa only [sum_defect hn] using (tendsto_sum_weight hn).const_sub (weight (root : FareyNode n))
  have hs : Summable (@defect n) := summable_of_sum_le defect_nonneg fun s ↦ by
    refine ge_of_tendsto hlim ?_
    filter_upwards [(tendsto_layersBelow hn).eventually (eventually_ge_atTop s)] with k hk
    exact Finset.sum_le_sum_of_subset_of_nonneg hk fun q _ _ ↦ defect_nonneg q
  have heq := tendsto_nhds_unique (hs.hasSum.comp (tendsto_layersBelow hn)) hlim
  exact heq ▸ hs.hasSum

/-- **Sum over the Farey intervals inside a reciprocal interval.** Let $n \ge 1$ and
$J_n = [1/(n + 1), 1/n]$. The family $1/(abcd(a + c)(b + d))$, indexed by the quadruples
$(a, b, c, d)$ of natural numbers with $bc = ad + 1$, $b \le (n + 1)a$ and $nc \le d$ (that is,
by the Farey intervals $[a/b, c/d] \subseteq J_n$, including $J_n$ itself), is summable with sum
$$
\frac{1}{n} + \frac{1}{n + 1} - 2 \log \frac{n + 1}{n}.
$$

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 3. -/
public theorem hasSum_farey_subintervals_reciprocal_interval {n : ℕ} (hn : 0 < n) :
    HasSum
      (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ |
          b * c = a * d + 1 ∧ b ≤ (n + 1) * a ∧ n * c ≤ d} =>
        match q.1 with
        | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d)))
      (1 / n + 1 / (n + 1) - 2 * Real.log ((n + 1) / n)) := by
  change HasSum (@defect n) _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hweight : weight (root : FareyNode n) = 1 / n + 1 / ((n : ℝ) + 1) := by
    simp only [weight, root, Nat.cast_one, Nat.cast_add, one_mul, mul_one]
    field_simp
    ring
  have hmass : logMass (root : FareyNode n) = 2 * Real.log (((n : ℝ) + 1) / n) := by
    simp only [logMass, leftValue, rightValue, root, Nat.cast_one, Nat.cast_add, one_div]
    rw [← Real.log_div (inv_pos.mpr hn').ne' (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹).ne',
      inv_div_inv]
  rw [← hweight, ← hmass]
  exact hasSum_defect hn

end MetaMathlibExt
