/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.MetricSpace.Basic
public import MathlibExt.Probability.MarkovMixing

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Path coupling

If a one-step coupling contracts the expected distance by `β` for
*adjacent* pairs, then the total variation between the chains after
`t` steps is at most `β^t * dist x y / δ`, where `δ` is the least
nonzero distance in the space. This is roadmap package ML-27 of the
Atlas TCS canon roadmap.

Adjacency is an abstract relation `Adj`, and `Path Adj dist x y` is
the path data joining `x` to `y`: either `x = y`, or one adjacent
step from `x` to some `y'` followed by a path from `y'` to `y`,
with the distance adding over the step. A coupling for an arbitrary
pair is built by gluing the adjacent couplings along such a path
(`glueCoupling`, the finite gluing lemma), so the only coupling the
user has to provide is the adjacent one. The global-coupling
iteration is the `coupling_tv` lemma.

Total variation is the `MarkovMixing.tvDist` of the two mass
functions, via the namespaced PMF bridge `tvDist` below.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 13.
-/

open Finset
open scoped Classical ENNReal

namespace MathlibExt.Probability.PathCoupling

/-- Total variation distance between two PMFs on a finite type:
`MarkovMixing.tvDist` of their real-valued mass functions. -/
noncomputable def tvDist {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  MathlibExt.Probability.MarkovMixing.tvDist (fun a => (p a).toReal)
    (fun a => (q a).toReal)

/-- The distribution of a Markov chain after `t` steps started from
`x`, where `K` is the one-step kernel. -/
noncomputable def chainDist {α : Type*} (K : α → PMF α) (x : α) : ℕ → PMF α
  | 0 => PMF.pure x
  | t + 1 => (chainDist K x t).bind K

/-- Path data joining two points: either the points coincide, or one
adjacent step followed by a path from the step's endpoint, with the
distance adding over the step. -/
inductive Path {α : Type*} (Adj : α → α → Prop) (d : α → α → ℝ) :
    α → α → Prop
  | refl (x : α) : Path Adj d x x
  | step {x y z : α} (h : Adj x y) (hd : d x z = d x y + d y z)
      (hpath : Path Adj d y z) : Path Adj d x z

private noncomputable def JCoupling {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) : ℕ → PMF (α × α)
  | 0 => PMF.pure (x, y)
  | t + 1 => (JCoupling C x y t).bind (fun z => C z.1 z.2)

private theorem chainDist_zero {α : Type*} (K : α → PMF α) (x : α) :
    chainDist K x 0 = PMF.pure x := rfl

private theorem chainDist_succ {α : Type*} (K : α → PMF α) (x : α) (t : ℕ) :
    chainDist K x (t + 1) = (chainDist K x t).bind K := rfl

private theorem JCoupling_zero {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) : JCoupling C x y 0 = PMF.pure (x, y) := rfl

private theorem JCoupling_succ {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) (t : ℕ) :
    JCoupling C x y (t + 1)
      = (JCoupling C x y t).bind (fun z => C z.1 z.2) := rfl

private theorem JCoupling_map_fst {α : Type*} (K : α → PMF α)
    (C : α → α → PMF (α × α))
    (hC_fst : ∀ x y, (C x y).map Prod.fst = K x) (x y : α) (t : ℕ) :
    (JCoupling C x y t).map Prod.fst = chainDist K x t := by
  induction t with
  | zero => rw [JCoupling_zero, chainDist_zero, PMF.pure_map]
  | succ t ih =>
      rw [JCoupling_succ, PMF.map_bind]
      simp only [hC_fst]
      have hcomp : (fun z : α × α => K z.1) = K ∘ Prod.fst := rfl
      rw [hcomp, ← PMF.bind_map, ih, chainDist_succ]

private theorem JCoupling_map_snd {α : Type*} (K : α → PMF α)
    (C : α → α → PMF (α × α))
    (hC_snd : ∀ x y, (C x y).map Prod.snd = K y) (x y : α) (t : ℕ) :
    (JCoupling C x y t).map Prod.snd = chainDist K y t := by
  induction t with
  | zero => rw [JCoupling_zero, chainDist_zero, PMF.pure_map]
  | succ t ih =>
      rw [JCoupling_succ, PMF.map_bind]
      simp only [hC_snd]
      have hcomp : (fun z : α × α => K z.2) = K ∘ Prod.snd := rfl
      rw [hcomp, ← PMF.bind_map, ih, chainDist_succ]

private theorem JCoupling_dist_le {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (C : α → α → PMF (α × α)) {β : ℝ}
    (hcontract : ∀ x y, ∑ z, (C x y z).toReal * dist z.1 z.2 ≤
      β * dist x y) (x y : α) (t : ℕ) :
    ∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2 ≤
      β ^ t * dist x y := by
  by_cases hβ0 : 0 ≤ β
  · induction t with
    | zero =>
        rw [JCoupling_zero]
        have hterm : ∀ z : α × α, ((PMF.pure (x, y)) z).toReal * dist z.1 z.2
            = if z = (x, y) then dist x y else 0 := by
          intro z
          by_cases h : z = (x, y)
          · subst h
            rw [PMF.pure_apply_self, ENNReal.toReal_one, one_mul,
              ite_eq_left rfl]
          · simp [h, PMF.pure_apply_of_ne _ _ h]
        have h1 : ∑ z, ((PMF.pure (x, y)) z).toReal * dist z.1 z.2
            = dist x y := by
          simp_rw [hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [h1, pow_zero, one_mul]
    | succ t ih =>
        rw [JCoupling_succ]
        have hside : ∀ z : α × α, ∀ a ∈ (univ : Finset (α × α)),
            ((JCoupling C x y t) a * (C a.1 a.2) z) ≠ ∞ := by
          intro z a _
          exact ENNReal.mul_ne_top ((JCoupling C x y t).apply_ne_top a)
            ((C a.1 a.2).apply_ne_top z)
        have hexpand : ∀ z : α × α,
            (((JCoupling C x y t).bind (fun w => C w.1 w.2)) z).toReal
              = ∑ w, ((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal := by
          intro z
          rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (hside z)]
          refine Finset.sum_congr rfl fun w _ => ?_
          show (((JCoupling C x y t) w) * ((C w.1 w.2) z)).toReal
            = ((JCoupling C x y t) w).toReal * (((C w.1 w.2) z)).toReal
          rw [ENNReal.toReal_mul]
        simp_rw [hexpand, Finset.sum_mul]
        have hswap : (∑ z, ∑ w, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2)
            = ∑ w, ∑ z, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2 :=
          Finset.sum_comm
        rw [hswap]
        have hfactor : ∀ w : α × α,
            (∑ z, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2)
              = ((JCoupling C x y t) w).toReal
                * (∑ z, ((C w.1 w.2) z).toReal * dist z.1 z.2) := by
          intro w
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          show (((JCoupling C x y t) w).toReal * ((C w.1 w.2) z).toReal)
              * dist z.1 z.2
            = ((JCoupling C x y t) w).toReal
              * (((C w.1 w.2) z).toReal * dist z.1 z.2)
          ring
        simp_rw [hfactor]
        calc ∑ w, ((JCoupling C x y t) w).toReal
                * (∑ z, ((C w.1 w.2) z).toReal * dist z.1 z.2)
            ≤ ∑ w, ((JCoupling C x y t) w).toReal * (β * dist w.1 w.2) := by
              apply Finset.sum_le_sum
              intro w _
              exact mul_le_mul_of_nonneg_left (hcontract w.1 w.2)
                ENNReal.toReal_nonneg
          _ = β * (∑ w, ((JCoupling C x y t) w).toReal * dist w.1 w.2) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun w _ => ?_
              show ((JCoupling C x y t) w).toReal * (β * dist w.1 w.2)
                = β * (((JCoupling C x y t) w).toReal * dist w.1 w.2)
              ring
          _ ≤ β * (β ^ t * dist x y) := mul_le_mul_of_nonneg_left ih hβ0
          _ = β ^ (t + 1) * dist x y := by
              rw [pow_succ]
              ring
  · have hneg : β < 0 := lt_of_not_ge hβ0
    have hdist0 : ∀ a b : α, dist a b = 0 := by
      intro a b
      have hsum : 0 ≤ ∑ z, (C a b z).toReal * dist z.1 z.2 :=
        Finset.sum_nonneg fun z _ =>
          mul_nonneg ENNReal.toReal_nonneg dist_nonneg
      have hle : 0 ≤ β * dist a b := le_trans hsum (hcontract a b)
      have hle' : dist a b ≤ 0 := nonpos_of_mul_nonneg_right hle hneg
      exact le_antisymm hle' dist_nonneg
    simp [hdist0]

private theorem map_fst_toReal {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : ((J.map Prod.fst) a).toReal = ∑ b, (J (a, b)).toReal := by
  have hne : ∀ w ∈ (univ : Finset (α × α)),
      (if a = w.1 then J w else 0) ≠ ∞ := by
    intro w _
    split_ifs with h
    · exact J.apply_ne_top w
    · exact ENNReal.zero_ne_top
  have hinner : ∀ x : α, (∑ y : α, (if a = x then J (x, y) else 0).toReal)
      = if a = x then (∑ y, (J (x, y)).toReal) else 0 := by
    intro x
    by_cases h : a = x <;> simp [h]
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum hne,
    Fintype.sum_prod_type]
  simp only []
  show (∑ x : α, ∑ y : α, (if a = x then J (x, y) else 0).toReal)
    = ∑ b, (J (a, b)).toReal
  simp_rw [hinner]
  rw [Finset.sum_ite_eq]
  simp

private theorem map_snd_toReal {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : ((J.map Prod.snd) a).toReal = ∑ b, (J (b, a)).toReal := by
  have hne : ∀ w ∈ (univ : Finset (α × α)),
      (if a = w.2 then J w else 0) ≠ ∞ := by
    intro w _
    split_ifs with h
    · exact J.apply_ne_top w
    · exact ENNReal.zero_ne_top
  have hpush : ∀ x y : α, (if a = y then J (x, y) else 0).toReal
      = if a = y then (J (x, y)).toReal else 0 := by
    intro x y
    by_cases h : a = y <;> simp [h]
  have hinner : ∀ x : α, (∑ y : α, (if a = y then J (x, y) else 0).toReal)
      = (J (x, a)).toReal := by
    intro x
    simp_rw [hpush]
    rw [Finset.sum_ite_eq]
    simp
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum hne,
    Fintype.sum_prod_type]
  simp only []
  show (∑ x : α, ∑ y : α, (if a = y then J (x, y) else 0).toReal)
    = ∑ b, (J (b, a)).toReal
  simp_rw [hinner]

private theorem tvDist_map_le {α : Type*} [Fintype α] (J : PMF (α × α)) :
    tvDist (J.map Prod.fst) (J.map Prod.snd)
      ≤ ∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) := by
  have hfst : ∀ a : α, ((J.map Prod.fst) a).toReal
      = ∑ b, (J (a, b)).toReal := fun a => map_fst_toReal J a
  have hsnd : ∀ a : α, ((J.map Prod.snd) a).toReal
      = ∑ b, (J (b, a)).toReal := fun a => map_snd_toReal J a
  have hterm : ∀ a b : α, |(J (a, b)).toReal - (J (b, a)).toReal|
      ≤ (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1)
        + (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_one, mul_one]
      calc |(J (a, b)).toReal - (J (b, a)).toReal|
          ≤ |(J (a, b)).toReal| + |(J (b, a)).toReal| := abs_sub _ _
        _ = (J (a, b)).toReal + (J (b, a)).toReal := by
            rw [abs_of_nonneg ENNReal.toReal_nonneg,
              abs_of_nonneg ENNReal.toReal_nonneg]
  have hper : ∀ a : α, |((J.map Prod.fst) a).toReal
        - ((J.map Prod.snd) a).toReal|
      ≤ (∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
        + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) := by
    intro a
    have hsub : (∑ b, (J (a, b)).toReal) - (∑ b, (J (b, a)).toReal)
        = ∑ b, ((J (a, b)).toReal - (J (b, a)).toReal) :=
      (Finset.sum_sub_distrib _ _).symm
    rw [hfst a, hsnd a, hsub]
    have habs : ∀ g : α → ℝ, |∑ b, g b| ≤ ∑ b, |g b| := by
      intro g
      have h := norm_sum_le (univ : Finset α) g
      simpa only [Real.norm_eq_abs] using h
    calc |∑ b, ((J (a, b)).toReal - (J (b, a)).toReal)|
        ≤ ∑ b, |(J (a, b)).toReal - (J (b, a)).toReal| := habs _
      _ ≤ ∑ b, ((J (a, b)).toReal * (if a = b then (0 : ℝ) else 1)
          + (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) := by
          apply Finset.sum_le_sum
          intro b _
          exact hterm a b
      _ = (∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
          + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) :=
          Finset.sum_add_distrib
  have hsum : (∑ a, |((J.map Prod.fst) a).toReal
        - ((J.map Prod.snd) a).toReal|)
      ≤ 2 * (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) := by
    have hA : (∑ a : α, ∑ b : α, (J (a, b)).toReal
            * (if a = b then (0 : ℝ) else 1))
        = ∑ z : α × α, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) :=
      (Fintype.sum_prod_type' _).symm
    have hB : (∑ a : α, ∑ b : α, (J (b, a)).toReal
            * (if b = a then (0 : ℝ) else 1))
        = ∑ z : α × α, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) :=
      (Fintype.sum_prod_type_right' _).symm
    calc (∑ a, |((J.map Prod.fst) a).toReal - ((J.map Prod.snd) a).toReal|)
        ≤ ∑ a, ((∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
          + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1))) := by
          apply Finset.sum_le_sum
          intro a _
          exact hper a
      _ = (∑ a : α, ∑ b : α, (J (a, b)).toReal
              * (if a = b then (0 : ℝ) else 1))
          + (∑ a : α, ∑ b : α, (J (b, a)).toReal
              * (if b = a then (0 : ℝ) else 1)) :=
          Finset.sum_add_distrib
      _ = 2 * (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) := by
          rw [hA, hB]
          ring
  have htv : tvDist (J.map Prod.fst) (J.map Prod.snd)
      = (1 / 2) * (∑ a, |((J.map Prod.fst) a).toReal
          - ((J.map Prod.snd) a).toReal|) := rfl
  rw [htv]
  calc (1 / 2) * (∑ a, |((J.map Prod.fst) a).toReal
          - ((J.map Prod.snd) a).toReal|)
      ≤ (1 / 2) * (2 * (∑ z, (J z).toReal
        * (if z.1 = z.2 then (0 : ℝ) else 1))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) := by ring

private theorem mass_le_dist_div {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (J : PMF (α × α)) {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y) :
    (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1))
      ≤ (∑ z, (J z).toReal * dist z.1 z.2) / δ := by
  rw [le_div_iff₀ hδ, Finset.sum_mul]
  refine Finset.sum_le_sum fun z _ => ?_
  show ((J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) * δ
    ≤ (J z).toReal * dist z.1 z.2
  by_cases h : z.1 = z.2
  · rw [ite_eq_left h, mul_zero, zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg dist_nonneg
  · rw [ite_eq_right h, mul_one]
    exact mul_le_mul_of_nonneg_left (hdist z.1 z.2 h)
      ENNReal.toReal_nonneg

/-- The first marginal of a joint PMF over a product, as a finite sum. -/
private theorem map_fst_apply {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : (J.map Prod.fst) a = ∑ b, J (a, b) := by
  have hinner : ∀ x : α, (∑ y : α, (if a = x then J (x, y) else 0))
      = if a = x then (∑ y, J (x, y)) else 0 := by
    intro x
    by_cases h : a = x <;> simp [h]
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Finset.sum_ite_eq]
  simp

/-- The second marginal of a joint PMF over a product, as a finite sum. -/
private theorem map_snd_apply {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : (J.map Prod.snd) a = ∑ b, J (b, a) := by
  have hinner : ∀ x : α, (∑ y : α, (if a = y then J (x, y) else 0))
      = (J (x, a)) := by
    intro x
    simp_rw [Finset.sum_ite_eq]
    simp
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp_rw [hinner]

/-- If the second marginal vanishes at `b`, the joint vanishes on the
whole fibre over `b`. -/
private theorem apply_eq_zero_of_map_snd_eq_zero {α : Type*} [Fintype α]
    {J : PMF (α × α)} {b : α} (h : (J.map Prod.snd) b = 0) (a : α) :
    J (a, b) = 0 := by
  have hsum : ∑ a', J (a', b) = 0 := by
    rw [← map_snd_apply]
    exact h
  exact (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => zero_le).mp hsum a
    (Finset.mem_univ a)

/-- A PMF on a finite type has finite total mass `1`. -/
private theorem PMF_sum_eq_one {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ b, μ b = 1 := by
  have h := PMF.tsum_coe μ
  rwa [tsum_fintype] at h

/-- If the first marginal vanishes at `a`, the joint vanishes on the
whole fibre over `a`. -/
private theorem apply_eq_zero_of_map_fst_eq_zero {α : Type*} [Fintype α]
    {J : PMF (α × α)} {a : α} (h : (J.map Prod.fst) a = 0) (b : α) :
    J (a, b) = 0 := by
  have hsum : ∑ b', J (a, b') = 0 := by
    rw [← map_fst_apply]
    exact h
  exact (Finset.sum_eq_zero_iff_of_nonneg fun b' _ => zero_le).mp hsum b
    (Finset.mem_univ b)

/-- Gluing two couplings along their common middle marginal: if `J1`
couples `μ1` with `μ2` and `J2` couples `μ2` with `μ3`, the glued
coupling couples `μ1` with `μ3`. Its mass at `(a, c)` is the
conditional sum `∑ b, J1 (a, b) * J2 (b, c) / μ2 b`. -/
private noncomputable def glueCoupling {α : Type*} [Fintype α]
    (J1 J2 : PMF (α × α)) (μ2 : PMF α)
    (h1 : J1.map Prod.snd = μ2) (h2 : J2.map Prod.fst = μ2) : PMF (α × α) :=
  PMF.ofFintype (fun p => ∑ b, J1 (p.1, b) * J2 (b, p.2) / μ2 b) (by
    have hS1 : ∀ b : α, ∑ a, J1 (a, b) = μ2 b := fun b => by
      rw [← map_snd_apply]
      exact congrArg (fun p => p b) h1
    have hS2 : ∀ b : α, ∑ c, J2 (b, c) = μ2 b := fun b => by
      rw [← map_fst_apply]
      exact congrArg (fun p => p b) h2
    have hfactor : ∀ b : α,
        (∑ p : α × α, J1 (p.1, b) * J2 (b, p.2) / μ2 b)
          = (∑ a, J1 (a, b)) * (∑ c, J2 (b, c)) / μ2 b := by
      intro b
      rw [Fintype.sum_prod_type]
      have hterm : ∀ a c : α, J1 (a, b) * J2 (b, c) / μ2 b
          = J1 (a, b) * (J2 (b, c) / μ2 b) := fun a c => by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      simp_rw [hterm, ← Fintype.sum_mul_sum, ← ENNReal.sum_div]
      rw [mul_div_assoc]
    have hcancel : ∀ b : α, μ2 b * μ2 b / μ2 b = μ2 b := by
      intro b
      by_cases h0 : μ2 b = 0
      · simp [h0]
      · rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h0
            (μ2.apply_ne_top b), mul_one]
    calc ∑ p : α × α, ∑ b, J1 (p.1, b) * J2 (b, p.2) / μ2 b
        = ∑ b, (∑ p : α × α, J1 (p.1, b) * J2 (b, p.2) / μ2 b) :=
          Finset.sum_comm
      _ = ∑ b, (∑ a, J1 (a, b)) * (∑ c, J2 (b, c)) / μ2 b :=
          Finset.sum_congr rfl fun b _ => hfactor b
      _ = ∑ b, μ2 b * μ2 b / μ2 b :=
          Finset.sum_congr rfl fun b _ => by rw [hS1 b, hS2 b]
      _ = ∑ b, μ2 b :=
          Finset.sum_congr rfl fun b _ => hcancel b
      _ = 1 := PMF_sum_eq_one μ2)

/-- The first marginal of a glued coupling is the first marginal of
the first coupling. -/
private theorem glueCoupling_map_fst {α : Type*} [Fintype α]
    {J1 J2 : PMF (α × α)} {μ2 : PMF α}
    (h1 : J1.map Prod.snd = μ2) (h2 : J2.map Prod.fst = μ2) :
    (glueCoupling J1 J2 μ2 h1 h2).map Prod.fst = J1.map Prod.fst := by
  ext a
  rw [map_fst_apply, map_fst_apply]
  change (∑ c, ∑ b, J1 (a, b) * J2 (b, c) / μ2 b) = ∑ b, J1 (a, b)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hS2 : ∑ c, J2 (b, c) = μ2 b := by
    rw [← map_fst_apply]
    exact congrArg (fun p => p b) h2
  have hterm : ∀ c : α, J1 (a, b) * J2 (b, c) / μ2 b
      = J1 (a, b) * (J2 (b, c) / μ2 b) := fun c => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  simp_rw [hterm, ← Finset.mul_sum, ← ENNReal.sum_div, hS2]
  by_cases h0 : μ2 b = 0
  · have hJ : J1 (a, b) = 0 :=
      apply_eq_zero_of_map_snd_eq_zero (by rw [h1]; exact h0) a
    simp [hJ, h0]
  · rw [ENNReal.div_self h0 (μ2.apply_ne_top b), mul_one]

/-- The second marginal of a glued coupling is the second marginal
of the second coupling. -/
private theorem glueCoupling_map_snd {α : Type*} [Fintype α]
    {J1 J2 : PMF (α × α)} {μ2 : PMF α}
    (h1 : J1.map Prod.snd = μ2) (h2 : J2.map Prod.fst = μ2) :
    (glueCoupling J1 J2 μ2 h1 h2).map Prod.snd = J2.map Prod.snd := by
  ext c
  rw [map_snd_apply, map_snd_apply]
  change (∑ a, ∑ b, J1 (a, b) * J2 (b, c) / μ2 b) = ∑ b, J2 (b, c)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hS1 : ∑ a, J1 (a, b) = μ2 b := by
    rw [← map_snd_apply]
    exact congrArg (fun p => p b) h1
  have hterm : ∀ a : α, J1 (a, b) * J2 (b, c) / μ2 b
      = (J1 (a, b) / μ2 b) * J2 (b, c) := fun a => by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  simp_rw [hterm, ← Finset.sum_mul, ← ENNReal.sum_div, hS1]
  by_cases h0 : μ2 b = 0
  · have hJ : J2 (b, c) = 0 :=
      apply_eq_zero_of_map_fst_eq_zero (by rw [h2]; exact h0) c
    simp [hJ, h0]
  · rw [ENNReal.div_self h0 (μ2.apply_ne_top b), one_mul]

/-- The expected distance under a glued coupling is at most the sum
of the expected distances under the two couplings, by the triangle
inequality. -/
private theorem glueCoupling_dist_le {α : Type*} [PseudoMetricSpace α]
    [Fintype α] {J1 J2 : PMF (α × α)} {μ2 : PMF α}
    (h1 : J1.map Prod.snd = μ2) (h2 : J2.map Prod.fst = μ2) :
    ∑ z, ((glueCoupling J1 J2 μ2 h1 h2) z).toReal * dist z.1 z.2 ≤
      (∑ z, (J1 z).toReal * dist z.1 z.2)
        + (∑ z, (J2 z).toReal * dist z.1 z.2) := by
  have hS1r : ∀ b : α, ∑ a, (J1 (a, b)).toReal = (μ2 b).toReal := by
    intro b
    have h : ∑ a, J1 (a, b) = μ2 b := by
      rw [← map_snd_apply]
      exact congrArg (fun p => p b) h1
    rw [← h, ENNReal.toReal_sum fun a _ => J1.apply_ne_top (a, b)]
  have hS2r : ∀ b : α, ∑ c, (J2 (b, c)).toReal = (μ2 b).toReal := by
    intro b
    have h : ∑ c, J2 (b, c) = μ2 b := by
      rw [← map_fst_apply]
      exact congrArg (fun p => p b) h2
    rw [← h, ENNReal.toReal_sum fun c _ => J2.apply_ne_top (b, c)]
  have hne : ∀ a b c : α, J1 (a, b) * J2 (b, c) / μ2 b ≠ ∞ := by
    intro a b c
    by_cases h0 : μ2 b = 0
    · have hJ : J1 (a, b) = 0 :=
        apply_eq_zero_of_map_snd_eq_zero (by rw [h1]; exact h0) a
      rw [hJ]
      simp
    · exact ENNReal.div_ne_top
        (ENNReal.mul_ne_top (J1.apply_ne_top _) (J2.apply_ne_top _)) h0
  have hterm_toReal : ∀ a b c : α,
      ((J1 (a, b) * J2 (b, c) / μ2 b).toReal)
        = (J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal := by
    intro a b c
    rw [ENNReal.toReal_div, ENNReal.toReal_mul]
  have hsumr : ∀ a b : α,
      (∑ c, (J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
        = (J1 (a, b)).toReal := by
    intro a b
    have hfactor :
        (∑ c, (J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
          = (J1 (a, b)).toReal * ((∑ c, (J2 (b, c)).toReal) / (μ2 b).toReal) := by
      simp_rw [mul_div_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_div]
    rw [hfactor, hS2r b]
    by_cases h0 : (μ2 b).toReal = 0
    · have hμ : μ2 b = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (μ2 b)).mp h0 with h | h
        · exact h
        · exact absurd h (μ2.apply_ne_top b)
      have hJ : (J1 (a, b)).toReal = 0 := by
        rw [apply_eq_zero_of_map_snd_eq_zero (by rw [h1]; exact hμ) a]
        exact ENNReal.toReal_zero
      rw [hJ, h0, div_zero, mul_zero]
    · rw [div_self h0, mul_one]
  have hsumr2 : ∀ b c : α,
      (∑ a, (J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
        = (J2 (b, c)).toReal := by
    intro b c
    have hfactor :
        (∑ a, (J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
          = ((∑ a, (J1 (a, b)).toReal) / (μ2 b).toReal)
            * (J2 (b, c)).toReal := by
      have hterm : ∀ a : α, (J1 (a, b)).toReal * (J2 (b, c)).toReal
          / (μ2 b).toReal
          = ((J1 (a, b)).toReal / (μ2 b).toReal) * (J2 (b, c)).toReal :=
        fun a => by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.sum_div]
    rw [hfactor, hS1r b]
    by_cases h0 : (μ2 b).toReal = 0
    · have hμ : μ2 b = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff (μ2 b)).mp h0 with h | h
        · exact h
        · exact absurd h (μ2.apply_ne_top b)
      have hJ : (J2 (b, c)).toReal = 0 := by
        rw [apply_eq_zero_of_map_fst_eq_zero (by rw [h2]; exact hμ) c]
        exact ENNReal.toReal_zero
      rw [hJ, h0, div_zero, zero_mul]
    · rw [div_self h0, one_mul]
  have hLHS : (∑ z, ((glueCoupling J1 J2 μ2 h1 h2) z).toReal * dist z.1 z.2)
      = ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a c := by
    calc ∑ z, ((glueCoupling J1 J2 μ2 h1 h2) z).toReal * dist z.1 z.2
        = ∑ a, ∑ c, ((glueCoupling J1 J2 μ2 h1 h2) (a, c)).toReal
            * dist (a, c).1 (a, c).2 :=
          Fintype.sum_prod_type (fun z =>
            ((glueCoupling J1 J2 μ2 h1 h2) z).toReal * dist z.1 z.2)
      _ = ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a c := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro c _
          change ((glueCoupling J1 J2 μ2 h1 h2) (a, c)).toReal * dist a c
              = ∑ b, ((J1 (a, b)).toReal * (J2 (b, c)).toReal
                / (μ2 b).toReal) * dist a c
          have hglue : (glueCoupling J1 J2 μ2 h1 h2) (a, c)
              = ∑ b, J1 (a, b) * J2 (b, c) / μ2 b := rfl
          rw [hglue, ENNReal.toReal_sum fun b _ => hne a b c, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro b _
          rw [hterm_toReal]
  have hbound : (∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a c)
      ≤ ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * (dist a b + dist b c) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_left (dist_triangle a b c)
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg
  have hS1eq : (∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a b)
      = ∑ z, (J1 z).toReal * dist z.1 z.2 := by
    calc ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a b
        = ∑ a, ∑ b, ∑ c,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a b := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
      _ = ∑ a, ∑ b, (J1 (a, b)).toReal * dist a b := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [← Finset.sum_mul, hsumr]
      _ = ∑ z, (J1 z).toReal * dist z.1 z.2 := by
          exact (Fintype.sum_prod_type
            (fun z => (J1 z).toReal * dist z.1 z.2)).symm
  have hS2eq : (∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist b c)
      = ∑ z, (J2 z).toReal * dist z.1 z.2 := by
    calc ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist b c
        = ∑ c, ∑ a, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist b c :=
          Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist b c := by
          apply Finset.sum_congr rfl
          intro c _
          exact Finset.sum_comm
      _ = ∑ c, ∑ b, (J2 (b, c)).toReal * dist b c := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro b _
          rw [← Finset.sum_mul, hsumr2]
      _ = ∑ b, ∑ c, (J2 (b, c)).toReal * dist b c :=
          Finset.sum_comm
      _ = ∑ z, (J2 z).toReal * dist z.1 z.2 := by
          exact (Fintype.sum_prod_type
            (fun z => (J2 z).toReal * dist z.1 z.2)).symm
  rw [hLHS]
  calc ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a c
      ≤ ∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * (dist a b + dist b c) :=
        hbound
    _ = (∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist a b)
        + (∑ a, ∑ c, ∑ b,
          ((J1 (a, b)).toReal * (J2 (b, c)).toReal / (μ2 b).toReal)
            * dist b c) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ z, (J1 z).toReal * dist z.1 z.2)
        + (∑ z, (J2 z).toReal * dist z.1 z.2) := by
        rw [hS1eq, hS2eq]

/-- The diagonal coupling of a PMF with itself. -/
private noncomputable def diagCoupling {α : Type*} [Fintype α] (μ : PMF α) :
    PMF (α × α) :=
  PMF.ofFintype (fun p => if p.1 = p.2 then μ p.1 else 0) (by
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a : α, (∑ b, (if a = b then μ a else 0)) = μ a :=
      fun a => by simp
    simp_rw [hinner]
    exact PMF_sum_eq_one μ)

private theorem diagCoupling_map_fst {α : Type*} [Fintype α] (μ : PMF α) :
    (diagCoupling μ).map Prod.fst = μ := by
  ext a
  rw [map_fst_apply]
  change (∑ b, if a = b then μ a else 0) = μ a
  simp

private theorem diagCoupling_map_snd {α : Type*} [Fintype α] (μ : PMF α) :
    (diagCoupling μ).map Prod.snd = μ := by
  ext b
  rw [map_snd_apply]
  change (∑ a, if a = b then μ a else 0) = μ b
  simp

private theorem diagCoupling_dist {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (μ : PMF α) :
    ∑ z, ((diagCoupling μ) z).toReal * dist z.1 z.2 = 0 := by
  apply Finset.sum_eq_zero
  intro z _
  by_cases h : z.1 = z.2
  · rw [h, dist_self, mul_zero]
  · have hz : (diagCoupling μ) z = 0 := by
      change (if z.1 = z.2 then μ z.1 else 0) = 0
      rw [ite_eq_right h]
    rw [hz]
    simp

/-- A coupling for an arbitrary pair, built by gluing the adjacent
couplings along a `Path`: the diagonal coupling at the base, and the
glued coupling at a step, with the expected distance adding over the
step by the path's distance hypothesis. -/
private theorem coupling_of_path {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (K : α → PMF α) (Adj : α → α → Prop)
    (Cadj : ∀ x y, Adj x y → PMF (α × α))
    (hCadj_fst : ∀ x y (h : Adj x y), (Cadj x y h).map Prod.fst = K x)
    (hCadj_snd : ∀ x y (h : Adj x y), (Cadj x y h).map Prod.snd = K y)
    {β : ℝ}
    (hcontract_adj : ∀ x y (h : Adj x y),
      ∑ z, ((Cadj x y h) z).toReal * dist z.1 z.2 ≤ β * dist x y)
    {x z : α} (hpath : Path Adj dist x z) :
    ∃ J : PMF (α × α), J.map Prod.fst = K x ∧ J.map Prod.snd = K z ∧
      (∑ w, (J w).toReal * dist w.1 w.2) ≤ β * dist x z := by
  induction hpath with
  | refl x =>
      refine ⟨diagCoupling (K x), diagCoupling_map_fst _,
        diagCoupling_map_snd _, ?_⟩
      rw [diagCoupling_dist, dist_self, mul_zero]
  | step h hd hpath ih =>
      obtain ⟨J2, h2fst, h2snd, h2dist⟩ := ih
      refine ⟨glueCoupling (Cadj _ _ h) J2 (K _) (hCadj_snd _ _ h) h2fst,
        ?_, ?_, ?_⟩
      · rw [glueCoupling_map_fst (hCadj_snd _ _ h) h2fst, hCadj_fst _ _ h]
      · rw [glueCoupling_map_snd (hCadj_snd _ _ h) h2fst, h2snd]
      · calc ∑ w, ((glueCoupling (Cadj _ _ h) J2 (K _)
              (hCadj_snd _ _ h) h2fst) w).toReal * dist w.1 w.2
            ≤ (∑ w, ((Cadj _ _ h) w).toReal * dist w.1 w.2)
              + (∑ w, (J2 w).toReal * dist w.1 w.2) :=
            glueCoupling_dist_le (hCadj_snd _ _ h) h2fst
        _ ≤ β * dist _ _ + β * dist _ _ :=
            add_le_add (hcontract_adj _ _ h) h2dist
        _ = β * dist _ _ := by rw [hd, mul_add]

/-- Coupling bound from a contraction assumed for every pair: the
iterated coupling contracts the expected distance, and the coupling
inequality turns that into a total-variation bound. -/
private theorem coupling_tv {α : Type*} [PseudoMetricSpace α] [Fintype α]
    (K : α → PMF α) (C : α → α → PMF (α × α))
    (hC_fst : ∀ x y, (C x y).map Prod.fst = K x)
    (hC_snd : ∀ x y, (C x y).map Prod.snd = K y)
    {β δ : ℝ} (hβ : β ≤ 1) (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y)
    (hcontract : ∀ x y, ∑ z, (C x y z).toReal * dist z.1 z.2 ≤
      β * dist x y)
    (x y : α) (t : ℕ) :
    tvDist (chainDist K x t) (chainDist K y t) ≤ β ^ t * dist x y / δ := by
  have hfst : (JCoupling C x y t).map Prod.fst = chainDist K x t :=
    JCoupling_map_fst K C hC_fst x y t
  have hsnd : (JCoupling C x y t).map Prod.snd = chainDist K y t :=
    JCoupling_map_snd K C hC_snd x y t
  have hdecay : ∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2
      ≤ β ^ t * dist x y :=
    JCoupling_dist_le C hcontract x y t
  have hcouple := tvDist_map_le (JCoupling C x y t)
  rw [hfst, hsnd] at hcouple
  have hmass := mass_le_dist_div (JCoupling C x y t) hδ hdist
  calc tvDist (chainDist K x t) (chainDist K y t)
      ≤ ∑ z, ((JCoupling C x y t) z).toReal
        * (if z.1 = z.2 then (0 : ℝ) else 1) := hcouple
    _ ≤ (∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2) / δ := hmass
    _ ≤ β ^ t * dist x y / δ := (div_le_div_iff_of_pos_right hδ).mpr hdecay

/-- Path coupling bound: suppose `Cadj x y` is a one-step coupling
of `K x` and `K y` for every *adjacent* pair `x y`, and the coupled
distance contracts in expectation by `β ≤ 1` on adjacent pairs.
On a finite metric space whose nonzero distances are at least
`δ > 0`, and where every two points are joined by a `Path` (adjacent
steps with additive distance), the chains started at `x`, `y`
satisfy `tvDist ≤ β^t * dist x y / δ` after `t` steps. The
all-pairs coupling is obtained by gluing the adjacent couplings
along the path, then iterating it. -/
theorem path_coupling_tv {α : Type*} [PseudoMetricSpace α] [Fintype α]
    (K : α → PMF α)
    (Adj : α → α → Prop)
    (Cadj : ∀ x y, Adj x y → PMF (α × α))
    (hCadj_fst : ∀ x y (h : Adj x y), (Cadj x y h).map Prod.fst = K x)
    (hCadj_snd : ∀ x y (h : Adj x y), (Cadj x y h).map Prod.snd = K y)
    {β δ : ℝ} (hβ : β ≤ 1) (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y)
    (hcontract_adj : ∀ x y (h : Adj x y),
      ∑ z, ((Cadj x y h) z).toReal * dist z.1 z.2 ≤ β * dist x y)
    (hpath : ∀ x y, Path Adj dist x y)
    (x y : α) (t : ℕ) :
    tvDist (chainDist K x t) (chainDist K y t) ≤ β ^ t * dist x y / δ := by
  choose C hC_fst hC_snd hC_contract using
    fun x y => coupling_of_path K Adj Cadj hCadj_fst hCadj_snd
      hcontract_adj (hpath x y)
  exact coupling_tv K C hC_fst hC_snd hβ hδ hdist hC_contract x y t

end MathlibExt.Probability.PathCoupling
