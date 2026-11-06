/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

section
open Set

namespace MathlibExt.Analysis.FunctionalAnalysis.GeometricWanted

/-! ### Step 1–2: the canonical isometry `E →ₗᵢ C(B_{E*}, ℝ)` (Hahn–Banach + Banach–Alaoglu). -/

/-- The closed unit ball of the dual space, seen inside the weak-* dual `WeakDual ℝ E`. -/
private def dualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (WeakDual ℝ E) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1

private theorem isCompact_dualBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsCompact (dualBall E) :=
  WeakDual.isCompact_closedBall 0 1

private instance instCompactSpaceDualBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CompactSpace (dualBall E) := isCompact_iff_compactSpace.mp isCompact_dualBall

private theorem mem_dualBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : WeakDual ℝ E} : φ ∈ dualBall E ↔ ‖WeakDual.toStrongDual φ‖ ≤ 1 := by
  simp [dualBall]

/-- Evaluation `φ ↦ φ x` as a continuous function on the (compact) dual ball. -/
private noncomputable def evalCM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    C(dualBall E, ℝ) :=
  ⟨fun φ => (φ : WeakDual ℝ E) x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩

@[simp] private theorem evalCM_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (φ : dualBall E) : evalCM x φ = (φ : WeakDual ℝ E) x := rfl

/-- The canonical linear isometric embedding `E →ₗᵢ C(B_{E*}, ℝ)`. -/
private noncomputable def toCK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗᵢ[ℝ] C(dualBall E, ℝ) where
  toFun := evalCM
  map_add' x y := by ext φ; simp [map_add]
  map_smul' c x := by ext φ; simp [map_smul]
  norm_map' x := by
    change ‖evalCM x‖ = ‖x‖
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg x)]
      intro φ
      rw [evalCM_apply]
      calc ‖(φ : WeakDual ℝ E) x‖
          = ‖(WeakDual.toStrongDual (φ : WeakDual ℝ E)) x‖ := by rw [WeakDual.toStrongDual_apply]
        _ ≤ ‖WeakDual.toStrongDual (φ : WeakDual ℝ E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
        _ ≤ 1 * ‖x‖ := by gcongr; exact (mem_dualBall.mp φ.2)
        _ = ‖x‖ := one_mul _
    · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ x
      have hmem : StrongDual.toWeakDual g ∈ dualBall E := by
        rw [mem_dualBall]; simpa using hg1
      calc ‖x‖ = |g x| := by rw [hgx]; exact (abs_of_nonneg (norm_nonneg x)).symm
        _ = ‖evalCM x ⟨StrongDual.toWeakDual g, hmem⟩‖ := by
              rw [evalCM_apply, Real.norm_eq_abs]; rfl
        _ ≤ ‖evalCM x‖ := ContinuousMap.norm_coe_le_norm _ _

/-! ### Precomposition by a continuous surjection is a linear isometry. -/

private def precompLI {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    [TopologicalSpace β] [CompactSpace β] (g : C(α, β)) (hg : Function.Surjective g) :
    C(β, ℝ) →ₗᵢ[ℝ] C(α, ℝ) where
  toFun f := f.comp g
  map_add' f₁ f₂ := by ext a; simp
  map_smul' c f := by ext a; simp
  norm_map' f := by
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg f)]
      intro a
      simpa using ContinuousMap.norm_coe_le_norm f (g a)
    · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
      intro b
      obtain ⟨a, rfl⟩ := hg b
      simpa using ContinuousMap.norm_coe_le_norm (f.comp g) a

private instance instCompactSpaceCantor : CompactSpace (cantorSet) :=
  isCompact_iff_compactSpace.mp isCompact_cantorSet

/-- The Cantor set continuously surjects onto the (compact metric) dual ball
(Hausdorff–Alexandroff, via `cantorSet ≃ₜ (ℕ → Bool)`). -/
private theorem exists_cantor_surjection (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ f : cantorSet → dualBall E, Continuous f ∧ Function.Surjective f := by
  have : Nonempty (dualBall E) := ⟨⟨0, by rw [mem_dualBall]; simp⟩⟩
  have : TopologicalSpace.MetrizableSpace (dualBall E) :=
    WeakDual.metrizable_of_isCompact ℝ E (dualBall E) isCompact_dualBall
  let _inst : MetricSpace (dualBall E) := TopologicalSpace.metrizableSpaceMetric (dualBall E)
  obtain ⟨ψ, hψc, hψs⟩ := exists_nat_bool_continuous_surjective_of_compact (dualBall E)
  exact ⟨ψ ∘ cantorSetHomeomorphNatToBool,
    hψc.comp cantorSetHomeomorphNatToBool.continuous,
    hψs.comp cantorSetHomeomorphNatToBool.surjective⟩

/-! ### Step 3: the linear isometric extension `C(cantorSet, ℝ) →ₗᵢ C([0,1], ℝ)`.

For `f` continuous on the Cantor set, extend it to `[0,1]` by linear interpolation across the
complementary gaps.  `lo y` / `hi y` are the closest Cantor points on either side of `y`. -/

private theorem one_mem_cantorSet : (1:ℝ) ∈ cantorSet := by
  rw [cantorSet, mem_iInter]; intro n
  induction n with
  | zero => rw [preCantorSet_zero]; norm_num
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

private theorem cantor_subset : cantorSet ⊆ Icc (0:ℝ) 1 := cantorSet_subset_unitInterval

private noncomputable def lo (y : ℝ) : ℝ := sSup (cantorSet ∩ Iic y)
private noncomputable def hi (y : ℝ) : ℝ := sInf (cantorSet ∩ Ici y)

private theorem Slo_bddAbove {y : ℝ} : BddAbove (cantorSet ∩ Iic y) :=
  ⟨1, fun _ hs => (cantor_subset hs.1).2⟩
private theorem Shi_bddBelow {y : ℝ} : BddBelow (cantorSet ∩ Ici y) :=
  ⟨0, fun _ hs => (cantor_subset hs.1).1⟩

private theorem lo_mem {y : ℝ} (hy : 0 ≤ y) : lo y ∈ cantorSet ∩ Iic y :=
  (isClosed_cantorSet.inter isClosed_Iic).csSup_mem ⟨0, zero_mem_cantorSet, hy⟩ Slo_bddAbove
private theorem hi_mem {y : ℝ} (hy : y ≤ 1) : hi y ∈ cantorSet ∩ Ici y :=
  (isClosed_cantorSet.inter isClosed_Ici).csInf_mem ⟨1, one_mem_cantorSet, hy⟩ Shi_bddBelow

private theorem lo_cantor {y : ℝ} (hy : 0 ≤ y) : lo y ∈ cantorSet := (lo_mem hy).1
private theorem lo_le {y : ℝ} (hy : 0 ≤ y) : lo y ≤ y := (lo_mem hy).2
private theorem hi_cantor {y : ℝ} (hy : y ≤ 1) : hi y ∈ cantorSet := (hi_mem hy).1
private theorem le_hi {y : ℝ} (hy : y ≤ 1) : y ≤ hi y := (hi_mem hy).2

private theorem le_lo {y s : ℝ} (hs : s ∈ cantorSet) (hsy : s ≤ y) : s ≤ lo y :=
  le_csSup Slo_bddAbove ⟨hs, hsy⟩
private theorem hi_le {y s : ℝ} (hs : s ∈ cantorSet) (hys : y ≤ s) : hi y ≤ s :=
  csInf_le Shi_bddBelow ⟨hs, hys⟩

private theorem lo_le_hi {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : lo y ≤ hi y :=
  le_trans (lo_le hy0) (le_hi hy1)

private theorem lo_eq_self {s : ℝ} (hs : s ∈ cantorSet) : lo s = s :=
  le_antisymm (lo_le (cantor_subset hs).1) (le_lo hs le_rfl)
private theorem hi_eq_self {s : ℝ} (hs : s ∈ cantorSet) : hi s = s :=
  le_antisymm (hi_le hs le_rfl) (le_hi (cantor_subset hs).2)

open Classical in
/-- `f` extended by `0` off the Cantor set; used only at Cantor points. -/
private noncomputable def Fext (f : C(cantorSet, ℝ)) (s : ℝ) : ℝ :=
  if h : s ∈ cantorSet then f ⟨s, h⟩ else 0

private theorem Fext_mem (f : C(cantorSet, ℝ)) {s : ℝ} (h : s ∈ cantorSet) :
    Fext f s = f ⟨s, h⟩ := dite_eq_left h

private noncomputable def frac (y : ℝ) : ℝ :=
  if hi y = lo y then 0 else (y - lo y) / (hi y - lo y)

private noncomputable def gval (f : C(cantorSet, ℝ)) (y : ℝ) : ℝ :=
  Fext f (lo y) + (Fext f (hi y) - Fext f (lo y)) * frac y

private theorem frac_mem {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : frac y ∈ Icc (0:ℝ) 1 := by
  unfold frac; split_ifs with h
  · simp
  · have hlh : lo y < hi y := lt_of_le_of_ne (lo_le_hi hy0 hy1) (fun e => h e.symm)
    refine ⟨div_nonneg (by linarith [lo_le hy0]) (by linarith), ?_⟩
    rw [div_le_one (by linarith)]; linarith [le_hi hy1]

private theorem gval_conv (f : C(cantorSet, ℝ)) (y : ℝ) :
    gval f y = (1 - frac y) * Fext f (lo y) + frac y * Fext f (hi y) := by
  unfold gval; ring

private theorem abs_Fext_le (f : C(cantorSet, ℝ)) {s : ℝ} (hs : s ∈ cantorSet) :
    |Fext f s| ≤ ‖f‖ := by
  rw [Fext_mem f hs, ← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm f ⟨s, hs⟩

private theorem gval_abs_le (f : C(cantorSet, ℝ)) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |gval f y| ≤ ‖f‖ := by
  have ht := frac_mem hy0 hy1
  have hlo := abs_le.mp (abs_Fext_le f (lo_cantor hy0))
  have hhi := abs_le.mp (abs_Fext_le f (hi_cantor hy1))
  rw [gval_conv, abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [ht.1, ht.2, hlo.1, hlo.2, hhi.1, hhi.2,
      mul_nonneg ht.1 (by linarith [hhi.2] : (0:ℝ) ≤ ‖f‖ - Fext f (hi y)),
      mul_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - frac y)
        (by linarith [hlo.2] : (0:ℝ) ≤ ‖f‖ - Fext f (lo y)),
      mul_nonneg ht.1 (by linarith [hhi.1] : (0:ℝ) ≤ Fext f (hi y) + ‖f‖),
      mul_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - frac y)
        (by linarith [hlo.1] : (0:ℝ) ≤ Fext f (lo y) + ‖f‖)]

private theorem gval_eq {s : ℝ} (hs : s ∈ cantorSet) (f : C(cantorSet, ℝ)) :
    gval f s = f ⟨s, hs⟩ := by
  have hlo := lo_eq_self hs
  have hhi := hi_eq_self hs
  unfold gval
  rw [hlo, hhi]
  simp [Fext_mem f hs]

private theorem frac_eq (y : ℝ) : frac y = (y - lo y) / (hi y - lo y) := by
  unfold frac; split_ifs with h
  · rw [h, sub_self, div_zero]
  · rfl

private theorem no_between {y s : ℝ} (_hy0 : 0 ≤ y) (_hy1 : y ≤ 1) (hs : s ∈ cantorSet)
    (h1 : lo y < s) (h2 : s < hi y) : False := by
  rcases le_total s y with h | h
  · exact absurd (le_lo hs h) (not_le.mpr h1)
  · exact absurd (hi_le hs h) (not_le.mpr h2)

private theorem lo_const {y₀ y : ℝ} (hy0 : 0 ≤ y₀) (hy1 : y₀ ≤ 1)
    (hya : lo y₀ < y) (hyb : y < hi y₀) : lo y = lo y₀ := by
  have hy0' : 0 ≤ y := le_trans (cantor_subset (lo_cantor hy0)).1 hya.le
  refine le_antisymm ?_ (le_lo (lo_cantor hy0) hya.le)
  by_contra hc
  push Not at hc
  exact no_between hy0 hy1 (lo_cantor hy0') hc (lt_of_le_of_lt (lo_le hy0') hyb)

private theorem hi_const {y₀ y : ℝ} (hy0 : 0 ≤ y₀) (hy1 : y₀ ≤ 1)
    (hya : lo y₀ < y) (hyb : y < hi y₀) : hi y = hi y₀ := by
  have hy1' : y ≤ 1 := le_trans hyb.le (cantor_subset (hi_cantor hy1)).2
  refine le_antisymm (hi_le (hi_cantor hy1) hyb.le) ?_
  by_contra hc
  push Not at hc
  exact no_between hy0 hy1 (hi_cantor hy1') (lt_of_lt_of_le hya (le_hi hy1')) hc

/-- Weighted gap term is small: either the gap is short (so `f` barely moves) or it is long
(so the interpolation weight is tiny).  This is the heart of the continuity estimate. -/
private theorem gap_term (f : C(cantorSet, ℝ)) {a b u ε δ' : ℝ}
    (ha : a ∈ cantorSet) (hb : b ∈ cantorSet) (hab : a ≤ b)
    (hu0 : 0 ≤ u) (huab : u ≤ b - a) (hε : 0 < ε)
    (hunif : ∀ s ∈ cantorSet, ∀ t ∈ cantorSet, |s - t| < δ' → |Fext f s - Fext f t| < ε)
    (hδ' : 0 < δ') (_hu_δ' : u < δ') (hu_reg : u < ε * δ' / (2 * (‖f‖ + 1))) :
    (u / (b - a)) * |Fext f b - Fext f a| < ε := by
  have hMpos : (0:ℝ) < 2 * (‖f‖ + 1) := by positivity
  have hle : |Fext f b - Fext f a| ≤ 2 * (‖f‖ + 1) := by
    obtain ⟨h1a, h1b⟩ := abs_le.mp (abs_Fext_le f ha)
    obtain ⟨h2a, h2b⟩ := abs_le.mp (abs_Fext_le f hb)
    rw [abs_le]; constructor <;> nlinarith [norm_nonneg f]
  rcases eq_or_lt_of_le hab with hEq | hlt
  · have hu : u = 0 := le_antisymm (by rw [← hEq] at huab; linarith) hu0
    rw [hu]; simp only [zero_div, zero_mul, gt_iff_lt]; positivity
  · have hbma : 0 < b - a := by linarith
    rcases lt_or_ge (b - a) δ' with hreg | hreg
    · have hfab : |Fext f b - Fext f a| < ε :=
        hunif b hb a ha (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]; exact hreg)
      have hratio : u / (b - a) ≤ 1 := (div_le_one hbma).mpr huab
      calc (u / (b - a)) * |Fext f b - Fext f a|
          ≤ 1 * |Fext f b - Fext f a| := mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
        _ = |Fext f b - Fext f a| := one_mul _
        _ < ε := hfab
    · have hratio : u / (b - a) < ε / (2 * (‖f‖ + 1)) := by
        have step1 : u / (b - a) ≤ u / δ' := div_le_div_of_nonneg_left hu0 hδ' hreg
        have step2 : u / δ' < ε / (2 * (‖f‖ + 1)) := by
          rw [div_lt_iff₀ hδ']
          calc u < ε * δ' / (2 * (‖f‖ + 1)) := hu_reg
            _ = ε / (2 * (‖f‖ + 1)) * δ' := by ring
        exact lt_of_le_of_lt step1 step2
      calc (u / (b - a)) * |Fext f b - Fext f a|
          ≤ (u / (b - a)) * (2 * (‖f‖ + 1)) :=
            mul_le_mul_of_nonneg_left hle (div_nonneg hu0 hbma.le)
        _ < (ε / (2 * (‖f‖ + 1))) * (2 * (‖f‖ + 1)) := mul_lt_mul_of_pos_right hratio hMpos
        _ = ε := by field_simp

private theorem gval_continuousOn (f : C(cantorSet, ℝ)) :
    ContinuousOn (gval f) (Icc (0:ℝ) 1) := by
  have huc : UniformContinuous (fun s : cantorSet => f s) :=
    CompactSpace.uniformContinuous_of_continuous (map_continuous f)
  have hunif : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ cantorSet, ∀ t ∈ cantorSet,
      |s - t| < δ → |Fext f s - Fext f t| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.mp huc ε hε
    refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
    have hd := hδε (a := ⟨s, hs⟩) (b := ⟨t, ht⟩)
      (by rw [Subtype.dist_eq, Real.dist_eq]; exact hst)
    rw [Fext_mem f hs, Fext_mem f ht, ← Real.dist_eq]; exact hd
  intro y₀ hy₀
  obtain ⟨hy0, hy1⟩ := hy₀
  by_cases hy₀c : y₀ ∈ cantorSet
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ', hδ', hunifδ'⟩ := hunif (ε / 2) (by linarith)
    refine ⟨min δ' (ε / 2 * δ' / (2 * (‖f‖ + 1))), lt_min hδ' (by positivity),
      fun y hy hdist => ?_⟩
    rw [Real.dist_eq] at hdist
    have hy0' : (0:ℝ) ≤ y := hy.1
    have hy1' : y ≤ 1 := hy.2
    have hd1 : |y - y₀| < δ' := lt_of_lt_of_le hdist (min_le_left _ _)
    have hd2 : |y - y₀| < ε / 2 * δ' / (2 * (‖f‖ + 1)) := lt_of_lt_of_le hdist (min_le_right _ _)
    have ht := frac_mem hy0' hy1'
    have haey : lo y ≤ y := lo_le hy0'
    have hyeb : y ≤ hi y := le_hi hy1'
    have hfe := frac_eq y
    have hg0 : gval f y₀ = Fext f y₀ := by rw [gval_eq hy₀c f, Fext_mem f hy₀c]
    rw [Real.dist_eq, hg0]
    by_cases hyeq : hi y = lo y
    · have hyc : y ∈ cantorSet := by
        have hey : lo y = y := le_antisymm haey (hyeq ▸ hyeb)
        rw [← hey]; exact lo_cantor hy0'
      rw [show gval f y = Fext f y from by rw [gval_eq hyc f, Fext_mem f hyc]]
      have := hunifδ' y hyc y₀ hy₀c hd1
      linarith
    · have hlt : lo y < hi y := lt_of_le_of_ne (le_trans haey hyeb) (fun e => hyeq e.symm)
      have hne : hi y - lo y ≠ 0 := by linarith
      have hpos : y₀ ≤ lo y ∨ hi y ≤ y₀ := by
        by_contra hcon; push Not at hcon
        exact no_between hy0' hy1' hy₀c hcon.1 hcon.2
      rcases hpos with hcase | hcase
      · have habsy : |y - y₀| = y - y₀ := abs_of_nonneg (by linarith)
        rw [habsy] at hd1 hd2
        have hla : |Fext f (lo y) - Fext f y₀| < ε / 2 := by
          apply hunifδ' (lo y) (lo_cantor hy0') y₀ hy₀c
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ lo y - y₀)]; linarith
        have hgap : frac y * |Fext f (hi y) - Fext f (lo y)| < ε / 2 := by
          rw [hfe]
          exact gap_term f (lo_cantor hy0') (hi_cantor hy1') (le_of_lt hlt)
            (by linarith) (by linarith) (by linarith) hunifδ' hδ'
            (by linarith) (by linarith)
        have htri1 : |gval f y - Fext f y₀| ≤
            |Fext f (lo y) - Fext f y₀| + frac y * |Fext f (hi y) - Fext f (lo y)| := by
          rw [gval_conv]
          have e : (1 - frac y) * Fext f (lo y) + frac y * Fext f (hi y) - Fext f y₀
                 = (Fext f (lo y) - Fext f y₀) + frac y * (Fext f (hi y) - Fext f (lo y)) := by ring
          rw [e]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_nonneg ht.1]
        linarith
      · have habsy : |y - y₀| = y₀ - y := by rw [abs_of_nonpos (by linarith)]; ring
        rw [habsy] at hd1 hd2
        have hofe : 1 - frac y = (hi y - y) / (hi y - lo y) := by
          rw [hfe, ← div_self hne, div_sub_div_same]; congr 1; ring
        have hhi : |Fext f (hi y) - Fext f y₀| < ε / 2 := by
          apply hunifδ' (hi y) (hi_cantor hy1') y₀ hy₀c
          rw [abs_of_nonpos (by linarith : hi y - y₀ ≤ 0)]; linarith
        have hgap : (1 - frac y) * |Fext f (hi y) - Fext f (lo y)| < ε / 2 := by
          rw [hofe]
          exact gap_term f (lo_cantor hy0') (hi_cantor hy1') (le_of_lt hlt)
            (by linarith) (by linarith) (by linarith) hunifδ' hδ'
            (by linarith) (by linarith)
        have htri2 : |gval f y - Fext f y₀| ≤
            |Fext f (hi y) - Fext f y₀| + (1 - frac y) * |Fext f (hi y) - Fext f (lo y)| := by
          rw [gval_conv]
          have e : (1 - frac y) * Fext f (lo y) + frac y * Fext f (hi y) - Fext f y₀
                 = (Fext f (hi y) - Fext f y₀) + (1 - frac y) *
                     (Fext f (lo y) - Fext f (hi y)) := by
            ring
          rw [e]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 - frac y from by linarith [ht.2]),
            abs_sub_comm (Fext f (lo y)) (Fext f (hi y))]
        linarith
  · have ha : lo y₀ ∈ cantorSet := lo_cantor hy0
    have hb : hi y₀ ∈ cantorSet := hi_cantor hy1
    have hay : lo y₀ < y₀ := lt_of_le_of_ne (lo_le hy0) (fun e => hy₀c (e ▸ ha))
    have hyb : y₀ < hi y₀ := lt_of_le_of_ne (le_hi hy1) (fun e => hy₀c (e.symm ▸ hb))
    have key : ∀ y ∈ Ioo (lo y₀) (hi y₀),
        gval f y = Fext f (lo y₀)
          + (Fext f (hi y₀) - Fext f (lo y₀)) * ((y - lo y₀) / (hi y₀ - lo y₀)) := by
      intro y hy
      have hc1 := lo_const hy0 hy1 hy.1 hy.2
      have hc2 := hi_const hy0 hy1 hy.1 hy.2
      unfold gval frac
      rw [hc1, hc2, ite_eq_right (fun e => (ne_of_lt (lt_trans hay hyb)) e.symm)]
    have hcont : ContinuousAt (fun y : ℝ =>
        Fext f (lo y₀)
          + (Fext f (hi y₀) - Fext f (lo y₀)) * ((y - lo y₀) / (hi y₀ - lo y₀))) y₀ := by
      fun_prop
    have hEq : (gval f) =ᶠ[nhds y₀]
        (fun y => Fext f (lo y₀)
          + (Fext f (hi y₀) - Fext f (lo y₀)) * ((y - lo y₀) / (hi y₀ - lo y₀))) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds hay hyb) key
    exact (hcont.congr hEq.symm).continuousWithinAt

private noncomputable def gvalCM (f : C(cantorSet, ℝ)) : C(Icc (0:ℝ) 1, ℝ) :=
  ⟨fun y => gval f y.1, (gval_continuousOn f).domRestrict⟩

@[simp] private theorem gvalCM_apply (f : C(cantorSet, ℝ)) (y : Icc (0 : ℝ) 1) :
    gvalCM f y = gval f y.1 := rfl

private theorem Fext_add (f g : C(cantorSet, ℝ)) (s : ℝ) :
    Fext (f + g) s = Fext f s + Fext g s := by unfold Fext; split_ifs with h <;> simp
private theorem Fext_smul (c : ℝ) (f : C(cantorSet, ℝ)) (s : ℝ) :
    Fext (c • f) s = c * Fext f s := by unfold Fext; split_ifs with h <;> simp

/-- The linear isometric extension operator `C(cantorSet, ℝ) →ₗᵢ C([0,1], ℝ)`. -/
private noncomputable def extendLI : C(cantorSet, ℝ) →ₗᵢ[ℝ] C(Icc (0:ℝ) 1, ℝ) where
  toFun := gvalCM
  map_add' f g := by
    ext y; simp only [gvalCM_apply, ContinuousMap.add_apply]
    unfold gval; rw [Fext_add, Fext_add]; ring
  map_smul' c f := by
    ext y; simp only [gvalCM_apply, ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    unfold gval; rw [Fext_smul, Fext_smul]; ring
  norm_map' f := by
    change ‖gvalCM f‖ = ‖f‖
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg f)]
      intro y
      rw [gvalCM_apply, Real.norm_eq_abs]
      exact gval_abs_le f y.2.1 y.2.2
    · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
      intro s
      calc ‖f s‖ = ‖gvalCM f ⟨s.1, cantor_subset s.2⟩‖ := by
            simp only [gvalCM_apply]; rw [gval_eq s.2 f]
        _ ≤ ‖gvalCM f‖ := ContinuousMap.norm_coe_le_norm _ _

/-! ### Assembly. -/

/--
**Banach–Mazur embedding theorem.** Every separable real Banach space $E$ admits a linear
isometric embedding $e \colon E \to C([0, 1], \mathbb{R})$ into the space of continuous real
functions on $[0, 1]$ with the supremum norm, such that the range of $e$ is closed.

Proves `Wanted` entry `banachMazur_embedding`.

Source: S. Banach and S. Mazur 1932 embedding theorem; Banach, Theorie des
operations lineaires; Henson-Michalewski, separable Banach as universal space; Lean states
separable real Banach case with `E →ₗᵢ[ℝ] C(Icc 0 1, ℝ)` and `IsClosed (range)`.
-/
theorem banachMazur_embedding
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (e : E →ₗᵢ[ℝ] C(Set.Icc (0:ℝ) 1, ℝ)), IsClosed
        (Set.range (e : E → C(Set.Icc (0:ℝ) 1, ℝ))) := by
  obtain ⟨Φf, hΦc, hΦs⟩ := exists_cantor_surjection E
  let Φ : C(cantorSet, dualBall E) := ⟨Φf, hΦc⟩
  refine ⟨extendLI.comp ((precompLI Φ hΦs).comp toCK), ?_⟩
  exact (extendLI.comp ((precompLI Φ hΦs).comp
    toCK)).isometry.isUniformInducing.isComplete_range.isClosed

end MathlibExt.Analysis.FunctionalAnalysis.GeometricWanted
