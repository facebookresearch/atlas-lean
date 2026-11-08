/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.MetricSpace.PiNat

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.CountablyCompact

@[expose] public section

open Set Metric Filter Topology

private theorem exists_finset_norming_of_span_finset
    {𝕜 : Type*} [RCLike 𝕜]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : Finset (StrongDual 𝕜 W)) :
    ∃ G : Finset W, (∀ g ∈ G, ‖g‖ ≤ 1) ∧
      ∀ ψ ∈ Submodule.span 𝕜 (T : Set (StrongDual 𝕜 W)),
        ∃ g ∈ G, ‖ψ‖ ≤ 2 * ‖ψ g‖ := by
  classical
  let V := Submodule.span 𝕜 (T : Set (StrongDual 𝕜 W))
  have hfin : FiniteDimensional 𝕜 V := FiniteDimensional.span_finset 𝕜 T
  have hprop : ProperSpace V := FiniteDimensional.proper_rclike 𝕜 V
  let O : { w : W // ‖w‖ < 1 } → Set V :=
    fun w => { ψ | ‖(ψ : StrongDual 𝕜 W)‖ < 2 * ‖(ψ : StrongDual 𝕜 W) w‖ }
  have hopen : ∀ w : { w : W // ‖w‖ < 1 }, IsOpen (O w) := by
    intro w
    apply isOpen_lt
    · exact continuous_norm.comp continuous_subtype_val
    · apply Continuous.mul continuous_const
      apply Continuous.norm
      exact ((ContinuousLinearMap.apply 𝕜 𝕜 (w : W)).continuous.comp
        continuous_subtype_val)
  have hcover : Metric.sphere (0 : V) 1 ⊆ ⋃ w, O w := by
    intro ψ hψ
    have hV1 : ‖ψ‖ = 1 := by
      have h := Metric.mem_sphere.mp hψ
      have e : dist ψ (0 : V) = ‖ψ‖ := dist_zero_right ψ
      exact e.symm.trans h
    have hnorm1 : ‖(ψ : StrongDual 𝕜 W)‖ = 1 := hV1
    obtain ⟨w, hw1, hw2⟩ :=
      ContinuousLinearMap.exists_lt_apply_of_lt_opNorm (ψ : StrongDual 𝕜 W)
        (show (1/2 : ℝ) < ‖(ψ : StrongDual 𝕜 W)‖ by rw [hnorm1]; norm_num)
    rw [Set.mem_iUnion]
    refine ⟨⟨w, hw1⟩, ?_⟩
    change ‖(ψ : StrongDual 𝕜 W)‖ < 2 * ‖(ψ : StrongDual 𝕜 W) w‖
    rw [hnorm1]
    linarith [hw2]
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere _ _
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover O hopen hcover
  refine ⟨insert (0 : W) (t.image Subtype.val), ?_, ?_⟩
  · intro g hg
    rw [Finset.mem_insert, Finset.mem_image] at hg
    rcases hg with rfl | ⟨w, _, heq⟩
    · simp
    · subst heq
      exact le_of_lt w.property
  · intro ψ hψ
    by_cases hzero : ψ = 0
    · refine ⟨0, Finset.mem_insert_self 0 _, ?_⟩
      subst hzero
      simp
    · have hne : (0 : ℝ) ≠ ‖ψ‖ := fun h => hzero (norm_eq_zero.mp h.symm)
      have hpos : 0 < ‖ψ‖ := lt_of_le_of_ne (norm_nonneg _) hne
      let c : ℝ := ‖ψ‖
      have hcpos : 0 < c := hpos
      have hcne : c ≠ 0 := ne_of_gt hcpos
      let ψ' : V := ⟨((c⁻¹ : ℝ) : 𝕜) • ψ, V.smul_mem _ hψ⟩
      have hψ'norm : ‖(ψ' : StrongDual 𝕜 W)‖ = 1 := by
        change ‖(((c⁻¹ : ℝ) : 𝕜) • ψ)‖ = 1
        rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hcpos)]
        exact inv_mul_cancel₀ hcne
      have hψ'sph : ψ' ∈ Metric.sphere (0 : V) 1 := by
        have e : dist ψ' (0 : V) = ‖ψ'‖ := dist_zero_right ψ'
        have h1 : ‖ψ'‖ = 1 := hψ'norm
        rw [Metric.mem_sphere]
        exact e.trans h1
      have hmem := ht hψ'sph
      simp only [Set.mem_iUnion] at hmem
      obtain ⟨w, hwt, hwO⟩ := hmem
      refine ⟨(w : W), Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hwt, rfl⟩), ?_⟩
      have hO : ‖(ψ' : StrongDual 𝕜 W)‖ < 2 * ‖(ψ' : StrongDual 𝕜 W) (w : W)‖ := hwO
      rw [hψ'norm] at hO
      have hnormw : ‖(ψ' : StrongDual 𝕜 W) (w : W)‖ = c⁻¹ * ‖ψ (w : W)‖ := by
        change ‖((((c⁻¹ : ℝ) : 𝕜) • ψ) : StrongDual 𝕜 W) (w : W)‖ = _
        rw [smul_apply, norm_smul, RCLike.norm_ofReal,
          abs_of_pos (inv_pos.mpr hcpos)]
      rw [hnormw] at hO
      have hle : c ≤ 2 * ‖ψ (w : W)‖ := by
        have hmul := mul_le_mul_of_nonneg_left (le_of_lt hO) (le_of_lt hcpos)
        simp only [mul_one] at hmul
        have heq : c * (2 * (c⁻¹ * ‖ψ (w : W)‖)) = 2 * ‖ψ (w : W)‖ := by
          calc c * (2 * (c⁻¹ * ‖ψ (w : W)‖)) = (c * c⁻¹) * (2 * ‖ψ (w : W)‖) := by ring
            _ = 2 * ‖ψ (w : W)‖ := by rw [mul_inv_cancel₀ hcne, one_mul]
        rwa [heq] at hmul
      have hψc : ‖ψ‖ = c := rfl
      rw [hψc]
      exact hle

private theorem whitley_sequence
    {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (j : X →L[𝕜] StrongDual 𝕜 W) (Φ : StrongDual 𝕜 W) (A : Set X)
    (happrox : ∀ S : Finset W, ∀ ε > 0, ∃ a ∈ A, ∀ g ∈ S, ‖Φ g - j a g‖ < ε) :
    ∃ x : ℕ → X, ∃ G : ℕ → Finset W,
      (∀ n, x n ∈ A) ∧
      (∀ n, ∀ g ∈ G n, ‖g‖ ≤ 1) ∧
      (∀ n, ∀ ψ ∈ Submodule.span 𝕜 (↑(insert Φ ((fun i => j (x i)) '' Set.Iio n)) : Set
          (StrongDual 𝕜 W)),
        ∃ g ∈ G n, ‖ψ‖ ≤ 2 * ‖ψ g‖) ∧
      (∀ k n, k ≤ n → ∀ g ∈ G k, ‖Φ g - j (x n) g‖ < 1 / ((n : ℝ) + 1)) := by
  classical
  have hN6 : ∀ T : Finset (StrongDual 𝕜 W), ∃ G : Finset W,
      (∀ g ∈ G, ‖g‖ ≤ 1) ∧
      ∀ ψ ∈ Submodule.span 𝕜 (T : Set (StrongDual 𝕜 W)),
        ∃ g ∈ G, ‖ψ‖ ≤ 2 * ‖ψ g‖ :=
    fun T => exists_finset_norming_of_span_finset T
  choose nset hnset using hN6
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hpick : ∀ S : Finset W, ∀ n : ℕ, ∃ a ∈ A,
      ∀ g ∈ S, ‖Φ g - j a g‖ < 1 / ((n : ℝ) + 1) := by
    intro S n
    exact happrox S _ (hpos n)
  choose pick hpick_mem hpick_bound using hpick
  -- state recursion
  let st : ℕ → Finset (StrongDual 𝕜 W) × Finset W :=
    fun n => Nat.rec (motive := fun _ => Finset (StrongDual 𝕜 W) × Finset W)
      (∅, ∅)
      (fun n ih => (insert (j (pick (ih.2 ∪ nset (insert Φ ih.1)) n)) ih.1,
        ih.2 ∪ nset (insert Φ ih.1))) n
  have hst0 : st 0 = (∅, ∅) := rfl
  have hstS : ∀ n, st (n + 1) =
      (insert (j (pick ((st n).2 ∪ nset (insert Φ (st n).1)) n)) (st n).1,
        (st n).2 ∪ nset (insert Φ (st n).1)) := fun n => rfl
  let G : ℕ → Finset W := fun n => nset (insert Φ (st n).1)
  let x : ℕ → X := fun n => pick ((st n).2 ∪ G n) n
  have hG : ∀ n, G n = nset (insert Φ (st n).1) := fun n => rfl
  have hx : ∀ n, x n = pick ((st n).2 ∪ G n) n := fun n => rfl
  -- invariants
  have hP : ∀ n, (st n).1 = Finset.image (fun i => j (x i)) (Finset.range n) := by
    intro n
    induction n with
    | zero => simp [hst0]
    | succ n ih =>
      have h1 : st (n + 1) =
          (insert (j (x n)) (st n).1, (st n).2 ∪ G n) := by
        rw [hstS n, hx n, hG n]
      have h2 : (st (n + 1)).1 = insert (j (x n)) (st n).1 := by rw [h1]
      rw [h2, ih, Finset.range_add_one, Finset.image_insert]
  have hS : ∀ n, (st n).2 = (Finset.range n).biUnion G := by
    intro n
    induction n with
    | zero => simp [hst0]
    | succ n ih =>
      have h1 : st (n + 1) =
          (insert (j (x n)) (st n).1, (st n).2 ∪ G n) := by
        rw [hstS n, hx n, hG n]
      have h2 : (st (n + 1)).2 = (st n).2 ∪ G n := by rw [h1]
      rw [h2, ih, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
  refine ⟨x, G, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hx n]
    exact hpick_mem _ _
  · intro n g hg
    rw [hG n] at hg
    exact (hnset _).1 g hg
  · intro n ψ hψ
    have hspan : Submodule.span 𝕜
        (↑(insert Φ ((fun i => j (x i)) '' Set.Iio n)) : Set (StrongDual 𝕜 W)) =
        Submodule.span 𝕜 (↑(insert Φ (st n).1) : Set (StrongDual 𝕜 W)) := by
      congr 1
      rw [hP n, Finset.coe_insert, Finset.coe_image, Finset.coe_range]
    rw [hspan] at hψ
    rw [hG n]
    exact (hnset _).2 ψ hψ
  · intro k n hkn g hg
    have hmem : g ∈ (st n).2 ∪ G n := by
      rcases eq_or_lt_of_le hkn with rfl | hlt
      · exact Finset.mem_union_right _ hg
      · have hkr : k ∈ Finset.range n := Finset.mem_range.mpr hlt
        have hsub : G k ⊆ (st n).2 := by
          rw [hS n]
          exact Finset.subset_biUnion_of_mem G hkr
        exact Finset.mem_union_left _ (hsub hg)
    rw [hx n]
    exact hpick_bound _ _ g hmem

private theorem WeakSpace_isClosed_image_toWeakSpace_of_isClosed_submodule
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Y : Submodule 𝕜 E) (hY : IsClosed (Y : Set E)) :
    IsClosed ((⇑(toWeakSpace 𝕜 E)) '' (Y : Set E)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hconv : Convex ℝ ((Submodule.restrictScalars ℝ Y : Submodule ℝ E) : Set E) :=
    Submodule.convex _
  have hcoe : ((Submodule.restrictScalars ℝ Y : Submodule ℝ E) : Set E) = (Y : Set E) := rfl
  rw [hcoe] at hconv
  have hclo := Convex.toWeakSpace_closure 𝕜 hconv
  rw [hY.closure_eq] at hclo
  rw [hclo]
  exact isClosed_closure

private theorem exists_countable_separating_dual_of_countable
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {D : Set E} (hD : D.Countable) :
    ∃ F : Set (StrongDual 𝕜 E), F.Countable ∧
      ∀ z ∈ closure (Submodule.span 𝕜 D : Set E), (∀ g ∈ F, g z = 0) → z = 0 := by
  have hsep1 : TopologicalSpace.IsSeparable D := hD.isSeparable
  have hsep2 : TopologicalSpace.IsSeparable (Submodule.span 𝕜 D : Set E) := hsep1.span
  have hsep3 : TopologicalSpace.IsSeparable (closure (Submodule.span 𝕜 D : Set E)) :=
    hsep2.closure
  obtain ⟨c, hc_count, hsub⟩ := hsep3
  choose g hg using fun (y : E) => exists_dual_vector'' 𝕜 y
  refine ⟨(fun y => g y) '' c, hc_count.image _, fun z hz hvan => ?_⟩
  have hz' : z ∈ closure c := hsub hz
  have h2 : ∀ ε > 0, ‖z‖ < 2 * ε := by
    intro ε hε
    obtain ⟨y, hyc, hdist⟩ := (Metric.mem_closure_iff.mp hz') ε hε
    have hdist' : ‖z - y‖ < ε := by
      rw [← dist_eq_norm]
      exact hdist
    have hgy : g y y = ((‖y‖ : ℝ) : 𝕜) := (hg y).2
    have hgz : g y z = 0 := hvan _ (mem_image_of_mem _ hyc)
    have hdiff : g y (y - z) = ((‖y‖ : ℝ) : 𝕜) := by
      rw [map_sub, hgy, hgz, sub_zero]
    have hle : ‖g y (y - z)‖ ≤ ‖y - z‖ := by
      calc ‖g y (y - z)‖ ≤ ‖g y‖ * ‖y - z‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖y - z‖ := by gcongr; exact (hg y).1
        _ = ‖y - z‖ := one_mul _
    have hnormy : ‖y‖ ≤ ‖y - z‖ := by
      have h1 : ‖(((‖y‖ : ℝ)) : 𝕜)‖ = ‖y‖ := RCLike.norm_coe_norm
      rw [← hdiff] at h1
      rw [← h1]
      exact hle
    have htri : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      have h := norm_add_le (z - y) y
      rwa [sub_add_cancel] at h
    have e1 : ‖z - y‖ < ε := hdist'
    have e2 : ‖y - z‖ < ε := by rw [norm_sub_rev]; exact hdist'
    linarith [htri, hnormy, e1, e2]
  have hzero : ‖z‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hgt
    have hpos : 0 < ‖z‖ := lt_of_not_ge hgt
    have hlt := h2 (‖z‖ / 4) (by linarith)
    linarith
  exact norm_eq_zero.mp hzero

private theorem WeakSpace_exists_norm_le_of_isSeqCompact
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set (WeakSpace 𝕜 E)} (hs : IsSeqCompact s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ s, ‖(toWeakSpace 𝕜 E).symm w‖ ≤ M := by
  have hbound : ∀ g : StrongDual 𝕜 E, ∃ C, ∀ w ∈ s, ‖g ((toWeakSpace 𝕜 E).symm w)‖ ≤ C := by
    intro g
    have hcont : Continuous (fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) :=
      WeakBilin.eval_continuous ((topDualPairing 𝕜 E).flip) g
    have hseq : SeqContinuous (fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) :=
      hcont.seqContinuous
    have himg : IsSeqCompact ((fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) '' s) :=
      hs.image hseq
    have hcomp : IsCompact ((fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) '' s) :=
      himg.isCompact
    obtain ⟨C, hC⟩ := hcomp.isBounded.subset_ball 0
    refine ⟨C, fun w hw => ?_⟩
    have hmem : (fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) w ∈
        (fun w : WeakSpace 𝕜 E => g ((toWeakSpace 𝕜 E).symm w)) '' s := mem_image_of_mem _ hw
    have hmem2 := hC hmem
    simp only [mem_ball, dist_zero_right] at hmem2
    exact le_of_lt hmem2
  have hfam : ∀ g : StrongDual 𝕜 E, ∃ C, ∀ i : ↥s,
      ‖((NormedSpace.inclusionInDoubleDual 𝕜 E) ((toWeakSpace 𝕜 E).symm (i : WeakSpace 𝕜 E))) g‖ ≤
          C := by
    intro g
    obtain ⟨C, hC⟩ := hbound g
    refine ⟨C, fun i => ?_⟩
    rw [NormedSpace.dual_def]
    exact hC _ i.property
  obtain ⟨C', hC'⟩ := banach_steinhaus hfam
  refine ⟨max C' 0, le_max_right _ _, fun w hw => ?_⟩
  refine NormedSpace.norm_le_dual_bound 𝕜 _ (le_max_right _ _) fun f => ?_
  have h1 : ‖(NormedSpace.inclusionInDoubleDual 𝕜 E) ((toWeakSpace 𝕜 E).symm w)‖ ≤ C' :=
    hC' ⟨w, hw⟩
  calc ‖f ((toWeakSpace 𝕜 E).symm w)‖
      = ‖(NormedSpace.inclusionInDoubleDual 𝕜 E) ((toWeakSpace 𝕜 E).symm w) f‖ := by
        rw [NormedSpace.dual_def]
    _ ≤ ‖(NormedSpace.inclusionInDoubleDual 𝕜 E) ((toWeakSpace 𝕜 E).symm w)‖ * ‖f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C' * ‖f‖ := by gcongr
    _ ≤ max C' 0 * ‖f‖ := by gcongr; exact le_max_left _ _

private theorem WeakSpace_exists_bidual_limit_of_ultrafilter
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set (WeakSpace 𝕜 E)} {M : ℝ} (hM : ∀ w ∈ s, ‖(toWeakSpace 𝕜 E).symm w‖ ≤ M)
    (U : Ultrafilter (WeakSpace 𝕜 E)) (hU : (U : Filter (WeakSpace 𝕜 E)) ≤ 𝓟 s) :
    ∃ Φ : StrongDual 𝕜 (StrongDual 𝕜 E),
      (∀ g : StrongDual 𝕜 E,
        Tendsto (fun w => g ((toWeakSpace 𝕜 E).symm w)) (↑U) (𝓝 (Φ g))) ∧
      (∀ S : Finset (StrongDual 𝕜 E), ∀ ε > 0, ∃ w ∈ s,
        ∀ g ∈ S, ‖Φ g - g ((toWeakSpace 𝕜 E).symm w)‖ < ε) := by
  let Jw := NormedSpace.inclusionInDoubleDualWeak 𝕜 E
  -- the compact target
  have hmem : ∀ w ∈ s, Jw w ∈ WeakDual.toStrongDual ⁻¹'
      (Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) M) := by
    intro w hw
    have hnorm : ‖WeakDual.toStrongDual (Jw w)‖ ≤ M := by
      have hJ : WeakDual.toStrongDual (Jw w)
          = (NormedSpace.inclusionInDoubleDual 𝕜 E) ((toWeakSpace 𝕜 E).symm w) := rfl
      rw [hJ]
      exact le_trans (NormedSpace.double_dual_bound 𝕜 E _) (hM w hw)
    rw [mem_preimage]
    set y := WeakDual.toStrongDual (Jw w) with hy
    have hnorm' : ‖y‖ ≤ M := hnorm
    rw [Metric.mem_closedBall]
    have e : dist y 0 = ‖y - 0‖ := dist_eq_norm y 0
    have e2 : y - (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) = y := sub_zero y
    rw [e, e2]
    exact hnorm'
  have hK : IsCompact (WeakDual.toStrongDual ⁻¹'
      (Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) M)) :=
    WeakDual.isCompact_closedBall _ _
  -- the ultrafilter maps into the compact set
  have hle : (↑(Ultrafilter.map (⇑Jw) U) : Filter _) ≤
      𝓟 (WeakDual.toStrongDual ⁻¹' (Metric.closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) M)) := by
    rw [le_principal_iff, Ultrafilter.coe_map]
    have hsU : s ∈ (↑U : Filter (WeakSpace 𝕜 E)) := le_principal_iff.mp hU
    apply mem_of_superset hsU
    intro w hw
    exact hmem w hw
  obtain ⟨Φ', hΦ'mem, hlim⟩ := hK.ultrafilter_le_nhds _ hle
  refine ⟨WeakDual.toStrongDual Φ', ?_, ?_⟩
  · -- part (a): coordinate convergence
    intro g
    have hlim' : Tendsto (⇑Jw) (↑U : Filter (WeakSpace 𝕜 E)) (𝓝 Φ') := by
      have h := hlim
      rwa [Ultrafilter.coe_map] at h
    have h1 : Tendsto (fun w : WeakSpace 𝕜 E => (Jw w) g) (↑U : Filter (WeakSpace 𝕜 E))
        (𝓝 (Φ' g)) :=
      ((WeakDual.eval_continuous g).tendsto Φ').comp hlim'
    have e1 : (fun w : WeakSpace 𝕜 E => (Jw w) g)
        = (fun w => g ((toWeakSpace 𝕜 E).symm w)) := by
      funext w
      exact NormedSpace.inclusionInDoubleDualWeak_apply_apply 𝕜 E w g
    have e2 : Φ' g = (WeakDual.toStrongDual Φ') g := rfl
    rwa [e1, e2] at h1
  · -- part (b): finite approximation
    intro S ε hε
    have hev : ∀ g ∈ S, ∀ᶠ w in (↑U : Filter (WeakSpace 𝕜 E)),
        ‖(WeakDual.toStrongDual Φ') g - g ((toWeakSpace 𝕜 E).symm w)‖ < ε := by
      intro g hg
      have h := (fun g => Tendsto (fun w => g ((toWeakSpace 𝕜 E).symm w))
          (↑U : Filter (WeakSpace 𝕜 E))
        (𝓝 ((WeakDual.toStrongDual Φ') g))) g
      -- prove via part (a) again to avoid forward reference: use same argument
      have hlim' : Tendsto (⇑Jw) (↑U : Filter (WeakSpace 𝕜 E)) (𝓝 Φ') := by
        have h' := hlim
        rwa [Ultrafilter.coe_map] at h'
      have h1 : Tendsto (fun w : WeakSpace 𝕜 E => (Jw w) g) (↑U : Filter (WeakSpace 𝕜 E))
          (𝓝 (Φ' g)) :=
        ((WeakDual.eval_continuous g).tendsto Φ').comp hlim'
      have e1 : (fun w : WeakSpace 𝕜 E => (Jw w) g)
          = (fun w => g ((toWeakSpace 𝕜 E).symm w)) := by
        funext w
        exact NormedSpace.inclusionInDoubleDualWeak_apply_apply 𝕜 E w g
      have e2 : Φ' g = (WeakDual.toStrongDual Φ') g := rfl
      rw [e1, e2] at h1
      rw [Metric.tendsto_nhds] at h1
      have h2 := h1 ε hε
      apply h2.mono
      intro w hw
      rw [dist_eq_norm] at hw
      rwa [norm_sub_rev]
    have hall : ∀ᶠ w in (↑U : Filter (WeakSpace 𝕜 E)), ∀ i : ↥S,
        ‖(WeakDual.toStrongDual Φ') (i : StrongDual 𝕜 E)
          - (i : StrongDual 𝕜 E) ((toWeakSpace 𝕜 E).symm w)‖ < ε := by
      rw [Filter.eventually_all]
      intro ⟨g, hg⟩
      exact hev g hg
    have hsU : s ∈ (↑U : Filter (WeakSpace 𝕜 E)) := le_principal_iff.mp hU
    obtain ⟨w, hwP, hws⟩ := (hall.and hsU).exists
    exact ⟨w, hws, fun g hg => hwP ⟨g, hg⟩⟩

private theorem eq_zero_of_approx_of_norming
    {𝕜 : Type*} [RCLike 𝕜]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {S : Set (StrongDual 𝕜 W)} {F : Set W}
    (hF : ∀ g ∈ F, ‖g‖ ≤ 1)
    (hnorm : ∀ ψ' ∈ S, ∃ g ∈ F, ‖ψ'‖ ≤ 2 * ‖ψ' g‖)
    {ψ : StrongDual 𝕜 W}
    (happrox : ∀ ε > 0, ∃ ψ' ∈ S, ‖ψ - ψ'‖ < ε)
    (hvan : ∀ g ∈ F, ψ g = 0) :
    ψ = 0 := by
  suffices h : ‖ψ‖ = 0 by exact norm_eq_zero.mp h
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨ψ', hψ'S, hclose⟩ := happrox (ε / 3) (by linarith)
  obtain ⟨g, hgF, hnormg⟩ := hnorm ψ' hψ'S
  have hg1 : ‖g‖ ≤ 1 := hF g hgF
  have hclose' : ‖ψ' - ψ‖ < ε / 3 := by rwa [norm_sub_rev]
  have hclose2 : ‖ψ - ψ'‖ < ε / 3 := hclose
  have hdiff : ψ' g = (ψ' - ψ) g := by
    rw [sub_apply, hvan g hgF, sub_zero]
  have hop : ‖ψ' - ψ‖ * ‖g‖ ≤ ε / 3 := by
    calc ‖ψ' - ψ‖ * ‖g‖ ≤ (ε / 3) * 1 :=
          mul_le_mul (le_of_lt hclose') hg1 (norm_nonneg _) (by linarith)
      _ = ε / 3 := mul_one _
  have hest : ‖ψ'‖ ≤ 2 * (ε / 3) := by
    have h1 : ‖ψ' g‖ ≤ ε / 3 := by
      rw [hdiff]
      exact le_trans (ContinuousLinearMap.le_opNorm _ _) hop
    linarith [hnormg]
  have htri : ‖ψ‖ ≤ ‖ψ'‖ + ‖ψ - ψ'‖ := by
    have h := norm_add_le ψ' (ψ - ψ')
    simpa using h
  calc ‖ψ‖ ≤ ‖ψ'‖ + ‖ψ - ψ'‖ := htri
    _ < 2 * (ε / 3) + ε / 3 := by linarith [hest, hclose2]
    _ = 0 + ε := by ring

private theorem mem_span_insert_image_Iio_of_mem_span_insert_range
    {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {Φ : M} {v : ℕ → M} {ψ : M}
    (hψ : ψ ∈ Submodule.span R (insert Φ (range v))) :
    ∃ n, ψ ∈ Submodule.span R (insert Φ (v '' Set.Iio n)) := by
  classical
  obtain ⟨T, hTsub, hTmem⟩ := Submodule.mem_span_finite_of_mem_span hψ
  have hchoice : ∀ (t : M), t ∈ T → ∃ m, t = Φ ∨ v m = t := by
    intro t ht
    have hmem : t ∈ insert Φ (range v) := hTsub ht
    simp only [mem_insert_iff, mem_range] at hmem
    rcases hmem with rfl | ⟨m, hm⟩
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨m, Or.inr hm⟩
  choose m hm using hchoice
  let g : M → ℕ := fun t => if h : t ∈ T then m t h else 0
  let N := (T.image g).sup id
  refine ⟨N + 1, Submodule.span_mono ?_ hTmem⟩
  intro t ht
  simp only [mem_insert_iff, mem_image, mem_Iio] at *
  by_cases hΦ : t = Φ
  · exact Or.inl hΦ
  · right
    have hdisj := (hm t ht).resolve_left hΦ
    refine ⟨m t ht, ?_, hdisj⟩
    have hmem : g t ∈ T.image g := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have hle : id (g t) ≤ N := Finset.le_sup hmem
    have hg : g t = m t ht := dite_eq_left ht
    simp only [id] at hle
    rw [hg] at hle
    omega

private theorem eq_of_tendsto_subseq_of_tolerance
    {𝕜 : Type*} [RCLike 𝕜]
    {c L : 𝕜} {a : ℕ → 𝕜} {k : ℕ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hbound : ∀ n ≥ k, ‖c - a n‖ < 1 / ((n : ℝ) + 1))
    (hlim : Tendsto (fun j => a (φ j)) atTop (𝓝 L)) :
    c = L := by
  have h1 : Tendsto (fun j => ‖c - a (φ j)‖) atTop (𝓝 ‖c - L‖) :=
    (hlim.const_sub c).norm
  have hev : ∀ᶠ j in atTop, ‖c - a (φ j)‖ ≤ 1 / ((j : ℝ) + 1) := by
    apply eventually_atTop.mpr
    refine ⟨k, fun j hj => ?_⟩
    have hkj : φ j ≥ k := le_trans hj (hφ.id_le j)
    have hle : (j : ℝ) ≤ (φ j : ℝ) := by exact_mod_cast hφ.id_le j
    calc ‖c - a (φ j)‖ ≤ 1 / (((φ j : ℕ) : ℝ) + 1) := le_of_lt (hbound _ hkj)
      _ ≤ 1 / ((j : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ‖c - L‖ ≤ 0 := le_of_tendsto_of_tendsto h1 h2 hev
  have hzero : ‖c - L‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

private theorem whitley_limit_eq
    {𝕜 : Type*} [RCLike 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (j : X →L[𝕜] StrongDual 𝕜 W) (hj : ∀ v, ‖j v‖ ≤ ‖v‖)
    (Φ : StrongDual 𝕜 W) (x : ℕ → X) (G : ℕ → Finset W) (xbar : X)
    (hR2 : ∀ n, ∀ g ∈ G n, ‖g‖ ≤ 1)
    (hR3 : ∀ n, ∀ ψ ∈ Submodule.span 𝕜
      (↑(insert Φ ((fun i => j (x i)) '' Set.Iio n)) : Set (StrongDual 𝕜 W)),
      ∃ g ∈ G n, ‖ψ‖ ≤ 2 * ‖ψ g‖)
    (hagree : ∀ n, ∀ g ∈ G n, Φ g = j xbar g)
    (hmem : xbar ∈ closure (Submodule.span 𝕜 (Set.range x) : Set X)) :
    Φ = j xbar := by
  classical
  set ψ := Φ - j xbar with hψ
  set S : Set (StrongDual 𝕜 W) :=
    (Submodule.span 𝕜 (insert Φ (Set.range (fun i => j (x i)))) : Set (StrongDual 𝕜 W)) with hS
  set F : Set W := ⋃ n, ↑(G n) with hF
  have hnorm : ∀ ψ' ∈ S, ∃ g ∈ F, ‖ψ'‖ ≤ 2 * ‖ψ' g‖ := by
    intro ψ' hψ'
    obtain ⟨n, hn⟩ :=
      mem_span_insert_image_Iio_of_mem_span_insert_range (R := 𝕜) (v := fun i => j (x i)) hψ'
    obtain ⟨g, hgG, hgbound⟩ := hR3 n ψ' hn
    exact ⟨g, Set.mem_iUnion.mpr ⟨n, hgG⟩, hgbound⟩
  have happrox : ∀ ε > 0, ∃ ψ' ∈ S, ‖ψ - ψ'‖ < ε := by
    intro ε hε
    obtain ⟨z, hzspan, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
    have hnorm1 : ‖xbar - z‖ < ε := by
      have e : dist xbar z = ‖xbar - z‖ := dist_eq_norm _ _
      rwa [e] at hdist
    have hjz : j z ∈ Submodule.span 𝕜 (Set.range (fun i => j (x i))) := by
      have himg := Submodule.apply_mem_span_image_of_mem_span j.toLinearMap hzspan
      have eimg : (⇑j.toLinearMap '' Set.range x) = Set.range (fun i => j (x i)) := by
        rw [← Set.range_comp]
        congr 1
      have eelt : (⇑j.toLinearMap) z = j z := rfl
      rw [eimg] at himg
      rwa [eelt] at himg
    have hΦS : Φ ∈ S := Submodule.subset_span (Set.mem_insert _ _)
    have hjzS : j z ∈ S := by
      apply Submodule.span_mono _ hjz
      intro t ht
      exact Set.mem_insert_of_mem _ ht
    have hψ'S : Φ - j z ∈ S := sub_mem hΦS hjzS
    refine ⟨Φ - j z, hψ'S, ?_⟩
    have ediff : ψ - (Φ - j z) = j z - j xbar := by rw [hψ]; abel
    have emap : j z - j xbar = j (z - xbar) := (map_sub j z xbar).symm
    rw [ediff, emap]
    calc ‖j (z - xbar)‖ ≤ ‖z - xbar‖ := hj _
      _ = ‖xbar - z‖ := norm_sub_rev _ _
      _ < ε := hnorm1
  have hvan : ∀ g ∈ F, ψ g = 0 := by
    intro g hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    have e : ψ g = Φ g - j xbar g := sub_apply _ _ _
    rw [e, hagree n g hn]
    simp
  have hFbound : ∀ g ∈ F, ‖g‖ ≤ 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    exact hR2 n g hn
  have hzero : ψ = 0 :=
    eq_zero_of_approx_of_norming (S := S) (F := F) hFbound hnorm happrox hvan
  rw [hψ] at hzero
  exact sub_eq_zero.mp hzero

private theorem WeakSpace_isSeqCompact_of_isCompact
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set (WeakSpace 𝕜 E)} (hs : IsCompact s) :
    IsSeqCompact s := by
  classical
  intro u hu
  set ι := toWeakSpace 𝕜 E with hι
  set D : Set E := Set.range (fun n => ι.symm (u n)) with hD
  set Y : Submodule 𝕜 E := (Submodule.span 𝕜 D).topologicalClosure with hY
  have hYclosed : IsClosed (Y : Set E) := Submodule.isClosed_topologicalClosure _
  have hιY : IsClosed (⇑ι '' (Y : Set E)) :=
    WeakSpace_isClosed_image_toWeakSpace_of_isClosed_submodule (𝕜 := 𝕜) (E := E) Y hYclosed
  set Kset : Set (WeakSpace 𝕜 E) := s ∩ ⇑ι '' (Y : Set E) with hKset
  have hKcomp : IsCompact Kset := hs.inter_right hιY
  have hKspace : CompactSpace Kset := isCompact_iff_compactSpace.mp hKcomp
  have hDcount : D.Countable := Set.countable_range _
  obtain ⟨F, hFcount, hFsep⟩ :=
    exists_countable_separating_dual_of_countable (𝕜 := 𝕜) (E := E) (D := D) hDcount
  have hFenc : Encodable ↥F := hFcount.toEncodable
  have hYcoe : (Y : Set E) = closure (Submodule.span 𝕜 D : Set E) :=
    Submodule.topologicalClosure_coe _
  -- the separating family of maps
  set f : ↥F → Kset → 𝕜 :=
    fun i p => (i : StrongDual 𝕜 E) (ι.symm (p : WeakSpace 𝕜 E)) with hf
  have hcont : ∀ i, Continuous (f i) := by
    intro i
    have hc : Continuous (fun w : WeakSpace 𝕜 E => (i : StrongDual 𝕜 E) (ι.symm w)) :=
      WeakBilin.eval_continuous _ _
    exact hc.comp continuous_subtype_val
  have hsep : Pairwise (fun (p q : Kset) => ∃ i, f i p ≠ f i q) := by
    intro p q hpq
    have hne : ι.symm (p : WeakSpace 𝕜 E) - ι.symm (q : WeakSpace 𝕜 E) ≠ 0 := by
      intro h0
      apply hpq
      apply Subtype.ext
      have h1 : ι.symm (p : WeakSpace 𝕜 E) = ι.symm (q : WeakSpace 𝕜 E) :=
        sub_eq_zero.mp h0
      have h2 := congrArg (⇑ι) h1
      rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
    have hmemY : ι.symm (p : WeakSpace 𝕜 E) - ι.symm (q : WeakSpace 𝕜 E) ∈ (Y : Set E) := by
      have hpY : ι.symm (p : WeakSpace 𝕜 E) ∈ (Y : Set E) := by
        obtain ⟨y, hyY, hy⟩ := (p.property.2)
        have e : ι.symm (p : WeakSpace 𝕜 E) = y := by
          rw [← hy]
          exact LinearEquiv.symm_apply_apply _ _
        rwa [e]
      have hqY : ι.symm (q : WeakSpace 𝕜 E) ∈ (Y : Set E) := by
        obtain ⟨y, hyY, hy⟩ := (q.property.2)
        have e : ι.symm (q : WeakSpace 𝕜 E) = y := by
          rw [← hy]
          exact LinearEquiv.symm_apply_apply _ _
        rwa [e]
      exact Y.sub_mem hpY hqY
    have hmemCl : ι.symm (p : WeakSpace 𝕜 E) - ι.symm (q : WeakSpace 𝕜 E)
        ∈ closure (Submodule.span 𝕜 D : Set E) := by
      rwa [← hYcoe]
    set z : E := ι.symm (p : WeakSpace 𝕜 E) - ι.symm (q : WeakSpace 𝕜 E) with hz
    have hnez : z ≠ 0 := hne
    have hmemClz : z ∈ closure (Submodule.span 𝕜 D : Set E) := hmemCl
    by_contra hcon
    have hcon' : ∀ i, f i p = f i q := by
      intro i
      by_contra h
      exact hcon ⟨i, h⟩
    have hvan : ∀ g ∈ F, (g : StrongDual 𝕜 E) z = 0 := by
      intro g hg
      have hfg := hcon' ⟨g, hg⟩
      have e : (g : StrongDual 𝕜 E) (ι.symm (p : WeakSpace 𝕜 E)) =
          (g : StrongDual 𝕜 E) (ι.symm (q : WeakSpace 𝕜 E)) := hfg
      have emap : (g : StrongDual 𝕜 E) z =
          (g : StrongDual 𝕜 E) (ι.symm (p : WeakSpace 𝕜 E)) -
          (g : StrongDual 𝕜 E) (ι.symm (q : WeakSpace 𝕜 E)) := by
        rw [hz]
        exact map_sub _ _ _
      rw [emap, e, sub_self]
    have hzero := hFsep z hmemClz hvan
    exact hnez hzero
  -- metrizability + sequential compactness of K
  have hmet : TopologicalSpace.MetrizableSpace Kset :=
    Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating f hcont hsep
  -- every u n lies in K
  have huK : ∀ n, u n ∈ Kset := by
    intro n
    constructor
    · exact hu n
    · -- u n = ι (ι⁻¹ (u n)), with ι⁻¹ (u n) ∈ Y
      have hmem : ι.symm (u n) ∈ (Y : Set E) := by
        have hDmem : ι.symm (u n) ∈ D := Set.mem_range_self n
        have hspan : ι.symm (u n) ∈ (Submodule.span 𝕜 D : Set E) :=
          Submodule.subset_span hDmem
        have hle : (Submodule.span 𝕜 D : Set E) ⊆ (Y : Set E) :=
          Submodule.le_topologicalClosure _
        exact hle hspan
      exact ⟨ι.symm (u n), hmem, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨a, φ, hφmono, hφlim⟩ :=
    SeqCompactSpace.tendsto_subseq (fun n => (⟨u n, huK n⟩ : Kset))
  refine ⟨(a : WeakSpace 𝕜 E), a.property.1, φ, hφmono, ?_⟩
  have hlim : Tendsto ((fun n => (⟨u n, huK n⟩ : Kset)) ∘ φ) atTop (𝓝 a) := hφlim
  have hcont2 : Continuous (Subtype.val : Kset → WeakSpace 𝕜 E) := continuous_subtype_val
  have hlim2 := (hcont2.tendsto a).comp hlim
  have efun : (Subtype.val ∘ (fun n => (⟨u n, huK n⟩ : Kset)) ∘ φ) = u ∘ φ := rfl
  rwa [efun] at hlim2

private theorem WeakSpace_exists_mem_eval_eq_of_isSeqCompact
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set (WeakSpace 𝕜 E)} (hs : IsSeqCompact s)
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E))
    (happrox : ∀ S : Finset (StrongDual 𝕜 E), ∀ ε > 0, ∃ w ∈ s,
      ∀ g ∈ S, ‖Φ g - g ((toWeakSpace 𝕜 E).symm w)‖ < ε) :
    ∃ a ∈ s, ∀ g : StrongDual 𝕜 E, Φ g = g ((toWeakSpace 𝕜 E).symm a) := by
  classical
  set ι := toWeakSpace 𝕜 E with hι
  set J := NormedSpace.inclusionInDoubleDual 𝕜 E with hJ
  set A : Set E := ι ⁻¹' s with hA
  -- rewrite approximation into N7 form
  have happrox' : ∀ S : Finset (StrongDual 𝕜 E), ∀ ε > 0, ∃ a ∈ A,
      ∀ g ∈ S, ‖Φ g - J a g‖ < ε := by
    intro S ε hε
    obtain ⟨w, hws, hw⟩ := happrox S ε hε
    refine ⟨ι.symm w, ?_, ?_⟩
    · change ι.symm w ∈ ι ⁻¹' s
      rw [Set.mem_preimage, LinearEquiv.apply_symm_apply]
      exact hws
    · intro g hg
      have e : J (ι.symm w) g = g (ι.symm w) := NormedSpace.dual_def 𝕜 E _ _
      rw [e]
      exact hw g hg
  obtain ⟨x, G, hR1, hR2, hR3, hR4⟩ := whitley_sequence J Φ A happrox'
  -- the sequence in s
  have hxs : ∀ n, ι (x n) ∈ s := fun n => hR1 n
  obtain ⟨a, haS, φ, hφmono, hφlim⟩ := hs hxs
  set xbar : E := ι.symm a with hxbar
  -- xbar in closed span
  have hmemCl : xbar ∈ closure (Submodule.span 𝕜 (Set.range x) : Set E) := by
    set Y : Submodule 𝕜 E := (Submodule.span 𝕜 (Set.range x)).topologicalClosure with hY
    have hYclosed : IsClosed (Y : Set E) := Submodule.isClosed_topologicalClosure _
    have hιY : IsClosed (⇑ι '' (Y : Set E)) :=
      WeakSpace_isClosed_image_toWeakSpace_of_isClosed_submodule
        (𝕜 := 𝕜) (E := E) Y hYclosed
    have hmem : ∀ n, ι (x (φ n)) ∈ ⇑ι '' (Y : Set E) := by
      intro n
      refine ⟨x (φ n), ?_, rfl⟩
      apply Submodule.le_topologicalClosure
      exact Submodule.subset_span (Set.mem_range_self _)
    have hev : ∀ᶠ n in Filter.atTop, ι (x (φ n)) ∈ ⇑ι '' (Y : Set E) :=
      Filter.Eventually.of_forall hmem
    have haY : a ∈ ⇑ι '' (Y : Set E) := hιY.mem_of_tendsto hφlim hev
    obtain ⟨y, hyY, hya⟩ := haY
    have exbar : xbar = y := by
      rw [hxbar, ← hya]
      exact LinearEquiv.symm_apply_apply _ _
    rw [exbar]
    have hYcoe : (Y : Set E) = closure (Submodule.span 𝕜 (Set.range x) : Set E) :=
      Submodule.topologicalClosure_coe _
    rw [← hYcoe]
    exact hyY
  -- agreement on norming sets via N10
  have hagree : ∀ k, ∀ g ∈ G k, Φ g = J xbar g := by
    intro k g hg
    -- limit of evals
    have hcon : Continuous (fun w : WeakSpace 𝕜 E => g (ι.symm w)) :=
      WeakBilin.eval_continuous _ _
    have hlim0 : Filter.Tendsto (fun j => g (ι.symm (ι (x (φ j))))) Filter.atTop
        (nhds (g (ι.symm a))) := (hcon.tendsto a).comp hφlim
    have hlim : Filter.Tendsto (fun j => J (x (φ j)) g) Filter.atTop (nhds (J xbar g)) := by
      have e1 : (fun j => J (x (φ j)) g) = (fun j => g (x (φ j))) := by
        funext j
        exact (NormedSpace.dual_def 𝕜 E _ _).symm
      have e2 : J xbar g = g (ι.symm a) := NormedSpace.dual_def 𝕜 E _ _
      rw [e1, e2]
      simpa using hlim0
    have hbound : ∀ n ≥ k, ‖Φ g - J (x n) g‖ < 1 / ((n : ℝ) + 1) :=
      fun n hn => hR4 k n hn g hg
    exact eq_of_tendsto_subseq_of_tolerance hφmono hbound hlim
  have hj : ∀ v, ‖J v‖ ≤ ‖v‖ := fun v => NormedSpace.double_dual_bound 𝕜 E v
  have hΦeq : Φ = J xbar := whitley_limit_eq J hj Φ x G xbar hR2 hR3 hagree hmemCl
  refine ⟨a, haS, fun g => ?_⟩
  have e : Φ g = J xbar g := congrFun (congrArg DFunLike.coe hΦeq) g
  rw [e, NormedSpace.dual_def]

private theorem WeakSpace_isCompact_of_isSeqCompact
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set (WeakSpace 𝕜 E)} (hs : IsSeqCompact s) :
    IsCompact s := by
  classical
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro U hU
  set ι := toWeakSpace 𝕜 E with hι
  obtain ⟨M, hMpos, hM⟩ := WeakSpace_exists_norm_le_of_isSeqCompact (𝕜 := 𝕜) (E := E) hs
  obtain ⟨Φ, hΦlim, hΦapprox⟩ :=
    WeakSpace_exists_bidual_limit_of_ultrafilter (s := s) (fun w hw => hM w hw) U hU
  obtain ⟨a, haS, haΦ⟩ :=
    WeakSpace_exists_mem_eval_eq_of_isSeqCompact hs Φ (fun S ε hε => hΦapprox S ε hε)
  refine ⟨a, haS, ?_⟩
  -- show U → a weakly via coordinate-wise convergence
  set B : E →ₗ[𝕜] StrongDual 𝕜 E →ₗ[𝕜] 𝕜 := (topDualPairing 𝕜 E).flip with hB
  have hBinj : Function.Injective ⇑B := by
    intro v w hvw
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := 𝕜) (V := E) hne
    have e1 : B v f = f v := by rw [hB, LinearMap.flip_apply, topDualPairing_apply]
    have e2 : B w f = f w := by rw [hB, LinearMap.flip_apply, topDualPairing_apply]
    have e3 : B v f = B w f := congrFun (congrArg DFunLike.coe hvw) f
    rw [e1, e2] at e3
    exact hf e3
  have hiff : Filter.Tendsto (id : WeakSpace 𝕜 E → WeakSpace 𝕜 E) (↑U : Filter _) (𝓝 a) ↔
      ∀ g, Filter.Tendsto (fun i : WeakSpace 𝕜 E => B (id i) g) (↑U : Filter _) (𝓝 (B a g)) :=
    WeakBilin.tendsto_iff_forall_eval_tendsto B hBinj
  -- apply with f := id, x := a
  have hgoal : Filter.Tendsto (id : WeakSpace 𝕜 E → WeakSpace 𝕜 E) (↑U : Filter _) (𝓝 a) := by
    rw [hiff]
    intro g
    have hlim := hΦlim g
    -- hlim : Tendsto (fun w => g (ι⁻¹ w)) ↑U (𝓝 (Φ g))
    have e1 : (fun i : WeakSpace 𝕜 E => B (id i) g) = (fun w => g (ι.symm w)) := by
      funext i
      show B (id i) g = g (ι.symm i)
      rw [hB, LinearMap.flip_apply, topDualPairing_apply]
      congr 1
    have e2 : B a g = Φ g := by
      have h1 : B (id a) g = g (ι.symm a) := congrFun e1 a
      have h2 : B a g = B (id a) g := rfl
      rw [h2, h1, ← haΦ g]
    rw [e1, e2]
    exact hlim
  have hgoal' : Filter.map (id : WeakSpace 𝕜 E → WeakSpace 𝕜 E) (↑U : Filter _) ≤ 𝓝 a :=
    hgoal
  rw [Filter.map_id] at hgoal'
  exact hgoal'

section
namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

open Set Metric

/--
For a Banach space over `ℝ` or `ℂ`, a set in the weak topology `WeakSpace 𝕜 E` is compact iff it
is sequentially compact. Source: W. F. Eberlein, Weak Compactness in Banach Spaces,
PNAS 33 (1947), 51–53, DOI 10.1073/pnas.33.3.51, and V. Smulian (1947); Dunford-Schwartz,
Linear Operators I, 1958, V.5-6; Lean states `RCLike` Banach case with
`IsCompact ↔ IsSeqCompact` in `WeakSpace`.

Proves `Wanted` entry `eberlein_smulian`.
-/
theorem eberlein_smulian
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {s : Set (WeakSpace 𝕜 E)} :
    IsCompact s ↔ IsSeqCompact s := by
  constructor
  · exact WeakSpace_isSeqCompact_of_isCompact
  · exact WeakSpace_isCompact_of_isSeqCompact

end MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted
end
