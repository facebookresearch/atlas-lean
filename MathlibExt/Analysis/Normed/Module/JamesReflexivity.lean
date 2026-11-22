/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import MathlibExt.Analysis.FunctionalAnalysis.BanachSpace
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Tactic.Linarith

/-!
# James' reflexivity theorem

This file characterizes reflexive Banach spaces over `ℝ` or `ℂ` by norm attainment of every
continuous linear functional on the closed unit ball.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

open Set Metric
open Filter

private def jamesClusterSet {X : Type*} [TopologicalSpace X] (u : ℕ → X) : Set X :=
  {x | MapClusterPt x atTop u}

private def jamesClusterHull {X : Type*} [TopologicalSpace X]
    [AddCommGroup X] [Module ℝ X] (u : ℕ → X) : Set X :=
  closedConvexHull ℝ (jamesClusterSet u)

private def jamesDualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (WeakDual ℝ E) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1

private theorem james_dualBall_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Convex ℝ (jamesDualBall E) := by
  exact (convex_closedBall (0 : StrongDual ℝ E) 1).linear_preimage
    WeakDual.toStrongDual.toLinearMap

private theorem james_clusterHull_nonempty_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E) :
    (jamesClusterHull u).Nonempty ∧ IsCompact (jamesClusterHull u) := by
  have hball : IsCompact (jamesDualBall E) :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1
  have humap : Filter.map u atTop ≤ Filter.principal (jamesDualBall E) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Filter.Eventually.of_forall hu
  obtain ⟨x, _, hx⟩ := hball.exists_mapClusterPt humap
  have hxcluster : x ∈ jamesClusterSet u := hx
  have hclustersub : jamesClusterSet u ⊆ jamesDualBall E := by
    intro y hy
    exact (WeakDual.isClosed_closedBall 0 1).mem_of_mapClusterPt hy
      (Filter.Eventually.of_forall hu)
  have hsub : jamesClusterHull u ⊆ jamesDualBall E :=
    closedConvexHull_min hclustersub james_dualBall_convex
      (WeakDual.isClosed_closedBall 0 1)
  refine ⟨⟨x, subset_closedConvexHull hxcluster⟩, ?_⟩
  exact hball.of_isClosed_subset isClosed_closedConvexHull hsub

private theorem james_clusterHull_subset_dualBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E) :
    jamesClusterHull u ⊆ jamesDualBall E := by
  have hclustersub : jamesClusterSet u ⊆ jamesDualBall E := by
    intro y hy
    exact (WeakDual.isClosed_closedBall 0 1).mem_of_mapClusterPt hy
      (Filter.Eventually.of_forall hu)
  exact closedConvexHull_min hclustersub james_dualBall_convex
    (WeakDual.isClosed_closedBall 0 1)

private theorem james_clusterHull_comp_subset
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (u : ℕ → X) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    jamesClusterHull (u ∘ σ) ⊆ jamesClusterHull u := by
  apply (closedConvexHull ℝ).monotone
  intro x hx
  exact hx.of_comp hσ.tendsto_atTop

private theorem james_clusterHull_add_eq
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    (u : ℕ → X) (k : ℕ) :
    jamesClusterHull (u ∘ fun n ↦ n + k) = jamesClusterHull u := by
  apply congrArg (closedConvexHull ℝ)
  ext x
  change ClusterPt x (map (u ∘ fun n ↦ n + k) atTop) ↔
    ClusterPt x (map u atTop)
  rw [← map_map, map_add_atTop_eq_nat]

private theorem james_refine_clusterHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E)
    (φ : WeakDual ℝ E → ℝ)
    (hclosed : ∀ r, IsClosed {x | φ x ≤ r})
    (hconvex : ∀ r, Convex ℝ {x | φ x ≤ r})
    (hbounded : BddAbove (φ '' jamesClusterHull u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ x ∈ jamesClusterHull (u ∘ σ), ∀ y ∈ jamesClusterHull (u ∘ σ),
        |φ x - φ y| < ε := by
  let _ : LocallyConvexSpace ℝ (WeakDual ℝ E) :=
    WithSeminorms.toLocallyConvexSpace (WeakDual.withSeminorms ℝ E)
  have hKne : (jamesClusterHull u).Nonempty :=
    (james_clusterHull_nonempty_compact u hu).1
  let S : ℝ := sSup (φ '' jamesClusterHull u)
  have hnear : S - ε < S := sub_lt_self S hε
  obtain ⟨v, ⟨z, hzK, rfl⟩, hz⟩ :=
    exists_lt_of_lt_csSup (hKne.image φ) hnear
  have hc : ∃ c ∈ jamesClusterSet u, S - ε < φ c := by
    by_contra h
    have hclusters : jamesClusterSet u ⊆ {x | φ x ≤ S - ε} := by
      intro c hc
      exact le_of_not_gt fun hgt => h ⟨c, hc, hgt⟩
    have hKsub : jamesClusterHull u ⊆ {x | φ x ≤ S - ε} :=
      closedConvexHull_min hclusters (hconvex _) (hclosed _)
    exact (not_lt_of_ge (hKsub hzK)) hz
  obtain ⟨c, hccluster, hcφ⟩ := hc
  let A : Set (WeakDual ℝ E) := {x | φ x ≤ S - ε}
  obtain ⟨U, V, hUopen, hVopen, hUconvex, _, hcU, hAV, hUV⟩ :=
    exists_open_convex_of_notMem (s := A) (x := c)
      (by exact not_le.mpr hcφ) (hconvex _) (hclosed _)
  have hfreq : ∃ᶠ n in atTop, u n ∈ U :=
    hccluster.frequently (hUopen.mem_nhds hcU)
  obtain ⟨σ, hσ, hσU⟩ := Filter.extraction_of_frequently_atTop hfreq
  refine ⟨σ, hσ, ?_⟩
  have hKclosure : jamesClusterHull (u ∘ σ) ⊆ closure U := by
    apply closedConvexHull_min
    · intro x hx
      exact isClosed_closure.mem_of_mapClusterPt hx
        (Filter.Eventually.of_forall fun n => subset_closure (hσU n))
    · exact hUconvex.closure
    · exact isClosed_closure
  have hKsub : jamesClusterHull (u ∘ σ) ⊆ jamesClusterHull u :=
    james_clusterHull_comp_subset u hσ
  have hclosureV : Disjoint (closure U) V := hUV.closure_left hVopen
  intro x hx y hy
  have hxlo : S - ε < φ x := by
    apply lt_of_not_ge
    intro hxle
    exact Set.disjoint_left.1 hclosureV (hKclosure hx) (hAV hxle)
  have hylo : S - ε < φ y := by
    apply lt_of_not_ge
    intro hyle
    exact Set.disjoint_left.1 hclosureV (hKclosure hy) (hAV hyle)
  have hxhi : φ x ≤ S := le_csSup hbounded ⟨x, hKsub hx, rfl⟩
  have hyhi : φ y ≤ S := le_csSup hbounded ⟨y, hKsub hy, rfl⟩
  rw [abs_lt]
  constructor <;> linarith

private theorem james_diagonal_clusterHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E)
    (φ : ℕ → WeakDual ℝ E → ℝ)
    (hclosed : ∀ m r, IsClosed {x | φ m x ≤ r})
    (hconvex : ∀ m r, Convex ℝ {x | φ m x ≤ r})
    (hbounded : ∀ m, BddAbove (φ m '' jamesDualBall E)) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧
      ∀ m, ∀ x ∈ jamesClusterHull (u ∘ δ), ∀ y ∈ jamesClusterHull (u ∘ δ),
        φ m x = φ m y := by
  let Seq := {σ : ℕ → ℕ // StrictMono σ}
  let initial : Seq := ⟨id, strictMono_id⟩
  have hrefine (n : ℕ) (s : Seq) :
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ 0 < ρ 0 ∧
        ∀ x ∈ jamesClusterHull ((u ∘ s.1) ∘ ρ),
          ∀ y ∈ jamesClusterHull ((u ∘ s.1) ∘ ρ),
            |φ (Nat.unpair n).1 x - φ (Nat.unpair n).1 y| <
              1 / ((Nat.unpair n).2 + 1 : ℝ) := by
    have hboundK : BddAbove
        (φ (Nat.unpair n).1 '' jamesClusterHull (u ∘ s.1)) := by
      apply (hbounded (Nat.unpair n).1).mono
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, james_clusterHull_subset_dualBall (u ∘ s.1) (fun k ↦ hu _) hx, rfl⟩
    have heps : 0 < 1 / ((Nat.unpair n).2 + 1 : ℝ) := by positivity
    obtain ⟨σ, hσ, hosc⟩ := james_refine_clusterHull (u ∘ s.1) (fun k ↦ hu _)
      (φ (Nat.unpair n).1) (hclosed _) (hconvex _) hboundK heps
    let ρ : ℕ → ℕ := σ ∘ fun k ↦ k + 1
    have hρ : StrictMono ρ := hσ.comp (strictMono_id.add_const 1)
    refine ⟨ρ, hρ, ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.zero_le (σ 0)) (hσ Nat.zero_lt_one)
    · intro x hx y hy
      apply hosc x ?_ y ?_
      · exact james_clusterHull_comp_subset ((u ∘ s.1) ∘ σ)
          (strictMono_id.add_const 1) hx
      · exact james_clusterHull_comp_subset ((u ∘ s.1) ∘ σ)
          (strictMono_id.add_const 1) hy
  let pick (n : ℕ) (s : Seq) : ℕ → ℕ := Classical.choose (hrefine n s)
  have pick_spec (n : ℕ) (s : Seq) :
      StrictMono (pick n s) ∧ 0 < pick n s 0 ∧
        ∀ x ∈ jamesClusterHull ((u ∘ s.1) ∘ pick n s),
          ∀ y ∈ jamesClusterHull ((u ∘ s.1) ∘ pick n s),
            |φ (Nat.unpair n).1 x - φ (Nat.unpair n).1 y| <
              1 / ((Nat.unpair n).2 + 1 : ℝ) :=
    Classical.choose_spec (hrefine n s)
  let step (n : ℕ) (s : Seq) : Seq :=
    ⟨s.1 ∘ pick n s, s.2.comp (pick_spec n s).1⟩
  let state : ℕ → Seq := fun n ↦ Nat.rec initial (fun n s ↦ step n s) n
  have state_succ (n : ℕ) : state (n + 1) = step n (state n) := by
    simp [state]
  let δ : ℕ → ℕ := fun n ↦ (state n).1 0
  have hδstep (n : ℕ) : δ n < δ (n + 1) := by
    rw [show δ n = (state n).1 0 by rfl,
      show δ (n + 1) = (state (n + 1)).1 0 by rfl, state_succ]
    exact (state n).2 (pick_spec n (state n)).2.1
  have hδ : StrictMono δ := strictMono_nat_of_lt_succ hδstep
  have hrange_succ (n : ℕ) :
      Set.range (state (n + 1)).1 ⊆ Set.range (state n).1 := by
    rw [state_succ]
    rintro _ ⟨k, rfl⟩
    exact ⟨pick n (state n) k, rfl⟩
  have hrange : Antitone (fun n ↦ Set.range (state n).1) :=
    antitone_nat_of_succ_le hrange_succ
  have hfinal (p : ℕ) :
      jamesClusterHull (u ∘ δ) ⊆ jamesClusterHull (u ∘ (state p).1) := by
    have hpre (k : ℕ) : δ (p + k) ∈ Set.range (state p).1 := by
      apply hrange (Nat.le_add_right p k)
      exact ⟨0, rfl⟩
    let θ : ℕ → ℕ := fun k ↦ Classical.choose (hpre k)
    have hθ (k : ℕ) : (state p).1 (θ k) = δ (p + k) :=
      Classical.choose_spec (hpre k)
    have hθmono : StrictMono θ := by
      intro a b hab
      rw [← (state p).2.lt_iff_lt, hθ, hθ]
      exact hδ (Nat.add_lt_add_left hab p)
    rw [← james_clusterHull_add_eq (u ∘ δ) p]
    have hsub := james_clusterHull_comp_subset (u ∘ (state p).1) hθmono
    have heq : (u ∘ δ) ∘ (fun n ↦ n + p) = (u ∘ (state p).1) ∘ θ := by
      funext k
      simp only [Function.comp_apply, hθ, Nat.add_comm]
    rw [heq]
    exact hsub
  refine ⟨δ, hδ, ?_⟩
  intro m x hx y hy
  by_contra hne
  have hpos : 0 < |φ m x - φ m y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  let n := Nat.pair m k
  have hx' : x ∈ jamesClusterHull (u ∘ (state (n + 1)).1) := hfinal (n + 1) hx
  have hy' : y ∈ jamesClusterHull (u ∘ (state (n + 1)).1) := hfinal (n + 1) hy
  have hosc := (pick_spec n (state n)).2.2 x
  rw [state_succ] at hx' hy'
  have hlt := hosc hx' y hy'
  rw [show Nat.unpair n = (m, k) by simp [n]] at hlt
  exact (not_lt_of_ge hk.le) hlt

private theorem james_isClosed_norm_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : StrongDual ℝ E) (a r : ℝ) :
    IsClosed {x : WeakDual ℝ E | ‖y - a • WeakDual.toStrongDual x‖ ≤ r} := by
  let A : WeakDual ℝ E → WeakDual ℝ E := fun x ↦
    StrongDual.toWeakDual y - a • x
  have hA : Continuous A := continuous_const.sub (continuous_const_smul a)
  have hp := (WeakDual.isClosed_closedBall (0 : StrongDual ℝ E) r).preimage hA
  convert hp using 1
  ext x
  simp [A]

private theorem james_convex_norm_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : StrongDual ℝ E) (a r : ℝ) :
    Convex ℝ {x : WeakDual ℝ E | ‖y - a • WeakDual.toStrongDual x‖ ≤ r} := by
  let A : WeakDual ℝ E →ᵃ[ℝ] WeakDual ℝ E :=
    AffineMap.const ℝ (WeakDual ℝ E) (StrongDual.toWeakDual y) -
      a • AffineMap.id ℝ (WeakDual ℝ E)
  have h := (convex_closedBall (0 : StrongDual ℝ E) r).linear_preimage
    WeakDual.toStrongDual.toLinearMap
  have hp : Convex ℝ (A ⁻¹' (WeakDual.toStrongDual ⁻¹' closedBall 0 r)) :=
    h.affine_preimage A
  convert hp using 1
  ext x
  simp [A]

private theorem james_bddAbove_norm_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y : StrongDual ℝ E) (a : ℝ) :
    BddAbove ((fun x : WeakDual ℝ E ↦ ‖y - a • WeakDual.toStrongDual x‖) ''
      jamesDualBall E) := by
  refine ⟨‖y‖ + |a|, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxnorm : ‖WeakDual.toStrongDual x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  calc
    ‖y - a • WeakDual.toStrongDual x‖ ≤ ‖y‖ + ‖a • WeakDual.toStrongDual x‖ :=
      norm_sub_le _ _
    _ = ‖y‖ + |a| * ‖WeakDual.toStrongDual x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖y‖ + |a| * 1 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hxnorm (abs_nonneg a))
    _ = ‖y‖ + |a| := by rw [mul_one]

private theorem james_clusterHull_norm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → StrongDual ℝ E) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ∃ δ : ℕ → ℕ, StrictMono δ ∧
      ∀ x ∈ jamesClusterHull (StrongDual.toWeakDual ∘ f ∘ δ),
        ∀ z ∈ jamesClusterHull (StrongDual.toWeakDual ∘ f ∘ δ),
          ∀ y ∈ (Submodule.span ℝ (Set.range f)).topologicalClosure,
            ∀ a : ℝ, ‖y - a • WeakDual.toStrongDual x‖ =
              ‖y - a • WeakDual.toStrongDual z‖ := by
  let Y : Submodule ℝ (StrongDual ℝ E) :=
    (Submodule.span ℝ (Set.range f)).topologicalClosure
  have hYsep : TopologicalSpace.IsSeparable (Y : Set (StrongDual ℝ E)) := by
    change TopologicalSpace.IsSeparable
      (((Submodule.span ℝ (Set.range f)).topologicalClosure :
        Submodule ℝ (StrongDual ℝ E)) : Set (StrongDual ℝ E))
    rw [Submodule.topologicalClosure_coe]
    exact (Set.countable_range f).isSeparable.span.closure
  let _ : TopologicalSpace.SeparableSpace Y := hYsep.separableSpace
  let d : ℕ → Y := TopologicalSpace.denseSeq Y
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let φ : ℕ → WeakDual ℝ E → ℝ := fun n x ↦
    ‖(d (Nat.unpair n).1 : StrongDual ℝ E) -
      q (Nat.unpair n).2 • WeakDual.toStrongDual x‖
  have hu (n : ℕ) : (StrongDual.toWeakDual ∘ f) n ∈ jamesDualBall E := by
    exact mem_closedBall_zero_iff.mpr (hf n)
  obtain ⟨δ, hδ, hconst⟩ := james_diagonal_clusterHull (StrongDual.toWeakDual ∘ f)
    hu φ (fun m ↦ james_isClosed_norm_sub_smul _ _)
    (fun m ↦ james_convex_norm_sub_smul _ _) (fun m ↦ james_bddAbove_norm_sub_smul _ _)
  refine ⟨δ, hδ, ?_⟩
  intro x hx z hz y hy a
  let yY : Y := ⟨y, hy⟩
  let F : Y × ℝ → ℝ := fun p ↦
    ‖(p.1 : StrongDual ℝ E) - p.2 • WeakDual.toStrongDual x‖
  let G : Y × ℝ → ℝ := fun p ↦
    ‖(p.1 : StrongDual ℝ E) - p.2 • WeakDual.toStrongDual z‖
  have hF : Continuous F := by
    exact ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_snd.smul continuous_const)).norm
  have hG : Continuous G := by
    exact ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_snd.smul continuous_const)).norm
  have hdense : DenseRange (Prod.map d q) :=
    (TopologicalSpace.denseRange_denseSeq Y).prodMap
      (TopologicalSpace.denseRange_denseSeq ℝ)
  have heqcomp : F ∘ Prod.map d q = G ∘ Prod.map d q := by
    funext p
    have hc := hconst (Nat.pair p.1 p.2) x hx z hz
    simpa [φ, d, q, F, G] using hc
  have heq : F = G := hdense.equalizer hF hG heqcomp
  exact congrFun heq (yY, a)

private theorem james_clusterHull_apply_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → StrongDual ℝ E) (x : E)
    (hlim : Tendsto (fun n ↦ f n x) atTop (nhds 0)) :
    ∀ w ∈ jamesClusterHull (StrongDual.toWeakDual ∘ f), w x = 0 := by
  let H : Set (WeakDual ℝ E) := {w | w x = 0}
  have hHclosed : IsClosed H := isClosed_eq (WeakDual.eval_continuous x) continuous_const
  have hHconvex : Convex ℝ H := by
    intro a ha b hb r s hr hs hrs
    change r * a x + s * b x = 0
    change a x = 0 at ha
    change b x = 0 at hb
    rw [ha, hb, mul_zero, mul_zero, add_zero]
  have hcluster : jamesClusterSet (StrongDual.toWeakDual ∘ f) ⊆ H := by
    intro w hw
    have hwscalar : MapClusterPt (w x) atTop (fun n ↦ f n x) := by
      convert hw.continuousAt_comp (WeakDual.eval_continuous x).continuousAt using 1
      rfl
    obtain ⟨ψ, hψmono, hψw⟩ := hwscalar.tendsto_subseq
    have hwlim : Tendsto (fun n ↦ f (ψ n) x) atTop (nhds (w x)) := hψw
    have hzero : Tendsto (fun n ↦ ((StrongDual.toWeakDual ∘ f) (ψ n)) x)
        atTop (nhds 0) := by
      convert hlim.comp hψmono.tendsto_atTop using 1
      rfl
    exact tendsto_nhds_unique hwlim hzero
  exact closedConvexHull_min hcluster hHconvex hHclosed

private theorem james_clusterHull_eq_iInter_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E) :
    jamesClusterHull u = ⋂ n : ℕ, closure (convexHull ℝ (u '' Set.Ici n)) := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iInter]
    intro n
    apply closedConvexHull_min (𝕜 := ℝ)
      (t := closure (convexHull ℝ (u '' Set.Ici n)))
    · intro z hz
      have htail : z ∈ closure (u '' Set.Ici n) := by
        simpa only [Set.mem_Ici] using
          (mapClusterPt_atTop_iff_forall_mem_closure.mp hz n)
      exact closure_mono (subset_convexHull ℝ _) htail
    · exact (convex_convexHull ℝ _).closure
    · exact isClosed_closure
    · exact hx
  · intro x hx
    simp only [Set.mem_iInter] at hx
    by_contra hxK
    let _ : LocallyConvexSpace ℝ (WeakDual ℝ E) :=
      WithSeminorms.toLocallyConvexSpace (WeakDual.withSeminorms ℝ E)
    obtain ⟨U, V, hUopen, hVopen, _, hVconvex, hxU, hKV, hUV⟩ :=
      exists_open_convex_of_notMem (s := jamesClusterHull u) (x := x) hxK
        (convex_closedConvexHull (𝕜 := ℝ)) isClosed_closedConvexHull
    have hevent : ∀ᶠ n in atTop, u n ∈ V := by
      by_contra h
      have hfreq : ∃ᶠ n in atTop, u n ∉ V := Filter.not_eventually.mp h
      obtain ⟨σ, hσ, hσV⟩ := Filter.extraction_of_frequently_atTop hfreq
      have hball : IsCompact (jamesDualBall E) := WeakDual.isCompact_closedBall 0 1
      have humap : Filter.map (u ∘ σ) atTop ≤ Filter.principal (jamesDualBall E) := by
        rw [Filter.le_principal_iff, Filter.mem_map]
        exact Filter.Eventually.of_forall fun n ↦ hu _
      obtain ⟨z, _, hz⟩ := hball.exists_mapClusterPt humap
      have hzcluster : z ∈ jamesClusterSet u := hz.of_comp hσ.tendsto_atTop
      have hzV : z ∈ V := hKV (subset_closedConvexHull hzcluster)
      have hznotV : z ∈ Vᶜ := by
        exact (hVopen.isClosed_compl).mem_of_mapClusterPt hz
          (Filter.Eventually.of_forall fun n ↦ hσV n)
      exact hznotV hzV
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    have htailV : u '' Set.Ici N ⊆ V := by
      rintro _ ⟨n, hn, rfl⟩
      exact hN n hn
    have hclosureV : closure (convexHull ℝ (u '' Set.Ici N)) ⊆ closure V :=
      closure_mono (convexHull_min htailV hVconvex)
    have hxclosureV : x ∈ closure V := hclosureV (hx N)
    exact Set.disjoint_left.1 (hUV.closure_right hUopen) hxU hxclosureV

private theorem james_clusterSet_convexBlocks_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u g : ℕ → WeakDual ℝ E) (hu : ∀ n, u n ∈ jamesDualBall E)
    (hg : ∀ n, g n ∈ convexHull ℝ (u '' Set.Ici n)) :
    jamesClusterSet g ⊆ jamesClusterHull u := by
  rw [james_clusterHull_eq_iInter_tail u hu]
  intro z hz
  simp only [Set.mem_iInter]
  intro n
  apply isClosed_closure.mem_of_mapClusterPt hz
  filter_upwards [eventually_ge_atTop n] with m hm
  apply subset_closure
  exact convexHull_mono (Set.image_mono (Set.Ici_subset_Ici.mpr hm)) (hg m)

private theorem james_selection_step
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Set V) (hAne : A.Nonempty) (hAconv : Convex ℝ A)
    (u : V) {β γ r : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hgap : ‖u‖ + β * r < sInf ((fun a : V ↦ ‖u + β • a‖) '' A)) :
    ∃ a₀ ∈ A,
      ‖u + β • a₀‖ + γ * r <
        sInf ((fun a : V ↦ ‖u + β • a₀ + γ • a‖) '' A) := by
  let m : ℝ := sInf ((fun a : V ↦ ‖u + β • a‖) '' A)
  let ε : ℝ := ((m - ‖u‖) / β - r) / 3
  have hratio : r < (m - ‖u‖) / β := by
    apply (lt_div_iff₀ hβ).2
    change ‖u‖ + β * r < m at hgap
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hm_lt : m < m + γ * ε :=
    lt_add_of_pos_right _ (mul_pos hγ hε)
  obtain ⟨_, ⟨a₀, ha₀, rfl⟩, ha₀near⟩ :=
    exists_lt_of_csInf_lt (hAne.image (fun a : V ↦ ‖u + β • a‖)) hm_lt
  refine ⟨a₀, ha₀, ?_⟩
  have hlower : ‖u + β • a₀‖ + γ * r + γ * ε ≤
      sInf ((fun a : V ↦ ‖u + β • a₀ + γ • a‖) '' A) := by
    apply le_csInf (hAne.image _)
    rintro _ ⟨a, ha, rfl⟩
    let v : V := (β / (β + γ)) • a₀ + (γ / (β + γ)) • a
    have hsumpos : 0 < β + γ := add_pos hβ hγ
    have hv : v ∈ A := by
      apply hAconv ha₀ ha
      · positivity
      · positivity
      · field_simp [hsumpos.ne']
    have hvm : m ≤ ‖u + β • v‖ := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
      · exact ⟨v, hv, rfl⟩
    have huv : u + (β + γ) • v = u + β • a₀ + γ • a := by
      dsimp [v]
      have hb : (β + γ) * (β / (β + γ)) = β := by
        field_simp [hsumpos.ne']
      have hg : (β + γ) * (γ / (β + γ)) = γ := by
        field_simp [hsumpos.ne']
      rw [smul_add, smul_smul, smul_smul, hb, hg]
      module
    let p : ℝ → ℝ := fun t ↦ ‖(AffineMap.lineMap u (u + v)) t‖
    have hpconv : ConvexOn ℝ Set.univ p := by
      exact convexOn_univ_norm.comp_affineMap (AffineMap.lineMap u (u + v))
    have hslope := hpconv.slope_mono_adjacent (x := 0) (y := β) (z := β + γ)
      (Set.mem_univ _) (Set.mem_univ _) hβ (by linarith)
    have hp0 : p 0 = ‖u‖ := by simp [p]
    have hpβ : p β = ‖u + β • v‖ := by
      apply congrArg norm
      simp only [AffineMap.lineMap_apply_module]
      module
    have hpβγ : p (β + γ) = ‖u + (β + γ) • v‖ := by
      apply congrArg norm
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hp0, hpβ, hpβγ] at hslope
    norm_num only [sub_zero, add_sub_cancel_left] at hslope
    have hsteep : r + 2 * ε < (‖u + β • v‖ - ‖u‖) / β := by
      have hmsteep : r + 2 * ε < (m - ‖u‖) / β := by
        dsimp [ε]
        linarith [hratio]
      exact hmsteep.trans_le (div_le_div_of_nonneg_right (sub_le_sub_right hvm _) hβ.le)
    have hfar : ‖u + β • v‖ + γ * (r + 2 * ε) <
        ‖u + (β + γ) • v‖ := by
      have hmul := (lt_div_iff₀ hγ).mp (hsteep.trans_le hslope)
      nlinarith
    change ‖u + β • a₀‖ + γ * r + γ * ε ≤ ‖u + β • a₀ + γ • a‖
    rw [← huv]
    change ‖u + β • a₀‖ < m + γ * ε at ha₀near
    have ha₀bound : ‖u + β • a₀‖ < ‖u + β • v‖ + γ * ε :=
      ha₀near.trans_le (by linarith)
    linarith
  exact lt_of_lt_of_le (by linarith [mul_pos hγ hε]) hlower

private theorem james_selection_sequence
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ℕ → Set V) (hAne : ∀ n, (A n).Nonempty)
    (hAconv : ∀ n, Convex ℝ (A n)) (hAanti : ∀ n, A (n + 1) ⊆ A n)
    {r R q : ℝ} (hr : r < R) (hq : 0 < q)
    (hlower : ∀ a ∈ A 0, R ≤ ‖a‖) :
    ∃ a : ℕ → V, (∀ n, a n ∈ A n) ∧
      ∀ n, ‖∑ i ∈ Finset.range n, q ^ i • a i‖ + q ^ n * r <
        ‖∑ i ∈ Finset.range (n + 1), q ^ i • a i‖ := by
  let β : ℕ → ℝ := fun n ↦ q ^ n
  let Inv (n : ℕ) (u : V) : Prop :=
    ‖u‖ + β n * r < sInf ((fun a : V ↦ ‖u + β n • a‖) '' A n)
  let State (n : ℕ) := {u : V // Inv n u}
  have hinit : Inv 0 0 := by
    change ‖(0 : V)‖ + q ^ 0 * r <
      sInf ((fun a : V ↦ ‖(0 : V) + q ^ 0 • a‖) '' A 0)
    simp only [norm_zero, zero_add, pow_zero, one_mul, one_smul]
    exact hr.trans_le (le_csInf ((hAne 0).image _) fun _ h ↦ by
      obtain ⟨a, ha, rfl⟩ := h
      exact hlower a ha)
  let initial : State 0 := ⟨0, hinit⟩
  have hstep (n : ℕ) (s : State n) :
      ∃ a₀ ∈ A n,
        ‖s.1 + β n • a₀‖ + β (n + 1) * r <
          sInf ((fun a : V ↦ ‖s.1 + β n • a₀ + β (n + 1) • a‖) '' A n) := by
    exact james_selection_step (A n) (hAne n) (hAconv n) s.1
      (pow_pos hq n) (pow_pos hq (n + 1)) s.2
  let pick (n : ℕ) (s : State n) : V := Classical.choose (hstep n s)
  have pick_spec (n : ℕ) (s : State n) :
      pick n s ∈ A n ∧
        ‖s.1 + β n • pick n s‖ + β (n + 1) * r <
          sInf ((fun a : V ↦ ‖s.1 + β n • pick n s + β (n + 1) • a‖) '' A n) :=
    Classical.choose_spec (hstep n s)
  let next (n : ℕ) (s : State n) : State (n + 1) := by
    refine ⟨s.1 + β n • pick n s, ?_⟩
    change ‖s.1 + β n • pick n s‖ + β (n + 1) * r <
      sInf ((fun a : V ↦
        ‖s.1 + β n • pick n s + β (n + 1) • a‖) '' A (n + 1))
    apply (pick_spec n s).2.trans_le
    apply le_csInf ((hAne (n + 1)).image _)
    rintro _ ⟨a, ha, rfl⟩
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
    · exact ⟨a, hAanti n ha, rfl⟩
  let state : (n : ℕ) → State n := fun n ↦
    Nat.rec initial (fun n s ↦ next n s) n
  have state_succ (n : ℕ) : (state (n + 1)).1 =
      (state n).1 + β n • pick n (state n) := by
    simp [state, next]
  let a : ℕ → V := fun n ↦ pick n (state n)
  have ha (n : ℕ) : a n ∈ A n := (pick_spec n (state n)).1
  have hstate (n : ℕ) : (state n).1 =
      ∑ i ∈ Finset.range n, β i • a i := by
    induction n with
    | zero => rfl
    | succ n ih => rw [state_succ, ih, Finset.sum_range_succ]
  refine ⟨a, ha, ?_⟩
  intro n
  have hgap := (state n).2
  have hinf_le : sInf ((fun z : V ↦ ‖(state n).1 + β n • z‖) '' A n) ≤
      ‖(state n).1 + β n • a n‖ := by
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
    · exact ⟨a n, ha n, rfl⟩
  have h := hgap.trans_le hinf_le
  rw [hstate n] at h
  simpa [β, Finset.sum_range_succ] using h

private theorem james_convex_tail_norm_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (f : ℕ → StrongDual ℝ E) (fLim : StrongDual ℝ E) (θ : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ 1)
    (htri : ∀ j n, j < n → θ < f j (x n))
    (hzero : ∀ n, fLim (x n) = 0) :
    ∀ n, ∀ h ∈ convexHull ℝ (f '' Set.Ici n), θ < ‖h - fLim‖ := by
  intro n h hh
  obtain ⟨ι, hι, w, z, hw, hwsum, hz, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hh
  let _ : Fintype ι := hι
  have hz' (i : ι) : ∃ k : ℕ, n ≤ k ∧ f k = z i := by
    simpa only [Set.mem_image, Set.mem_Ici] using hz i
  choose k hkN hkz using hz'
  let m : ℕ := Finset.univ.sup k + 1
  have hkm (i : ι) : k i < m := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := k) (Finset.mem_univ i))
  have hzeval (i : ι) : θ < z i (x m) := by
    rw [← hkz i]
    exact htri (k i) m (hkm i)
  have hhalf : Convex ℝ {g : StrongDual ℝ E | θ < g (x m)} := by
    intro a ha b hb r s hr hs hrs
    change θ < r * a (x m) + s * b (x m)
    by_cases hr0 : r = 0
    · subst r
      simp only [zero_add] at hrs
      subst s
      simpa using hb
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      calc
        θ = r * θ + s * θ := by rw [← add_mul, hrs, one_mul]
        _ < r * a (x m) + s * b (x m) :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left ha hrpos)
            (mul_le_mul_of_nonneg_left hb.le hs)
  have hcombo : (∑ i, w i • z i) ∈ {g : StrongDual ℝ E | θ < g (x m)} := by
    have hmem : (∑ i, w i • z i) ∈ convexHull ℝ (Set.range z) :=
      mem_convexHull_of_exists_fintype w z hw hwsum
        (fun i ↦ Set.mem_range_self i) rfl
    apply (convexHull_min (t := {g : StrongDual ℝ E | θ < g (x m)}) _ hhalf) hmem
    rintro _ ⟨i, rfl⟩
    exact hzeval i
  have hheval : θ < h (x m) := by
    rw [← hsum]
    exact hcombo
  have hdiff : θ < (h - fLim) (x m) := by
    simp only [sub_apply, hzero, sub_zero]
    exact hheval
  calc
    θ < ‖(h - fLim) (x m)‖ := hdiff.trans_le (Real.le_norm_self _)
    _ ≤ ‖h - fLim‖ * ‖x m‖ := (h - fLim).le_opNorm (x m)
    _ ≤ ‖h - fLim‖ * 1 := mul_le_mul_of_nonneg_left (hx m) (norm_nonneg _)
    _ = ‖h - fLim‖ := mul_one _

private theorem james_exists_separator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Φ : StrongDual ℝ (StrongDual ℝ E))
    (hΦ : Φ ∉ Set.range (NormedSpace.inclusionInDoubleDual ℝ E)) :
    ∃ L : StrongDual ℝ (StrongDual ℝ (StrongDual ℝ E)),
      0 < L Φ ∧
        ∀ x : E, L (NormedSpace.inclusionInDoubleDual ℝ E x) = 0 := by
  let J := NormedSpace.inclusionInDoubleDual ℝ E
  have hrangeclosed : IsClosed (Set.range J) := by
    have hJiso : Isometry J := by
      apply Isometry.of_dist_eq
      intro x y
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact (NormedSpace.inclusionInDoubleDualLi ℝ (E := E)).norm_map (x - y)
    exact hJiso.isClosedEmbedding.isClosed_range
  have hrangeconvex : Convex ℝ (Set.range J) := by
    rw [show Set.range J = (J.toLinearMap.range : Set _) by ext; simp]
    exact Submodule.convex _
  let _ : LocallyConvexSpace ℝ (StrongDual ℝ (StrongDual ℝ E)) :=
    @NormedSpace.toLocallyConvexSpace (StrongDual ℝ (StrongDual ℝ E))
      (inferInstance) (inferInstance)
  obtain ⟨L, c, hLc, hcΦ⟩ :=
    geometric_hahn_banach_closed_point hrangeconvex hrangeclosed hΦ
  have hcpos : 0 < c := by
    have h0 := hLc 0 ⟨0, map_zero J⟩
    simpa using h0
  have hLzero (z : StrongDual ℝ (StrongDual ℝ E)) (hz : z ∈ Set.range J) : L z = 0 := by
    by_contra hz0
    let a : ℝ := (c + 1) / L z
    have haz : a • z ∈ Set.range J := by
      obtain ⟨x, rfl⟩ := hz
      exact ⟨a • x, by simp [J]⟩
    have hlt := hLc (a • z) haz
    have ha : a * L z = c + 1 := div_mul_cancel₀ (c + 1) hz0
    rw [map_smul, smul_eq_mul, ha] at hlt
    linarith
  have hLΦpos : 0 < L Φ := hcpos.trans hcΦ
  exact ⟨L, hLΦpos, fun x ↦ hLzero _ ⟨x, rfl⟩⟩

/-- A finite-coordinate form of Goldstine's theorem for the real bidual unit ball. -/
theorem _root_.NormedSpace.goldstine_finite
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : StrongDual ℝ (StrongDual ℝ X)) (hT : ‖T‖ ≤ 1)
    (s : Finset (StrongDual ℝ X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ ∀ z ∈ s, |z x - T z| < ε := by
  let S : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    (StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual ℝ X) ''
      closedBall (0 : X) 1
  let U : Set (WeakDual ℝ (StrongDual ℝ X)) :=
    {w | ∀ z ∈ s, |w z - T z| < ε}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ z ∈ s, {w | |w z - T z| < ε} by ext; simp [U]]
    exact isOpen_biInter_finset fun z _ ↦
      isOpen_lt (continuous_abs.comp ((WeakDual.eval_continuous z).sub continuous_const))
        continuous_const
  have hTU : StrongDual.toWeakDual T ∈ U := by
    intro z hz
    simp [hε]
  have hTS : StrongDual.toWeakDual T ∈ closure S := by
    change StrongDual.toWeakDual T ∈ closure
      ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual ℝ X) ''
        closedBall (0 : X) 1)
    rw [MetaMathlibExt.goldstine]
    simp only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual]
    apply Metric.mem_closedBall.mpr
    have e : dist T 0 = ‖T‖ := dist_zero_right T
    rw [e]
    exact hT
  obtain ⟨w, hwU, hwS⟩ := mem_closure_iff.mp hTS U hUopen hTU
  obtain ⟨x, hx, rfl⟩ := hwS
  refine ⟨x, mem_closedBall_zero_iff.mp hx, ?_⟩
  intro z hz
  exact hwU z hz

private theorem james_normalize_functional
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : StrongDual ℝ (StrongDual ℝ X))
    (z : StrongDual ℝ X) (hz : 0 < L z) :
    ∃ T : StrongDual ℝ (StrongDual ℝ X),
      ‖T‖ ≤ 1 ∧ 0 < T z ∧ ∀ y, L y = 0 → T y = 0 := by
  obtain ⟨C, hCpos, hC⟩ := L.bound
  let T : StrongDual ℝ (StrongDual ℝ X) := C⁻¹ • L
  refine ⟨T, ?_, ?_, ?_⟩
  · apply T.opNorm_le_bound zero_le_one
    intro y
    change ‖(C⁻¹ • L) y‖ ≤ 1 * ‖y‖
    rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hCpos), one_mul]
    calc
      C⁻¹ * ‖L y‖ ≤ C⁻¹ * (C * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hC y) (inv_nonneg.mpr hCpos.le)
      _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul]
  · change 0 < (C⁻¹ • L) z
    rw [smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hCpos) hz
  · intro y hy
    change (C⁻¹ • L) y = 0
    rw [smul_apply, smul_eq_mul, hy, mul_zero]

private theorem james_build_triangular_sequences
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : E →L[ℝ] StrongDual ℝ X) (Φ : StrongDual ℝ X)
    (happrox : ∀ (s : Finset X) {ε : ℝ}, 0 < ε →
      ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ z ∈ s, |A x z - Φ z| < ε)
    (T : StrongDual ℝ (StrongDual ℝ X)) (hT : ‖T‖ ≤ 1)
    (hTΦ : 0 < T Φ) (hTA : ∀ x, T (A x) = 0) :
    ∃ x : ℕ → E, ∃ f : ℕ → X, ∃ θ : ℝ, 0 < θ ∧
      (∀ n, ‖x n‖ ≤ 1) ∧ (∀ n, ‖f n‖ ≤ 1) ∧
      (∀ j n, j < n → θ < A (x n) (f j)) ∧
      ∀ j, Tendsto (fun n ↦ A (x j) (f n)) atTop (nhds 0) := by
  classical
  let θ : ℝ := T Φ / 2
  have hθ : 0 < θ := div_pos hTΦ (by positivity)
  let η : ℕ → ℝ := fun n ↦ min (T Φ / 4) (1 / (n + 1 : ℝ))
  have hηpos (n : ℕ) : 0 < η n := by
    exact lt_min (div_pos hTΦ (by positivity)) (by positivity)
  have hηle (n : ℕ) : η n ≤ T Φ / 4 := min_le_left _ _
  have hηlim : Tendsto η atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ (hηpos n).le) (fun n ↦ min_le_right _ _)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hxexists (l : List X) :
      ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ z ∈ l, |A x z - Φ z| < T Φ / 4 := by
    obtain ⟨x, hx, hxl⟩ := happrox l.toFinset (ε := T Φ / 4)
      (div_pos hTΦ (by positivity))
    exact ⟨x, hx, fun z hz ↦ hxl z (List.mem_toFinset.mpr hz)⟩
  let chooseX (l : List X) : E := Classical.choose (hxexists l)
  have chooseX_spec (l : List X) :
      ‖chooseX l‖ ≤ 1 ∧ ∀ z ∈ l, |A (chooseX l) z - Φ z| < T Φ / 4 :=
    Classical.choose_spec (hxexists l)
  have hfexists (n : ℕ) (l : List E) :
      ∃ f : X, ‖f‖ ≤ 1 ∧ |Φ f - T Φ| < η n ∧
        ∀ x ∈ l, |A x f| < η n := by
    let s : Finset (StrongDual ℝ X) := {Φ} ∪ l.toFinset.image A
    obtain ⟨f, hf, hfs⟩ := NormedSpace.goldstine_finite T hT s (hηpos n)
    refine ⟨f, hf, ?_, ?_⟩
    · exact hfs Φ (by simp [s])
    · intro x hx
      have hmem : A x ∈ s := Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨x, List.mem_toFinset.mpr hx, rfl⟩)
      have h := hfs (A x) hmem
      simpa [hTA x] using h
  let chooseF (n : ℕ) (l : List E) : X := Classical.choose (hfexists n l)
  have chooseF_spec (n : ℕ) (l : List E) :
      ‖chooseF n l‖ ≤ 1 ∧ |Φ (chooseF n l) - T Φ| < η n ∧
        ∀ x ∈ l, |A x (chooseF n l)| < η n :=
    Classical.choose_spec (hfexists n l)
  let State := List E × List X
  let initial : State := ([], [])
  let step (n : ℕ) (s : State) : State :=
    let xn := chooseX s.2
    let fn := chooseF n (s.1 ++ [xn])
    (s.1 ++ [xn], s.2 ++ [fn])
  let state : ℕ → State := fun n ↦ Nat.rec initial (fun n s ↦ step n s) n
  have state_succ (n : ℕ) : state (n + 1) = step n (state n) := by simp [state]
  let x : ℕ → E := fun n ↦ chooseX (state n).2
  let f : ℕ → X := fun n ↦ chooseF n ((state n).1 ++ [x n])
  have state_succ_fst (n : ℕ) : (state (n + 1)).1 = (state n).1 ++ [x n] := by
    rw [state_succ]
  have state_succ_snd (n : ℕ) : (state (n + 1)).2 = (state n).2 ++ [f n] := by
    rw [state_succ]
  have hxmem : ∀ {j n}, j < n → x j ∈ (state n).1 := by
    intro j n hjn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [show n + 1 = n + 1 by rfl, state_succ_fst]
        rw [List.mem_append, List.mem_singleton]
        by_cases h : j < n
        · exact Or.inl (ih h)
        · have hjn' : j = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hjn)
            (Nat.le_of_not_gt h)
          exact Or.inr (congrArg x hjn')
  have hfmem : ∀ {j n}, j < n → f j ∈ (state n).2 := by
    intro j n hjn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [show n + 1 = n + 1 by rfl, state_succ_snd]
        rw [List.mem_append, List.mem_singleton]
        by_cases h : j < n
        · exact Or.inl (ih h)
        · have hjn' : j = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hjn)
            (Nat.le_of_not_gt h)
          exact Or.inr (congrArg f hjn')
  refine ⟨x, f, θ, hθ, fun n ↦ (chooseX_spec _).1,
    fun n ↦ (chooseF_spec _ _).1, ?_, ?_⟩
  · intro j n hjn
    have hfx := (chooseF_spec j ((state j).1 ++ [x j])).2.1
    have hxn := (chooseX_spec (state n).2).2 (f j) (hfmem hjn)
    change |Φ (f j) - T Φ| < η j at hfx
    change |A (x n) (f j) - Φ (f j)| < T Φ / 4 at hxn
    rw [abs_lt] at hfx hxn
    change T Φ / 2 < A (x n) (f j)
    have hηj := hηle j
    linarith
  · intro j
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _) ?_ hηlim
    filter_upwards [eventually_ge_atTop j] with n hnj
    have hxjl : x j ∈ (state n).1 ++ [x n] := by
      rw [List.mem_append]
      by_cases h : j < n
      · exact Or.inl (hxmem h)
      · exact Or.inr (by simp [show j = n by omega])
    exact ((chooseF_spec n ((state n).1 ++ [x n])).2.2 (x j) hxjl).le

private theorem james_triangular_sequences_of_not_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hJ : ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) :
    ∃ x : ℕ → E, ∃ f : ℕ → StrongDual ℝ E, ∃ θ : ℝ, 0 < θ ∧
      (∀ n, ‖x n‖ ≤ 1) ∧ (∀ n, ‖f n‖ ≤ 1) ∧
      (∀ j n, j < n → θ < f j (x n)) ∧
      ∀ j, Tendsto (fun n ↦ f n (x j)) atTop (nhds 0) := by
  rw [Function.Surjective] at hJ
  push Not at hJ
  obtain ⟨Φ, hΦ⟩ := hJ
  have hΦrange : Φ ∉ Set.range (NormedSpace.inclusionInDoubleDual ℝ E) := by
    rintro ⟨x, hx⟩
    exact hΦ x hx
  have hΦne : Φ ≠ 0 := by
    intro heq
    apply hΦrange
    exact ⟨0, by simp [heq]⟩
  obtain ⟨C, hCpos, hC⟩ := Φ.bound
  let Φ0 : StrongDual ℝ (StrongDual ℝ E) := C⁻¹ • Φ
  have hΦ0norm : ‖Φ0‖ ≤ 1 := by
    apply Φ0.opNorm_le_bound zero_le_one
    intro f
    change ‖(C⁻¹ • Φ) f‖ ≤ 1 * ‖f‖
    rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hCpos), one_mul]
    calc
      C⁻¹ * ‖Φ f‖ ≤ C⁻¹ * (C * ‖f‖) :=
        mul_le_mul_of_nonneg_left (hC f) (inv_nonneg.mpr hCpos.le)
      _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul]
  have hΦ0range : Φ0 ∉ Set.range (NormedSpace.inclusionInDoubleDual ℝ E) := by
    rintro ⟨x, hx⟩
    apply hΦrange
    refine ⟨C • x, ?_⟩
    rw [map_smul, hx]
    change C • (C⁻¹ • Φ) = Φ
    rw [← mul_smul, mul_inv_cancel₀ hCpos.ne', one_smul]
  obtain ⟨L, hLΦ, hLzero⟩ := james_exists_separator Φ0 hΦ0range
  obtain ⟨T, hTnorm, hTΦ, hTzero⟩ :=
    james_normalize_functional (X := StrongDual ℝ E) L Φ0 hLΦ
  have happrox (s : Finset (StrongDual ℝ E)) {ε : ℝ} (hε : 0 < ε) :
      ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ z ∈ s,
        |NormedSpace.inclusionInDoubleDual ℝ E x z - Φ0 z| < ε := by
    exact NormedSpace.goldstine_finite Φ0 hΦ0norm s hε
  obtain ⟨x, f, θ, hθ, hx, hf, htri, hzero⟩ :=
    james_build_triangular_sequences (NormedSpace.inclusionInDoubleDual ℝ E) Φ0
      happrox T hTnorm hTΦ (fun x ↦ hTzero _ (hLzero x))
  refine ⟨x, f, θ, hθ, hx, hf, ?_, ?_⟩
  · simpa only [NormedSpace.dual_def] using htri
  · simpa only [NormedSpace.dual_def] using hzero

private theorem james_positive_norm_attainment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ∀ f : StrongDual ℝ E, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖)
    (f : StrongDual ℝ E) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ f x = ‖f‖ := by
  obtain ⟨x, hx, hfx⟩ := h f
  by_cases hnonneg : 0 ≤ f x
  · refine ⟨x, hx, ?_⟩
    calc
      f x = |f x| := (abs_of_nonneg hnonneg).symm
      _ = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ = ‖f‖ := hfx
  · refine ⟨-x, by simpa, ?_⟩
    have hneg : f x < 0 := lt_of_not_ge hnonneg
    rw [map_neg, ← hfx, Real.norm_eq_abs, abs_of_neg hneg]

private theorem james_select_convex_blocks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (f : ℕ → StrongDual ℝ E) (fLim : StrongDual ℝ E) (θ : ℝ)
    (hθ : 0 < θ) (hx : ∀ n, ‖x n‖ ≤ 1)
    (htri : ∀ j n, j < n → θ < f j (x n))
    (hzero : ∀ n, fLim (x n) = 0) :
    ∃ g : ℕ → StrongDual ℝ E,
      (∀ n, g n ∈ convexHull ℝ (f '' Set.Ici n)) ∧
      ∀ n,
        ‖∑ i ∈ Finset.range n, (θ / 32) ^ i • (g i - fLim)‖ +
            (θ / 32) ^ n * (θ / 2) <
          ‖∑ i ∈ Finset.range (n + 1), (θ / 32) ^ i • (g i - fLim)‖ := by
  let A : ℕ → Set (StrongDual ℝ E) := fun n ↦
    (fun h ↦ h - fLim) '' convexHull ℝ (f '' Set.Ici n)
  have hAne (n : ℕ) : (A n).Nonempty := by
    refine ⟨f n - fLim, ⟨f n, ?_, rfl⟩⟩
    exact subset_convexHull ℝ (f '' Set.Ici n)
      (Set.mem_image_of_mem f (Set.mem_Ici.mpr le_rfl))
  have hAconv (n : ℕ) : Convex ℝ (A n) := by
    rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ r s hr hs hrs
    refine ⟨r • a' + s • b', (convex_convexHull ℝ _ ha' hb' hr hs hrs), ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]
    linear_combination (fLim y) * hrs
  have hAanti (n : ℕ) : A (n + 1) ⊆ A n := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, convexHull_mono (Set.image_mono (Set.Ici_subset_Ici.mpr
      (Nat.le_add_right n 1))) ha, rfl⟩
  have hlower : ∀ a ∈ A 0, θ ≤ ‖a‖ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (james_convex_tail_norm_lower x f fLim θ hx htri hzero 0 a ha).le
  obtain ⟨a, ha, hsel⟩ := james_selection_sequence A hAne hAconv hAanti
    (r := θ / 2) (R := θ) (q := θ / 32) (by linarith) (div_pos hθ (by norm_num)) hlower
  have hgexists (n : ℕ) :
      ∃ g ∈ convexHull ℝ (f '' Set.Ici n), g - fLim = a n := by
    exact ha n
  choose g hg hgsub using hgexists
  refine ⟨g, hg, ?_⟩
  simpa only [hgsub] using hsel

private theorem james_sum_smul_sub
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Finset ℕ) (β : ℕ → ℝ) (g : ℕ → V) (z : V) :
    (∑ i ∈ s, β i • (g i - z)) =
      (∑ i ∈ s, β i • g i) - (∑ i ∈ s, β i) • z := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_smul]

private theorem james_geometric_series_contradiction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hattain : ∀ f : StrongDual ℝ E, ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖)
    (g : ℕ → StrongDual ℝ E) (gLimW : WeakDual ℝ E) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ < 1)
    (hgNorm : ∀ n, ‖g n‖ ≤ 1) (hgLimNorm : ‖WeakDual.toStrongDual gLimW‖ ≤ 1)
    (hinc : ∀ n,
      ‖∑ i ∈ Finset.range n,
          (θ / 32) ^ i • (g i - WeakDual.toStrongDual gLimW)‖ +
          (θ / 32) ^ n * (θ / 2) <
        ‖∑ i ∈ Finset.range (n + 1),
          (θ / 32) ^ i • (g i - WeakDual.toStrongDual gLimW)‖)
    (hcluster : MapClusterPt gLimW atTop (StrongDual.toWeakDual ∘ g)) : False := by
  let gLim : StrongDual ℝ E := WeakDual.toStrongDual gLimW
  let q : ℝ := θ / 32
  have hqpos : 0 < q := div_pos hθ (by norm_num)
  have hqhalf : q ≤ 1 / 2 := by
    dsimp [q]
    linarith [hθone]
  have hqone : q < 1 := hqhalf.trans_lt (by norm_num)
  let term : ℕ → StrongDual ℝ E := fun n ↦ q ^ n • (g n - gLim)
  have hgeom : Summable (fun n : ℕ ↦ q ^ n) :=
    summable_geometric_of_lt_one hqpos.le hqone
  have htermNorm (n : ℕ) : ‖term n‖ ≤ 2 * q ^ n := by
    rw [show term n = q ^ n • (g n - gLim) by rfl, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hqpos.le n)]
    calc
      q ^ n * ‖g n - gLim‖ ≤ q ^ n * (‖g n‖ + ‖gLim‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hqpos.le n)
      _ ≤ q ^ n * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add (hgNorm n) hgLimNorm)
          (pow_nonneg hqpos.le n)
      _ = 2 * q ^ n := by ring
  have hseries : Summable term :=
    (hgeom.mul_left 2).of_norm_bounded htermNorm
  let G : StrongDual ℝ E := ∑' n, term n
  obtain ⟨c, hc, hGc⟩ := james_positive_norm_attainment hattain G
  let P : ℕ → StrongDual ℝ E := fun n ↦ ∑ i ∈ Finset.range n, term i
  have hinc' (n : ℕ) : ‖P n‖ + q ^ n * (θ / 2) < ‖P (n + 1)‖ := by
    exact hinc n
  have htailHas (n : ℕ) :
      HasSum (fun k : ℕ ↦ 2 * q ^ (k + (n + 1)))
        (2 * q ^ (n + 1) * (1 - q)⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hqpos.le hqone).mul_left
      (2 * q ^ (n + 1))
    convert h using 1
    · ext k
      rw [pow_add]
      ring
  have htailNorm (n : ℕ) :
      ‖∑' k : ℕ, term (k + (n + 1))‖ ≤
        2 * q ^ (n + 1) * (1 - q)⁻¹ := by
    apply tsum_of_norm_bounded (htailHas n)
    intro k
    exact htermNorm (k + (n + 1))
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith [hqhalf])]
    linarith [hqhalf]
  have htailSmall (n : ℕ) :
      2 * ‖∑' k : ℕ, term (k + (n + 1))‖ ≤ q ^ n * (θ / 4) := by
    calc
      2 * ‖∑' k : ℕ, term (k + (n + 1))‖ ≤
          2 * (2 * q ^ (n + 1) * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left (htailNorm n) (by norm_num)
      _ ≤ 2 * (2 * q ^ (n + 1) * 2) := by
        gcongr
      _ = q ^ n * (θ / 4) := by
        rw [pow_succ]
        dsimp [q]
        ring
  let R : ℕ → StrongDual ℝ E := fun n ↦ ∑' k : ℕ, term (k + (n + 1))
  have hdecomp (n : ℕ) : P (n + 1) + R n = G := by
    simpa only [P, R, G] using hseries.sum_add_tsum_nat_add (n + 1)
  have heval_le (H : StrongDual ℝ E) : H c ≤ ‖H‖ := by
    calc
      H c ≤ ‖H c‖ := Real.le_norm_self _
      _ ≤ ‖H‖ * ‖c‖ := H.le_opNorm c
      _ ≤ ‖H‖ * 1 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = ‖H‖ := mul_one _
  have hdefect (n : ℕ) :
      ‖P (n + 1)‖ ≤ P (n + 1) c + 2 * ‖R n‖ := by
    have hP : P (n + 1) = G - R n := by
      rw [← hdecomp n]
      abel
    have heval : P (n + 1) c + R n c = G c := by
      simpa only [add_apply] using
        congrArg (fun H : StrongDual ℝ E ↦ H c) (hdecomp n)
    calc
      ‖P (n + 1)‖ = ‖G - R n‖ := congrArg norm hP
      _ ≤ ‖G‖ + ‖R n‖ := norm_sub_le _ _
      _ = G c + ‖R n‖ := by rw [hGc]
      _ = P (n + 1) c + R n c + ‖R n‖ := by rw [heval]
      _ ≤ P (n + 1) c + 2 * ‖R n‖ := by
        linarith [heval_le (R n)]
  have hPsuccEval (n : ℕ) :
      P (n + 1) c = P n c + q ^ n * (g n c - gLim c) := by
    simp only [P, Finset.sum_range_succ, term, add_apply, smul_apply, sub_apply,
      smul_eq_mul]
  have huniform (n : ℕ) : θ / 4 < g n c - gLim c := by
    have hscaled : q ^ n * (θ / 4) < q ^ n * (g n c - gLim c) := by
      have htail := htailSmall n
      change 2 * ‖R n‖ ≤ q ^ n * (θ / 4) at htail
      nlinarith [hinc' n, heval_le (P n), hdefect n, hPsuccEval n]
    exact lt_of_mul_lt_mul_left hscaled (pow_pos hqpos n).le
  let H : Set (WeakDual ℝ E) := {w | θ / 4 ≤ w c - gLimW c}
  have hHclosed : IsClosed H :=
    isClosed_le continuous_const ((WeakDual.eval_continuous c).sub continuous_const)
  have hgwH : ∀ᶠ n in atTop, (StrongDual.toWeakDual ∘ g) n ∈ H := by
    apply Filter.Eventually.of_forall
    intro n
    change θ / 4 ≤ (StrongDual.toWeakDual (g n)) c - gLimW c
    simpa only [gLim, StrongDual.toWeakDual_apply, WeakDual.toStrongDual_apply] using
      (huniform n).le
  have hgLimH : gLimW ∈ H := hHclosed.mem_of_mapClusterPt hcluster hgwH
  change θ / 4 ≤ gLimW c - gLimW c at hgLimH
  linarith

/-- If every `𝕜`-linear functional attains its norm on the closed unit ball, then every
real-linear functional does too after restricting scalars from an `RCLike` field. -/
private theorem james_norm_attainment_restrictScalars
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (h : ∀ f : StrongDual 𝕜 E,
      ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖) :
    let _ := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ f : StrongDual ℝ E,
      ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ := by
  dsimp only
  let _ := NormedSpace.restrictScalars ℝ 𝕜 E
  intro f
  obtain ⟨y, hy, hfy⟩ := h f.extendRCLike
  set z : 𝕜 := f.extendRCLike y with hz
  by_cases hz0 : z = 0
  · have hf0 : ‖f‖ = 0 := by
      rw [← StrongDual.norm_extendRCLike (𝕜 := 𝕜) f, ← hfy, hz0, norm_zero]
    exact ⟨0, by simp, by simp [hf0]⟩
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set u : 𝕜 := (↑(‖z‖⁻¹) : 𝕜) * starRingEnd 𝕜 z with hu
    have hu_norm : ‖u‖ = 1 := by
      rw [hu, norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_pos (inv_pos.mpr hzpos), inv_mul_cancel₀ hzpos.ne']
    refine ⟨u • y, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, hu_norm, one_mul]
      exact mem_closedBall_zero_iff.mp hy
    · have hgz : f.extendRCLike (u • y) = (↑‖z‖ : 𝕜) := by
        rw [map_smul, smul_eq_mul, ← hz, hu, mul_assoc, RCLike.conj_mul,
          pow_two, ← RCLike.ofReal_mul]
        norm_cast
        rw [← mul_assoc, inv_mul_cancel₀ hzpos.ne', one_mul]
      rw [← StrongDual.re_extendRCLike_apply (𝕜 := 𝕜) f (u • y), hgz,
        RCLike.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), hfy,
        StrongDual.norm_extendRCLike (𝕜 := 𝕜) f]

/-- Surjectivity of the canonical map into the real bidual implies surjectivity over an
`RCLike` field after restricting scalars. -/
private theorem james_surjective_inclusionInDoubleDual_of_restrictScalars
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hreal :
      let _ := NormedSpace.restrictScalars ℝ 𝕜 E
      Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E) := by
  let _ := NormedSpace.restrictScalars ℝ 𝕜 E
  intro Φ
  let Ψ : StrongDual ℝ (StrongDual ℝ E) :=
    RCLike.reCLM.comp
      ((Φ.restrictScalars ℝ).comp
        (StrongDual.extendRCLikeL (𝕜 := 𝕜) (F := E)).toContinuousLinearMap)
  obtain ⟨x, hx⟩ := hreal Ψ
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  have hre (g : StrongDual 𝕜 E) : RCLike.re (Φ g) = RCLike.re (g x) := by
    let gr : StrongDual ℝ E := RCLike.reCLM.comp (g.restrictScalars ℝ)
    have hext : gr.extendRCLike = g := by
      apply ContinuousLinearMap.ext
      intro y
      apply RCLike.ext_iff.mpr
      constructor
      · rw [StrongDual.re_extendRCLike_apply]
        rfl
      · rw [StrongDual.im_extendRCLike_apply]
        change -RCLike.re (g ((RCLike.I : 𝕜) • y)) = RCLike.im (g y)
        rw [map_smul, smul_eq_mul, RCLike.I_mul_re, neg_neg]
    have hΨ : Ψ gr = gr x := by
      rw [← NormedSpace.dual_def ℝ E x gr, hx]
    rw [show Ψ gr = RCLike.re (Φ gr.extendRCLike) by rfl, hext] at hΨ
    exact hΨ
  apply RCLike.ext_iff.mpr
  constructor
  · rw [NormedSpace.dual_def]
    exact (hre f).symm
  · have hI := hre ((RCLike.I : 𝕜) • f)
    have hI' : -RCLike.im (Φ f) = -RCLike.im (f x) := by
      calc
        -RCLike.im (Φ f) = RCLike.re (RCLike.I * Φ f) :=
          (RCLike.I_mul_re _).symm
        _ = RCLike.re (Φ ((RCLike.I : 𝕜) • f)) := by
          rw [map_smul, smul_eq_mul]
        _ = RCLike.re (((RCLike.I : 𝕜) • f) x) := hI
        _ = RCLike.re (RCLike.I * f x) := by rfl
        _ = -RCLike.im (f x) := RCLike.I_mul_re _
    rw [NormedSpace.dual_def]
    exact (neg_injective hI').symm

private theorem james_norm_attainment_of_surjective
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hJ : Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E))
    (f : StrongDual 𝕜 E) :
    ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ := by
  by_cases hf : f = 0
  · subst hf
    exact ⟨0, by simp, by simp⟩
  · have hfnorm : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    obtain ⟨Φ, hΦnorm, hΦeval⟩ := exists_dual_vector 𝕜 f hfnorm
    obtain ⟨x, hx⟩ := hJ Φ
    refine ⟨x, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      have hxnorm : ‖x‖ = ‖Φ‖ := by
        rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x]
        exact congrArg norm hx
      rw [hxnorm, hΦnorm]
    · have hfx : f x = Φ f := by
        rw [← NormedSpace.dual_def 𝕜 E x f, hx]
      rw [hfx, hΦeval, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg f)]

/--
**James' reflexivity theorem.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$ be a
Banach space over $\mathbb{K}$. The canonical embedding of $E$ into its bidual $E^{**}$ is
surjective if and only if every continuous linear functional $f \colon E \to \mathbb{K}$ attains
its norm on the closed unit ball, that is, there is $x \in E$ with $\|x\| \le 1$ and
$|f(x)| = \|f\|$.

Proof: The reverse implication uses the general real James convex-block argument, with Goldstine
approximation and weak-star cluster hulls. Restriction of scalars transfers the result from real
scalars to $\mathbb{K}$.

Proves `Wanted` entry `james_reflexivity`.

Source:
R. C. James, Reflexivity and the Supremum of Linear Functionals, Ann. of Math. 66 (1957),
DOI 10.2307/1970122; Bourbaki form; Lean states `RCLike` Banach case with norm-attainment
equivalence for reflexivity.
-/
theorem james_reflexivity
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)
      ↔ ∀ f : StrongDual 𝕜 E, ∃ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ = ‖f‖ := by
  constructor
  · exact fun hJ f ↦ james_norm_attainment_of_surjective hJ f
  · intro hattain
    apply james_surjective_inclusionInDoubleDual_of_restrictScalars
    let _ := NormedSpace.restrictScalars ℝ 𝕜 E
    have hattainReal : ∀ f : StrongDual ℝ E,
        ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
      simpa only [mem_closedBall_zero_iff] using james_norm_attainment_restrictScalars hattain
    by_contra hJ
    obtain ⟨x, f, θ, hθ, hx, hf, htri, hpointwise⟩ :=
      james_triangular_sequences_of_not_surjective hJ
    obtain ⟨δ, hδ, hnorm⟩ := james_clusterHull_norm_eq f hf
    let x' : ℕ → E := x ∘ δ
    let f' : ℕ → StrongDual ℝ E := f ∘ δ
    let u : ℕ → WeakDual ℝ E := StrongDual.toWeakDual ∘ f'
    have hu (n : ℕ) : u n ∈ jamesDualBall E := by
      exact mem_closedBall_zero_iff.mpr (hf (δ n))
    obtain ⟨fLimW, hfLimW⟩ := (james_clusterHull_nonempty_compact u hu).1
    let fLim : StrongDual ℝ E := WeakDual.toStrongDual fLimW
    have hx' (n : ℕ) : ‖x' n‖ ≤ 1 := hx (δ n)
    have hf' (n : ℕ) : ‖f' n‖ ≤ 1 := hf (δ n)
    have htri' (j n : ℕ) (hjn : j < n) : θ < f' j (x' n) :=
      htri (δ j) (δ n) (hδ hjn)
    have hpointwise' (j : ℕ) : Tendsto (fun n ↦ f' n (x' j)) atTop (nhds 0) := by
      exact (hpointwise (δ j)).comp hδ.tendsto_atTop
    have hfLimZero (j : ℕ) : fLim (x' j) = 0 := by
      exact james_clusterHull_apply_eq_zero f' (x' j) (hpointwise' j) fLimW hfLimW
    obtain ⟨g, hg, hselect⟩ :=
      james_select_convex_blocks x' f' fLim θ hθ hx' htri' hfLimZero
    have hgNorm (n : ℕ) : ‖g n‖ ≤ 1 := by
      apply mem_closedBall_zero_iff.mp
      apply (convexHull_min (t := closedBall (0 : StrongDual ℝ E) 1) ?_
        (convex_closedBall 0 1)) (hg n)
      rintro z ⟨k, _, rfl⟩
      exact mem_closedBall_zero_iff.mpr (hf' k)
    let gw : ℕ → WeakDual ℝ E := StrongDual.toWeakDual ∘ g
    have hgwBall (n : ℕ) : gw n ∈ jamesDualBall E :=
      mem_closedBall_zero_iff.mpr (hgNorm n)
    have hgwBlocks (n : ℕ) : gw n ∈ convexHull ℝ (u '' Set.Ici n) := by
      change StrongDual.toWeakDual (g n) ∈ convexHull ℝ (u '' Set.Ici n)
      apply (convexHull_min
        (t := StrongDual.toWeakDual ⁻¹' convexHull ℝ (u '' Set.Ici n)) ?_ ?_) (hg n)
      · rintro z ⟨k, hk, rfl⟩
        exact subset_convexHull ℝ (u '' Set.Ici n) ⟨k, hk, rfl⟩
      · exact (convex_convexHull ℝ _).linear_preimage
          StrongDual.toWeakDual.toLinearMap
    have hgwmap : Filter.map gw atTop ≤ Filter.principal (jamesDualBall E) := by
      rw [Filter.le_principal_iff, Filter.mem_map]
      exact Filter.Eventually.of_forall hgwBall
    obtain ⟨gLimW, hgLimBall, hgLimCluster⟩ :=
      (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) 1).exists_mapClusterPt hgwmap
    have hgLimK : gLimW ∈ jamesClusterHull u :=
      james_clusterSet_convexBlocks_subset u gw hu hgwBlocks hgLimCluster
    let gLim : StrongDual ℝ E := WeakDual.toStrongDual gLimW
    have hθone : θ < 1 := by
      calc
        θ < f 0 (x 1) := htri 0 1 Nat.zero_lt_one
        _ ≤ ‖f 0 (x 1)‖ := Real.le_norm_self _
        _ ≤ ‖f 0‖ * ‖x 1‖ := (f 0).le_opNorm (x 1)
        _ ≤ 1 * 1 := mul_le_mul (hf 0) (hx 1) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hfLimNorm : ‖fLim‖ ≤ 1 := by
      change ‖WeakDual.toStrongDual fLimW‖ ≤ 1
      exact mem_closedBall_zero_iff.mp
        (james_clusterHull_subset_dualBall u hu hfLimW)
    have hgLimNorm : ‖gLim‖ ≤ 1 := by
      exact mem_closedBall_zero_iff.mp hgLimBall
    have hgSpan (n : ℕ) : g n ∈ Submodule.span ℝ (Set.range f) := by
      apply (convexHull_min (t := (Submodule.span ℝ (Set.range f) :
        Set (StrongDual ℝ E))) ?_ (Submodule.convex _)) (hg n)
      rintro z ⟨k, _, rfl⟩
      apply Submodule.subset_span
      exact ⟨δ k, rfl⟩
    have hfLimK : fLimW ∈
        jamesClusterHull (StrongDual.toWeakDual ∘ f ∘ δ) := by
      simpa only [u, f', Function.comp_assoc] using hfLimW
    have hgLimK' : gLimW ∈
        jamesClusterHull (StrongDual.toWeakDual ∘ f ∘ δ) := by
      simpa only [u, f', Function.comp_assoc] using hgLimK
    have hpartialNorm (n : ℕ) :
        ‖∑ i ∈ Finset.range n, (θ / 32) ^ i • (g i - fLim)‖ =
          ‖∑ i ∈ Finset.range n, (θ / 32) ^ i • (g i - gLim)‖ := by
      let y : StrongDual ℝ E := ∑ i ∈ Finset.range n, (θ / 32) ^ i • g i
      let a : ℝ := ∑ i ∈ Finset.range n, (θ / 32) ^ i
      have hy : y ∈ Submodule.span ℝ (Set.range f) := by
        apply Submodule.sum_mem
        intro i hi
        exact Submodule.smul_mem _ _ (hgSpan i)
      have hid := hnorm fLimW hfLimK gLimW hgLimK' y
        (Submodule.le_topologicalClosure _ hy) a
      rw [james_sum_smul_sub, james_sum_smul_sub]
      simpa only [y, a, fLim, gLim] using hid
    have hinc' (n : ℕ) :
        ‖∑ i ∈ Finset.range n,
            (θ / 32) ^ i • (g i - WeakDual.toStrongDual gLimW)‖ +
            (θ / 32) ^ n * (θ / 2) <
          ‖∑ i ∈ Finset.range (n + 1),
            (θ / 32) ^ i • (g i - WeakDual.toStrongDual gLimW)‖ := by
      simpa only [gLim, ← hpartialNorm n, ← hpartialNorm (n + 1)] using hselect n
    exact james_geometric_series_contradiction hattainReal g gLimW θ hθ hθone
      hgNorm hgLimNorm hinc' hgLimCluster

end MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted
