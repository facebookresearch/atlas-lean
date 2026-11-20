/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

open Metric Set Topology
open scoped UniformConvergence

namespace StatMech.FrontierA



theorem holomorphicFamily_equicontinuousOn_of_compactBounded
    {ι : Type*} (F : ι → ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ U → EquicontinuousOn F K := by
  intro K _hK hKU z hz
  apply EquicontinuousAt.equicontinuousWithinAt
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z (hKU hz)
  let R : ℝ := r / 2
  have hR : 0 < R := div_pos hr zero_lt_two
  have hclosedU : closedBall z R ⊆ U := by
    exact (closedBall_subset_ball (by dsimp [R]; linarith)).trans hrU
  obtain ⟨C, hC⟩ := hbounded (closedBall z R)
    (isCompact_closedBall z R) hclosedU
  let L : ℝ := (2 * C) / R
  apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : ℂ => L * dist w z)
  · have hcontinuous : ContinuousAt (fun w : ℂ => L * dist w z) z := by
      fun_prop
    simpa using hcontinuous.tendsto
  · filter_upwards [ball_mem_nhds z hR] with w hw
    intro i
    have hdiff : DifferentiableOn ℂ (F i) (ball z R) :=
      (hF i).mono ((ball_subset_closedBall.trans hclosedU))
    have hmaps : MapsTo (F i) (ball z R) (closedBall (F i z) (2 * C)) := by
      intro y hy
      rw [mem_closedBall]
      calc
        dist (F i y) (F i z) ≤ ‖F i y‖ + ‖F i z‖ := dist_le_norm_add_norm _ _
        _ ≤ C + C := add_le_add
          (hC i y (ball_subset_closedBall hy))
          (hC i z (mem_closedBall_self hR.le))
        _ = 2 * C := by ring
    have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      hdiff hmaps hw
    simpa only [L, dist_comm] using hschwarz





theorem holomorphicFamily_restrictionClosure_compact
    {ι : Type*} (F : ι → ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (closure (Set.range (fun i =>
      UniformFun.ofFun (fun z : K => F i z)))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ι → K →ᵤ ℂ := fun i => UniformFun.ofFun (fun z => F i z)
  let S : Set (K →ᵤ ℂ) := Set.range f
  let sets : Set (Set K) := {Set.univ}
  let eval : (K →ᵤ ℂ) → K → ℂ := UniformFun.toFun
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun sets ∘ eval) := by
    let e := UniformOnFun.uniformEquivUniformFun ℂ sets
      (show Set.univ ∈ sets by simp [sets])
    change IsClosedEmbedding e.symm
    exact e.symm.toHomeomorph.isClosedEmbedding
  have hEqK : EquicontinuousOn F K :=
    holomorphicFamily_equicontinuousOn_of_compactBounded
      F U hU hF hbounded K hK hKU
  have hSEq : EquicontinuousOn (eval ∘ ((↑) : S → K →ᵤ ℂ)) Set.univ := by
    rw [equicontinuousOn_univ]
    have hrestrict : Equicontinuous (K.restrict ∘ F) :=
      (equicontinuous_restrict_iff F).2 hEqK
    let pick : S → ι := fun q => Classical.choose q.property
    have hpick (q : S) : f (pick q) = q := Classical.choose_spec q.property
    have hsub := hrestrict.comp pick
    convert hsub using 1
    funext q z
    have h := congrArg (fun a : K →ᵤ ℂ => UniformFun.toFun a z) (hpick q)
    simpa only [f, eval, Function.comp_apply] using h.symm
  obtain ⟨C, hC⟩ := hbounded K hK hKU
  have hpoint : ∀ T ∈ sets, ∀ z ∈ T,
      ∃ Q : Set ℂ, IsCompact Q ∧ ∀ q ∈ S, eval q z ∈ Q := by
    intro T hT z _hz
    have hTuniv : T = Set.univ := by
      simpa only [sets, Set.mem_singleton_iff] using hT
    subst T
    refine ⟨closedBall 0 (max C 0), isCompact_closedBall 0 (max C 0), ?_⟩
    intro q hq
    obtain ⟨i, rfl⟩ := hq
    rw [mem_closedBall]
    simpa only [eval, f, dist_zero_right] using
      (hC i z z.property).trans (le_max_left C 0)
  have hcompact : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := sets)
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact isCompact_univ)
      hclosed
      (fun T hT => by
        have : T = Set.univ := by
          simpa only [sets, Set.mem_singleton_iff] using hT
        subst T
        exact hSEq)
      hpoint
  simpa only [S, f] using hcompact



theorem holomorphicFamily_uniformSubsequenceOn_compact
    {ι : Type*} (F : ι → ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℕ → ι) :
    ∃ (g : K → ℂ) (ψ : ℕ → ℕ), StrictMono ψ ∧
      TendstoUniformly
        (fun n (z : K) => F (u (ψ n)) z) g Filter.atTop := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ℕ → K →ᵤ ℂ := fun n => UniformFun.ofFun (fun z => F (u n) z)
  let S : Set (K →ᵤ ℂ) := Set.range f
  have hcompact : IsCompact (closure S) := by
    simpa only [S, f] using
      (holomorphicFamily_restrictionClosure_compact
        (fun n => F (u n)) U hU (fun n => hF (u n))
        (fun K hK hKU => by
          obtain ⟨C, hC⟩ := hbounded K hK hKU
          exact ⟨C, fun n => hC (u n)⟩)
        K hK hKU)
  obtain ⟨g, _hg, ψ, hψ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (show f n ∈ S from ⟨n, rfl⟩))
  refine ⟨UniformFun.toFun g, ψ, hψ, ?_⟩
  have huniform := UniformFun.tendsto_iff_tendstoUniformly.mp hlim
  refine (tendstoUniformly_congr
    (F := UniformFun.toFun ∘ f ∘ ψ)
    (F' := fun n (z : K) => F (u (ψ n)) z)
    (p := (Filter.atTop : Filter ℕ)) ?_).mp huniform
  exact Filter.Eventually.of_forall fun n => by
    funext z
    rfl

end StatMech.FrontierA
