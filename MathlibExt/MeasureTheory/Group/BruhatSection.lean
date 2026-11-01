/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_
translate_eq_one_of_subset_mul.lean`
and
`P2M/Sol/S_MeasureTheory_exists_hasCompactSupport_integral_subgroup_
translate_eq_one_of_subset_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

open scoped Pointwise Topology

namespace BruhatSectionAux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Average

variable (T : Subgroup G) [MeasurableSpace T] [BorelSpace T]
  (τ : MeasureTheory.Measure T)

omit [MeasurableSpace ↥T] [BorelSpace ↥T] in
private theorem isClosedEmbedding_val_mul (hT : IsClosed (T : Set G)) (x : G) :
    Topology.IsClosedEmbedding fun t : T => (t : G) * x :=
  (Homeomorph.mulRight x).isClosedEmbedding.comp hT.isClosedEmbedding_subtypeVal

private noncomputable def avg (ψ : G → ℝ) (x : G) : ℝ :=
  ∫ t : T, ψ ((t : G) * x) ∂τ

variable {T τ}

private theorem avg_mul [τ.IsMulRightInvariant] (ψ : G → ℝ) (t₀ : T) (x : G) :
    avg T τ ψ ((t₀ : G) * x) = avg T τ ψ x := by
  unfold avg
  have hcomp : (fun t : T => ψ ((t : G) * ((t₀ : G) * x))) =
      fun t : T => (fun s : T => ψ ((s : G) * x)) (t * t₀) := by
    funext t
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [hcomp, MeasureTheory.integral_mul_right_eq_self
    (fun s : T => ψ ((s : G) * x)) t₀]

omit [BorelSpace T] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem avg_nonneg {ψ : G → ℝ} (hψ : ∀ x, 0 ≤ ψ x) (x : G) :
    0 ≤ avg T τ ψ x :=
  MeasureTheory.integral_nonneg fun _ => hψ _

private theorem avg_pos [LocallyCompactSpace G] (hT : IsClosed (T : Set G))
    [τ.IsOpenPosMeasure] [MeasureTheory.IsFiniteMeasureOnCompacts τ] {ψ : G → ℝ}
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ : ∀ x, 0 ≤ ψ x) {x : G}
    (hx : ψ x ≠ 0) : 0 < avg T τ ψ x := by
  unfold avg
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (1 : T)) ?_ ?_ (fun t => hψ _) ?_
  · exact hψc.comp (isClosedEmbedding_val_mul T hT x).continuous
  · exact hψs.comp_isClosedEmbedding (isClosedEmbedding_val_mul T hT x)
  · simpa using hx

private theorem continuous_avg [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (hT : IsClosed (T : Set G))
    [MeasureTheory.IsLocallyFiniteMeasure τ] {ψ : G → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) : Continuous (avg T τ ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hN, hNx₀⟩ := exists_compact_mem_nhds x₀
  set s : Set T := ((↑) : T → G) ⁻¹' (tsupport ψ * N⁻¹) with hs
  have hsc : IsCompact s :=
    hT.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hψs.isCompact.mul hN.inv)
  have hF : Continuous (fun p : G × T => ψ ((p.2 : G) * p.1)) :=
    hψc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have hcont : Continuous fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    continuous_parametric_integral_of_continuous
      (f := fun x (t : T) => ψ ((t : G) * x)) (by exact hF) hsc
  have heq : ∀ x ∈ N, avg T τ ψ x = ∫ t in s, ψ ((t : G) * x) ∂τ := by
    intro x hx
    unfold avg
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      fun t ht => ?_).symm
    by_contra hne
    apply ht
    rw [hs, Set.mem_preimage]
    have h1 : (t : G) * x ∈ tsupport ψ :=
      subset_tsupport ψ (Function.mem_support.mpr hne)
    refine Set.mem_mul.mpr ⟨(t : G) * x, h1, x⁻¹, Set.inv_mem_inv.mpr hx, ?_⟩
    simp
  have hev : avg T τ ψ =ᶠ[𝓝 x₀] fun x => ∫ t in s, ψ ((t : G) * x) ∂τ :=
    Filter.eventually_of_mem hNx₀ heq
  exact (hcont.continuousAt.congr hev.symm)

end Average

private theorem main [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : MeasureTheory.Measure T)
    [τ.IsHaarMeasure] [τ.IsMulRightInvariant] {E C : Set G} (hC : IsCompact C)
    (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 := by
  obtain ⟨ψ, hψC, -, hψs, hψ01⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  have _ : LocallyCompactSpace T :=
    hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  have hΨc : Continuous (avg T τ ψ) := continuous_avg hT hψc hψs
  refine ⟨fun x => ψ x / avg T τ ψ x, fun x => div_nonneg (hψ0 x) (avg_nonneg hψ0 x),
    hψc.measurable.div hΨc.measurable, ?_, ?_⟩
  · refine hψs.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])
  · intro x hx
    obtain ⟨t₀, ht₀, c, hc, rfl⟩ := Set.mem_mul.mp (hE hx)
    have hpos : 0 < avg T τ ψ (t₀ * c) := by
      have havg := avg_mul (T := T) (τ := τ) ψ ⟨t₀, ht₀⟩ c
      simp only at havg
      rw [havg]
      exact avg_pos hT hψc hψs hψ0 (by rw [hψC hc]; simp)
    have hinv : ∀ t : T, avg T τ ψ ((t : G) * (t₀ * c)) = avg T τ ψ (t₀ * c) :=
      fun t => avg_mul ψ t (t₀ * c)
    simp_rw [hinv]
    rw [MeasureTheory.integral_div, div_eq_one_iff_eq hpos.ne']
    rfl

end BruhatSectionAux

namespace MeasureTheory

/-- A Bruhat section: given a closed subgroup `T` of a locally compact group
and a set `E` contained in `T • C` for compact `C`, there is a compactly
supported nonnegative measurable function `w` whose integral over each
`T`-translate meeting `E` equals `1`.

This is the standard tool for unfolding integrals over homogeneous spaces:
it is used to build sections of quotient maps `G → G ⧸ T`, to average
functions over subgroups in automorphic forms, and to construct
partitions of unity subordinate to subgroup translates. -/
theorem exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (T : Subgroup G) (hT : IsClosed (T : Set G))
    [MeasurableSpace T] [BorelSpace T] (τ : Measure T) [τ.IsHaarMeasure]
    [τ.IsMulRightInvariant] {E C : Set G} (hC : IsCompact C)
    (hE : E ⊆ (T : Set G) * C) :
    ∃ w : G → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
      ∀ x ∈ E, ∫ t : T, w ((t : G) * x) ∂τ = 1 :=
  BruhatSectionAux.main T hT τ hC hE

end MeasureTheory
