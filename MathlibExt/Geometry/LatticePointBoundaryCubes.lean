/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.ConstMulAction
public import MathlibExt.Geometry.LatticePointCubeSandwich
public import MathlibExt.Geometry.LipschitzImageCubeCount
public import MathlibExt.Topology.Connected.Frontier

/-!
# Boundary cubes lie in Lipschitz image cube sets (ATLAS N385, prerequisite)

Source: `v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean`, lines 509--608
at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.
See `atlas-lean` blob `facebookresearch/atlas-lean` at that revision for context.

This module ports only the boundary-cube inclusion and the natural-cardinality
bound (source `boundary_cubes_bound`, lines 509--608). It excludes the real
sandwich, the final asymptotic, and everything at source lines 609 onward.

Source-to-API map (all within lines 509--608 above):
- source `innerCubeSet_subset_outerCubeSet` prerequisite is reused from
  `LatticePointCubeSandwich.innerCubeSet_subset_outerCubeSet`, not duplicated;
- source `preconnected_frontier_inter` is reused from
  `IsPreconnected.inter_frontier_nonempty_of_inter_compl`, not duplicated;
- source per-chart set `bdry i` is reused from
  `LipschitzImageCubeCount.integerCubeSet (maps i) t`, not duplicated;
- source difference inclusion (`hDiff`) becomes
  `LatticePointBoundaryCubes.outer_diff_inner_subset_iUnion_integerCubeSet`;
- source cardinality computation (final `calc`) becomes
  `LatticePointBoundaryCubes.card_outer_le_card_inner_add_sum`.

The source hypotheses `hn : 0 < n` and `hS : MeasurableSet S` are unused and
do not appear here; the parameter dimension is generalized from source `n - 1`
to an independent `d`. No sign or nonvanishing hypothesis on `t` is needed.

This file is a prerequisite stage for N385, not the full N385 target.
-/

@[expose] public section

open Set Topology LatticePointCubeSandwich LipschitzImageCubeCount

namespace LatticePointBoundaryCubes

/-- **Boundary cubes meet the dilated frontier charts.** Let $S \subseteq \mathbb{R}^n$, let
$f_1, \dots, f_m : [0,1]^d \to \mathbb{R}^n$ be maps whose ranges together cover the frontier of
$S$, and let $t$ be a real number. For $v \in \mathbb{Z}^n$ write $Q_v$ for the half-open unit
cube $\prod_i [v_i, v_i + 1)$. If $v$ lies in the outer cube set of $S$ at scale $t$ (some
$x \in Q_v$ has $x / t \in S$, coordinatewise, with $x / 0 = 0$) but not in the inner cube set
(not every $x \in Q_v$ has $x / t \in S$), then $v$ lies in the integer cube set of some $f_i$ at
scale $t$: there is $y \in [0,1]^d$ with $t f_i(y) \in Q_v$. -/
theorem outer_diff_inner_subset_iUnion_integerCubeSet
    {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ} :
    outerCubeSet S t \ innerCubeSet S t ⊆
      ⋃ i, integerCubeSet (maps i) t := by
  by_cases ht : t = 0
  · subst ht
    intro v ⟨hv_outer, hv_not_inner⟩
    rw [mem_outerCubeSet_iff] at hv_outer
    rw [mem_innerCubeSet_iff] at hv_not_inner
    push Not at hv_not_inner
    obtain ⟨x, -, hx_in_S⟩ := hv_outer
    obtain ⟨x', -, hx'_not_S⟩ := hv_not_inner
    have hzero : (fun i => x i / (0 : ℝ)) = fun _ => 0 := by
      funext i
      exact div_zero _
    have hzero' : (fun i => x' i / (0 : ℝ)) = fun _ => 0 := by
      funext i
      exact div_zero _
    rw [hzero] at hx_in_S
    rw [hzero'] at hx'_not_S
    exact absurd hx_in_S hx'_not_S
  · intro v ⟨hv_outer, hv_not_inner⟩
    rw [mem_outerCubeSet_iff] at hv_outer
    rw [mem_innerCubeSet_iff] at hv_not_inner
    push Not at hv_not_inner
    obtain ⟨x, hx_cube, hx_in_S⟩ := hv_outer
    obtain ⟨x', hx'_cube, hx'_not_S⟩ := hv_not_inner
    have hcube_preconn : IsPreconnected (integerUnitCube v) := by
      have heq : integerUnitCube v =
          Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1)) := by
        ext y
        simp only [mem_integerUnitCube_iff, Set.mem_pi, Set.mem_univ,
          Set.mem_Ico, true_implies]
      rw [heq]
      exact (convex_pi (fun i _ => convex_Ico _ _)).isPreconnected
    set T : Set (Fin n → ℝ) := {y | (fun i => y i / t) ∈ S} with hT_def
    have hx_T : x ∈ integerUnitCube v ∩ T := ⟨hx_cube, hx_in_S⟩
    have hx'_Tc : x' ∈ integerUnitCube v ∩ Tᶜ := ⟨hx'_cube, hx'_not_S⟩
    obtain ⟨z, hz_cube, hz_frontier⟩ :=
      hcube_preconn.inter_frontier_nonempty_of_inter_compl
        ⟨x, hx_T⟩ ⟨x', hx'_Tc⟩
    have hz_on_frontier : (fun i => z i / t) ∈ frontier S := by
      have ht_inv_ne : t⁻¹ ≠ 0 := inv_ne_zero ht
      set φ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
        Homeomorph.smulOfNeZero t⁻¹ ht_inv_ne with φ_def
      have hT_eq : T = φ ⁻¹' S := by
        ext y
        simp only [hT_def, Set.mem_ofPred_eq, Set.mem_preimage, φ_def,
          Homeomorph.smulOfNeZero_apply]
        constructor
        · intro h
          convert h using 1
          ext i
          simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
        · intro h
          convert h using 1
          ext i
          simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
      rw [hT_eq, ← φ.preimage_frontier] at hz_frontier
      simp only [Set.mem_preimage, φ_def,
        Homeomorph.smulOfNeZero_apply] at hz_frontier
      convert hz_frontier using 1
      ext i
      simp [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    have hmem := hCover hz_on_frontier
    rw [Set.mem_iUnion] at hmem
    obtain ⟨i, hi⟩ := hmem
    rw [Set.mem_range] at hi
    obtain ⟨y, hy_eq⟩ := hi
    rw [Set.mem_iUnion]
    refine ⟨i, y, fun j => ?_⟩
    have hjz : (maps i y) j = z j / t := congr_fun hy_eq j
    have hzj := (mem_integerUnitCube_iff.mp hz_cube) j
    constructor
    · have hmul : t * (z j / t) = z j := by field_simp
      rw [hjz, hmul]
      exact hzj.1
    · have hmul : t * (z j / t) = z j := by field_simp
      rw [hjz, hmul]
      exact hzj.2

/-- **Counting outer cubes by inner cubes and boundary charts.** Let $S \subseteq \mathbb{R}^n$,
let $f_1, \dots, f_m : [0,1]^d \to \mathbb{R}^n$ be maps whose ranges together cover the frontier
of $S$, and let $t$ be a real number. Let $O$ and $I$ be the outer and inner cube sets of $S$ at
scale $t$: the $v \in \mathbb{Z}^n$ for which some, respectively every, point $x$ of the half-open
unit cube $\prod_i [v_i, v_i + 1)$ has $x / t \in S$ (coordinatewise, with $x / 0 = 0$). Let $C_i$
be the integer cube set of $f_i$ at scale $t$: the $v$ whose half-open unit cube contains
$t f_i(y)$ for some $y \in [0,1]^d$. If $O$ and every $C_i$ are finite, then
$|O| \le |I| + \sum_{i=1}^m |C_i|$. -/
theorem card_outer_le_card_inner_add_sum
    {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ}
    (hFinOuter : (outerCubeSet S t).Finite)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    Nat.card (outerCubeSet S t) ≤
      Nat.card (innerCubeSet S t) +
        ∑ i, Nat.card (integerCubeSet (maps i) t) := by
  have hInner : innerCubeSet S t ⊆ outerCubeSet S t :=
    innerCubeSet_subset_outerCubeSet S t
  have hFinUnion : (⋃ i, integerCubeSet (maps i) t).Finite :=
    Set.finite_iUnion hFinMaps
  have hDiff : outerCubeSet S t \ innerCubeSet S t ⊆
      ⋃ i, integerCubeSet (maps i) t :=
    outer_diff_inner_subset_iUnion_integerCubeSet S maps hCover
  have hnc : (outerCubeSet S t).ncard ≤ (innerCubeSet S t).ncard +
      ∑ i, (integerCubeSet (maps i) t).ncard := by
    calc (outerCubeSet S t).ncard
        = (outerCubeSet S t \ innerCubeSet S t).ncard + (innerCubeSet S t).ncard :=
          (Set.ncard_sdiff_add_ncard_of_subset hInner hFinOuter).symm
      _ = (innerCubeSet S t).ncard + (outerCubeSet S t \ innerCubeSet S t).ncard :=
          add_comm _ _
      _ ≤ (innerCubeSet S t).ncard + (⋃ i, integerCubeSet (maps i) t).ncard :=
          Nat.add_le_add_left (Set.ncard_le_ncard hDiff hFinUnion) _
      _ ≤ (innerCubeSet S t).ncard + ∑ i, (integerCubeSet (maps i) t).ncard :=
          Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype _) _
  simp only [Nat.card_coe_set_eq]
  exact hnc

end LatticePointBoundaryCubes
