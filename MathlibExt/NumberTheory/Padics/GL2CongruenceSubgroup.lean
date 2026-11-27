/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup.lean`,
`Theorems/Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.lean`,
`Theorems/Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup.lean`,
`Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean`,
`Definitions/Def_LocalLanglands_LocalHeckeInstance.lean`,
`Definitions/Def_LocalLanglands_IntegralSubgroupCompact.lean`,
`Definitions/Def_LocalLanglands_IntegralSubgroupOpen.lean`,
`P2M/Sol/S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup.lean`,
`P2M/Sol/S_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup.lean` and
`P2M/Sol/S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup.lean`
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

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

open scoped Topology

namespace Padic

variable (p : ℕ) [Fact p.Prime]

private theorem padic_norm_add_le_of_le {x y : ℚ_[p]} {ε : ℝ} (hx : ‖x‖ ≤ ε) (hy : ‖y‖ ≤ ε) :
    ‖x + y‖ ≤ ε :=
  le_trans (Padic.nonarchimedean _ _) (max_le hx hy)

private theorem norm_matrix_one_entry_le_one (i j : Fin 2) :
    ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h]

private theorem norm_entry_le_one_of_sub_entry_le {A : Matrix (Fin 2) (Fin 2) ℚ_[p]} {ε : ℝ}
    (hε : ε ≤ 1) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ ε) (i j : Fin 2) : ‖A i j‖ ≤ 1 := by
  have h : A i j = (A - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
    rw [Matrix.sub_apply]
    ring
  rw [h]
  exact padic_norm_add_le_of_le p (le_trans (hA i j) hε) (norm_matrix_one_entry_le_one p i j)

private theorem norm_matrix_mul_entry_le {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]} {a b : ℝ}
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin 2) :
    ‖(A * B) i j‖ ≤ a * b := by
  have ha0 : (0 : ℝ) ≤ a := le_trans (norm_nonneg _) (hA i j)
  have hb0 : (0 : ℝ) ≤ b := le_trans (norm_nonneg _) (hB i j)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_) <;>
  · rw [norm_mul]
    exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) ha0


private theorem radius_pos (n : ℕ) : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  exact zpow_pos hp0 _

private theorem radius_le_one (n : ℕ) : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact pow_le_one₀ (inv_nonneg.mpr (le_of_lt (lt_trans one_pos hp1))) (le_of_lt hpinv)

private theorem radius_antitone {m n : ℕ} (h : m ≤ n) :
    (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast le_of_lt (Fact.out : p.Prime).one_lt
  apply zpow_le_zpow_right₀ hp1
  omega

private theorem radius_lt_one {n : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ (-(n : ℤ)) < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp1
  refine lt_of_le_of_lt (radius_antitone p hn) ?_
  rw [Nat.cast_one, zpow_neg, zpow_one]
  exact hpinv



/-- The integral subgroup of `GL(2, K)`: matrices coming from `GL(2, R)` under
an algebra map `R → K`. -/
public def integralSubgroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :
    Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range

theorem mem_integralSubgroup_iff {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    {x : GL (Fin 2) K} :
    x ∈ integralSubgroup R K ↔
      ∃ y : GL (Fin 2) R, Matrix.GeneralLinearGroup.map (algebraMap R K) y = x :=
  Iff.rfl


lemma exists_entry_eq_of_mem_integralSubgroup {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] {x : GL (Fin 2) K}
    (hx : x ∈ integralSubgroup R K) (i j : Fin 2) :
    ∃ r : R, algebraMap R K r = (x : Matrix (Fin 2) (Fin 2) K) i j := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(y : Matrix (Fin 2) (Fin 2) R) i j, rfl⟩


theorem mem_integralSubgroup_iff_entries_mem {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    (g : GL (Fin 2) K) :
    g ∈ integralSubgroup R K
      ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ Set.range (algebraMap R K))
        ∧ (∀ i j, ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j
            ∈ Set.range (algebraMap R K)) := by
  constructor
  · intro hg
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · obtain ⟨r, hr⟩ := exists_entry_eq_of_mem_integralSubgroup hg i j
      exact ⟨r, hr⟩
    · obtain ⟨r, hr⟩ :=
        exists_entry_eq_of_mem_integralSubgroup (inv_mem hg) i j
      exact ⟨r, hr⟩
  · rintro ⟨hg, hginv⟩
    set A : Matrix (Fin 2) (Fin 2) R := fun i j => (hg i j).choose with hA
    set B : Matrix (Fin 2) (Fin 2) R := fun i j => (hginv i j).choose with hB
    have hAspec : ∀ i j, algebraMap R K (A i j) = (g : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hg i j).choose_spec
    have hBspec : ∀ i j,
        algebraMap R K (B i j) = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j :=
      fun i j => (hginv i j).choose_spec
    have hmapA : (A.map (algebraMap R K)) = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hAspec i j
    have hmapB : (B.map (algebraMap R K))
        = ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hBspec i j
    have hmatinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) R =>
        M.map (algebraMap R K) := fun M M' hMM' => by
      ext i j
      apply hinj
      have := congrFun (congrFun hMM' i) j
      simpa [Matrix.map_apply] using this
    have hAB : A * B = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.mul_inv g)
    have hBA : B * A = 1 := by
      apply hmatinj
      simp only [Matrix.map_mul, Matrix.map_one (algebraMap R K) (map_zero _) (map_one _),
        hmapA, hmapB]
      exact (Units.inv_mul g)
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    apply Units.ext
    exact hmapA


theorem range_algebraMap_padicInt (p : ℕ) [Fact p.Prime] :
    Set.range (algebraMap ℤ_[p] ℚ_[p]) = Set.range ((↑) : ℤ_[p] → ℚ_[p]) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, (PadicInt.algebraMap_apply r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, PadicInt.algebraMap_apply r⟩


private instance instCompactSpaceMatrix {m n R : Type*} [TopologicalSpace R]
    [CompactSpace R] : CompactSpace (Matrix m n R) :=
  inferInstanceAs (CompactSpace (m → n → R))

private theorem gl2_compactSpace (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R] :
    CompactSpace (GL (Fin 2) R) := inferInstance

public theorem isCompact_coe_integralSubgroup (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] [CompactSpace R]
    (K : Type*) [Field K] [Algebra R K] [TopologicalSpace K]
    (hcont : Continuous (algebraMap R K)) :
    IsCompact ((integralSubgroup R K : Set (GL (Fin 2) K))) := by
  haveI : CompactSpace (GL (Fin 2) R) := gl2_compactSpace R
  have hmapcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)) := by
    unfold Matrix.GeneralLinearGroup.map
    refine Continuous.units_map _ ?_
    exact continuous_matrix fun i j =>
      hcont.comp ((continuous_apply j).comp (continuous_apply i))
  have hr : IsCompact
      (Set.range ⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K))) :=
    isCompact_range hmapcont
  simpa [integralSubgroup, MonoidHom.coe_range] using hr


/-- The principal congruence subgroup of `GL(2, ℚ_[p])` of level `p ^ n`:
matrices whose entries, and those of their inverse, are within `p ^ (-n)` of
the identity in the p-adic norm. -/
public def gl2CongruenceSubgroup (n : ℕ) : Subgroup (GL (Fin 2) ℚ_[p]) where
  carrier := {g : GL (Fin 2) ℚ_[p] |
    (∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
    (∀ i j, ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖
      ≤ (p : ℝ) ^ (-(n : ℤ)))}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · simp only [inv_one, Units.val_one, sub_self, Matrix.zero_apply, norm_zero]
      exact le_of_lt (radius_pos p n)
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    refine ⟨hg.2, ?_⟩
    rw [inv_inv]
    exact hg.1
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    have hgentry : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hg1
    have hhinventry : ∀ i j,
        ‖((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 :=
      norm_entry_le_one_of_sub_entry_le p (radius_le_one p n) hh2
    constructor
    · intro i j
      have hfact : ((g * h : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) * ((h : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hg1 i j)
      have := norm_matrix_mul_entry_le p hgentry hh1 i j
      rwa [one_mul] at this
    · intro i j
      have hfact : (((g * h)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1
          = ((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
              * (((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1)
            + (((h⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) := by
        rw [mul_inv_rev, Units.val_mul, mul_sub, mul_one]
        abel
      rw [hfact, Matrix.add_apply]
      refine padic_norm_add_le_of_le p ?_ (hh2 i j)
      have := norm_matrix_mul_entry_le p hhinventry hg2 i j
      rwa [one_mul] at this

public theorem mem_gl2CongruenceSubgroup_iff {n : ℕ} {g : GL (Fin 2) ℚ_[p]} :
    g ∈ gl2CongruenceSubgroup p n ↔
      (∀ i j, ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) ∧
      (∀ i j, ‖(((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) i j‖
        ≤ (p : ℝ) ^ (-(n : ℤ))) :=
  Iff.rfl

public theorem gl2CongruenceSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    gl2CongruenceSubgroup p n ≤ gl2CongruenceSubgroup p m := by
  intro g hg
  rw [mem_gl2CongruenceSubgroup_iff] at hg ⊢
  exact ⟨fun i j => le_trans (hg.1 i j) (radius_antitone p h),
    fun i j => le_trans (hg.2 i j) (radius_antitone p h)⟩

private theorem norm_sub_one_entry_le_one_iff {M : Matrix (Fin 2) (Fin 2) ℚ_[p]} {i j : Fin 2} :
    ‖(M - 1) i j‖ ≤ 1 ↔ ‖M i j‖ ≤ 1 := by
  constructor
  · intro h
    have heq : M i j = (M - 1) i j + (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j := by
      rw [Matrix.sub_apply]
      ring
    rw [heq]
    exact padic_norm_add_le_of_le p h (norm_matrix_one_entry_le_one p i j)
  · intro h
    rw [Matrix.sub_apply, sub_eq_add_neg]
    refine padic_norm_add_le_of_le p h ?_
    rw [norm_neg]
    exact norm_matrix_one_entry_le_one p i j

public theorem isOpen_coe_gl2CongruenceSubgroup (n : ℕ) :
    IsOpen ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  have hradius : ((p : ℝ) ^ (-(n : ℤ)) : ℝ) ≠ 0 := ne_of_gt (radius_pos p n)
  have hchar : ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
        Set (GL (Fin 2) ℚ_[p]))
      = (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
          (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
            ∈ Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
              ((p : ℝ) ^ (-(n : ℤ)))})
        ∩ (⋂ i, ⋂ j, {g : GL (Fin 2) ℚ_[p] |
          ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j
            ∈ Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
              ((p : ℝ) ^ (-(n : ℤ)))}) := by
    ext g
    simp only [SetLike.mem_coe, mem_gl2CongruenceSubgroup_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply]
  rw [hchar]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hradius).preimage
      (Units.continuous_val.matrix_elem i j)
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hradius).preimage
      (Units.continuous_coe_inv.matrix_elem i j)


public theorem gl2CongruenceSubgroup_zero_eq_integralSubgroup :
    gl2CongruenceSubgroup p 0 = integralSubgroup ℤ_[p] ℚ_[p] := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    have ha := PadicInt.algebraMap_apply (p := p) a
    have hb := PadicInt.algebraMap_apply (p := p) b
    rw [ha, hb] at hab
    exact Subtype.coe_injective hab
  have mem_range_iff : ∀ {x : ℚ_[p]},
      x ∈ Set.range (algebraMap ℤ_[p] ℚ_[p]) ↔ ‖x‖ ≤ 1 := by
    intro x
    rw [range_algebraMap_padicInt p]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hradius : ((p : ℝ) ^ (-((0 : ℕ) : ℤ)) : ℝ) = 1 := by norm_num
  ext g
  rw [mem_gl2CongruenceSubgroup_iff, mem_integralSubgroup_iff_entries_mem hinj g]
  simp only [hradius]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h1 i j)),
           fun i j => mem_range_iff.mpr ((norm_sub_one_entry_le_one_iff p).mp (h2 i j))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h1 i j)),
           fun i j => (norm_sub_one_entry_le_one_iff p).mpr (mem_range_iff.mp (h2 i j))⟩

public theorem gl2CongruenceSubgroup_le_integralSubgroup (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ integralSubgroup ℤ_[p] ℚ_[p] := by
  rw [← gl2CongruenceSubgroup_zero_eq_integralSubgroup p]
  exact gl2CongruenceSubgroup_antitone p (Nat.zero_le n)

/-- Every principal congruence subgroup of `GL(2, ℚ_[p])` is compact: it is a
closed subset of the compact integral subgroup. -/
public theorem isCompact_coe_gl2CongruenceSubgroup (n : ℕ) :
    IsCompact ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val)
    (Subgroup.isClosed_of_isOpen _ (isOpen_coe_gl2CongruenceSubgroup p n)) ?_
  exact fun g hg => gl2CongruenceSubgroup_le_integralSubgroup p n hg

end Padic
