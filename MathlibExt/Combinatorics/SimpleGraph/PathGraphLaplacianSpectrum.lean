/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Path-graph Laplacian spectrum

The cosine eigenvectors and eigenvalues of one half of the Laplacian of a
finite path graph, with the resulting spectral-gap estimate. The formulas
follow Kitaev, Shen and Vyalyi, Classical and Quantum Computation,
Sections 14.4.2 and 14.4.4.
The eigenvalue and eigenvector formulas are those already recorded for the
path graph in the archived development at
`v1/Atlas/AnAlgorithmistsToolkit/code/PathSpectrum.lean`.
-/

@[expose] public section

open scoped Matrix

namespace MathlibExt.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrum

/-- One half of the real Laplacian matrix of the path graph on `Fin n`. -/
noncomputable def halfPathLaplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (SimpleGraph.pathGraph n).lapMatrix ℝ

/-- The `k`-th cosine mode for the path-graph Laplacian. -/
noncomputable def pathCosineMode (n k : ℕ) : Fin n → ℝ :=
  fun j => Real.cos (Real.pi * k * ((j : ℝ) + 1 / 2) / n)

/-- Three-term recurrence for cosine, used at interior vertices. -/
private theorem cos_add_add_sub (A B : ℝ) :
    Real.cos (A - B) + Real.cos (A + B) = 2 * Real.cos A * Real.cos B := by
  have h1 := Real.cos_add A B
  have h2 := Real.cos_sub A B
  linear_combination h1 + h2

private theorem neighborFinset_pathGraph_one {n : ℕ} (hn : n = 1) (i : Fin n) :
    (SimpleGraph.pathGraph n).neighborFinset i = ∅ := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj]
  have hi : i.val = 0 := by have h1 := i.isLt; omega
  have hu : u.val = 0 := by have h2 := u.isLt; omega
  simp [hi, hu]

private theorem neighborFinset_pathGraph_left {n : ℕ} (hn : 2 ≤ n) {i : Fin n}
    (hi : i.val = 0) :
    (SimpleGraph.pathGraph n).neighborFinset i = {⟨1, by omega⟩} := by
  ext u
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
    Finset.mem_singleton]
  constructor
  · intro h
    apply Fin.ext
    show u.val = 1
    omega
  · intro h
    have hu : u.val = 1 := Fin.ext_iff.mp h
    omega

private theorem neighborFinset_pathGraph_right {n : ℕ} (hn : 2 ≤ n) {i : Fin n}
    (hi : i.val + 1 = n) :
    (SimpleGraph.pathGraph n).neighborFinset i = {⟨i.val - 1, by omega⟩} := by
  ext u
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
    Finset.mem_singleton]
  constructor
  · intro h
    apply Fin.ext
    show u.val = i.val - 1
    omega
  · intro h
    have hu : u.val = i.val - 1 := Fin.ext_iff.mp h
    omega

private theorem neighborFinset_pathGraph_interior {n : ℕ} {i : Fin n}
    (hlo : 0 < i.val) (hhi : i.val + 1 < n) :
    (SimpleGraph.pathGraph n).neighborFinset i =
      {⟨i.val - 1, by omega⟩, ⟨i.val + 1, by omega⟩} := by
  ext u
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h
    · right
      apply Fin.ext
      show u.val = i.val + 1
      omega
    · left
      apply Fin.ext
      show u.val = i.val - 1
      omega
  · intro h
    rcases h with h | h
    · right
      have hu : u.val = i.val - 1 := Fin.ext_iff.mp h
      omega
    · left
      have hu : u.val = i.val + 1 := Fin.ext_iff.mp h
      omega

/-- Each cosine mode satisfies the eigen-equation of the half path Laplacian.

This holds for every `k`, including indices where the mode vanishes (such as
`k = n`), so it does not by itself make the mode an eigenvector. -/
theorem halfPathLaplacian_mulVec_pathCosineMode {n : ℕ} (hn : 0 < n) (k : ℕ) :
    halfPathLaplacian n *ᵥ pathCosineMode n k =
      (1 - Real.cos (Real.pi * k / n)) • pathCosineMode n k := by
  simp only [halfPathLaplacian, Matrix.smul_mulVec]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [SimpleGraph.lapMatrix_mulVec_apply]
  by_cases hn1 : n = 1
  · subst hn1
    have hi0 : i.val = 0 := by have hlt := i.isLt; omega
    have hi0' : i = ⟨0, by norm_num⟩ := Fin.ext hi0
    have hnb := neighborFinset_pathGraph_one rfl i
    have hdeg : (SimpleGraph.pathGraph 1).degree i = 0 := by
      have hcard := congrArg Finset.card hnb
      rw [Finset.card_empty] at hcard
      rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
    rw [hnb, Finset.sum_empty, hdeg]
    simp only [pathCosineMode, hi0', Nat.cast_zero, Nat.cast_one]
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hcos1 : Real.cos (Real.pi * ((m + m : ℕ) : ℝ) / 1) = 1 := by
        have harg : Real.pi * ((m + m : ℕ) : ℝ) / 1
            = 0 + (m : ℝ) * (2 * Real.pi) := by
          push_cast
          ring
        rw [harg, Real.cos_add_nat_mul_two_pi, Real.cos_zero]
      rw [hcos1]
      norm_num
    · have hcos0 : Real.cos (Real.pi * ((2 * m + 1 : ℕ) : ℝ) * (0 + 1 / 2) / 1)
          = 0 := by
        have harg : Real.pi * ((2 * m + 1 : ℕ) : ℝ) * (0 + 1 / 2) / 1
            = (m : ℝ) * Real.pi + Real.pi / 2 := by
          push_cast
          ring
        rw [harg]
        have h1 := Real.cos_add ((m : ℝ) * Real.pi) (Real.pi / 2)
        rw [Real.cos_pi_div_two, Real.sin_pi_div_two,
          Real.sin_nat_mul_pi] at h1
        rw [h1]
        ring
      rw [hcos0]
      norm_num
  · have hn2 : 2 ≤ n := by omega
    have hlt := i.isLt
    by_cases hi0 : i.val = 0
    · have hi0' : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hnb := neighborFinset_pathGraph_left hn2 hi0
      have hdeg : (SimpleGraph.pathGraph n).degree i = 1 := by
        have hcard := congrArg Finset.card hnb
        rw [Finset.card_singleton] at hcard
        rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
      rw [hnb, Finset.sum_singleton, hdeg, hi0']
      simp only [pathCosineMode, Nat.cast_zero, Nat.cast_one]
      set A : ℝ := Real.pi * (k : ℝ) * (0 + 1 / 2) / (n : ℝ) with hAdef
      set B : ℝ := Real.pi * (k : ℝ) / (n : ℝ) with hBdef
      have e1 : Real.pi * (k : ℝ) * (1 + 1 / 2) / (n : ℝ) = B + A := by
        rw [hAdef, hBdef]
        ring
      rw [e1]
      have h3 := cos_add_add_sub B A
      have e2 : B - A = A := by
        rw [hAdef, hBdef]
        ring
      rw [e2] at h3
      linear_combination -h3 / 2
    · by_cases hilast : i.val + 1 = n
      · have hnb := neighborFinset_pathGraph_right hn2 hilast
        have hdeg : (SimpleGraph.pathGraph n).degree i = 1 := by
          have hcard := congrArg Finset.card hnb
          rw [Finset.card_singleton] at hcard
          rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
        rw [hnb, Finset.sum_singleton, hdeg]
        simp only [pathCosineMode]
        rw [Nat.cast_sub (show 1 ≤ i.val by omega), Nat.cast_one]
        set U : ℝ := Real.pi * (k : ℝ) * ((i.val : ℝ) + 1 / 2) / (n : ℝ)
          with hUdef
        set B : ℝ := Real.pi * (k : ℝ) / (n : ℝ) with hBdef
        have e1 : Real.pi * (k : ℝ) * ((i.val : ℝ) - 1 + 1 / 2) / (n : ℝ)
            = U - B := by
          rw [hUdef, hBdef]
          ring
        rw [e1]
        set D : ℝ := Real.pi * (k : ℝ) with hDdef
        set A' : ℝ := Real.pi * (k : ℝ) / (2 * (n : ℝ)) with hAdef
        have hncast : (n : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hilast.symm
        have hne1 : (i.val : ℝ) + 1 ≠ 0 := by positivity
        have hne2 : 2 * ((i.val : ℝ) + 1) ≠ 0 := by positivity
        have eU : U = D - A' := by
          rw [hUdef, hDdef, hAdef, hncast]
          field_simp
          ring
        have eUB : U + B = D + A' := by
          rw [hUdef, hBdef, hDdef, hAdef, hncast]
          field_simp
          ring
        have h1 := Real.cos_add D A'
        have h2 := Real.cos_sub D A'
        have hsin : Real.sin D = 0 := by
          rw [hDdef]
          have h := Real.sin_nat_mul_pi k
          rwa [mul_comm (k : ℝ) Real.pi] at h
        have hmir : Real.cos (U + B) = Real.cos U := by
          rw [eUB, eU]
          linear_combination h1 - h2 - 2 * Real.sin A' * hsin
        have h3 := cos_add_add_sub U B
        rw [hmir] at h3
        linear_combination -h3 / 2
      · have hlo : 0 < i.val := by omega
        have hhi : i.val + 1 < n := by omega
        have h1mem : i.val - 1 < n := by omega
        have h2mem : i.val + 1 < n := by omega
        have hne : (⟨i.val - 1, h1mem⟩ : Fin n) ≠ ⟨i.val + 1, h2mem⟩ := by
          intro hcon
          have hv : i.val - 1 = i.val + 1 := Fin.ext_iff.mp hcon
          omega
        have hnb' := neighborFinset_pathGraph_interior hlo hhi
        have hnb : (SimpleGraph.pathGraph n).neighborFinset i
            = {⟨i.val - 1, h1mem⟩, ⟨i.val + 1, h2mem⟩} := hnb'
        have hdeg : (SimpleGraph.pathGraph n).degree i = 2 := by
          have hcard := congrArg Finset.card hnb
          rw [Finset.card_pair hne] at hcard
          rwa [SimpleGraph.card_neighborFinset_eq_degree] at hcard
        have hsum : ∑ u ∈ (SimpleGraph.pathGraph n).neighborFinset i,
            pathCosineMode n k u
            = pathCosineMode n k ⟨i.val - 1, h1mem⟩
              + pathCosineMode n k ⟨i.val + 1, h2mem⟩ := by
          rw [hnb]
          exact Finset.sum_pair hne
        rw [hsum, hdeg]
        simp only [pathCosineMode]
        rw [Nat.cast_sub (show 1 ≤ i.val by omega), Nat.cast_one]
        rw [Nat.cast_add, Nat.cast_one]
        set U : ℝ := Real.pi * (k : ℝ) * ((i.val : ℝ) + 1 / 2) / (n : ℝ)
          with hUdef
        set B : ℝ := Real.pi * (k : ℝ) / (n : ℝ) with hBdef
        have e1 : Real.pi * (k : ℝ) * ((i.val : ℝ) - 1 + 1 / 2) / (n : ℝ)
            = U - B := by
          rw [hUdef, hBdef]
          ring
        have e2 : Real.pi * (k : ℝ) * ((i.val : ℝ) + 1 + 1 / 2) / (n : ℝ)
            = U + B := by
          rw [hUdef, hBdef]
          ring
        rw [e1, e2]
        have h3 := cos_add_add_sub U B
        linear_combination -h3 / 2

/-- The cosine modes indexed below `n` are nonzero. -/
theorem pathCosineMode_ne_zero {n k : ℕ} (hk : k < n) :
    pathCosineMode n k ≠ 0 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have : NeZero n := ⟨by omega⟩
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
  have h0val : ((0 : Fin n) : ℝ) = 0 := by simp
  rw [Function.ne_iff]
  refine ⟨0, ?_⟩
  simp only [pathCosineMode, Pi.zero_apply, h0val]
  have harg : Real.pi * (k : ℝ) * (0 + 1 / 2) / (n : ℝ)
      = (Real.pi / 2) * ((k : ℝ) / (n : ℝ)) := by
    ring
  rw [harg]
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  rw [Set.mem_Ioo]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hkn : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
  have hkn1 : (k : ℝ) / (n : ℝ) < 1 := by
    rw [div_lt_one hnPos]
    exact_mod_cast hk
  constructor
  · have hnn : (0 : ℝ) ≤ (Real.pi / 2) * ((k : ℝ) / (n : ℝ)) :=
      mul_nonneg hpi2.le hkn
    linarith [Real.pi_pos]
  · calc (Real.pi / 2) * ((k : ℝ) / (n : ℝ)) < (Real.pi / 2) * 1 :=
          mul_lt_mul_of_pos_left hkn1 hpi2
      _ = Real.pi / 2 := mul_one _

/-- Each cosine mode indexed below `n` is an eigenvector of the half path
Laplacian: it is nonzero and satisfies the eigen-equation. -/
theorem halfPathLaplacian_eigenvector_pathCosineMode {n k : ℕ} (hn : 0 < n)
    (hk : k < n) :
    pathCosineMode n k ≠ 0 ∧
      halfPathLaplacian n *ᵥ pathCosineMode n k =
        (1 - Real.cos (Real.pi * k / n)) • pathCosineMode n k :=
  ⟨pathCosineMode_ne_zero hk, halfPathLaplacian_mulVec_pathCosineMode hn k⟩

private theorem cos_arg_nonneg {n k : ℕ} (hn : 0 < n) :
    (0 : ℝ) ≤ Real.pi * (k : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  exact div_nonneg (mul_nonneg Real.pi_pos.le hk0) hnR.le

private theorem cos_arg_le_pi {n l : ℕ} (hn : 0 < n) (hln : l ≤ n) :
    Real.pi * (l : ℝ) / (n : ℝ) ≤ Real.pi := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlnR : (l : ℝ) ≤ (n : ℝ) := by exact_mod_cast hln
  have h1 : (l : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hnR).mpr hlnR
  have hmul := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
  rw [mul_one] at hmul
  calc Real.pi * (l : ℝ) / (n : ℝ) = Real.pi * ((l : ℝ) / (n : ℝ)) := by ring
    _ ≤ Real.pi := hmul

private theorem cos_eigenvalue_lt {n k l : ℕ} (hn : 0 < n) (hln : l ≤ n)
    (hkl : k < l) :
    Real.cos (Real.pi * (l : ℝ) / (n : ℝ))
      < Real.cos (Real.pi * (k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hklR : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (cos_arg_nonneg hn)
    (cos_arg_le_pi hn hln)
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hklR Real.pi_pos) hnR)

private theorem cos_eigenvalue_le {n k l : ℕ} (hn : 0 < n) (hln : l ≤ n)
    (hkl : k ≤ l) :
    Real.cos (Real.pi * (l : ℝ) / (n : ℝ))
      ≤ Real.cos (Real.pi * (k : ℝ) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hklR : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  exact Real.cos_le_cos_of_nonneg_of_le_pi (cos_arg_nonneg hn)
    (cos_arg_le_pi hn hln)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hklR Real.pi_pos.le) hnR.le)

private theorem halfPathLaplacian_isSymm (n : ℕ) :
    (halfPathLaplacian n).IsSymm := by
  simp only [halfPathLaplacian]
  exact ((SimpleGraph.pathGraph n).isSymm_lapMatrix ℝ).smul _

/-- Distinct cosine modes indexed below `n` are orthogonal. -/
theorem pathCosineMode_dotProduct_eq_zero {n k l : ℕ}
    (hk : k < n) (hl : l < n) (hkl : k ≠ l) :
    pathCosineMode n k ⬝ᵥ pathCosineMode n l = 0 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hcos : Real.cos (Real.pi * (k : ℝ) / (n : ℝ))
      ≠ Real.cos (Real.pi * (l : ℝ) / (n : ℝ)) := by
    rcases lt_or_gt_of_ne hkl with h | h
    · exact ne_of_gt (cos_eigenvalue_lt hn hl.le h)
    · exact ne_of_lt (cos_eigenvalue_lt hn hk.le h)
  have hne : (1 - Real.cos (Real.pi * (k : ℝ) / (n : ℝ)))
      ≠ (1 - Real.cos (Real.pi * (l : ℝ) / (n : ℝ))) := by
    intro hcon
    apply hcos
    linarith
  have hk_eq := halfPathLaplacian_mulVec_pathCosineMode hn k
  have hl_eq := halfPathLaplacian_mulVec_pathCosineMode hn l
  have hcomm := (halfPathLaplacian_isSymm n).dotProduct_mulVec_comm
    (x := pathCosineMode n k) (y := pathCosineMode n l)
  rw [hk_eq, hl_eq] at hcomm
  simp only [dotProduct_smul, smul_eq_mul] at hcomm
  rw [dotProduct_comm (pathCosineMode n l)
    (pathCosineMode n k)] at hcomm
  have hfactor : ((1 - Real.cos (Real.pi * (k : ℝ) / (n : ℝ)))
      - (1 - Real.cos (Real.pi * (l : ℝ) / (n : ℝ))))
      * (pathCosineMode n k ⬝ᵥ pathCosineMode n l) = 0 := by
    linear_combination -hcomm
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact absurd hzero (sub_ne_zero.mpr hne)
  · exact hzero

private theorem cosineModes_linearIndependent {n : ℕ} :
    LinearIndependent ℝ (fun k : Fin n => pathCosineMode n k.val) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hdot0 : (∑ i, g i • pathCosineMode n i.val) ⬝ᵥ pathCosineMode n j.val
      = 0 := by
    rw [hg]
    exact zero_dotProduct _
  have hsingle :
      ∑ i, ((g i • pathCosineMode n i.val) ⬝ᵥ pathCosineMode n j.val)
      = (g j • pathCosineMode n j.val) ⬝ᵥ pathCosineMode n j.val := by
    refine Finset.sum_eq_single j ?_ ?_
    · intro i _ hij
      have hval : i.val ≠ j.val := fun hcon => hij (Fin.ext hcon)
      have horth := pathCosineMode_dotProduct_eq_zero i.isLt j.isLt hval
      rw [smul_dotProduct, smul_eq_mul, horth, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [sum_dotProduct, hsingle, smul_dotProduct, smul_eq_mul] at hdot0
  have hw : pathCosineMode n j.val ⬝ᵥ pathCosineMode n j.val ≠ 0 :=
    fun h => pathCosineMode_ne_zero j.isLt (dotProduct_self_eq_zero.mp h)
  exact (mul_eq_zero.mp hdot0).resolve_right hw

private theorem cosineModes_span {n : ℕ} (v : Fin n → ℝ) :
    ∃ c : Fin n → ℝ, ∑ k, c k • pathCosineMode n k.val = v := by
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ) :=
    (Module.finrank_pi ℝ).symm
  have hspan := cosineModes_linearIndependent.span_eq_top_of_card_eq_finrank'
    hcard
  have hmem : v ∈ Submodule.span ℝ
      (Set.range fun k : Fin n => pathCosineMode n k.val) := by
    rw [hspan]
    trivial
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem

/-- The eigenvalues of the half path Laplacian are exactly the displayed
cosine values. -/
theorem halfPathLaplacian_hasEigenvalue_iff {n : ℕ} (hn : 0 < n) (μ : ℝ) :
    (∃ v ≠ 0, halfPathLaplacian n *ᵥ v = μ • v) ↔
      ∃ k < n, μ = 1 - Real.cos (Real.pi * k / n) := by
  constructor
  · rintro ⟨v, hv0, hvv⟩
    by_contra hcon
    push Not at hcon
    have hall : ∀ j : Fin n,
        pathCosineMode n j.val ⬝ᵥ v = 0 := by
      intro j
      have hj_eq := halfPathLaplacian_mulVec_pathCosineMode hn j.val
      have hcomm := (halfPathLaplacian_isSymm n).dotProduct_mulVec_comm
        (x := v) (y := pathCosineMode n j.val)
      rw [hj_eq, hvv] at hcomm
      simp only [dotProduct_smul, smul_eq_mul] at hcomm
      rw [dotProduct_comm v (pathCosineMode n j.val)] at hcomm
      have hfactor : (μ - (1 - Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ))))
          * (pathCosineMode n j.val ⬝ᵥ v) = 0 := by
        linear_combination -hcomm
      have hnej : μ ≠ 1 - Real.cos (Real.pi * (j.val : ℝ) / (n : ℝ)) :=
        hcon j.val j.isLt
      rcases mul_eq_zero.mp hfactor with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hnej
      · exact h0
    obtain ⟨c, hc⟩ := cosineModes_span v
    have hself : (∑ k, c k • pathCosineMode n k.val) ⬝ᵥ v = 0 := by
      rw [sum_dotProduct]
      apply Finset.sum_eq_zero
      intro k _
      rw [smul_dotProduct, smul_eq_mul, hall k, mul_zero]
    rw [hc] at hself
    exact hv0 (dotProduct_self_eq_zero.mp hself)
  · rintro ⟨k, hk, rfl⟩
    exact ⟨pathCosineMode n k, pathCosineMode_ne_zero hk,
      halfPathLaplacian_mulVec_pathCosineMode hn k⟩

/-- Each cosine value indexed below `n` is an eigenvalue of the half path
Laplacian, viewed as a linear map. -/
theorem halfPathLaplacian_hasEigenvalue {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    Module.End.HasEigenvalue (Matrix.toLin' (halfPathLaplacian n))
      (1 - Real.cos (Real.pi * k / n)) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := pathCosineMode n k)
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact halfPathLaplacian_mulVec_pathCosineMode hn k
  · exact pathCosineMode_ne_zero hk

/-- Each cosine value indexed below `n` lies in the spectrum of the half
path Laplacian. -/
theorem halfPathLaplacian_mem_spectrum {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    (1 - Real.cos (Real.pi * k / n)) ∈ spectrum ℝ (halfPathLaplacian n) := by
  rw [← Matrix.spectrum_toLin']
  exact Module.End.hasEigenvalue_iff_mem_spectrum.mp
    (halfPathLaplacian_hasEigenvalue hn hk)

private theorem pathCosineMode_zero_apply {n : ℕ} (j : Fin n) :
    pathCosineMode n 0 j = 1 := by
  simp [pathCosineMode, Real.cos_zero]

private theorem dot_mode_expansion {n : ℕ} (c : Fin n → ℝ)
    (v : Fin n → ℝ) (hc : ∑ k, c k • pathCosineMode n k.val = v)
    (k : Fin n) :
    pathCosineMode n k.val ⬝ᵥ v
      = c k * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val) := by
  rw [← hc, dotProduct_sum]
  have hsingle :
      ∑ j, (pathCosineMode n k.val ⬝ᵥ (c j • pathCosineMode n j.val))
      = pathCosineMode n k.val ⬝ᵥ (c k • pathCosineMode n k.val) := by
    refine Finset.sum_eq_single k ?_ ?_
    · intro j _ hjk
      have hval : k.val ≠ j.val := fun h => hjk (Fin.ext h.symm)
      have horth := pathCosineMode_dotProduct_eq_zero k.isLt j.isLt hval
      rw [dotProduct_smul, smul_eq_mul, horth, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hsingle, dotProduct_smul, smul_eq_mul]

private theorem dotProduct_self_nonneg {n : ℕ} (v : Fin n → ℝ) :
    (0 : ℝ) ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg _

/-- Quadratic-form spectral gap on the zero-sum subspace. -/
theorem halfPathLaplacian_quadForm_ge {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (hv : ∑ j, v j = 0) :
    (1 - Real.cos (Real.pi / n)) * (v ⬝ᵥ v) ≤
      v ⬝ᵥ (halfPathLaplacian n *ᵥ v) := by
  obtain ⟨c, hc⟩ := cosineModes_span v
  have hdot0 : pathCosineMode n 0 ⬝ᵥ v = 0 := by
    have h1 : pathCosineMode n 0 ⬝ᵥ v = ∑ j, v j := by
      simp only [dotProduct, pathCosineMode_zero_apply, one_mul]
    rw [h1, hv]
  have hc0 : c ⟨0, hn⟩ = 0 := by
    have hdot := dot_mode_expansion c v hc ⟨0, hn⟩
    have hdot' : pathCosineMode n 0 ⬝ᵥ v
        = c ⟨0, hn⟩ * (pathCosineMode n 0 ⬝ᵥ pathCosineMode n 0) := hdot
    rw [hdot0] at hdot'
    have hw0 : pathCosineMode n 0 ⬝ᵥ pathCosineMode n 0 ≠ 0 :=
      fun h => pathCosineMode_ne_zero hn (dotProduct_self_eq_zero.mp h)
    have hmul : c ⟨0, hn⟩ * (pathCosineMode n 0 ⬝ᵥ pathCosineMode n 0) = 0 :=
      hdot'.symm
    exact (mul_eq_zero.mp hmul).resolve_right hw0
  have hvv : v ⬝ᵥ v = ∑ k,
      (c k) ^ 2 * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val) := by
    have hsum : (∑ k, c k • pathCosineMode n k.val) ⬝ᵥ v = ∑ k,
        (c k) ^ 2 * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val) := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_dotProduct, smul_eq_mul, dot_mode_expansion c v hc k]
      ring
    rw [hc] at hsum
    exact hsum
  have hHv : v ⬝ᵥ (halfPathLaplacian n *ᵥ v) = ∑ k,
      (1 - Real.cos (Real.pi * (k.val : ℝ) / (n : ℝ)))
        * ((c k) ^ 2 * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val)) := by
    have hsum : (∑ k, c k • pathCosineMode n k.val) ⬝ᵥ (halfPathLaplacian n *ᵥ v)
        = ∑ k, (1 - Real.cos (Real.pi * (k.val : ℝ) / (n : ℝ)))
          * ((c k) ^ 2
            * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val)) := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_dotProduct, smul_eq_mul]
      have hsym := (halfPathLaplacian_isSymm n).dotProduct_mulVec_comm
        (x := pathCosineMode n k.val) (y := v)
      rw [hsym]
      have hk_eq := halfPathLaplacian_mulVec_pathCosineMode hn k.val
      rw [hk_eq, dotProduct_smul, smul_eq_mul,
        dotProduct_comm v (pathCosineMode n k.val),
        dot_mode_expansion c v hc k]
      ring
    rw [hc] at hsum
    exact hsum
  rw [hvv, hHv, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk0 : k = ⟨0, hn⟩
  · subst hk0
    simp [hc0]
  · have hval0 : k.val ≠ 0 := by
      intro h0
      apply hk0
      exact Fin.ext h0
    have hk1 : 1 ≤ k.val := by omega
    have hcos := cos_eigenvalue_le hn k.isLt.le hk1
    have harg1 : Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) = Real.pi / (n : ℝ) := by
      rw [Nat.cast_one, mul_one]
    rw [harg1] at hcos
    have hmono : (1 - Real.cos (Real.pi / (n : ℝ)))
        ≤ 1 - Real.cos (Real.pi * (k.val : ℝ) / (n : ℝ)) := by
      linarith [hcos]
    have hnonneg : (0 : ℝ) ≤ (c k) ^ 2
        * (pathCosineMode n k.val ⬝ᵥ pathCosineMode n k.val) :=
      mul_nonneg (sq_nonneg _)
        (dotProduct_self_nonneg (pathCosineMode n k.val))
    exact mul_le_mul_of_nonneg_right hmono hnonneg

/-- Every nonzero eigenvalue is bounded below by the first positive cosine
value, and that value is attained. -/
theorem halfPathLaplacian_eigenvalue_ge {n : ℕ} (hn : 2 ≤ n) :
    (∀ μ : ℝ, (∃ v ≠ 0, halfPathLaplacian n *ᵥ v = μ • v) → μ ≠ 0 →
      1 - Real.cos (Real.pi / n) ≤ μ) ∧
    ∃ v ≠ 0,
      halfPathLaplacian n *ᵥ v =
        (1 - Real.cos (Real.pi / n)) • v := by
  have hn0 : 0 < n := by omega
  constructor
  · intro μ hμ hμ0
    obtain ⟨k, hk, rfl⟩ :=
      (halfPathLaplacian_hasEigenvalue_iff hn0 μ).mp hμ
    have hmu0 : (1 : ℝ) - Real.cos (Real.pi * ((0 : ℕ) : ℝ) / (n : ℝ)) = 0 := by
      have harg : Real.pi * ((0 : ℕ) : ℝ) / (n : ℝ) = 0 := by simp
      rw [harg, Real.cos_zero]
      norm_num
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hμ0 hmu0
    have hk1 : 1 ≤ k := by omega
    have hcos := cos_eigenvalue_le hn0 hk.le hk1
    have harg1 : Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) = Real.pi / (n : ℝ) := by
      rw [Nat.cast_one, mul_one]
    rw [harg1] at hcos
    linarith [hcos]
  · refine ⟨pathCosineMode n 1, pathCosineMode_ne_zero (by omega), ?_⟩
    have h := halfPathLaplacian_mulVec_pathCosineMode hn0 1
    have harg1 : Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ) = Real.pi / (n : ℝ) := by
      rw [Nat.cast_one, mul_one]
    rw [harg1] at h
    exact h

/-- Elementary lower bound for the first positive path eigenvalue. -/
theorem two_div_sq_le_one_sub_cos_pi_div {n : ℕ} (hn : 1 ≤ n) :
    2 / (n : ℝ) ^ 2 ≤ 1 - Real.cos (Real.pi / n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hAbs : |Real.pi / (n : ℝ)| ≤ Real.pi := by
    rw [abs_of_nonneg (by positivity)]
    calc Real.pi / (n : ℝ) ≤ Real.pi / 1 :=
            div_le_div_of_nonneg_left Real.pi_pos.le zero_lt_one hnR
        _ = Real.pi := div_one Real.pi
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h := Real.cos_le_one_sub_mul_cos_sq (x := Real.pi / (n : ℝ)) hAbs
  have hval : 2 / Real.pi ^ 2 * (Real.pi / (n : ℝ)) ^ 2 = 2 / (n : ℝ) ^ 2 := by
    field_simp
  rw [hval] at h
  linarith

/-- The `c / T ^ 2` propagation-gap estimate in the normalization with
`n = T + 1` path vertices. -/
theorem propagation_gap_ge (T : ℕ) (hT : 1 ≤ T) :
    1 / (2 * (T : ℝ) ^ 2) ≤
      1 - Real.cos (Real.pi / (T + 1)) := by
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  have h2 := two_div_sq_le_one_sub_cos_pi_div (n := T + 1) (by omega)
  rw [Nat.cast_add, Nat.cast_one] at h2
  have hstep : 1 / (2 * (T : ℝ) ^ 2) ≤ 2 / ((T : ℝ) + 1) ^ 2 := by
    have e1 : (0 : ℝ) < 2 * (T : ℝ) ^ 2 := by positivity
    have e2 : (0 : ℝ) < ((T : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_div_iff₀ e1 e2]
    nlinarith [hT', hTpos, sq_nonneg ((T : ℝ) - 1), sq_nonneg (T : ℝ)]
  linarith

end MathlibExt.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrum
