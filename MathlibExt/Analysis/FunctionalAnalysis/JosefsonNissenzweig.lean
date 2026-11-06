/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import MathlibExt.Analysis.FunctionalAnalysis.BanachLimit
import MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1

@[expose] public section

section
namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

private theorem jn_rclike_of_real
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional 𝕜 E)
    (hreal : ¬ FiniteDimensional ℝ E →
      ∃ (φ : ℕ → StrongDual ℝ E), (∀ n, ‖φ n‖ = 1) ∧
        ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : ℝ))) :
    ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  have hInfReal : ¬ FiniteDimensional ℝ E := by
    intro h
    apply hInf
    let _ : FiniteDimensional ℝ E := h
    exact Module.Finite.of_restrictScalars_finite ℝ 𝕜 E
  obtain ⟨φ, hφnorm, hφ⟩ := hreal hInfReal
  refine ⟨fun n => (φ n).extendRCLike, ?_, ?_⟩
  · intro n
    exact StrongDual.norm_extendRCLike (φ n) |>.trans (hφnorm n)
  · intro x
    have hx : Filter.Tendsto (RCLike.ofReal ∘ fun n => (φ n) x) Filter.atTop
        (nhds (0 : 𝕜)) := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto 0).comp (hφ x)
    have hIx : Filter.Tendsto
        (RCLike.ofReal ∘ fun n => (φ n) ((RCLike.I : 𝕜) • x)) Filter.atTop
        (nhds (0 : 𝕜)) := by
      simpa only [RCLike.ofReal_zero] using
        (RCLike.continuous_ofReal.tendsto 0).comp (hφ ((RCLike.I : 𝕜) • x))
    change Filter.Tendsto (fun n => RCLike.ofReal ((φ n) x) -
      (RCLike.I : 𝕜) * RCLike.ofReal ((φ n) ((RCLike.I : 𝕜) • x))) Filter.atTop (nhds 0)
    simpa only [Function.comp_apply, mul_zero, sub_zero] using
      hx.sub (tendsto_const_nhds.mul hIx)

private theorem jn_dual_infinite_dimensional
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    ¬ FiniteDimensional 𝕜 (StrongDual 𝕜 E) := by
  intro hDual
  apply hInf
  let _ : FiniteDimensional 𝕜 (StrongDual 𝕜 E) := hDual
  let _ : FiniteDimensional 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    FiniteDimensional.of_injective (ContinuousLinearMap.coeLM 𝕜)
      ContinuousLinearMap.coe_injective
  exact FiniteDimensional.of_injective (K := 𝕜) (V := E)
    (V₂ := StrongDual 𝕜 (StrongDual 𝕜 E))
    (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).toLinearMap
    (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).injective

private theorem jn_exists_separated_dual_sequence
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ) (φ : ℕ → StrongDual 𝕜 E), 1 < R ∧
      (∀ n, ‖φ n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖φ m - φ n‖ := by
  exact exists_seq_norm_le_one_le_norm_sub (jn_dual_infinite_dimensional hInf)

private theorem jn_of_pointwise_cauchy_subsequence
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (φ : ℕ → StrongDual 𝕜 E)
    (hsep : Pairwise fun m n => 1 ≤ ‖φ m - φ n‖)
    (u : ℕ → ℕ) (hu : StrictMono u)
    (hcauchy : ∀ x : E, CauchySeq (fun n => (φ (u n)) x)) :
    ∃ (ψ : ℕ → StrongDual 𝕜 E), (∀ n, ‖ψ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let d : ℕ → StrongDual 𝕜 E := fun n => φ (u (2 * n)) - φ (u (2 * n + 1))
  have hd : ∀ n, 1 ≤ ‖d n‖ := by
    intro n
    apply hsep
    exact hu.injective.ne (by omega)
  let ψ : ℕ → StrongDual 𝕜 E := fun n => (((‖d n‖⁻¹ : ℝ) : 𝕜) • d n)
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    have hpos : 0 < ‖d n‖ := lt_of_lt_of_le zero_lt_one (hd n)
    simp only [ψ, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hpos)]
  · intro x
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hcauchy x)
    have heven : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun a ha => ?_⟩
      omega
    have hodd : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun a ha => ?_⟩
      omega
    have hd0 : Filter.Tendsto (fun n => (d n) x) Filter.atTop (nhds (0 : 𝕜)) := by
      simpa only [Function.comp_apply, d, sub_apply, sub_self] using
        (ha.comp heven).sub (ha.comp hodd)
    rw [Metric.tendsto_atTop] at hd0 ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hd0 ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hcoef : ‖(((‖d n‖⁻¹ : ℝ) : 𝕜))‖ ≤ 1 := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hd n))).2 (hd n)
    rw [dist_zero_right]
    calc
      ‖(ψ n) x‖ = ‖(((‖d n‖⁻¹ : ℝ) : 𝕜))‖ * ‖(d n) x‖ := by
        simp only [ψ, smul_apply, norm_smul]
      _ ≤ 1 * ‖(d n) x‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
      _ < ε := by simpa only [one_mul, dist_zero_right] using hN n hn

private theorem jn_of_lower_bounded_pointwise_null
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (φ : ℕ → StrongDual 𝕜 E) (δ : ℝ) (hδ : 0 < δ)
    (hlower : ∀ n, δ ≤ ‖φ n‖)
    (hnull : ∀ x : E,
      Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜))) :
    ∃ (ψ : ℕ → StrongDual 𝕜 E), (∀ n, ‖ψ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let ψ : ℕ → StrongDual 𝕜 E := fun n => (((‖φ n‖⁻¹ : ℝ) : 𝕜) • φ n)
  refine ⟨ψ, ?_, ?_⟩
  · intro n
    have hpos : 0 < ‖φ n‖ := hδ.trans_le (hlower n)
    simp only [ψ, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (ne_of_gt hpos)]
  · intro x
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero_norm (a := fun n => δ⁻¹ * ‖(φ n) x‖)
    · intro n
      have hpos : 0 < ‖φ n‖ := hδ.trans_le (hlower n)
      have hcoef : ‖φ n‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hpos hδ).mpr (hlower n)
      simp only [ψ, smul_apply, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs,
        abs_mul, abs_inv, abs_norm]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((φ n) x))
    · simpa only [norm_zero, mul_zero] using (hnull x).norm.const_mul δ⁻¹

private def jnCoeffNorm (a : ℕ →₀ ℝ) : ℝ :=
  a.sum fun _ t => |t|

private structure JnBlocking where
  coeff : ℕ → ℕ →₀ ℝ
  norm_one : ∀ n, jnCoeffNorm (coeff n) = 1
  successive : ∀ {m n}, m < n → ∀ i ∈ (coeff m).support,
    ∀ j ∈ (coeff n).support, i < j

private noncomputable def jnBlockApply
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (b : JnBlocking) (x : ℕ → E) (n : ℕ) : E :=
  Finsupp.linearCombination ℝ x (b.coeff n)

private theorem jn_coeffNorm_smul (r : ℝ) (a : ℕ →₀ ℝ) :
    jnCoeffNorm (r • a) = |r| * jnCoeffNorm a := by
  classical
  by_cases hr : r = 0
  · simp [hr, jnCoeffNorm]
  · simp [jnCoeffNorm, Finsupp.sum, hr, abs_mul, Finset.mul_sum]

private theorem jn_coeffNorm_add_of_disjoint {a b : ℕ →₀ ℝ}
    (h : Disjoint a.support b.support) :
    jnCoeffNorm (a + b) = jnCoeffNorm a + jnCoeffNorm b := by
  classical
  unfold jnCoeffNorm
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, Finsupp.support_add_eq h,
    Finset.sum_union h]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hib : i ∉ b.support := Finset.disjoint_left.mp h hi
    simp [Finsupp.notMem_support_iff.mp hib]
  · apply Finset.sum_congr rfl
    intro i hi
    have hia : i ∉ a.support := Finset.disjoint_right.mp h hi
    simp [Finsupp.notMem_support_iff.mp hia]

private theorem jn_support_sum_subset (s : Finset ℕ) (a : ℕ → ℕ →₀ ℝ) :
    (∑ i ∈ s, a i).support ⊆ s.biUnion fun i => (a i).support := by
  classical
  intro q hq
  rw [Finset.mem_biUnion]
  by_contra hnone
  push Not at hnone
  have hz : ∀ i ∈ s, a i q = 0 := by
    intro i hi
    exact Finsupp.notMem_support_iff.mp (hnone i hi)
  apply Finsupp.mem_support_iff.mp hq
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact hz i hi

private theorem jn_coeffNorm_sum_of_pairwise_disjoint
    (s : Finset ℕ) (a : ℕ → ℕ →₀ ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (a i).support (a j).support) :
    jnCoeffNorm (∑ i ∈ s, a i) = ∑ i ∈ s, jnCoeffNorm (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jnCoeffNorm]
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
          Disjoint (a j).support (a k).support := by
        exact fun j hj k hk => h j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk)
      have hdis : Disjoint (a i).support (∑ j ∈ s, a j).support := by
        rw [Finset.disjoint_left]
        intro q hqi hqsum
        obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp
          (jn_support_sum_subset s a hqsum)
        exact Finset.disjoint_left.mp
          (h i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (by intro hij; subst j; exact hi hj)) hqi hqj
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        jn_coeffNorm_add_of_disjoint hdis, ih hrest]

private theorem jn_coeffNorm_linearCombination
    (a : ℕ → ℕ →₀ ℝ)
    (ha : Pairwise fun i j => Disjoint (a i).support (a j).support)
    (b : ℕ →₀ ℝ) :
    jnCoeffNorm (Finsupp.linearCombination ℝ a b) =
      b.sum fun i t => |t| * jnCoeffNorm (a i) := by
  classical
  rw [Finsupp.linearCombination_apply]
  change jnCoeffNorm (∑ i ∈ b.support, b i • a i) =
    ∑ i ∈ b.support, |b i| * jnCoeffNorm (a i)
  rw [jn_coeffNorm_sum_of_pairwise_disjoint]
  · apply Finset.sum_congr rfl
    intro i hi
    exact jn_coeffNorm_smul (b i) (a i)
  · intro i hi j hj hij
    have hbi : b i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hbj : b j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simpa [hbi, hbj] using ha hij

private theorem jn_blocking_disjoint (b : JnBlocking) :
    Pairwise fun i j => Disjoint (b.coeff i).support (b.coeff j).support := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact (b.successive hijlt q hqi q hqj).false
  · exact (b.successive hjilt q hqj q hqi).false

private theorem jn_blocking_support_nonempty (b : JnBlocking) (n : ℕ) :
    (b.coeff n).support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro hzero
  have h := b.norm_one n
  simp [hzero, jnCoeffNorm] at h

private noncomputable def jnBlockFirst (b : JnBlocking) (n : ℕ) : ℕ :=
  (b.coeff n).support.min' (jn_blocking_support_nonempty b n)

private theorem jn_blockFirst_strictMono (b : JnBlocking) :
    StrictMono (jnBlockFirst b) := by
  intro m n hmn
  exact b.successive hmn _ (Finset.min'_mem _ _) _ (Finset.min'_mem _ _)

private theorem jn_block_index_le_support (b : JnBlocking) (n i : ℕ)
    (hi : i ∈ (b.coeff n).support) : n ≤ i := by
  exact (jn_blockFirst_strictMono b).id_le n |>.trans (Finset.min'_le _ _ hi)

private theorem jn_linearCombination_support_subset
    (a : ℕ → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    (Finsupp.linearCombination ℝ a b).support ⊆
      b.support.biUnion fun i => (a i).support := by
  classical
  rw [Finsupp.linearCombination_apply]
  change (∑ i ∈ b.support, b i • a i).support ⊆ _
  intro q hq
  obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
    (jn_support_sum_subset b.support (fun i => b i • a i) hq)
  refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
  by_contra hnot
  apply Finsupp.mem_support_iff.mp hqi
  simp [Finsupp.notMem_support_iff.mp hnot]

private noncomputable def jnBlockingComp (a b : JnBlocking) : JnBlocking where
  coeff n := Finsupp.linearCombination ℝ a.coeff (b.coeff n)
  norm_one n := by
    rw [jn_coeffNorm_linearCombination a.coeff (jn_blocking_disjoint a)]
    simp_rw [a.norm_one, mul_one]
    exact b.norm_one n
  successive := by
    intro m n hmn q hqm r hnr
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset a.coeff (b.coeff m) hqm)
    obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset a.coeff (b.coeff n) hnr)
    exact a.successive (b.successive hmn i hi j hj) q hqi r hrj

private theorem jn_blockApply_comp
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : JnBlocking) (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnBlockingComp a b) x n =
      jnBlockApply b (jnBlockApply a x) n := by
  exact Finsupp.linearCombination_linearCombination ℝ x a.coeff (b.coeff n)

private theorem jn_blockApply_comp_fun
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a b : JnBlocking) (x : ℕ → E) :
    jnBlockApply (jnBlockingComp a b) x =
      jnBlockApply b (jnBlockApply a x) := by
  funext n
  exact jn_blockApply_comp a b x n

private theorem jnBlocking_ext {a b : JnBlocking}
    (h : ∀ n, a.coeff n = b.coeff n) : a = b := by
  cases a with
  | mk ac an as =>
      cases b with
      | mk bc bn bs =>
          dsimp at h
          have hab : ac = bc := funext h
          subst bc
          rfl

private theorem jn_blockingComp_assoc (a b c : JnBlocking) :
    jnBlockingComp (jnBlockingComp a b) c =
      jnBlockingComp a (jnBlockingComp b c) := by
  apply jnBlocking_ext
  intro n
  exact (Finsupp.linearCombination_linearCombination ℝ a.coeff b.coeff
    (c.coeff n)).symm

private noncomputable def jnSubsequenceBlocking
    (u : ℕ → ℕ) (hu : StrictMono u) : JnBlocking where
  coeff n := Finsupp.single (u n) 1
  norm_one n := by simp [jnCoeffNorm]
  successive := by
    intro m n hmn i hi j hj
    simp only [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hi hj
    subst i
    subst j
    exact hu hmn

@[simp] private theorem jn_blockApply_subsequence
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (u : ℕ → ℕ) (hu : StrictMono u) (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnSubsequenceBlocking u hu) x n = x (u n) := by
  simp [jnBlockApply, jnSubsequenceBlocking]

private noncomputable def jnIdBlocking : JnBlocking :=
  jnSubsequenceBlocking id strictMono_id

private theorem jn_blockingComp_id (b : JnBlocking) :
    jnBlockingComp b jnIdBlocking = b := by
  apply jnBlocking_ext
  intro n
  simp [jnBlockingComp, jnIdBlocking, jnSubsequenceBlocking]

private noncomputable def jnBlockingChain (step : ℕ → JnBlocking) : ℕ → JnBlocking
  | 0 => jnIdBlocking
  | n + 1 => jnBlockingComp (jnBlockingChain step n) (step n)

private noncomputable def jnBlockingTailChain
    (step : ℕ → JnBlocking) (k : ℕ) : ℕ → JnBlocking
  | 0 => jnIdBlocking
  | d + 1 => jnBlockingComp (jnBlockingTailChain step k d) (step (k + d))

private theorem jn_blockingChain_add (step : ℕ → JnBlocking) (k d : ℕ) :
    jnBlockingChain step (k + d) =
      jnBlockingComp (jnBlockingChain step k) (jnBlockingTailChain step k d) := by
  induction d with
  | zero => simp [jnBlockingTailChain, jn_blockingComp_id]
  | succ d ih =>
      rw [Nat.add_succ, jnBlockingChain, ih, jn_blockingComp_assoc]
      rfl

private noncomputable def jnDiagonalBlocking (step : ℕ → JnBlocking) : JnBlocking where
  coeff n := (jnBlockingChain step n).coeff n
  norm_one n := (jnBlockingChain step n).norm_one n
  successive := by
    intro m n hmn i hi j hj
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn.le
    have hchain : jnBlockingChain step n =
        jnBlockingComp (jnBlockingChain step m) (jnBlockingTailChain step m d) := by
      rw [hd]
      exact jn_blockingChain_add step m d
    rw [hchain] at hj
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset (jnBlockingChain step m).coeff
        ((jnBlockingTailChain step m d).coeff n) hj)
    have hnq : n ≤ q := jn_block_index_le_support
      (jnBlockingTailChain step m d) n q hq
    exact (jnBlockingChain step m).successive (hmn.trans_le hnq) i hi j hjq

private theorem jn_blockApply_diagonal
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (step : ℕ → JnBlocking) (x : ℕ → E) (k d : ℕ) :
    jnBlockApply (jnDiagonalBlocking step) x (k + d) =
      jnBlockApply (jnBlockingTailChain step k d)
        (jnBlockApply (jnBlockingChain step k) x) (k + d) := by
  change jnBlockApply (jnBlockingChain step (k + d)) x (k + d) = _
  rw [jn_blockingChain_add, jn_blockApply_comp]

private noncomputable def jnGroupedBlocking
    (p : ℕ) (s : ℕ → ℝ)
    (hs : ∑ i ∈ Finset.range p, |s i| = 1) : JnBlocking where
  coeff n := ∑ i ∈ Finset.range p, Finsupp.single (p * n + i) (s i)
  norm_one n := by
    rw [jn_coeffNorm_sum_of_pairwise_disjoint]
    · simpa [jnCoeffNorm] using hs
    · intro i hi j hj hij
      by_cases hsi : s i = 0
      · simp [hsi]
      by_cases hsj : s j = 0
      · simp [hsj]
      rw [Finsupp.support_single _ hsi, Finsupp.support_single _ hsj]
      simpa [Finset.disjoint_singleton] using hij
  successive := by
    intro m n hmn q hqm r hnr
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
      (jn_support_sum_subset (Finset.range p)
        (fun i => Finsupp.single (p * m + i) (s i)) hqm)
    obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp
      (jn_support_sum_subset (Finset.range p)
        (fun j => Finsupp.single (p * n + j) (s j)) hnr)
    have hq : q = p * m + i := Finset.mem_singleton.mp
      (Finsupp.support_single_subset hqi)
    have hr : r = p * n + j := Finset.mem_singleton.mp
      (Finsupp.support_single_subset hrj)
    have hi' : i < p := Finset.mem_range.mp hi
    have hmn' : m + 1 ≤ n := Nat.succ_le_of_lt hmn
    have hleft : p * m + i < p * (m + 1) := by
      rw [Nat.mul_succ]
      omega
    have hmiddle : p * (m + 1) ≤ p * n := Nat.mul_le_mul_left p hmn'
    omega

private theorem jn_exists_strictMono_of_cofinal (P : ℕ → Prop)
    (hP : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ n, P (u n) := by
  classical
  let u : ℕ → ℕ := Nat.rec (Classical.choose (hP 0))
    (fun _ previous => Classical.choose (hP (previous + 1)))
  have huP : ∀ n, P (u n) := by
    intro n
    cases n with
    | zero => exact (Classical.choose_spec (hP 0)).2
    | succ n => exact (Classical.choose_spec (hP (u n + 1))).2
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    exact Nat.lt_of_succ_le (Classical.choose_spec (hP (u n + 1))).1
  exact ⟨u, strictMono_nat_of_lt_succ hstep, huP⟩

private def jnWholeGroupIndex (p : ℕ) (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  p * u (n / p) + n % p

private theorem jn_wholeGroupIndex_strictMono {p : ℕ} (hp : 0 < p)
    {u : ℕ → ℕ} (hu : StrictMono u) :
    StrictMono (jnWholeGroupIndex p u) := by
  intro m n hmn
  have hdiv : m / p ≤ n / p := Nat.div_le_div_right hmn.le
  rcases hdiv.eq_or_lt with hdiv | hdiv
  · have hm : p * (m / p) + m % p = m := by
      simpa [Nat.mul_comm] using Nat.div_add_mod m p
    have hn : p * (n / p) + n % p = n := by
      simpa [Nat.mul_comm] using Nat.div_add_mod n p
    have hmod : m % p < n % p := by
      rw [hdiv] at hm
      omega
    unfold jnWholeGroupIndex
    rw [hdiv]
    exact Nat.add_lt_add_left hmod _
  · have hu' : u (m / p) < u (n / p) := hu hdiv
    have hmmod : m % p < p := Nat.mod_lt m hp
    unfold jnWholeGroupIndex
    have hleft : p * u (m / p) + m % p < p * (u (m / p) + 1) := by
      rw [Nat.mul_succ]
      omega
    have hmiddle : p * (u (m / p) + 1) ≤ p * u (n / p) :=
      Nat.mul_le_mul_left p hu'
    omega

private noncomputable def jnWholeGroupBlocking (p : ℕ) (hp : 0 < p)
    (u : ℕ → ℕ) (hu : StrictMono u) : JnBlocking :=
  jnSubsequenceBlocking (jnWholeGroupIndex p u)
    (jn_wholeGroupIndex_strictMono hp hu)

@[simp] private theorem jn_blockApply_wholeGroup
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (p : ℕ) (hp : 0 < p) (u : ℕ → ℕ) (hu : StrictMono u)
    (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnWholeGroupBlocking p hp u hu) x n =
      x (jnWholeGroupIndex p u n) := by
  exact jn_blockApply_subsequence _ _ _ _

private theorem jn_wholeGroupIndex_nested
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (u : ℕ → ℕ)
    (n i : ℕ) (hi : i < p) :
    jnWholeGroupIndex (p * q) u (p * n + i) =
      p * (q * u (n / q) + n % q) + i := by
  have hrem : p * (n % q) + i < p * q := by
    have hnmod : n % q < q := Nat.mod_lt n hq
    have hleft : p * (n % q) + i < p * (n % q + 1) := by
      rw [Nat.mul_succ]
      omega
    have hright : p * (n % q + 1) ≤ p * q :=
      Nat.mul_le_mul_left p hnmod
    exact hleft.trans_le hright
  have hrepr : p * (n % q) + i + (p * q) * (n / q) = p * n + i := by
    have hn := Nat.mod_add_div n q
    calc
      p * (n % q) + i + (p * q) * (n / q) =
          p * (n % q + q * (n / q)) + i := by ring
      _ = p * n + i := by rw [hn]
  have hdivmod := (Nat.div_mod_unique (Nat.mul_pos hp hq)).2 ⟨hrepr, hrem⟩
  unfold jnWholeGroupIndex
  rw [hdivmod.1, hdivmod.2]
  ring

private abbrev JnBoundedSeq := BoundedContinuousFunction ℕ ℝ

private noncomputable def jnShift (d : ℕ) (f : JnBoundedSeq) : JnBoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => f (n + d)) ‖f‖ (fun n => f.norm_coe_le_norm (n + d))

@[simp] private theorem jn_shift_apply (d : ℕ) (f : JnBoundedSeq) (n : ℕ) :
    jnShift d f n = f (n + d) := rfl

private def jnRademacher (k : ℕ) : JnBoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (-1 : ℝ) ^ (n / 2 ^ k)) 1 (fun n => by simp)

@[simp] private theorem jn_rademacher_apply (k n : ℕ) :
    jnRademacher k n = (-1 : ℝ) ^ (n / 2 ^ k) := rfl

private theorem jn_banach_shift
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (f : JnBoundedSeq) (d : ℕ) : L f = L (jnShift d f) := by
  induction d with
  | zero =>
      congr 1
  | succ d ih =>
      rw [ih]
      apply hshift
      intro n
      simp only [jn_shift_apply]
      congr 1
      omega

private theorem jn_rademacher_shift_self (k n : ℕ) :
    jnRademacher k (n + 2 ^ k) = -jnRademacher k n := by
  simp only [jn_rademacher_apply]
  rw [Nat.add_div_right n (by positivity : 0 < 2 ^ k)]
  rw [pow_succ]
  ring

private theorem jn_rademacher_shift_of_lt {i k : ℕ} (hik : i < k) (n : ℕ) :
    jnRademacher i (n + 2 ^ k) = jnRademacher i n := by
  have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_of_le hik.le]
  have heven : Even (2 ^ (k - i)) :=
    Nat.even_pow.mpr ⟨even_two, Nat.sub_ne_zero_of_lt hik⟩
  simp only [jn_rademacher_apply, hpow]
  rw [Nat.add_mul_div_left n (2 ^ (k - i)) (by positivity : 0 < 2 ^ i)]
  rw [pow_add, heven.neg_one_pow, mul_one]

private theorem jn_rademacher_period (k m i : ℕ) :
    jnRademacher k (2 ^ (k + 1) * m + i) = jnRademacher k i := by
  have hindex : 2 ^ (k + 1) * m + i = i + 2 ^ k * (2 * m) := by
    rw [pow_succ]
    ring
  rw [hindex]
  simp only [jn_rademacher_apply]
  rw [Nat.add_mul_div_left i (2 * m) (by positivity : 0 < 2 ^ k), pow_add]
  have heven : Even (2 * m) := even_two_mul m
  rw [heven.neg_one_pow, mul_one]

private theorem jn_rademacher_group_norm (k : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (k + 1)),
        |((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)| = 1 := by
  have hp : (2 ^ (k + 1) : ℝ) ≠ 0 := by positivity
  have hr : ∀ i, |jnRademacher k i| = 1 := by
    intro i
    simp only [jn_rademacher_apply, abs_pow, abs_neg, abs_one, one_pow]
  simp_rw [abs_mul, abs_inv, hr, mul_one]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp [hp]

private noncomputable def jnRademacherBlocking (k : ℕ) : JnBlocking :=
  jnGroupedBlocking (2 ^ (k + 1))
    (fun i => (2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)
    (jn_rademacher_group_norm k)

private theorem jn_blockApply_rademacherBlocking
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (k : ℕ) (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnRademacherBlocking k) x n =
      ∑ i ∈ Finset.range (2 ^ (k + 1)),
        ((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i) •
          x (2 ^ (k + 1) * n + i) := by
  change Finsupp.linearCombination ℝ x
      (∑ i ∈ Finset.range (2 ^ (k + 1)),
        Finsupp.single (2 ^ (k + 1) * n + i)
          ((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private theorem jn_blockApply_rademacherBlocking_wholeGroup
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {k j : ℕ} (hkj : k ≤ j) (u : ℕ → ℕ) (hu : StrictMono u)
    (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply (jnWholeGroupBlocking (2 ^ (j + 1)) (by positivity) u hu) x) n =
      jnBlockApply (jnRademacherBlocking k) x
        (jnWholeGroupIndex (2 ^ (j - k)) u n) := by
  have hpow : 2 ^ (j + 1) = 2 ^ (k + 1) * 2 ^ (j - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [jn_blockApply_rademacherBlocking, jn_blockApply_rademacherBlocking]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jn_blockApply_wholeGroup]
  congr 2
  rw [hpow]
  exact jn_wholeGroupIndex_nested (by positivity) (by positivity) u n i
    (Finset.mem_range.mp hi)

private theorem jn_banach_rademacher_orthogonal
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (i j : ℕ) : L (jnRademacher i * jnRademacher j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [← hone]
    apply congrArg L
    ext n
    simp only [BoundedContinuousFunction.mul_apply, jn_rademacher_apply,
      BoundedContinuousFunction.const_apply]
    have : (-1 : ℝ) ^ (n / 2 ^ i) = 1 ∨ (-1 : ℝ) ^ (n / 2 ^ i) = -1 := by
      exact neg_one_pow_eq_or ℝ _
    rcases this with h | h <;> rw [h] <;> norm_num
  · simp only [hij, ite_false]
    have hlt : ∀ {a b : ℕ}, a < b → L (jnRademacher a * jnRademacher b) = 0 := by
      intro a b hab
      have hs := jn_banach_shift L hshift (jnRademacher a * jnRademacher b) (2 ^ b)
      have heq : jnShift (2 ^ b) (jnRademacher a * jnRademacher b) =
          -(jnRademacher a * jnRademacher b) := by
        ext n
        simp only [jn_shift_apply, BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.neg_apply]
        rw [jn_rademacher_shift_of_lt hab, jn_rademacher_shift_self]
        ring
      rw [heq, map_neg] at hs
      linarith
    rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hlt hijlt
    · rw [mul_comm]
      exact hlt hjilt

private theorem jn_banach_const
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (a : ℝ) : L (BoundedContinuousFunction.const ℕ a) = a := by
  have hconst : BoundedContinuousFunction.const ℕ a =
      a • BoundedContinuousFunction.const ℕ (1 : ℝ) := by
    ext n
    simp
  rw [hconst, map_smul, hone, smul_eq_mul, mul_one]

private noncomputable def jnBlockMean (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) : JnBoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * (n / p) + i))
    ‖f‖ (fun n => by
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
      have hsum : ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
          (p : ℝ) * ‖f‖ := by
        calc
          ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
              ∑ i ∈ Finset.range p, ‖f (p * (n / p) + i)‖ := norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range p, ‖f‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact f.norm_coe_le_norm _
          _ = (p : ℝ) * ‖f‖ := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpR]
      calc
        (p : ℝ)⁻¹ * ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
            (p : ℝ)⁻¹ * ((p : ℝ) * ‖f‖) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpR.le)
        _ = ‖f‖ := by field_simp)

@[simp] private theorem jn_blockMean_apply (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    jnBlockMean p hp f n =
      (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * (n / p) + i) := rfl

private theorem jn_blockMean_on_block (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n i : ℕ) (hi : i < p) :
    jnBlockMean p hp f (p * n + i) =
      (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, f (p * n + j) := by
  rw [jn_blockMean_apply, Nat.mul_add_div hp, Nat.div_eq_of_lt hi, Nat.add_zero]

private theorem jn_blockMean_sub_sum (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    ∑ i ∈ Finset.range p,
      (f - jnBlockMean p hp f) (p * n + i) = 0 := by
  simp only [BoundedContinuousFunction.sub_apply, Finset.sum_sub_distrib]
  have hmeans : ∑ i ∈ Finset.range p, jnBlockMean p hp f (p * n + i) =
      ∑ _i ∈ Finset.range p,
        ((p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, f (p * n + j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact jn_blockMean_on_block p hp f n i (Finset.mem_range.mp hi)
  rw [hmeans, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private def jnPartialSum (d : JnBoundedSeq) : ℕ → ℝ
  | 0 => 0
  | n + 1 => jnPartialSum d n + d n

private theorem jn_partialSum_add (d : JnBoundedSeq) (n r : ℕ) :
    jnPartialSum d (n + r) =
      jnPartialSum d n + ∑ i ∈ Finset.range r, d (n + i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, jnPartialSum, ih, Finset.sum_range_succ]
      ring

private theorem jn_partialSum_blocks (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    jnPartialSum (f - jnBlockMean p hp f) (p * n) = 0 := by
  induction n with
  | zero => simp [jnPartialSum]
  | succ n ih =>
      rw [Nat.mul_succ, jn_partialSum_add, ih, zero_add,
        jn_blockMean_sub_sum]

private noncomputable def jnBlockPrimitive (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) : JnBoundedSeq :=
  let d := f - jnBlockMean p hp f
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (jnPartialSum d) ((p : ℝ) * ‖d‖) (fun n => by
      let q := n / p
      let r := n % p
      have hr : r < p := Nat.mod_lt n hp
      have hn : p * q + r = n := by
        simpa [q, r, Nat.mul_comm] using Nat.div_add_mod n p
      have hsum := jn_partialSum_add d (p * q) r
      rw [jn_partialSum_blocks p hp f q] at hsum
      have heq : jnPartialSum d n = ∑ i ∈ Finset.range r, d (p * q + i) := by
        rw [← hn, hsum, zero_add]
      rw [heq]
      calc
        ‖∑ i ∈ Finset.range r, d (p * q + i)‖ ≤
            ∑ i ∈ Finset.range r, ‖d (p * q + i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range r, ‖d‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact d.norm_coe_le_norm _
        _ = (r : ℝ) * ‖d‖ := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (p : ℝ) * ‖d‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg d)
          exact_mod_cast hr.le)

@[simp] private theorem jn_blockPrimitive_apply (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    jnBlockPrimitive p hp f n =
      jnPartialSum (f - jnBlockMean p hp f) n := rfl

private theorem jn_blockPrimitive_coboundary (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) :
    jnShift 1 (jnBlockPrimitive p hp f) - jnBlockPrimitive p hp f =
      f - jnBlockMean p hp f := by
  ext n
  simp only [BoundedContinuousFunction.sub_apply, jn_shift_apply,
    jn_blockPrimitive_apply]
  rw [show n + 1 = n.succ from rfl, jnPartialSum]
  rw [BoundedContinuousFunction.sub_apply]
  ring

private theorem jn_banach_blockMean
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq) :
    L f = L (jnBlockMean p hp f) := by
  let g := jnBlockPrimitive p hp f
  have hs : L g = L (jnShift 1 g) := by
    apply hshift
    intro n
    rfl
  have hc := congrArg L (jn_blockPrimitive_coboundary p hp f)
  simp only [map_sub] at hc
  linarith

private theorem jn_banach_of_blockMeans
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    {δ : ℝ} (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq)
    (hmean : ∀ n, δ ≤ jnBlockMean p hp f n) :
    δ ≤ L f := by
  let c : JnBoundedSeq := BoundedContinuousFunction.const ℕ δ
  have hnonneg : ∀ n, 0 ≤ (jnBlockMean p hp f - c) n := by
    intro n
    simp only [BoundedContinuousFunction.sub_apply, sub_nonneg]
    exact hmean n
  have hL := hpos (jnBlockMean p hp f - c) hnonneg
  rw [map_sub, jn_banach_const L hone] at hL
  rw [jn_banach_blockMean L hshift p hp f]
  exact sub_nonneg.mp hL

private theorem jn_banach_of_positive_block_means
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    {δ : ℝ} (p : ℕ) (hp : 0 < p) (f : JnBoundedSeq)
    (hmean : ∀ n, 0 < n →
      δ ≤ (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * n + i)) :
    δ ≤ L f := by
  let g := jnShift p f
  have hg : ∀ n, δ ≤ jnBlockMean p hp g n := by
    intro n
    rw [jn_blockMean_apply]
    have hsum : ∑ i ∈ Finset.range p, g (p * (n / p) + i) =
        ∑ i ∈ Finset.range p, f (p * (n / p + 1) + i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [g, jn_shift_apply]
      congr 1
      ring
    rw [hsum]
    exact hmean (n / p + 1) (Nat.zero_lt_succ _)
  have hgf := jn_banach_of_blockMeans L hpos hone hshift p hp g hg
  rwa [← jn_banach_shift L hshift f p] at hgf

private theorem jn_banach_rademacher_bessel
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (f : JnBoundedSeq) (N : ℕ) :
    ∑ i ∈ Finset.range N, (L (jnRademacher i * f)) ^ 2 ≤ ‖f‖ ^ 2 := by
  let c : ℕ → ℝ := fun i => L (jnRademacher i * f)
  let b : JnBoundedSeq := ∑ i ∈ Finset.range N, c i • jnRademacher i
  have hfb : L (f * b) = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
    simp only [b, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [c]
    rw [mul_comm f, mul_comm (L (jnRademacher i * f))]
    exact (pow_two _).symm
  have hbb : L (b * b) = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
    calc
      L (b * b) = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          c i * c j * L (jnRademacher j * jnRademacher i) := by
        simp only [b, Finset.sum_mul, Finset.mul_sum, map_sum, map_smul,
          mul_smul_comm, smul_mul_assoc, smul_eq_mul]
        simp only [mul_assoc]
      _ = ∑ i ∈ Finset.range N, (c i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · rw [jn_banach_rademacher_orthogonal L hone hshift i i]
          simp [pow_two]
        · intro j hj hji
          rw [jn_banach_rademacher_orthogonal L hone hshift j i]
          simp only [hji, ite_false, mul_zero]
        · exact fun hnot => (hnot hi).elim
  have hsq : 0 ≤ L ((f - b) * (f - b)) := by
    apply hpos
    intro n
    simp only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply]
    exact mul_self_nonneg _
  have hsum_le : ∑ i ∈ Finset.range N, (c i) ^ 2 ≤ L (f * f) := by
    have hexpand : L ((f - b) * (f - b)) =
        L (f * f) - 2 * L (f * b) + L (b * b) := by
      have heq : (f - b) * (f - b) = f * f - (2 : ℝ) • (f * b) + b * b := by
        ext n
        simp only [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.sub_apply,
          BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        ring
      rw [heq, map_add, map_sub, map_smul]
      simp only [smul_eq_mul]
    rw [hexpand, hfb, hbb] at hsq
    linarith
  have hff : L (f * f) ≤ ‖f‖ ^ 2 := by
    let q : JnBoundedSeq := BoundedContinuousFunction.const ℕ (‖f‖ ^ 2) - f * f
    have hq : 0 ≤ L q := by
      apply hpos
      intro n
      simp only [q, BoundedContinuousFunction.sub_apply,
        BoundedContinuousFunction.const_apply, BoundedContinuousFunction.mul_apply,
        sub_nonneg]
      have habs : |f n| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm n
      simpa only [pow_two, abs_mul_abs_self] using
        (sq_le_sq₀ (abs_nonneg (f n)) (norm_nonneg f)).mpr habs
    simp only [q, map_sub, jn_banach_const L hone] at hq
    linarith
  simpa only [c] using hsum_le.trans hff

private theorem jn_banach_rademacher_tendsto_zero
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (f : JnBoundedSeq) :
    Filter.Tendsto (fun i => L (jnRademacher i * f)) Filter.atTop (nhds 0) := by
  let a : ℕ → ℝ := fun i => L (jnRademacher i * f)
  have hsquares : Summable (fun i => (a i) ^ 2) := by
    refine summable_of_sum_range_le (c := ‖f‖ ^ 2) (fun i => sq_nonneg (a i)) ?_
    intro N
    exact jn_banach_rademacher_bessel L hpos hone hshift f N
  have hsquare0 : Filter.Tendsto (fun i => (a i) ^ 2) Filter.atTop (nhds 0) :=
    hsquares.tendsto_atTop_zero
  have habs0 : Filter.Tendsto (fun i => |a i|) Filter.atTop (nhds 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp hsquare0 using 1
    · funext i
      simp only [Function.comp_apply, Real.sqrt_sq_eq_abs]
    · simp
  simpa only [a] using (tendsto_zero_iff_norm_tendsto_zero.mpr habs0)

private noncomputable def jnBoundedEval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R) : E →L[ℝ] JnBoundedSeq := by
  let F : E → JnBoundedSeq := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
      (fun n => (z n) x) (R * ‖x‖) (fun n => by
        exact (ContinuousLinearMap.le_opNorm (z n) x).trans
          (mul_le_mul_of_nonneg_right (hz n) (norm_nonneg x)))
  let f : E →ₗ[ℝ] JnBoundedSeq :=
    { toFun := F
      map_add' := fun x y => by
        ext n
        simp only [F, BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
          map_add, BoundedContinuousFunction.add_apply]
      map_smul' := fun c x => by
        ext n
        simp only [F, BoundedContinuousFunction.coe_ofNormedAddCommGroupDiscrete,
          map_smul, BoundedContinuousFunction.smul_apply, RingHom.id_apply] }
  exact f.mkContinuous R fun x => by
    apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    · exact mul_nonneg (le_trans (norm_nonneg (z 0)) (hz 0)) (norm_nonneg x)
    · intro n
      exact (ContinuousLinearMap.le_opNorm (z n) x).trans
        (mul_le_mul_of_nonneg_right (hz n) (norm_nonneg x))

@[simp] private theorem jn_boundedEval_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R)
    (x : E) (n : ℕ) : jnBoundedEval z R hz x n = (z n) x := rfl

private noncomputable def jnRademacherFunctional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : JnBoundedSeq →L[ℝ] ℝ) (z : ℕ → StrongDual ℝ E) (R : ℝ)
    (hz : ∀ n, ‖z n‖ ≤ R) (k : ℕ) : StrongDual ℝ E :=
  L.comp ((ContinuousLinearMap.mul ℝ JnBoundedSeq (jnRademacher k)).comp (jnBoundedEval z R hz))

@[simp] private theorem jn_rademacherFunctional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : JnBoundedSeq →L[ℝ] ℝ) (z : ℕ → StrongDual ℝ E) (R : ℝ)
    (hz : ∀ n, ‖z n‖ ≤ R) (k : ℕ) (x : E) :
    jnRademacherFunctional L z R hz k x = L (jnRademacher k * jnBoundedEval z R hz x) := rfl

private theorem jn_rademacher_block_mean_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R)
    (k n : ℕ) (x : E) :
    ((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (2 ^ (k + 1)),
          (jnRademacher k * jnBoundedEval z R hz x) (2 ^ (k + 1) * n + i) =
      jnBlockApply (jnRademacherBlocking k) z n x := by
  rw [jn_blockApply_rademacherBlocking]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    BoundedContinuousFunction.mul_apply, jn_boundedEval_apply]
  simp_rw [jn_rademacher_period]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem jn_rademacherFunctional_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R) (x : E) :
    Filter.Tendsto (fun k => jnRademacherFunctional L z R hz k x)
      Filter.atTop (nhds 0) := by
  simpa only [jn_rademacherFunctional_apply] using
    jn_banach_rademacher_tendsto_zero L hpos hone hshift (jnBoundedEval z R hz x)

private theorem jn_of_rademacher_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : JnBoundedSeq →L[ℝ] ℝ)
    (hpos : ∀ f : JnBoundedSeq, (∀ n, 0 ≤ f n) → 0 ≤ L f)
    (hone : L (BoundedContinuousFunction.const ℕ (1 : ℝ)) = 1)
    (hshift : ∀ (f g : JnBoundedSeq), (∀ n, g n = f (n + 1)) → L f = L g)
    (z : ℕ → StrongDual ℝ E) (R : ℝ) (hz : ∀ n, ‖z n‖ ≤ R)
    (δ : ℝ) (hδ : 0 < δ)
    (hlower : ∀ k, δ ≤ ‖jnRademacherFunctional L z R hz k‖) :
    ∃ (ψ : ℕ → StrongDual ℝ E), (∀ k, ‖ψ k‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun k => (ψ k) x) Filter.atTop (nhds (0 : ℝ)) := by
  let w : ℕ → StrongDual ℝ E := fun k => jnRademacherFunctional L z R hz k
  let ψ : ℕ → StrongDual ℝ E := fun k => ‖w k‖⁻¹ • w k
  refine ⟨ψ, ?_, ?_⟩
  · intro k
    have hwpos : 0 < ‖w k‖ := hδ.trans_le (hlower k)
    simp only [ψ, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (ne_of_gt hwpos)]
  · intro x
    have hw0 : Filter.Tendsto (fun k => (w k) x) Filter.atTop (nhds (0 : ℝ)) :=
      jn_rademacherFunctional_tendsto_zero L hpos hone hshift z R hz x
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero_norm (a := fun k => δ⁻¹ * ‖(w k) x‖)
    · intro k
      have hwpos : 0 < ‖w k‖ := hδ.trans_le (hlower k)
      have hcoef : ‖w k‖⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hwpos hδ).mpr (hlower k)
      simp only [ψ, smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), abs_abs]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg ((w k) x))
    · simpa only [norm_zero, mul_zero] using hw0.norm.const_mul δ⁻¹

private def JnL1Lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (x : ℕ → E) : Prop :=
  ∀ a : ℕ →₀ ℝ, c * a.sum (fun _ t => |t|) ≤
    ‖Finsupp.linearCombination ℝ x a‖

private theorem jn_block_preserves_l1_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} {x : ℕ → E} (hx : JnL1Lower c x) (b : JnBlocking) :
    JnL1Lower c (jnBlockApply b x) := by
  intro a
  have h := hx (Finsupp.linearCombination ℝ b.coeff a)
  have hnorm : (Finsupp.linearCombination ℝ b.coeff a).sum (fun _ t => |t|) =
      a.sum (fun _ t => |t|) := by
    change jnCoeffNorm (Finsupp.linearCombination ℝ b.coeff a) = jnCoeffNorm a
    rw [jn_coeffNorm_linearCombination b.coeff (jn_blocking_disjoint b)]
    simp_rw [b.norm_one, mul_one]
    rfl
  rw [Finsupp.linearCombination_linearCombination ℝ x b.coeff a] at h
  rw [hnorm] at h
  exact h

private theorem jn_l1Lower_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} {x : ℕ → E} (hx : JnL1Lower c x) (n : ℕ) :
    c ≤ ‖x n‖ := by
  simpa using hx (Finsupp.single n 1)

private theorem jn_block_preserves_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {x : ℕ → E} (hx : ∀ n, ‖x n‖ ≤ R) (b : JnBlocking) :
    ∀ n, ‖jnBlockApply b x n‖ ≤ R := by
  intro n
  rw [jnBlockApply, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ i ∈ (b.coeff n).support, b.coeff n i • x i‖ ≤
        ∑ i ∈ (b.coeff n).support, ‖b.coeff n i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ (b.coeff n).support, |b.coeff n i| * R := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
    _ = R := by
      rw [← Finset.sum_mul, ← Finsupp.sum, ← jnCoeffNorm, b.norm_one, one_mul]

private theorem jn_l1Lower_of_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E}
    (hx : MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted.HasUniformL1LowerBound
      (𝕜 := ℝ) x) :
    ∃ c : ℝ, 0 < c ∧ JnL1Lower c x := by
  obtain ⟨c, hc, hx⟩ := hx
  refine ⟨c, hc, fun a => ?_⟩
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Real.norm_eq_abs] using hx a

private theorem jn_blockApply_eval_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : JnBlocking) (z : ℕ → StrongDual ℝ E) (x : E) (n : ℕ) {ε : ℝ}
    (h : ∀ i ∈ (b.coeff n).support, ‖z i x‖ < ε) :
    ‖jnBlockApply b z n x‖ < ε := by
  rw [jnBlockApply, Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [sum_apply, smul_apply, smul_eq_mul]
  calc
    ‖∑ i ∈ (b.coeff n).support, b.coeff n i * z i x‖ ≤
        ∑ i ∈ (b.coeff n).support, ‖b.coeff n i * z i x‖ := norm_sum_le _ _
    _ = ∑ i ∈ (b.coeff n).support, |b.coeff n i| * ‖z i x‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Real.norm_eq_abs]
    _ < ∑ i ∈ (b.coeff n).support, |b.coeff n i| * ε := by
      apply Finset.sum_lt_sum_of_nonempty (jn_blocking_support_nonempty b n)
      intro i hi
      exact mul_lt_mul_of_pos_left (h i hi)
        (abs_pos.mpr (Finsupp.mem_support_iff.mp hi))
    _ = ε := by
      rw [← Finset.sum_mul, ← Finsupp.sum, ← jnCoeffNorm, b.norm_one, one_mul]

private def JnPointwiseNull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) : Prop :=
  ∀ x : E, Filter.Tendsto (fun n => z n x) Filter.atTop (nhds 0)

private def JnBlockStable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (z : ℕ → StrongDual ℝ E) : Prop :=
  ∀ b : JnBlocking, ∃ x : E, ‖x‖ ≤ 1 ∧
    ∀ N, ∃ n, N ≤ n ∧ δ ≤ ‖jnBlockApply b z n x‖

private theorem jn_blockStable_blockApply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (a : JnBlocking) : JnBlockStable δ (jnBlockApply a z) := by
  intro b
  obtain ⟨x, hx, hcofinal⟩ := hz (jnBlockingComp a b)
  refine ⟨x, hx, fun N => ?_⟩
  obtain ⟨n, hn, hgood⟩ := hcofinal N
  refine ⟨n, hn, ?_⟩
  rw [jn_blockApply_comp] at hgood
  exact hgood

private theorem jn_stable_rademacher_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    ∃ (x : E) (u : ℕ → ℕ), ‖x‖ ≤ 1 ∧ StrictMono u ∧
      ∀ n, δ ≤ jnBlockApply (jnRademacherBlocking k) z (u n) x := by
  classical
  obtain ⟨x, hx, hcofinal⟩ := hz (jnRademacherBlocking k)
  let a : ℕ → ℝ := fun n => jnBlockApply (jnRademacherBlocking k) z n x
  by_cases hpositive : ∀ N, ∃ n, N ≤ n ∧ δ ≤ a n
  · obtain ⟨u, hu, hgood⟩ := jn_exists_strictMono_of_cofinal _ hpositive
    exact ⟨x, u, hx, hu, hgood⟩
  · push Not at hpositive
    obtain ⟨N, hN⟩ := hpositive
    have hnegative : ∀ M, ∃ n, M ≤ n ∧ δ ≤ -a n := by
      intro M
      obtain ⟨n, hn, habs⟩ := hcofinal (max M N)
      have hnM : M ≤ n := (le_max_left _ _).trans hn
      have hnN : N ≤ n := (le_max_right _ _).trans hn
      refine ⟨n, hnM, ?_⟩
      change δ ≤ ‖a n‖ at habs
      have hlt : a n < δ := hN n hnN
      rcases le_total 0 (a n) with ha | ha
      · rw [Real.norm_eq_abs, abs_of_nonneg ha] at habs
        exact (not_lt_of_ge habs hlt).elim
      · simpa only [Real.norm_eq_abs, abs_of_nonpos ha] using habs
    obtain ⟨u, hu, hgood⟩ := jn_exists_strictMono_of_cofinal _ hnegative
    refine ⟨-x, u, by simpa using hx, hu, fun n => ?_⟩
    simpa only [map_neg] using hgood n

private structure JnStableRademacherStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (z : ℕ → StrongDual ℝ E) (k : ℕ) where
  x : E
  u : ℕ → ℕ
  norm_le : ‖x‖ ≤ 1
  strictMono : StrictMono u
  good : ∀ n, δ ≤ jnBlockApply (jnRademacherBlocking k) z (u n) x

private noncomputable def jnStableRademacherStepData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnStableRademacherStep δ z k := by
  let h := jn_stable_rademacher_step hz k
  let x := Classical.choose h
  let hrest := Classical.choose_spec h
  let u := Classical.choose hrest
  let hprops := Classical.choose_spec hrest
  exact ⟨x, u, hprops.1, hprops.2.1, hprops.2.2⟩

private noncomputable def jnStableBlockingChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) :
    ℕ → JnBlocking
  | 0 => jnIdBlocking
  | k + 1 =>
      let base := jnStableBlockingChain hz k
      let data := jnStableRademacherStepData (jn_blockStable_blockApply hz base) k
      jnBlockingComp base
        (jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity) data.u data.strictMono)

private noncomputable def jnStableStageData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnStableRademacherStep δ (jnBlockApply (jnStableBlockingChain hz k) z) k :=
  jnStableRademacherStepData
    (jn_blockStable_blockApply hz (jnStableBlockingChain hz k)) k

private noncomputable def jnStableStepBlocking
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    JnBlocking :=
  jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity)
    (jnStableStageData hz k).u (jnStableStageData hz k).strictMono

private theorem jn_stableBlockingChain_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k : ℕ) :
    jnStableBlockingChain hz (k + 1) =
      jnBlockingComp (jnStableBlockingChain hz k) (jnStableStepBlocking hz k) := by
  rfl

private theorem jn_stableBlockingChain_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (n : ℕ) :
    jnStableBlockingChain hz n = jnBlockingChain (jnStableStepBlocking hz) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [jn_stableBlockingChain_succ, jnBlockingChain, ih]

private theorem jn_stableBlockingChain_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (k d : ℕ) :
    jnStableBlockingChain hz (k + d) =
      jnBlockingComp (jnStableBlockingChain hz k)
        (jnBlockingTailChain (jnStableStepBlocking hz) k d) := by
  rw [jn_stableBlockingChain_eq, jn_stableBlockingChain_eq,
    jn_blockingChain_add]

private theorem jn_log2_monotone : Monotone Nat.log2 := by
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  · have hn : n ≠ 0 := by omega
    exact (Nat.le_log2 hn).2 ((Nat.log2_self_le hm).trans hmn)

private theorem jn_add_le_of_dvd_of_lt
    {p a b : ℕ} (hp : 0 < p) (ha : p ∣ a) (hb : p ∣ b) (hab : a < b) :
    a + p ≤ b := by
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨s, hs⟩ := hb
  rw [hs] at hab ⊢
  have hrs : r < s := (Nat.mul_lt_mul_left hp).mp hab
  rw [← Nat.mul_succ]
  exact Nat.mul_le_mul_left p hrs

private theorem jn_log2_group_const (k n i : ℕ) (hn : 0 < n)
    (hi : i < 2 ^ (k + 1)) :
    Nat.log2 (2 ^ (k + 1) * n + i) =
      Nat.log2 (2 ^ (k + 1) * n) := by
  let p := 2 ^ (k + 1)
  let a := p * n
  let q := Nat.log2 a
  have hp : 0 < p := by simp [p]
  have ha : a ≠ 0 := Nat.mul_ne_zero hp.ne' hn.ne'
  have hq : k + 1 ≤ q := by
    apply (Nat.le_log2 ha).2
    exact Nat.le_mul_of_pos_right p hn
  have hupper : a + p ≤ 2 ^ (q + 1) := by
    apply jn_add_le_of_dvd_of_lt hp
    · exact dvd_mul_right p n
    · exact Nat.pow_dvd_pow 2 (hq.trans (Nat.le_succ q))
    · exact Nat.lt_log2_self
  apply (Nat.log2_eq_iff (by positivity : a + i ≠ 0)).2
  constructor
  · exact (Nat.log2_self_le ha).trans (Nat.le_add_right a i)
  · exact (Nat.add_lt_add_left hi a).trans_le hupper

private noncomputable def jnStableDiagonalBlocking
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) : JnBlocking where
  coeff n := (jnStableBlockingChain hz (Nat.log2 n)).coeff n
  norm_one n := (jnStableBlockingChain hz (Nat.log2 n)).norm_one n
  successive := by
    intro m n hmn i hi j hj
    have hlog : Nat.log2 m ≤ Nat.log2 n := jn_log2_monotone hmn.le
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlog
    have hchain : jnStableBlockingChain hz (Nat.log2 n) =
        jnBlockingComp (jnStableBlockingChain hz (Nat.log2 m))
          (jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d) := by
      rw [hd]
      exact jn_stableBlockingChain_add hz (Nat.log2 m) d
    rw [hchain] at hj
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset
        (jnStableBlockingChain hz (Nat.log2 m)).coeff
        ((jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d).coeff n) hj)
    have hnq : n ≤ q := jn_block_index_le_support
      (jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d) n q hq
    exact (jnStableBlockingChain hz (Nat.log2 m)).successive
      (hmn.trans_le hnq) i hi j hjq

private theorem jn_blockApply_stableDiagonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) (n : ℕ) :
    jnBlockApply (jnStableDiagonalBlocking hz) z n =
      jnBlockApply (jnStableBlockingChain hz (Nat.log2 n)) z n := by
  rfl

private theorem jn_rademacher_stableDiagonal_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (k n : ℕ) (hn : 0 < n) :
    jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply (jnStableDiagonalBlocking hz) z) n =
      jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply
          (jnStableBlockingChain hz (Nat.log2 (2 ^ (k + 1) * n))) z) n := by
  rw [jn_blockApply_rademacherBlocking, jn_blockApply_rademacherBlocking]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jn_blockApply_stableDiagonal,
    jn_log2_group_const k n i hn (Finset.mem_range.mp hi)]

private theorem jn_stableBlockingChain_good
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (k d n : ℕ) :
    δ ≤ jnBlockApply (jnRademacherBlocking k)
      (jnBlockApply (jnStableBlockingChain hz (k + 1 + d)) z) n
      (jnStableStageData hz k).x := by
  induction d generalizing n with
  | zero =>
      rw [Nat.add_zero, jn_stableBlockingChain_succ, jn_blockApply_comp_fun]
      change δ ≤ jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply
          (jnWholeGroupBlocking (2 ^ (k + 1)) (by positivity)
            (jnStableStageData hz k).u (jnStableStageData hz k).strictMono)
          (jnBlockApply (jnStableBlockingChain hz k) z)) n
        (jnStableStageData hz k).x
      rw [jn_blockApply_rademacherBlocking_wholeGroup (le_refl k)]
      simpa [jnWholeGroupIndex, Nat.mod_one] using (jnStableStageData hz k).good n
  | succ d ih =>
      let j := k + 1 + d
      have hindex : k + 1 + (d + 1) = j + 1 := by omega
      rw [hindex, jn_stableBlockingChain_succ, jn_blockApply_comp_fun]
      change δ ≤ jnBlockApply (jnRademacherBlocking k)
        (jnBlockApply
          (jnWholeGroupBlocking (2 ^ (j + 1)) (by positivity)
            (jnStableStageData hz j).u (jnStableStageData hz j).strictMono)
          (jnBlockApply (jnStableBlockingChain hz j) z)) n
        (jnStableStageData hz k).x
      rw [jn_blockApply_rademacherBlocking_wholeGroup (by omega)]
      exact ih (jnWholeGroupIndex (2 ^ (j - k)) (jnStableStageData hz j).u n)

private theorem jn_stableDiagonal_good
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z)
    (k n : ℕ) (hn : 0 < n) :
    δ ≤ jnBlockApply (jnRademacherBlocking k)
      (jnBlockApply (jnStableDiagonalBlocking hz) z) n
      (jnStableStageData hz k).x := by
  rw [jn_rademacher_stableDiagonal_eq hz k n hn]
  have hnonzero : 2 ^ (k + 1) * n ≠ 0 := by positivity
  have hstage : k + 1 ≤ Nat.log2 (2 ^ (k + 1) * n) := by
    apply (Nat.le_log2 hnonzero).2
    exact Nat.le_mul_of_pos_right _ hn
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hstage
  rw [hd]
  exact jn_stableBlockingChain_good hz k d n

private theorem jn_of_stable_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ R : ℝ} (hδ : 0 < δ) (z : ℕ → StrongDual ℝ E)
    (hzbound : ∀ n, ‖z n‖ ≤ R) (hz : JnBlockStable δ z) :
    ∃ (ψ : ℕ → StrongDual ℝ E), (∀ k, ‖ψ k‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun k => (ψ k) x) Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨L, hpos, hone, hshift, _⟩ :=
    MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit
  let b := jnStableDiagonalBlocking hz
  let y : ℕ → StrongDual ℝ E := jnBlockApply b z
  have hy : ∀ n, ‖y n‖ ≤ R := jn_block_preserves_bound hzbound b
  have hlower : ∀ k, δ ≤ ‖jnRademacherFunctional L y R hy k‖ := by
    intro k
    let x := (jnStableStageData hz k).x
    have hvalue : δ ≤ jnRademacherFunctional L y R hy k x := by
      rw [jn_rademacherFunctional_apply]
      apply jn_banach_of_positive_block_means L hpos hone hshift
        (2 ^ (k + 1)) (by positivity)
      intro n hn
      calc
        δ ≤ jnBlockApply (jnRademacherBlocking k) y n x := by
          simpa only [y, b, x] using jn_stableDiagonal_good hz k n hn
        _ = ((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ *
            ∑ i ∈ Finset.range (2 ^ (k + 1)),
              (jnRademacher k * jnBoundedEval y R hy x)
                (2 ^ (k + 1) * n + i) :=
          (jn_rademacher_block_mean_eval y R hy k n x).symm
    calc
      δ ≤ jnRademacherFunctional L y R hy k x := hvalue
      _ ≤ ‖jnRademacherFunctional L y R hy k x‖ := Real.le_norm_self _
      _ ≤ ‖jnRademacherFunctional L y R hy k‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖jnRademacherFunctional L y R hy k‖ * 1 :=
        mul_le_mul_of_nonneg_left (jnStableStageData hz k).norm_le (norm_nonneg _)
      _ = ‖jnRademacherFunctional L y R hy k‖ := mul_one _
  exact jn_of_rademacher_lower_bound L hpos hone hshift y R hy δ hδ hlower

private theorem jn_not_stable_small
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (h : ¬JnBlockStable δ z) :
    ∃ b : JnBlocking, ∀ x : E, ‖x‖ ≤ 1 →
      ∃ N, ∀ n, N ≤ n → ‖jnBlockApply b z n x‖ < δ := by
  unfold JnBlockStable at h
  push Not at h
  exact h

private theorem jn_stable_block_or_pointwise_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : ℕ → StrongDual ℝ E) :
    (∃ b : JnBlocking, JnPointwiseNull (jnBlockApply b z)) ∨
      ∃ (b : JnBlocking) (δ : ℝ), 0 < δ ∧
        JnBlockStable δ (jnBlockApply b z) := by
  classical
  by_cases hs : ∃ (b : JnBlocking) (δ : ℝ), 0 < δ ∧
      JnBlockStable δ (jnBlockApply b z)
  · exact Or.inr hs
  · left
    push Not at hs
    have hsmall : ∀ (base : JnBlocking) (q : ℕ),
        ∃ next : JnBlocking, ∀ x : E, ‖x‖ ≤ 1 →
          ∃ N, ∀ n, N ≤ n →
            ‖jnBlockApply next (jnBlockApply base z) n x‖ <
              1 / ((q : ℝ) + 1) := by
      intro base q
      exact jn_not_stable_small (hs base (1 / ((q : ℝ) + 1)) (by positivity))
    let next (base : JnBlocking) (q : ℕ) : JnBlocking :=
      Classical.choose (hsmall base q)
    let states : ℕ → JnBlocking := fun n =>
      Nat.rec jnIdBlocking (fun q base => jnBlockingComp base (next base q)) n
    let step : ℕ → JnBlocking := fun q => next (states q) q
    have hstates_zero : states 0 = jnIdBlocking := rfl
    have hstates_succ : ∀ q, states (q + 1) =
        jnBlockingComp (states q) (step q) := fun q => rfl
    have hstates_chain : ∀ q, states q = jnBlockingChain step q := by
      intro q
      induction q with
      | zero => rfl
      | succ q ih =>
          rw [show q + 1 = q.succ from rfl, hstates_succ q, jnBlockingChain, ih]
    let diagonal := jnDiagonalBlocking step
    refine ⟨diagonal, ?_⟩
    intro x
    by_cases hx : x = 0
    · subst x
      simpa only [map_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0))
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let y : E := ‖x‖⁻¹ • x
      have hy : ‖y‖ ≤ 1 := by
        have hy_eq : ‖y‖ = 1 := by
          simp [y, norm_smul, inv_mul_cancel₀ (ne_of_gt hxpos)]
        exact hy_eq.le
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨q, hq⟩ := exists_nat_one_div_lt (div_pos hε hxpos)
      have hnext := Classical.choose_spec (hsmall (states q) q) y hy
      obtain ⟨N, hN⟩ := hnext
      have hN' : ∀ i, N ≤ i →
          ‖jnBlockApply (states (q + 1)) z i y‖ < 1 / ((q : ℝ) + 1) := by
        intro i hi
        rw [hstates_succ, jn_blockApply_comp]
        exact hN i hi
      let M := max (q + 1) N
      refine ⟨M, fun n hn => ?_⟩
      have hqn : q + 1 ≤ n := (le_max_left _ _).trans hn
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hqn
      have hdiag := jn_blockApply_diagonal step z (q + 1) d
      rw [← hstates_chain (q + 1)] at hdiag
      have hsmall_diag : ‖jnBlockApply diagonal z n y‖ < 1 / ((q : ℝ) + 1) := by
        rw [hd]
        rw [hdiag]
        apply jn_blockApply_eval_lt
        intro i hi
        apply hN' i
        apply ((le_max_right _ _).trans hn).trans
        simpa only [hd] using
          (jn_block_index_le_support (jnBlockingTailChain step (q + 1) d)
            (q + 1 + d) i hi)
      rw [dist_zero_right]
      have hxy : x = ‖x‖ • y := by
        symm
        simp [y, smul_smul, mul_inv_cancel₀ (ne_of_gt hxpos)]
      have hfinal : ‖x‖ * ‖jnBlockApply diagonal z n y‖ < ε := by
        calc
        ‖x‖ * ‖jnBlockApply diagonal z n y‖ <
            ‖x‖ * (1 / ((q : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left hsmall_diag hxpos
        _ < ε := by
          have := mul_lt_mul_of_pos_left hq hxpos
          calc
            ‖x‖ * (1 / ((q : ℝ) + 1)) < ‖x‖ * (ε / ‖x‖) := this
            _ = ε := by
              rw [div_eq_mul_inv]
              calc
                ‖x‖ * (ε * ‖x‖⁻¹) = ε * (‖x‖ * ‖x‖⁻¹) := by ring
                _ = ε := by rw [mul_inv_cancel₀ hxpos.ne', mul_one]
      calc
        ‖‖jnBlockApply diagonal z n x‖‖ = ‖jnBlockApply diagonal z n x‖ := norm_norm _
        _ = ‖x‖ * ‖jnBlockApply diagonal z n y‖ := by
          have happ : jnBlockApply diagonal z n x =
              ‖x‖ • jnBlockApply diagonal z n y := by
            calc
              jnBlockApply diagonal z n x =
                  jnBlockApply diagonal z n (‖x‖ • y) :=
                congrArg (fun v : E => (jnBlockApply diagonal z n) v) hxy
              _ = ‖x‖ • jnBlockApply diagonal z n y :=
                (jnBlockApply diagonal z n).map_smul ‖x‖ y
          rw [happ, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (norm_nonneg x)]
        _ < ε := hfinal

private theorem jn_l1Lower_linearIndependent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) :
    LinearIndependent ℝ x := by
  rw [linearIndependent_iff]
  intro a ha
  have h := hx a
  rw [ha, norm_zero] at h
  have hsum_nonneg : 0 ≤ a.sum (fun _ t => |t|) := by
    apply Finsupp.sum_nonneg
    exact fun _ _ => abs_nonneg _
  have hsum : a.sum (fun _ t => |t|) = 0 := by nlinarith
  apply Finsupp.ext
  intro i
  by_cases hi : i ∈ a.support
  · have hall : ∀ j ∈ a.support, |a j| = 0 := by
      rw [← Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)]
      exact hsum
    exact abs_eq_zero.mp (hall i hi)
  · change a i = 0
    simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hi

private noncomputable def jnL1Basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) :
    Module.Basis ℕ ℝ ↑(Submodule.span ℝ (Set.range x)) :=
  Module.Basis.span (jn_l1Lower_linearIndependent hc hx)

private noncomputable def jnL1SignLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m : ℕ) :
    (Submodule.span ℝ (Set.range x)) →ₗ[ℝ] ℝ :=
  (jnL1Basis hc hx).constr ℝ (fun i => jnRademacher i m)

private theorem jn_l1SignLinearMap_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m : ℕ)
    (y : Submodule.span ℝ (Set.range x)) :
    ‖jnL1SignLinearMap hc hx m y‖ ≤ c⁻¹ * ‖y‖ := by
  let b := jnL1Basis hc hx
  let a : ℕ →₀ ℝ := b.repr y
  have hcomb : Finsupp.linearCombination ℝ x a = (y : E) := by
    have hsub : b.repr.symm a = y := b.repr.symm_apply_apply y
    have hval := congrArg Subtype.val hsub
    rw [Finsupp.linearCombination_apply]
    calc
      a.sum (fun i t => t • x i) = a.sum (fun i t => t • (b i : E)) := by
        apply Finsupp.sum_congr
        intro i hi
        simp only [b, jnL1Basis, Module.Basis.coe_span_apply]
      _ = ((a.sum (fun i t => t • b i) : Submodule.span ℝ (Set.range x)) : E) := by
        exact (map_finsuppSum (Submodule.span ℝ (Set.range x)).subtype a
          (fun i t => t • b i)).symm
      _ = (y : E) := by
        simpa only [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply] using hval
  have hsum : a.sum (fun _ t => |t|) ≤ c⁻¹ * ‖y‖ := by
    apply (le_inv_mul_iff₀ hc).mpr
    simpa only [hcomb, Submodule.norm_coe] using hx a
  calc
    ‖jnL1SignLinearMap hc hx m y‖ =
        |a.sum (fun i t => t * jnRademacher i m)| := by
      simp only [Real.norm_eq_abs, jnL1SignLinearMap, Module.Basis.constr_apply, a,
        b, smul_eq_mul]
    _ ≤ a.sum (fun _ t => |t|) := by
      rw [Finsupp.sum, Finsupp.sum]
      calc
        |∑ i ∈ a.support, a i * jnRademacher i m| ≤
            ∑ i ∈ a.support, |a i * jnRademacher i m| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ a.support, |a i| := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [abs_mul, jn_rademacher_apply, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    _ ≤ c⁻¹ * ‖y‖ := hsum

private noncomputable def jnL1SignFunctional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m : ℕ) :
    StrongDual ℝ ↑(Submodule.span ℝ (Set.range x)) :=
  (jnL1SignLinearMap hc hx m).mkContinuous c⁻¹ (jn_l1SignLinearMap_bound hc hx m)

@[simp] private theorem jn_l1SignFunctional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m i : ℕ) :
    jnL1SignFunctional hc hx m
        ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ = jnRademacher i m := by
  simp only [jnL1SignFunctional, LinearMap.mkContinuous_apply, jnL1SignLinearMap]
  rw [show ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      jnL1Basis hc hx i by
    ext
    simp only [jnL1Basis, Module.Basis.coe_span_apply]]
  exact (jnL1Basis hc hx).constr_basis ℝ _ i

private noncomputable def jnL1Extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m : ℕ) :
    StrongDual ℝ E :=
  Classical.choose (exists_extension_norm_eq
    (Submodule.span ℝ (Set.range x)) (jnL1SignFunctional hc hx m))

@[simp] private theorem jn_l1Extension_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m i : ℕ) :
    jnL1Extension hc hx m (x i) = jnRademacher i m := by
  rw [show jnL1Extension hc hx m (x i) =
      jnL1SignFunctional hc hx m
        ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ by
    let y : Submodule.span ℝ (Set.range x) :=
      ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
    change Classical.choose (exists_extension_norm_eq
      (Submodule.span ℝ (Set.range x)) (jnL1SignFunctional hc hx m)) (y : E) =
        jnL1SignFunctional hc hx m y
    exact (Classical.choose_spec (exists_extension_norm_eq
      (Submodule.span ℝ (Set.range x)) (jnL1SignFunctional hc hx m))).1 y]
  exact jn_l1SignFunctional_apply hc hx m i

private theorem jn_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional ℝ E) :
    ∃ (ψ : ℕ → StrongDual ℝ E), (∀ n, ‖ψ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (ψ n) x) Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨R, z, hR, hzbound, hzsep⟩ := jn_exists_separated_dual_sequence hInf
  have hbounded : Bornology.IsBounded (Set.range z) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * R, fun m n => ?_⟩
    rw [dist_eq_norm]
    calc
      ‖z m - z n‖ ≤ ‖z m‖ + ‖z n‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hzbound m) (hzbound n)
      _ = 2 * R := by ring
  obtain ⟨u, hu, hweak | hlower⟩ :=
    MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted.rosenthal_l1
      (𝕜 := ℝ) (E := StrongDual ℝ E) z hbounded
  · apply jn_of_pointwise_cauchy_subsequence z hzsep u hu
    intro x
    apply Metric.cauchySeq_iff.2
    intro ε hε
    let f : StrongDual ℝ E →L[ℝ] ℝ :=
      NormedSpace.inclusionInDoubleDual ℝ E x
    obtain ⟨N, hN⟩ := hweak f ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [f, NormedSpace.dual_def, dist_eq_norm] using hN m n hm hn
  · obtain ⟨c, hc, hclower⟩ := jn_l1Lower_of_uniform hlower
    let y : ℕ → StrongDual ℝ E := z ∘ u
    have hybound : ∀ n, ‖y n‖ ≤ R := fun n => hzbound (u n)
    rcases jn_stable_block_or_pointwise_null y with hnull | hstable
    · obtain ⟨b, hbnull⟩ := hnull
      let w : ℕ → StrongDual ℝ E := jnBlockApply b y
      have hwlower : ∀ n, c ≤ ‖w n‖ :=
        jn_l1Lower_norm (jn_block_preserves_l1_lower hclower b)
      exact jn_of_lower_bounded_pointwise_null w c hc hwlower hbnull
    · obtain ⟨b, δ, hδ, hbstable⟩ := hstable
      let w : ℕ → StrongDual ℝ E := jnBlockApply b y
      have hwbound : ∀ n, ‖w n‖ ≤ R := jn_block_preserves_bound hybound b
      exact jn_of_stable_block hδ w hwbound hbstable


/--
**Josefson–Nissenzweig theorem.** Let $E$ be an infinite-dimensional Banach space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then there is a sequence $(\varphi_n)_{n \in \mathbb{N}}$
of continuous linear functionals on $E$ with $\|\varphi_n\| = 1$ for every $n$ such that
$\varphi_n(x) \to 0$ for every $x \in E$; that is, the unit sphere of the dual of $E$ contains a
weak-star null sequence.

Proof: We apply Rosenthal's `ℓ¹` dichotomy to a separated dual sequence, then use the stable-block
and Banach-limit/Rademacher route of Hagler--Johnson (1977) and Behrends (1995).

Proves `Wanted` entry `josefson_nissenzweig`.

Source: B. Josefson, Weak sequential convergence in the
dual of a Banach space does not imply norm convergence, Bull. Amer. Math. Soc. 81 (1975),
166–168, DOI 10.1090/S0002-9904-1975-13691-3; and A. Nissenzweig, w* sequential convergence,
Israel J. Math. 22 (1975), 266–272, DOI 10.1007/BF02761594, Josefson-Nissenzweig theorem;
Diestel, Sequences and Series; Lean states `RCLike` infinite-dimensional Banach case with
`‖φ n‖=1` and pointwise weak-star nullness.
-/
theorem josefson_nissenzweig
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (hInf : ¬ FiniteDimensional 𝕜 E) :
    ∃ (φ : ℕ → StrongDual 𝕜 E), (∀ n, ‖φ n‖ = 1) ∧
      ∀ x : E, Filter.Tendsto (fun n => (φ n) x) Filter.atTop (nhds (0 : 𝕜)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  exact jn_rclike_of_real hInf jn_real

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
