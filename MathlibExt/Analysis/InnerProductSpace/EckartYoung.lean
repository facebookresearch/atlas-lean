/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.EckartYoungWanted

/-- Master identity: expanding `T` on the eigenbasis of `T* ∘ T`, the squared norm
of a linear combination of the images is the eigenvalue-weighted sum. -/
private theorem norm_sq_sum_smul_image
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (n : ℕ) (hn : Module.finrank 𝕜 E = n)
    (d : Fin n → 𝕜) :
    ‖∑ i, d i • T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i)‖ ^ 2 =
      ∑ i, (T.isSymmetric_adjoint_comp_self.eigenvalues hn) i * ‖d i‖ ^ 2 := by
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn with hb
  set ev := T.isSymmetric_adjoint_comp_self.eigenvalues hn with hev
  have hA : ∀ j, (LinearMap.adjoint T ∘ₗ T) (b j) = (ev j : 𝕜) • b j :=
    fun j => LinearMap.IsSymmetric.apply_eigenvectorBasis _ hn j
  have hpair : ∀ i j : Fin n,
      inner 𝕜 (T (b i)) (T (b j)) = (ev j : 𝕜) * (if i = j then (1 : 𝕜) else 0) := by
    intro i j
    have h : inner 𝕜 (T (b i)) (T (b j)) = inner 𝕜 (b i) ((LinearMap.adjoint T ∘ₗ T) (b j)) :=
      (LinearMap.adjoint_inner_right T (b i) (T (b j))).symm
    rw [h, hA j, inner_smul_right, b.inner_eq_ite]
  have estep : ∀ i j : Fin n,
      (starRingEnd 𝕜) (d i) * (d j * ((ev j : 𝕜) * (if i = j then (1 : 𝕜) else 0)))
        = (if i = j then (starRingEnd 𝕜) (d i) * (d i * (ev i : 𝕜)) else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij]
  have hcollapse : ∀ i : Fin n,
      (∑ j, (starRingEnd 𝕜) (d i) * (d j * ((ev j : 𝕜) *
        (if i = j then (1 : 𝕜) else 0)))) = ((ev i * ‖d i‖ ^ 2 : ℝ) : 𝕜) := by
    intro i
    simp_rw [estep i]
    rw [Finset.sum_ite_eq _ _ _]
    simp only [Finset.mem_univ, ite_true]
    have hc : (starRingEnd 𝕜) (d i) * d i = ((‖d i‖ ^ 2 : ℝ) : 𝕜) := by
      have hcm := RCLike.conj_mul (d i)
      exact_mod_cast hcm
    calc (starRingEnd 𝕜) (d i) * (d i * (ev i : 𝕜))
        = (ev i : 𝕜) * ((starRingEnd 𝕜) (d i) * d i) := by ring
      _ = (ev i : 𝕜) * ((‖d i‖ ^ 2 : ℝ) : 𝕜) := by rw [hc]
      _ = ((ev i * ‖d i‖ ^ 2 : ℝ) : 𝕜) := by rw [RCLike.ofReal_mul]
  have step1 : ∀ y : F, inner 𝕜 (∑ i, d i • T (b i)) (y)
      = ∑ i, (starRingEnd 𝕜) (d i) * inner 𝕜 (T (b i)) (y) := by
    intro y
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_left]
  have hexpand : inner 𝕜 (∑ i, d i • T (b i)) (∑ j, d j • T (b j))
      = ((∑ i, (ev i * ‖d i‖ ^ 2 : ℝ) : ℝ) : 𝕜) := by
    rw [step1]
    simp only [inner_sum, inner_smul_right, Finset.mul_sum, hpair]
    simp only [hcollapse]
    rw [← map_sum]
  have hself : ((‖∑ i, d i • T (b i)‖ ^ 2 : ℝ) : 𝕜)
      = inner 𝕜 (∑ i, d i • T (b i)) (∑ i, d i • T (b i)) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact_mod_cast rfl
  exact RCLike.ofReal_injective (hself.trans hexpand)

/-- Upper bound: the rank-`k` truncation `S` of `T` satisfies `‖T - S‖ ≤ σ_k`. -/
private theorem upper_bound
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (k : ℕ) :
    ∃ S : E →ₗ[𝕜] F, Module.finrank 𝕜 S.range ≤ k ∧
      ‖(T - S).toContinuousLinearMap‖ ≤ T.singularValues k := by
  set n := Module.finrank 𝕜 E with hn_def
  have hn : Module.finrank 𝕜 E = n := rfl
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn with hb
  set ev := T.isSymmetric_adjoint_comp_self.eigenvalues hn with hev
  have hev_eq : ∀ i : Fin n, ev i = T.singularValues i.val ^ 2 :=
    fun i => (LinearMap.sq_singularValues_of_lt T hn i.isLt).symm
  have hanti := T.singularValues_antitone
  set S : E →ₗ[𝕜] F := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
    (((innerSL 𝕜) (b i)).toLinearMap).smulRight (T (b i)) with hSdef
  have hSx : ∀ x : E, S x = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
      inner 𝕜 (b i) (x) • T (b i) := by
    intro x
    rw [hSdef, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.smulRight_apply]
    congr 1
  have hTx : ∀ x : E, T x = ∑ i, inner 𝕜 (b i) (x) • T (b i) := by
    intro x
    conv_lhs => rw [← b.sum_repr' x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hTS : ∀ x : E, (T - S) x =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < k),
        inner 𝕜 (b i) (x) • T (b i) := by
    intro x
    rw [LinearMap.sub_apply, hTx x, hSx x]
    have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k) (fun i => inner 𝕜 (b i) (x) • T (b i))
    rw [← hpart, add_sub_cancel_left]
  have hBeq : ∀ x : E, (T - S) x
      = ∑ i, (if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x)) • T (b i) := by
    intro x
    rw [hTS x]
    have e1 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < k),
          inner 𝕜 (b i) (x) • T (b i))
        = ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < k),
          (if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x)) • T (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [ite_eq_right hi]
    have e2 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val < k),
          (if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x)) • T (b i))
        = ∑ i, (if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x)) • T (b i) :=
      Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        rw [ite_eq_left hi, zero_smul])
    rw [e1, e2]
  have hBnorm : ∀ x : E, ‖(T - S) x‖ ^ 2
      = ∑ i, ev i * ‖(if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x))‖ ^ 2 := by
    intro x
    rw [hBeq x]
    exact norm_sq_sum_smul_image 𝕜 E F T n hn _
  have hterm : ∀ x : E, ∀ i : Fin n,
      ev i * ‖(if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x))‖ ^ 2
        ≤ T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
    intro x i
    by_cases hi : i.val < k
    · rw [ite_eq_left hi, norm_zero, zero_pow two_ne_zero, mul_zero]
      positivity
    · rw [ite_eq_right hi]
      have hki : k ≤ i.val := not_lt.mp hi
      have hσ : T.singularValues i.val ≤ T.singularValues k := hanti hki
      have hnn : (0 : ℝ) ≤ T.singularValues i.val := T.singularValues_nonneg _
      rw [hev_eq i]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ hnn hσ 2
  have hsum : ∀ x : E,
      (∑ i, ev i * ‖(if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x))‖ ^ 2)
        ≤ T.singularValues k ^ 2 * ‖x‖ ^ 2 := by
    intro x
    calc ∑ i, ev i * ‖(if i.val < k then (0 : 𝕜) else inner 𝕜 (b i) (x))‖ ^ 2
        ≤ ∑ i, T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => hterm x i)
      _ = T.singularValues k ^ 2 * ∑ i, ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ = T.singularValues k ^ 2 * ‖x‖ ^ 2 := by
          rw [b.sum_sq_norm_inner_right x]
  have hpoint : ∀ x : E, ‖(T - S) x‖ ≤ T.singularValues k * ‖x‖ := by
    intro x
    have h2 : ‖(T - S) x‖ ^ 2 ≤ (T.singularValues k * ‖x‖) ^ 2 := by
      rw [hBnorm x, mul_pow]
      exact hsum x
    exact le_of_sq_le_sq h2
      (mul_nonneg (T.singularValues_nonneg k) (norm_nonneg x))
  have hop : ‖(T - S).toContinuousLinearMap‖ ≤ T.singularValues k := by
    apply ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg k)
    exact hpoint
  have hrank : Module.finrank 𝕜 S.range ≤ k := by
    set w : Fin k → F := fun j =>
      if h : j.val < n then T (b ⟨j.val, h⟩) else 0 with hw
    have hle : S.range ≤ Submodule.span 𝕜 (Set.range w) := by
      intro y hy
      rw [LinearMap.mem_range] at hy
      obtain ⟨x, rfl⟩ := hy
      rw [hSx x]
      apply Submodule.sum_mem
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      apply Submodule.smul_mem _ _ _
      have h2 : w ⟨i.val, hi⟩ = T (b i) := by
        rw [hw]
        change (if h : i.val < n then T (b ⟨i.val, h⟩) else (0 : F)) = _
        rw [dite_eq_left i.isLt]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, h2⟩
    calc Module.finrank 𝕜 S.range
        ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range w)) :=
          Submodule.finrank_mono hle
      _ = (Set.range w).finrank 𝕜 := rfl
      _ ≤ k := le_trans (finrank_range_le_card w) (by simp)
  exact ⟨S, hrank, hop⟩

/-- Lower bound: every rank-`k` map `S` satisfies `σ_k ≤ ‖T - S‖`. -/
private theorem lower_bound
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (k : ℕ)
    (S : E →ₗ[𝕜] F) (hS : Module.finrank 𝕜 S.range ≤ k) :
    T.singularValues k ≤ ‖(T - S).toContinuousLinearMap‖ := by
  by_cases hkn : k < Module.finrank 𝕜 E
  · set n := Module.finrank 𝕜 E with hn_def
    have hn : Module.finrank 𝕜 E = n := rfl
    have hkn' : k + 1 ≤ n := hkn
    set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn with hb
    set ev := T.isSymmetric_adjoint_comp_self.eigenvalues hn with hev
    have hev_eq : ∀ i : Fin n, ev i = T.singularValues i.val ^ 2 :=
      fun i => (LinearMap.sq_singularValues_of_lt T hn i.isLt).symm
    have hanti := T.singularValues_antitone
    have hTx : ∀ x : E, T x = ∑ i, inner 𝕜 (b i) (x) • T (b i) := by
      intro x
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
    set m : Fin (n - (k + 1)) → Fin n :=
      fun j => ⟨k + 1 + j.val, by have h := j.isLt; omega⟩ with hm
    set Q : E →ₗ[𝕜] (Fin (n - (k + 1)) → 𝕜) :=
      LinearMap.pi (fun j => ((innerSL 𝕜) (b (m j))).toLinearMap) with hQdef
    have hQapply : ∀ (x : E) (j : Fin (n - (k + 1))),
        Q x j = inner 𝕜 (b (m j)) (x) := by
      intro x j
      rw [hQdef, LinearMap.pi_apply]
      exact innerSL_apply_apply 𝕜 _ _
    have hQrank : Module.finrank 𝕜 Q.range ≤ n - (k + 1) := by
      have h1 : Module.finrank 𝕜 Q.range
          ≤ Module.finrank 𝕜 (Fin (n - (k + 1)) → 𝕜) := by
        have hmo := Submodule.finrank_mono (s := Q.range) (t := ⊤) le_top
        rwa [finrank_top] at hmo
      rw [Module.finrank_pi] at h1
      simpa [Fintype.card_fin] using h1
    have hQker : k + 1 ≤ Module.finrank 𝕜 Q.ker := by
      have hrn := LinearMap.finrank_range_add_finrank_ker Q
      rw [hn] at hrn
      omega
    have hSker : Module.finrank 𝕜 E - k ≤ Module.finrank 𝕜 S.ker := by
      have hrn := LinearMap.finrank_range_add_finrank_ker S
      omega
    have hU : 1 ≤ Module.finrank 𝕜 ↥(S.ker ⊓ Q.ker) := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq S.ker Q.ker
      have hle : Module.finrank 𝕜 ↥(S.ker ⊔ Q.ker) ≤ n := by
        have hmo := Submodule.finrank_mono (s := S.ker ⊔ Q.ker) (t := ⊤) le_top
        rwa [finrank_top, hn] at hmo
      omega
    have hUne : S.ker ⊓ Q.ker ≠ ⊥ := by
      intro hcon
      rw [hcon, finrank_bot] at hU
      omega
    obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    rw [Submodule.mem_inf] at hxmem
    obtain ⟨hxS, hxQ⟩ := hxmem
    have hSx0 : S x = 0 := LinearMap.mem_ker.mp hxS
    have hQx0 : Q x = 0 := LinearMap.mem_ker.mp hxQ
    have hvan : ∀ i : Fin n, k + 1 ≤ i.val → inner 𝕜 (b i) (x) = 0 := by
      intro i hi
      have h0 : Q x ⟨i.val - (k + 1), by omega⟩ = 0 := by rw [hQx0]; rfl
      rw [hQapply] at h0
      have hvv : k + 1 + (i.val - (k + 1)) = i.val := by omega
      have hmi : m ⟨i.val - (k + 1), by omega⟩ = i := Fin.ext hvv
      rw [hmi] at h0
      exact h0
    have hTSx : (T - S) x = T x := by rw [LinearMap.sub_apply, hSx0, sub_zero]
    have hTnorm : ‖T x‖ ^ 2 = ∑ i, ev i * ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
      conv_lhs => rw [hTx x]
      exact norm_sq_sum_smul_image 𝕜 E F T n hn _
    have hvan_sum : (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ i.val ≤ k),
          T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h0 : inner 𝕜 (b i) (x) = 0 := hvan i (by omega)
      simp [h0]
    have hPx : T.singularValues k ^ 2 * ‖x‖ ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k),
          T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
      have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n => i.val ≤ k)
        (fun i => T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2)
      calc T.singularValues k ^ 2 * ‖x‖ ^ 2
          = ∑ i, T.singularValues k ^ 2 * ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
            rw [← b.sum_sq_norm_inner_right x, Finset.mul_sum]
        _ = _ := by rw [← hpart, hvan_sum, add_zero]
    have hsplit : (∑ i, ev i * ‖inner 𝕜 (b i) (x)‖ ^ 2)
        = ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k),
          ev i * ‖inner 𝕜 (b i) (x)‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hni
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hni
      have h0 : inner 𝕜 (b i) (x) = 0 := hvan i (by omega)
      simp [h0]
    have hlow : T.singularValues k ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
      rw [hTnorm, hsplit, hPx]
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hσ : T.singularValues k ≤ T.singularValues i.val := hanti hi
      have hnn : (0 : ℝ) ≤ T.singularValues k := T.singularValues_nonneg _
      rw [hev_eq i]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ hnn hσ 2
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hle : T.singularValues k * ‖x‖
        ≤ ‖(T - S).toContinuousLinearMap‖ * ‖x‖ := by
      have h1 : T.singularValues k * ‖x‖ ≤ ‖(T - S) x‖ := by
        have h2 : (T.singularValues k * ‖x‖) ^ 2 ≤ ‖(T - S) x‖ ^ 2 := by
          rw [mul_pow, hTSx]
          exact hlow
        exact le_of_sq_le_sq h2 (norm_nonneg _)
      have h3 : ‖(T - S) x‖ ≤ ‖(T - S).toContinuousLinearMap‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm (T - S).toContinuousLinearMap x
      exact le_trans h1 h3
    exact le_of_mul_le_mul_right hle hxpos
  · have hle : Module.finrank 𝕜 E ≤ k := not_lt.mp hkn
    have h0 : T.singularValues k = 0 := T.singularValues_of_finrank_le hle
    rw [h0]
    exact norm_nonneg _

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/--
**Eckart–Young theorem in operator norm.** Let $E$ and $F$ be finite-dimensional inner product
spaces over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T : E \to F$ be a linear map and let
$k \ge 0$ be an integer. The infimum of the operator norms $\|T - S\|$ over all linear maps
$S : E \to F$ whose range has dimension at most $k$ equals $\sigma_k(T)$, where
$\sigma_0(T) \ge \sigma_1(T) \ge \cdots$ are the singular values of $T$ listed with multiplicity
and indexed from $0$, and $\sigma_j(T) = 0$ for $j \ge \dim E$.

Proves `Wanted` entry `eckartYoung_best_rank_approx_operator_norm`.

Source: C. Eckart and G. Young, The Approximation of One Matrix by Another of Lower Rank,
Psychometrika 1 (1936), 211-218, DOI 10.1007/BF02288367; unitary-invariant extension L. Mirsky, QJM
11 (1960), DOI 10.1093/qmath/11.1.50.
-/
theorem eckartYoung_best_rank_approx_operator_norm
    (T : E →ₗ[𝕜] F) (k : ℕ) :
    sInf
        { r : ℝ |
          ∃ S : E →ₗ[𝕜] F,
            Module.finrank 𝕜 S.range ≤ k ∧
              r = ‖(T - S).toContinuousLinearMap‖ } =
      T.singularValues k := by
  have hbdd : BddBelow { r : ℝ | ∃ S : E →ₗ[𝕜] F,
      Module.finrank 𝕜 S.range ≤ k ∧
        r = ‖(T - S).toContinuousLinearMap‖ } := by
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨S, -, rfl⟩ := hr
    exact norm_nonneg _
  apply le_antisymm
  · obtain ⟨S₀, hS₀r, hS₀n⟩ := upper_bound 𝕜 E F T k
    have hmem : ‖(T - S₀).toContinuousLinearMap‖ ∈ { r : ℝ |
        ∃ S : E →ₗ[𝕜] F,
          Module.finrank 𝕜 S.range ≤ k ∧
            r = ‖(T - S).toContinuousLinearMap‖ } :=
      ⟨S₀, hS₀r, rfl⟩
    exact le_trans (csInf_le hbdd hmem) hS₀n
  · apply le_csInf
    · refine ⟨_, ⟨0, ?_, rfl⟩⟩
      rw [LinearMap.range_zero, finrank_bot]
      exact Nat.zero_le k
    · intro b hb
      obtain ⟨S, hSr, rfl⟩ := hb
      exact lower_bound 𝕜 E F T k S hSr

end MathlibExt.Analysis.InnerProductSpace.EckartYoungWanted
