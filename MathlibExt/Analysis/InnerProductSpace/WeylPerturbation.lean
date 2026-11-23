/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Weyl perturbation inequality

Weyl's Hermitian eigenvalue perturbation inequality.

Source: H. Weyl, Math. Ann. 71 (1912), DOI 10.1007/BF01456804;
Horn-Johnson Matrix Analysis (modern reference).
-/

section

namespace MathlibExt.Analysis.InnerProductSpace.WeylPerturbationWanted

open Matrix

private lemma expand_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (v : ι' → E) (ev : ι' → ℝ)
    (T : E →ₗ[ℂ] E)
    (hTv : ∀ j, T (v j) = ((ev j : ℝ) : ℂ) • v j)
    (horth : ∀ j k, inner ℂ (v j) (v k) = if j = k then 1 else 0)
    (r : ι' → ℂ) (x : E) (hx : x = ∑ j, r j • v j) :
    inner ℂ (T x) x =
      ∑ j, ((ev j : ℝ) : ℂ) * ((starRingEnd ℂ) (r j) * r j) := by
  have hTx : T x = ∑ j, (r j * ((ev j : ℝ) : ℂ)) • v j := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_smul, hTv j, ← mul_smul]
  rw [hTx, hx, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  simp_rw [inner_smul_left, inner_smul_right, horth, map_mul, Complex.conj_ofReal,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

private lemma re_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (v : ι' → E) (ev : ι' → ℝ)
    (T : E →ₗ[ℂ] E)
    (hTv : ∀ j, T (v j) = ((ev j : ℝ) : ℂ) • v j)
    (horth : ∀ j k, inner ℂ (v j) (v k) = if j = k then 1 else 0)
    (r : ι' → ℂ) (x : E) (hx : x = ∑ j, r j • v j) :
    RCLike.re (inner ℂ (T x) x) =
      ∑ j, ev j * RCLike.re ((starRingEnd ℂ) (r j) * r j) := by
  rw [expand_inner v ev T hTv horth r x hx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [RCLike.mul_re]

private lemma w_nonneg (w : ℂ) : 0 ≤ RCLike.re ((starRingEnd ℂ) w * w) := by
  rw [mul_comm ((starRingEnd ℂ) w) w, ← RCLike.inner_apply]
  exact inner_self_nonneg

private lemma norm_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (v : ι' → E)
    (horth : ∀ j k, inner ℂ (v j) (v k) = if j = k then 1 else 0)
    (r : ι' → ℂ) (x : E) (hx : x = ∑ j, r j • v j) :
    ‖x‖ ^ 2 = ∑ j, RCLike.re ((starRingEnd ℂ) (r j) * r j) := by
  have hTv : ∀ j, (LinearMap.id : E →ₗ[ℂ] E) (v j) = (((1 : ℝ)) : ℂ) • v j := by
    intro j
    rw [LinearMap.id_apply, Complex.ofReal_one, one_smul]
  have h1 := re_expand v (fun _ => 1) _ hTv horth r x hx
  simp only [one_mul] at h1
  rw [LinearMap.id_apply] at h1
  rw [← h1]
  exact norm_sq_eq_re_inner x

private lemma head_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (v : ι' → E) (ev : ι' → ℝ)
    (T : E →ₗ[ℂ] E)
    (hTv : ∀ j, T (v j) = ((ev j : ℝ) : ℂ) • v j)
    (horth : ∀ j k, inner ℂ (v j) (v k) = if j = k then 1 else 0)
    (c : ℝ) (x : E) (r : ι' → ℂ) (hx : x = ∑ j, r j • v j)
    (hc : ∀ j, c ≤ ev j) :
    c * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (T x) x) := by
  rw [re_expand v ev T hTv horth r x hx, norm_expand v horth r x hx, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hc j) (w_nonneg _)

private lemma tail_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (v : ι' → E) (ev : ι' → ℝ)
    (T : E →ₗ[ℂ] E)
    (hTv : ∀ j, T (v j) = ((ev j : ℝ) : ℂ) • v j)
    (horth : ∀ j k, inner ℂ (v j) (v k) = if j = k then 1 else 0)
    (C : ℝ) (x : E) (r : ι' → ℂ) (hx : x = ∑ j, r j • v j)
    (hC : ∀ j, ev j ≤ C) :
    RCLike.re (inner ℂ (T x) x) ≤ C * ‖x‖ ^ 2 := by
  rw [re_expand v ev T hTv horth r x hx, norm_expand v horth r x hx, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hC j) (w_nonneg _)

private lemma repr_of_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (a : OrthonormalBasis (Fin m) ℂ E) (s : Finset (Fin m))
    (x : E) (hx : x ∈ Submodule.span ℂ (Set.range (fun j : ↥s => a (j : Fin m)))) :
    ∃ r : ↥s → ℂ, x = ∑ j, r j • a (j : Fin m) := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨c, ?_⟩
  rw [← hc]
  exact Finsupp.sum_fintype _ _ (fun j => zero_smul ℂ (a ↑j))

private lemma inter_nontrivial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {m : ℕ} (hn : Module.finrank ℂ E = m)
    (a b : OrthonormalBasis (Fin m) ℂ E)
    (sA sB : Finset (Fin m)) (hcard : sA.card + sB.card = m + 1) :
    ∃ x : E, x ≠ 0 ∧
      x ∈ Submodule.span ℂ (Set.range (fun j : ↥sA => a (j : Fin m))) ∧
      x ∈ Submodule.span ℂ (Set.range (fun j : ↥sB => b (j : Fin m))) := by
  set SA : Submodule ℂ E :=
    Submodule.span ℂ (Set.range (fun j : ↥sA => a (j : Fin m))) with hSA
  set SB : Submodule ℂ E :=
    Submodule.span ℂ (Set.range (fun j : ↥sB => b (j : Fin m))) with hSB
  have hLIa : LinearIndependent ℂ (fun j : ↥sA => a (j : Fin m)) :=
    a.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hLIb : LinearIndependent ℂ (fun j : ↥sB => b (j : Fin m)) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hmemA : ∀ j : ↥sA, a (j : Fin m) ∈ SA := by
    intro j
    rw [hSA]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hmemB : ∀ j : ↥sB, b (j : Fin m) ∈ SB := by
    intro j
    rw [hSB]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hLIa' : LinearIndependent ℂ (fun j : ↥sA => (⟨a (j : Fin m), hmemA j⟩ : ↥SA)) :=
    LinearIndependent.of_comp SA.subtype hLIa
  have hLIb' : LinearIndependent ℂ (fun j : ↥sB => (⟨b (j : Fin m), hmemB j⟩ : ↥SB)) :=
    LinearIndependent.of_comp SB.subtype hLIb
  have hcA : sA.card ≤ Module.finrank ℂ ↥SA := by
    rw [← Fintype.card_coe]
    exact hLIa'.fintype_card_le_finrank
  have hcB : sB.card ≤ Module.finrank ℂ ↥SB := by
    rw [← Fintype.card_coe]
    exact hLIb'.fintype_card_le_finrank
  have hle : Module.finrank ℂ ↥(SA ⊔ SB) ≤ m := by
    calc Module.finrank ℂ ↥(SA ⊔ SB)
        ≤ Module.finrank ℂ ↥(⊤ : Submodule ℂ E) := Submodule.finrank_mono le_top
      _ = Module.finrank ℂ E := Submodule.topEquiv.finrank_eq
      _ = m := hn
  have hform := Submodule.finrank_sup_add_finrank_inf_eq SA SB
  have h1 : 1 ≤ Module.finrank ℂ ↥(SA ⊓ SB) := by omega
  have hne : SA ⊓ SB ≠ ⊥ := by
    intro hcon
    have h0 : Module.finrank ℂ ↥(SA ⊓ SB) = 0 := by rw [hcon]; exact finrank_bot _ _
    omega
  obtain ⟨x, hxm, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨x, hxn, ?_, ?_⟩
  · have hxmA := (Submodule.mem_inf.mp hxm).1
    rwa [hSA] at hxmA
  · have hxmB := (Submodule.mem_inf.mp hxm).2
    rwa [hSB] at hxmB

private lemma weyl_one_sided {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {m : ℕ} (hn : Module.finrank ℂ E = m)
    (TA TB : E →ₗ[ℂ] E) (hTA : TA.IsSymmetric) (hTB : TB.IsSymmetric)
    (i : Fin m) :
    hTA.eigenvalues hn i - hTB.eigenvalues hn i ≤
      ‖(TA - TB).toContinuousLinearMap‖ := by
  set sA : Finset (Fin m) := Finset.univ.filter (fun j => j ≤ i) with hsA
  set sB : Finset (Fin m) := Finset.univ.filter (fun j => i ≤ j) with hsB
  have hcard : sA.card + sB.card = m + 1 := by
    have hunion : sA ∪ sB = Finset.univ := by
      ext j
      simp only [hsA, hsB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact iff_true_intro (le_total j i)
    have hinter : sA ∩ sB = {i} := by
      ext j
      simp only [hsA, hsB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_singleton]
      exact le_antisymm_iff.symm
    have h := Finset.card_union_add_card_inter sA sB
    rw [hunion, hinter, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton] at h
    omega
  set aA := hTA.eigenvectorBasis hn with haA
  set aB := hTB.eigenvectorBasis hn with haB
  set αA := hTA.eigenvalues hn with hαA
  set αB := hTB.eigenvalues hn with hαB
  have hantiA : Antitone αA := hTA.eigenvalues_antitone hn
  have hantiB : Antitone αB := hTB.eigenvalues_antitone hn
  obtain ⟨x, hxn, hxA, hxB⟩ := inter_nontrivial hn aA aB sA sB hcard
  obtain ⟨rA, hrA⟩ := repr_of_mem_span aA sA x hxA
  obtain ⟨rB, hrB⟩ := repr_of_mem_span aB sB x hxB
  have horthA : ∀ j k : ↥sA, inner ℂ (aA ↑j) (aA ↑k) = if j = k then 1 else 0 := by
    intro j k
    have h := orthonormal_iff_ite.mp aA.orthonormal (↑j : Fin m) (↑k : Fin m)
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true] at h ⊢
      exact h
    · have hjk2 : (↑j : Fin m) ≠ ↑k := fun hc => hjk (Subtype.ext hc)
      rw [ite_eq_right hjk2] at h
      rw [ite_eq_right hjk]
      exact h
  have horthB : ∀ j k : ↥sB, inner ℂ (aB ↑j) (aB ↑k) = if j = k then 1 else 0 := by
    intro j k
    have h := orthonormal_iff_ite.mp aB.orthonormal (↑j : Fin m) (↑k : Fin m)
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true] at h ⊢
      exact h
    · have hjk2 : (↑j : Fin m) ≠ ↑k := fun hc => hjk (Subtype.ext hc)
      rw [ite_eq_right hjk2] at h
      rw [ite_eq_right hjk]
      exact h
  have hTvA : ∀ j : ↥sA, TA (aA ↑j) = (((αA ↑j : ℝ)) : ℂ) • aA ↑j := by
    intro j
    have h := hTA.apply_eigenvectorBasis hn (↑j : Fin m)
    rwa [← haA, ← hαA] at h
  have hTvB : ∀ j : ↥sB, TB (aB ↑j) = (((αB ↑j : ℝ)) : ℂ) • aB ↑j := by
    intro j
    have h := hTB.apply_eigenvectorBasis hn (↑j : Fin m)
    rwa [← haB, ← hαB] at h
  have hcA : ∀ j : ↥sA, αA i ≤ αA ↑j := by
    intro j
    have hj : (↑j : Fin m) ∈ Finset.univ.filter (fun j => j ≤ i) := j.property
    have hle : (↑j : Fin m) ≤ i := (Finset.mem_filter.mp hj).2
    exact hantiA hle
  have hcB : ∀ j : ↥sB, αB ↑j ≤ αB i := by
    intro j
    have hj : (↑j : Fin m) ∈ Finset.univ.filter (fun j => i ≤ j) := j.property
    have hle : i ≤ (↑j : Fin m) := (Finset.mem_filter.mp hj).2
    exact hantiB hle
  have hhead : αA i * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (TA x) x) :=
    head_bound _ _ _ hTvA horthA _ _ _ hrA hcA
  have htail : RCLike.re (inner ℂ (TB x) x) ≤ αB i * ‖x‖ ^ 2 :=
    tail_bound _ _ _ hTvB horthB _ _ _ hrB hcB
  have hD : (αA i - αB i) * ‖x‖ ^ 2 ≤
      RCLike.re (inner ℂ ((TA - TB) x) x) := by
    have e1 : RCLike.re (inner ℂ ((TA - TB) x) x) =
        RCLike.re (inner ℂ (TA x) x) - RCLike.re (inner ℂ (TB x) x) := by
      rw [LinearMap.sub_apply, inner_sub_left]
      exact map_sub _ _ _
    rw [e1]
    have e2 : (αA i - αB i) * ‖x‖ ^ 2 =
        αA i * ‖x‖ ^ 2 - αB i * ‖x‖ ^ 2 := by ring
    rw [e2]
    linarith
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hxn) 2
  have hle1 : αA i - αB i ≤
      RCLike.re (inner ℂ ((TA - TB) x) x) / ‖x‖ ^ 2 :=
    (le_div_iff₀ hpos).mpr hD
  have hray : ((TA - TB).toContinuousLinearMap).rayleighQuotient x =
      RCLike.re (inner ℂ ((TA - TB) x) x) / ‖x‖ ^ 2 := rfl
  rw [← hray] at hle1
  exact hle1.trans
    ((le_abs_self _).trans
      (((TA - TB).toContinuousLinearMap).rayleighQuotient_le_norm x))

/--
**Weyl's perturbation inequality.** Let $A$ and $B$ be Hermitian $n \times n$ complex matrices,
and let $\lambda_1(A) \ge \dots \ge \lambda_n(A)$ and $\lambda_1(B) \ge \dots \ge \lambda_n(B)$ be
their eigenvalues, listed with multiplicity in decreasing order. Then
$|\lambda_i(A) - \lambda_i(B)| \le \|A - B\|$ for every $i$, where $\|A - B\|$ is the operator
norm of $A - B$ acting on $\mathbb{C}^n$ with the Euclidean norm.

Proves `Wanted` entry `weyl_eigenvalue_perturbation_le`.

Source: H. Weyl, Math. Ann. 71 (1912), DOI 10.1007/BF01456804.
-/
theorem weyl_eigenvalue_perturbation_le
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin n) :
    let hA_sym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    let hB_sym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
    |hA_sym.eigenvalues finrank_euclideanSpace_fin i -
        hB_sym.eigenvalues finrank_euclideanSpace_fin i| ≤
      ‖(Matrix.toEuclideanLin (A - B)).toContinuousLinearMap‖ := by
  change |(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace_fin i -
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
      finrank_euclideanSpace_fin i| ≤
    ‖(Matrix.toEuclideanLin (A - B)).toContinuousLinearMap‖
  have d1 := weyl_one_sided (E := EuclideanSpace ℂ (Fin n))
    finrank_euclideanSpace_fin
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB) i
  have d2 := weyl_one_sided (E := EuclideanSpace ℂ (Fin n))
    finrank_euclideanSpace_fin
    (Matrix.toEuclideanLin B) (Matrix.toEuclideanLin A)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) i
  have hnorm : ‖(Matrix.toEuclideanLin B -
      Matrix.toEuclideanLin A).toContinuousLinearMap‖ =
      ‖(Matrix.toEuclideanLin A -
        Matrix.toEuclideanLin B).toContinuousLinearMap‖ := by
    have e : Matrix.toEuclideanLin B - Matrix.toEuclideanLin A =
        -(Matrix.toEuclideanLin A - Matrix.toEuclideanLin B) := by rw [neg_sub]
    rw [e, map_neg, norm_neg]
  rw [hnorm] at d2
  have hsub : Matrix.toEuclideanLin (A - B) =
      Matrix.toEuclideanLin A - Matrix.toEuclideanLin B := map_sub _ _ _
  rw [hsub, abs_le]
  exact ⟨by linarith, d1⟩

end MathlibExt.Analysis.InnerProductSpace.WeylPerturbationWanted
