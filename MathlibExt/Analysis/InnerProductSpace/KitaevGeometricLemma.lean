/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import MathlibExt.Analysis.InnerProductSpace.CourantFischer

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Kitaev's geometric lemma

For nonnegative operators `A₁` and `A₂` whose null spaces meet only at
zero, and whose nonzero eigenvalues are all at least `v`, the smallest
eigenvalue of `A₁ + A₂` is bounded below by
`2 * v * sin² (ϑ / 2)`, where `ϑ` is the angle between the null spaces.

The angle is recorded through the operator norm of the composition of
the two orthogonal projections.  In finite dimensions this is the
maximum absolute inner product between unit vectors in the two
subspaces, with the value `0` when either subspace is zero.

Source: A. Yu. Kitaev, A. H. Shen, and M. N. Vyalyi, *Classical and
Quantum Computation*, American Mathematical Society, 2002, Lemma 14.4.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.KitaevGeometricLemma

open scoped _root_.InnerProductSpace

/-- The cosine of the angle between two subspaces, defined as the
operator norm of the composition of their orthogonal projections. -/
noncomputable def subspaceCos {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] : ℝ :=
  ‖L.starProjection ∘L M.starProjection‖

/-- The angle between two subspaces, with cosine `subspaceCos L M`. -/
noncomputable def subspaceAngle {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] : ℝ :=
  Real.arccos (subspaceCos L M)

/-- The subspace cosine is nonnegative. -/
theorem subspaceCos_nonneg {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] :
    0 ≤ subspaceCos L M := by
  unfold subspaceCos
  exact norm_nonneg _

/-- The subspace cosine is at most one. -/
theorem subspaceCos_le_one {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] :
    subspaceCos L M ≤ 1 := by
  unfold subspaceCos
  have hL : ‖L.starProjection‖ ≤ 1 := by
    apply Submodule.starProjection_norm_le
  have hM : ‖M.starProjection‖ ≤ 1 := by
    apply Submodule.starProjection_norm_le
  have hcomp : ‖L.starProjection ∘L M.starProjection‖ ≤
      ‖L.starProjection‖ * ‖M.starProjection‖ := by
    apply ContinuousLinearMap.opNorm_comp_le
  have hMnn : 0 ≤ ‖M.starProjection‖ := norm_nonneg _
  calc ‖L.starProjection ∘L M.starProjection‖
      ≤ ‖L.starProjection‖ * ‖M.starProjection‖ := hcomp
    _ ≤ 1 * 1 := by
        apply mul_le_mul hL hM hMnn zero_le_one
    _ = 1 := by ring

/-- Inner products across the two subspaces are bounded by their
subspace cosine. -/
theorem norm_inner_le_subspaceCos_mul_norm {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (L M : Submodule 𝕜 E) [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] {x y : E} (hx : x ∈ L) (hy : y ∈ M) :
    ‖⟪x, y⟫_𝕜‖ ≤ subspaceCos L M * ‖x‖ * ‖y‖ := by
  have hx' : L.starProjection x = x := by
    rw [Submodule.starProjection_eq_self_iff]
    exact hx
  have hy' : M.starProjection y = y := by
    rw [Submodule.starProjection_eq_self_iff]
    exact hy
  unfold subspaceCos
  calc ‖⟪x, y⟫_𝕜‖
      = ‖⟪L.starProjection x, M.starProjection y⟫_𝕜‖ := by
        rw [hx', hy']
    _ = ‖⟪x, L.starProjection (M.starProjection y)⟫_𝕜‖ := by
        rw [Submodule.inner_starProjection_left_eq_right]
    _ = ‖⟪x, (L.starProjection ∘L M.starProjection) y⟫_𝕜‖ := by
        rw [ContinuousLinearMap.comp_apply]
    _ ≤ ‖x‖ * ‖(L.starProjection ∘L M.starProjection) y‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖L.starProjection ∘L M.starProjection‖ * ‖y‖) := by
        apply mul_le_mul_of_nonneg_left
        · apply ContinuousLinearMap.le_opNorm
        · exact norm_nonneg _
    _ = ‖L.starProjection ∘L M.starProjection‖ * ‖x‖ * ‖y‖ := by
        ring

/-- Squared norm of a star projection as a real inner product. -/
private theorem normSq_starProjection_eq_re_inner {𝕜 : Type*}
    [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (L : Submodule 𝕜 E)
    [L.HasOrthogonalProjection] (x : E) :
    ‖L.starProjection x‖ ^ 2 =
      RCLike.re ⟪L.starProjection x, x⟫_𝕜 := by
  have hmem : L.starProjection x ∈ L := by
    apply Submodule.starProjection_apply_mem
  have horth : x - L.starProjection x ∈ Lᗮ := by
    apply Submodule.sub_starProjection_mem_orthogonal
  have h0 : ⟪L.starProjection x, x - L.starProjection x⟫_𝕜 = 0 := by
    apply Submodule.inner_right_of_mem_orthogonal
    · assumption
    · assumption
  have hsub : ⟪L.starProjection x, x - L.starProjection x⟫_𝕜 =
      ⟪L.starProjection x, x⟫_𝕜 - ⟪L.starProjection x,
        L.starProjection x⟫_𝕜 := by
    rw [inner_sub_right]
  have hinner : ⟪L.starProjection x, x⟫_𝕜 =
      ⟪L.starProjection x, L.starProjection x⟫_𝕜 := by
    have h := h0
    rw [hsub] at h
    exact sub_eq_zero.mp h
  rw [hinner, inner_self_eq_norm_sq_to_K]
  simp

/-- The sum of the squared norms of the two orthogonal projections is
at most `1 + cos ϑ` times the squared norm of the vector.  This is
inequality (14.12) in the source proof, in quadratic-form form. -/
theorem norm_sq_starProjection_add_norm_sq_starProjection_le
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (L M : Submodule 𝕜 E)
    [L.HasOrthogonalProjection] [M.HasOrthogonalProjection] (x : E) :
    ‖L.starProjection x‖ ^ 2 + ‖M.starProjection x‖ ^ 2 ≤
      (1 + subspaceCos L M) * ‖x‖ ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  set a := L.starProjection x with ha
  set b := M.starProjection x with hb
  set c := subspaceCos L M with hc
  set S := ‖a‖ ^ 2 + ‖b‖ ^ 2 with hSdef
  have hc_nn : 0 ≤ c := by
    rw [hc]
    apply subspaceCos_nonneg
  have hS_nn : 0 ≤ S := by
    rw [hSdef]
    positivity
  by_cases hS0 : S = 0
  · rw [hS0]
    have h1c : 0 ≤ 1 + c := by linarith
    have hx2 : 0 ≤ ‖x‖ ^ 2 := by positivity
    exact mul_nonneg h1c hx2
  have hSpos : 0 < S := lt_of_le_of_ne hS_nn (fun h => hS0 h.symm)
  have ha_mem : a ∈ L := by
    rw [ha]
    apply Submodule.starProjection_apply_mem
  have hb_mem : b ∈ M := by
    rw [hb]
    apply Submodule.starProjection_apply_mem
  have hLa : ‖a‖ ^ 2 = RCLike.re ⟪a, x⟫_𝕜 := by
    rw [ha]
    apply normSq_starProjection_eq_re_inner
  have hLb : ‖b‖ ^ 2 = RCLike.re ⟪b, x⟫_𝕜 := by
    rw [hb]
    apply normSq_starProjection_eq_re_inner
  have hS_eq : S = RCLike.re ⟪a + b, x⟫_𝕜 := by
    rw [hSdef, hLa, hLb, ← map_add, inner_add_left]
  have hle : S ≤ ‖a + b‖ * ‖x‖ := by
    rw [hS_eq]
    apply re_inner_le_norm
  have hadd : ‖a + b‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * RCLike.re ⟪a, b⟫_𝕜 + ‖b‖ ^ 2 := by
    apply norm_add_sq
  have hre_le : RCLike.re ⟪a, b⟫_𝕜 ≤ ‖⟪a, b⟫_𝕜‖ := by
    apply RCLike.re_le_norm
  have hinner_le : ‖⟪a, b⟫_𝕜‖ ≤ c * ‖a‖ * ‖b‖ := by
    rw [hc]
    exact norm_inner_le_subspaceCos_mul_norm L M ha_mem hb_mem
  have hre_bound : RCLike.re ⟪a, b⟫_𝕜 ≤ c * ‖a‖ * ‖b‖ :=
    le_trans hre_le hinner_le
  have h2ab : 2 * ‖a‖ * ‖b‖ ≤ S := by
    rw [hSdef]
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have h2re : 2 * RCLike.re ⟪a, b⟫_𝕜 ≤ c * S := by
    have hmul : 2 * RCLike.re ⟪a, b⟫_𝕜 ≤
        2 * (c * ‖a‖ * ‖b‖) := by
      apply mul_le_mul_of_nonneg_left hre_bound (by norm_num)
    have heq : 2 * (c * ‖a‖ * ‖b‖) = c * (2 * ‖a‖ * ‖b‖) := by
      ring
    have hle2 : c * (2 * ‖a‖ * ‖b‖) ≤ c * S := by
      apply mul_le_mul_of_nonneg_left h2ab hc_nn
    rw [heq] at hmul
    exact le_trans hmul hle2
  have hnorm_le : ‖a + b‖ ^ 2 ≤ (1 + c) * S := by
    have hexpand : (1 + c) * S = S + c * S := by ring
    have hadd' : ‖a + b‖ ^ 2 = S + 2 * RCLike.re ⟪a, b⟫_𝕜 := by
      rw [hadd, hSdef]; ring
    rw [hadd', hexpand]
    linarith [h2re]
  have hSq : S ^ 2 ≤ (1 + c) * ‖x‖ ^ 2 * S := by
    have hpow : S ^ 2 ≤ (‖a + b‖ * ‖x‖) ^ 2 := by
      rw [pow_two, pow_two]
      apply mul_self_le_mul_self hS_nn hle
    have hmulpow : (‖a + b‖ * ‖x‖) ^ 2 =
        ‖a + b‖ ^ 2 * ‖x‖ ^ 2 := by
      rw [mul_pow]
    have hx2nn : 0 ≤ ‖x‖ ^ 2 := by positivity
    have hle_mul : ‖a + b‖ ^ 2 * ‖x‖ ^ 2 ≤
        (1 + c) * S * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right hnorm_le hx2nn
    rw [hmulpow] at hpow
    have htrans : S ^ 2 ≤ (1 + c) * S * ‖x‖ ^ 2 :=
      le_trans hpow hle_mul
    have heq2 : (1 + c) * S * ‖x‖ ^ 2 =
        (1 + c) * ‖x‖ ^ 2 * S := by ring
    rw [heq2] at htrans
    exact htrans
  have hS2 : S * S ≤ (1 + c) * ‖x‖ ^ 2 * S := by
    have hpow2 : S ^ 2 = S * S := by ring
    rw [hpow2] at hSq
    exact hSq
  exact le_of_mul_le_mul_right hS2 hSpos

/-- A positive operator has Rayleigh form at least `v * ‖x‖²` on the
orthogonal complement of its kernel when every nonzero eigenvalue is
at least `v`. -/
theorem rayleighForm_ge_of_mem_ker_orthogonal {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    {v : ℝ}
    (hgap : ∀ μ : 𝕜, Module.End.HasEigenvalue T μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    {x : E} (hx : x ∈ (LinearMap.ker T)ᗮ) :
    v * ‖x‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm T x := by
  have hSym : T.IsSymmetric := hT.1
  set n := Module.finrank 𝕜 E
  have hn : Module.finrank 𝕜 E = n := rfl
  have hexp :
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        T x =
        ∑ i : Fin n, hSym.eigenvalues hn i *
          ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 := by
    apply MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm_eq_expansion
  have hnorm : ‖x‖ ^ 2 =
      ∑ i : Fin n,
        ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 :=
    (OrthonormalBasis.sum_sq_norm_inner_right _ _).symm
  have hterm : ∀ i : Fin n, v *
      ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 ≤
      hSym.eigenvalues hn i *
        ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 := by
    intro i
    set e := (hSym.eigenvectorBasis hn) i with he
    set lam := hSym.eigenvalues hn i with hlam
    have hEig : Module.End.HasEigenvalue T (lam : 𝕜) := by
      rw [hlam]
      apply hSym.hasEigenvalue_eigenvalues
    rcases hgap (lam : 𝕜) hEig with h0 | hgap_le
    · have happly : T e = (lam : 𝕜) • e := by
        rw [he, hlam]
        apply hSym.apply_eigenvectorBasis
      have he_mem : e ∈ LinearMap.ker T := by
        rw [LinearMap.mem_ker, happly, h0, zero_smul]
      have hinner0 : ⟪e, x⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (K := LinearMap.ker T) he_mem hx
      have hwi0 : ‖⟪e, x⟫_𝕜‖ ^ 2 = 0 := by
        simp [hinner0]
      simp [hwi0]
    · have hre_eq : RCLike.re (lam : 𝕜) = lam := by
        simp
      have hvle : v ≤ lam := by
        rw [← hre_eq]
        exact hgap_le
      have hwi_nn : 0 ≤ ‖⟪e, x⟫_𝕜‖ ^ 2 := by
        positivity
      exact mul_le_mul_of_nonneg_right hvle hwi_nn
  have hsum : ∑ i : Fin n, v *
      ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 ≤
      ∑ i : Fin n, hSym.eigenvalues hn i *
        ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact hterm i
  have hmul_sum : v * ‖x‖ ^ 2 =
      ∑ i : Fin n, v *
        ‖⟪(hSym.eigenvectorBasis hn) i, x⟫_𝕜‖ ^ 2 := by
    rw [hnorm, Finset.mul_sum]
  rw [hmul_sum, hexp]
  exact hsum

/-- Rayleigh form is unchanged by subtracting the kernel projection. -/
private theorem rayleighForm_eq_sub_starProjection {𝕜 : Type*}
    [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        T x =
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        T (x - (LinearMap.ker T).starProjection x) := by
  have hSym : T.IsSymmetric := hT.1
  set y := x - (LinearMap.ker T).starProjection x with hy
  have hPx_mem : (LinearMap.ker T).starProjection x ∈
      LinearMap.ker T := by
    apply Submodule.starProjection_apply_mem
  have hTPx : T ((LinearMap.ker T).starProjection x) = 0 :=
    LinearMap.mem_ker.mp hPx_mem
  have hTy : T y = T x := by
    rw [hy, map_sub, hTPx, sub_zero]
  have hTx_eq : T x = T y := hTy.symm
  have hzero : ⟪T y, (LinearMap.ker T).starProjection x⟫_𝕜 = 0 := by
    rw [hSym y ((LinearMap.ker T).starProjection x), hTPx,
      inner_zero_right]
  have hdecomp : y + (LinearMap.ker T).starProjection x = x := by
    rw [hy, sub_add_cancel]
  have hinner_eq : ⟪T x, x⟫_𝕜 = ⟪T y, y⟫_𝕜 := by
    rw [hTx_eq, ← hdecomp, inner_add_right, hzero, add_zero]
  unfold MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
  rw [hinner_eq]

/-- **Kitaev's geometric lemma, quadratic-form version.** -/
theorem kitaev_geometric_quadratic {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) {v : ℝ} (hv : 0 ≤ v)
    (hgapA : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hgapB : ∀ μ : 𝕜, Module.End.HasEigenvalue B μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hdisj : Disjoint (LinearMap.ker A) (LinearMap.ker B)) (x : E) :
    (2 * v * Real.sin
        (subspaceAngle (LinearMap.ker A) (LinearMap.ker B) / 2) ^ 2) *
        ‖x‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        (A + B) x := by
  set c := subspaceCos (LinearMap.ker A) (LinearMap.ker B) with hc
  set th := subspaceAngle (LinearMap.ker A) (LinearMap.ker B) with hth
  set PAx := (LinearMap.ker A).starProjection x with hPAx
  set PBx := (LinearMap.ker B).starProjection x with hPBx
  set yA := x - PAx with hyA
  set yB := x - PBx with hyB
  set S := ‖PAx‖ ^ 2 + ‖PBx‖ ^ 2 with hSdef
  have hyA_mem : yA ∈ (LinearMap.ker A)ᗮ := by
    rw [hyA, hPAx]
    apply Submodule.sub_starProjection_mem_orthogonal
  have hyB_mem : yB ∈ (LinearMap.ker B)ᗮ := by
    rw [hyB, hPBx]
    apply Submodule.sub_starProjection_mem_orthogonal
  have hrayA :
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        A x =
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          A yA := by
    rw [hyA, hPAx]
    exact rayleighForm_eq_sub_starProjection hA x
  have hrayB :
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        B x =
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          B yB := by
    rw [hyB, hPBx]
    exact rayleighForm_eq_sub_starProjection hB x
  have hgapA_yA : v * ‖yA‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        A yA :=
    rayleighForm_ge_of_mem_ker_orthogonal hA hgapA hyA_mem
  have hgapB_yB : v * ‖yB‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        B yB :=
    rayleighForm_ge_of_mem_ker_orthogonal hB hgapB hyB_mem
  have hA_le : v * ‖yA‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        A x := by
    rw [hrayA]
    exact hgapA_yA
  have hB_le : v * ‖yB‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        B x := by
    rw [hrayB]
    exact hgapB_yB
  have hadd_ray :
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        (A + B) x =
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          A x +
          MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
            B x := by
    unfold MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
    rw [LinearMap.add_apply, inner_add_left, map_add]
  have hadd_le : v * ‖yA‖ ^ 2 + v * ‖yB‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        A x +
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          B x :=
    add_le_add hA_le hB_le
  have hsum_le : v * ‖yA‖ ^ 2 + v * ‖yB‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        (A + B) x := by
    rw [← hadd_ray] at hadd_le
    exact hadd_le
  have hnormA : ‖x‖ ^ 2 = ‖yA‖ ^ 2 + ‖PAx‖ ^ 2 := by
    rw [hyA, hPAx]
    have hA0 := Submodule.norm_sq_eq_add_norm_sq_starProjection x
      (LinearMap.ker A)
    have horthA : (LinearMap.ker A)ᗮ.starProjection x =
        x - (LinearMap.ker A).starProjection x := by
      rw [Submodule.starProjection_orthogonal]
      simp
    rw [horthA, add_comm] at hA0
    exact hA0
  have hnormB : ‖x‖ ^ 2 = ‖yB‖ ^ 2 + ‖PBx‖ ^ 2 := by
    rw [hyB, hPBx]
    have hB0 := Submodule.norm_sq_eq_add_norm_sq_starProjection x
      (LinearMap.ker B)
    have horthB : (LinearMap.ker B)ᗮ.starProjection x =
        x - (LinearMap.ker B).starProjection x := by
      rw [Submodule.starProjection_orthogonal]
      simp
    rw [horthB, add_comm] at hB0
    exact hB0
  have hyA_eq : ‖yA‖ ^ 2 = ‖x‖ ^ 2 - ‖PAx‖ ^ 2 := by
    linarith
  have hyB_eq : ‖yB‖ ^ 2 = ‖x‖ ^ 2 - ‖PBx‖ ^ 2 := by
    linarith
  have hproj : ‖PAx‖ ^ 2 + ‖PBx‖ ^ 2 ≤ (1 + c) * ‖x‖ ^ 2 := by
    rw [hPAx, hPBx, hc]
    exact norm_sq_starProjection_add_norm_sq_starProjection_le _ _ x
  have hc_nn : 0 ≤ c := by
    rw [hc]
    apply subspaceCos_nonneg
  have hc_le : c ≤ 1 := by
    rw [hc]
    apply subspaceCos_le_one
  have hcos : Real.cos th = c := by
    rw [hth]
    unfold subspaceAngle
    rw [← hc]
    apply Real.cos_arccos
    · linarith [hc_nn]
    · exact hc_le
  have htrig : 2 * Real.sin (th / 2) ^ 2 = 1 - c := by
    have h2 : 2 * (th / 2) = th := by ring
    have h := Real.sin_sq_eq_half_sub (th / 2)
    rw [h2] at h
    rw [h, hcos]
    ring
  have hgoal_eq : (2 * v * Real.sin (th / 2) ^ 2) * ‖x‖ ^ 2 =
      v * ((1 - c) * ‖x‖ ^ 2) := by
    calc (2 * v * Real.sin (th / 2) ^ 2) * ‖x‖ ^ 2
        = v * (2 * Real.sin (th / 2) ^ 2) * ‖x‖ ^ 2 := by ring
      _ = v * (1 - c) * ‖x‖ ^ 2 := by rw [htrig]
      _ = v * ((1 - c) * ‖x‖ ^ 2) := by ring
  have hspec_eq : v * ‖yA‖ ^ 2 + v * ‖yB‖ ^ 2 =
      v * (2 * ‖x‖ ^ 2 - S) := by
    rw [hyA_eq, hyB_eq, hSdef]
    ring
  have hle_inner : (1 - c) * ‖x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 - S := by
    have hexpand1 : (1 + c) * ‖x‖ ^ 2 =
        ‖x‖ ^ 2 + c * ‖x‖ ^ 2 := by ring
    have hexpand2 : (1 - c) * ‖x‖ ^ 2 =
        ‖x‖ ^ 2 - c * ‖x‖ ^ 2 := by ring
    rw [hexpand1] at hproj
    rw [hexpand2]
    linarith
  have hle_v : v * ((1 - c) * ‖x‖ ^ 2) ≤
      v * (2 * ‖x‖ ^ 2 - S) :=
    mul_le_mul_of_nonneg_left hle_inner hv
  calc (2 * v * Real.sin (th / 2) ^ 2) * ‖x‖ ^ 2
      = v * ((1 - c) * ‖x‖ ^ 2) := hgoal_eq
    _ ≤ v * (2 * ‖x‖ ^ 2 - S) := hle_v
    _ = v * ‖yA‖ ^ 2 + v * ‖yB‖ ^ 2 := hspec_eq.symm
    _ ≤ MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          (A + B) x := hsum_le

/-- **Kitaev's geometric lemma.**  In the Loewner order on operators,
`A + B` is at least `2 * v * sin² (ϑ / 2)` times the identity. -/
theorem kitaev_geometric_lemma {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) {v : ℝ} (hv : 0 ≤ v)
    (hgapA : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hgapB : ∀ μ : 𝕜, Module.End.HasEigenvalue B μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hdisj : Disjoint (LinearMap.ker A) (LinearMap.ker B)) :
    (((2 * v * Real.sin
        (subspaceAngle (LinearMap.ker A) (LinearMap.ker B) / 2) ^ 2 : ℝ) :
        𝕜) • (1 : E →ₗ[𝕜] E)) ≤ A + B := by
  set th := subspaceAngle (LinearMap.ker A) (LinearMap.ker B) with hth
  set r := 2 * v * Real.sin (th / 2) ^ 2 with hr
  rw [LinearMap.le_def]
  constructor
  · have hA_symm : A.IsSymmetric := hA.1
    have hB_symm : B.IsSymmetric := hB.1
    have hAB_symm : (A + B).IsSymmetric := hA_symm.add hB_symm
    have hc_symm : ((((r : ℝ) : 𝕜)) • (1 : E →ₗ[𝕜] E)).IsSymmetric := by
      intro x y
      simp [LinearMap.smul_apply, Module.End.one_apply,
        inner_smul_left, inner_smul_right]
    exact hAB_symm.sub hc_symm
  · intro x
    have hquad : r * ‖x‖ ^ 2 ≤
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          (A + B) x := by
      rw [hr, hth]
      exact kitaev_geometric_quadratic hA hB hv hgapA hgapB hdisj x
    have hsmul : ⟪(((r : ℝ) : 𝕜) • x), x⟫_𝕜 =
        (((r * ‖x‖ ^ 2 : ℝ) : 𝕜)) := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp
    have hRe_smul : RCLike.re ⟪(((r : ℝ) : 𝕜) • x), x⟫_𝕜 =
        r * ‖x‖ ^ 2 := by
      rw [hsmul]
      simp
    have hTx : (A + B - ((((r : ℝ) : 𝕜)) • 1)) x =
        (A + B) x - ((((r : ℝ) : 𝕜)) • x) := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply]
    have hinner : ⟪(A + B - ((((r : ℝ) : 𝕜)) • 1)) x, x⟫_𝕜 =
        ⟪(A + B) x, x⟫_𝕜 - ⟪(((r : ℝ) : 𝕜) • x), x⟫_𝕜 := by
      rw [hTx, inner_sub_left]
    have hRe_eq : RCLike.re
          ⟪(A + B - ((((r : ℝ) : 𝕜)) • 1)) x, x⟫_𝕜 =
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
          (A + B) x - r * ‖x‖ ^ 2 := by
      rw [hinner, map_sub, hRe_smul,
        MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm]
    rw [hRe_eq]
    linarith [hquad]

/-- Eigenvalue form of Kitaev's geometric lemma: every eigenvalue of
`A + B` is at least the geometric bound. -/
theorem kitaev_geometric_eigenvalue_ge {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {A B : E →ₗ[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) {v : ℝ} (hv : 0 ≤ v)
    (hgapA : ∀ μ : 𝕜, Module.End.HasEigenvalue A μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hgapB : ∀ μ : 𝕜, Module.End.HasEigenvalue B μ →
      μ = 0 ∨ v ≤ RCLike.re μ)
    (hdisj : Disjoint (LinearMap.ker A) (LinearMap.ker B))
    {μ : 𝕜} (hμ : Module.End.HasEigenvalue (A + B) μ) :
    2 * v * Real.sin
        (subspaceAngle (LinearMap.ker A) (LinearMap.ker B) / 2) ^ 2 ≤
      RCLike.re μ := by
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx_ne : x ≠ 0 := (Module.End.hasEigenvector_iff.mp hx).2
  have hx_eq : (A + B) x = μ • x := hx.apply_eq_smul
  have hquad : (2 * v * Real.sin
          (subspaceAngle (LinearMap.ker A) (LinearMap.ker B) / 2) ^ 2) *
        ‖x‖ ^ 2 ≤
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        (A + B) x :=
    kitaev_geometric_quadratic hA hB hv hgapA hgapB hdisj x
  have hray_eq :
      MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
        (A + B) x = RCLike.re μ * ‖x‖ ^ 2 := by
    unfold MathlibExt.Analysis.InnerProductSpace.CourantFischer.rayleighForm
    rw [hx_eq, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp
  rw [hray_eq] at hquad
  have hx2pos : 0 < ‖x‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hx_ne) 2
  exact le_of_mul_le_mul_right hquad hx2pos

/-- A common nonzero kernel vector rules out every positive scalar
lower bound, so the trivial-intersection hypothesis is necessary for a
positive conclusion. -/
theorem not_pos_smul_one_le_of_exists_mem_ker_inf {𝕜 : Type*}
    [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {A B : E →ₗ[𝕜] E}
    {c : ℝ} (hc : 0 < c)
    {x : E} (hx : x ≠ 0)
    (hxker : x ∈ LinearMap.ker A ⊓ LinearMap.ker B) :
    ¬ (((c : ℝ) : 𝕜) • (1 : E →ₗ[𝕜] E)) ≤ A + B := by
  intro hle
  have hxA : x ∈ LinearMap.ker A :=
    (Submodule.mem_inf.mp hxker).1
  have hxB : x ∈ LinearMap.ker B :=
    (Submodule.mem_inf.mp hxker).2
  have hAx : A x = 0 := LinearMap.mem_ker.mp hxA
  have hBx : B x = 0 := LinearMap.mem_ker.mp hxB
  have hPos : (A + B - (((c : ℝ) : 𝕜) • 1)).IsPositive :=
    LinearMap.le_def.mp hle
  have hnonneg :
      0 ≤ RCLike.re ⟪(A + B - (((c : ℝ) : 𝕜) • 1)) x, x⟫_𝕜 :=
    hPos.2 x
  have hcalc : ⟪(A + B - (((c : ℝ) : 𝕜) • 1)) x, x⟫_𝕜 =
      -(((c * ‖x‖ ^ 2 : ℝ) : 𝕜)) := by
    simp [LinearMap.sub_apply, LinearMap.add_apply, hAx, hBx,
      LinearMap.smul_apply, Module.End.one_apply,
      inner_smul_left, inner_self_eq_norm_sq_to_K]
  rw [hcalc] at hnonneg
  have hre : RCLike.re (-(((c * ‖x‖ ^ 2 : ℝ) : 𝕜))) =
      -(c * ‖x‖ ^ 2) := by
    simp
  rw [hre] at hnonneg
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx2pos : 0 < ‖x‖ ^ 2 := pow_pos hxpos 2
  have hcpos : 0 < c * ‖x‖ ^ 2 := mul_pos hc hx2pos
  linarith

end MathlibExt.Analysis.InnerProductSpace.KitaevGeometricLemma
