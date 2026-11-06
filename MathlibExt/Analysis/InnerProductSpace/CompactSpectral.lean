/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Spectral theorem for compact operators
-/

section
universe uE

namespace MathlibExt.Analysis.InnerProductSpace.CompactSpectralWanted

/-- A translate `T - c • 1` of a normal operator is normal. -/
private theorem aux_normal_sub
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T) (c : ℂ) :
    IsStarNormal (T - c • 1) := by
  have hcomm : Commute T (star (c • (1 : E →L[ℂ] E))) := by
    have h : star (c • (1 : E →L[ℂ] E))
        = Algebra.algebraMap ℂ (E →L[ℂ] E) (star c) := by
      rw [star_smul, star_one, Algebra.algebraMap_eq_smul_one]
    rw [h]
    exact Algebra.commute_algebraMap_right _ _
  exact hcomm.isStarNormal_sub

/-- Eigenvectors of a normal operator are eigenvectors of the adjoint (conjugate eigenvalue). -/
private theorem aux_adjoint_eigen
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T)
    (w : E) (ν : ℂ) (hw : T w = ν • w) :
    ContinuousLinearMap.adjoint T w = (star ν) • w := by
  have hN := aux_normal_sub T hT ν
  have h0 : (T - ν • 1) w = 0 := by simp [hw]
  have hadj0 : ContinuousLinearMap.adjoint (T - ν • 1) w = 0 :=
    (ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hN w).mpr h0
  have hexp : ContinuousLinearMap.adjoint (T - ν • 1)
      = ContinuousLinearMap.adjoint T - (star ν) • 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint (T - ν • 1),
      ← ContinuousLinearMap.star_eq_adjoint T, star_sub, star_smul, star_one]
  rw [hexp] at hadj0
  have heq : ContinuousLinearMap.adjoint T w
      = ((star ν) • (1 : E →L[ℂ] E)) w := sub_eq_zero.mp hadj0
  rw [heq]
  rfl

/-- Eigenspaces of a normal operator for distinct eigenvalues are orthogonal. -/
private theorem aux_orth
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T)
    (μ ν : ℂ) (hμν : μ ≠ ν) (v w : E)
    (hv : v ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)
    (hw : w ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) ν) :
    @inner ℂ E _ v w = 0 := by
  have hN := aux_normal_sub T hT ν
  have hrange : ((T - ν • (1 : E →L[ℂ] E)).range)ᗮ
      = (T - ν • (1 : E →L[ℂ] E)).ker :=
    ContinuousLinearMap.IsStarNormal.orthogonal_range hN
  have hvT : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hwT : T w = ν • w := Module.End.mem_eigenspace_iff.mp hw
  have hSv : (T - ν • (1 : E →L[ℂ] E)) v = (μ - ν) • v := by
    simp [hvT, sub_smul]
  have hwker : w ∈ (T - ν • (1 : E →L[ℂ] E)).ker := by
    rw [LinearMap.mem_ker]
    simp [hwT]
  have hinner : @inner ℂ E _ ((T - ν • (1 : E →L[ℂ] E)) v) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      ((⟨v, rfl⟩ : (T - ν • (1 : E →L[ℂ] E)) v ∈ (T - ν • (1 : E →L[ℂ] E)).range))
      (hrange ▸ hwker)
  rw [hSv, inner_smul_left, starRingEnd_apply] at hinner
  have hstar : star (μ - ν) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hμν)
  exact (mul_eq_zero.mp hinner).resolve_left hstar

/-- The orthogonal complement of all eigenspaces is invariant under a normal operator. -/
private theorem aux_invariant
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T) (v : E)
    (hv : v ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ) :
    T v ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
  intro μ
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hadj : ContinuousLinearMap.adjoint T w = (star μ) • w :=
    aux_adjoint_eigen T hT w μ (Module.End.mem_eigenspace_iff.mp hw)
  have hvw : @inner ℂ E _ w v = 0 :=
    (Submodule.mem_orthogonal _ _).mp hv w (Submodule.mem_iSup_of_mem μ hw)
  rw [← ContinuousLinearMap.adjoint_inner_left T v w, hadj, inner_smul_left,
    starRingEnd_apply, hvw, mul_zero]

/-- The orthogonal complement of all eigenspaces is invariant under the adjoint. -/
private theorem aux_invariant_adjoint
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (v : E)
    (hv : v ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ) :
    ContinuousLinearMap.adjoint T v
      ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
  intro μ
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hwT : T w = μ • w := Module.End.mem_eigenspace_iff.mp hw
  have hTw : T w ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μ := by
    rw [hwT]
    exact Submodule.smul_mem _ _ hw
  have hinner : @inner ℂ E _ (T w) v = 0 :=
    (Submodule.mem_orthogonal _ _).mp hv _ (Submodule.mem_iSup_of_mem μ hTw)
  rw [ContinuousLinearMap.adjoint_inner_right T w v]
  exact hinner

/-- The restriction of a normal operator to a subspace reducing for `T` and `T†` is normal. -/
private theorem aux_restrict_normal
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsStarNormal T)
    (K : Submodule ℂ E) [CompleteSpace ↥K]
    (hTK : ∀ x ∈ K, T x ∈ K)
    (hAK : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K) :
    IsStarNormal (T.restrict hTK) := by
  have hadj_eq : ContinuousLinearMap.adjoint (T.restrict hTK)
      = (ContinuousLinearMap.adjoint T).restrict hAK := by
    rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    change @inner ℂ E _
        ((((ContinuousLinearMap.adjoint T).restrict hAK) x : ↥K) : E) (y : E)
      = @inner ℂ E _ (x : E) ((((T.restrict hTK) y : ↥K)) : E)
    change @inner ℂ E _ (ContinuousLinearMap.adjoint T (x : E)) (y : E)
      = @inner ℂ E _ (x : E) (T (y : E))
    exact ContinuousLinearMap.adjoint_inner_left T (y : E) (x : E)
  have hcommT : Commute (ContinuousLinearMap.adjoint T) T := by
    have h : Commute (star T) T := hT.star_comm_self
    rwa [ContinuousLinearMap.star_eq_adjoint] at h
  have hTT : (ContinuousLinearMap.adjoint T) ∘L T
      = T ∘L (ContinuousLinearMap.adjoint T) := by
    have h := hcommT.eq
    rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def] at h
  rw [isStarNormal_iff, ContinuousLinearMap.star_eq_adjoint, hadj_eq]
  change (ContinuousLinearMap.adjoint T).restrict hAK * (T.restrict hTK)
    = (T.restrict hTK) * (ContinuousLinearMap.adjoint T).restrict hAK
  apply ContinuousLinearMap.ext
  intro x
  change (ContinuousLinearMap.adjoint T).restrict hAK ((T.restrict hTK) x)
    = (T.restrict hTK) ((ContinuousLinearMap.adjoint T).restrict hAK x)
  apply Subtype.ext
  change ContinuousLinearMap.adjoint T (T (x : E))
    = T (ContinuousLinearMap.adjoint T (x : E))
  have hcon : ((ContinuousLinearMap.adjoint T ∘SL T) (x : E))
      = ((T ∘SL ContinuousLinearMap.adjoint T) (x : E)) := by rw [hTT]
  simpa using hcon

/-- Eigenspaces of a continuous operator are closed. -/
private theorem aux_eigenspace_closed
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (μ : ℂ) :
    IsClosed (Module.End.eigenspace (T : E →ₗ[ℂ] E) μ : Set E) := by
  have heq : Module.End.eigenspace (T : E →ₗ[ℂ] E) μ
      = LinearMap.ker ((T - μ • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    ext x
    simp [LinearMap.mem_ker, sub_eq_zero]
  rw [heq]
  have hclosed : IsClosed (((T - μ • 1 : E →L[ℂ] E)).ker : Set E) :=
    ContinuousLinearMap.isClosed_ker _
  have hker_eq : ((((T - μ • 1 : E →L[ℂ] E)).ker : Submodule ℂ E) : Set E)
      = ((LinearMap.ker ((T - μ • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) := rfl
  rwa [hker_eq] at hclosed

/-- The restriction of `T` to the orthogonal complement of all eigenspaces has no eigenvalues. -/
private theorem aux_restrict_noEigen
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E)
    (hTK : ∀ x ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ,
      T x ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ) :
    ∀ μ : ℂ, ¬ Module.End.HasEigenvalue (T.restrict hTK).toLinearMap μ := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  obtain ⟨hv_mem, hv_ne⟩ := Module.End.hasEigenvector_iff.mp hv
  have hSv : (T.restrict hTK) v = μ • v :=
    Module.End.mem_eigenspace_iff.mp hv_mem
  have hTv : T (v : E) = μ • (v : E) := by
    have h1 : ((T.restrict hTK) v : E)
        = ((μ • v : ↥((⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ)) : E) := by
      rw [hSv]
    simpa using h1
  have hmem : (v : E) ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μ :=
    Module.End.mem_eigenspace_iff.mpr hTv
  have hsup : (v : E) ∈ ⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ :=
    Submodule.mem_iSup_of_mem μ hmem
  have horth : (v : E)
      ∈ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ := v.2
  have h0 : @inner ℂ E _ (v : E) (v : E) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hsup horth
  have hve : (v : E) = 0 := inner_self_eq_zero.mp h0
  apply hv_ne
  apply Subtype.ext
  change ((v : ↥((⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ)) : E)
    = (((0 : ↥((⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ))) : E)
  rw [hve]
  rfl

/-- An operator on a nonzero finite-dimensional complex inner product space has an eigenvalue. -/
private theorem aux_exists_eigenvalue
    {V : Type uE} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (R : V →L[ℂ] V) : ∃ ν, Module.End.HasEigenvalue (R : V →ₗ[ℂ] V) ν := by
  have hmonic : (R : V →ₗ[ℂ] V).charpoly.Monic := LinearMap.charpoly_monic _
  have hpos : 0 < (R : V →ₗ[ℂ] V).charpoly.natDegree := by
    rw [LinearMap.charpoly_natDegree _]
    exact Module.finrank_pos
  have hdeg : (R : V →ₗ[ℂ] V).charpoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
    exact_mod_cast ne_of_gt hpos
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ν, (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hν⟩

/-- The orthogonal complement of all eigenspaces of a compact normal operator is trivial. -/
private theorem aux_compl_bot
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT_compact : IsCompactOperator T) (hT_normal : IsStarNormal T) :
    (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ = ⊥ := by
  set K : Submodule ℂ E :=
    (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ with hKdef
  have : CompleteSpace ↥K :=
    Submodule.instOrthogonalCompleteSpace
      (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)
  have hTK : ∀ x ∈ K, T x ∈ K := fun x hx => aux_invariant T hT_normal x hx
  have hAK : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K :=
    fun x hx => aux_invariant_adjoint T x hx
  set S : ↥K →L[ℂ] ↥K := T.restrict hTK with hSdef
  have hS_compact : IsCompactOperator S :=
    hT_compact.restrict' (fun x hx => hTK x hx)
  have hS_normal : IsStarNormal S := aux_restrict_normal T hT_normal K hTK hAK
  have hS_noEigen : ∀ μ : ℂ, ¬ Module.End.HasEigenvalue S.toLinearMap μ :=
    aux_restrict_noEigen T hTK
  have hG_compact : IsCompactOperator (ContinuousLinearMap.adjoint S ∘L S) :=
    hS_compact.clm_comp (ContinuousLinearMap.adjoint S)
  have hG_symm : (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ]
      ↥K).IsSymmetric := by
    intro x y
    change @inner ℂ ↥K _ (ContinuousLinearMap.adjoint S (S x)) y
      = @inner ℂ ↥K _ x (ContinuousLinearMap.adjoint S (S y))
    rw [ContinuousLinearMap.adjoint_inner_left S y (S x),
      ContinuousLinearMap.adjoint_inner_right S x (S y)]
  have hG_eig : ∀ μ : ℂ, Module.End.HasEigenvalue
      (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ → μ = 0 := by
    intro μ hμ
    by_contra hne
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨hv_mem, hv_ne⟩ := Module.End.hasEigenvector_iff.mp hv
    have hF_fin : FiniteDimensional ℂ
        ↥(Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ) :=
      ContinuousLinearMap.finite_dimensional_eigenspace hG_compact μ hne
    have hcomm : S ∘L (ContinuousLinearMap.adjoint S)
        = (ContinuousLinearMap.adjoint S) ∘L S := by
      have h := hS_normal.star_comm_self
      rw [ContinuousLinearMap.star_eq_adjoint] at h
      have he := h.eq
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def] at he
      exact he.symm
    have hSF : ∀ x ∈ Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ,
        S x ∈ Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have hx' : (ContinuousLinearMap.adjoint S ∘L S) x = μ • x := hx
      have e1 : (ContinuousLinearMap.adjoint S ∘L S) (S x)
          = S ((ContinuousLinearMap.adjoint S ∘L S) x) := by
        have h := DFunLike.congr_fun hcomm.symm (S x)
        simpa using h
      change (ContinuousLinearMap.adjoint S ∘L S) (S x) = μ • S x
      rw [e1, hx', map_smul]
    have hF_nontrivial : Nontrivial ↥(Module.End.eigenspace
        (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ) := by
      have hw' : (⟨v, hv_mem⟩ : ↥(Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ)) ≠ 0 := by
        intro hcon
        apply hv_ne
        have hcc := congr_arg (fun w : ↥(Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ) => (w : ↥K)) hcon
        simpa using hcc
      exact ⟨⟨v, hv_mem⟩, 0, hw'⟩
    have hF_closed : IsClosed ((Module.End.eigenspace
        (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ) : Set ↥K) :=
      aux_eigenspace_closed _ μ
    have : CompleteSpace ↥(Module.End.eigenspace
        (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ) :=
      hF_closed.completeSpace_coe
    obtain ⟨ν, hν⟩ := aux_exists_eigenvalue (V := ↥(Module.End.eigenspace
        (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ))
      (S.restrict hSF)
    obtain ⟨w, hw⟩ := hν.exists_hasEigenvector
    obtain ⟨hw_mem, hw_ne⟩ := Module.End.hasEigenvector_iff.mp hw
    have hRw : (S.restrict hSF) w = ν • w :=
      Module.End.mem_eigenspace_iff.mp hw_mem
    have hSw : S (w : ↥K) = ν • (w : ↥K) := by
      have h1 : ((S.restrict hSF) w : ↥K) = S ((w : ↥K)) := rfl
      have h2 : ((ν • w : ↥(Module.End.eigenspace
          (((ContinuousLinearMap.adjoint S ∘L S : ↥K →L[ℂ] ↥K)) : ↥K →ₗ[ℂ] ↥K) μ)) : ↥K)
          = ν • ((w : ↥K)) := rfl
      rw [hRw] at h1
      rw [h2] at h1
      exact h1.symm
    have hwK_ne : (w : ↥K) ≠ 0 := by
      intro hcon
      apply hw_ne
      exact Subtype.coe_injective (by simpa using hcon)
    exact hS_noEigen ν (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hSw, hwK_ne⟩)
  have hG_zero : (ContinuousLinearMap.adjoint S ∘L S) = 0 :=
    (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      hG_compact hG_symm).mp hG_eig
  have hS_zero : S = 0 :=
    ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hG_zero
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hTv : T v = 0 := by
    have hSv0 : S (⟨v, hv⟩ : ↥K) = 0 := by rw [hS_zero]; rfl
    have h1 : ((S (⟨v, hv⟩ : ↥K) : ↥K) : E) = T v := rfl
    have h2 : (((0 : ↥K)) : E) = (0 : E) := rfl
    calc T v = ((S (⟨v, hv⟩ : ↥K) : ↥K) : E) := h1.symm
      _ = (((0 : ↥K)) : E) := by rw [hSv0]
      _ = 0 := h2
  have hmem0 : (v : E) ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) 0 := by
    rw [Module.End.mem_eigenspace_iff]
    simpa using hTv
  have hsup : (v : E) ∈ ⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ :=
    Submodule.mem_iSup_of_mem 0 hmem0
  have h0 : @inner ℂ E _ (v : E) (v : E) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hsup hv
  have hve : (v : E) = 0 := inner_self_eq_zero.mp h0
  exact hve

/-- Eigenvalues of a compact normal operator bounded away from zero form a finite set. -/
private theorem aux_finite_eigenvalues
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT_compact : IsCompactOperator T) (hT_normal : IsStarNormal T)
    (ε : ℝ) (hε : 0 < ε) :
    Set.Finite {μ : ℂ | Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) μ ∧ ε ≤ ‖μ‖} := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e := hinf.natEmbedding with hedef
  have ha : ∀ n, Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) ((e n) : ℂ)
      ∧ ε ≤ ‖((e n) : ℂ)‖ := fun n => (e n).2
  have hinj : Function.Injective (fun n => ((e n) : ℂ)) := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have hex : ∀ n, ∃ x : E, T x = ((e n) : ℂ) • x ∧ ‖x‖ = 1 := by
    intro n
    obtain ⟨x, hx⟩ := (ha n).1.exists_hasEigenvector
    obtain ⟨hx_mem, hx_ne⟩ := Module.End.hasEigenvector_iff.mp hx
    have hxT : T x = ((e n) : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx_mem
    refine ⟨(((‖x‖⁻¹ : ℝ)) : ℂ) • x, ?_, ?_⟩
    · rw [map_smul, hxT]
      exact (smul_comm _ _ _).symm
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx_ne)]
  choose u hu_eig hu_norm using hex
  have horth : ∀ m n, m ≠ n → @inner ℂ E _ (u m) (u n) = 0 := by
    intro m n hmn
    have hne : ((e m) : ℂ) ≠ ((e n) : ℂ) := fun hcon => hmn (hinj hcon)
    exact aux_orth T hT_normal _ _ hne _ _
      (Module.End.mem_eigenspace_iff.mpr (hu_eig m))
      (Module.End.mem_eigenspace_iff.mpr (hu_eig n))
  have hsep : ∀ m n, m ≠ n → ε ≤ ‖T (u m) - T (u n)‖ := by
    intro m n hmn
    have h1 : T (u m) - T (u n)
        = ((e m) : ℂ) • (u m) - ((e n) : ℂ) • (u n) := by
      rw [hu_eig m, hu_eig n]
    have hort : @inner ℂ E _ (((e m) : ℂ) • (u m)) (((e n) : ℂ) • (u n)) = 0 := by
      have e1 : @inner ℂ E _ (((e m) : ℂ) • (u m)) (((e n) : ℂ) • (u n))
          = (starRingEnd ℂ ((e m) : ℂ))
            * @inner ℂ E _ (u m) (((e n) : ℂ) • (u n)) :=
        inner_smul_left _ _ _
      have e2 : @inner ℂ E _ (u m) (((e n) : ℂ) • (u n))
          = ((e n) : ℂ) * @inner ℂ E _ (u m) (u n) :=
        inner_smul_right _ _ _
      rw [e1, e2, horth m n hmn, mul_zero, mul_zero]
    have hpyth : ‖T (u m) - T (u n)‖ ^ 2
        = ‖((e m) : ℂ)‖ ^ 2 + ‖((e n) : ℂ)‖ ^ 2 := by
      have e3 : ‖(((e m) : ℂ) • (u m)) - (((e n) : ℂ) • (u n))‖ ^ 2
          = ‖(((e m) : ℂ) • (u m))‖ ^ 2
            - 2 * RCLike.re (@inner ℂ E _ (((e m) : ℂ) • (u m)) (((e n) : ℂ) • (u n)))
            + ‖(((e n) : ℂ) • (u n))‖ ^ 2 :=
        norm_sub_sq _ _
      rw [h1, e3, hort]
      simp [norm_smul, hu_norm m, hu_norm n]
    have hge : ε ^ 2 ≤ ‖T (u m) - T (u n)‖ ^ 2 := by
      rw [hpyth]
      have hm := (ha m).2
      have hn := (ha n).2
      nlinarith [sq_nonneg (‖((e m) : ℂ)‖ - ε), sq_nonneg (‖((e n) : ℂ)‖ - ε),
        sq_nonneg (‖((e m) : ℂ)‖), sq_nonneg (‖((e n) : ℂ)‖)]
    have hnn : (0 : ℝ) ≤ ‖T (u m) - T (u n)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖T (u m) - T (u n)‖ - ε), hge, hnn, hε]
  have hcompact := hT_compact.isCompact_closure_image_closedBall (1 : ℝ)
  have hmem : ∀ n, T (u n)
      ∈ closure (⇑T '' Metric.closedBall (0 : E) 1) := by
    intro n
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hu_norm n]
  obtain ⟨L, -, φ, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 2) (by linarith)
  have h1 := hN (N + 1) (Nat.le_succ N) N (le_refl N)
  simp only [Function.comp_apply] at h1
  have h2 : ε ≤ dist (T (u (φ (N + 1)))) (T (u (φ N))) := by
    rw [dist_eq_norm]
    apply hsep
    exact ne_of_gt (hmono (Nat.lt_succ_self N))
  linarith

/--
**Spectral theorem for compact normal operators.** Let $E$ be a complex Hilbert space and $T$
a compact normal operator on $E$. Then there are a Hilbert basis $(b_i)_{i \in I}$ of $E$
and complex numbers $(\mu_i)_{i \in I}$ such that $T b_i = \mu_i b_i$ for every $i$, and the
eigenvalues vanish at infinity: for every $\varepsilon > 0$ the set of $i$ with
$|\mu_i| \ge \varepsilon$ is finite.

Proves `Wanted` entry `compactNormal_hilbertBasis`.

Source: Compact normal spectral theorem, Hilbert-Schmidt and Riesz 1910s;
Reed-Simon I; Rudin Functional Analysis; Lean states complex Hilbert compact `IsStarNormal` case
with same finite-level-set vanishing condition and same-universe index.
-/
theorem compactNormal_hilbertBasis
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT_compact : IsCompactOperator T)
    (hT_normal : IsStarNormal T) :
    ∃ (ι : Type uE) (b : HilbertBasis ι ℂ E) (μ : ι → ℂ),
      (∀ ε > (0 : ℝ), Set.Finite { i | ε ≤ ‖μ i‖ }) ∧
      (∀ i, T (b i) = μ i • b i) := by
  classical
  -- Step 1: orthonormal basis of each eigenspace, indexed in the same universe.
  have hex : ∀ μ : ℂ, ∃ (w : Set ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ))
      (b : HilbertBasis w ℂ ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)),
      ⇑b = Subtype.val := by
    intro μ
    have := (aux_eigenspace_closed T μ).completeSpace_coe
    exact exists_hilbertBasis ℂ _
  choose W B hB using hex
  -- Step 2: the global orthonormal set, as a union of eigenspace bases.
  set s : Set E := ⋃ μ, Set.image
    (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ) => (y : E)) (W μ) with hsdef
  have hmemW : ∀ i : ↥s, ∃ (μ : ℂ) (y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)),
      y ∈ W μ ∧ (y : E) = (i : E) := by
    change ∀ i : ↥(⋃ μ, Set.image
      (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ) => (y : E)) (W μ)),
      ∃ (μ : ℂ) (y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)),
        y ∈ W μ ∧ (y : E) = (i : E)
    intro i
    have hi : (i : E) ∈ ⋃ μ, Set.image
        (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ) => (y : E)) (W μ) := i.2
    simp only [Set.mem_iUnion, Set.mem_image] at hi
    obtain ⟨μ, y, hyW, hyeq⟩ := hi
    exact ⟨μ, y, hyW, hyeq⟩
  -- Step 3: the global family is orthonormal.
  have horth : Orthonormal ℂ (Subtype.val : ↥s → E) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain ⟨μi, yi, hyiW, hyeq_i⟩ := hmemW i
    obtain ⟨μj, yj, hyjW, hyeq_j⟩ := hmemW j
    have hBi := (B μi).orthonormal
    have hBj := (B μj).orthonormal
    rw [orthonormal_iff_ite] at hBi hBj
    by_cases hij : i = j
    · have h1 : @inner ℂ ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μi) _
          (B μi ⟨yi, hyiW⟩) (B μi ⟨yi, hyiW⟩) = 1 := by
        rw [hBi]; simp
      have hcoe : (B μi ⟨yi, hyiW⟩ :
          ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μi)) = yi := by
        have hcon := congr_fun (hB μi) ⟨yi, hyiW⟩
        simpa using hcon
      have hinner : @inner ℂ E _ (yi : E) (yi : E) = 1 := by
        have hsub := Submodule.coe_inner
          (Module.End.eigenspace (T : E →ₗ[ℂ] E) μi)
          (B μi ⟨yi, hyiW⟩) (B μi ⟨yi, hyiW⟩)
        rw [h1, hcoe] at hsub
        exact hsub.symm
      have eij : (j : E) = (i : E) := congrArg Subtype.val hij.symm
      have hei : (i : E) = (yi : E) := hyeq_i.symm
      rw [ite_eq_left hij, eij, hei]
      exact hinner
    · have hif : (if i = j then (1 : ℂ) else 0) = 0 := ite_eq_right hij
      rw [hif]
      by_cases hμ : μi = μj
      · subst hμ
        have hzi_ne : (⟨yi, hyiW⟩ : ↥(W μi)) ≠ ⟨yj, hyjW⟩ := by
          intro hcon
          apply hij
          have hy_eq : yi = yj := Subtype.mk.injEq .. ▸ hcon
          apply Subtype.ext
          show (i : E) = (j : E)
          rw [← hyeq_i, ← hyeq_j, hy_eq]
        have h1 : @inner ℂ ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μi) _
            (B μi ⟨yi, hyiW⟩) (B μi ⟨yj, hyjW⟩) = 0 := by
          rw [hBi _ _]
          exact ite_eq_right hzi_ne
        have hcoei : (B μi ⟨yi, hyiW⟩ :
            ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μi)) = yi := by
          have hcon := congr_fun (hB μi) ⟨yi, hyiW⟩
          simpa using hcon
        have hcoej : (B μi ⟨yj, hyjW⟩ :
            ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μi)) = yj := by
          have hcon := congr_fun (hB μi) ⟨yj, hyjW⟩
          simpa using hcon
        have hsub : @inner ℂ E _ (yi : E) (yj : E) = 0 := by
          have hsub0 := Submodule.coe_inner
            (Module.End.eigenspace (T : E →ₗ[ℂ] E) μi)
            (B μi ⟨yi, hyiW⟩) (B μi ⟨yj, hyjW⟩)
          rw [h1, hcoei, hcoej] at hsub0
          exact hsub0.symm
        have hei : (i : E) = (yi : E) := hyeq_i.symm
        have hej : (j : E) = (yj : E) := hyeq_j.symm
        rw [hei, hej]
        exact hsub
      · have hi_mem : (i : E)
            ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μi := hyeq_i ▸ yi.2
        have hj_mem : (j : E)
            ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μj := hyeq_j ▸ yj.2
        exact aux_orth T hT_normal μi μj hμ _ _ hi_mem hj_mem
  -- Global basis vectors are nonzero.
  have hne_all : ∀ i : ↥s, (i : E) ≠ 0 := by
    intro i
    have h1 : ‖(Subtype.val : ↥s → E) i‖ = 1 := horth.norm_eq_one i
    have hval : (Subtype.val : ↥s → E) i = (i : E) := rfl
    rw [hval] at h1
    intro hcon
    rw [hcon, norm_zero] at h1
    exact one_ne_zero h1.symm
  -- Step 4: the closed span is everything.
  have hspan : (Submodule.span ℂ (Set.range (Subtype.val : ↥s → E)))ᗮ = ⊥ := by
    have hle : (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)
        ≤ (Submodule.span ℂ (Set.range (Subtype.val : ↥s → E))).topologicalClosure := by
      apply iSup_le
      intro μ x hx
      set V : Submodule ℂ E :=
        Module.End.eigenspace (T : E →ₗ[ℂ] E) μ with hVdef
      set xv : ↥V := ⟨x, hx⟩ with hxvdef
      have hdense := (B μ).dense_span
      have hmem_top : xv ∈ (⊤ : Submodule ℂ ↥V) := trivial
      rw [← hdense] at hmem_top
      set fL : ↥V →ₗ[ℂ] E := V.subtype with hfLdef
      have hfx : fL xv = x := rfl
      have hmap_le : Submodule.map fL (Submodule.span ℂ (Set.range ⇑(B μ)))
          ≤ Submodule.span ℂ (Set.range (Subtype.val : ↥s → E)) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
        have hBz : (B μ k : ↥V) = (k : ↥V) := by
          have hcon := congr_fun (hB μ) k
          simpa using hcon
        have hmem_s : fL (B μ k) ∈ s := by
          rw [hsdef]
          simp only [Set.mem_iUnion, Set.mem_image]
          refine ⟨μ, (B μ k : ↥V), ?_, ?_⟩
          · rw [hBz]
            exact k.2
          · rw [hBz]
            rfl
        have hmem_range : fL (B μ k) ∈ Set.range (Subtype.val : ↥s → E) :=
          ⟨⟨fL (B μ k), hmem_s⟩, rfl⟩
        exact Submodule.subset_span hmem_range
      have hxv_cl : xv ∈ closure
          (↑(Submodule.span ℂ (Set.range ⇑(B μ))) : Set ↥V) := by
        have hco : (↑((Submodule.span ℂ (Set.range ⇑(B μ))).topologicalClosure) :
            Set ↥V) = closure ↑(Submodule.span ℂ (Set.range ⇑(B μ))) :=
          Submodule.topologicalClosure_coe _
        rw [← hco]
        exact hmem_top
      have hcont : Continuous ⇑fL := V.subtypeL.continuous
      have himg := image_closure_subset_closure_image hcont
        (s := ↑(Submodule.span ℂ (Set.range ⇑(B μ))) )
      have hfx_cl : fL xv ∈ closure
          (⇑fL '' ↑(Submodule.span ℂ (Set.range ⇑(B μ))) : Set E) :=
        himg ⟨xv, hxv_cl, rfl⟩
      have hsub_set : ⇑fL '' ↑(Submodule.span ℂ (Set.range ⇑(B μ)))
          ⊆ ↑(Submodule.span ℂ (Set.range (Subtype.val : ↥s → E))) := by
        rintro y ⟨v, hv, rfl⟩
        have hmap_mem : fL v ∈ Submodule.map fL (Submodule.span ℂ (Set.range ⇑(B μ))) :=
          Submodule.mem_map.mpr ⟨v, hv, rfl⟩
        have hle_mem := hmap_le hmap_mem
        exact hle_mem
      have hfin : fL xv ∈ closure
          (↑(Submodule.span ℂ (Set.range (Subtype.val : ↥s → E))) : Set E) :=
        closure_mono hsub_set hfx_cl
      have hco2 : (↑((Submodule.span ℂ
          (Set.range (Subtype.val : ↥s → E))).topologicalClosure) : Set E)
          = closure ↑(Submodule.span ℂ (Set.range (Subtype.val : ↥s → E))) :=
        Submodule.topologicalClosure_coe _
      rw [← hco2] at hfin
      rw [hfx] at hfin
      exact hfin
    have horth_le : (Submodule.span ℂ (Set.range (Subtype.val : ↥s → E)))ᗮ
        ≤ (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ := by
      have h1 := Submodule.orthogonal_closure
        (Submodule.span ℂ (Set.range (Subtype.val : ↥s → E)))
      rw [← h1]
      exact Submodule.orthogonal_le hle
    have hbot : (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ = ⊥ :=
      aux_compl_bot T hT_compact hT_normal
    rw [hbot] at horth_le
    exact le_bot_iff.mp horth_le
  -- Step 5: the Hilbert basis and eigenvalue selector.
  set b : HilbertBasis ↥s ℂ E :=
    HilbertBasis.mkOfOrthogonalEqBot horth hspan with hbdef
  have hbcoe : ⇑b = Subtype.val :=
    HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  have hmem : ∀ i : ↥s, ∃ μ,
      (i : E) ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μ := by
    intro i
    obtain ⟨μ, y, hyW, hyeq⟩ := hmemW i
    exact ⟨μ, hyeq ▸ y.2⟩
  choose μf hμf using hmem
  refine ⟨↥s, b, μf, ?_, ?_⟩
  · -- Vanishing at infinity.
    intro ε hε
    have hF : Set.Finite {μ : ℂ |
        Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) μ ∧ ε ≤ ‖μ‖} :=
      aux_finite_eigenvalues T hT_compact hT_normal ε hε
    have hfib : ∀ μ₀ : ℂ, μ₀ ∈ {μ : ℂ |
          Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) μ ∧ ε ≤ ‖μ‖} →
        Set.Finite { i : ↥s | μf i = μ₀ } := by
      intro μ₀ hμ₀
      obtain ⟨hEig, hle⟩ := hμ₀
      have hne : μ₀ ≠ 0 := by
        intro hcon
        rw [hcon, norm_zero] at hle
        linarith
      have hfin_dim : FiniteDimensional ℂ
          ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ₀) :=
        ContinuousLinearMap.finite_dimensional_eigenspace hT_compact μ₀ hne
      have hLI := (B μ₀).orthonormal.linearIndependent
      rw [hB μ₀] at hLI
      have hfinW : Finite ↥(W μ₀) := LinearIndependent.finite hLI
      have htfin : (Set.image
          (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ₀) => (y : E))
          (W μ₀)).Finite := by
        have h1 : (Set.univ : Set ↥(W μ₀)).Finite := Set.finite_univ
        have himg := h1.image
          (fun z : ↥(W μ₀) => ((z : ↥(Module.End.eigenspace
            (T : E →ₗ[ℂ] E) μ₀)) : E))
        have heq : (fun z : ↥(W μ₀) => ((z : ↥(Module.End.eigenspace
              (T : E →ₗ[ℂ] E) μ₀)) : E)) '' Set.univ
            = Set.image
              (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ₀) => (y : E))
              (W μ₀) := by
          ext x
          simp only [Set.mem_image, Set.mem_univ, true_and]
          constructor
          · rintro ⟨z, rfl⟩
            exact ⟨z.1, z.2, rfl⟩
          · rintro ⟨y, hyW, rfl⟩
            exact ⟨⟨y, hyW⟩, rfl⟩
        rwa [heq] at himg
      have himg_sub : Subtype.val '' { i : ↥s | μf i = μ₀ }
          ⊆ Set.image
            (fun y : ↥(Module.End.eigenspace (T : E →ₗ[ℂ] E) μ₀) => (y : E))
            (W μ₀) := by
        rintro x ⟨i, hi, rfl⟩
        simp only [Set.mem_ofPred_eq] at hi
        obtain ⟨μ₁, y, hyW, hyeq⟩ := hmemW i
        have h1 : (i : E) ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) μ₁ :=
          hyeq ▸ y.2
        have h2 : (i : E) ∈ Module.End.eigenspace (T : E →ₗ[ℂ] E) (μf i) :=
          hμf i
        rw [hi] at h2
        have hμeq : μ₁ = μ₀ := by
          have hT1 : T (i : E) = μ₁ • (i : E) :=
            Module.End.mem_eigenspace_iff.mp h1
          have hT2 : T (i : E) = μ₀ • (i : E) :=
            Module.End.mem_eigenspace_iff.mp h2
          have heq : μ₁ • (i : E) = μ₀ • (i : E) := hT1.symm.trans hT2
          have hsm : (μ₁ - μ₀) • (i : E) = 0 := by
            rw [sub_smul, heq, sub_self]
          rcases smul_eq_zero.mp hsm with h | h
          · exact sub_eq_zero.mp h
          · exact absurd h (hne_all i)
        subst hμeq
        exact ⟨y, hyW, hyeq⟩
      have himg_fin : (Subtype.val '' { i : ↥s | μf i = μ₀ }).Finite :=
        htfin.subset himg_sub
      exact himg_fin.of_finite_image Subtype.val_injective.injOn
    have hsub : { i : ↥s | ε ≤ ‖μf i‖ }
        ⊆ ⋃ μ₀ ∈ {μ : ℂ | Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) μ ∧ ε ≤ ‖μ‖},
          { i : ↥s | μf i = μ₀ } := by
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      have hEig : Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) (μf i) :=
        Module.End.hasEigenvalue_of_hasEigenvector ⟨hμf i, hne_all i⟩
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨μf i, ⟨hEig, hi⟩, rfl⟩
    exact (hF.biUnion hfib).subset hsub
  · -- Eigen-equation.
    intro i
    have hT : T (i : E) = μf i • (i : E) :=
      Module.End.mem_eigenspace_iff.mp (hμf i)
    have hbi : b i = (i : E) := congr_fun hbcoe i
    rw [hbi]
    exact hT

end MathlibExt.Analysis.InnerProductSpace.CompactSpectralWanted
