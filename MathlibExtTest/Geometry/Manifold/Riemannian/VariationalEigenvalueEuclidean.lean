/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.VariationalEigenvalueEuclidean
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Public-client tests for the Euclidean variational-eigenvalue bridge.
-/

open TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

namespace Manifold.VariationalEigenvalueEuclideanTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

/-- Forward coercion simplifies by `simp` and agrees with `f` at each point. -/
theorem forward_apply (Ω : Opens E) (f : TestFunction Ω ℝ ⊤) (x : E) :
    ⇑((testFunctionLinearEquiv Ω f : ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω)) :
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯) x = f x := by
  simp

/-- Inverse coercion of a core member simplifies by `simp` at each point. -/
theorem inverse_apply (Ω : Opens E)
    (u : ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω)) (x : E) :
    ⇑((testFunctionLinearEquiv Ω).symm u) x =
      ⇑(u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯) x := by
  simp

/-- Linear combinations through the bridge evaluate pointwise. -/
theorem add_smul_apply (Ω : Opens E) (f g : TestFunction Ω ℝ ⊤) (c : ℝ)
    (x : E) :
    ⇑((testFunctionLinearEquiv Ω (f + c • g) :
      ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω)) :
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯) x = f x + c * g x := by
  simp [coe_testFunctionLinearEquiv, smul_eq_mul]

/-- The manifold Rayleigh quotient of the zero test function is `0`. -/
theorem rayleighQuotient_zero_testFunction
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
      ⇑(0 : DirichletLaplacian.SmoothTestSpace Ω) = 0 := by
  have hq : DirichletLaplacian.rayleighQuotient
      (0 : DirichletLaplacian.SmoothTestSpace Ω) = 0 := by
    unfold DirichletLaplacian.rayleighQuotient
    simp
  have hbridge : rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
      ⇑(0 : DirichletLaplacian.SmoothTestSpace Ω) =
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
        (0 : DirichletLaplacian.SmoothTestSpace Ω)) :=
    rayleighQuotient_testFunction (0 : DirichletLaplacian.SmoothTestSpace Ω)
  rw [hbridge, hq]
  simp

/-- Every bundled test function on the empty open set vanishes. -/
private theorem bot_testFunction_eq_zero
    (f : TestFunction (⊥ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) :
    f = 0 := by
  have hz : Set.EqOn ⇑f 0 ((⊥ : Opens (EuclideanSpace ℝ (Fin n))) : Set _)ᶜ :=
    TestFunction.zero_on_compl f
  have hcompl : (((⊥ : Opens (EuclideanSpace ℝ (Fin n))) :
      Set (EuclideanSpace ℝ (Fin n)))ᶜ) = Set.univ := by
    simp
  have hzuniv : Set.EqOn ⇑f 0 Set.univ := by
    rw [← hcompl]
    exact hz
  apply TestFunction.ext
  intro a
  have ha : ⇑f a = (0 : EuclideanSpace ℝ (Fin n) → ℝ) a :=
    hzuniv (Set.mem_univ a)
  simpa using ha

/-- On the empty domain the manifold value is `⊤` and the real value is `0`. -/
theorem empty_domain (j : ℕ) :
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (⊥ : Opens (EuclideanSpace ℝ (Fin n)))) volume j = ⊤ ∧
      DirichletLaplacian.variationalEigenvalue
        (⊥ : Opens (EuclideanSpace ℝ (Fin n))) j = 0 := by
  have hhyp : ∀ V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace
      (⊥ : Opens (EuclideanSpace ℝ (Fin n)))), Module.finrank ℝ ↥V ≠ j + 1 := by
    intro V hcon
    have hVbot : V = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hx0 : x = 0 := bot_testFunction_eq_zero x
      rw [Submodule.mem_bot]
      exact hx0
    have h0 : Module.finrank ℝ ↥V = 0 := by
      rw [hVbot]
      exact finrank_bot ℝ _
    omega
  exact variationalEigenvalue_eq_top_of_forall_finrank_ne _ j hhyp

/-- Witness upper bound through the Dirichlet identification. -/
theorem witness_le (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ)
    (V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω))
    (hfin : Module.finrank ℝ ↥V = j + 1) :
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j ≤
      ⨆ f : ↥V, ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0),
        ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
          (f : DirichletLaplacian.SmoothTestSpace Ω)) := by
  have hbridge : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j =
      ⨅ Vd : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω),
        ⨅ (_ : Module.finrank ℝ ↥Vd = j + 1),
          ⨆ f : ↥Vd, ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0),
            ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω)) :=
    variationalEigenvalue_eq_iInf_dirichletLaplacian Ω j
  rw [hbridge]
  exact le_trans (iInf_le _ V) (iInf_le _ hfin)

/-- Finite manifold value bounds the real value through `toReal`. -/
theorem real_le_toReal (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ)
    (hM : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j ≠ ⊤) :
    DirichletLaplacian.variationalEigenvalue Ω j ≤
      (variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j).toReal := by
  have hle : ENNReal.ofReal (DirichletLaplacian.variationalEigenvalue Ω j) ≤
      variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j :=
    ofReal_dirichletLaplacian_variationalEigenvalue_le Ω j
  have htop : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j ≠ ⊤ :=
    hM
  have hto : ENNReal.ofReal ((variationalEigenvalue 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j).toReal) =
      variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j :=
    ENNReal.ofReal_toReal htop
  have hle2 : ENNReal.ofReal (DirichletLaplacian.variationalEigenvalue Ω j) ≤
      ENNReal.ofReal ((variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j).toReal) := by
    rw [hto]
    exact hle
  have hnn : (0 : ℝ) ≤ ((variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j).toReal) :=
    ENNReal.toReal_nonneg
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp hle2

/-- Center of the concrete bump test function. -/
private def bumpCenter : EuclideanSpace ℝ (Fin 1) := 0

/-- Concrete smooth bump with fixed radii around the center. -/
private def bumpObj : ContDiffBump bumpCenter :=
  ContDiffBump.mk 1 2 one_pos one_lt_two

/-- Concrete nonzero test function on the whole space from the bump. -/
noncomputable def phi : DirichletLaplacian.SmoothTestSpace
    (⊤ : Opens (EuclideanSpace ℝ (Fin 1))) :=
  TestFunction.mk (↑bumpObj) bumpObj.contDiff bumpObj.hasCompactSupport (by
    rw [Opens.coe_top]
    exact Set.subset_univ _)

/-- The concrete test function equals `1` at the bump center. -/
theorem phi_center_eq_one : ⇑phi bumpCenter = 1 := by
  have hmem : bumpCenter ∈ Metric.closedBall bumpCenter bumpObj.rIn := by
    rw [Metric.mem_closedBall, dist_self]
    have hr : bumpObj.rIn = 1 := rfl
    rw [hr]
    exact zero_le_one
  exact ContDiffBump.one_of_mem_closedBall bumpObj hmem

/-- The concrete test function is nonzero since it is `1` at the center. -/
theorem phi_ne_zero : phi ≠ 0 := by
  intro h0
  have h1 : ⇑phi bumpCenter = 1 := phi_center_eq_one
  rw [h0] at h1
  simp at h1

/-- The core member has the same values as the concrete test function. -/
theorem core_apply (x : EuclideanSpace ℝ (Fin 1)) :
    ⇑((testFunctionLinearEquiv _ phi :
      ↥(smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) _)) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)),
        EuclideanSpace ℝ (Fin 1); 𝓘(ℝ, ℝ), ℝ⟯) x = ⇑phi x := by
  simp

/-- The core member of the concrete test function equals `1` at the bump center. -/
theorem core_at_center :
    ⇑((testFunctionLinearEquiv _ phi :
      ↥(smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) _)) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)),
        EuclideanSpace ℝ (Fin 1); 𝓘(ℝ, ℝ), ℝ⟯) bumpCenter = 1 := by
  simp [phi_center_eq_one]

/-- The core member of the concrete test function is nonzero. -/
theorem core_ne_zero :
    testFunctionLinearEquiv _ phi ≠ 0 := by
  intro h0
  apply phi_ne_zero
  have hsym : (testFunctionLinearEquiv _).symm
      (testFunctionLinearEquiv _ phi) = phi :=
    LinearEquiv.symm_apply_apply _ _
  rw [h0] at hsym
  simpa using hsym.symm

/-- The inverse equivalence sends the core member back to the test function. -/
theorem core_symm_apply :
    (testFunctionLinearEquiv _).symm (testFunctionLinearEquiv _ phi) =
      phi := by
  simp

/-- Mass of the core member is positive and finite via the core lemma. -/
theorem core_mass :
    0 < ∫⁻ x, ‖⇑((testFunctionLinearEquiv _ phi :
      ↥(smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) _)) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)),
        EuclideanSpace ℝ (Fin 1); 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂volume ∧
      ∫⁻ x, ‖⇑((testFunctionLinearEquiv _ phi :
      ↥(smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) _)) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)),
        EuclideanSpace ℝ (Fin 1); 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂volume < ⊤ :=
  mass_pos_lt_top_of_mem_smoothTestSubmodule volume
    (testFunctionLinearEquiv _ phi).property (by
      intro h0
      apply core_ne_zero
      apply Subtype.ext
      simpa using h0)

/-- The Dirichlet quotient of the concrete test function is positive. -/
theorem dirichlet_rayleigh_pos :
    0 < DirichletLaplacian.rayleighQuotient phi := by
  have hdiff : Differentiable ℝ (⇑phi) :=
    (TestFunction.contDiff phi).differentiable (by simp)
  have hex : ∃ x, fderiv ℝ (⇑phi) x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hconst : ∀ x y : EuclideanSpace ℝ (Fin 1),
        (⇑phi) x = (⇑phi) y := fun x y =>
      is_const_of_fderiv_eq_zero hdiff hcon x y
    have hone : ∀ x : EuclideanSpace ℝ (Fin 1), (⇑phi) x = 1 := by
      intro x
      rw [hconst x bumpCenter]
      exact phi_center_eq_one
    have hsupp_eq : Function.support (⇑phi) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      simp [Function.mem_support, hone x]
    have hts : tsupport (⇑phi) = Set.univ := by
      have h1 : tsupport (⇑phi) =
          closure (Function.support (⇑phi)) := rfl
      rw [h1, hsupp_eq, closure_univ]
    have his : IsCompact (tsupport (⇑phi)) :=
      HasCompactSupport.isCompact (TestFunction.hasCompactSupport phi)
    exact IsCompact.ne_univ his hts
  obtain ⟨x₀, hx₀⟩ := hex
  have hcontD : Continuous (fderiv ℝ (⇑phi)) :=
    (TestFunction.contDiff phi).continuous_fderiv (by simp)
  have hnum_cont : Continuous (fun x : EuclideanSpace ℝ (Fin 1) =>
      (‖fderiv ℝ (⇑phi) x‖ ^ 2 : ℝ)) :=
    hcontD.norm.pow 2
  have hsupp_deriv : HasCompactSupport (fderiv ℝ (⇑phi)) :=
    HasCompactSupport.fderiv ℝ (TestFunction.hasCompactSupport phi)
  have hnum_supp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 1) =>
      (‖fderiv ℝ (⇑phi) x‖ ^ 2 : ℝ)) :=
    hasCompactSupport_norm_sq hsupp_deriv
  have hnum_ne : (fun x : EuclideanSpace ℝ (Fin 1) =>
      (‖fderiv ℝ (⇑phi) x‖ ^ 2 : ℝ)) x₀ ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx₀)
  have hnum_pos : 0 < ∫ x : EuclideanSpace ℝ (Fin 1),
      (‖fderiv ℝ (⇑phi) x‖ ^ 2 : ℝ) ∂volume :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hnum_cont
      hnum_supp (fun x => sq_nonneg _) hnum_ne
  have hcontP : Continuous (fun x : EuclideanSpace ℝ (Fin 1) =>
      (|(⇑phi) x| ^ 2 : ℝ)) :=
    (TestFunction.continuous phi).abs.pow 2
  have hnorm_eq : (fun x : EuclideanSpace ℝ (Fin 1) =>
      (‖(⇑phi) x‖ ^ 2 : ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin 1) => (|(⇑phi) x| ^ 2 : ℝ)) := by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  have hden_supp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 1) =>
      (|(⇑phi) x| ^ 2 : ℝ)) := by
    rw [← hnorm_eq]
    exact hasCompactSupport_norm_sq (TestFunction.hasCompactSupport phi)
  have hden_ne : (fun x : EuclideanSpace ℝ (Fin 1) =>
      (|(⇑phi) x| ^ 2 : ℝ)) bumpCenter ≠ 0 := by
    simp only [phi_center_eq_one]
    norm_num
  have hden_pos : 0 < ∫ x : EuclideanSpace ℝ (Fin 1),
      (|(⇑phi) x| ^ 2 : ℝ) ∂volume :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcontP
      hden_supp (fun x => sq_nonneg _) hden_ne
  unfold DirichletLaplacian.rayleighQuotient
  exact div_pos hnum_pos hden_pos

/-- Bridge equality for the concrete test function through `ofReal`. -/
theorem manifold_rayleigh_eq :
    rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) volume ⇑phi =
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient phi) :=
  rayleighQuotient_testFunction phi

/-- The manifold quotient of the concrete function is positive and finite. -/
theorem manifold_rayleigh_pos_fin :
    0 < rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) volume ⇑phi ∧
      rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) volume ⇑phi ≠ ⊤ := by
  rw [manifold_rayleigh_eq]
  exact ⟨ENNReal.ofReal_pos.mpr dirichlet_rayleigh_pos,
    ENNReal.ofReal_ne_top⟩

/-- Scaling the concrete test function does not change its Dirichlet quotient. -/
theorem dirichlet_rayleigh_smul (c : ℝ) (hc : c ≠ 0) :
    DirichletLaplacian.rayleighQuotient (c • phi) =
      DirichletLaplacian.rayleighQuotient phi := by
  have hdiff : Differentiable ℝ (⇑phi) :=
    (TestFunction.contDiff phi).differentiable (by simp)
  have hfun2 : (⇑(c • phi) : EuclideanSpace ℝ (Fin 1) → ℝ) = c • ⇑phi := by
    funext x
    simp [smul_eq_mul]
  have hderiv_fun : fderiv ℝ (⇑(c • phi)) =
      fun x => c • fderiv ℝ (⇑phi) x := by
    funext x
    rw [hfun2]
    exact fderiv_const_smul (hdiff.differentiableAt) c
  have hc2 : (c ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hc
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 1),
      (‖fderiv ℝ (⇑(c • phi)) x‖ ^ 2 : ℝ) =
        (c ^ 2) * (‖fderiv ℝ (⇑phi) x‖ ^ 2) := by
    intro x
    rw [show fderiv ℝ (⇑(c • phi)) x = c • fderiv ℝ (⇑phi) x from
      congrFun hderiv_fun x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hden : ∀ x : EuclideanSpace ℝ (Fin 1),
      (|(⇑(c • phi)) x| ^ 2 : ℝ) = (c ^ 2) * (|(⇑phi) x| ^ 2) := by
    intro x
    rw [hfun2, Pi.smul_apply, smul_eq_mul, abs_mul, mul_pow, sq_abs]
  have hnum : (∫ x : EuclideanSpace ℝ (Fin 1),
      (‖fderiv ℝ (⇑(c • phi)) x‖ ^ 2 : ℝ) ∂volume) =
      (c ^ 2) * (∫ x : EuclideanSpace ℝ (Fin 1),
        (‖fderiv ℝ (⇑phi) x‖ ^ 2 : ℝ) ∂volume) := by
    rw [show (fun x : EuclideanSpace ℝ (Fin 1) =>
      (‖fderiv ℝ (⇑(c • phi)) x‖ ^ 2 : ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin 1) =>
        (c ^ 2) * (‖fderiv ℝ (⇑phi) x‖ ^ 2)) from funext hnorm,
      integral_const_mul]
  have hdenI : (∫ x : EuclideanSpace ℝ (Fin 1),
      (|(⇑(c • phi)) x| ^ 2 : ℝ) ∂volume) =
      (c ^ 2) * (∫ x : EuclideanSpace ℝ (Fin 1),
        (|(⇑phi) x| ^ 2 : ℝ) ∂volume) := by
    rw [show (fun x : EuclideanSpace ℝ (Fin 1) =>
      (|(⇑(c • phi)) x| ^ 2 : ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin 1) =>
        (c ^ 2) * (|(⇑phi) x| ^ 2)) from funext hden,
      integral_const_mul]
  unfold DirichletLaplacian.rayleighQuotient
  rw [hnum, hdenI, mul_div_mul_left _ _ hc2]

/-- Scaling does not change the manifold quotient through the bridge. -/
theorem manifold_rayleigh_smul (c : ℝ) (hc : c ≠ 0) :
    rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) volume ⇑(c • phi) =
      rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) volume ⇑phi := by
  rw [rayleighQuotient_testFunction (c • phi),
    rayleighQuotient_testFunction phi, dirichlet_rayleigh_smul c hc]

/-- One-dimensional witness gives a finite min-max upper bound at index `0`. -/
theorem minmax_le_fin :
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
        (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))) volume 0 ≤
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient phi) ∧
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
        (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))) volume 0 < ⊤ := by
  have hfin : Module.finrank ℝ ↥(ℝ ∙ phi) = 0 + 1 := by
    simpa using finrank_span_singleton phi_ne_zero
  have hsup : (⨆ f : ↥(ℝ ∙ phi),
      ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace
        (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))) ≠ 0),
        ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
          (f : DirichletLaplacian.SmoothTestSpace
            (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))))) ≤
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient phi) := by
    apply iSup_le
    intro f
    apply iSup_le
    intro hne
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp f.property
    have ha0 : a ≠ 0 := by
      intro hz
      apply hne
      rw [← ha, hz, zero_smul]
    have heq : DirichletLaplacian.rayleighQuotient
        (f : DirichletLaplacian.SmoothTestSpace
          (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))) =
        DirichletLaplacian.rayleighQuotient phi := by
      rw [← ha]
      exact dirichlet_rayleigh_smul a ha0
    rw [heq]
  have hle : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
        (⊤ : Opens (EuclideanSpace ℝ (Fin 1)))) volume 0 ≤
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient phi) :=
    le_trans (witness_le _ 0 _ hfin) hsup
  exact ⟨hle, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩

end Manifold.VariationalEigenvalueEuclideanTest
