/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.VariationalEigenvalue
public import MathlibExt.Analysis.InnerProductSpace.DirichletSpectrum

/-!
# Euclidean bridge for variational eigenvalues

`DirichletLaplacian.SmoothTestSpace`, `DirichletLaplacian.rayleighQuotient`,
`DirichletLaplacian.variationalEigenvalue` and
`NonnegativeDiscreteSpectrum.IsDirichletSpectrum` form the Euclidean API on
open subsets of `EuclideanSpace` with `volume`. The `Manifold` API with
`Manifold.rayleighQuotient`, `Manifold.variationalEigenvalue` and
`Manifold.smoothTestSubmodule` covers Riemannian manifolds and weighted
measures, with explicit `⊤` for empty admissible families. Use the
`DirichletLaplacian` API for Euclidean domains going through
`NonnegativeDiscreteSpectrum.IsDirichletSpectrum`, and the `Manifold` API for
manifolds and weighted measures. `Manifold.testFunctionLinearEquiv` identifies
the bundled `TestFunction` core with the predicate-defined
`Manifold.smoothTestSubmodule` on a normed space. Proved here: Rayleigh
quotients agree through `ENNReal.ofReal`; the real min-max value is `≤` the
manifold value; `Manifold.variationalEigenvalue_eq_iInf_dirichletLaplacian`
identifies the manifold min-max with the `ℝ≥0∞` min-max of the real quotient;
`Manifold.variationalEigenvalue_eq_top_of_forall_finrank_ne` shows that if no
`(j+1)`-dimensional submodule of the test space exists, then the manifold
value is `⊤` and the real value is `0`. Separately, the
real `sSup` of a set that is not bounded above is `0`, so the comparison in
`Manifold.ofReal_dirichletLaplacian_variationalEigenvalue_le` is stated only
as `≤`; the reverse inequality is not proved here.
`Manifold.mass_pos_lt_top_of_mem_smoothTestSubmodule`, proved in the core module,
shows nonzero core members have positive finite mass, so the admissibility
condition of `Manifold.variationalEigenvalue` holds automatically on the core
and is used here. `Manifold.dirichletEigenvalue` is not bridged here because
it uses `Manifold.riemannianVolume`, whose equality with `volume` on `EuclideanSpace`
is not available at this pin for `n ≥ 2`.
-/

@[expose] public section
open TopologicalSpace MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
noncomputable section
namespace Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Linear equivalence between bundled test functions and the smooth core. -/
def testFunctionLinearEquiv (Ω : Opens E) :
    TestFunction Ω ℝ ⊤ ≃ₗ[ℝ] ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω) where
  toFun := fun f : TestFunction Ω ℝ ⊤ =>
    ⟨⟨⇑f, contMDiff_iff_contDiff.mpr (TestFunction.contDiff f)⟩,
      TestFunction.hasCompactSupport f, TestFunction.tsupport_subset f⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro x
    rfl
  map_smul' := by
    intro r f
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro x
    rfl
  invFun := fun u : ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω) =>
    ⟨⇑(u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯),
      contMDiff_iff_contDiff.mp
        (ContMDiffMap.contMDiff (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯)),
      u.property.1, u.property.2⟩
  left_inv := by
    intro f
    apply TestFunction.ext
    intro a
    rfl
  right_inv := by
    intro u
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro x
    rfl

/-- Coercion of the forward equivalence is the bundled coercion. -/
@[simp] theorem coe_testFunctionLinearEquiv (Ω : Opens E)
    (f : TestFunction Ω ℝ ⊤) :
    ⇑((testFunctionLinearEquiv Ω f : ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω)) :
      C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯) = ⇑f :=
  rfl

/-- Coercion of the inverse equivalence is the bundled coercion. -/
@[simp] theorem coe_testFunctionLinearEquiv_symm (Ω : Opens E)
    (u : ↥(smoothTestSubmodule 𝓘(ℝ, E) Ω)) :
    ⇑((testFunctionLinearEquiv Ω).symm u) =
      ⇑(u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, ℝ), ℝ⟯) :=
  rfl

/-- Finrank of the transferred Dirichlet submodule equals the original. -/
private theorem finrank_map_comap_eq {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (V' : Submodule ℝ C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯)
    (hVW : V' ≤ smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) :
    Module.finrank ℝ ↥(Submodule.map (testFunctionLinearEquiv Ω).symm.toLinearMap
      (Submodule.comap
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
        V')) = Module.finrank ℝ ↥V' := by
  set S := smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω with hSdef
  have hmap : Submodule.map S.subtype (Submodule.comap S.subtype V') = V' := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Submodule.comap S.subtype V',
          S.subtype y = x := Submodule.mem_map.mp hx
      rw [← hyx]
      exact Submodule.mem_comap.mp hy
    · intro x hx
      have hxW : x ∈ S := hVW hx
      exact Submodule.mem_map.mpr ⟨⟨x, hxW⟩, Submodule.mem_comap.mpr hx, rfl⟩
  have heq : Module.finrank ℝ ↥(Submodule.comap S.subtype V') =
      Module.finrank ℝ ↥(Submodule.map S.subtype
        (Submodule.comap S.subtype V')) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ Subtype.val_injective _)
  have hfin : Module.finrank ℝ ↥(Submodule.map
      (testFunctionLinearEquiv Ω).symm.toLinearMap
      (Submodule.comap S.subtype V')) =
      Module.finrank ℝ ↥(Submodule.comap S.subtype V') :=
    LinearEquiv.finrank_map_eq _ _
  rw [hfin, heq, hmap]

/-- Manifold and Euclidean Rayleigh quotients agree through `ofReal`. -/
theorem rayleighQuotient_testFunction {n : ℕ}
    {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (f : DirichletLaplacian.SmoothTestSpace Ω) :
    rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
        (f : EuclideanSpace ℝ (Fin n) → ℝ) =
      ENNReal.ofReal (DirichletLaplacian.rayleighQuotient f) := by
  have hcont : Continuous (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
    TestFunction.continuous f
  have hsupp : HasCompactSupport (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
    TestFunction.hasCompactSupport f
  have hderiv : Continuous (fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ)) :=
    (TestFunction.contDiff f).continuous_fderiv (by simp)
  have hnum_cont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ)) :=
    hderiv.norm.pow 2
  have hden_cont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ)) :=
    hcont.abs.pow 2
  have hsupp_deriv : HasCompactSupport
      (fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ)) :=
    HasCompactSupport.fderiv ℝ hsupp
  have hnum_supp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) =>
      (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ)) :=
    hasCompactSupport_norm_sq (g := fderiv ℝ _) hsupp_deriv
  have hnorm_eq : (fun x : EuclideanSpace ℝ (Fin n) =>
      (‖(f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ)) =
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ)) := by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  have hden_supp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) =>
      (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ)) := by
    rw [← hnorm_eq]
    exact hasCompactSupport_norm_sq (g := (f : _ → ℝ)) hsupp
  by_cases hf0 : f = 0
  · have hfun0 : (f : EuclideanSpace ℝ (Fin n) → ℝ) =
        (0 : EuclideanSpace ℝ (Fin n) → ℝ) := by rw [hf0]; rfl
    have henergy : dirichletEnergy 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
        (f : EuclideanSpace ℝ (Fin n) → ℝ) = 0 := by
      rw [hfun0]
      exact dirichletEnergy_const _ volume 0
    have hmass0 : (∫⁻ x : EuclideanSpace ℝ (Fin n),
        (‖(f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) ∂volume) = 0 := by
      rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
          (‖(f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2)) =
          (fun _ => (0 : ℝ≥0∞)) by funext x; rw [hfun0]; simp]
      exact lintegral_zero
    have hL : rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
        (f : EuclideanSpace ℝ (Fin n) → ℝ) = 0 := by
      unfold rayleighQuotient
      rw [henergy, hmass0]
      exact ENNReal.zero_div
    have hR : DirichletLaplacian.rayleighQuotient f = 0 := by
      have hfd : fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) = 0 := by
        rw [hfun0]; simp
      unfold DirichletLaplacian.rayleighQuotient
      rw [hfd, hfun0]
      simp
    rw [hL, hR]
    simp
  · have hfne : (f : EuclideanSpace ℝ (Fin n) → ℝ) ≠
        (0 : EuclideanSpace ℝ (Fin n) → ℝ) := by
      intro h0
      apply hf0
      apply TestFunction.ext
      intro a
      exact congrFun h0 a
    obtain ⟨x₀, hx₀⟩ : ∃ x, (f : EuclideanSpace ℝ (Fin n) → ℝ) x ≠ 0 := by
      obtain ⟨y, hy⟩ : ∃ x, (f : EuclideanSpace ℝ (Fin n) → ℝ) x ≠
          (0 : EuclideanSpace ℝ (Fin n) → ℝ) x := Function.ne_iff.mp hfne
      exact ⟨y, by simpa using hy⟩
    have hden_ne : (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x₀| ^ 2 : ℝ) ≠ 0 :=
      pow_ne_zero 2 (abs_ne_zero.mpr hx₀)
    have hden_pos : 0 < ∫ x : EuclideanSpace ℝ (Fin n),
        (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ) ∂volume :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hden_cont
        hden_supp (fun x => sq_nonneg _) hden_ne
    have hnum_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ)) volume :=
      Continuous.integrable_of_hasCompactSupport hnum_cont hnum_supp
    have hden_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ)) volume :=
      Continuous.integrable_of_hasCompactSupport hden_cont hden_supp
    have hnum_ae : 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin n) =>
        (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ)) :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    have hden_ae : 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin n) =>
        (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ)) :=
      Filter.Eventually.of_forall fun _ => sq_nonneg _
    have hnum_eq : ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
        (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ) ∂volume) =
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
          (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) ∂volume := by
      have hbase : ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
          (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ) ∂volume) =
          ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
            (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2) ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hnum_int hnum_ae
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2)
            = (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) := by
        intro x
        have hnn : (0 : ℝ) ≤ ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ :=
          norm_nonneg _
        have h1 : ENNReal.ofReal ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ =
            ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ := by
          rw [show (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ : ℝ) =
            (((‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖₊ : ℝ≥0)) : ℝ)
            by rw [coe_nnnorm]]
          rw [ENNReal.ofReal_coe_nnreal, enorm_eq_nnnorm]
        rw [ENNReal.ofReal_pow hnn 2, h1]
      rw [hbase]
      exact congrArg _ (funext hpt)
    have hden_eq : ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
        (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ) ∂volume) =
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
          (‖(f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) ∂volume := by
      have hbase : ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
          (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ) ∂volume) =
          ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
            (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2) ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hden_int hden_ae
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2) =
            (‖(f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) := by
        intro x
        rw [ENNReal.ofReal_pow (abs_nonneg _) 2, ← Real.enorm_eq_ofReal_abs _]
      rw [hbase]
      exact congrArg _ (funext hpt)
    have henergy_eq : dirichletEnergy 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        volume (f : EuclideanSpace ℝ (Fin n) → ℝ) =
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
          (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ₑ ^ 2) ∂volume :=
      dirichletEnergy_vectorSpace volume _
    have hdiv : ENNReal.ofReal
        ((∫ x : EuclideanSpace ℝ (Fin n),
          (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ) ∂volume) /
          (∫ x : EuclideanSpace ℝ (Fin n),
            (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ) ∂volume)) =
        ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
          (‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 : ℝ) ∂volume) /
          ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
            (|(f : EuclideanSpace ℝ (Fin n) → ℝ) x| ^ 2 : ℝ) ∂volume) :=
      ENNReal.ofReal_div_of_pos hden_pos
    unfold rayleighQuotient DirichletLaplacian.rayleighQuotient
    rw [henergy_eq, hdiv, hnum_eq, hden_eq]

/-- Real min-max is below the manifold min-max through `ofReal`. -/
theorem ofReal_dirichletLaplacian_variationalEigenvalue_le {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    ENNReal.ofReal (DirichletLaplacian.variationalEigenvalue Ω j) ≤
      variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j := by
  have hqnn : ∀ a : DirichletLaplacian.SmoothTestSpace Ω,
      0 ≤ DirichletLaplacian.rayleighQuotient a := by
    intro a
    unfold DirichletLaplacian.rayleighQuotient
    exact div_nonneg (integral_nonneg_of_ae (Filter.Eventually.of_forall
      fun x => sq_nonneg _)) (integral_nonneg_of_ae (Filter.Eventually.of_forall
      fun x => sq_nonneg _))
  have hbdd : BddBelow {a : ℝ | ∃ V : Submodule ℝ
      (DirichletLaplacian.SmoothTestSpace Ω),
      Module.finrank ℝ ↥V = j + 1 ∧
        a = sSup {q : ℝ | ∃ f : ↥V,
          (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
            DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω) = q}} := by
    refine ⟨0, ?_⟩
    intro a ha
    obtain ⟨V, hfinV, rfl⟩ : ∃ V : Submodule ℝ
        (DirichletLaplacian.SmoothTestSpace Ω), _ ∧ _ := ha
    apply Real.sSup_nonneg
    intro q hq
    obtain ⟨fp, hnefp, rfl⟩ : ∃ f : ↥V,
        (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧ _ := hq
    exact hqnn _
  apply le_iInf
  intro V'
  apply le_iInf
  intro hVW
  apply le_iInf
  intro hfin
  apply le_iInf
  intro hmass
  let Vd : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω) :=
    Submodule.map (testFunctionLinearEquiv Ω).symm.toLinearMap
      (Submodule.comap
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype V')
  have hfinD : Module.finrank ℝ ↥Vd = j + 1 := by
    have h1 : Module.finrank ℝ ↥Vd = Module.finrank ℝ ↥V' :=
      finrank_map_comap_eq Ω V' hVW
    rw [h1, hfin]
  have hmem : sSup {q : ℝ | ∃ f : ↥Vd,
      (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
        DirichletLaplacian.rayleighQuotient
          (f : DirichletLaplacian.SmoothTestSpace Ω) = q} ∈
      {a : ℝ | ∃ V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω),
        Module.finrank ℝ ↥V = j + 1 ∧
          a = sSup {q : ℝ | ∃ f : ↥V,
            (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
              DirichletLaplacian.rayleighQuotient
                (f : DirichletLaplacian.SmoothTestSpace Ω) = q}} :=
    ⟨Vd, hfinD, rfl⟩
  have hle : sInf {a : ℝ | ∃ V : Submodule ℝ
      (DirichletLaplacian.SmoothTestSpace Ω),
      Module.finrank ℝ ↥V = j + 1 ∧
        a = sSup {q : ℝ | ∃ f : ↥V,
          (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
            DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω) = q}} ≤
      sSup {q : ℝ | ∃ f : ↥Vd,
        (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
          DirichletLaplacian.rayleighQuotient
            (f : DirichletLaplacian.SmoothTestSpace Ω) = q} :=
    csInf_le hbdd hmem
  have hof1 : ENNReal.ofReal (DirichletLaplacian.variationalEigenvalue Ω j) ≤
      ENNReal.ofReal (sSup {q : ℝ | ∃ f : ↥Vd,
        (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
          DirichletLaplacian.rayleighQuotient
            (f : DirichletLaplacian.SmoothTestSpace Ω) = q}) :=
    ENNReal.ofReal_le_ofReal hle
  set b : ℝ≥0∞ := ⨆ (u : ↥V'), ⨆ (_ : u ≠ 0),
    rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
      ⇑(u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯)
  have hof2 : ENNReal.ofReal (sSup {q : ℝ | ∃ f : ↥Vd,
      (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
        DirichletLaplacian.rayleighQuotient
          (f : DirichletLaplacian.SmoothTestSpace Ω) = q}) ≤ b := by
    by_cases hbtop : b = ⊤
    · rw [hbtop]
      exact le_top
    · have hbne : b ≠ (⊤ : ℝ≥0∞) := hbtop
      have htb : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hbne
      have ht0 : (0 : ℝ) ≤ b.toReal := ENNReal.toReal_nonneg
      have hsup_le : sSup {q : ℝ | ∃ f : ↥Vd,
          (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
            DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω) = q} ≤ b.toReal := by
        refine Real.sSup_le ?_ ht0
        intro q hq
        obtain ⟨fp, hfpne, rfl⟩ : ∃ f : ↥Vd,
            (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧ _ := hq
        obtain ⟨y, hyQ, hyx⟩ : ∃ y ∈ Submodule.comap
            (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype V',
            ⇑(testFunctionLinearEquiv Ω).symm.toLinearMap y =
              (fp : DirichletLaplacian.SmoothTestSpace Ω) :=
          Submodule.mem_map.mp fp.property
        have hyV : (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
            y ∈ V' := Submodule.mem_comap.mp hyQ
        have hyx' : (testFunctionLinearEquiv Ω).symm y =
            (fp : DirichletLaplacian.SmoothTestSpace Ω) := hyx
        set u0 : ↥V' := ⟨(smoothTestSubmodule 𝓘(ℝ,
            EuclideanSpace ℝ (Fin n)) Ω).subtype y, hyV⟩ with hu0def
        have hu_eq : (u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
            (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
              y := by
          rw [hu0def]
        have hcoe_fun : (⇑(fp : DirichletLaplacian.SmoothTestSpace Ω) :
            EuclideanSpace ℝ (Fin n) → ℝ) = ⇑(u0 : C^∞⟮𝓘(ℝ,
              EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n);
              𝓘(ℝ, ℝ), ℝ⟯) := by
          rw [← hyx', coe_testFunctionLinearEquiv_symm Ω y, hu_eq]
          rfl
        have hu0 : u0 ≠ 0 := by
          intro h0
          apply hfpne
          have hcongr : (u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
              EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
              ((0 : ↥V') : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
            congrArg Subtype.val h0
          have hzero_val : ((0 : ↥V') : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
              EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
              (0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) := by
            simp
          have hcu : (u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
              EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) = 0 :=
            hcongr.trans hzero_val
          have hfun0 : (⇑(fp : DirichletLaplacian.SmoothTestSpace Ω) :
              EuclideanSpace ℝ (Fin n) → ℝ) =
              (0 : EuclideanSpace ℝ (Fin n) → ℝ) := by
            rw [hcoe_fun, hcu, ContMDiffMap.coe_zero]
          apply TestFunction.ext
          intro a
          exact congrFun hfun0 a
        have hof : ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
            (fp : DirichletLaplacian.SmoothTestSpace Ω)) ≤ b := by
          rw [← rayleighQuotient_testFunction, hcoe_fun]
          change rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
              ⇑(u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) ≤
              ⨆ (u : ↥V'), ⨆ (_ : u ≠ 0),
                rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
                  ⇑(u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                    EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯)
          calc rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
                  ⇑(u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                    EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯)
              ≤ ⨆ (_ : u0 ≠ 0), rayleighQuotient 𝓘(ℝ,
                  EuclideanSpace ℝ (Fin n)) volume
                  ⇑(u0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                    EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
                le_iSup (fun (_ : u0 ≠ 0) => rayleighQuotient 𝓘(ℝ,
                  EuclideanSpace ℝ (Fin n)) volume ⇑(u0 : C^∞⟮𝓘(ℝ,
                    EuclideanSpace ℝ (Fin n)), EuclideanSpace ℝ (Fin n);
                    𝓘(ℝ, ℝ), ℝ⟯)) hu0
            _ ≤ ⨆ (u : ↥V'), ⨆ (_ : u ≠ 0),
                  rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
                    ⇑(u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                      EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
                le_iSup (fun u : ↥V' => ⨆ (_ : u ≠ 0),
                  rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
                    ⇑(u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
                      EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯)) u0
        have hof' : ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
            (fp : DirichletLaplacian.SmoothTestSpace Ω)) ≤
            ENNReal.ofReal b.toReal := by
          rw [htb]
          exact hof
        exact (ENNReal.ofReal_le_ofReal_iff ht0).mp hof'
      have hle' : ENNReal.ofReal (sSup {q : ℝ | ∃ f : ↥Vd,
          (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
            DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω) = q}) ≤
          ENNReal.ofReal b.toReal :=
        ENNReal.ofReal_le_ofReal hsup_le
      rw [htb] at hle'
      exact hle'
  exact hof1.trans hof2

/-- Junk-value case: no `(j+1)`-dimensional test space on either side. -/
theorem variationalEigenvalue_eq_top_of_forall_finrank_ne {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ)
    (h : ∀ V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω),
      Module.finrank ℝ ↥V ≠ j + 1) :
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j = ⊤ ∧
      DirichletLaplacian.variationalEigenvalue Ω j = 0 := by
  have hempty : {a : ℝ | ∃ V : Submodule ℝ
      (DirichletLaplacian.SmoothTestSpace Ω),
      Module.finrank ℝ ↥V = j + 1 ∧
        a = sSup {q : ℝ | ∃ f : ↥V,
          (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0 ∧
            DirichletLaplacian.rayleighQuotient
              (f : DirichletLaplacian.SmoothTestSpace Ω) = q}} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨V, hfinV, rfl⟩ : ∃ V : Submodule ℝ
        (DirichletLaplacian.SmoothTestSpace Ω), _ ∧ _ := ha
    exact h V hfinV
  have hDir : DirichletLaplacian.variationalEigenvalue Ω j = 0 := by
    unfold DirichletLaplacian.variationalEigenvalue
    rw [hempty, Real.sInf_empty]
  have hTop : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j = ⊤ := by
    apply iInf_eq_top.mpr
    intro V'
    apply iInf_eq_top.mpr
    intro hVW
    apply iInf_eq_top.mpr
    intro hfin
    have hfinD : Module.finrank ℝ ↥(Submodule.map
        (testFunctionLinearEquiv Ω).symm.toLinearMap (Submodule.comap
          (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
          V')) = j + 1 := by
      rw [finrank_map_comap_eq Ω V' hVW, hfin]
    exact False.elim (h _ hfinD)
  exact ⟨hTop, hDir⟩

/-- Manifold min-max equals the `ℝ≥0∞` min-max of the real quotient. -/
theorem variationalEigenvalue_eq_iInf_dirichletLaplacian {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j =
      ⨅ V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω),
        ⨅ (_ : Module.finrank ℝ ↥V = j + 1),
          ⨆ f : ↥V, ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0),
            ENNReal.ofReal
              (DirichletLaplacian.rayleighQuotient
                (f : DirichletLaplacian.SmoothTestSpace Ω)) := by
  apply le_antisymm
  · apply le_iInf
    intro Vd
    apply le_iInf
    intro hfinD
    set V' := Submodule.map
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
        (Submodule.map (testFunctionLinearEquiv Ω).toLinearMap Vd) with hV'def
    have hVW : V' ≤
        smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω := by
      intro x hx
      have hu_mem : x ∈ Submodule.map
          (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
          (Submodule.map (testFunctionLinearEquiv Ω).toLinearMap Vd) := by
        rw [← hV'def]
        exact hx
      obtain ⟨y, _, hyx⟩ : ∃ y, y ∈ Submodule.map
          (testFunctionLinearEquiv Ω).toLinearMap Vd ∧
          (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
            y = x :=
        Submodule.mem_map.mp hu_mem
      have hxS : (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
          y ∈ smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω :=
        y.property
      rw [hyx] at hxS
      exact hxS
    have hfin : Module.finrank ℝ ↥V' = j + 1 := by
      have h1 : Module.finrank ℝ ↥V' = Module.finrank ℝ ↥(Submodule.map
          (testFunctionLinearEquiv Ω).toLinearMap Vd) := by
        rw [hV'def]
        exact Submodule.finrank_map_subtype_eq _ _
      have h2 : Module.finrank ℝ ↥(Submodule.map
          (testFunctionLinearEquiv Ω).toLinearMap Vd) =
          Module.finrank ℝ ↥Vd :=
        LinearEquiv.finrank_map_eq _ _
      rw [h1, h2, hfinD]
    have hmass : ∀ u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V' → u ≠ 0 →
        0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂volume ∧
          ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂volume < ⊤ := by
      intro u hu hne
      exact mass_pos_lt_top_of_mem_smoothTestSubmodule volume (hVW hu) hne
    have hle : variationalEigenvalue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω) volume j ≤
        ⨆ u : ↥V', ⨆ (_ : u ≠ 0), rayleighQuotient 𝓘(ℝ,
          EuclideanSpace ℝ (Fin n)) volume
          ⇑(u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
      variationalEigenvalue_le_iSup _ volume j hVW hfin hmass
    apply le_trans hle
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    have hu_mem : (u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) ∈ Submodule.map
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
        (Submodule.map (testFunctionLinearEquiv Ω).toLinearMap Vd) := by
      rw [← hV'def]
      exact u.property
    obtain ⟨y, hyq, hyx⟩ : ∃ y, y ∈ Submodule.map
        (testFunctionLinearEquiv Ω).toLinearMap Vd ∧
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
          y = (u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
      Submodule.mem_map.mp hu_mem
    obtain ⟨fval, hfVd, hfy⟩ : ∃ a, a ∈ Vd ∧
        (testFunctionLinearEquiv Ω).toLinearMap a = y :=
      Submodule.mem_map.mp hyq
    have hfval_ne : fval ≠ 0 := by
      intro h0
      apply hu
      apply Subtype.ext
      have hy0 : y = 0 := by
        rw [← hfy, h0]
        exact map_zero _
      have hu0 : (u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) = 0 := by
        rw [← hyx, hy0]
        exact map_zero _
      exact hu0
    have hfun : (⇑(u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :
        EuclideanSpace ℝ (Fin n) → ℝ) = ⇑fval := by
      rw [← hyx, ← hfy]
      exact coe_testFunctionLinearEquiv Ω fval
    have hR : rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
        ⇑(u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
        ENNReal.ofReal (DirichletLaplacian.rayleighQuotient fval) := by
      rw [hfun]
      exact rayleighQuotient_testFunction fval
    rw [hR]
    apply le_iSup_of_le ⟨fval, hfVd⟩
    apply le_iSup_of_le hfval_ne
    exact le_rfl
  · apply le_iInf
    intro V'
    apply le_iInf
    intro hVW
    apply le_iInf
    intro hfin
    apply le_iInf
    intro _
    set Vd := Submodule.map (testFunctionLinearEquiv Ω).symm.toLinearMap
        (Submodule.comap
          (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
          V') with hVddef
    have hfinD : Module.finrank ℝ ↥Vd = j + 1 := by
      rw [hVddef, finrank_map_comap_eq Ω V' hVW, hfin]
    have hle : (⨅ V : Submodule ℝ (DirichletLaplacian.SmoothTestSpace Ω),
          ⨅ (_ : Module.finrank ℝ ↥V = j + 1), ⨆ f : ↥V,
            ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0),
              ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
                (f : DirichletLaplacian.SmoothTestSpace Ω))) ≤
        ⨆ f : ↥Vd, ⨆ (_ : (f : DirichletLaplacian.SmoothTestSpace Ω) ≠ 0),
          ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
            (f : DirichletLaplacian.SmoothTestSpace Ω)) :=
      le_trans (iInf_le _ Vd) (iInf_le _ hfinD)
    apply le_trans hle
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    have hf_mem : (f.val : DirichletLaplacian.SmoothTestSpace Ω) ∈
        Submodule.map (testFunctionLinearEquiv Ω).symm.toLinearMap
          (Submodule.comap
            (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
            V') := by
      rw [← hVddef]
      exact f.property
    obtain ⟨y, hyQ, hyx⟩ : ∃ y, y ∈ Submodule.comap
        (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype V' ∧
        (testFunctionLinearEquiv Ω).symm.toLinearMap y =
          (f.val : DirichletLaplacian.SmoothTestSpace Ω) :=
      Submodule.mem_map.mp hf_mem
    have huV : (smoothTestSubmodule 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) Ω).subtype
        y ∈ V' :=
      Submodule.mem_comap.mp hyQ
    set u : ↥V' := ⟨(smoothTestSubmodule 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n)) Ω).subtype y, huV⟩ with hu_def
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hf
      have hcongr : (u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
          ((0 : ↥V') : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) :=
        congrArg Subtype.val h0
      have hzero_val : ((0 : ↥V') : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
          (0 : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) := by
        simp
      have hu_val : (u : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) =
          (smoothTestSubmodule 𝓘(ℝ,
            EuclideanSpace ℝ (Fin n)) Ω).subtype y := by
        rw [hu_def]
      have hval0 : (smoothTestSubmodule 𝓘(ℝ,
          EuclideanSpace ℝ (Fin n)) Ω).subtype y = 0 := by
        rw [← hu_val, hcongr, hzero_val]
      have hy0 : y = 0 := by
        apply Subtype.ext
        exact hval0
      rw [← hyx, hy0]
      exact map_zero _
    have hfun : (⇑(f.val : DirichletLaplacian.SmoothTestSpace Ω) :
        EuclideanSpace ℝ (Fin n) → ℝ) =
        ⇑(u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
          EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) := by
      rw [← hyx]
      exact coe_testFunctionLinearEquiv_symm Ω y
    have hR : ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
        (f.val : DirichletLaplacian.SmoothTestSpace Ω)) =
        rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
          ⇑(u.val : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
            EuclideanSpace ℝ (Fin n); 𝓘(ℝ, ℝ), ℝ⟯) := by
      have hbase : rayleighQuotient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) volume
          ⇑(f.val : DirichletLaplacian.SmoothTestSpace Ω) =
          ENNReal.ofReal (DirichletLaplacian.rayleighQuotient
            (f.val : DirichletLaplacian.SmoothTestSpace Ω)) :=
        rayleighQuotient_testFunction _
      rw [hfun] at hbase
      exact hbase.symm
    rw [hR]
    apply le_iSup_of_le u
    apply le_iSup_of_le hu_ne
    exact le_rfl

end Manifold
