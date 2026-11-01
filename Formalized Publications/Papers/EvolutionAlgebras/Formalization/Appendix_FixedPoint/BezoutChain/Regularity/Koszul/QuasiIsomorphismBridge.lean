/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ReducedMasters
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExtComparison
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Koszul quasi-isomorphism bridge (R2 exactness → augmentation quasi-iso)

This file builds the augmentation pair `(π, QuasiIso π)` that `ExtComparison`
(step A5, part 2) and `SelfDuality` R-D3 consume: the chain map from the
Koszul chain complex to the residue-field single complex, plus its
quasi-isomorphism proof, from R2 exactness. It unblocks C1+C2
(`koszulProjectiveResolutionOfSequence` + `koszulExt_subsingleton_below`).

## Survey: what turns pointwise exactness into `QuasiIso`?

Mathlib `v4.34.0` has the endpoint pieces but no "augmented exact complex
gives a quasi-isomorphism" lemma (the only link is a project comment at
`Algebra/Homology/Augment.lean`). The consumed API:

* `ChainComplex.toSingle₀Equiv` (`Algebra/Homology/Single.lean`):
  `(C ⟶ single₀.obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }` —
  builds `π` from the augmentation, with
  `toSingle₀Equiv_symm_apply_f_zero` (`Single.lean`).
* `quasiIsoAt_iff_exactAt` (`Algebra/Homology/QuasiIso.lean`):
  from `K.ExactAt i`, `QuasiIsoAt f i ↔ L.ExactAt i` — positive degrees.
* `ChainComplex.exactAt_succ_single_obj` (`Algebra/Homology/SingleHomology.lean`):
  single complexes are exact away from `0`.
* `ChainComplex.quasiIsoAt₀_iff` (`Algebra/Homology/QuasiIso.lean`):
  degree-0 reduction to the `sc' 1 0 0` short-complex map.
* `ShortComplex.quasiIso_iff_isIso_leftHomologyMap'`
  (`Algebra/Homology/ShortComplex/QuasiIso.lean`): `QuasiIso φ` from an
  explicit left-homology map iso.
* `ShortComplex.moduleCat_exact_iff`
  (`Algebra/Homology/ShortComplex/ModuleCat.lean`): element-level
  exactness in `ModuleCat`; `moduleCatLeftHomologyData`  with
  `moduleCatLeftHomologyData_f'_hom`; the map characterizations
  `cyclesMap'_i` (`ShortComplex/LeftHomology.lean`) and
  `leftHomologyπ_naturality'`.
* `HomologicalComplex.exactAt_iff'`
  (`Algebra/Homology/ShortComplex/HomologicalComplex.lean`).
* `ModuleCat.mono_iff_injective` / `epi_iff_surjective`
  (`Algebra/Category/ModuleCat/EpiMono.lean,50`); `isIso_of_mono_of_epi`
  (`CategoryTheory/Balanced.lean`, abelian → balanced).

The gap (proved here in minimal homology-level form): over `ModuleCat`,
an augmentation `f₀` that is epi with `ker = boundaries` induces an iso
on `H₀` (mono + epi of `leftHomologyMap'`, §4), and `contractExactAt`
gives `ExactAt` at positive degrees (§2).

## Contents

* (§1) `koszulAugToSingle`: the augmentation chain map (general `φ`, `X`).
* (§2) `koszul_exactAt_succ_of_contractExact`: `contractExactAt` → `ExactAt`.
* (§3) `koszul_quasiIsoAt_succ_of_contractExact`: positive-degree quasi-iso.
* (§4) `koszul_quasiIsoAt_zero_of_augExact`: degree-0 quasi-iso from
  `Epi f₀` + `ker = boundaries` (the minimal homology-level iso).
* (§5) `koszul_quasiIso_of_augmentedExact`: the general master.
* (§6) Residue instantiation over `R_P`: `koszulResidueField`,
  `koszulResidueAug`, `koszulResidue_comp_contract_eq_zero`,
  `koszulResidue_epi`, `koszulResidue_augExactZero` (all from `hgen` alone),
  `koszulResiduePi`, and the master `koszulResiduePi_quasiIso` on `[hker]`
  via `grlift_r2_exact_reduced`, plus `koszulResidueProjectiveResolution`
  (the exact `ExtComparison` shape C1+C2 consume).

## References

Project (read-only): `Regularity/Koszul/KoszulComplex.lean` (`koszulChainComplex`,
`koszulCMor_succ`, `koszulContract_ι`, `mem_piece_one_iff`),
`Regularity/Koszul/AugmentedConeStep.lean` (`contractExactAt`:61),
`Regularity/Multiplicity/ReducedMasters.lean` (`grlift_r2_exact_reduced`:80),
`Regularity/Koszul/ExtComparison.lean` (`koszulProjectiveResolutionOfSequence`).

Mathlib (`lean-toolchain` pins `v4.34.0`): as listed in the survey above,
plus `LinearAlgebra/ExteriorPower/Basic.lean` (`zeroEquiv`:434,
`zeroEquiv_ιMulti`:442, `ιMulti_apply_coe`:60),
`LinearAlgebra/ExteriorAlgebra/Basic.lean` (`ιMulti_zero_apply`:304),
`RingTheory/Ideal/Quotient/Defs.lean` (`eq_zero_iff_mem`:111),
`LinearAlgebra/Finsupp/LinearCombination.lean`
(`Submodule.mem_span_range_iff_exists_fun`:379),
`LinearAlgebra/StdBasis.lean` (`basisFun_apply`:126),
`LinearAlgebra/Basis/Defs.lean` (`Basis.sum_repr`:259, `constr_basis`:538).

## Status

* §§1–5 (general bridge): unconditional on the stated hyps.
* §6 augmentation package (`w`, epi, augmented exactness at 0):
  unconditional on `[hgen]` (sop data).
* `koszulResiduePi_quasiIso`: conditional-exact on `[hker]` (via R2Reduced).

## Residual register

* `hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥` closes via the
  `hwit`-chain (`ker_assemble_ker_eq_bot`, parallel lane).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace QuasiIsomorphismBridge

open CategoryTheory HomologicalComplex KoszulComplex AugmentedConeStep ReducedMasters
  GradedSurjection ExtComparison

universe u

/-! ## §1. The augmentation chain map (general) -/

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The augmentation chain map from the Koszul chain complex to the single
complex, from a degree-0 morphism killing the first differential
(`ChainComplex.toSingle₀Equiv`).
-/
noncomputable abbrev koszulAugToSingle (φ : M →ₗ[R] R) (X : ModuleCat.{u} R)
    (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0) :
    koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨f₀, w⟩

/-- The augmentation map acts as `f₀` in degree 0. -/
@[simp]
theorem koszulAugToSingle_f_zero (φ : M →ₗ[R] R) (X : ModuleCat.{u} R)
    (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0) :
    (koszulAugToSingle φ X f₀ w).f 0 = f₀ :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The `τ₂` component of the degree-0 short-complex map is `f₀`. -/
theorem koszulAugToSingle_τ₂ (φ : M →ₗ[R] R) (X : ModuleCat.{u} R)
    (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0) :
    ((shortComplexFunctor' _ _ 1 0 0).map
      (koszulAugToSingle φ X f₀ w)).τ₂ = f₀ := by
  change (koszulAugToSingle φ X f₀ w).f 0 = f₀
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The first differential of the Koszul chain complex is the contraction. -/
theorem koszul_d_one_zero (φ : M →ₗ[R] R) :
    (koszulChainComplex φ).d 1 0 = ModuleCat.ofHom (koszulContract φ 0) := by
  rw [koszulChainComplex_d]
  exact koszulCMor_succ φ 0

/-- The zeroth differential of the Koszul chain complex vanishes. -/
theorem koszul_d_zero_zero (φ : M →ₗ[R] R) :
    (koszulChainComplex φ).d 0 0 = 0 := by
  rw [koszulChainComplex_d]
  exact dite_eq_right (show ¬ (0 + 1 = 0) by decide)

/-! ## §2. Positive-degree exactness from `contractExactAt` -/

/-- R2 exactness gives categorical exactness at every positive degree:
element-level exactness (`moduleCat_exact_iff`) on the `sc'` short complex,
whose maps are the contractions (`koszulCMor_succ`).
-/
theorem koszul_exactAt_succ_of_contractExact (φ : M →ₗ[R] R)
    (hexact : ∀ j, contractExactAt φ j) (n : ℕ) :
    (koszulChainComplex φ).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have hg : ((koszulChainComplex φ).sc' (n + 1 + 1) (n + 1) n).g =
      ModuleCat.ofHom (koszulContract φ n) := by
    change (koszulChainComplex φ).d (n + 1) n = _
    rw [koszulChainComplex_d]
    exact koszulCMor_succ φ n
  have hf : ((koszulChainComplex φ).sc' (n + 1 + 1) (n + 1) n).f =
      ModuleCat.ofHom (koszulContract φ (n + 1)) := by
    change (koszulChainComplex φ).d (n + 1 + 1) (n + 1) = _
    rw [koszulChainComplex_d]
    exact koszulCMor_succ φ (n + 1)
  intro x₂ hx₂
  rw [hg] at hx₂
  rw [hf]
  obtain ⟨ww, hw⟩ := hexact n x₂ hx₂
  exact ⟨ww, hw⟩

/-! ## §3. Positive-degree quasi-isomorphism -/

/-- At positive degrees both sides are exact, so the augmentation is a
quasi-isomorphism there (`quasiIsoAt_iff_exactAt` +
`ChainComplex.exactAt_succ_single_obj`).
-/
theorem koszul_quasiIsoAt_succ_of_contractExact (φ : M →ₗ[R] R)
    (X : ModuleCat.{u} R) (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0)
    (hexact : ∀ j, contractExactAt φ j) (n : ℕ) :
    QuasiIsoAt (koszulAugToSingle φ X f₀ w) (n + 1) := by
  have hK := koszul_exactAt_succ_of_contractExact φ hexact n
  rw [quasiIsoAt_iff_exactAt _ _ hK]
  exact ChainComplex.exactAt_succ_single_obj _ _

/-! ## §4. Degree-0 quasi-isomorphism (the minimal homology-level iso) -/

/-- Degree-0 quasi-isomorphism from an epi augmentation with
`ker = boundaries`: via `sc' 1 0 0` and the explicit left-homology data,
`leftHomologyMap'` is mono (augmented cycles are boundaries) and epi
(`f₀` is epi), hence an iso.
-/
theorem koszul_quasiIsoAt_zero_of_augExact (φ : M →ₗ[R] R)
    (X : ModuleCat.{u} R) (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0)
    (hepi : Epi f₀)
    (hker : ∀ b : (koszulChainComplex φ).X 0, f₀ b = 0 →
      ∃ c : (koszulChainComplex φ).X 1, (koszulChainComplex φ).d 1 0 c = b) :
    QuasiIsoAt (koszulAugToSingle φ X f₀ w) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_isIso_leftHomologyMap' _
    (((koszulChainComplex φ).sc' 1 0 0).moduleCatLeftHomologyData)
    ((((ChainComplex.single₀ _).obj X).sc' 1 0 0).moduleCatLeftHomologyData)]
  set S₁ := (koszulChainComplex φ).sc' 1 0 0 with hS₁
  set S₂ := ((ChainComplex.single₀ _).obj X).sc' 1 0 0 with hS₂
  set φmap := (shortComplexFunctor' _ _ 1 0 0).map
    (koszulAugToSingle φ X f₀ w) with hφmap
  set h₁ : S₁.LeftHomologyData := S₁.moduleCatLeftHomologyData with hh₁
  set h₂ : S₂.LeftHomologyData := S₂.moduleCatLeftHomologyData with hh₂
  set φH := ShortComplex.leftHomologyMap' φmap h₁ h₂ with hφH
  set φK := ShortComplex.cyclesMap' φmap h₁ h₂ with hφK
  have hτ₂ : φmap.τ₂ = f₀ := koszulAugToSingle_τ₂ φ X f₀ w
  have hnat : ∀ k : h₁.K, φH (h₁.π k) = h₂.π (φK k) := by
    intro k
    have h := ShortComplex.leftHomologyπ_naturality' φmap h₁ h₂
    have happ := congrArg (fun g : h₁.K ⟶ h₂.H => g k) h
    exact happ
  have hval : ∀ k : h₁.K, (φK k).val = f₀ k.val := by
    intro k
    have h := ShortComplex.cyclesMap'_i φmap h₁ h₂
    have happ := congrArg (fun g : h₁.K ⟶ S₂.X₂ => g k) h
    rw [hτ₂] at happ
    exact happ
  have hfc : ∀ c : S₁.X₁, (h₁.f' c).val = S₁.f c := fun c => rfl
  have hK00 : S₁.g = 0 := by
    change (koszulChainComplex φ).d 0 0 = 0
    exact koszul_d_zero_zero φ
  have hSf : S₂.f = 0 := rfl
  have hf2zero : h₂.f'.hom = 0 := by
    have hmod : h₂.f'.hom = S₂.moduleCatToCycles :=
      ShortComplex.moduleCatLeftHomologyData_f'_hom S₂
    have hhom : S₂.f.hom = 0 := by rw [hSf]; rfl
    rw [hmod]
    change S₂.f.hom.codRestrict _ _ = 0
    rw [hhom]
    rfl
  have hfrange : LinearMap.range h₂.f'.hom = ⊥ := by
    rw [hf2zero, LinearMap.range_zero]
  rw [isIso_iff_mono_and_epi]
  constructor
  · -- Mono: augmented cycles are boundaries.
    rw [ModuleCat.mono_iff_injective]
    intro q₁ q₂ hq
    obtain ⟨k₁, hk₁⟩ := Submodule.mkQ_surjective _ q₁
    obtain ⟨k₂, hk₂⟩ := Submodule.mkQ_surjective _ q₂
    have e1 : h₁.π k₁ = q₁ := hk₁
    have e2 : h₁.π k₂ = q₂ := hk₂
    have hq' : h₂.π (φK k₁) = h₂.π (φK k₂) := by
      have a1 := hnat k₁
      have a2 := hnat k₂
      rw [e1] at a1
      rw [e2] at a2
      rw [hq] at a1
      exact a1.symm.trans a2
    have hmem : φK k₁ - φK k₂ ∈ LinearMap.range h₂.f'.hom :=
      (Submodule.Quotient.eq _).mp hq'
    rw [hfrange] at hmem
    have hKK : φK k₁ = φK k₂ := sub_eq_zero.mp ((Submodule.mem_bot R).mp hmem)
    have hdiff0 : f₀ (k₁.val - k₂.val) = 0 := by
      have hsub : f₀.hom (k₁.val - k₂.val) = f₀.hom k₁.val - f₀.hom k₂.val :=
        map_sub _ _ _
      have v1 : f₀.hom k₁.val = (φK k₁).val := hval k₁
      have v2 : f₀.hom k₂.val = (φK k₂).val := hval k₂
      have heq : f₀.hom k₁.val = f₀.hom k₂.val :=
        v1.trans ((congrArg Subtype.val hKK).trans v2.symm)
      have h0 : f₀.hom k₁.val - f₀.hom k₂.val = 0 := sub_eq_zero.mpr heq
      exact hsub.trans h0
    obtain ⟨c, hc⟩ := hker _ hdiff0
    have hrange : k₁ - k₂ ∈ LinearMap.range h₁.f'.hom := by
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change (h₁.f' c).val = (k₁ - k₂).val
      rw [hfc c]
      show S₁.f c = (k₁ - k₂).val
      have hfd : S₁.f c = (koszulChainComplex φ).d 1 0 c := rfl
      rw [hfd, hc]
      rfl
    have hq12 : h₁.π k₁ = h₁.π k₂ :=
      (Submodule.Quotient.eq _).mpr hrange
    rw [e1, e2] at hq12
    exact hq12
  · -- Epi: `f₀` is epi.
    rw [ModuleCat.epi_iff_surjective]
    intro r
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ r
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective f₀).mp hepi y.val
    have hg1x : x ∈ LinearMap.ker S₁.g.hom := by
      change S₁.g.hom x = 0
      rw [hK00]
      rfl
    refine ⟨h₁.π ⟨x, hg1x⟩, ?_⟩
    have h1 : φH (h₁.π ⟨x, hg1x⟩) = h₂.π (φK ⟨x, hg1x⟩) := hnat _
    have h2 : φK ⟨x, hg1x⟩ = y :=
      Subtype.ext ((hval _).trans hx)
    rw [h1, h2]
    exact hy

/-! ## §5. The general master -/

/-- General master: R2 exactness plus an epi augmentation with
`ker = boundaries` gives the augmentation quasi-isomorphism.
-/
theorem koszul_quasiIso_of_augmentedExact (φ : M →ₗ[R] R)
    (X : ModuleCat.{u} R) (f₀ : (koszulChainComplex φ).X 0 ⟶ X)
    (w : (koszulChainComplex φ).d 1 0 ≫ f₀ = 0)
    (hexact : ∀ j, contractExactAt φ j)
    (hepi : Epi f₀)
    (hker : ∀ b : (koszulChainComplex φ).X 0, f₀ b = 0 →
      ∃ c : (koszulChainComplex φ).X 1, (koszulChainComplex φ).d 1 0 c = b) :
    QuasiIso (koszulAugToSingle φ X f₀ w) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact koszul_quasiIsoAt_zero_of_augExact φ X f₀ w hepi hker
  | succ n => exact koszul_quasiIsoAt_succ_of_contractExact φ X f₀ w hexact n

/-! ## §6. Residue instantiation over `R_P` -/

variable {K : Type u} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- The residue field of `R_P` as a module object. -/
noncomputable def koszulResidueField : ModuleCat.{u} (Localization.AtPrime P) :=
  ModuleCat.of _ ((Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P))

/-- The residue augmentation `mk ∘ zeroEquiv`. -/
noncomputable def koszulResidueAug (d : ℕ) :
    ↥(⋀[Localization.AtPrime P]^0 (Fin d → Localization.AtPrime P)) →ₗ[Localization.AtPrime P]
      ((Localization.AtPrime P) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
  (Submodule.mkQ _).comp (exteriorPower.zeroEquiv _ _).toLinearMap

/-- Membership form of the augmentation vanishing. -/
theorem koszulResidueAug_eq_zero_iff (d : ℕ)
    (b : ↥(⋀[Localization.AtPrime P]^0 (Fin d → Localization.AtPrime P))) :
    koszulResidueAug P d b = 0 ↔
      exteriorPower.zeroEquiv _ _ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  change (Submodule.mkQ _) _ = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

/-- `zeroEquiv` on a contracted generator recovers `φ`: contraction of
`ι mm` is `algebraMap (φ mm)` (`koszulContract_ι`), and `zeroEquiv` of
`algebraMap r` is `r` (both sides agree on `r • ιMulti 0`). -/
theorem koszulResidue_zeroEquiv_contract (d : ℕ)
    (g : Fin d → Localization.AtPrime P) (mm : Fin d → Localization.AtPrime P)
    (h : ExteriorAlgebra.ι (Localization.AtPrime P) mm ∈
      ⋀[Localization.AtPrime P]^1 (Fin d → Localization.AtPrime P)) :
    exteriorPower.zeroEquiv _ _
        (koszulContract (koszulContractOfSequence g) 0
          ⟨ExteriorAlgebra.ι _ mm, h⟩)
      = (koszulContractOfSequence g) mm := by
  have hval := koszulContract_ι (koszulContractOfSequence g) mm h
  have halg : ∀ (b : ↥(⋀[Localization.AtPrime P]^0 (Fin d → Localization.AtPrime P)))
      (r : Localization.AtPrime P),
      (b : ExteriorAlgebra (Localization.AtPrime P) (Fin d → Localization.AtPrime P)) =
        algebraMap _ _ r →
      exteriorPower.zeroEquiv _ _ b = r := by
    intro b r hb
    have heq : b = r • exteriorPower.ιMulti _ 0
        (fun _ => (0 : Fin d → Localization.AtPrime P)) := by
      apply Subtype.ext
      change (b : ExteriorAlgebra (Localization.AtPrime P)
        (Fin d → Localization.AtPrime P)) = r • _
      rw [hb, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
        Algebra.smul_def, mul_one]
    rw [heq, map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  exact halg _ _ hval

/-- The contraction functional lies in the span of the sequence. -/
theorem koszulResidue_contract_mem_span (d : ℕ)
    (g : Fin d → Localization.AtPrime P) (mm : Fin d → Localization.AtPrime P) :
    (koszulContractOfSequence g) mm ∈ Ideal.span (Set.range g) := by
  have hrep : (koszulContractOfSequence g) mm = ∑ i, mm i • g i := by
    have hmm : mm = ∑ i, (Pi.basisFun (Localization.AtPrime P) (Fin d)).repr mm i •
        (Pi.basisFun (Localization.AtPrime P) (Fin d)) i :=
      ((Pi.basisFun (Localization.AtPrime P) (Fin d)).sum_repr mm).symm
    conv_lhs => rw [hmm]
    rw [map_sum]
    simp only [koszulContractOfSequence, map_smul, Module.Basis.constr_basis,
      Pi.basisFun_repr]
  rw [hrep]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The augmentation kills the first differential (needs `hgen` to identify
the maximal ideal with the span).
-/
theorem koszulResidue_comp_contract_eq_zero (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (koszulChainComplex (koszulContractOfSequence g)).d 1 0 ≫
      ModuleCat.ofHom (koszulResidueAug P d) = 0 := by
  rw [koszul_d_one_zero]
  have hcomp : (koszulResidueAug P d).comp
      (koszulContract (koszulContractOfSequence g) 0) = 0 := by
    apply LinearMap.ext
    intro a
    change koszulResidueAug P d (koszulContract _ 0 a) = 0
    obtain ⟨mm, hmm⟩ := mem_piece_one_iff.mp a.2
    have ha : a = ⟨ExteriorAlgebra.ι _ mm, by rw [hmm]; exact a.2⟩ :=
      Subtype.ext hmm.symm
    rw [ha, koszulResidueAug_eq_zero_iff, koszulResidue_zeroEquiv_contract]
    rw [← hgen]
    exact koszulResidue_contract_mem_span P d g mm
  have hzero : ModuleCat.ofHom ((koszulResidueAug P d).comp
      (koszulContract (koszulContractOfSequence g) 0)) = 0 := by
    rw [hcomp, ModuleCat.ofHom_zero]
  exact hzero

/-- The residue augmentation is epi (`mkQ` is surjective, `zeroEquiv` is a
bijection).
-/
theorem koszulResidue_epi (d : ℕ) :
    Epi (ModuleCat.ofHom (koszulResidueAug P d)) := by
  rw [ModuleCat.epi_iff_surjective]
  intro y
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective _ y
  refine ⟨(exteriorPower.zeroEquiv _ _).symm r, ?_⟩
  change koszulResidueAug P d _ = y
  simp only [koszulResidueAug, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearEquiv.apply_symm_apply]
  exact hr

/-- The degree-0 computation on a standard basis vector. -/
theorem koszulResidue_zeroEquiv_contract_single (d : ℕ)
    (g : Fin d → Localization.AtPrime P) (i : Fin d) :
    exteriorPower.zeroEquiv _ _ (koszulContract (koszulContractOfSequence g) 0
      ⟨ExteriorAlgebra.ι _ (Pi.single i 1),
        mem_piece_one_iff.mpr ⟨_, rfl⟩⟩) = g i := by
  have h1 := koszulResidue_zeroEquiv_contract P d g (Pi.single i 1)
    (mem_piece_one_iff.mpr ⟨_, rfl⟩)
  have h2 : (koszulContractOfSequence g) (Pi.single i 1) = g i := by
    rw [← Pi.basisFun_apply]
    exact Module.Basis.constr_basis _ _ _ _
  exact h1.trans h2

/-- Augmented exactness at 0: every augmented cycle is a boundary. From
`hgen`, `zeroEquiv b ∈ span g` gives coefficients, and the boundary is
built from the standard basis vectors.
-/
theorem koszulResidue_augExactZero (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (b : ↥(⋀[Localization.AtPrime P]^0 (Fin d → Localization.AtPrime P)))
    (hb : koszulResidueAug P d b = 0) :
    ∃ c : ↥(⋀[Localization.AtPrime P]^1 (Fin d → Localization.AtPrime P)),
      koszulContract (koszulContractOfSequence g) 0 c = b := by
  have hmem : exteriorPower.zeroEquiv _ _ b ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    (koszulResidueAug_eq_zero_iff P d b).mp hb
  rw [← hgen] at hmem
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun
    (Localization.AtPrime P)).mp hmem
  refine ⟨∑ i, cc i • (⟨ExteriorAlgebra.ι _ (Pi.single i 1),
    mem_piece_one_iff.mpr ⟨_, rfl⟩⟩ :
      ↥(⋀[Localization.AtPrime P]^1 (Fin d → Localization.AtPrime P))), ?_⟩
  apply (exteriorPower.zeroEquiv _ _).injective
  simp only [map_sum, map_smul]
  simp_rw [koszulResidue_zeroEquiv_contract_single]
  exact hcc

/-- The residue augmentation chain map (needs `hgen` for `w`). -/
noncomputable def koszulResiduePi (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    koszulChainComplex (koszulContractOfSequence g) ⟶
      (ChainComplex.single₀ _).obj (koszulResidueField P) :=
  koszulAugToSingle _ _ (ModuleCat.ofHom (koszulResidueAug P d))
    (koszulResidue_comp_contract_eq_zero P d g hgen)

/-- Master: the residue augmentation is a quasi-isomorphism, from R2
exactness (`grlift_r2_exact_reduced`) plus the §6 augmentation package.

Conditional on exactly `[hker]`. -/
theorem koszulResiduePi_quasiIso (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    QuasiIso (koszulResiduePi P d g hgen) := by
  have hexact := grlift_r2_exact_reduced P d g hgen hker
  have hepi := koszulResidue_epi P d
  have hker4 : ∀ b : (koszulChainComplex (koszulContractOfSequence g)).X 0,
      ModuleCat.ofHom (koszulResidueAug P d) b = 0 →
      ∃ c : (koszulChainComplex (koszulContractOfSequence g)).X 1,
        (koszulChainComplex (koszulContractOfSequence g)).d 1 0 c = b := by
    intro b hb
    obtain ⟨c, hc⟩ := koszulResidue_augExactZero P d g hgen b hb
    refine ⟨c, ?_⟩
    change (koszulChainComplex _).d 1 0 c = b
    have hd10 : (koszulChainComplex (koszulContractOfSequence g)).d 1 0 =
        ModuleCat.ofHom (koszulContract (koszulContractOfSequence g) 0) :=
      koszul_d_one_zero _
    rw [hd10]
    exact hc
  exact koszul_quasiIso_of_augmentedExact _ _ _ _ hexact hepi hker4

/-- The Koszul projective resolution of the residue field, in the exact
`ExtComparison` shape C1+C2 consume.

Conditional on exactly `[hker]`. -/
noncomputable def koszulResidueProjectiveResolution (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    {I : Type u} [LinearOrder I]
    (b : Module.Basis I (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P)) :
    ProjectiveResolution (koszulResidueField P) :=
  koszulProjectiveResolutionOfSequence b g _ (koszulResiduePi P d g hgen)
    (koszulResiduePi_quasiIso P d g hgen hker)

#print axioms koszul_exactAt_succ_of_contractExact
#print axioms koszul_quasiIsoAt_succ_of_contractExact
#print axioms koszul_quasiIsoAt_zero_of_augExact
#print axioms koszul_quasiIso_of_augmentedExact
#print axioms koszulResidue_augExactZero
#print axioms koszulResiduePi_quasiIso

end QuasiIsomorphismBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
