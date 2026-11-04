/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Logic.Small.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

open CategoryTheory Polynomial TensorProduct

noncomputable section

universe u v

namespace MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted

/-- `hs_AllLE R d`: every object of `ModuleCat.{v} R` has projective dimension `≤ d`. -/
private def hs_AllLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (N : ModuleCat.{v} R), CategoryTheory.HasProjectiveDimensionLE N d

/-- `hs_mapX f`: the `R[X]`-linear extension of `PolynomialModule.map R f`. -/
private def hs_mapX {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') : PolynomialModule R L →ₗ[R[X]] PolynomialModule R L' where
  toFun := PolynomialModule.map R f
  map_add' := map_add _
  map_smul' := fun p q => by
    change PolynomialModule.map R f (p • q) = p • PolynomialModule.map R f q
    rw [PolynomialModule.map_smul, Algebra.algebraMap_self, Polynomial.map_id]

/-- The underlying function of `hs_mapX f` is `PolynomialModule.map R f`. -/
private theorem hs_mapX_apply {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') (q : PolynomialModule R L) :
    hs_mapX f q = PolynomialModule.map R f q := rfl

/-- `hs_mapX f` on singletons. -/
private theorem hs_mapX_single {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') (i : ℕ) (m : L) :
    hs_mapX f (PolynomialModule.single R i m) = PolynomialModule.single R i (f m) := by
  rw [hs_mapX_apply]
  exact PolynomialModule.map_single R _ _ _

/-- Coefficients of `hs_mapX f q`. -/
private theorem hs_coeff_map {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') (q : PolynomialModule R L) (n : ℕ) :
    (hs_mapX f q).coeff n = f (q.coeff n) := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i m =>
      rw [hs_mapX_single]
      simp only [PolynomialModule.coeff_single, Finsupp.single_apply]
      split_ifs with h <;> simp_all

/-- The coefficients of a `coeffLinearEquiv` preimage. -/
private theorem hs_symm_coeff {R : Type u} [CommRing R] {L : Type v}
    [AddCommGroup L] [Module R L] (c : ℕ →₀ L) :
    ((PolynomialModule.coeffLinearEquiv R R).symm c).coeff = c :=
  LinearEquiv.apply_symm_apply (PolynomialModule.coeffLinearEquiv R R) c

/-- `hs_mapX f` is injective when `f` is. -/
private theorem hs_mapX_injective {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') (hf : Function.Injective f) :
    Function.Injective (hs_mapX f) := by
  intro p q h
  apply PolynomialModule.coeff_injective
  ext n
  have h2 := congrArg (fun r => r.coeff n) h
  rw [hs_coeff_map, hs_coeff_map] at h2
  exact hf h2

/-- `hs_mapX g` is surjective when `g` is. -/
private theorem hs_mapX_surjective {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (g : L →ₗ[R] L') (hg : Function.Surjective g) :
    Function.Surjective (hs_mapX g) := by
  intro q
  obtain ⟨c, hc⟩ := Finsupp.mapRange_surjective (⇑g) (map_zero g) hg q.coeff
  refine ⟨(PolynomialModule.coeffLinearEquiv R R).symm c, ?_⟩
  apply PolynomialModule.coeff_injective
  ext n
  rw [hs_coeff_map, hs_symm_coeff]
  have hcn := congrArg (fun r => r n) hc
  simp only [Finsupp.mapRange_apply] at hcn
  exact hcn

/-- `hs_mapX` preserves exactness. -/
private theorem hs_mapX_exact {R : Type u} [CommRing R] {K L L' : Type v}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup L'] [Module R L']
    (f : K →ₗ[R] L) (g : L →ₗ[R] L')
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (hs_mapX f) (hs_mapX g) := by
  rw [LinearMap.exact_iff] at hfg ⊢
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hf
  have hrow : LinearMap.range (Finsupp.mapRange.linearMap (α := ℕ) f)
      = Finsupp.submodule (fun _ => LinearMap.range f) :=
    Finsupp.range_mapRange_linearMap f hker ℕ
  ext q
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hq
    have hmem : q.coeff ∈ LinearMap.range (Finsupp.mapRange.linearMap (α := ℕ) f) := by
      rw [hrow, Finsupp.mem_submodule_iff]
      intro n
      have hqn0 : (hs_mapX g q).coeff n = 0 := by simp [hq]
      rw [hs_coeff_map] at hqn0
      have hmem2 : q.coeff n ∈ LinearMap.ker g := hqn0
      rw [hfg] at hmem2
      exact hmem2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(PolynomialModule.coeffLinearEquiv R R).symm c, ?_⟩
    apply PolynomialModule.coeff_injective
    ext n
    rw [hs_coeff_map, hs_symm_coeff]
    have hcn := congrArg (fun r => r n) hc
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply] at hcn
    exact hcn
  · rintro ⟨p, rfl⟩
    have hzero : (hs_mapX g (hs_mapX f p)).coeff = 0 := by
      ext n
      simp only [hs_coeff_map, Finsupp.zero_apply]
      have hmem : f (p.coeff n) ∈ LinearMap.ker g := by
        rw [hfg]
        exact ⟨_, rfl⟩
      exact LinearMap.mem_ker.mp hmem
    exact PolynomialModule.coeff_eq_zero.mp hzero

/-- Extension of scalars to `R[X]` preserves module projectivity. (module level) -/
private theorem hs_projective_polynomialModule_module {R : Type u} [CommRing R]
    {L : Type v} [AddCommGroup L] [Module R L] [Module.Projective R L] :
    Module.Projective R[X] (PolynomialModule R L) :=
  Module.Projective.of_equiv'
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R L)

/-- Extension of scalars to `R[X]` preserves categorical projectivity. -/
private theorem hs_projective_polynomialModule {R : Type u} [CommRing R] [Small.{v} R[X]]
    {L : Type v} [AddCommGroup L] [Module R L] [Module.Projective R L] :
    Projective (ModuleCat.of R[X] (PolynomialModule R L)) :=
  (IsProjective.iff_projective _).mp hs_projective_polynomialModule_module

/-- Base change of projective dimension along `R → R[X]`. -/
private theorem hs_baseChange_pd {R : Type u} [CommRing R] [Small.{v} R] [Small.{v} R[X]]
    (d : ℕ) (L : Type v) [AddCommGroup L] [Module R L]
    [HasProjectiveDimensionLE (ModuleCat.of R L) d] :
    HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R L)) d := by
  induction d generalizing L with
  | zero =>
      have h0 : Projective (ModuleCat.of R L) :=
        (projective_iff_hasProjectiveDimensionLE_zero _).mpr ‹_›
      have hmod : Module.Projective R L := (IsProjective.iff_projective L).mpr h0
      have hmodI := hmod
      exact (projective_iff_hasProjectiveDimensionLE_zero _).mp hs_projective_polynomialModule
  | succ d ih =>
      rcases ModuleCat.enoughProjectives.1 (ModuleCat.of R L) with ⟨⟨P, f⟩⟩
      have hsurj : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective _).mp ‹_›
      have T_exact : (LinearMap.shortComplexKer f.hom).ShortExact :=
        LinearMap.shortExact_shortComplexKer hsurj
      have hK : HasProjectiveDimensionLT (LinearMap.shortComplexKer f.hom).X₁ (d + 1) :=
        (T_exact.hasProjectiveDimensionLT_X₃_iff d ‹_›).mp ‹_›
      have hKI := hK
      have ihK := ih (LinearMap.ker f.hom)
      have hcomp : (hs_mapX f.hom).comp (hs_mapX (LinearMap.ker f.hom).subtype) = 0 := by
        refine LinearMap.ext fun q => PolynomialModule.coeff_eq_zero.mp ?_
        ext n
        simp only [LinearMap.comp_apply, hs_coeff_map, Finsupp.zero_apply]
        exact (q.coeff n).property
      let T' := ShortComplex.mk (ModuleCat.ofHom (hs_mapX (LinearMap.ker f.hom).subtype))
        (ModuleCat.ofHom (hs_mapX f.hom)) (by
          rw [← ModuleCat.ofHom_comp, hcomp, ModuleCat.ofHom_zero])
      have hPmod : Module.Projective R (P : Type v) :=
        (IsProjective.iff_projective (P : Type v)).mpr ‹_›
      have hPmodI := hPmod
      have hPX₂ : Projective T'.X₂ := hs_projective_polynomialModule
      have T'_exact : T'.ShortExact :=
        ModuleCat.shortComplex_shortExact T'
          (hs_mapX_exact _ _ (Submodule.injective_subtype _)
            (LinearMap.exact_subtype_ker_map _))
          (hs_mapX_injective _ (Submodule.injective_subtype _))
          (hs_mapX_surjective _ hsurj)
      exact (T'_exact.hasProjectiveDimensionLT_X₃_iff d hPX₂).mpr ihK

/-- Coefficients of `X • q` at a successor index. -/
private theorem hs_coeff_X_smul_succ {R : Type u} [CommRing R] {N : Type v}
    [AddCommGroup N] [Module R N] (q : PolynomialModule R N) (n : ℕ) :
    ((Polynomial.X : R[X]) • q).coeff (n + 1) = q.coeff n := by
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp

/-- Coefficients of `X • q` at index zero. -/
private theorem hs_coeff_X_smul_zero {R : Type u} [CommRing R] {N : Type v}
    [AddCommGroup N] [Module R N] (q : PolynomialModule R N) :
    ((Polynomial.X : R[X]) • q).coeff 0 = 0 := by
  rw [← Polynomial.monomial_one_one_eq_X, PolynomialModule.monomial_smul_apply]
  simp

/-- The tensor equivalence sends `Xⁱ ⊗ₜ m` to `single i m`. -/
private theorem hs_equiv_tmul {R : Type u} [CommRing R] {N : Type v}
    [AddCommGroup N] [Module R N] (i : ℕ) (m : N) :
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R N)
      (((Polynomial.X : R[X]) ^ i) ⊗ₜ[R] m) = PolynomialModule.single R i m := by
  change (LinearMap.liftBaseChange R[X] (PolynomialModule.lsingle R 0))
    (((Polynomial.X : R[X]) ^ i) ⊗ₜ[R] m) = _
  rw [LinearMap.liftBaseChange_tmul]
  have hls : PolynomialModule.lsingle R (M := N) 0 m = PolynomialModule.single R 0 m := by
    apply PolynomialModule.coeff_injective
    ext n
    rw [PolynomialModule.lsingle_apply, PolynomialModule.coeff_single]
    simp [Finsupp.single_apply]
  rw [hls, ← Polynomial.monomial_one_right_eq_X_pow,
    PolynomialModule.monomial_smul_single, add_zero, one_smul]

section hs_char

variable {R : Type u} [CommRing R] {N : Type v}
  [AddCommGroup N] [Module R[X] N] [Module R N] [IsScalarTower R R[X] N]

/-- Multiply by `X` as an `R`-linear endomorphism. -/
private def hs_xAct : N →ₗ[R] N :=
  ((Polynomial.X : R[X]) • (LinearMap.id : N →ₗ[R[X]] N)).restrictScalars R

/-- `hs_xAct m = X • m`. -/
private theorem hs_xAct_apply (m : N) :
    hs_xAct (R := R) m = (Polynomial.X : R[X]) • m := rfl

/-- Evaluation of coefficients: `Σ single i mᵢ ↦ Σ Xⁱ • mᵢ`. -/
private def hs_phi : PolynomialModule R N →ₗ[R[X]] N :=
  (LinearMap.liftBaseChange R[X] (LinearMap.id : N →ₗ[R] N)).comp
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R N).symm.toLinearMap

/-- `p ↦ X • p − (X acting on each coefficient)`. -/
private def hs_psi : PolynomialModule R N →ₗ[R[X]] PolynomialModule R N :=
  (Polynomial.X : R[X]) • (LinearMap.id : PolynomialModule R N →ₗ[R[X]] _) -
    hs_mapX hs_xAct

/-- `hs_phi` on singletons. -/
private theorem hs_phi_single (i : ℕ) (m : N) :
    hs_phi (PolynomialModule.single R i m) = (Polynomial.X : R[X]) ^ i • m := by
  have hsymm : (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R N).symm
      (PolynomialModule.single R i m) = ((Polynomial.X : R[X]) ^ i) ⊗ₜ[R] m :=
    (LinearEquiv.symm_apply_eq _).mpr (hs_equiv_tmul i m).symm
  change (LinearMap.liftBaseChange R[X] (LinearMap.id : N →ₗ[R] N))
    ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule R N).symm
      (PolynomialModule.single R i m)) = _
  rw [hsymm, LinearMap.liftBaseChange_tmul, LinearMap.id_apply]

/-- `hs_psi` on singletons. -/
private theorem hs_psi_single (i : ℕ) (m : N) :
    hs_psi (PolynomialModule.single R i m) = PolynomialModule.single R (i + 1) m
      - PolynomialModule.single R i ((Polynomial.X : R[X]) • m) := by
  have hsub : hs_psi (PolynomialModule.single R i m)
      = ((Polynomial.X : R[X]) •
          (LinearMap.id : PolynomialModule R N →ₗ[R[X]] _))
          (PolynomialModule.single R i m)
        - hs_mapX hs_xAct (PolynomialModule.single R i m) := rfl
  have h1 : ((Polynomial.X : R[X]) •
      (LinearMap.id : PolynomialModule R N →ₗ[R[X]] _)) (PolynomialModule.single R i m)
      = PolynomialModule.single R (i + 1) m := by
    rw [← Polynomial.monomial_one_one_eq_X, LinearMap.smul_apply, LinearMap.id_apply,
      PolynomialModule.monomial_smul_single, add_comm (1 : ℕ) i, one_smul]
  rw [hsub, h1, hs_mapX_single, hs_xAct_apply]

/-- `hs_phi` is surjective. -/
private theorem hs_phi_surjective : Function.Surjective (hs_phi (R := R) (N := N)) := by
  intro m
  refine ⟨PolynomialModule.single R 0 m, ?_⟩
  rw [hs_phi_single, pow_zero, one_smul]

/-- `hs_phi (hs_psi q) = 0` for all `q`. -/
private theorem hs_phi_psi_apply (q : PolynomialModule R N) : hs_phi (hs_psi q) = 0 := by
  induction q using PolynomialModule.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single i m =>
      rw [hs_psi_single, map_sub, hs_phi_single, hs_phi_single, pow_succ, mul_smul,
        sub_self]

/-- `hs_phi ∘ₗ hs_psi = 0`. -/
private theorem hs_phi_comp_psi :
    (hs_phi (R := R) (N := N)).comp (hs_psi (R := R) (N := N)) = 0 := by
  apply LinearMap.ext
  intro q
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact hs_phi_psi_apply q

/-- `hs_psi` is injective. -/
private theorem hs_psi_injective : Function.Injective (hs_psi (R := R) (N := N)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hsplit : ∀ n, (hs_psi (R := R) (N := N) q).coeff (n + 1)
      = q.coeff n - (Polynomial.X : R[X]) • q.coeff (n + 1) := by
    intro n
    have hsub : hs_psi (R := R) (N := N) q
        = (Polynomial.X : R[X]) • q - hs_mapX (hs_xAct (R := R)) q := rfl
    have e1 : (PolynomialModule.coeffLinearEquiv R R) (hs_psi (R := R) (N := N) q)
        = (PolynomialModule.coeffLinearEquiv R R) ((Polynomial.X : R[X]) • q)
          - (PolynomialModule.coeffLinearEquiv R R)
            (hs_mapX (hs_xAct (R := R)) q) := by
      rw [hsub]
      exact map_sub _ _ _
    have e2 : ∀ p : PolynomialModule R N,
        (PolynomialModule.coeffLinearEquiv R R) p = p.coeff := fun p => rfl
    rw [e2, e2, e2] at e1
    have e3 := congrArg (fun c => c (n + 1)) e1
    simp only [Finsupp.sub_apply] at e3
    rw [hs_coeff_X_smul_succ, hs_coeff_map, hs_xAct_apply] at e3
    exact e3
  have hrec : ∀ n, q.coeff n = (Polynomial.X : R[X]) • q.coeff (n + 1) := by
    intro n
    have hqn : (hs_psi (R := R) (N := N) q).coeff (n + 1) = 0 := by simp [hq]
    rw [hsplit] at hqn
    exact sub_eq_zero.mp hqn
  have hpow : ∀ (n j : ℕ),
      q.coeff n = ((Polynomial.X : R[X]) ^ j) • q.coeff (n + j) := by
    intro n j
    induction j with
    | zero => simp
    | succ j ih =>
        have h := hrec (n + j)
        rw [pow_succ, mul_smul, ih, h, Nat.add_assoc]
  have hzero : ∀ n, q.coeff n = 0 := by
    intro n
    have h := hpow n (q.coeff.support.sup id + 1)
    have hmem : q.coeff (n + (q.coeff.support.sup id + 1)) = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hcon
      have hle : n + (q.coeff.support.sup id + 1) ≤ q.coeff.support.sup id := by
        have h2 := Finset.le_sup (f := id) (s := q.coeff.support) hcon
        simpa using h2
      omega
    rw [hmem, smul_zero] at h
    exact h
  rw [← PolynomialModule.coeff_eq_zero]
  exact Finsupp.ext fun n => by simpa using hzero n

/-- Every `p` differs from `single 0 (phi p)` by an element of the range of `psi`. -/
private theorem hs_sub_single_mem_range (p : PolynomialModule R N) :
    p - PolynomialModule.single R 0 (hs_phi (R := R) (N := N) p)
      ∈ LinearMap.range (hs_psi (R := R) (N := N)) := by
  induction p using PolynomialModule.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, PolynomialModule.single_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  | single i m =>
      induction i generalizing m with
      | zero =>
          rw [hs_phi_single, pow_zero, one_smul, sub_self]
          exact Submodule.zero_mem _
      | succ i ih =>
          have hphi : hs_phi (R := R) (N := N) (PolynomialModule.single R (i + 1) m)
              = (Polynomial.X : R[X]) ^ (i + 1) • m := hs_phi_single _ _
          rw [hphi, pow_succ, mul_smul]
          have hdecomp : PolynomialModule.single R (i + 1) m
                - PolynomialModule.single R 0
                  ((Polynomial.X : R[X]) ^ i • (Polynomial.X : R[X]) • m)
              = hs_psi (R := R) (N := N) (PolynomialModule.single R i m)
                + (PolynomialModule.single R i ((Polynomial.X : R[X]) • m)
                  - PolynomialModule.single R 0
                    ((Polynomial.X : R[X]) ^ i • (Polynomial.X : R[X]) • m)) := by
            rw [hs_psi_single]
            abel
          have ih' := ih ((Polynomial.X : R[X]) • m)
          rw [hs_phi_single] at ih'
          rw [hdecomp]
          exact Submodule.add_mem _ (LinearMap.mem_range_self _ _) ih'

/-- Exactness of `hs_psi` followed by `hs_phi`. -/
private theorem hs_exact_psi_phi :
    Function.Exact (hs_psi (R := R) (N := N)) (hs_phi (R := R) (N := N)) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro p hp
    have h := hs_sub_single_mem_range (R := R) (N := N) p
    have hp0 : hs_phi (R := R) (N := N) p = 0 := hp
    rw [hp0, PolynomialModule.single_zero, sub_zero] at h
    exact h
  · rintro p ⟨q, rfl⟩
    exact LinearMap.congr_fun (hs_phi_comp_psi (R := R) (N := N)) q

/-- The characteristic short exact sequence. -/
private theorem hs_char_shortExact :
    (ShortComplex.mk (ModuleCat.ofHom (hs_psi (R := R) (N := N)))
      (ModuleCat.ofHom (hs_phi (R := R) (N := N)))
      (by rw [← ModuleCat.ofHom_comp, hs_phi_comp_psi, ModuleCat.ofHom_zero])).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (hs_exact_psi_phi (R := R) (N := N))
    (hs_psi_injective (R := R) (N := N)) (hs_phi_surjective (R := R) (N := N))

end hs_char

/-- Polynomial extension raises the uniform projective-dimension bound by one. -/
private theorem hs_polynomial_step {R : Type u} [CommRing R] [Small.{v} R] [Small.{v} R[X]]
    (d : ℕ) (h : hs_AllLE.{u, v} (R := R) d) : hs_AllLE.{u, v} (R := R[X]) (d + 1) := by
  intro N
  let : Module R (N : Type v) := Module.compHom _ (algebraMap R R[X])
  have htower : IsScalarTower R R[X] (N : Type v) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have htowerI := htower
  have hL : HasProjectiveDimensionLE (ModuleCat.of R (N : Type v)) d :=
    h (ModuleCat.of R (N : Type v))
  have hLI := hL
  have hNLT : HasProjectiveDimensionLT (ModuleCat.of R[X]
      (PolynomialModule R (N : Type v))) (d + 1) := hs_baseChange_pd d (N : Type v)
  have hNLTI := hNLT
  have h2 : HasProjectiveDimensionLT (ModuleCat.of R[X]
      (PolynomialModule R (N : Type v))) (d + 2) :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of R[X] (PolynomialModule R (N : Type v)))
      (n := d + 1) (m := d + 2) (h := by omega)
  have hS := hs_char_shortExact (R := R) (N := (N : Type v))
  have h3 : HasProjectiveDimensionLT (ModuleCat.of R[X] (N : Type v)) (d + 2) :=
    hS.hasProjectiveDimensionLT_X₃ (d + 1) hNLT h2
  exact h3

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Transport of the uniform bound along a ring isomorphism. -/
private theorem hs_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [Small.{v} A] [Small.{v} B] (e : A ≃+* B) (d : ℕ)
    (h : hs_AllLE.{u, v} (R := B) d) : hs_AllLE.{u, v} (R := A) d := by
  intro N
  let : Module B (N : Type v) := Module.compHom _ (RingEquiv.toRingHom e.symm)
  have hN' : HasProjectiveDimensionLE (ModuleCat.of B (N : Type v)) d :=
    h (ModuleCat.of B (N : Type v))
  have hN'I := hN'
  let e' : (ModuleCat.of B (N : Type v)) ≃ₛₗ[RingHomClass.toRingHom e.symm] N :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e.symm e' d

/-- Uniform bound zero over a field. -/
private theorem hs_field (k : Type u) [Field k] [Small.{v} k] :
    hs_AllLE.{u, v} (R := k) 0 := by
  intro N
  have hproj : Module.Projective k (N : Type v) := Module.Projective.of_free
  have hprojI := hproj
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
    ((IsProjective.iff_projective (N : Type v)).mp hproj)

/-- Uniform bound `n` over `MvPolynomial (Fin n) k`. -/
private theorem hs_mvPolynomial (k : Type u) [Field k] [Small.{v} k] (n : ℕ) :
    hs_AllLE.{u, v} (R := MvPolynomial (Fin n) k) n := by
  induction n with
  | zero =>
      exact hs_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)) 0 (hs_field k)
  | succ n ih =>
      have hsmall : Small.{v} (Polynomial (MvPolynomial (Fin n) k)) :=
        small_map (MvPolynomial.finSuccEquiv k n).symm.toEquiv
      have hsmallI := hsmall
      have hpoly := hs_polynomial_step (R := MvPolynomial (Fin n) k) n ih
      exact hs_ringEquiv (MvPolynomial.finSuccEquiv k n).toRingEquiv (n + 1) hpoly

/-- A nontrivial module forces the field to be small. -/
private theorem hs_small_of_nontrivial {k : Type u} [Field k] {n : ℕ} {M : Type v}
    [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M] [Nontrivial M] :
    Small.{v} k := by
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hinj : Function.Injective
      (fun c : k => (MvPolynomial.C c : MvPolynomial (Fin n) k) • m₀) := by
    intro a b hab
    change (MvPolynomial.C a : MvPolynomial (Fin n) k) • m₀
      = (MvPolynomial.C b : MvPolynomial (Fin n) k) • m₀ at hab
    by_contra hne
    have hdiff : ((MvPolynomial.C a - MvPolynomial.C b :
        MvPolynomial (Fin n) k)) • m₀ = 0 := by
      rw [sub_smul, hab, sub_self]
    have hsub : (MvPolynomial.C (a - b) : MvPolynomial (Fin n) k) • m₀ = 0 := by
      rw [map_sub]
      exact hdiff
    have h2 : m₀ = 0 := by
      have hmul : ((MvPolynomial.C (a - b)⁻¹ * MvPolynomial.C (a - b) :
          MvPolynomial (Fin n) k)) • m₀ = 0 := by
        rw [mul_smul, hsub, smul_zero]
      rwa [← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), map_one, one_smul] at hmul
    exact hm₀ h2
  exact small_of_injective hinj

end MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted

@[expose] public section

/-!
# Hilbert syzygy theorem

Hilbert's syzygy theorem: finitely generated modules over
`MvPolynomial (Fin n) k` have projective dimension at most `n`.
-/

namespace MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted

/--
**Hilbert's syzygy theorem.** Let $k$ be a field, let $n$ be a natural number, and let $M$ be a
finitely generated module over the polynomial ring $k[X_1, \dots, X_n]$ in $n$ variables. Then
$M$ has projective dimension at most $n$ in the category of $k[X_1, \dots, X_n]$-modules.

Proves `Wanted` entry `hilbert_syzygy`.

Source: D. Hilbert, Math. Ann. 36 (1890)
473–534 finite free resolution length ≤n; Lang, Algebra; Lean states field case `k[X₁, …, Xₙ]`
with `HasProjectiveDimensionLE n` and n=0 field case.
-/
theorem hilbert_syzygy
    {k : Type*} [Field k]
    {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M] :
    CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of (MvPolynomial (Fin n) k) M) n := by
  rcases subsingleton_or_nontrivial M with hsing | hnontriv
  · have hzero : Limits.IsZero (ModuleCat.of (MvPolynomial (Fin n) k) M) :=
      ModuleCat.isZero_of_subsingleton _
    have hlt0 : HasProjectiveDimensionLT (ModuleCat.of (MvPolynomial (Fin n) k) M) 0 :=
      hzero.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ (n := 0) (m := n + 1) (h := Nat.zero_le _)
  · have hksmall : Small k := hs_small_of_nontrivial (k := k) (n := n) (M := M)
    have hksmallI := hksmall
    exact hs_mvPolynomial k n (ModuleCat.of _ M)

end MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted
