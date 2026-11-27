/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Adapted from
`Theorems/Thm_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.lean`,
`P2M/Sol/S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.lean`,
`Theorems/Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_
pow_smul_of_finiteType.lean`
and
`P2M/Sol/S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_
pow_smul_of_finiteType.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.ScaleRoots

@[expose] public section

open Polynomial

universe u v



section Denominators

variable {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [Algebra R C]
  {L : Type*} [Field L] [Algebra C L] [Algebra R L] [IsScalarTower R C L]
  [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]

private lemma exists_mul_eq_of_mem_adjoin (S : Set C) {w : L}
    (hw : w ∈ Algebra.adjoin (FractionRing R) ((algebraMap C L) '' S)) :
    ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R S, algebraMap R L r * w = algebraMap C L c := by
  obtain ⟨⟨r, hr⟩, hrw⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin (nonZeroDivisors R) (FractionRing R) _ w hw
  rw [← IsScalarTower.coe_toAlgHom' R C L, Algebra.adjoin_image] at hrw
  obtain ⟨c, hc, hcw⟩ := Subalgebra.mem_map.mp hrw
  exact ⟨r, nonZeroDivisors.ne_zero hr, c, hc, by rw [← Algebra.smul_def]; exact hcw.symm⟩

end Denominators

section Scaling

variable {K : Type*} [Field K] {d : ℕ}

private noncomputable def scaleAux (u : Fin d → K) :
    MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (u i) * MvPolynomial.X i

private lemma scaleAux_comp_scaleAux_inv (u : Fin d → K) (hu : ∀ i, u i ≠ 0) :
    (scaleAux u).comp (scaleAux fun i => (u i)⁻¹) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [scaleAux, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X, map_mul,
    MvPolynomial.aeval_C, AlgHom.coe_id, id_eq, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hu i), map_one, one_mul]

private lemma scaleAux_injective (u : Fin d → K) (hu : ∀ i, u i ≠ 0) :
    Function.Injective (scaleAux u) := by
  have hu' : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  have h := scaleAux_comp_scaleAux_inv (fun i => (u i)⁻¹) hu'
  simp only [inv_inv] at h
  intro a b hab
  have := congrArg (scaleAux fun i => (u i)⁻¹) hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, h] at this
  simpa using this

end Scaling

section Main

variable {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C]

private theorem genericPointMain :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
      ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by
  classical
  let K := FractionRing R
  let L := FractionRing C
  let : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have hCL : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  let CK : Subalgebra K L := Algebra.adjoin K ((algebraMap C L) '' (s : Set C))
  have : Algebra.FiniteType K CK := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨(s.image (algebraMap C L)), by simp [CK]⟩
  have hmemCK : ∀ c : C, algebraMap C L c ∈ CK := by
    intro c
    have hc : c ∈ Algebra.adjoin R (s : Set C) := by rw [hs]; exact Algebra.mem_top
    have : (Algebra.adjoin R (s : Set C)).map (IsScalarTower.toAlgHom R C L) ≤
        CK.restrictScalars R := by
      rw [AlgHom.map_adjoin]
      exact Algebra.adjoin_le (fun x hx => Algebra.subset_adjoin hx)
    exact this ⟨c, hc, rfl⟩
  obtain ⟨d, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg K CK
  have hw : ∀ i : Fin d, ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R (s : Set C),
      algebraMap R L r * (g (MvPolynomial.X i) : L) = algebraMap C L c :=
    fun i => exists_mul_eq_of_mem_adjoin (R := R) _ (g (MvPolynomial.X i)).2
  choose ρ hρ0 z _hzmem hz using hw
  have hg_aeval : ∀ p : MvPolynomial (Fin d) K,
      (g p : L) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) p := by
    intro p
    have : (CK.val.comp g) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this
  have hzaeval : ∀ p : MvPolynomial (Fin d) K,
      MvPolynomial.aeval (fun i => algebraMap C L (z i)) p =
        (g (scaleAux (fun i => algebraMap R K (ρ i)) p) : L) := by
    intro p
    rw [hg_aeval]
    have : (MvPolynomial.aeval (fun i => algebraMap C L (z i)) : MvPolynomial (Fin d) K →ₐ[K] L)
        = (MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L))).comp
          (scaleAux fun i => algebraMap R K (ρ i)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [MvPolynomial.aeval_X, AlgHom.coe_comp, Function.comp_apply, scaleAux, map_mul,
        MvPolynomial.aeval_C]
      rw [← hz i, IsScalarTower.algebraMap_apply R K L]
    exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this
  have hρK : ∀ i, algebraMap R K (ρ i) ≠ 0 := fun i => (map_ne_zero_iff _ hRK).mpr (hρ0 i)
  have hzind : AlgebraicIndependent R z := by
    rw [AlgebraicIndependent]
    intro p q hpq
    have h1 : MvPolynomial.aeval (fun i => algebraMap C L (z i))
          (MvPolynomial.map (algebraMap R K) p)
        = MvPolynomial.aeval (fun i => algebraMap C L (z i))
          (MvPolynomial.map (algebraMap R K) q) := by
      rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap]
      have e : ∀ t : MvPolynomial (Fin d) R, MvPolynomial.aeval (fun i => algebraMap C L (z i)) t =
          algebraMap C L (MvPolynomial.aeval z t) := by
        intro t
        rw [← MvPolynomial.aeval_algebraMap_apply]
        rfl
      rw [e, e]
      exact congrArg _ hpq
    rw [hzaeval, hzaeval] at h1
    have h2 := hginj (Subtype.ext h1)
    have h3 := scaleAux_injective _ hρK h2
    exact MvPolynomial.map_injective _ hRK h3
  set A : Subalgebra R C := Algebra.adjoin R (Set.range z) with hA
  have hrange : ∀ p : MvPolynomial (Fin d) K,
      (g p : L) ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
    intro p
    rw [hg_aeval]
    induction p using MvPolynomial.induction_on with
    | C κ => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ κ
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      refine mul_mem hp ?_
      have : (g (MvPolynomial.X i) : L) =
          algebraMap K L (algebraMap R K (ρ i))⁻¹ * algebraMap C L (z i) := by
        rw [← hz i, IsScalarTower.algebraMap_apply R K L, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ (hρK i), map_one, one_mul]
      rw [this]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin ⟨z i, ⟨i, rfl⟩, rfl⟩)
  have hint : ∀ c : C, ∃ τ : R, τ ≠ 0 ∧ IsIntegral A (τ • c) := by
    intro c
    have hgint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hgfin
    obtain ⟨P, hPm, hP⟩ := hgint ⟨algebraMap C L c, hmemCK c⟩
    let P₂ : L[X] := (P.map g.toRingHom).map (CK.val : CK →+* L)
    have hP₂m : P₂.Monic := (hPm.map _).map _
    have hP₂ : P₂.eval (algebraMap C L c) = 0 := by
      have h2 : (CK.val : CK →+* L) (P.eval₂ g.toRingHom ⟨_, hmemCK c⟩) = 0 := by
        rw [hP, map_zero]
      rw [Polynomial.hom_eval₂] at h2
      simp only [P₂, Polynomial.map_map, Polynomial.eval_map]
      exact h2
    have hcoef : ∀ j : ℕ, ∃ r : R, r ≠ 0 ∧ ∃ a ∈ A, algebraMap R L r * P₂.coeff j =
        algebraMap C L a := by
      intro j
      have hj : P₂.coeff j ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
        simp only [P₂, Polynomial.coeff_map]
        exact hrange _
      exact exists_mul_eq_of_mem_adjoin (R := R) _ hj
    choose r hr0 a haA ha using hcoef
    let τ : R := ∏ j ∈ Finset.range P₂.natDegree, r j
    have hτ0 : τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hr0 j
    refine ⟨τ, hτ0, ?_⟩
    let P₃ : L[X] := P₂.scaleRoots (algebraMap R L τ)
    have hP₃m : P₃.Monic := (Polynomial.monic_scaleRoots_iff _).mpr hP₂m
    have hP₃ : P₃.eval₂ (RingHom.id L) (algebraMap R L τ * algebraMap C L c) = 0 := by
      have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id L) (r := algebraMap C L c)
        (s := algebraMap R L τ) (by rw [Polynomial.eval₂_id]; exact hP₂)
      simpa using h
    have hlift : P₃ ∈ Polynomial.lifts (algebraMap A L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro j
      simp only [P₃, Polynomial.coeff_scaleRoots]
      by_cases hj : j < P₂.natDegree
      · obtain ⟨k, hk⟩ : ∃ k, P₂.natDegree - j = k + 1 := ⟨P₂.natDegree - j - 1, by omega⟩
        have hdvd : r j ∣ τ := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
        obtain ⟨τ', hτ'⟩ := hdvd
        refine ⟨⟨algebraMap R C (τ' * τ ^ k) * a j,
          mul_mem (Subalgebra.algebraMap_mem _ _) (haA j)⟩, ?_⟩
        change algebraMap C L (algebraMap R C (τ' * τ ^ k) * a j) =
          P₂.coeff j * algebraMap R L τ ^ (P₂.natDegree - j)
        rw [hk, map_mul, ← IsScalarTower.algebraMap_apply, ← ha j, pow_succ, hτ', map_mul,
          map_mul, map_pow, map_mul]
        ring
      · by_cases hj' : j = P₂.natDegree
        · subst hj'
          refine ⟨1, ?_⟩
          rw [hP₂m.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
        · refine ⟨0, ?_⟩
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, map_zero]
    obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₃m
    have hτc : IsIntegral A (algebraMap C L (τ • c)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQmap, Polynomial.eval, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
      exact hP₃
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A C L) hCL).mp hτc
  choose τ hτ0 hτint using hint
  let r : R := ∏ c ∈ s, τ c
  have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hτ0 c
  refine ⟨r, hr0, d, z, hzind, ?_⟩
  have hAint : ∀ x : R, IsIntegral A (algebraMap R C x) := fun x =>
    (isIntegral_algebraMap (R := A) (A := C)
      (x := ⟨algebraMap R C x, Subalgebra.algebraMap_mem _ x⟩))
  let T : Subalgebra R C :=
    { carrier := {c | ∃ n : ℕ, IsIntegral A (r ^ n • c)}
      mul_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a * b) = (r ^ n • a) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
        rw [this]
        exact ha.mul hb
      add_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a + b) =
            algebraMap R C (r ^ m) * (r ^ n • a) + algebraMap R C (r ^ n) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
        rw [this]
        exact ((hAint _).mul ha).add ((hAint _).mul hb)
      algebraMap_mem' := by
        intro x
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul]
        exact hAint x }
  have hsT : (s : Set C) ⊆ T := by
    intro c hc
    refine ⟨1, ?_⟩
    obtain ⟨r', hr'⟩ : τ c ∣ r := Finset.dvd_prod_of_mem _ hc
    have : r ^ 1 • c = algebraMap R C r' * (τ c • c) := by
      rw [pow_one, hr', Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [this]
    exact (hAint r').mul (hτint c)
  have hT : Algebra.adjoin R (s : Set C) ≤ T := Algebra.adjoin_le hsT
  intro c
  have hc : c ∈ T := hT (by rw [hs]; exact Algebra.mem_top)
  exact hc

end Main

/-- For a finite type algebra `B` over a commutative ring `A` and a prime
`𝔮` of `B`, some element `s` of `A` outside the contraction of `𝔮` bounds the
transcendence degrees of all specializations: for every prime `𝔔 ⊇ 𝔮` whose
contraction still avoids `s`, the transcendence degree of `B ⧸ 𝔔` over
`A ⧸ 𝔔.under A` is at most that of `B ⧸ 𝔮` over `A ⧸ 𝔮.under A`. -/
public theorem Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) := by
  classical
  set 𝔭 := 𝔮.under A with h𝔭
  have : Algebra.FiniteType (A ⧸ 𝔭) (B ⧸ 𝔮) := inferInstance
  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    genericPointMain (R := A ⧸ 𝔭) (C := B ⧸ 𝔮)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hs : s ∉ 𝔭 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  refine ⟨s, hs, ?_⟩
  intro 𝔔 _ h𝔮𝔔 hs𝔔
  have hd : (d : Cardinal) ≤ Algebra.trdeg (A ⧸ 𝔭) (B ⧸ 𝔮) := by
    simpa using hz.lift_cardinalMk_le_trdeg
  refine le_trans ?_ hd
  set 𝔭' := 𝔔.under A with h𝔭'
  have h𝔭𝔭' : 𝔭 ≤ 𝔭' := Ideal.comap_mono h𝔮𝔔
  let πR : A ⧸ 𝔭 →+* A ⧸ 𝔭' := Ideal.Quotient.factor h𝔭𝔭'
  let πC : B ⧸ 𝔮 →+* B ⧸ 𝔔 := Ideal.Quotient.factor h𝔮𝔔
  have hπ : ∀ x : A ⧸ 𝔭, πC (algebraMap (A ⧸ 𝔭) (B ⧸ 𝔮) x)
      = algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR x) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hr' : πR (Ideal.Quotient.mk 𝔭 s) ≠ 0 := by
    change Ideal.Quotient.mk 𝔭' s ≠ 0
    exact fun h => hs𝔔 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let z' : Fin d → B ⧸ 𝔔 := fun i => πC (z i)
  let D : Subalgebra (A ⧸ 𝔭) (B ⧸ 𝔮) := Algebra.adjoin (A ⧸ 𝔭) (Set.range z)
  let D' : Subalgebra (A ⧸ 𝔭') (B ⧸ 𝔔) := Algebra.adjoin (A ⧸ 𝔭') (Set.range z')
  have hDD' : ∀ x ∈ D, πC x ∈ D' := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩; exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro x; rw [hπ]; exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy; rw [map_add]; exact D'.add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact D'.mul_mem hx hy
  have : Algebra.IsAlgebraic D' (B ⧸ 𝔔) := by
    refine ⟨fun c' => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.factor_surjective h𝔮𝔔 c'
    change IsAlgebraic D' (πC c)
    obtain ⟨n, hn⟩ := hint c
    let φ : D →+* D' := (πC.comp (algebraMap D (B ⧸ 𝔮))).codRestrict D' fun d => hDD' _ d.2
    have h1 : IsIntegral D' (πC ((Ideal.Quotient.mk 𝔭 s) ^ n • c)) :=
      IsIntegral.map_of_comp_eq φ πC (RingHom.ext fun _ => rfl) hn
    simp only [Algebra.smul_def, map_pow, map_mul] at h1
    rw [hπ] at h1
    let ρ : D' := ⟨algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR (Ideal.Quotient.mk 𝔭 s)) ^ n,
      D'.pow_mem (Subalgebra.algebraMap_mem _ _) n⟩
    have hρ : (ρ : B ⧸ 𝔔) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, ← map_zero (algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔)),
        (FaithfulSMul.algebraMap_injective (A ⧸ 𝔭') (B ⧸ 𝔔)).eq_iff]
      exact hr'
    have hρ' : ρ ≠ 0 := fun h => hρ (by rw [h]; rfl)
    have h2 : IsAlgebraic D' (ρ • πC c) := by
      rw [Algebra.smul_def]
      exact h1.isAlgebraic
    exact IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hρ') h2
  have hrange : Cardinal.mk (Set.range z') ≤ (d : Cardinal.{v}) := by
    simpa using Cardinal.mk_range_le_lift (f := z')
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (A ⧸ 𝔭') (Set.range z')).trans hrange
