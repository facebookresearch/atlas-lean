/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.ResiduallyFinite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

section
/-!
# Malcev residual finiteness for linear groups

Records Malcev's residual finiteness theorem for finitely generated linear groups.
-/

namespace MathlibExt.GroupTheory.LinearGroupFinitenessWanted

private theorem span_nat_prime_isMaximal (p : ℕ) (hp : p.Prime) :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal := by
  have hP : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hI : Irreducible ((p : ℤ)) := hP.irreducible
  exact PrincipalIdealRing.isMaximal_of_irreducible hI

private theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hne
  · apply eq_bot_iff.mpr
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have hn1 : x.natAbs + 1 ≠ 1 := by
      intro h
      apply hx0
      have : x.natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp this
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
    have hqdvd' : ¬ ((q : ℤ) ∣ x) := by
      intro hd
      have h1 : ((q : ℤ)) ∣ (((x.natAbs : ℕ)) : ℤ) :=
        dvd_trans hd (Int.dvd_natAbs.mpr (dvd_refl x))
      have h2 : q ∣ x.natAbs := Int.natCast_dvd_natCast.mp h1
      have h3 : q ∣ 1 := (Nat.dvd_add_right h2).mp hqdvd
      have h4 : q = 1 := Nat.dvd_one.mp h3
      exact hqprime.ne_one h4
    have hxspan : x ∉ Ideal.span ({(q : ℤ)} : Set ℤ) := by
      rw [Ideal.mem_span_singleton]
      exact hqdvd'
    have hmax := span_nat_prime_isMaximal q hqprime
    have hx' : x ∈ sInf {J : Ideal ℤ | ⊥ ≤ J ∧ J.IsMaximal} := hx
    have hmem : x ∈ Ideal.span ({(q : ℤ)} : Set ℤ) :=
      Submodule.mem_sInf.mp hx' _ ⟨bot_le, hmax⟩
    exact hxspan hmem
  · obtain rfl | ⟨p, hp, hPeq⟩ := Ideal.isPrime_int_iff.mp hP
    · exact absurd rfl hne
    · rw [hPeq]
      exact @Ideal.jacobson_eq_self_of_isMaximal _ _ _ (span_nat_prime_isMaximal p hp)

private theorem finite_of_finiteType_int {F : Type*} [Field F] [Algebra ℤ F]
    [Algebra.FiniteType ℤ F] : Finite F := by
  have := isJacobsonRing_int
  have hfin := finite_of_finite_type_of_isJacobsonRing ℤ F
  have := hfin
  have hInt : Algebra.IsIntegral ℤ F := Algebra.IsIntegral.of_finite ℤ F
  have hmax : (RingHom.ker (algebraMap ℤ F)).IsMaximal :=
    Algebra.ker_algebraMap_isMaximal_of_isIntegral ℤ F
  have hker : RingHom.ker (algebraMap ℤ F) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hmax Int.not_isField
  have := IsPrincipalIdealRing.principal (RingHom.ker (algebraMap ℤ F))
  have hspan : ℤ ∙ Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F)) =
      RingHom.ker (algebraMap ℤ F) :=
    Submodule.IsPrincipal.span_singleton_generator _
  have hg0 : Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F)) ≠ 0 := by
    intro h0
    apply hker
    rw [← hspan, h0]
    exact (Submodule.span_singleton_eq_bot).mpr rfl
  have hmpos : 0 < (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs :=
    Int.natAbs_pos.mpr hg0
  have : CharP F (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs :=
    ⟨fun x => by
      constructor
      · intro hx
        have h1 : algebraMap ℤ F ((x : ℕ) : ℤ) = 0 := by
          rw [map_natCast]
          exact hx
        have hmem : ((x : ℕ) : ℤ) ∈ RingHom.ker (algebraMap ℤ F) :=
          RingHom.mem_ker.mpr h1
        rw [← hspan] at hmem
        have hmem2 : ((x : ℕ) : ℤ) ∈
            Ideal.span ({Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))} : Set ℤ) :=
          hmem
        rw [Ideal.mem_span_singleton] at hmem2
        have h2 : (((Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs : ℕ) :
            ℤ) ∣
            ((x : ℕ) : ℤ) :=
          dvd_trans Int.natAbs_dvd_self hmem2
        exact Int.natCast_dvd_natCast.mp h2
      · intro hdvd
        have h2 : (((Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs : ℕ) :
            ℤ) ∣
            ((x : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdvd
        have h3 : Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F)) ∣ ((x : ℕ) : ℤ) :=
          dvd_trans (Int.dvd_natAbs.mpr (dvd_refl _)) h2
        have hmem : ((x : ℕ) : ℤ) ∈ RingHom.ker (algebraMap ℤ F) := by
          rw [← hspan]
          change ((x : ℕ) : ℤ) ∈ Ideal.span _
          rw [Ideal.mem_span_singleton]
          exact h3
        have h4 := RingHom.mem_ker.mp hmem
        rwa [map_natCast] at h4⟩
  let := ZMod.algebra F (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs
  have hFT : Algebra.FiniteType ℤ F := inferInstance
  have hFT' : (algebraMap ℤ F).FiniteType := RingHom.finiteType_algebraMap.mpr hFT
  have hcomp : (algebraMap (ZMod (Submodule.IsPrincipal.generator
      (RingHom.ker (algebraMap ℤ F))).natAbs) F).comp
      (algebraMap ℤ (ZMod (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs))
          =
      algebraMap ℤ F :=
    Subsingleton.elim _ _
  have h2 : ((algebraMap (ZMod (Submodule.IsPrincipal.generator
      (RingHom.ker (algebraMap ℤ F))).natAbs) F).comp
      (algebraMap ℤ (ZMod (Submodule.IsPrincipal.generator
          (RingHom.ker (algebraMap ℤ F))).natAbs))).FiniteType := by
    rw [hcomp]
    exact hFT'
  have hFTZ : Algebra.FiniteType (ZMod
      (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs) F :=
    RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType h2)
  have hInt2 : Algebra.IsIntegral
      (ZMod (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs) F := by
    rw [Algebra.isIntegral_def]
    intro x
    obtain ⟨P, hPm, hP0⟩ := (Algebra.isIntegral_def.mp hInt) x
    refine ⟨P.map (Int.castRingHom (ZMod
        (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs)), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : ((algebraMap (ZMod (Submodule.IsPrincipal.generator
        (RingHom.ker (algebraMap ℤ F))).natAbs) F).comp
        (Int.castRingHom (ZMod (Submodule.IsPrincipal.generator
            (RingHom.ker (algebraMap ℤ F))).natAbs))) =
        algebraMap ℤ F :=
      Subsingleton.elim _ _
    rw [hc, ← Polynomial.aeval_def]
    exact hP0
  have hfin2 : Module.Finite (ZMod
      (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs) F :=
    Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨hInt2, hFTZ⟩
  have hNZ : NeZero (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs :=
    ⟨hmpos.ne'⟩
  have : Finite (ZMod (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs) :=
    inferInstance
  have : Module.Finite (ZMod (Submodule.IsPrincipal.generator
      (RingHom.ker (algebraMap ℤ F))).natAbs) F :=
    hfin2
  exact Module.finite_of_finite (ZMod
      (Submodule.IsPrincipal.generator (RingHom.ker (algebraMap ℤ F))).natAbs)

/--
**Malcev's theorem on linear groups.** Let $K$ be a field and $n$ a natural number. Every finitely
generated subgroup of the general linear group $\mathrm{GL}_n(K)$ is residually finite.

Proves `Wanted` entry `malcev_residuallyFinite`.

Source: A.
I. Malcev, Mat. Sb. 8 (1940) 405–422; Wehrfritz, Infinite Linear Groups; Lean states subgroup `G ≤
GL_n(K)` with `Group.FG G`.
-/
theorem malcev_residuallyFinite
    {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hFG : Group.FG G) : Group.ResiduallyFinite G := by
  classical
  obtain ⟨_, S, _, hS⟩ := Group.fg_iff'.mp hFG
  set E : ↥G → Matrix (Fin n) (Fin n) K :=
    fun g => ((g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hE
  set T : Finset K := (S.biUnion fun s => Finset.univ.biUnion fun i =>
    Finset.univ.image fun j => E s i j) ∪ S.image fun s => (E s).det⁻¹ with hT
  set R : Subalgebra ℤ K := Algebra.adjoin ℤ (↑T : Set K) with hR
  have hEmul : ∀ a b : ↥G, E (a * b) = E a * E b := by
    intro a b
    simp only [hE]
    simp
  have hEone : E (1 : ↥G) = 1 := by
    simp only [hE]
    simp
  have hEinv : ∀ a : ↥G, E (a⁻¹) = (E a)⁻¹ := by
    intro a
    simp only [hE]
    simp
  have det_mem : ∀ B : Matrix (Fin n) (Fin n) K, (∀ i j, B i j ∈ R) → B.det ∈ R := by
    intro B hB
    rw [Matrix.det_apply]
    exact AddSubmonoid.sum_mem R.toAddSubmonoid (fun σ _ =>
      Subalgebra.zsmul_mem R ((Submonoid.prod_mem R.toSubmonoid (fun i _ => hB _ _) : _ ∈ R)) _)
  have adj_mem : ∀ (A : Matrix (Fin n) (Fin n) K), (∀ i j, A i j ∈ R) →
      ∀ i j, A.adjugate i j ∈ R := by
    intro A hA i j
    rw [Matrix.adjugate_apply]
    apply det_mem
    intro i' j'
    rw [Matrix.updateRow_apply]
    split_ifs with hij
    · subst hij
      by_cases hjj : j' = i
      · subst hjj
        rw [Pi.single_eq_same]
        exact one_mem R
      · rw [Pi.single_eq_of_ne hjj]
        exact zero_mem R
    · exact hA _ _
  have key : ∀ g : ↥G, (∀ i j, E g i j ∈ R) ∧ ((E g).det⁻¹ ∈ R) := by
    intro g
    have hgmem : g ∈ Subgroup.closure (↑S : Set ↥G) := by
      rw [hS]
      exact Subgroup.mem_top g
    refine Subgroup.closure_induction (p := fun g _ => (∀ i j, E g i j ∈ R) ∧ ((E g).det⁻¹ ∈ R)) ?_
        ?_ ?_ ?_ hgmem
    · intro s hs
      constructor
      · intro i j
        apply Algebra.subset_adjoin
        rw [hT, Finset.mem_coe, Finset.mem_union]
        left
        exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
          Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩⟩
      · apply Algebra.subset_adjoin
        rw [hT, Finset.mem_coe, Finset.mem_union]
        right
        exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · constructor
      · intro i j
        rw [hEone, Matrix.one_apply]
        split_ifs with hij
        · exact one_mem R
        · exact zero_mem R
      · rw [hEone, Matrix.det_one, inv_one]
        exact one_mem R
    · intro x y hx hy ihx ihy
      obtain ⟨hex, hdx⟩ := ihx
      obtain ⟨hey, hdy⟩ := ihy
      constructor
      · intro i j
        rw [hEmul, Matrix.mul_apply]
        exact AddSubmonoid.sum_mem R.toAddSubmonoid
            (fun k _ => (mul_mem (hex _ _) (hey _ _) : _ ∈ R))
      · rw [hEmul, Matrix.det_mul, mul_inv_rev]
        exact mul_mem hdy hdx
    · intro x hx ih
      obtain ⟨hex, hdx⟩ := ih
      constructor
      · intro i j
        rw [hEinv, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
        exact mul_mem hdx (adj_mem _ hex _ _)
      · have h1 : ((E x)⁻¹).det = ((E x).det)⁻¹ := by
          rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
        rw [hEinv, h1, inv_inv]
        exact det_mem _ hex
  have := isJacobsonRing_int
  have hFT : Algebra.FiniteType ℤ ↥(Algebra.adjoin ℤ (↑T : Set K)) :=
      Algebra.FiniteType.adjoin_of_finite (R := ℤ) T.finite_toSet
  have : IsJacobsonRing ↥R := isJacobsonRing_of_finiteType (A := ℤ)
  have hbot : (⊥ : Ideal ↥R).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.mp inferInstance _ inferInstance
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  have hne : E g ≠ 1 := by
    intro hcon
    rw [hE] at hcon
    exact hg (Subtype.ext (Units.ext hcon))
  have hex : ∃ i j, E g i j ≠ (1 : Matrix (Fin n) (Fin n) K) i j := by
    by_contra hcon
    apply hne
    apply Matrix.ext
    intro i j
    by_contra hneij
    exact hcon ⟨i, j, hneij⟩
  obtain ⟨i, j, hij⟩ := hex
  have hr0 : E g i j - (1 : Matrix (Fin n) (Fin n) K) i j ≠ 0 := sub_ne_zero.mpr hij
  have h1R : (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := by
    rw [Matrix.one_apply]
    split_ifs with hij2
    · exact one_mem R
    · exact zero_mem R
  have hrR : E g i j - (1 : Matrix (Fin n) (Fin n) K) i j ∈ R :=
    sub_mem ((key g).1 i j) h1R
  have hrnbot : (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) ∈ (⊥ : Ideal ↥R) →
      False := by
    rw [Submodule.mem_bot]
    intro hcon
    apply hr0
    exact Subtype.ext_iff.mp hcon
  have hrnjac : (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) ∉
      (⊥ : Ideal ↥R).jacobson := by
    rw [hbot]
    exact hrnbot
  obtain ⟨m, ⟨hle, hmax⟩, hrm⟩ : ∃ J : Ideal ↥R, (⊥ ≤ J ∧ J.IsMaximal) ∧
      (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) ∉ J := by
    by_contra hcon
    apply hrnjac
    have hx' : (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) ∈
        sInf {J : Ideal ↥R | ⊥ ≤ J ∧ J.IsMaximal} :=
      Submodule.mem_sInf.mpr (by
        intro J hJ
        by_contra hJmem
        exact hcon ⟨J, hJ, hJmem⟩)
    exact hx'
  have := hmax
  have := Ideal.Quotient.field m
  have hFTQ : Algebra.FiniteType ℤ (↥R ⧸ m) := by
    have h1 : (algebraMap ℤ ↥R).FiniteType := RingHom.finiteType_algebraMap.mpr hFT
    have h2 : (Ideal.Quotient.mk m).FiniteType :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    have hcomp : (Ideal.Quotient.mk m).comp (algebraMap ℤ ↥R) = algebraMap ℤ (↥R ⧸ m) :=
      Subsingleton.elim _ _
    have h3 : ((Ideal.Quotient.mk m).comp (algebraMap ℤ ↥R)).FiniteType :=
      RingHom.FiniteType.comp h2 h1
    rw [hcomp] at h3
    exact RingHom.finiteType_algebraMap.mp h3
  have hFin : Finite (↥R ⧸ m) :=
    @finite_of_finiteType_int _ (Ideal.Quotient.field m)
      (Ideal.Quotient.algebra ℤ) hFTQ
  have := hFin
  have : Finite (Matrix (Fin n) (Fin n) (↥R ⧸ m)) := Pi.finite
  have hunit : ∀ h : ↥G, IsUnit ((Ideal.Quotient.mk m).mapMatrix
      (fun i j => (⟨E h i j, (key h).1 i j⟩ : ↥R))) := by
    intro h
    set M : Matrix (Fin n) (Fin n) ↥R :=
      fun i j => (⟨E h i j, (key h).1 i j⟩ : ↥R) with hM
    change IsUnit ((Ideal.Quotient.mk m).mapMatrix M)
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
    have hdet0 : (E h).det ≠ 0 := ((h : Matrix.GeneralLinearGroup (Fin n) K).det).ne_zero
    have hbridge : ((M.det : ↥R).val = (E h).det) := by
      have hmap : (R.val.toRingHom).mapMatrix M = E h :=
        Matrix.ext fun i j => rfl
      have hmd := RingHom.map_det R.val.toRingHom M
      rw [hmap] at hmd
      exact hmd
    have hU : IsUnit (M.det) := by
      rw [isUnit_iff_exists]
      refine ⟨⟨(E h).det⁻¹, (key h).2⟩, ?_, ?_⟩
      · apply Subtype.ext
        rw [Subalgebra.coe_mul, hbridge]
        exact mul_inv_cancel₀ hdet0
      · apply Subtype.ext
        rw [Subalgebra.coe_mul, hbridge]
        exact inv_mul_cancel₀ hdet0
    obtain ⟨u, hu1, hu2⟩ := isUnit_iff_exists.mp hU
    refine isUnit_iff_exists.mpr ⟨(Ideal.Quotient.mk m) u, ?_, ?_⟩
    · rw [← map_mul, hu1, map_one]
    · rw [← map_mul, hu2, map_one]
  refine ⟨Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m), inferInstance, inferInstance,
    { toFun := fun h => IsUnit.unit (hunit h), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Units.ext
    rw [IsUnit.unit_spec]
    set M1 : Matrix (Fin n) (Fin n) ↥R :=
      fun i j => (⟨E (1:↥G) i j, (key 1).1 i j⟩ : ↥R) with hM1
    change ((Ideal.Quotient.mk m).mapMatrix M1) = _
    have hmat1 : M1 = 1 := by
      ext i j
      change E (1:↥G) i j = ((1 : Matrix (Fin n) (Fin n) ↥R) i j).val
      rw [hEone, Matrix.one_apply, Matrix.one_apply]
      split_ifs with hij <;> rfl
    rw [RingHom.mapMatrix_apply, hmat1, Matrix.GeneralLinearGroup.coe_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro a b
    apply Units.ext
    rw [IsUnit.unit_spec, Matrix.GeneralLinearGroup.coe_mul, IsUnit.unit_spec, IsUnit.unit_spec]
    set Ma : Matrix (Fin n) (Fin n) ↥R :=
      fun i j => (⟨E a i j, (key a).1 i j⟩ : ↥R) with hMa
    set Mb : Matrix (Fin n) (Fin n) ↥R :=
      fun i j => (⟨E b i j, (key b).1 i j⟩ : ↥R) with hMb
    set Mab : Matrix (Fin n) (Fin n) ↥R :=
      fun i j => (⟨E (a*b) i j, (key (a*b)).1 i j⟩ : ↥R) with hMab
    change ((Ideal.Quotient.mk m).mapMatrix Mab) =
      ((Ideal.Quotient.mk m).mapMatrix Ma) * ((Ideal.Quotient.mk m).mapMatrix Mb)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← Matrix.map_mul]
    have hmat : Mab = Ma * Mb := by
      ext i j
      change E (a*b) i j = ((Ma * Mb) i j).val
      rw [hEmul, Matrix.mul_apply, Matrix.mul_apply]
      have hsum := AddSubmonoid.coe_finsetSum R.toAddSubmonoid
        (fun k => Ma i k * Mb k j) Finset.univ
      rw [hsum]
      apply Finset.sum_congr rfl
      intro k _
      have e1 : ((Ma i k : ↥R).val = E a i k) := rfl
      have e2 : ((Mb k j : ↥R).val = E b k j) := rfl
      rw [Subalgebra.coe_mul R, e1, e2]
    rw [hmat]
  · intro hcon
    set Mg : Matrix (Fin n) (Fin n) ↥R :=
      fun a b => (⟨E g a b, (key g).1 a b⟩ : ↥R) with hMg
    have hentry : ∀ a b, ((Ideal.Quotient.mk m).mapMatrix Mg) a b =
        (((1 : Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m))) : Matrix _ _ _) a b := by
      intro a b
      have hcc0 : IsUnit.unit (hunit g) = 1 := by exact hcon
      have hcc := congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m) =>
        (Units.val u) a b) hcc0
      simp only [IsUnit.unit_spec] at hcc
      exact hcc
    have h2 := hentry i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h2
    have hEeq : E g i j = (E g i j - (1 : Matrix (Fin n) (Fin n) K) i j) +
        (1 : Matrix (Fin n) (Fin n) K) i j :=
      (sub_add_cancel _ _).symm
    have hReq : Mg i j =
        (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) +
            (⟨(1 : Matrix (Fin n) (Fin n) K) i j, h1R⟩ : ↥R) := by
      apply Subtype.ext
      change E g i j = _
      exact hEeq
    rw [hReq, map_add] at h2
    have h4 : (Ideal.Quotient.mk m) (⟨(1 : Matrix (Fin n) (Fin n) K) i j, h1R⟩ : ↥R) =
        (((1 : Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m))) : Matrix _ _ _) i j := by
      rw [Matrix.GeneralLinearGroup.coe_one]
      simp only [Matrix.one_apply]
      split_ifs with hij2
      · change (Ideal.Quotient.mk m) 1 = (1 : (↥R ⧸ m))
        exact map_one _
      · change (Ideal.Quotient.mk m) 0 = (0 : (↥R ⧸ m))
        exact map_zero _
    rw [h4] at h2
    have h5 : (Ideal.Quotient.mk m) (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) =
        0 := by
      have h6 : (Ideal.Quotient.mk m) (⟨E g i j - (1 : Matrix (Fin n) (Fin n) K) i j, hrR⟩ : ↥R) +
          (((1 : Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m))) : Matrix _ _ _) i j = 0 +
          (((1 : Matrix.GeneralLinearGroup (Fin n) (↥R ⧸ m))) : Matrix _ _ _) i j := by
        rw [zero_add]
        exact h2
      exact add_right_cancel_iff.mp h6
    exact hrm (Ideal.Quotient.eq_zero_iff_mem.mp h5)

end MathlibExt.GroupTheory.LinearGroupFinitenessWanted
end
