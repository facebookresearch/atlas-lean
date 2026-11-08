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
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

@[expose] public section

section
/-!
# Selberg finiteness for linear groups

Records Selberg's lemma for finitely generated linear groups.
-/

namespace MathlibExt.GroupTheory.LinearGroupFinitenessWanted

private theorem selberg_isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rw [Ideal.isPrime_int_iff] at hP
  rcases hP with rfl | ⟨p, hp, rfl⟩
  · -- P = ⊥
    rw [Ideal.eq_jacobson_iff_notMem]
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    have h1 : x.natAbs + 1 ≠ 1 := by
      simp [hx0]
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd h1
    refine ⟨Ideal.span ({(q : ℤ)} : Set ℤ), ⟨bot_le, ?hmax⟩, ?hxq⟩
    · have hPrime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      exact PrincipalIdealRing.isMaximal_of_irreducible hPrime.irreducible
    · rw [Ideal.mem_span_singleton]
      intro hdvd
      have hnat : q ∣ x.natAbs := by
        have h := (Int.natAbs_dvd_natAbs).mpr hdvd
        simpa using h
      have hone : q ∣ 1 := by
        have h2 := (Nat.dvd_add_right hnat).mp hqdvd
        simpa using h2
      have hq1 : q = 1 := Nat.dvd_one.mp hone
      have := hq.two_le
      omega
  · have hPrime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hPrime.irreducible
    exact @Ideal.jacobson_eq_self_of_isMaximal _ _ _ hmax

private theorem selberg_finite_of_finiteType_int (F : Type*) [Field F] [Algebra ℤ F]
    [Algebra.FiniteType ℤ F] : Finite F := by
  have := selberg_isJacobsonRing_int
  have hmodA := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hint : Algebra.IsIntegral ℤ F := Algebra.IsIntegral.of_finite ℤ F
  have hmax : (RingHom.ker (algebraMap ℤ F)).IsMaximal :=
    Algebra.ker_algebraMap_isMaximal_of_isIntegral ℤ F
  have hne : (RingHom.ker (algebraMap ℤ F)) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hmax Int.not_isField
  have hprime : (RingHom.ker (algebraMap ℤ F)).IsPrime := hmax.isPrime
  rw [Ideal.isPrime_int_iff] at hprime
  rcases hprime with hbot | ⟨p, hp, hpk⟩
  · exact absurd hbot hne
  · have hmem : ((p : ℤ)) ∈ RingHom.ker (algebraMap ℤ F) := by
      rw [hpk]
      exact Ideal.mem_span_singleton_self _
    have hp0 : algebraMap ℤ F (p : ℤ) = 0 := RingHom.mem_ker.mp hmem
    have hp0' : (p : F) = 0 := by simpa using hp0
    have hchar : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0'
    have := hchar
    have : NeZero p := ⟨hp.ne_zero⟩
    let _ := ZMod.algebra F p
    have hFT : Algebra.FiniteType ℤ F := inferInstance
    have hFT' : (algebraMap ℤ F).FiniteType := RingHom.finiteType_algebraMap.mpr hFT
    have hcomp : (algebraMap (ZMod p) F).comp (algebraMap ℤ (ZMod p)) =
        algebraMap ℤ F :=
      Subsingleton.elim _ _
    have h2 : ((algebraMap (ZMod p) F).comp (algebraMap ℤ (ZMod p))).FiniteType := by
      rw [hcomp]
      exact hFT'
    have hFTZ : Algebra.FiniteType (ZMod p) F :=
      RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType h2)
    have hInt2 : Algebra.IsIntegral (ZMod p) F := by
      rw [Algebra.isIntegral_def]
      intro x
      obtain ⟨P, hPm, hP0⟩ := (Algebra.isIntegral_def.mp hint) x
      refine ⟨P.map (Int.castRingHom (ZMod p)), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hc : ((algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p))) =
          algebraMap ℤ F :=
        Subsingleton.elim _ _
      rw [hc, ← Polynomial.aeval_def]
      exact hP0
    have hfin2 : Module.Finite (ZMod p) F :=
      Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨hInt2, hFTZ⟩
    have : Finite (ZMod p) := inferInstance
    have : Module.Finite (ZMod p) F := hfin2
    exact Module.finite_of_finite (ZMod p)

private theorem selberg_residue_finite_and_char {R : Type*} [CommRing R] [Algebra ℤ R]
    [Algebra.FiniteType ℤ R] {m : Ideal R} (hm : m.IsMaximal) :
    Finite (R ⧸ m) ∧ ∃ p : ℕ, Nat.Prime p ∧ ∀ N : ℕ, ((N : R) ∈ m ↔ p ∣ N) := by
  have := hm
  let _ := Ideal.Quotient.field m
  have hfin : Finite (R ⧸ m) := selberg_finite_of_finiteType_int (R ⧸ m)
  refine ⟨hfin, ?_⟩
  obtain ⟨p, hpchar⟩ := CharP.exists (R ⧸ m)
  have := hpchar
  have hp : Nat.Prime p := CharP.char_is_prime (R ⧸ m) p
  refine ⟨p, hp, fun N => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hcast : ((Ideal.Quotient.mk m) (N : R)) = (N : R ⧸ m) := map_natCast _ _
  rw [hcast]
  exact CharP.cast_eq_zero_iff (R ⧸ m) p N

private theorem selberg_entry_finset {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (S : Finset ↥G) :
    ∃ T : Finset K, (∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      ((((s : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ T)) ∧
      (∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      (((((s⁻¹ : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) i j ∈ T) := by
  classical
  refine ⟨((S.biUnion (fun s => (Finset.univ.biUnion (fun i => Finset.univ.image (fun j =>
    ((((s : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j)))))) ∪
    (S.biUnion (fun s => (Finset.univ.biUnion (fun i => Finset.univ.image (fun j =>
    (((((s⁻¹ : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) i j)))))), ?_, ?_⟩
  · intro s hs i j
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hs, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, rfl⟩
  · intro s hs i j
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨s, hs, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ j, rfl⟩

private theorem selberg_entries_mem_of_subset {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (S : Finset ↥G) (hS : Subgroup.closure (↑S : Set ↥G) = ⊤)
    (T : Finset K)
    (hTgen : ∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      ((((s : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ T))
    (hTinv : ∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      (((((s⁻¹ : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ T)
    (B : Subalgebra ℤ K) (hB : (↑T : Set K) ⊆ ↑B) :
    ∀ g : ↥G, ∀ i j : Fin n,
      ((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ B) := by
  classical
  have hmem : ∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      ((((s : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ B) := by
    intro s hs i j
    exact hB (Finset.mem_coe.mpr (hTgen s hs i j))
  have hmemInv : ∀ s : ↥G, s ∈ S → ∀ i j : Fin n,
      ((((s⁻¹ : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j ∈ B := by
    intro s hs i j
    exact hB (Finset.mem_coe.mpr (hTinv s hs i j))
  intro g i j
  have hg : g ∈ Subgroup.closure (↑S : Set ↥G) := by
    rw [hS]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction'' (fun x hx a b => hmem x hx a b)
    (fun x hx a b => hmemInv x hx a b) (fun a b => ?one) (fun x y _ _ hx hy a b => ?mul) hg i j
  · -- one
    have h1 : (((((1 : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) a b
        = (1 : Matrix (Fin n) (Fin n) K) a b := by
      rw [Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one]
    rw [h1, Matrix.one_apply]
    by_cases hij : a = b
    · simp [hij]
    · simp [hij]
  · -- mul
    have hxy : (((((x * y : ↥G)) : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        = ((((x : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)) *
          ((((y : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)) := by
      rw [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    rw [hxy, Matrix.mul_apply]
    exact Subalgebra.sum_mem _ (fun k _ => Subalgebra.mul_mem _ (hx _ k) (hy k _))

private theorem selberg_exists_lift_hom {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (B : Subalgebra ℤ K)
    (hB : ∀ g : ↥G, ∀ i j : Fin n,
      ((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j ∈ B)) :
    ∃ φ : ↥G →* Matrix.GeneralLinearGroup (Fin n) ↥B,
      Function.Injective φ ∧ ∀ g : ↥G, ∀ i j : Fin n,
        ((Units.val (φ g) i j : ↥B) : K) =
        ((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j) := by
  classical
  set M : ↥G → Matrix (Fin n) (Fin n) ↥B :=
    fun g => Matrix.of (fun i j =>
      ⟨((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j),
        hB g i j⟩)
  set E : ↥G → Matrix (Fin n) (Fin n) K :=
    fun g => ((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K)) with hE
  have hMspec : ∀ g : ↥G, ∀ i j : Fin n, (((M g i j : ↥B)) : K) = E g i j := by
    intro g i j
    rfl
  have hEmul : ∀ a b : ↥G, E (a * b) = E a * E b := by
    intro a b
    simp [hE, Subgroup.coe_mul]
  have hEone : E 1 = (1 : Matrix (Fin n) (Fin n) K) := by
    simp [hE]
  have hEinv : ∀ g : ↥G, E g * E (g⁻¹) = 1 := by
    intro g
    have h1 : ((g : Matrix.GeneralLinearGroup (Fin n) K)) *
        (((g⁻¹ : ↥G) : Matrix.GeneralLinearGroup (Fin n) K)) = 1 := by
      rw [Subgroup.coe_inv]
      exact mul_inv_cancel _
    have h2 := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h1
    simp only [hE] at h2 ⊢
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at h2
  have hEinv' : ∀ g : ↥G, E (g⁻¹) * E g = 1 := by
    intro g
    have h1 : (((g⁻¹ : ↥G) : Matrix.GeneralLinearGroup (Fin n) K)) *
        ((g : Matrix.GeneralLinearGroup (Fin n) K)) = 1 := by
      rw [Subgroup.coe_inv]
      exact inv_mul_cancel _
    have h2 := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h1
    simp only [hE] at h2 ⊢
    rwa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] at h2
  have hvinj : Function.Injective ⇑(Subalgebra.val B) := by
    intro a b hab
    rw [Subalgebra.val_apply, Subalgebra.val_apply] at hab
    exact Subtype.val_injective hab
  have hmapinj : Function.Injective
      (fun A : Matrix (Fin n) (Fin n) ↥B => Matrix.map A ⇑(Subalgebra.val B)) :=
    Matrix.map_injective hvinj
  have hmap : ∀ g : ↥G, Matrix.map (M g) ⇑(Subalgebra.val B) = E g := by
    intro g
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply, Subalgebra.val_apply]
    exact hMspec g i j
  have hmap_one : Matrix.map (1 : Matrix (Fin n) (Fin n) ↥B) ⇑(Subalgebra.val B) =
      (1 : Matrix (Fin n) (Fin n) K) :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hval_inv : ∀ g : ↥G, M g * M (g⁻¹) = 1 := by
    intro g
    apply hmapinj
    change Matrix.map (M g * M (g⁻¹)) ⇑(Subalgebra.val B) = Matrix.map 1 ⇑(Subalgebra.val B)
    rw [Matrix.map_mul, hmap, hmap, hEinv, hmap_one]
  have hinv_val : ∀ g : ↥G, M (g⁻¹) * M g = 1 := by
    intro g
    apply hmapinj
    change Matrix.map (M (g⁻¹) * M g) ⇑(Subalgebra.val B) = Matrix.map 1 ⇑(Subalgebra.val B)
    rw [Matrix.map_mul, hmap, hmap, hEinv', hmap_one]
  have hMeq_one : M 1 = 1 := by
    apply hmapinj
    change Matrix.map (M 1) ⇑(Subalgebra.val B) = Matrix.map 1 ⇑(Subalgebra.val B)
    rw [hmap, hEone, hmap_one]
  have hMmul : ∀ a b : ↥G, M (a * b) = M a * M b := by
    intro a b
    apply hmapinj
    change Matrix.map (M (a * b)) ⇑(Subalgebra.val B) = Matrix.map (M a * M b) ⇑(Subalgebra.val B)
    rw [hmap, hEmul, Matrix.map_mul, hmap, hmap]
  set F : ↥G → Matrix.GeneralLinearGroup (Fin n) ↥B :=
    fun g => Units.mk (M g) (M (g⁻¹)) (hval_inv g) (hinv_val g)
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_ }, ?inj, ?spec⟩
  · apply Units.ext
    change M 1 = 1
    exact hMeq_one
  · intro a b
    apply Units.ext
    change M (a * b) = M a * M b
    exact hMmul a b
  · intro a b hab
    have hval : M a = M b := congrArg
      (fun u : Matrix.GeneralLinearGroup (Fin n) ↥B => (u : Matrix (Fin n) (Fin n) ↥B)) hab
    have hEeq : E a = E b := by
      have h1 : Matrix.map (M a) ⇑(Subalgebra.val B) =
          Matrix.map (M b) ⇑(Subalgebra.val B) := by rw [hval]
      rwa [hmap, hmap] at h1
    have hGL : ((a : Matrix.GeneralLinearGroup (Fin n) K)) =
        ((b : Matrix.GeneralLinearGroup (Fin n) K)) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      have h := congrFun (congrFun hEeq i) j
      simpa [hE] using h
    exact Subtype.ext hGL
  · intro g i j
    change ((((M g i j : ↥B))) : K) = _
    exact hMspec g i j

private theorem matrix_mul_entries_mem_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    {I J : Ideal R} {A C : Matrix n n R}
    (hA : ∀ i j, A i j ∈ I) (hC : ∀ i j, C i j ∈ J) :
    ∀ i j, (A * C) i j ∈ I * J := by
  intro i j
  rw [Matrix.mul_apply]
  apply Ideal.sum_mem
  intro k _
  exact Ideal.mul_mem_mul (hA i k) (hC k j)

private theorem matrix_congr_step {R : Type*} [CommRing R] {m : Ideal R} (hm : m.IsMaximal)
    {n : Type*} [Fintype n] [DecidableEq n]
    {l : ℕ} (hl : (l : R) ∉ m)
    {x y : Matrix n n R}
    (hx : ∀ i j, (x - 1) i j ∈ m) (_hy : ∀ i j, (y - 1) i j ∈ m)
    (hpow : x ^ l = y ^ l)
    {k : ℕ} (hk : 1 ≤ k)
    (hcongr : ∀ i j, (y - x) i j ∈ m ^ k) :
    ∀ i j, (y - x) i j ∈ m ^ (k + 1) := by
  set I : Ideal R := m ^ (k + 1) with hI
  set π : R →+* R ⧸ I := Ideal.Quotient.mk I with hπ
  set F := (π.mapMatrix : Matrix n n R →+* Matrix n n (R ⧸ I)) with hF
  set X : Matrix n n (R ⧸ I) := F x with hX
  set e : Matrix n n (R ⧸ I) := F (y - x) with he
  have hY : F y = X + e := by
    have : y = x + (y - x) := by abel
    conv_lhs => rw [this]
    rw [map_add]
  have mem_iff : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ I) ↔ F A = 0 := by
    intro A
    constructor
    · intro h
      ext i j
      have : (F A) i j = π (A i j) := by
        simp [hF, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [this]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (h i j)
    · intro h i j
      have : (F A) i j = π (A i j) := by
        simp [hF, RingHom.mapMatrix_apply, Matrix.map_apply]
      have h0 : (F A) i j = 0 := by rw [h]; rfl
      rw [this] at h0
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
  have hkk : m ^ k * m = I := by rw [hI, pow_succ]
  have hmkk : m * m ^ k = I := by rw [hI, pow_succ']
  have heX : e * X = e := by
    have h1 : ∀ i j, ((y - x) * (x - 1)) i j ∈ I := by
      have h := matrix_mul_entries_mem_mul (I := m ^ k) (J := m) hcongr hx
      rwa [hkk] at h
    have h2 : F ((y - x) * (x - 1)) = 0 := (mem_iff _).mp h1
    have h5 : (y - x) * x = (y - x) * (x - 1) + (y - x) := by
      have hthis : ((x - 1 : Matrix n n R) + 1) = x := by abel
      conv_lhs => rw [show (y - x) * x = (y - x) * ((x - 1) + 1) by rw [hthis]]
      rw [mul_add, mul_one]
    have h6 : F ((y - x) * x) = e := by
      rw [h5, map_add, h2, zero_add]
    rw [map_mul] at h6
    rw [h6]
  have hXe : X * e = e := by
    have h1 : ∀ i j, ((x - 1) * (y - x)) i j ∈ I := by
      have h := matrix_mul_entries_mem_mul (I := m) (J := m ^ k) hx hcongr
      rwa [hmkk] at h
    have h2 : F ((x - 1) * (y - x)) = 0 := (mem_iff _).mp h1
    have h5 : x * (y - x) = (x - 1) * (y - x) + (y - x) := by
      have hthis : ((x - 1 : Matrix n n R) + 1) = x := by abel
      conv_lhs => rw [show x * (y - x) = ((x - 1) + 1) * (y - x) by rw [hthis]]
      rw [add_mul, one_mul]
    have h6 : F (x * (y - x)) = e := by
      rw [h5, map_add, h2, zero_add]
    rw [map_mul] at h6
    rw [h6]
  have hee : e * e = 0 := by
    have hle : m ^ k * m ^ k ≤ I := by
      rw [hI, ← pow_add]
      apply Ideal.pow_le_pow_right
      omega
    have h1 : ∀ i j, ((y - x) * (y - x)) i j ∈ I := by
      intro i j
      exact hle (matrix_mul_entries_mem_mul (I := m ^ k) (J := m ^ k) hcongr hcongr i j)
    have h2 : F ((y - x) * (y - x)) = 0 := (mem_iff _).mp h1
    rwa [map_mul] at h2
  have hXj : ∀ j : ℕ, X ^ j * e = e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_assoc, ih, hXe]
  have hpow2 : ∀ j : ℕ, (X + e) ^ j = X ^ j + j • e := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih]
      have hje : (j • e) * X = j • e := by
        rw [smul_mul_assoc, heX]
      have hjee : (j • e) * e = 0 := by
        rw [smul_mul_assoc, hee, smul_zero]
      have hXje : X ^ j * e = e := hXj j
      rw [add_mul, mul_add, mul_add, hXje, hje, hjee, add_zero, pow_succ,
        add_nsmul, one_nsmul]
      abel
  have hle : l • e = 0 := by
    have h1 : (X + e) ^ l = X ^ l := by rw [← hY, ← map_pow, ← map_pow, hpow]
    rw [hpow2] at h1
    have : X ^ l + l • e = X ^ l + 0 := by rw [h1, add_zero]
    exact add_left_cancel this
  have hmem1 : ∀ i j, (l : R) * (y - x) i j ∈ I := by
    intro i j
    have h0 : (l • e) i j = 0 := by rw [hle]; rfl
    have hentry : (l • e) i j = π ((l : R) * (y - x) i j) := by
      simp [he, hF, RingHom.mapMatrix_apply, Matrix.map_apply, nsmul_eq_mul, map_mul, map_natCast]
    rw [hentry] at h0
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
  obtain ⟨c, u, hu, hcu⟩ := hm.exists_inv hl
  intro i j
  have hsplit : (y - x) i j = c * ((l : R) * (y - x) i j) + u * (y - x) i j := by
    have hthis : c * (l : R) * (y - x) i j + u * (y - x) i j = (y - x) i j := by
      have : (c * (l : R) + u) * (y - x) i j = 1 * (y - x) i j := by rw [hcu]
      rwa [add_mul, one_mul] at this
    linear_combination -hthis
  rw [hsplit]
  apply Ideal.add_mem
  · exact I.mul_mem_left _ (hmem1 i j)
  · have h2 : u * (y - x) i j ∈ m * m ^ k := Ideal.mul_mem_mul hu (hcongr i j)
    rwa [hmkk] at h2

private theorem matrix_pow_left_injective_of_congr {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] {m : Ideal R} (hm : m.IsMaximal)
    {n : Type*} [Fintype n] [DecidableEq n]
    {l : ℕ} (hl : (l : R) ∉ m)
    {x y : Matrix n n R}
    (hx : ∀ i j, (x - 1) i j ∈ m) (hy : ∀ i j, (y - 1) i j ∈ m)
    (hpow : x ^ l = y ^ l) : x = y := by
  have hall : ∀ (k : ℕ), 1 ≤ k → ∀ i j, (y - x) i j ∈ m ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro i j
      have h1 : (y - x) i j = (y - 1) i j - (x - 1) i j := by
        simp [Matrix.sub_apply]
      rw [h1, pow_one]
      exact Ideal.sub_mem _ (hy i j) (hx i j)
    | succ k hk ih =>
      exact matrix_congr_step hm hl hx hy hpow hk ih
  have hmem : ∀ i j, (y - x) i j ∈ ⨅ k, m ^ k := by
    intro i j
    rw [Ideal.mem_iInf]
    intro k
    cases k with
    | zero => simp
    | succ k =>
      by_cases hk : 1 ≤ k + 1
      · exact hall (k+1) hk i j
      · omega
  have hbot : (⨅ k, m ^ k) = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain m hm.ne_top
  have hzero : y - x = 0 := by
    ext i j
    have h := hmem i j
    rw [hbot] at h
    exact (Ideal.mem_bot).mp h
  have : y = x := by
    have h' : y - x + x = 0 + x := by rw [hzero]
    rwa [sub_add_cancel, zero_add] at h'
  exact this.symm

private theorem selberg_congruence_ker_finiteIndex {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (B : Subalgebra ℤ K) [Algebra.FiniteType ℤ ↥B]
    {m : Ideal ↥B} (hm : m.IsMaximal)
    (φ : ↥G →* Matrix.GeneralLinearGroup (Fin n) ↥B) :
    ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)).comp φ).ker.FiniteIndex := by
  classical
  have hfin : Finite (↥B ⧸ m) := (selberg_residue_finite_and_char hm).1
  exact Subgroup.finiteIndex_ker _

private theorem selberg_congruence_ker_pow_injective {K : Type*} [Field K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (B : Subalgebra ℤ K) [Algebra.FiniteType ℤ ↥B]
    {m : Ideal ↥B} (hm : m.IsMaximal)
    (φ : ↥G →* Matrix.GeneralLinearGroup (Fin n) ↥B)
    (hφ : Function.Injective φ)
    {l : ℕ} (hl : ((l : ℕ) : ↥B) ∉ m)
    {a b : ↥G}
    (ha : a ∈ ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)).comp φ).ker)
    (hb : b ∈ ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)).comp φ).ker)
    (hpow : a ^ l = b ^ l) : a = b := by
  classical
  have hNoeth : IsNoetherianRing ↥B := Algebra.FiniteType.isNoetherianRing ℤ ↥B
  have hra : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)) (φ a) = 1 := by
    have h := MonoidHom.mem_ker.mp ha
    rwa [MonoidHom.comp_apply] at h
  have hrb : (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)) (φ b) = 1 := by
    have h := MonoidHom.mem_ker.mp hb
    rwa [MonoidHom.comp_apply] at h
  have entry_of_ker : ∀ (c : ↥G),
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)) (φ c) = 1 →
      ∀ i j, (Units.val (φ c) - 1) i j ∈ m := by
    intro c hc i j
    have h1 : Units.val ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m)) (φ c)) i j
        = Units.val (1 : Matrix.GeneralLinearGroup (Fin n) (↥B ⧸ m)) i j := by
      rw [hc]
    simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one] at h1
    have h2 : (Ideal.Quotient.mk m)
          (Units.val (φ c) i j - ((1 : Matrix (Fin n) (Fin n) ↥B)) i j) = 0 := by
      rw [map_sub]
      have h3 : (Ideal.Quotient.mk m) (((1 : Matrix (Fin n) (Fin n) ↥B)) i j)
          = ((1 : Matrix (Fin n) (Fin n) (↥B ⧸ m))) i j := by
        simp only [Matrix.one_apply]
        by_cases hij : i = j <;> simp [hij]
      rw [h3, h1, sub_self]
    have h4 : (Units.val (φ c) i j - ((1 : Matrix (Fin n) (Fin n) ↥B)) i j) ∈ m :=
      (Ideal.Quotient.eq_zero_iff_mem).mp h2
    have h5 : (Units.val (φ c) - 1) i j
        = (Units.val (φ c) i j - ((1 : Matrix (Fin n) (Fin n) ↥B)) i j) := by
      rw [Matrix.sub_apply]
    rw [h5]
    exact h4
  have hxmem := entry_of_ker a hra
  have hymem := entry_of_ker b hrb
  have hxy : Units.val (φ a) ^ l = Units.val (φ b) ^ l := by
    have h1 : φ (a ^ l) = φ (b ^ l) := by rw [hpow]
    rw [map_pow, map_pow] at h1
    have h2 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) ↥B => Units.val u) h1
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h2
  have hmat : Units.val (φ a) = Units.val (φ b) :=
    matrix_pow_left_injective_of_congr hm hl hxmem hymem hxy
  have hphi : φ a = φ b := Units.ext hmat
  exact hφ hphi

private theorem selberg_exists_subalgebra_inverting_prime {K : Type*} [Field K] [CharZero K]
    (T : Set K) (hT : T.Finite) {p : ℕ} (hp : Nat.Prime p) :
    ∃ B2 : Subalgebra ℤ K, Algebra.FiniteType ℤ ↥B2 ∧ T ⊆ (↑B2 : Set K) ∧
      IsUnit ((p : ℕ) : ↥B2) ∧
      (∀ (m2 : Ideal ↥B2), m2.IsMaximal → ∀ e : ℕ, ((p ^ e : ℕ) : ↥B2) ∉ m2) := by
  classical
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set s : Set K := T ∪ {((p : K))⁻¹} with hs
  have hfin : s.Finite := hT.union (Set.finite_singleton _)
  set B2 : Subalgebra ℤ K := Algebra.adjoin ℤ s with hB2
  have hFT : Algebra.FiniteType ℤ ↥B2 := Algebra.FiniteType.adjoin_of_finite hfin
  have hsub : T ⊆ (↑B2 : Set K) := by
    intro x hx
    exact Algebra.subset_adjoin (Set.mem_union_left _ hx)
  have hmem : ((p : K))⁻¹ ∈ B2 := Algebra.subset_adjoin (Set.mem_union_right _ rfl)
  have hcast : ((((p : ℕ) : ↥B2)) : K) = (p : K) := map_natCast (Subalgebra.val B2) p
  have hpunit : IsUnit ((p : ℕ) : ↥B2) := by
    refine ⟨Units.mk ((p : ℕ) : ↥B2) ⟨((p : K))⁻¹, hmem⟩ ?_ ?_, rfl⟩
    · apply Subtype.ext
      change ((((p : ℕ) : ↥B2) * ⟨((p : K))⁻¹, hmem⟩ : ↥B2) : K) = ((1 : ↥B2) : K)
      rw [Subalgebra.coe_mul]
      show ((((p : ℕ) : ↥B2) : K) * ((⟨((p : K))⁻¹, hmem⟩ : ↥B2) : K)) = _
      rw [hcast]
      change (p : K) * (((p : K))⁻¹) = _
      rw [mul_inv_cancel₀ hp0]
      rfl
    · apply Subtype.ext
      change (((⟨((p : K))⁻¹, hmem⟩ * ((p : ℕ) : ↥B2) : ↥B2)) : K) = ((1 : ↥B2) : K)
      rw [Subalgebra.coe_mul]
      show (((⟨((p : K))⁻¹, hmem⟩ : ↥B2) : K) * ((((p : ℕ) : ↥B2)) : K)) = _
      change (((p : K))⁻¹) * ((p : K)) = _
      rw [inv_mul_cancel₀ hp0]
      rfl
  refine ⟨B2, hFT, hsub, hpunit, ?_⟩
  intro m2 hm2 e he
  have hcast2 : (((p ^ e : ℕ) : ↥B2)) = (((p : ℕ) : ↥B2)) ^ e := by
    simp [Nat.cast_pow]
  have hunit : IsUnit (((p ^ e : ℕ) : ↥B2) ) := by
    rw [hcast2]
    exact hpunit.pow e
  have htop : m2 = ⊤ := Ideal.eq_top_of_isUnit_mem m2 he hunit
  exact hm2.ne_top htop

/--
If `K` has characteristic zero, every finitely generated `G ≤ GL_n(K)` contains a finite-index
torsion-free subgroup `H`. Source: A. Selberg, Contributions to Function Theory (1960) Selberg's
lemma; Alperin, Proc. AMS 1969; Lean states char-zero case with H not required normal.

Proves `Wanted` entry `selberg_finiteIndex_torsionFree`.
-/
theorem selberg_finiteIndex_torsionFree
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hFG : Group.FG G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsMulTorsionFree H := by
  classical
  obtain ⟨Sset, hSclose, hSfin⟩ := Group.fg_iff.mp hFG
  set S : Finset ↥G := hSfin.toFinset with hSdef
  have hS : Subgroup.closure (↑S : Set ↥G) = ⊤ := by
    rw [hSdef, Set.Finite.coe_toFinset]
    exact hSclose
  obtain ⟨T, hTgen, hTinv⟩ := selberg_entry_finset G S
  set B1 : Subalgebra ℤ K := Algebra.adjoin ℤ (↑T : Set K) with hB1def
  have hB1FT : Algebra.FiniteType ℤ ↥B1 :=
    Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet T)
  have hB1sub : (↑T : Set K) ⊆ (↑B1 : Set K) := Algebra.subset_adjoin
  have hB1 : ∀ g : ↥G, ∀ i j : Fin n,
      (((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j) ∈ B1) :=
    selberg_entries_mem_of_subset G S hS T hTgen hTinv B1 hB1sub
  obtain ⟨φ1, hφ1inj, _hφ1spec⟩ := selberg_exists_lift_hom G B1 hB1
  obtain ⟨m1, hm1⟩ := Ideal.exists_maximal ↥B1
  have : Algebra.FiniteType ℤ ↥B1 := hB1FT
  obtain ⟨p, hpprime, hchar⟩ := (selberg_residue_finite_and_char hm1).2
  obtain ⟨B2, hB2FT, hTB2, _hpunit, hpmem⟩ :=
    selberg_exists_subalgebra_inverting_prime (↑T : Set K) (Finset.finite_toSet T) hpprime
  have hB2 : ∀ g : ↥G, ∀ i j : Fin n,
      (((((g : Matrix.GeneralLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j) ∈ B2) :=
    selberg_entries_mem_of_subset G S hS T hTgen hTinv B2 hTB2
  obtain ⟨φ2, hφ2inj, _hφ2spec⟩ := selberg_exists_lift_hom G B2 hB2
  obtain ⟨m2, hm2⟩ := Ideal.exists_maximal ↥B2
  have : Algebra.FiniteType ℤ ↥B2 := hB2FT
  set ρ1 := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m1)).comp φ1 with hρ1
  set ρ2 := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk m2)).comp φ2 with hρ2
  have hfin1 : ρ1.ker.FiniteIndex := selberg_congruence_ker_finiteIndex G B1 hm1 φ1
  have hfin2 : ρ2.ker.FiniteIndex := selberg_congruence_ker_finiteIndex G B2 hm2 φ2
  refine ⟨ρ1.ker ⊓ ρ2.ker, ?_, ?_⟩
  · have := hfin1
    have := hfin2
    infer_instance
  · refine IsMulTorsionFree.mk ?_
    intro N hN a b _hcommute hab
    have haG := Subgroup.mem_inf.mp a.property
    have hbG := Subgroup.mem_inf.mp b.property
    have habG : (a : ↥G) ^ N = (b : ↥G) ^ N := by
      have h := congrArg (fun x : ↥(ρ1.ker ⊓ ρ2.ker) => (x : ↥G)) hab
      rwa [Subgroup.coe_pow, Subgroup.coe_pow] at h
    obtain ⟨e, N', hNdvd, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hpprime.ne_one
    have hpow1 : ((a : ↥G) ^ (p ^ e)) ^ N' = ((b : ↥G) ^ (p ^ e)) ^ N' := by
      rw [← pow_mul, ← pow_mul, ← hN]
      exact habG
    have hmem1a : (a : ↥G) ^ (p ^ e) ∈ ρ1.ker := Subgroup.pow_mem _ haG.1 _
    have hmem1b : (b : ↥G) ^ (p ^ e) ∈ ρ1.ker := Subgroup.pow_mem _ hbG.1 _
    have hN' : ((N' : ℕ) : ↥B1) ∉ m1 := by
      rw [hchar N']
      exact hNdvd
    have hstep1 : (a : ↥G) ^ (p ^ e) = (b : ↥G) ^ (p ^ e) :=
      selberg_congruence_ker_pow_injective G B1 hm1 φ1 hφ1inj hN' hmem1a hmem1b hpow1
    have hpe : ((p ^ e : ℕ) : ↥B2) ∉ m2 := hpmem m2 hm2 e
    have hstep2 : (a : ↥G) = (b : ↥G) :=
      selberg_congruence_ker_pow_injective G B2 hm2 φ2 hφ2inj hpe haG.2 hbG.2 hstep1
    exact Subtype.ext hstep2

end MathlibExt.GroupTheory.LinearGroupFinitenessWanted
end
