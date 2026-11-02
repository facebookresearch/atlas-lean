/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import MathlibExt.Combinatorics.Words.Automatic
public import MathlibExt.Combinatorics.Words.CobhamUniformMorphism
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace MetaMathlibExt

@[expose] public section


section ChrHelpers

variable {K : Type*} [Field K] [Fintype K]

/-- Cartier-type operator `Λ_j`: coefficient `n` of `Λ_j g` is coefficient
`q * n + j` of `g`, where `q = Fintype.card K`. Packaged as a `K`-linear map
so additivity and `map_sum` come for free. -/
private noncomputable def chr_lam (j : ℕ) : PowerSeries K →ₗ[K] PowerSeries K where
  toFun g := PowerSeries.mk fun n => PowerSeries.coeff (Fintype.card K * n + j) g
  map_add' a b := by
    ext n
    simp [PowerSeries.coeff_mk, map_add]
  map_smul' r a := by
    ext n
    simp [PowerSeries.coeff_mk]

/-- Coefficients of `Λ_j g`. -/
private theorem chr_lam_coeff (j n : ℕ) (g : PowerSeries K) :
    PowerSeries.coeff n (chr_lam (K := K) j g) =
      PowerSeries.coeff (Fintype.card K * n + j) g := by
  change PowerSeries.coeff n
      (PowerSeries.mk fun m => PowerSeries.coeff (Fintype.card K * m + j) g) = _
  exact PowerSeries.coeff_mk _ _

/-- The `q`-th power distributes over finite sums. -/
private theorem chr_pow_card_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries K) :
    (∑ i ∈ s, g i) ^ Fintype.card K = ∑ i ∈ s, (g i) ^ Fintype.card K := by
  rw [← FiniteField.PowerSeries.expand_card (K := K) (∑ i ∈ s, g i), map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    FiniteField.PowerSeries.expand_card (K := K) (g i)

/-- The `q ^ m`-th power distributes over finite sums. -/
private theorem chr_pow_card_pow_sum {ι : Type*} (m : ℕ) (s : Finset ι)
    (g : ι → PowerSeries K) :
    (∑ i ∈ s, g i) ^ Fintype.card K ^ m
      = ∑ i ∈ s, (g i) ^ Fintype.card K ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : ∀ x : PowerSeries K,
        x ^ Fintype.card K ^ (m + 1) = (x ^ Fintype.card K ^ m) ^ Fintype.card K := by
      intro x
      rw [pow_succ, pow_mul]
    simp only [e]
    rw [ih]
    exact chr_pow_card_sum s _

omit [Field K] in
/-- Divisibility criterion shared by N3 and N4: for `i, j < q` with
`i ≤ q * n + j`, `q ∣ q * n + j - i` iff `i = j`. -/
private theorem chr_dvd_iff {i j n : ℕ} (hq : 1 ≤ Fintype.card K)
    (hi : i < Fintype.card K) (hj : j < Fintype.card K)
    (hle : i ≤ Fintype.card K * n + j) :
    Fintype.card K ∣ Fintype.card K * n + j - i ↔ i = j := by
  have hq0 : 0 < Fintype.card K := lt_of_lt_of_le Nat.zero_lt_one hq
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h
    have hqn : Fintype.card K * n + j = Fintype.card K * t + i := by omega
    have hB : Fintype.card K * t < Fintype.card K * (n + 1) := by
      have e1 : Fintype.card K * (n + 1)
          = Fintype.card K * n + Fintype.card K := by
        rw [mul_add, mul_one]
      omega
    have hA : Fintype.card K * n < Fintype.card K * (t + 1) := by
      have e2 : Fintype.card K * (t + 1)
          = Fintype.card K * t + Fintype.card K := by
        rw [mul_add, mul_one]
      omega
    have htn : t = n := by
      have h1 := Nat.lt_of_mul_lt_mul_left hB
      have h2 := Nat.lt_of_mul_lt_mul_left hA
      omega
    subst htn
    omega
  · intro h
    have heq : Fintype.card K * n + j - i = Fintype.card K * n := by omega
    rw [heq]
    exact dvd_mul_right _ _

/-- `Λ_j (X ^ i * g ^ q)` is `g` if `i = j` and `0` otherwise. -/
private theorem chr_lam_X_pow_mul_pow {i j : ℕ} (hq : 1 ≤ Fintype.card K)
    (hi : i < Fintype.card K) (hj : j < Fintype.card K) (g : PowerSeries K) :
    chr_lam (K := K) j (PowerSeries.X ^ i * g ^ Fintype.card K)
      = if i = j then g else 0 := by
  have hq0 : 0 < Fintype.card K := by omega
  rw [← FiniteField.PowerSeries.expand_card (K := K) g]
  by_cases hij : i = j
  · rw [ite_eq_left hij, hij]
    apply PowerSeries.ext
    intro n
    rw [chr_lam_coeff, PowerSeries.coeff_X_pow_mul']
    have hle : j ≤ Fintype.card K * n + j := Nat.le_add_left _ _
    rw [ite_eq_left hle, PowerSeries.coeff_expand]
    have hdiv : Fintype.card K ∣ Fintype.card K * n + j - j := by
      have heq : Fintype.card K * n + j - j = Fintype.card K * n := by omega
      rw [heq]
      exact dvd_mul_right _ _
    rw [ite_eq_left hdiv]
    have hfin : (Fintype.card K * n + j - j) / Fintype.card K = n := by
      have heq : Fintype.card K * n + j - j = Fintype.card K * n := by omega
      rw [heq]
      exact Nat.mul_div_cancel_left _ hq0
    rw [hfin]
  · rw [ite_eq_right hij]
    apply PowerSeries.ext
    intro n
    rw [chr_lam_coeff, PowerSeries.coeff_X_pow_mul']
    by_cases hle : i ≤ Fintype.card K * n + j
    · have hneg : ¬ Fintype.card K ∣ Fintype.card K * n + j - i :=
        fun hd => hij ((chr_dvd_iff hq hi hj hle).mp hd)
      rw [ite_eq_left hle, PowerSeries.coeff_expand, ite_eq_right hneg]
      simp
    · rw [ite_eq_right hle]
      simp

/-- Every series decomposes as `g = ∑_{j < q} X ^ j * (Λ_j g) ^ q`. -/
private theorem chr_decomp (hq : 1 ≤ Fintype.card K) (g : PowerSeries K) :
    g = ∑ j ∈ Finset.range (Fintype.card K),
      PowerSeries.X ^ j * (chr_lam (K := K) j g) ^ Fintype.card K := by
  have hq0 : 0 < Fintype.card K := lt_of_lt_of_le Nat.zero_lt_one hq
  have hmod : ∀ n : ℕ, n % Fintype.card K < Fintype.card K :=
    fun n => Nat.mod_lt _ hq0
  ext n
  rw [map_sum]
  rw [Finset.sum_eq_single (n % Fintype.card K)]
  · have hnm : Fintype.card K * (n / Fintype.card K) + n % Fintype.card K = n :=
      Nat.div_add_mod n (Fintype.card K)
    have hle : n % Fintype.card K ≤ n := Nat.mod_le _ _
    rw [← FiniteField.PowerSeries.expand_card (K := K)
      (chr_lam (K := K) (n % Fintype.card K) g)]
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_left hle, PowerSeries.coeff_expand]
    have hdiv : Fintype.card K ∣ n - n % Fintype.card K :=
      ⟨n / Fintype.card K, by omega⟩
    rw [ite_eq_left hdiv, chr_lam_coeff]
    have hq1 : (n - n % Fintype.card K) / Fintype.card K
        = n / Fintype.card K := by
      have heq : n - n % Fintype.card K
          = Fintype.card K * (n / Fintype.card K) := by omega
      rw [heq]
      exact Nat.mul_div_cancel_left _ hq0
    rw [hq1, hnm]
  · intro b hb hne
    have hbq : b < Fintype.card K := Finset.mem_range.mp hb
    rw [← FiniteField.PowerSeries.expand_card (K := K)
      (chr_lam (K := K) b g)]
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hle : b ≤ n
    · have hneg : ¬ Fintype.card K ∣ n - b := by
        intro hd
        apply hne
        obtain ⟨t, ht⟩ := hd
        have hnb : n = Fintype.card K * t + b := by omega
        have hcomp : n % Fintype.card K = b := by
          rw [hnb, add_comm, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt hbq
        exact hcomp.symm
      rw [ite_eq_left hle, PowerSeries.coeff_expand, ite_eq_right hneg]
    · rw [ite_eq_right hle]
  · intro hcon
    exact absurd (Finset.mem_range.mpr (hmod n)) hcon

/-- `Λ_j (a * b ^ q) = Λ_j a * b`: the Cartier property. -/
private theorem chr_lam_mul_pow {j : ℕ} (hj : j < Fintype.card K)
    (hq : 1 ≤ Fintype.card K) (a b : PowerSeries K) :
    chr_lam (K := K) j (a * b ^ Fintype.card K)
      = chr_lam (K := K) j a * b := by
  have hmem : j ∈ Finset.range (Fintype.card K) := Finset.mem_range.mpr hj
  conv_lhs => rw [chr_decomp hq a, Finset.sum_mul]
  rw [map_sum, Finset.sum_eq_single j]
  · rw [mul_assoc, ← mul_pow, chr_lam_X_pow_mul_pow hq hj hj,
      ite_eq_left rfl]
  · intro i hi hne
    rw [mul_assoc, ← mul_pow,
      chr_lam_X_pow_mul_pow hq (Finset.mem_range.mp hi) hj, ite_eq_right hne]
  · intro hcon
    exact absurd hmem hcon

/-- Polynomial version of `Λ_j`: coefficient `n` is `c.coeff (q * n + j)`. -/
private noncomputable def chr_lamP (j : ℕ) (c : Polynomial K) : Polynomial K :=
  ∑ n ∈ Finset.range (c.natDegree + 1),
    Polynomial.monomial n (c.coeff (Fintype.card K * n + j))

/-- Coefficients of the polynomial `Λ_j`. -/
private theorem chr_lamP_coeff (hq : 1 ≤ Fintype.card K) (j : ℕ)
    (c : Polynomial K) (n : ℕ) :
    (chr_lamP (K := K) j c).coeff n = c.coeff (Fintype.card K * n + j) := by
  unfold chr_lamP
  rw [Polynomial.finsetSum_coeff]
  by_cases hn : n < c.natDegree + 1
  · rw [Finset.sum_eq_single n]
    · rw [Polynomial.coeff_monomial, ite_eq_left rfl]
    · intro m _ hne
      rw [Polynomial.coeff_monomial, ite_eq_right hne]
    · intro hcon
      exact absurd (Finset.mem_range.mpr hn) hcon
  · have hnle : c.natDegree + 1 ≤ n := not_lt.mp hn
    have hnj : n ≤ Fintype.card K * n + j := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hq
      rw [ht, add_mul, one_mul]
      omega
    have h1 : ∀ m ∈ Finset.range (c.natDegree + 1),
        (Polynomial.monomial m (c.coeff (Fintype.card K * m + j))).coeff n
          = 0 := by
      intro m hm
      have hm' : m < c.natDegree + 1 := Finset.mem_range.mp hm
      have hnm : ¬ m = n := by omega
      rw [Polynomial.coeff_monomial, ite_eq_right hnm]
    rw [Finset.sum_eq_zero h1]
    have h2 : c.natDegree < Fintype.card K * n + j := by omega
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt h2).symm

/-- Coercion compatibility: `↑(Λ^P_j c) = Λ_j ↑c`. -/
private theorem chr_coe_lamP (hq : 1 ≤ Fintype.card K) (j : ℕ)
    (c : Polynomial K) :
    ((chr_lamP (K := K) j c : Polynomial K) : PowerSeries K)
      = chr_lam (K := K) j ((c : Polynomial K) : PowerSeries K) := by
  apply PowerSeries.ext
  intro n
  rw [chr_lam_coeff, Polynomial.coeff_coe, Polynomial.coeff_coe,
    chr_lamP_coeff hq]

/-- Degree bound: if `c.natDegree ≤ q * N` then `(Λ^P_j c).natDegree ≤ N`. -/
private theorem chr_natDegree_lamP_le (hq : 1 ≤ Fintype.card K) {j N : ℕ}
    (c : Polynomial K) (h : c.natDegree ≤ Fintype.card K * N) :
    (chr_lamP (K := K) j c).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [chr_lamP_coeff hq]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show N + 1 ≤ n by omega)
  have e : Fintype.card K * (N + 1 + t)
      = Fintype.card K * N + Fintype.card K + Fintype.card K * t := by
    ring
  rw [ht, e]
  omega

/-- `Λ^P_j 0 = 0`. -/
private theorem chr_lamP_zero (hq : 1 ≤ Fintype.card K) (j : ℕ) :
    chr_lamP (K := K) j 0 = 0 := by
  rw [Polynomial.ext_iff]
  intro n
  rw [chr_lamP_coeff hq]
  simp

/-- If `c ≠ 0` then `Λ^P_j c ≠ 0` for some `j < q`. -/
private theorem chr_lamP_ne_zero (hq : 1 ≤ Fintype.card K) {c : Polynomial K}
    (hc : c ≠ 0) :
    ∃ j, j < Fintype.card K ∧ chr_lamP (K := K) j c ≠ 0 := by
  by_contra hall
  have h : ∀ j, j < Fintype.card K → chr_lamP (K := K) j c = 0 := by
    intro j hj
    by_contra hjc
    exact hall ⟨j, hj, hjc⟩
  apply hc
  apply Polynomial.coe_eq_zero_iff.mp
  have hdecomp := chr_decomp hq ((c : Polynomial K) : PowerSeries K)
  rw [hdecomp]
  exact Finset.sum_eq_zero fun j hj => by
    rw [← chr_coe_lamP hq j c, h j (Finset.mem_range.mp hj)]
    simp

end ChrHelpers


section ChrMain

variable {K : Type*} [Field K] [Fintype K]

/-- Decidable equality on power series, needed for `Finset.image` in statements. -/
@[instance_reducible]
private noncomputable def chrDecEq : DecidableEq (PowerSeries K) :=
  Classical.decEq _

attribute [local instance] chrDecEq

omit [Fintype K] in
/-- The coercion is the algebra map. -/
private theorem chr_algebraMap (p : Polynomial K) :
    algebraMap (Polynomial K) (PowerSeries K) p
      = ((p : Polynomial K) : PowerSeries K) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.algebraMap_apply', PowerSeries.coeff_map, Polynomial.coeff_coe]
  simp

/-- One-step span inclusion `V m ≤ V (m + 1)`. -/
private theorem chr_span_step {F : Finset (PowerSeries K)}
    (hq : 1 ≤ Fintype.card K)
    (hF : ∀ g ∈ F, ∀ j, j < Fintype.card K → chr_lam (K := K) j g ∈ F)
    (m : ℕ) :
    Submodule.span (Polynomial K)
        (↑(F.image fun g => g ^ Fintype.card K ^ m) : Set (PowerSeries K))
      ≤ Submodule.span (Polynomial K)
        (↑(F.image fun g => g ^ Fintype.card K ^ (m + 1))
          : Set (PowerSeries K)) := by
  rw [Submodule.span_le]
  intro y hy
  obtain ⟨g, hgF, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  have hdecomp := chr_decomp hq g
  have hpow : g ^ Fintype.card K ^ m
      = ∑ j ∈ Finset.range (Fintype.card K),
        (PowerSeries.X ^ j * (chr_lam (K := K) j g) ^ Fintype.card K)
          ^ Fintype.card K ^ m := by
    conv_lhs => rw [hdecomp]
    rw [chr_pow_card_pow_sum]
  rw [hpow]
  apply Submodule.sum_mem
  intro j hj
  have hjq : j < Fintype.card K := Finset.mem_range.mp hj
  have hq1 : (PowerSeries.X ^ j) ^ Fintype.card K ^ m
      = ((Polynomial.X ^ (j * Fintype.card K ^ m) : Polynomial K)
        : PowerSeries K) := by
    rw [← pow_mul, Polynomial.coe_pow, Polynomial.coe_X]
  have hq2 : ((chr_lam (K := K) j g) ^ Fintype.card K) ^ Fintype.card K ^ m
      = (chr_lam (K := K) j g) ^ Fintype.card K ^ (m + 1) := by
    have e : Fintype.card K * Fintype.card K ^ m
        = Fintype.card K ^ (m + 1) := by
      rw [pow_succ']
    rw [← pow_mul, e]
  have hterm : (PowerSeries.X ^ j * (chr_lam (K := K) j g) ^ Fintype.card K)
        ^ Fintype.card K ^ m
      = ((Polynomial.X ^ (j * Fintype.card K ^ m) : Polynomial K)
        : PowerSeries K)
        * (chr_lam (K := K) j g) ^ Fintype.card K ^ (m + 1) := by
    rw [mul_pow, hq1, hq2]
  have hsmul : ((Polynomial.X ^ (j * Fintype.card K ^ m) : Polynomial K)
        : PowerSeries K)
        * (chr_lam (K := K) j g) ^ Fintype.card K ^ (m + 1)
      = ((Polynomial.X ^ (j * Fintype.card K ^ m) : Polynomial K)) •
        ((chr_lam (K := K) j g) ^ Fintype.card K ^ (m + 1)) := by
    rw [Algebra.smul_def, chr_algebraMap]
  rw [hterm, hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨chr_lam (K := K) j g, hF g hgF j hjq, rfl⟩))

/-- The span is monotone and contains every `f ^ (q ^ l)` for `l ≤ m`. -/
private theorem chr_span_mono {F : Finset (PowerSeries K)}
    (hq : 1 ≤ Fintype.card K) {f : PowerSeries K} (hf : f ∈ F)
    (hF : ∀ g ∈ F, ∀ j, j < Fintype.card K → chr_lam (K := K) j g ∈ F)
    {l m : ℕ} (hlm : l ≤ m) :
    f ^ Fintype.card K ^ l ∈ Submodule.span (Polynomial K)
      (↑(F.image fun g => g ^ Fintype.card K ^ m) : Set (PowerSeries K)) := by
  have hmono : Monotone (fun m => Submodule.span (Polynomial K)
      (↑(F.image fun g => g ^ Fintype.card K ^ m) : Set (PowerSeries K))) :=
    monotone_nat_of_le_succ (fun m => chr_span_step hq hF m)
  have hmem : f ^ Fintype.card K ^ l ∈
      (↑(F.image fun g => g ^ Fintype.card K ^ l) : Set (PowerSeries K)) := by
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨f, hf, rfl⟩
  have hle := hmono hlm
  simp only [] at hle
  exact hle (Submodule.subset_span hmem)

/-- A series with finite `q`-kernel is algebraic over `K[X]`. -/
private theorem chr_isAlgebraic_of_finite_kernel (hq : 1 ≤ Fintype.card K)
    {f : PowerSeries K}
    (hfin : Finite ↥(kKernel (Fintype.card K)
      (fun n => PowerSeries.coeff n f))) :
    IsAlgebraic (Polynomial K) f := by
  classical
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  set S : Finset (ℕ → K) :=
    (Set.finite_coe_iff.mp hfin).toFinset with hSdef
  set F : Finset (PowerSeries K) :=
    S.image (fun b => PowerSeries.mk b) with hFdef
  have hSmem : ∀ b : ℕ → K, b ∈ S ↔ b ∈ kKernel (Fintype.card K)
      (fun n => PowerSeries.coeff n f) := by
    intro b
    simp only [hSdef, Set.Finite.mem_toFinset]
  have hfmem : f ∈ F := by
    have hself : (fun n => PowerSeries.coeff n f) ∈ kKernel (Fintype.card K)
        (fun n => PowerSeries.coeff n f) :=
      chr_self_mem_kernel _
    have hmk : PowerSeries.mk (fun n => PowerSeries.coeff n f) = f :=
      PowerSeries.ext fun n => PowerSeries.coeff_mk n _
    rw [hFdef, Finset.mem_image]
    exact ⟨_, (hSmem _).mpr hself, hmk⟩
  have hstab : ∀ g ∈ F, ∀ j, j < Fintype.card K
      → chr_lam (K := K) j g ∈ F := by
    intro g hg j hj
    rw [hFdef, Finset.mem_image] at hg ⊢
    obtain ⟨b, hbS, rfl⟩ := hg
    refine ⟨fun n => b (Fintype.card K * n + j),
      (hSmem _).mpr (chr_kernel_lam_mem ((hSmem _).mp hbS) hj), ?_⟩
    apply PowerSeries.ext
    intro n
    simp only [chr_lam_coeff, PowerSeries.coeff_mk]
  by_cases hv : LinearIndependent (Polynomial K)
      (fun l : Fin (F.card + 1) => f ^ Fintype.card K ^ l.val)
  · exfalso
    have hrange : Set.range
          (fun l : Fin (F.card + 1) => f ^ Fintype.card K ^ l.val)
        ⊆ Submodule.span (Polynomial K)
          (↑(F.image fun g => g ^ Fintype.card K ^ F.card)
            : Set (PowerSeries K)) := by
      rintro y ⟨l, rfl⟩
      simp only []
      exact chr_span_mono hq hfmem hstab (Nat.lt_succ_iff.mp l.2)
    have hcard := linearIndependent_le_span' _ hv _ hrange
    simp only [Cardinal.mk_fin, Finset.coe_sort_coe,
      Fintype.card_coe] at hcard
    have hle : (F.image fun g => g ^ Fintype.card K ^ F.card).card
        ≤ F.card :=
      Finset.card_image_le
    have hlt : F.card + 1
        ≤ (F.image fun g => g ^ Fintype.card K ^ F.card).card := by
      exact_mod_cast hcard
    omega
  · rw [Fintype.not_linearIndependent_iff] at hv
    obtain ⟨g, hg0, l₁, hg1⟩ := hv
    set P : Polynomial (Polynomial K) :=
      ∑ l : Fin (F.card + 1),
        Polynomial.monomial (Fintype.card K ^ l.val) (g l) with hPdef
    have hPne : P ≠ 0 := by
      intro hcon
      apply hg1
      have hcoeff : P.coeff (Fintype.card K ^ l₁.val) = 0 := by
        rw [hcon, Polynomial.coeff_zero]
      have hsingle : (∑ l : Fin (F.card + 1),
            (Polynomial.monomial (Fintype.card K ^ l.val) (g l)).coeff
              (Fintype.card K ^ l₁.val))
          = g l₁ := by
        rw [Finset.sum_eq_single l₁]
        · rw [Polynomial.coeff_monomial, ite_eq_left rfl]
        · intro l _ hne
          have hneg : ¬ Fintype.card K ^ l.val
              = Fintype.card K ^ l₁.val := by
            intro hcon2
            apply hne
            exact Fin.ext (Nat.pow_right_injective hq2 hcon2)
          rw [Polynomial.coeff_monomial, ite_eq_right hneg]
        · intro hcon2
          exact absurd (Finset.mem_univ l₁) hcon2
      rw [hPdef, Polynomial.finsetSum_coeff, hsingle] at hcoeff
      exact hcoeff
    have hP0 : Polynomial.aeval f P = 0 := by
      have hsum : (∑ l : Fin (F.card + 1), Polynomial.aeval f
            (Polynomial.monomial (Fintype.card K ^ l.val) (g l)))
          = ∑ i, g i • (fun l : Fin (F.card + 1)
            => f ^ Fintype.card K ^ l.val) i := by
        apply Finset.sum_congr rfl
        intro l _
        simp only []
        rw [Polynomial.aeval_monomial, Algebra.smul_def]
      rw [hPdef, map_sum]
      exact hsum.trans hg0
    exact ⟨P, hPne, hP0⟩

/-- Ore relation: algebraicity gives
`Σ_{l ∈ range (m+1)} (c l) * f ^ (q ^ l) = 0` with some `c l ≠ 0`. -/
private theorem chr_ore {f : PowerSeries K}
    (halg : IsAlgebraic (Polynomial K) f) :
    ∃ m : ℕ, ∃ c : ℕ → Polynomial K,
      (∃ l ≤ m, c l ≠ 0)
        ∧ ∑ l ∈ Finset.range (m + 1), ((c l : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ l = 0 := by
  classical
  obtain ⟨y, hy0, hint⟩ := IsAlgebraic.exists_integral_multiple halg
  set g : PowerSeries K := y • f with hgdef
  have hg : ((y : Polynomial K) : PowerSeries K) * f = g := by
    rw [hgdef, Algebra.smul_def, chr_algebraMap]
  have hgmem : g ∈ Algebra.adjoin (Polynomial K) ({g} : Set (PowerSeries K)) := by
    simp
  obtain ⟨T, hT⟩ := hint.fg_adjoin_singleton
  have hmem : ∀ l : Fin (T.card + 1),
      g ^ Fintype.card K ^ l.val ∈ Submodule.span (Polynomial K)
        (↑T : Set (PowerSeries K)) := by
    intro l
    rw [hT]
    exact Subalgebra.pow_mem _ hgmem _
  by_cases hv : LinearIndependent (Polynomial K)
      (fun l : Fin (T.card + 1) => g ^ Fintype.card K ^ l.val)
  · exfalso
    have hrange : Set.range
          (fun l : Fin (T.card + 1) => g ^ Fintype.card K ^ l.val)
        ⊆ Submodule.span (Polynomial K) (↑T : Set (PowerSeries K)) := by
      rintro y_ ⟨l, rfl⟩
      simp only []
      exact hmem l
    have hcard := linearIndependent_le_span' _ hv _ hrange
    simp only [Cardinal.mk_fin, Finset.coe_sort_coe,
      Fintype.card_coe] at hcard
    have hlt : T.card + 1 ≤ T.card := by exact_mod_cast hcard
    omega
  · rw [Fintype.not_linearIndependent_iff] at hv
    obtain ⟨e, he0, l₁, he1⟩ := hv
    set c : ℕ → Polynomial K := fun l =>
      if h : l < T.card + 1 then e ⟨l, h⟩ * y ^ Fintype.card K ^ l else 0
      with hcdef
    have hterm : ∀ l (h : l < T.card + 1),
        ((c l : Polynomial K) : PowerSeries K) * f ^ Fintype.card K ^ l
        = e ⟨l, h⟩ • g ^ Fintype.card K ^ l := by
      intro l h
      have hc : c l = e ⟨l, h⟩ * y ^ Fintype.card K ^ l := dite_eq_left h
      rw [hc, Polynomial.coe_mul, Polynomial.coe_pow, mul_assoc, ← mul_pow, hg,
        Algebra.smul_def, chr_algebraMap]
    have hbridge : (∑ l ∈ Finset.range (T.card + 1),
          ((c l : Polynomial K) : PowerSeries K) * f ^ Fintype.card K ^ l)
        = ∑ i ∈ Finset.range (T.card + 1),
          (if h : i < T.card + 1 then e ⟨i, h⟩ • g ^ Fintype.card K ^ i
            else 0) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlm : l < T.card + 1 := Finset.mem_range.mp hl
      rw [dite_eq_left hlm]
      exact hterm l hlm
    have hfin0 : (∑ i ∈ Finset.range (T.card + 1),
          (if h : i < T.card + 1 then e ⟨i, h⟩ • g ^ Fintype.card K ^ i
            else 0)) = 0 :=
      (Finset.sum_fin_eq_sum_range _).symm.trans he0
    have hrel : (∑ l ∈ Finset.range (T.card + 1),
          ((c l : Polynomial K) : PowerSeries K) * f ^ Fintype.card K ^ l)
        = 0 := by
      rw [hbridge]
      exact hfin0
    have hcne : c l₁.val ≠ 0 := by
      have h1 : c l₁.val
          = e ⟨l₁.val, l₁.2⟩ * y ^ Fintype.card K ^ l₁.val := dite_eq_left l₁.2
      rw [h1]
      apply mul_ne_zero _ (pow_ne_zero _ hy0)
      exact he1
    exact ⟨T.card, c, ⟨l₁.val, Nat.lt_succ_iff.mp l₁.2, hcne⟩, hrel⟩

/-- Shift step: from a relation vanishing below `l₀ + 1` with `c (l₀ + 1) ≠ 0`,
produce one vanishing below `l₀` with nonzero `l₀`-coefficient. -/
private theorem chr_ore_zero_aux (hq : 1 ≤ Fintype.card K) (m : ℕ)
    (f : PowerSeries K) (l₀ : ℕ) :
    ∀ (_hl₀m : l₀ ≤ m) (c : ℕ → Polynomial K),
      (∀ l < l₀, c l = 0) → c l₀ ≠ 0 →
      (∑ l ∈ Finset.range (m + 1), ((c l : Polynomial K) : PowerSeries K)
        * f ^ Fintype.card K ^ l = 0) →
      ∃ c' : ℕ → Polynomial K, c' 0 ≠ 0 ∧
        (∑ l ∈ Finset.range (m + 1), ((c' l : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ l = 0) := by
  induction l₀ with
  | zero => intro _ c _ hc0 hrel; exact ⟨c, hc0, hrel⟩
  | succ l₀ ih =>
    intro _hl₀m c hvan hc0 hrel
    have hlm : l₀ < m := by omega
    have hc0' : c 0 = 0 := hvan 0 (Nat.zero_lt_succ _)
    have hrel1 : ∑ l ∈ Finset.range m,
          ((c (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1) = 0 := by
      have h := hrel
      rw [Finset.sum_range_succ'] at h
      rw [hc0', Polynomial.coe_zero, zero_mul, add_zero] at h
      exact h
    set G : ℕ → PowerSeries K := fun j =>
      ∑ l ∈ Finset.range m, ((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
        : PowerSeries K) * f ^ Fintype.card K ^ l with hGdef
    have hexpand : ∀ l ∈ Finset.range m,
        ((c (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1)
        = ∑ j ∈ Finset.range (Fintype.card K), PowerSeries.X ^ j *
          ((((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
            : PowerSeries K)) * f ^ Fintype.card K ^ l)
          ^ Fintype.card K := by
      intro l _
      have hdecomp := chr_decomp hq
        (((c (l + 1) : Polynomial K)) : PowerSeries K)
      have hpow : f ^ Fintype.card K ^ (l + 1)
          = (f ^ Fintype.card K ^ l) ^ Fintype.card K := by
        have e : Fintype.card K ^ (l + 1)
            = Fintype.card K ^ l * Fintype.card K := pow_succ _ _
        rw [e, ← pow_mul]
      rw [hpow]
      conv_lhs => rw [hdecomp, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, ← mul_pow, ← chr_coe_lamP hq]
    have hGj : ∀ j, PowerSeries.X ^ j * (G j) ^ Fintype.card K
        = ∑ l ∈ Finset.range m, PowerSeries.X ^ j *
          ((((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
            : PowerSeries K)) * f ^ Fintype.card K ^ l)
          ^ Fintype.card K := by
      intro j
      rw [hGdef]
      simp only []
      rw [chr_pow_card_sum, Finset.mul_sum]
    have hsum : (∑ l ∈ Finset.range m,
          ((c (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1))
        = ∑ j ∈ Finset.range (Fintype.card K),
          PowerSeries.X ^ j * (G j) ^ Fintype.card K := by
      calc _ = ∑ l ∈ Finset.range m, ∑ j ∈ Finset.range (Fintype.card K),
            PowerSeries.X ^ j *
            ((((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
              : PowerSeries K)) * f ^ Fintype.card K ^ l)
            ^ Fintype.card K :=
            Finset.sum_congr rfl (fun l hl => hexpand l hl)
        _ = ∑ j ∈ Finset.range (Fintype.card K), ∑ l ∈ Finset.range m,
            PowerSeries.X ^ j *
            ((((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
              : PowerSeries K)) * f ^ Fintype.card K ^ l)
            ^ Fintype.card K := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun j _ => (hGj j).symm)
    have hkey : ∑ j ∈ Finset.range (Fintype.card K),
        PowerSeries.X ^ j * (G j) ^ Fintype.card K = 0 :=
      hsum.symm.trans hrel1
    have hG0 : ∀ i, i < Fintype.card K → G i = 0 := by
      intro i hi
      have h := congrArg (chr_lam (K := K) i) hkey
      have hterm : ∀ j ∈ Finset.range (Fintype.card K),
          chr_lam (K := K) i (PowerSeries.X ^ j * (G j) ^ Fintype.card K)
          = if j = i then G j else 0 := by
        intro j hj
        exact chr_lam_X_pow_mul_pow hq (Finset.mem_range.mp hj) hi _
      have h2 : (∑ j ∈ Finset.range (Fintype.card K),
            chr_lam (K := K) i
              (PowerSeries.X ^ j * (G j) ^ Fintype.card K))
          = G i := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
          ite_eq_left (Finset.mem_range.mpr hi)]
      rw [map_sum, h2, map_zero] at h
      exact h
    obtain ⟨j, hjq, hjne⟩ := chr_lamP_ne_zero hq hc0
    set c' : ℕ → Polynomial K := fun l =>
      if l < m then chr_lamP (K := K) j (c (l + 1)) else 0 with hc'def
    have hvan' : ∀ l < l₀, c' l = 0 := by
      intro l hl
      have hlm2 : l < m := by omega
      have hcl : c (l + 1) = 0 := hvan (l + 1) (by omega)
      have hcc : c' l = chr_lamP (K := K) j (c (l + 1)) := dite_eq_left hlm2
      rw [hcc, hcl, chr_lamP_zero hq]
    have hc0'' : c' l₀ ≠ 0 := by
      have hcc : c' l₀ = chr_lamP (K := K) j (c (l₀ + 1)) := dite_eq_left hlm
      rw [hcc]
      exact hjne
    have hrel' : ∑ l ∈ Finset.range (m + 1),
          ((c' l : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ l = 0 := by
      have hFm : ((c' m : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ m = 0 := by
        have hm0 : c' m = 0 := dite_eq_right (lt_irrefl m)
        rw [hm0, Polynomial.coe_zero, zero_mul]
      have hFl : ∀ l ∈ Finset.range m,
          ((c' l : Polynomial K) : PowerSeries K) * f ^ Fintype.card K ^ l
          = ((chr_lamP (K := K) j (c (l + 1)) : Polynomial K)
            : PowerSeries K) * f ^ Fintype.card K ^ l := by
        intro l hl
        have hlm2 : l < m := Finset.mem_range.mp hl
        have hcc : c' l = chr_lamP (K := K) j (c (l + 1)) := dite_eq_left hlm2
        rw [hcc]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hFl, hFm, add_zero]
      exact hG0 j hjq
    exact ih (by omega) c' hvan' hc0'' hrel'

/-- From an Ore relation, one with nonzero constant coefficient. -/
private theorem chr_ore_zero (hq : 1 ≤ Fintype.card K) (m : ℕ)
    (f : PowerSeries K) (c : ℕ → Polynomial K)
    (hne : ∃ l ≤ m, c l ≠ 0)
    (hrel : ∑ l ∈ Finset.range (m + 1), ((c l : Polynomial K) : PowerSeries K)
      * f ^ Fintype.card K ^ l = 0) :
    ∃ c' : ℕ → Polynomial K, c' 0 ≠ 0 ∧
      (∑ l ∈ Finset.range (m + 1), ((c' l : Polynomial K) : PowerSeries K)
        * f ^ Fintype.card K ^ l = 0) := by
  classical
  obtain ⟨l₁, hl₁m, hl₁ne⟩ := hne
  have hex : ∃ l, c l ≠ 0 := ⟨l₁, hl₁ne⟩
  set l₀ := Nat.find hex with hl₀def
  have hmin : c l₀ ≠ 0 := Nat.find_spec hex
  have hfind_le : l₀ ≤ m := (Nat.find_min' hex hl₁ne).trans hl₁m
  have hvan : ∀ l < l₀, c l = 0 := by
    intro l hl
    have hneg := Nat.find_min hex hl
    simpa using hneg
  exact chr_ore_zero_aux hq m f l₀ hfind_le c hvan hmin hrel

/-- The finite set `H` of series controlled by degree-`N` coefficients. -/
private def chr_H (N m : ℕ) (c : ℕ → Polynomial K) (f : PowerSeries K) :
    Set (PowerSeries K) :=
  {h | ∃ t : ℕ → Polynomial K, (∀ l, (t l).natDegree ≤ N) ∧
    ((c 0 : Polynomial K) : PowerSeries K) * h
      = ∑ l ∈ Finset.range (m + 1), ((t l : Polynomial K) : PowerSeries K)
        * f ^ Fintype.card K ^ l}

/-- `f ∈ H`. -/
private theorem chr_mem_H (N m : ℕ) (c : ℕ → Polynomial K)
    (f : PowerSeries K)
    (hN : ∀ l ∈ Finset.range (m + 1), (c l).natDegree ≤ N) :
    f ∈ chr_H N m c f := by
  refine ⟨fun l => if l = 0 then c 0 else 0, ?_, ?_⟩
  · intro l
    simp only []
    by_cases hl : l = 0
    · rw [ite_eq_left hl]
      exact hN 0 (Finset.mem_range.mpr (Nat.zero_lt_succ m))
    · rw [ite_eq_right hl, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  · rw [Finset.sum_eq_single 0]
    · simp only [ite_true, pow_zero, pow_one]
    · intro b _ hne
      simp only [ite_eq_right hne]
      rw [Polynomial.coe_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ m)) hcon

/-- `H` is finite. -/
private theorem chr_H_finite (N m : ℕ) (c : ℕ → Polynomial K)
    (f : PowerSeries K) (hc0 : c 0 ≠ 0) :
    Finite ↥(chr_H N m c f) := by
  classical
  have hex : ∀ h : ↥(chr_H N m c f), ∃ t : ℕ → Polynomial K,
      (∀ l, (t l).natDegree ≤ N) ∧ ((c 0 : Polynomial K) : PowerSeries K) * h
        = ∑ l ∈ Finset.range (m + 1), ((t l : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ l := fun h => h.2
  choose t ht_deg ht_eq using hex
  have hinj : Function.Injective (fun h : ↥(chr_H N m c f) =>
      fun (l : Fin (m + 1)) (i : Fin (N + 1)) => ((t h l.1).coeff i.1)) := by
    intro h₁ h₂ heq
    have htl : ∀ l (h : l < m + 1), t h₁ l = t h₂ l := by
      intro l h
      apply Polynomial.ext_iff.mpr
      intro n
      by_cases hn : n ≤ N
      · have h1 := congrFun (congrFun heq ⟨l, h⟩) ⟨n, by omega⟩
        exact h1
      · have hn' : N < n := not_le.mp hn
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (ht_deg h₁ l) hn'),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt (ht_deg h₂ l) hn')]
    have heq2 : ((c 0 : Polynomial K) : PowerSeries K) * h₁
        = ((c 0 : Polynomial K) : PowerSeries K) * h₂ := by
      rw [ht_eq h₁, ht_eq h₂]
      apply Finset.sum_congr rfl
      intro l hl
      have hll : t h₁ l = t h₂ l := htl l (Finset.mem_range.mp hl)
      rw [hll]
    have hc0ps : ((c 0 : Polynomial K) : PowerSeries K) ≠ 0 :=
      fun h => hc0 (Polynomial.coe_eq_zero_iff.mp h)
    have hval : (h₁ : PowerSeries K) = h₂ := by
      have hsub : ((c 0 : Polynomial K) : PowerSeries K) * (h₁ - h₂) = 0 := by
        rw [mul_sub, heq2, sub_self]
      rcases mul_eq_zero.mp hsub with h | h
      · exact absurd h hc0ps
      · exact sub_eq_zero.mp h
    exact Subtype.ext hval
  exact Finite.of_injective _ hinj

/-- `H` is stable under every `Λ_j`, `j < q`. -/
private theorem chr_H_lam_mem (hq2 : 2 ≤ Fintype.card K) (N m : ℕ)
    (c : ℕ → Polynomial K) (f : PowerSeries K)
    (hN : ∀ l ∈ Finset.range (m + 1), (c l).natDegree ≤ N)
    (hrel : ∑ l ∈ Finset.range (m + 1), ((c l : Polynomial K) : PowerSeries K)
      * f ^ Fintype.card K ^ l = 0)
    {h : PowerSeries K} (hh : h ∈ chr_H N m c f)
    {j : ℕ} (hj : j < Fintype.card K) :
    chr_lam (K := K) j h ∈ chr_H N m c f := by
  classical
  obtain ⟨t, ht_deg, ht_eq⟩ := hh
  have hq1 : 1 ≤ Fintype.card K := by omega
  obtain ⟨u, hu⟩ : ∃ u, Fintype.card K = u + 2 := ⟨Fintype.card K - 2, by omega⟩
  have hsub1 : Fintype.card K - 1 = u + 1 := by omega
  have hsub2 : Fintype.card K - 2 = u := by omega
  have hF0 : f ^ Fintype.card K ^ 0 = f := by simp
  have hmem0 : ((c 0 : Polynomial K) : PowerSeries K) * h
      = (∑ l ∈ Finset.range m, ((t (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1))
        + ((t 0 : Polynomial K) : PowerSeries K) * f := by
    have h2 := ht_eq
    rwa [Finset.sum_range_succ', hF0] at h2
  have hrel0 : (∑ l ∈ Finset.range m, ((c (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1))
        + ((c 0 : Polynomial K) : PowerSeries K) * f = 0 := by
    have h2 := hrel
    rwa [Finset.sum_range_succ', hF0] at h2
  have hS1 : (∑ l ∈ Finset.range m, ((t (l + 1) : Polynomial K) : PowerSeries K)
        * f ^ Fintype.card K ^ (l + 1))
      = ((c 0 : Polynomial K) : PowerSeries K) * h
        - ((t 0 : Polynomial K) : PowerSeries K) * f :=
    (sub_eq_iff_eq_add.mpr hmem0).symm
  have hS2 : (∑ l ∈ Finset.range m, ((c (l + 1) : Polynomial K) : PowerSeries K)
        * f ^ Fintype.card K ^ (l + 1))
      = -(((c 0 : Polynomial K) : PowerSeries K) * f) :=
    eq_neg_of_add_eq_zero_left hrel0
  have hpow : ∀ l : ℕ, f ^ Fintype.card K ^ (l + 1)
      = (f ^ Fintype.card K ^ l) ^ Fintype.card K := by
    intro l
    rw [pow_succ, pow_mul]
  have hterm : ∀ l : ℕ,
      ((c 0 ^ (Fintype.card K - 1) * t (l + 1)
        - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1) : Polynomial K)
        : PowerSeries K) * f ^ Fintype.card K ^ (l + 1)
      = ((c 0 : Polynomial K) : PowerSeries K) ^ (Fintype.card K - 1)
          * (((t (l + 1) : Polynomial K) : PowerSeries K)
            * f ^ Fintype.card K ^ (l + 1))
        - ((c 0 : Polynomial K) : PowerSeries K) ^ (Fintype.card K - 2)
          * ((t 0 : Polynomial K) : PowerSeries K)
          * (((c (l + 1) : Polynomial K) : PowerSeries K)
            * f ^ Fintype.card K ^ (l + 1)) := by
    intro l
    push_cast
    ring
  have hsum : (∑ l ∈ Finset.range m,
        ((c 0 ^ (Fintype.card K - 1) * t (l + 1)
          - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1) : Polynomial K)
          : PowerSeries K) * f ^ Fintype.card K ^ (l + 1))
      = ((c 0 : Polynomial K) : PowerSeries K) ^ (Fintype.card K - 1)
        * (∑ l ∈ Finset.range m, ((t (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1))
        - ((c 0 : Polynomial K) : PowerSeries K) ^ (Fintype.card K - 2)
        * ((t 0 : Polynomial K) : PowerSeries K)
        * (∑ l ∈ Finset.range m, ((c (l + 1) : Polynomial K) : PowerSeries K)
          * f ^ Fintype.card K ^ (l + 1)) := by
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hC0q : ((c 0 : Polynomial K) : PowerSeries K) ^ Fintype.card K
      = ((c 0 : Polynomial K) : PowerSeries K) ^ u
        * ((c 0 : Polynomial K) : PowerSeries K)
        * ((c 0 : Polynomial K) : PowerSeries K) := by
    rw [hu, pow_add]
    ring
  have hC0qm1 : ((c 0 : Polynomial K) : PowerSeries K) ^ (Fintype.card K - 1)
      = ((c 0 : Polynomial K) : PowerSeries K) ^ u
        * ((c 0 : Polynomial K) : PowerSeries K) := by
    rw [hsub1, pow_succ]
  have hkey : ((c 0 : Polynomial K) : PowerSeries K) ^ Fintype.card K * h
      = ∑ l ∈ Finset.range m,
        ((c 0 ^ (Fintype.card K - 1) * t (l + 1)
          - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1) : Polynomial K)
          : PowerSeries K) * f ^ Fintype.card K ^ (l + 1) := by
    rw [hsum, hS1, hS2, hC0q, hC0qm1, hsub2]
    ring
  have hLamL : chr_lam (K := K) j
        (((c 0 : Polynomial K) : PowerSeries K) ^ Fintype.card K * h)
      = chr_lam (K := K) j h * ((c 0 : Polynomial K) : PowerSeries K) := by
    rw [mul_comm (((c 0 : Polynomial K) : PowerSeries K) ^ Fintype.card K) h]
    exact chr_lam_mul_pow hj hq1 h ((c 0 : Polynomial K) : PowerSeries K)
  have htermL : ∀ l : ℕ, chr_lam (K := K) j
        (((c 0 ^ (Fintype.card K - 1) * t (l + 1)
          - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1) : Polynomial K)
          : PowerSeries K) * f ^ Fintype.card K ^ (l + 1))
      = ((chr_lamP (K := K) j (c 0 ^ (Fintype.card K - 1) * t (l + 1)
          - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1)) : Polynomial K)
          : PowerSeries K) * f ^ Fintype.card K ^ l := by
    intro l
    rw [hpow l, chr_lam_mul_pow hj hq1, ← chr_coe_lamP hq1]
  have hfinal : chr_lam (K := K) j h * ((c 0 : Polynomial K) : PowerSeries K)
      = ∑ l ∈ Finset.range m,
        ((chr_lamP (K := K) j (c 0 ^ (Fintype.card K - 1) * t (l + 1)
          - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1)) : Polynomial K)
          : PowerSeries K) * f ^ Fintype.card K ^ l := by
    have hLam := congrArg (chr_lam (K := K) j) hkey
    rw [map_sum, hLamL] at hLam
    exact hLam.trans (Finset.sum_congr rfl (fun l _ => htermL l))
  have hdeg : ∀ k ≤ m, (c 0 ^ (Fintype.card K - 1) * t k
      - c 0 ^ (Fintype.card K - 2) * t 0 * c k).natDegree
      ≤ Fintype.card K * N := by
    intro k hkm
    have hc0N : (c 0).natDegree ≤ N :=
      hN 0 (Finset.mem_range.mpr (Nat.zero_lt_succ m))
    have hckN : (c k).natDegree ≤ N :=
      hN k (Finset.mem_range.mpr (by omega))
    have hpow1 : (c 0 ^ (Fintype.card K - 1)).natDegree
        ≤ (Fintype.card K - 1) * N :=
      le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul le_rfl hc0N)
    have hpow2 : (c 0 ^ (Fintype.card K - 2)).natDegree
        ≤ (Fintype.card K - 2) * N :=
      le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul le_rfl hc0N)
    have hT1 : (c 0 ^ (Fintype.card K - 1) * t k).natDegree
        ≤ (Fintype.card K - 1) * N + N :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add hpow1 (ht_deg k))
    have hT2 : (c 0 ^ (Fintype.card K - 2) * t 0 * c k).natDegree
        ≤ (Fintype.card K - 2) * N + N + N := by
      refine le_trans Polynomial.natDegree_mul_le (Nat.add_le_add ?_ hckN)
      exact le_trans Polynomial.natDegree_mul_le
        (Nat.add_le_add hpow2 (ht_deg 0))
    have e1 : (Fintype.card K - 1) * N + N ≤ Fintype.card K * N :=
      le_of_eq (by
        calc (Fintype.card K - 1) * N + N = (Fintype.card K - 1 + 1) * N := by
                rw [add_mul, one_mul]
          _ = Fintype.card K * N := by rw [Nat.sub_add_cancel hq1])
    have e2 : (Fintype.card K - 2) * N + N + N ≤ Fintype.card K * N :=
      le_of_eq (by
        calc (Fintype.card K - 2) * N + N + N
              = (Fintype.card K - 2 + 2) * N := by
                rw [add_mul, two_mul]
                exact add_assoc _ _ _
          _ = Fintype.card K * N := by
                rw [show Fintype.card K - 2 + 2 = Fintype.card K by omega])
    exact le_trans (Polynomial.natDegree_sub_le _ _)
      (max_le (le_trans hT1 e1) (le_trans hT2 e2))
  set t' : ℕ → Polynomial K := fun l => if l < m then
    chr_lamP (K := K) j (c 0 ^ (Fintype.card K - 1) * t (l + 1)
      - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1)) else 0 with ht'def
  have htl : ∀ l, l < m → t' l = chr_lamP (K := K) j
      (c 0 ^ (Fintype.card K - 1) * t (l + 1)
        - c 0 ^ (Fintype.card K - 2) * t 0 * c (l + 1)) := by
    intro l hl
    rw [ht'def]
    exact ite_eq_left hl
  have htm : t' m = 0 := by
    rw [ht'def]
    exact ite_eq_right (lt_irrefl m)
  have hdeg_all : ∀ l, (t' l).natDegree ≤ N := by
    intro l
    by_cases hl : l < m
    · rw [htl l hl]
      exact chr_natDegree_lamP_le hq1 _ (hdeg (l + 1) (by omega))
    · have e0 : t' l = 0 := by
        rw [ht'def]
        exact ite_eq_right hl
      rw [e0, Polynomial.natDegree_zero]
      exact Nat.zero_le N
  refine ⟨t', hdeg_all, ?_⟩
  rw [mul_comm ((c 0 : Polynomial K) : PowerSeries K) (chr_lam (K := K) j h),
    hfinal, Finset.sum_range_succ, htm, Polynomial.coe_zero, zero_mul, add_zero]
  exact Finset.sum_congr rfl (fun l hl => by
    rw [htl l (Finset.mem_range.mp hl)])

/-- An algebraic series has finite `q`-kernel. -/
private theorem chr_kernel_finite_of_isAlgebraic (hq : 1 ≤ Fintype.card K)
    {f : PowerSeries K} (halg : IsAlgebraic (Polynomial K) f) :
    Finite ↥(kKernel (Fintype.card K)
      (fun n => PowerSeries.coeff n f)) := by
  classical
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨m, c, hne, hrel⟩ := chr_ore halg
  obtain ⟨c', hc0', hrel'⟩ := chr_ore_zero hq m f c hne hrel
  set N := (Finset.range (m + 1)).sup (fun l => (c' l).natDegree)
  have hN : ∀ l ∈ Finset.range (m + 1), (c' l).natDegree ≤ N :=
    fun l hl => Finset.le_sup (f := fun l => (c' l).natDegree) hl
  have hHfin : Finite ↥(chr_H N m c' f) := chr_H_finite N m c' f hc0'
  have hmem : ∀ (e R : ℕ), R < Fintype.card K ^ e →
      PowerSeries.mk (fun n => PowerSeries.coeff (Fintype.card K ^ e * n + R) f)
        ∈ chr_H N m c' f := by
    intro e
    induction e with
    | zero =>
      intro R hR
      have hR0 : R = 0 := by simpa using hR
      subst hR0
      have hmk : PowerSeries.mk
          (fun n => PowerSeries.coeff (Fintype.card K ^ 0 * n + 0) f) = f := by
        apply PowerSeries.ext
        intro n
        simp
      rw [hmk]
      exact chr_mem_H N m c' f hN
    | succ e ih =>
      intro R hR
      have hpos : 0 < Fintype.card K ^ e := pow_pos (by omega) e
      have hR₁q : R / Fintype.card K ^ e < Fintype.card K := by
        have heq : Fintype.card K ^ (e + 1)
            = Fintype.card K * Fintype.card K ^ e := pow_succ' _ _
        rw [heq] at hR
        exact (Nat.div_lt_iff_lt_mul hpos).mpr hR
      have hres : ∀ n : ℕ, Fintype.card K ^ e
            * (Fintype.card K * n + R / Fintype.card K ^ e)
            + R % Fintype.card K ^ e
          = Fintype.card K ^ (e + 1) * n + R := by
        intro n
        have hdiv := Nat.div_add_mod R (Fintype.card K ^ e)
        have heq : Fintype.card K ^ (e + 1)
            = Fintype.card K ^ e * Fintype.card K := pow_succ _ _
        rw [heq, mul_add, add_assoc, hdiv, mul_assoc]
      have hseries : PowerSeries.mk (fun n => PowerSeries.coeff
          (Fintype.card K ^ (e + 1) * n + R) f)
          = chr_lam (K := K) (R / Fintype.card K ^ e)
            (PowerSeries.mk (fun n => PowerSeries.coeff
              (Fintype.card K ^ e * n + R % Fintype.card K ^ e) f)) := by
        apply PowerSeries.ext
        intro n
        simp only [chr_lam_coeff, PowerSeries.coeff_mk]
        rw [hres n]
      rw [hseries]
      exact chr_H_lam_mem hq2 N m c' f hN hrel'
        (ih (R % Fintype.card K ^ e) (Nat.mod_lt R hpos)) hR₁q
  rw [Set.finite_coe_iff]
  refine Set.Finite.subset (Set.finite_range
    (fun h : ↥(chr_H N m c' f) => fun n => PowerSeries.coeff n (h : PowerSeries K))) ?_
  intro b hb
  obtain ⟨e, R, hR, rfl⟩ := hb
  refine ⟨⟨PowerSeries.mk _, hmem e R hR⟩, funext fun n => ?_⟩
  change PowerSeries.coeff n
      (PowerSeries.mk (fun m => PowerSeries.coeff (Fintype.card K ^ e * m + R) f))
    = PowerSeries.coeff (Fintype.card K ^ e * n + R) f
  exact PowerSeries.coeff_mk n _

end ChrMain

/-- **Christol's theorem.** Let $p$ be a prime, $r \ge 1$ a natural number, and $K$ a finite field
of characteristic $p$ with $q = p^r$ elements. A formal power series
$f = \sum_n f_n X^n \in K[[X]]$ is algebraic over the polynomial ring $K[X]$ (it is a root of a
nonzero polynomial with coefficients in $K[X]$) if and only if its coefficient sequence
$n \mapsto f_n$ is $p$-automatic, that is, its $p$-kernel is finite.

Algebraicity over $K[X]$ is the denominator-cleared form of algebraicity over the rational
function field $K(X)$; it is not integrality over $K[X]$. Automaticity is taken in base $p$, not
in base $q$.

Proves `Wanted` entry `christol_theorem`.

Source: Adamczewski--Bell, arXiv:1205.4091v1, lines 260--265:
for `q` a positive integral power of the characteristic prime `p`, a series
over `F_q` is algebraic over `F_q(t)` iff its coefficient sequence is
`p`-automatic. -/
public theorem christol_theorem (K : Type*) [Field K] [Finite K] (p q r : ℕ)
    [CharP K p] (hp : Nat.Prime p) (hcard : Nat.card K = q) (hq : q = p ^ r)
    (hr : 0 < r) (f : PowerSeries K) :
    IsAlgebraic (Polynomial K) f ↔ IsKAutomatic p (fun n => PowerSeries.coeff n f) := by
  have hFin : Fintype K := Fintype.ofFinite K
  have hp0 : 0 < p := hp.pos
  have hqcard : Fintype.card K = q := by rw [Fintype.card_eq_nat_card, hcard]
  have hpr : Fintype.card K = p ^ r := by rw [hqcard, hq]
  have hqpos : 0 < q := by rw [hq]; exact pow_pos hp.pos r
  have hq1 : 1 ≤ Fintype.card K := by rw [hqcard]; omega
  constructor
  · intro halg
    have hfinqr : Finite ↥(kKernel (p ^ r) (fun n => PowerSeries.coeff n f)) := by
      rw [← hpr]
      exact chr_kernel_finite_of_isAlgebraic hq1 halg
    have hfinp := chr_pkernel_finite hr hp0 (fun n => PowerSeries.coeff n f)
    exact ⟨hp.two_le, hfinp⟩
  · intro hauto
    obtain ⟨_, hfinp⟩ := hauto
    have hfinq : Finite ↥(kKernel (Fintype.card K)
        (fun n => PowerSeries.coeff n f)) := by
      rw [hpr, Set.finite_coe_iff]
      exact (Set.finite_coe_iff.mp hfinp).subset (chr_qkernel_subset _)
    exact chr_isAlgebraic_of_finite_kernel hq1 hfinq

section ChrAuto

variable {B : Type*}

/-- **Christol's theorem, automaton form.** Let $p$ be a prime, $r \ge 1$ a natural number, and
$K$ a finite field of characteristic $p$ with $q = p^r$ elements. A formal power series
$f = \sum_n f_n X^n \in K[[X]]$ is algebraic over the polynomial ring $K[X]$ (it is a root of a
nonzero polynomial with coefficients in $K[X]$) if and only if its coefficient sequence
$n \mapsto f_n$ is $p$-automatic in the sense of finite automata with output. -/
public theorem christol_theorem_isKAutomaticSequence (K : Type) [Field K] [Fintype K]
    (p q r : ℕ) [CharP K p] (hp : Nat.Prime p) (hcard : Nat.card K = q)
    (hq : q = p ^ r) (hr : 0 < r) (f : PowerSeries K) :
    IsAlgebraic (Polynomial K) f
      ↔ IsKAutomaticSequence p (fun n => PowerSeries.coeff n f) := by
  exact (christol_theorem K p q r hp hcard hq hr f).trans
    (isKAutomatic_iff_isKAutomaticSequence p _)

end ChrAuto

end

end MetaMathlibExt
