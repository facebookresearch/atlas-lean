/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.FieldTheory.TsenWanted

universe u v w

private theorem MvPolynomial_natCast_le_height_of_isMaximal_fin (k : Type u) [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsMaximal] : (n : ℕ∞) ≤ P.height := by
  induction n using Nat.rec with
  | zero =>
    simp
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv k n
    let P' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := Ideal.map e.toRingEquiv P
    have hP'max : P'.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have hheight : P'.height = P.height := RingEquiv.height_map e.toRingEquiv P
    have hp_eq : Ideal.under (MvPolynomial (Fin n) k) P' = Ideal.comap Polynomial.C P' := by
      rw [Ideal.under_def, Polynomial.algebraMap_eq]
    have hpmax : (Ideal.under (MvPolynomial (Fin n) k) P').IsMaximal := by
      rw [hp_eq]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing P'
    have hlie : P'.LiesOver (Ideal.under (MvPolynomial (Fin n) k) P') := Ideal.over_under P'
    have heq : P'.height = (Ideal.under (MvPolynomial (Fin n) k) P').height + 1 :=
      Polynomial.height_eq_height_add_one _ P'
    have hle : (n : ℕ∞) ≤ (Ideal.under (MvPolynomial (Fin n) k) P').height :=
      @ih _ hpmax
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; ring
      _ ≤ (Ideal.under (MvPolynomial (Fin n) k) P').height + 1 := by gcongr
      _ = P'.height := heq.symm
      _ = P.height := hheight

private theorem MvPolynomial_card_le_height_of_isMaximal (k : Type u) [Field k] (σ : Type v)
    [Fintype σ] (J : Ideal (MvPolynomial σ k)) [J.IsMaximal] :
    (Fintype.card σ : ℕ∞) ≤ J.height := by
  let e := MvPolynomial.renameEquiv k (Fintype.equivFin σ)
  let J' : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) := Ideal.map e.toRingEquiv J
  have hJ'max : J'.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
  have hheight : J'.height = J.height := RingEquiv.height_map e.toRingEquiv J
  have hle : ((Fintype.card σ : ℕ) : ℕ∞) ≤ J'.height :=
    MvPolynomial_natCast_le_height_of_isMaximal_fin k _ J'
  rwa [hheight] at hle

private theorem Ideal_exists_isMaximal_ne_of_not_isMaximal (R : Type u) [CommRing R]
    [IsJacobsonRing R] (P : Ideal R) [P.IsPrime] (hP : ¬ P.IsMaximal)
    (M0 : Ideal R) [M0.IsMaximal] : ∃ J : Ideal R, P ≤ J ∧ J.IsMaximal ∧ J ≠ M0 := by
  by_contra h
  have hall : ∀ J : Ideal R, P ≤ J → J.IsMaximal → J = M0 := by
    intro J hle hm
    by_contra hne
    exact h ⟨J, hle, hm, hne⟩
  have hjac : P.jacobson = P :=
    (isJacobsonRing_iff_prime_eq.mp inferInstance) P inferInstance
  have hle : M0 ≤ P.jacobson := by
    change M0 ≤ sInf {J | P ≤ J ∧ J.IsMaximal}
    apply le_sInf
    intro J hJ
    obtain ⟨hPJ, hJmax⟩ := hJ
    rw [hall J hPJ hJmax]
  rw [hjac] at hle
  have hPne : P ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have heq : M0 = P := Ideal.IsMaximal.eq_of_le inferInstance hPne hle
  have hPmax : P.IsMaximal := heq ▸ inferInstance
  exact hP hPmax

private theorem MvPolynomial_exists_ne_zero_forall_eval_eq_zero_of_card_lt
    (k : Type u) [Field k] [IsAlgClosed k] (σ : Type v) (ι : Type w)
    [Fintype σ] [Fintype ι] (F : ι → MvPolynomial σ k)
    (hF : ∀ i, MvPolynomial.constantCoeff (F i) = 0)
    (hlt : Fintype.card ι < Fintype.card σ) :
    ∃ a : σ → k, a ≠ 0 ∧ ∀ i, MvPolynomial.eval a (F i) = 0 := by
  classical
  let s : Finset (MvPolynomial σ k) := Finset.univ.image F
  let I : Ideal (MvPolynomial σ k) := Ideal.span (↑s : Set (MvPolynomial σ k))
  let M0 : Ideal (MvPolynomial σ k) := MvPolynomial.vanishingIdeal k ({0} : Set (σ → k))
  have hM0max : M0.IsMaximal := by
    rw [MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton]
    exact ⟨0, rfl⟩
  have := hM0max
  have hmem : ∀ i, F i ∈ M0 := by
    intro i
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    have h1 : (MvPolynomial.aeval (0 : σ → k)) (F i) = MvPolynomial.eval 0 (F i) := by
      rw [← MvPolynomial.coe_aeval_eq_eval]
      rfl
    rw [h1, MvPolynomial.eval_zero]
    exact hF i
  have hI_le : I ≤ M0 := by
    rw [Ideal.span_le]
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    exact hmem i
  have hIne : I ≠ ⊤ := by
    intro htop
    rw [htop] at hI_le
    have htop2 : M0 = ⊤ := top_le_iff.mp hI_le
    exact hM0max.ne_top htop2
  obtain ⟨P, hPmem⟩ := Ideal.nonempty_minimalPrimes hIne
  have hPprime : P.IsPrime := Ideal.IsMinimalPrime.isPrime hPmem
  have := hPprime
  have hheight : P.height ≤ (s.card : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hPmem
  have hcard : s.card ≤ Fintype.card ι := by
    calc s.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card ι := Finset.card_univ
  have hPnotmax : ¬ P.IsMaximal := by
    intro hmax
    have := hmax
    have hN2 : (Fintype.card σ : ℕ∞) ≤ P.height :=
      MvPolynomial_card_le_height_of_isMaximal k σ P
    have hle : (Fintype.card σ : ℕ∞) ≤ (Fintype.card ι : ℕ∞) := by
      calc (Fintype.card σ : ℕ∞) ≤ P.height := hN2
        _ ≤ (s.card : ℕ∞) := hheight
        _ ≤ (Fintype.card ι : ℕ∞) := by exact_mod_cast hcard
    have hlt' : (Fintype.card ι : ℕ∞) < (Fintype.card σ : ℕ∞) :=
      ENat.natCast_lt_natCast.mpr hlt
    exact (not_lt_of_ge hle) hlt'
  obtain ⟨J, hPJ, hJmax, hJne⟩ :=
    Ideal_exists_isMaximal_ne_of_not_isMaximal _ P hPnotmax M0
  obtain ⟨a, ha⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hJmax)
  have hane : a ≠ 0 := by
    intro hzero
    apply hJne
    rw [ha, hzero]
  refine ⟨a, hane, fun i => ?_⟩
  have hFi : F i ∈ J := by
    apply hPJ
    apply Ideal.IsMinimalPrime.le hPmem
    apply Ideal.subset_span
    show F i ∈ (↑s : Set (MvPolynomial σ k))
    rw [Finset.coe_image, Finset.coe_univ]
    exact Set.mem_image_of_mem F (Set.mem_univ i)
  rw [ha] at hFi
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hFi
  have h2 : MvPolynomial.eval a (F i) = (MvPolynomial.aeval a) (F i) := by
    rw [← MvPolynomial.coe_aeval_eq_eval]
    rfl
  rw [h2]
  exact hFi

private theorem MvPolynomial_exists_isHomogeneous_map_eq_C_mul
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (σ : Type w) (d : ℕ) (f : MvPolynomial σ K)
    (hf : f.IsHomogeneous d) :
    ∃ (c : K) (g : MvPolynomial σ A), c ≠ 0 ∧ g.IsHomogeneous d ∧
      MvPolynomial.map (algebraMap A K) g = MvPolynomial.C c * f := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors A) (f.coeffs)
  set c : K := algebraMap A K (b : A) with hc
  have hcne : c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hsub : (↑(MvPolynomial.C c * f).coeffs : Set K) ⊆ Set.range (⇑(algebraMap A K)) := by
    intro y hy
    have hy2 : y ∈ (MvPolynomial.C c * f).coeffs := Finset.mem_coe.mp hy
    rw [MvPolynomial.mem_coeffs_iff] at hy2
    obtain ⟨s, hs, rfl⟩ := hy2
    rw [MvPolynomial.coeff_C_mul]
    have hsne : (MvPolynomial.C c * f).coeff s ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hs
    rw [MvPolynomial.coeff_C_mul] at hsne
    have hfsne : f.coeff s ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hsne
      exact hsne rfl
    have hmem : f.coeff s ∈ f.coeffs := MvPolynomial.coeff_mem_coeffs s hfsne
    have hint := hb (f.coeff s) hmem
    obtain ⟨y0, hy0⟩ := hint
    refine ⟨y0, ?_⟩
    rw [Algebra.smul_def] at hy0
    rw [hc]
    exact hy0
  rw [← MvPolynomial.mem_range_map_iff_coeffs_subset] at hsub
  obtain ⟨g, hg⟩ := hsub
  refine ⟨c, g, hcne, ?_, hg⟩
  have hhom : (MvPolynomial.C c * f).IsHomogeneous d := hf.C_mul c
  rw [← hg] at hhom
  exact MvPolynomial.IsHomogeneous.of_map (IsFractionRing.injective A K) hhom

private noncomputable def tsenGen (k : Type u) [Field k] (n N : ℕ) (i : Fin n) :
    Polynomial (MvPolynomial (Fin n × Fin (N + 1)) k) :=
  Finset.sum Finset.univ (fun j : Fin (N + 1) =>
    Polynomial.C (MvPolynomial.X (i, j)) * Polynomial.X ^ (j.val))

private noncomputable def tsenGeneric (k : Type u) [Field k] (n N : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) :
    Polynomial (MvPolynomial (Fin n × Fin (N + 1)) k) :=
  MvPolynomial.eval₂
    (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k))
    (tsenGen k n N) g

private theorem tsenGen_natDegree_le (k : Type u) [Field k] (n N : ℕ) (i : Fin n) :
    (tsenGen k n N i).natDegree ≤ N := by
  unfold tsenGen
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  calc (Polynomial.C (MvPolynomial.X (i, j)) *
      (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin (N+1)) k)) ^ (j.val)).natDegree
      ≤ (j.val) := Polynomial.natDegree_C_mul_X_pow_le _ _
    _ ≤ N := Fin.is_le j

private theorem tsenGeneric_natDegree_le (k : Type u) [Field k] (n N m d : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) (hg : g.IsHomogeneous d)
    (hm : ∀ s, (g.coeff s).natDegree ≤ m) :
    (tsenGeneric k n N g).natDegree ≤ d * N + m := by
  unfold tsenGeneric
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have hdeg : Finsupp.degree s = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hs) (hg.coeff_eq_zero hne)
  have hmap : ((Polynomial.mapRingHom
      (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k))
      (g.coeff s)).natDegree ≤ m := by
    rw [Polynomial.coe_mapRingHom]
    calc (Polynomial.map
        (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k)
        (g.coeff s)).natDegree
        ≤ (g.coeff s).natDegree := Polynomial.natDegree_map_le
      _ ≤ m := hm s
  have hprod : (∏ i, tsenGen k n N i ^ s i).natDegree ≤ d * N := by
    calc (∏ i, tsenGen k n N i ^ s i).natDegree
        ≤ ∑ i, (tsenGen k n N i ^ s i).natDegree :=
          Polynomial.natDegree_prod_le Finset.univ _
      _ ≤ ∑ i, s i * N := by
          apply Finset.sum_le_sum
          intro i _
          exact Polynomial.natDegree_pow_le_of_le _ (tsenGen_natDegree_le k n N i)
      _ = (∑ i, s i) * N := by rw [Finset.sum_mul]
      _ = d * N := by rw [← Finsupp.degree_eq_sum, hdeg]
  calc (((Polynomial.mapRingHom
        (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k))
        (g.coeff s)) *
      ∏ i, tsenGen k n N i ^ s i).natDegree
      ≤ m + d * N := Polynomial.natDegree_mul_le_of_le hmap hprod
    _ = d * N + m := by ring

private noncomputable def tsenSpec (k : Type u) [Field k] (n N : ℕ)
    (a : Fin n × Fin (N + 1) → k) (i : Fin n) : Polynomial k :=
  Finset.sum Finset.univ (fun j : Fin (N + 1) =>
    Polynomial.C (a (i, j)) * Polynomial.X ^ (j.val))

private theorem tsenGeneric_map_eval (k : Type u) [Field k] (n N : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) (a : Fin n × Fin (N + 1) → k) :
    Polynomial.map (MvPolynomial.eval a) (tsenGeneric k n N g) =
      MvPolynomial.eval (tsenSpec k n N a) g := by
  unfold tsenGeneric
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have hcomp : ((Polynomial.mapRingHom (MvPolynomial.eval a)).comp
      (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k)))
      = RingHom.id (Polynomial k) := by
    rw [Polynomial.mapRingHom_comp]
    have hid : ((MvPolynomial.eval a).comp
        (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (N + 1)) k)) = RingHom.id k := by
      apply RingHom.ext
      intro x
      simp [MvPolynomial.eval_C]
    rw [hid, Polynomial.mapRingHom_id]
  rw [hcomp, MvPolynomial.eval₂_id]
  have hpt : (⇑(Polynomial.mapRingHom (MvPolynomial.eval a)) ∘ tsenGen k n N)
      = tsenSpec k n N a := by
    funext i
    change ((Polynomial.mapRingHom (MvPolynomial.eval a)) ((tsenGen k n N) i)) = _
    unfold tsenGen tsenSpec
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sum]
    congr 1
    funext j
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      MvPolynomial.eval_X]
  rw [hpt]

private theorem tsenGeneric_constantCoeff_coeff (k : Type u) [Field k] (n : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) (d : ℕ) (hg : g.IsHomogeneous d)
    (hd : 0 < d) (N l : ℕ) :
    MvPolynomial.constantCoeff ((tsenGeneric k n N g).coeff l) = 0 := by
  have hspec : tsenSpec k n N (0 : Fin n × Fin (N + 1) → k) = 0 := by
    funext i
    unfold tsenSpec
    simp
  have h1 : MvPolynomial.constantCoeff ((tsenGeneric k n N g).coeff l) =
      MvPolynomial.eval (0 : Fin n × Fin (N + 1) → k) ((tsenGeneric k n N g).coeff l) := by
    rw [MvPolynomial.eval_zero]
  rw [h1, ← Polynomial.coeff_map, tsenGeneric_map_eval, hspec]
  have heval : MvPolynomial.eval (0 : Fin n → Polynomial k) g = 0 := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    apply hg.coeff_eq_zero
    rw [map_zero]
    exact ne_of_lt hd
  rw [heval, Polynomial.coeff_zero]

private theorem tsenSpec_ne_zero (k : Type u) [Field k] (n N : ℕ)
    (a : Fin n × Fin (N + 1) → k) (ha : a ≠ 0) :
    ∃ i, tsenSpec k n N a i ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp ha
  obtain ⟨i, j⟩ := p
  simp only [ne_eq] at hp
  refine ⟨i, ?_⟩
  intro hzero
  apply hp
  have hcoeff : (tsenSpec k n N a i).coeff (j.val) = a (i, j) := by
    unfold tsenSpec
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    have hcond : ∀ j' : Fin (N + 1), ((j.val = j'.val) ↔ (j' = j)) := by
      intro j'
      constructor
      · intro h
        exact Fin.val_injective h.symm
      · intro h
        rw [h]
    simp only [hcond]
    rw [Finset.sum_ite_eq']
    simp
  rw [hzero] at hcoeff
  simp at hcoeff
  exact hcoeff.symm

private theorem tsen_polynomial (k : Type u) [Field k] [IsAlgClosed k] (n d : ℕ)
    (g : MvPolynomial (Fin n) (Polynomial k)) (hg : g.IsHomogeneous d)
    (hd0 : 0 < d) (hdn : d < n) :
    ∃ x : Fin n → Polynomial k, (∃ i, x i ≠ 0) ∧ MvPolynomial.eval x g = 0 := by
  classical
  let m : ℕ := Finset.sup (α := ℕ) g.support (fun s => (g.coeff s).natDegree)
  have hm : ∀ s, (g.coeff s).natDegree ≤ m := by
    intro s
    by_cases hs : s ∈ g.support
    · change (g.coeff s).natDegree ≤ Finset.sup (α := ℕ) g.support (fun s => (g.coeff s).natDegree)
      exact Finset.le_sup (f := fun s => (g.coeff s).natDegree) hs
    · rw [MvPolynomial.notMem_support_iff.mp hs, Polynomial.natDegree_zero]
      exact Nat.zero_le _
  have hcard_lt : Fintype.card (Fin (d * m + m + 1)) < Fintype.card (Fin n × Fin (m + 1)) := by
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have hdn1 : d + 1 ≤ n := hdn
    have hd1 : 1 ≤ d := hd0
    nlinarith
  let F : Fin (d * m + m + 1) → MvPolynomial (Fin n × Fin (m + 1)) k :=
    fun l => (tsenGeneric k n m g).coeff (l.val)
  have hF : ∀ l, MvPolynomial.constantCoeff (F l) = 0 := by
    intro l
    exact tsenGeneric_constantCoeff_coeff k n g d hg hd0 m (l.val)
  obtain ⟨a, hane, ha0⟩ :=
    MvPolynomial_exists_ne_zero_forall_eval_eq_zero_of_card_lt k _ _ F hF hcard_lt
  have hdeg : (tsenGeneric k n m g).natDegree ≤ d * m + m :=
    tsenGeneric_natDegree_le k n m m d g hg hm
  have hmap0 : Polynomial.map (MvPolynomial.eval a) (tsenGeneric k n m g) = 0 := by
    apply Polynomial.ext
    intro l
    rw [Polynomial.coeff_map]
    by_cases hl : l < d * m + m + 1
    · have hFl : (tsenGeneric k n m g).coeff l = F ⟨l, hl⟩ := rfl
      rw [hFl]
      exact ha0 ⟨l, hl⟩
    · have hlt : (tsenGeneric k n m g).natDegree < l := by omega
      have hcoeff : (tsenGeneric k n m g).coeff l = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [hcoeff, map_zero, Polynomial.coeff_zero]
  have heval : MvPolynomial.eval (tsenSpec k n m a) g = 0 := by
    rw [← tsenGeneric_map_eval, hmap0]
  obtain ⟨i, hi⟩ := tsenSpec_ne_zero k n m a hane
  exact ⟨tsenSpec k n m a, ⟨i, hi⟩, heval⟩

/-!
# Tsen's theorem for `k(X)`
This module proves the rational-function-field case of Tsen's theorem: `k(X)` is `C₁` for
algebraically closed `k`.
-/

/--
**Tsen's theorem.** Let $k$ be an algebraically closed field and $k(X)$ the field of rational
functions over $k$. For all natural numbers $n$ and $d$ with $0 < d < n$, every homogeneous
polynomial $f$ of degree $d$ in $n$ variables over $k(X)$ has a nontrivial zero: there is
$x = (x_1, \dots, x_n) \in k(X)^n$ with $x_i \neq 0$ for some $i$ and $f(x) = 0$. In other
words, $k(X)$ is a $C_1$ field.

Proves `Wanted` entry `tsen`.

Source: C. Tsen, Divisionsalgebren über Funktionenkörpern, Nachr. Ges. Wiss. Göttingen
1933 335–339; reformulated by C. Chevalley and Lang; textbook in Lang, Algebra, rev 3rd ed.
-/
theorem tsen :
    ∀ (k : Type*) [Field k] [IsAlgClosed k] (n d : ℕ)
      (f : MvPolynomial (Fin n) (RatFunc k)),
      f.IsHomogeneous d → 0 < d → d < n →
        ∃ (x : Fin n → RatFunc k), (∃ i, x i ≠ 0) ∧ MvPolynomial.eval x f = 0 := by
  intro k _ _ n d f hf hd0 hdn
  obtain ⟨c, g, hcne, hg, hmap⟩ :=
    MvPolynomial_exists_isHomogeneous_map_eq_C_mul (Polynomial k) (RatFunc k) (Fin n) d f hf
  obtain ⟨x, ⟨i, hi⟩, hx0⟩ := tsen_polynomial k n d g hg hd0 hdn
  refine ⟨fun i => algebraMap (Polynomial k) (RatFunc k) (x i), ⟨i, ?_⟩, ?_⟩
  · exact (map_ne_zero_iff (algebraMap (Polynomial k) (RatFunc k))
      (RatFunc.algebraMap_injective k)).mpr hi
  · have hq : algebraMap (Polynomial k) (RatFunc k) (MvPolynomial.eval x g) =
        MvPolynomial.eval (fun i => algebraMap (Polynomial k) (RatFunc k) (x i))
          (MvPolynomial.map (algebraMap (Polynomial k) (RatFunc k)) g) :=
      MvPolynomial.map_eval _ _ _
    rw [hx0, map_zero, hmap, map_mul, MvPolynomial.eval_C] at hq
    rcases mul_eq_zero.mp hq.symm with h | h
    · exact absurd h hcne
    · exact h

end MathlibExt.FieldTheory.TsenWanted
end
