/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Algebra.Algebra.AmitsurLevitzkiWanted

private theorem al_matrix_map_smul_mul {R : Type*} {G : Type*} [CommRing R] [Semiring G]
    [Algebra R G]
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (g h : G) :
    (A.map (fun r => r • g)) * (B.map (fun r => r • h))
      = (A * B).map (fun r => r • (g * h)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro c _
  exact smul_mul_smul_comm _ _ _ _

private theorem al_map_one_smul_one {R : Type*} {G : Type*} [CommRing R] [Ring G] [Algebra R G]
    {n : ℕ} [DecidableEq (Fin n)] :
    ((1 : Matrix (Fin n) (Fin n) R).map (fun r => r • (1 : G))) = 1 := by
  apply Matrix.map_one
  · simp
  · simp

private theorem al_sum_map_smul_pow {R : Type*} {G : Type*} {ι : Type*} [CommRing R] [Ring G]
    [Algebra R G] [Fintype ι] {n : ℕ} [DecidableEq (Fin n)]
    (A : ι → Matrix (Fin n) (Fin n) R) (g : ι → G) (m : ℕ) :
    (∑ i, (A i).map (fun r => r • g i)) ^ m
      = ∑ f : Fin m → ι, (((List.ofFn fun k => A (f k)).prod).map
        (fun r => r • (List.ofFn fun k => g (f k)).prod)) := by
  classical
  induction m with
  | zero =>
    rw [pow_zero, Fintype.sum_unique]
    have h1 : (List.ofFn fun k : Fin 0 => A ((default : Fin 0 → ι) k)).prod
        = (1 : Matrix (Fin n) (Fin n) R) := by simp
    have h2 : (List.ofFn fun k : Fin 0 => g ((default : Fin 0 → ι) k)).prod = (1 : G) := by simp
    rw [h1, h2]
    exact al_map_one_smul_one.symm
  | succ m ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp only [Finset.mul_sum]
    have hre : (∑ x : ι, ∑ i : Fin m → ι, ((A x).map (fun r => r • g x)) *
        (((List.ofFn fun k => A (i k)).prod).map
          (fun r => r • (List.ofFn fun k => g (i k)).prod)))
        = ∑ p : ι × (Fin m → ι), ((A p.1).map (fun r => r • g p.1)) *
        (((List.ofFn fun k => A (p.2 k)).prod).map
          (fun r => r • (List.ofFn fun k => g (p.2 k)).prod)) := by
      exact (Fintype.sum_prod_type (fun p : ι × (Fin m → ι) => ((A p.1).map (fun r => r • g p.1)) *
        (((List.ofFn fun k => A (p.2 k)).prod).map
          (fun r => r • (List.ofFn fun k => g (p.2 k)).prod)))).symm
    rw [hre]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι)) _ _ ?_
    intro p
    obtain ⟨i, f⟩ := p
    simp only [Fin.consEquiv_apply]
    have hA : (List.ofFn fun k : Fin (m + 1) =>
          A (Fin.cons (α := fun _ : Fin (m + 1) => ι) i f k)).prod
        = A i * (List.ofFn fun k : Fin m => A (f k)).prod := by
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [List.prod_cons]
    have hg : (List.ofFn fun k : Fin (m + 1) =>
          g (Fin.cons (α := fun _ : Fin (m + 1) => ι) i f k)).prod
        = g i * (List.ofFn fun k : Fin m => g (f k)).prod := by
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [List.prod_cons]
    rw [hA, hg, ← al_matrix_map_smul_mul]

private theorem al_grassmann_pow_expansion {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (m : ℕ) :
    (∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ m
    = ∑ f : Fin m → Fin (2 * n),
      (((List.ofFn fun k => M (f k)).prod).map
        (fun r => r • (ExteriorAlgebra.ιMulti R m)
          ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) ∘ f))) := by
  rw [al_sum_map_smul_pow]
  apply Finset.sum_congr rfl
  intro f _
  have h : (List.ofFn fun k =>
      (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) (f k))
          :
        ExteriorAlgebra R (Fin (2 * n) → R))).prod
      = (ExteriorAlgebra.ιMulti R m)
        ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) ∘ f) := by
    rw [ExteriorAlgebra.ιMulti_apply]
    simp only [Function.comp_apply]
  rw [h]

private theorem al_grassmann_pow_eq_zero {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (m : ℕ) (hm : 2 * n < m) :
    (∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ m = 0 := by
  rw [al_grassmann_pow_expansion]
  apply Finset.sum_eq_zero
  intro f _
  have hnot : ¬ Function.Injective f := by
    intro hinj
    have hle := Fintype.card_le_of_injective f hinj
    simp [Fintype.card_fin] at hle
    omega
  rw [Function.Injective] at hnot
  push Not at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  have hnot2 : ¬ Function.Injective
      ((fun i : Fin (2 * n) => (Pi.single i (1 : R) : Fin (2 * n) → R)) ∘ f) := by
    intro hinj2
    apply hne
    apply hinj2
    simp only [Function.comp_apply]
    rw [hab]
  have hzero : (ExteriorAlgebra.ιMulti R m)
      ((fun i : Fin (2 * n) => (Pi.single i (1 : R) : Fin (2 * n) → R)) ∘ f) = 0 :=
    AlternatingMap.map_eq_zero_of_not_injective _ _ hnot2
  rw [hzero]
  ext a1 b1
  simp [Matrix.map_apply]

private theorem al_sign_smul_comm {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (r : R) (ω : ExteriorAlgebra R V) (u : ℤˣ) :
    r • ((u : ℤ) • ω) = (((u : ℤ) • r)) • ω := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp

-- N4
private theorem al_grassmann_pow_top {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
    (∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * n)
    = ((∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod).map
        (fun r => r • (ExteriorAlgebra.ιMulti R (2 * n))
          (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)))) := by
  rw [al_grassmann_pow_expansion]
  set vv : Fin (2 * n) → (Fin (2 * n) → R) :=
    (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) with hvv
  set ω := (ExteriorAlgebra.ιMulti R (2 * n)) vv with hω
  set T : (Fin (2 * n) → Fin (2 * n)) → Matrix (Fin n) (Fin n)
      (ExteriorAlgebra R (Fin (2 * n) → R)) :=
    fun f => (((List.ofFn fun k => M (f k)).prod).map
      (fun r => r • (ExteriorAlgebra.ιMulti R (2 * n)) (vv ∘ f))) with hT
  set S : Equiv.Perm (Fin (2 * n)) → Matrix (Fin n) (Fin n)
      (ExteriorAlgebra R (Fin (2 * n) → R)) :=
    fun σ => ((((σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod)).map
      (fun r => r • ω)) with hS
  have hTS : ∀ σ : Equiv.Perm (Fin (2 * n)), T (⇑σ) = S σ := by
    intro σ
    simp only [hT, hS, hω]
    have hperm : (ExteriorAlgebra.ιMulti R (2 * n)) (vv ∘ ⇑σ)
        = σ.sign • (ExteriorAlgebra.ιMulti R (2 * n)) vv :=
      AlternatingMap.map_perm _ vv σ
    rw [hperm, Units.smul_def]
    ext a b
    simp only [Matrix.map_apply]
    exact al_sign_smul_comm _ _ _
  -- vanishing of non-injective terms
  have hvan : ∀ f ∈ (Finset.univ : Finset (Fin (2 * n) → Fin (2 * n))),
      f ∉ Finset.map
        (⟨fun σ : Equiv.Perm (Fin (2 * n)) => (⇑σ : Fin (2 * n) → Fin (2 * n)),
          DFunLike.coe_injective⟩ : Equiv.Perm (Fin (2 * n)) ↪ (Fin (2 * n) → Fin (2 * n)))
        Finset.univ → T f = 0 := by
    intro f _ hf
    simp only [hT]
    have hnot : ¬ Function.Injective f := by
      intro hinj
      apply hf
      have hbij : Function.Bijective f := (Finite.injective_iff_bijective).mp hinj
      exact Finset.mem_map.mpr ⟨Equiv.ofBijective f hbij, Finset.mem_univ _, rfl⟩
    rw [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨a, b, hab, hne⟩ := hnot
    have hnot2 : ¬ Function.Injective (vv ∘ f) := by
      intro hinj2
      apply hne
      apply hinj2
      simp only [Function.comp_apply]
      rw [hab]
    have hzero : (ExteriorAlgebra.ιMulti R (2 * n)) (vv ∘ f) = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ hnot2
    rw [hzero]
    ext a1 b1
    simp [Matrix.map_apply]
  have hsub : Finset.map
      (⟨fun σ : Equiv.Perm (Fin (2 * n)) => (⇑σ : Fin (2 * n) → Fin (2 * n)),
        DFunLike.coe_injective⟩ : Equiv.Perm (Fin (2 * n)) ↪ (Fin (2 * n) → Fin (2 * n)))
      Finset.univ ⊆ Finset.univ := Finset.subset_univ _
  have hRHS : ((∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod).map
        (fun r => r • ω)) = ∑ σ : Equiv.Perm (Fin (2 * n)), S σ := by
    simp only [hS]
    ext a b
    simp only [Matrix.map_apply, Matrix.sum_apply, Finset.sum_smul]
  rw [hRHS, ← Finset.sum_subset hsub hvan, Finset.sum_map Finset.univ _ T]
  apply Finset.sum_congr rfl
  intro σ _
  exact hTS σ

private theorem al_trace_list_prod_ofFn_comp_finRotate {R : Type*} [CommRing R] (m n : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) R) :
    ((List.ofFn (A ∘ finRotate m)).prod.trace)
      = ((List.ofFn A).prod.trace) := by
  cases m with
  | zero =>
    simp
  | succ j =>
    have h1 : List.ofFn A = A 0 :: List.ofFn (fun i : Fin j => A i.succ) :=
      List.ofFn_succ
    have hcast : (fun i : Fin j => (A ∘ finRotate (j+1)) i.castSucc)
        = (fun i : Fin j => A i.succ) := by
      funext k
      simp [Function.comp_apply]
    have hlast : (A ∘ finRotate (j+1)) (Fin.last j) = A 0 := by
      simp [Function.comp_apply]
    have h2 : List.ofFn (A ∘ finRotate (j+1))
        = (List.ofFn (fun i : Fin j => A i.succ)).concat (A 0) := by
      rw [List.ofFn_succ', hcast, hlast]
    rw [h1, h2]
    rw [List.prod_cons, List.prod_concat]
    exact Matrix.trace_mul_comm _ _

private theorem al_trace_map_smul {R : Type*} {G : Type*} [CommRing R] [Ring G] [Algebra R G]
    {n : ℕ} (P : Matrix (Fin n) (Fin n) R) (g : G) :
    ((P.map (fun r => r • g)).trace) = (P.trace) • g := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, Finset.sum_smul]

private theorem al_sign_finRotate_even (k : ℕ) (hk : 1 ≤ k) :
    (finRotate (2 * k)).sign = -1 := by
  rw [sign_finRotate]
  have hodd : Odd (2 * k - 1) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact ⟨k', by omega⟩
  exact Odd.neg_one_pow hodd

private theorem al_grassmann_trace_pow_even_eq_zero {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (k : ℕ) (hk : 1 ≤ k)
    (h2 : IsUnit (2 : R)) :
    (((∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * k))).trace = 0 := by
  rw [al_grassmann_pow_expansion]
  rw [Matrix.trace_sum]
  simp only [al_trace_map_smul]
  set vv : Fin (2 * n) → (Fin (2 * n) → R) :=
    (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) with hvv
  set T : (Fin (2 * k) → Fin (2 * n)) → ExteriorAlgebra R (Fin (2 * n) → R) :=
    fun f => ((List.ofFn fun kk => M (f kk)).prod.trace) •
      (ExteriorAlgebra.ιMulti R (2 * k)) (vv ∘ f) with hT
  change ∑ f, T f = 0
  have hsign : (finRotate (2 * k)).sign = -1 := al_sign_finRotate_even k hk
  set e : (Fin (2 * k) → Fin (2 * n)) ≃ (Fin (2 * k) → Fin (2 * n)) :=
    Equiv.arrowCongr (finRotate (2 * k)).symm (Equiv.refl (Fin (2 * n))) with he
  have hemem : ∀ f, e f = f ∘ finRotate (2 * k) := by
    intro f
    simp [he, Equiv.arrowCongr]
  have hterm : ∀ f, T (e f) = -T f := by
    intro f
    simp only [hT]
    rw [hemem]
    have htr : ((List.ofFn fun kk => M ((f ∘ finRotate (2 * k)) kk)).prod.trace)
        = ((List.ofFn fun kk => M (f kk)).prod.trace) := by
      have hbase := al_trace_list_prod_ofFn_comp_finRotate (2 * k) n (M ∘ f)
      have e1 : (fun kk => M ((f ∘ finRotate (2 * k)) kk))
          = ((M ∘ f) ∘ finRotate (2 * k)) := rfl
      have e2 : (fun kk => M (f kk)) = (M ∘ f) := rfl
      rw [e1, e2]
      exact hbase
    have hι : (ExteriorAlgebra.ιMulti R (2 * k)) (vv ∘ (f ∘ finRotate (2 * k)))
        = (-1 : ℤˣ) • (ExteriorAlgebra.ιMulti R (2 * k)) (vv ∘ f) := by
      have h1 : vv ∘ (f ∘ finRotate (2 * k)) = (vv ∘ f) ∘ finRotate (2 * k) := by
        funext x
        rfl
      rw [h1, AlternatingMap.map_perm _ _ (finRotate (2 * k)), hsign]
    rw [htr, hι]
    simp [smul_neg]
  have hneg : (∑ f, T (e f)) = -(∑ f, T f) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro f _
    exact hterm f
  have hsum : ∑ f, T (e f) = ∑ f, T f := Equiv.sum_comp e T
  have heq : (∑ f, T f) = -(∑ f, T f) := by
    rw [← hneg]
    exact hsum.symm
  -- T = -T so 2 • T = 0
  have h2T : (2 : R) • (∑ f, T f) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [heq]
    exact neg_add_cancel _
  have h0 : (2 : R) • (∑ f, T f) = (2 : R) • (0 : ExteriorAlgebra R (Fin (2 * n) → R)) := by
    rw [h2T, smul_zero]
  exact (IsUnit.smul_left_cancel h2).mp h0

private theorem al_stdPoly_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (m n : ℕ) (M : Fin m → Matrix (Fin n) (Fin n) R) :
    f.mapMatrix (∑ σ : Equiv.Perm (Fin m),
      (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod)
    = ∑ σ : Equiv.Perm (Fin m),
      (σ.sign : ℤ) • (List.ofFn fun i => f.mapMatrix (M (σ i))).prod := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_zsmul]
  congr 1
  rw [map_list_prod]
  rw [List.map_ofFn]
  rfl

private theorem al_io_mul_io_mem_center {R : Type*} [CommRing R] {V : Type*}
    [AddCommGroup V] [Module R V] (x y : V) :
    (ExteriorAlgebra.ι R x) * (ExteriorAlgebra.ι R y)
      ∈ Subalgebra.center R (ExteriorAlgebra R V) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using ExteriorAlgebra.induction with
  | algebraMap r =>
    exact Algebra.commutes (A := ExteriorAlgebra R V) r _
  | ι z =>
    have h1 : ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R x
        = -(ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R z) := by
      have h := ExteriorAlgebra.ι_add_mul_swap (R := R) z x
      exact eq_neg_of_add_eq_zero_left h
    have h2 : ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R y
        = -(ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R z) := by
      have h := ExteriorAlgebra.ι_add_mul_swap (R := R) z y
      exact eq_neg_of_add_eq_zero_left h
    calc ExteriorAlgebra.ι R z * (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y)
        = (ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R x) * ExteriorAlgebra.ι R y := by
          rw [mul_assoc]
      _ = (-(ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R z)) * ExteriorAlgebra.ι R y := by
          rw [h1]
      _ = -(ExteriorAlgebra.ι R x * (ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R y)) := by
          rw [neg_mul, mul_assoc]
      _ = -(ExteriorAlgebra.ι R x * (-(ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R z))) := by
          rw [h2]
      _ = ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y * ExteriorAlgebra.ι R z := by
          rw [mul_neg, neg_neg, ← mul_assoc]
  | mul a b ha hb =>
    calc (a * b) * (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y)
        = a * (b * (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y)) := by rw [mul_assoc]
      _ = a * ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) * b) := by rw [hb]
      _ = (a * (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y)) * b := by rw [← mul_assoc]
      _ = ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) * a) * b := by rw [ha]
      _ = (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) * (a * b) := by rw [mul_assoc]
  | add a b ha hb =>
    rw [add_mul, mul_add, ha, hb]

private theorem al_grassmann_top_functional {R : Type*} [CommRing R] (m : ℕ) :
    let v : Fin m → (Fin m → R) := fun i => Pi.single i 1
    let fam : (i : ℕ) → ((Fin m → R) [⋀^Fin i]→ₗ[R] R) :=
      Pi.single (M := fun i : ℕ => ((Fin m → R) [⋀^Fin i]→ₗ[R] R)) m
        (Matrix.detRowAlternating (n := Fin m))
    (ExteriorAlgebra.liftAlternating fam) ((ExteriorAlgebra.ιMulti R m) v) = 1 := by
  simp only
  rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
  rw [Pi.single_eq_same]
  have hv : (fun i => Pi.single i (1 : R)) = ⇑(Pi.basisFun R (Fin m)) := by
    funext i
    exact (Pi.basisFun_apply R (Fin m) i).symm
  rw [hv, ← Pi.basisFun_det]
  exact Module.Basis.det_self _

private theorem al_imulti_two {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (w : Fin 2 → V) :
    (ExteriorAlgebra.ιMulti R 2) w
      = (ExteriorAlgebra.ι R (w 0)) * (ExteriorAlgebra.ι R (w 1)) := by
  have h2 : (List.ofFn fun i : Fin 2 => ExteriorAlgebra.ι R (w i))
      = [ExteriorAlgebra.ι R (w 0), ExteriorAlgebra.ι R (w 1)] := by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp
  calc (ExteriorAlgebra.ιMulti R 2) w
      = (List.ofFn fun i : Fin 2 => ExteriorAlgebra.ι R (w i)).prod := by
        rw [ExteriorAlgebra.ιMulti_apply]
    _ = _ := by rw [h2, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]

private theorem al_Xsq_entry_mem_center {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    (((∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ 2) a b
      ∈ Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) := by
  have hX2 := al_grassmann_pow_expansion n M 2
  set vv : Fin (2 * n) → (Fin (2 * n) → R) :=
    (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) with hvv
  have hentry : (((∑ i, (M i).map (fun r => r •
        (ExteriorAlgebra.ι R (vv i) :
          ExteriorAlgebra R (Fin (2 * n) → R)))) ^ 2) a b)
      = ∑ f : Fin 2 → Fin (2 * n),
        (((List.ofFn fun k => M (f k)).prod) a b) •
          (ExteriorAlgebra.ιMulti R 2) (vv ∘ f) := by
    rw [hX2]
    simp [Matrix.sum_apply, Matrix.map_apply]
  rw [hentry]
  apply Subalgebra.sum_mem
  intro f _
  apply Subalgebra.smul_mem
  rw [al_imulti_two]
  exact al_io_mul_io_mem_center _ _

private theorem al_grassmann_sq_matrix {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R)
    (hR : ∀ k : ℕ, 0 < k → IsUnit (k : R)) :
    ∃ Y : Matrix (Fin n) (Fin n)
        (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))),
      (∀ k : ℕ, ((Y ^ k).map (Subtype.val :
        (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) →
          (ExteriorAlgebra R (Fin (2 * n) → R))))
        = (∑ i, (M i).map (fun r => r •
          (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i)
              :
            ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * k))
      ∧ (∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0)
      ∧ (Y ^ (n + 1) = 0)
      ∧ (∀ k : ℕ, 0 < k → IsUnit (k :
        (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))))) := by
  have hmem := al_Xsq_entry_mem_center (R := R) n M
  set φ := (Subalgebra.val
    (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R)))).toRingHom with hφ
  let X : Matrix (Fin n) (Fin n) (ExteriorAlgebra R (Fin (2 * n) → R)) :=
    ∑ i, (M i).map (fun r => r •
      (ExteriorAlgebra.ι R (Pi.single i (1 : R)) : ExteriorAlgebra R (Fin (2 * n) → R)))
  let Y : Matrix (Fin n) (Fin n)
      (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) :=
    fun a b => ⟨(X ^ 2) a b, hmem a b⟩
  have hmapY : Y.map ⇑φ = X ^ 2 := rfl
  have hmapφ : ∀ k : ℕ, (Y ^ k).map ⇑φ = X ^ (2 * k) := by
    intro k
    rw [Matrix.map_pow, hmapY, ← pow_mul]
  have hinj : Function.Injective ⇑φ := Subtype.val_injective
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · intro k
    exact hmapφ k
  · intro k hk
    have h2 : IsUnit (2 : R) := hR 2 (by norm_num)
    have hX := al_grassmann_trace_pow_even_eq_zero n M k hk h2
    have h1 : ⇑φ ((Y ^ k).trace) = (((Y ^ k).map ⇑φ).trace) :=
      AddMonoidHom.map_trace _ _
    rw [hmapφ k, hX] at h1
    have h0 : ⇑φ ((Y ^ k).trace) = ⇑φ 0 := h1.trans (map_zero φ).symm
    exact hinj h0
  · have hX0 := al_grassmann_pow_eq_zero n M (2 * (n + 1))
      (show 2 * n < 2 * (n + 1) by omega)
    have hmap0 : ((Y ^ (n + 1)).map ⇑φ) = 0 := by
      rw [hmapφ (n + 1)]
      exact hX0
    have h0map : ((0 : Matrix (Fin n) (Fin n)
      (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R)))).map ⇑φ) = 0 :=
      Matrix.map_zero _ (map_zero _)
    exact (Matrix.map_injective hinj) (hmap0.trans h0map.symm)
  · intro k hk
    have hRk := hR k hk
    have hcast : ((k : ℕ) : (Subalgebra.center R
        (ExteriorAlgebra R (Fin (2 * n) → R))))
        = algebraMap R (Subalgebra.center R
          (ExteriorAlgebra R (Fin (2 * n) → R))) ((k : ℕ) : R) :=
      (map_natCast _ _).symm
    rw [hcast]
    exact IsUnit.map _ hRk

private theorem al_derivative_det_eq_sum_det_updateRow {C : Type*} [CommRing C]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial C)) :
    Polynomial.derivative (Matrix.det A)
      = ∑ i, Matrix.det (Matrix.updateRow A i (fun j => Polynomial.derivative (A i j))) := by
  have hLHS : Polynomial.derivative (Matrix.det A)
      = ∑ σ : Equiv.Perm ι,
        (Equiv.Perm.sign σ) • Polynomial.derivative (∏ i, A i (σ i)) := by
    conv_lhs => rw [← Matrix.det_transpose, Matrix.det_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Units.smul_def, map_zsmul, Matrix.transpose_apply]
  rw [hLHS]
  simp only [Polynomial.derivative_prod_finset, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hRHS_i : Matrix.det (Matrix.updateRow A i (fun j => Polynomial.derivative (A i j)))
      = ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ)
        • ((∏ j ∈ Finset.univ.erase i, A j (σ j)) * Polynomial.derivative (A i (σ i))) := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    simp only [Matrix.transpose_apply]
    set B := Matrix.updateRow A i (fun j => Polynomial.derivative (A i j)) with hB
    have hBi : B i (σ i) = Polynomial.derivative (A i (σ i)) := by
      rw [hB, Matrix.updateRow_self]
    have herase : (∏ j ∈ Finset.univ.erase i, B j (σ j))
        = ∏ j ∈ Finset.univ.erase i, A j (σ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjne : j ≠ i := Finset.ne_of_mem_erase hj
      exact congrFun (Matrix.updateRow_ne hjne) (σ j)
    have hsplit := (Finset.mul_prod_erase Finset.univ (fun j => B j (σ j))
      (Finset.mem_univ i)).symm
    rw [hsplit, hBi, herase]
    exact mul_comm _ _
  exact hRHS_i.symm

private theorem al_derivative_charpoly_eq_trace_adjugate {C : Type*} [CommRing C]
    {m : Type*} [Fintype m] [DecidableEq m]
    (Y : Matrix m m C) :
    Polynomial.derivative (Y.charpoly)
      = ((Matrix.adjugate (Matrix.charmatrix Y)).trace) := by
  have hrow : forall i, (fun j => Polynomial.derivative ((Matrix.charmatrix Y) i j))
      = Pi.single i 1 := by
    intro i
    funext j
    rw [Matrix.charmatrix_apply, map_sub, Polynomial.derivative_C, sub_zero,
      Matrix.diagonal_apply, Pi.single_apply]
    by_cases h : i = j
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact Polynomial.derivative_X
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      exact map_zero _
  rw [Matrix.charpoly.eq_1, al_derivative_det_eq_sum_det_updateRow]
  have htrace : (Matrix.adjugate (Matrix.charmatrix Y)).trace
      = ∑ i, (Matrix.adjugate (Matrix.charmatrix Y)) i i := by
    simp [Matrix.trace, Matrix.diag_apply]
  rw [htrace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.adjugate_apply, hrow i]

private theorem al_scalar_eq_smul_one {R : Type*} [CommRing R] {nn : Type*} [Fintype nn]
    [DecidableEq nn]
    (c : R) : (Matrix.scalar nn) c = c • (1 : Matrix nn nn R) := by
  ext a b
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]

private theorem al_X_mul_derivative_charpoly_of_nilpotent {C : Type*} [CommRing C] (n : ℕ)
    (Y : Matrix (Fin n) (Fin n) C)
    (hnil : Y ^ (n + 1) = 0)
    (htr : ∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0) :
    Polynomial.X * Polynomial.derivative (Y.charpoly)
      = ((n : Polynomial C)) * Y.charpoly := by
  set x : Matrix (Fin n) (Fin n) (Polynomial C) :=
    (Matrix.scalar (Fin n)) Polynomial.X with hx
  set y : Matrix (Fin n) (Fin n) (Polynomial C) :=
    Polynomial.C.mapMatrix Y with hy
  set χ : Polynomial C := Y.charpoly with hχ
  have hch : Matrix.charmatrix Y = x - y := by
    rw [hx, hy]
    exact Matrix.charmatrix.eq_1 Y
  have hcomm : Commute x y := by
    rw [hx]
    exact Matrix.scalar_commute _
      (fun r' => (show Polynomial.X * r' = r' * Polynomial.X from mul_comm _ _)) _
  set Q : Matrix (Fin n) (Fin n) (Polynomial C) :=
    ∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i) with hQ
  have hQeq : (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n + 1 - 1 - i))
      = (∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)) := by
    apply Finset.sum_congr rfl
    intro i _
    have hexp : n + 1 - 1 - i = n - i := by omega
    rw [hexp]
  have hgeom : Q * (x - y) = x ^ (n + 1) - y ^ (n + 1) := by
    rw [hQ, ← hQeq]
    exact Commute.geom_sum₂_mul hcomm (n + 1)
  have hy0 : y ^ (n + 1) = 0 := by
    rw [hy]
    have h1 : Polynomial.C.mapMatrix (Y ^ (n + 1))
        = (Polynomial.C.mapMatrix Y) ^ (n + 1) := map_pow _ _ _
    rw [← h1, hnil]
    exact map_zero _
  have hadj : Q * ((x - y) * (x - y).adjugate) = x ^ (n + 1) * (x - y).adjugate := by
    rw [← mul_assoc, hgeom, hy0, sub_zero]
  have hchi : (x - y).det = χ := by
    rw [← hch, hχ]
    exact (Matrix.charpoly.eq_1 Y).symm
  have hsmul : Q * ((x - y) * (x - y).adjugate) = χ • Q := by
    rw [Matrix.mul_adjugate, hchi, Matrix.mul_smul, mul_one]
  have hxpow : x ^ (n + 1)
      = ((Polynomial.X : Polynomial C) ^ (n + 1)) •
          (1 : Matrix (Fin n) (Fin n) (Polynomial C)) := by
    rw [hx, ← map_pow, al_scalar_eq_smul_one]
  have h1 : χ • Q = ((Polynomial.X : Polynomial C) ^ (n + 1)) • (x - y).adjugate := by
    have e1 : χ • Q = x ^ (n + 1) * (x - y).adjugate := by
      rw [← hsmul]
      exact hadj
    have e2 : x ^ (n + 1) * (x - y).adjugate
        = ((Polynomial.X : Polynomial C) ^ (n + 1)) • (x - y).adjugate := by
      rw [hxpow, smul_mul_assoc, one_mul]
    exact e1.trans e2
  have h2 : χ • Q.trace
      = ((Polynomial.X : Polynomial C) ^ (n + 1)) • Polynomial.derivative χ := by
    have h2a := congrArg Matrix.trace h1
    rw [Matrix.trace_smul, Matrix.trace_smul, ← hch,
      ← al_derivative_charpoly_eq_trace_adjugate] at h2a
    exact h2a
  have e3 : ∀ i : ℕ, (y ^ (n - i)).trace = Polynomial.C ((Y ^ (n - i)).trace) := by
    intro i
    have e2m : y ^ (n - i) = (Y ^ (n - i)).map ⇑(Polynomial.C) := by
      rw [hy]
      change ((Y.map ⇑Polynomial.C) ^ (n - i)) = _
      exact (Matrix.map_pow _ _ _).symm
    rw [e2m]
    exact (AddMonoidHom.map_trace _ _).symm
  have hterm : ∀ i : ℕ, (x ^ i * y ^ (n - i)).trace
      = Polynomial.X ^ i * Polynomial.C ((Y ^ (n - i)).trace) := by
    intro i
    rw [hx, ← map_pow, al_scalar_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.trace_smul, e3 i, smul_eq_mul]
  have hTn : Polynomial.C ((Y ^ (n - n)).trace) = Polynomial.C ((n : ℕ) : C) := by
    rw [Nat.sub_self, pow_zero, Matrix.trace_one, Fintype.card_fin]
  have hQtr : Q.trace
      = (Polynomial.X ^ n) * Polynomial.C ((n : ℕ) : C) := by
    rw [hQ, Matrix.trace_sum, Finset.sum_range_succ]
    have hrest : (∑ i ∈ Finset.range n, (x ^ i * y ^ (n - i)).trace) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hterm i]
      have htri : ((Y ^ (n - i)).trace) = 0 := htr (n - i) (by
        have hii : i < n := Finset.mem_range.mp hi
        omega)
      rw [htri, map_zero, mul_zero]
    rw [hrest, zero_add, hterm n, hTn]
  have h2m : χ * ((Polynomial.X ^ n) * Polynomial.C ((n : ℕ) : C))
      = Polynomial.X ^ (n + 1) * Polynomial.derivative χ := by
    rw [hQtr] at h2
    rwa [smul_eq_mul, smul_eq_mul] at h2
  have hmain : Polynomial.X ^ n * (Polynomial.C ((n : ℕ) : C) * χ)
      = Polynomial.X ^ n * (Polynomial.X * Polynomial.derivative χ) := by
    have e1 : Polynomial.X ^ n * (Polynomial.C ((n : ℕ) : C) * χ)
        = χ * (Polynomial.X ^ n * Polynomial.C ((n : ℕ) : C)) := by ring
    have e2 : Polynomial.X ^ n * (Polynomial.X * Polynomial.derivative χ)
        = Polynomial.X ^ (n + 1) * Polynomial.derivative χ := by ring
    rw [e1, e2]
    exact h2m
  have hcancel := (Polynomial.isRegular_X_pow n).left hmain
  rw [map_natCast] at hcancel
  exact hcancel.symm

private theorem al_pow_eq_zero_of_trace_pow_eq_zero {C : Type*} [CommRing C] (n : ℕ)
    (Y : Matrix (Fin n) (Fin n) C)
    (hC : ∀ k : ℕ, 0 < k → IsUnit (k : C))
    (hnil : Y ^ (n + 1) = 0)
    (htr : ∀ k : ℕ, 1 ≤ k → ((Y ^ k).trace) = 0) :
    Y.charpoly = Polynomial.X ^ n ∧ Y ^ n = 0 := by
  rcases subsingleton_or_nontrivial C with hsub | hnon
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · let := hnon
    set χ : Polynomial C := Y.charpoly with hχ
    have hN12 : Polynomial.X * Polynomial.derivative χ
        = ((n : Polynomial C)) * χ := by
      have h := al_X_mul_derivative_charpoly_of_nilpotent n Y hnil htr
      rwa [← hχ] at h
    have hkey : ∀ k : ℕ, (k : C) * χ.coeff k = (n : C) * χ.coeff k := by
      intro k
      cases k with
      | zero =>
        have h := congrArg (fun p => Polynomial.coeff p 0) hN12
        simpa using h
      | succ j =>
        have h := congrArg (fun p => Polynomial.coeff p (j + 1)) hN12
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
          Polynomial.coeff_natCast_mul] at h
        push_cast
        linear_combination h
    have hzero : ∀ k : ℕ, k ≠ n → χ.coeff k = 0 := by
      intro k hkn
      have hk := hkey k
      by_cases hlt : k < n
      · have hpos : 0 < n - k := by omega
        have hu := hC (n - k) hpos
        have hsubn : ((n - k : ℕ) : C) = (n : C) - (k : C) :=
          Nat.cast_sub (le_of_lt hlt)
        have h0 : ((n - k : ℕ) : C) * χ.coeff k = 0 := by
          rw [hsubn, sub_mul, hk, sub_self]
        exact IsUnit.mul_left_cancel hu (by rwa [mul_zero])
      · have hlt : n < k := by omega
        have hpos : 0 < k - n := by omega
        have hu := hC (k - n) hpos
        have hsubn : ((k - n : ℕ) : C) = (k : C) - (n : C) :=
          Nat.cast_sub (le_of_lt hlt)
        have h0 : ((k - n : ℕ) : C) * χ.coeff k = 0 := by
          rw [hsubn, sub_mul, hk, sub_self]
        exact IsUnit.mul_left_cancel hu (by rwa [mul_zero])
    have hchar : Y.charpoly = Polynomial.X ^ n := by
      apply Polynomial.ext
      intro k
      rw [Polynomial.coeff_X_pow]
      by_cases hkn : k = n
      · have hdeg : Y.charpoly.natDegree = n := by
          rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        rw [ite_eq_left hkn]
        have hkk : k = Y.charpoly.natDegree := by rw [hkn, hdeg]
        calc Y.charpoly.coeff k = Y.charpoly.coeff Y.charpoly.natDegree :=
              congrArg _ hkk
          _ = 1 := (Matrix.charpoly_monic Y).coeff_natDegree
      · rw [ite_eq_right hkn]
        have hthis := hzero k hkn
        rwa [hχ] at hthis
    refine ⟨hchar, ?_⟩
    have hCH := Matrix.aeval_self_charpoly Y
    rw [hchar, Polynomial.aeval_X_pow] at hCH
    exact hCH

private theorem al_top_smul_cancel {R : Type*} [CommRing R] (m : ℕ) (r : R)
    (h : r • (ExteriorAlgebra.ιMulti R m)
      (fun j : Fin m => (Pi.single j (1 : R) : Fin m → R)) = 0) :
    r = 0 := by
  have h1 : (ExteriorAlgebra.liftAlternating
      (Pi.single (M := fun i : ℕ => ((Fin m → R) [⋀^Fin i]→ₗ[R] R)) m
        (Matrix.detRowAlternating (n := Fin m))))
      (r • (ExteriorAlgebra.ιMulti R m)
        (fun j : Fin m => (Pi.single j (1 : R) : Fin m → R))) = r := by
    rw [map_smul]
    have h2 := al_grassmann_top_functional (R := R) m
    simp only at h2
    rw [h2, smul_eq_mul, mul_one]
  rw [h] at h1
  have h0 : (ExteriorAlgebra.liftAlternating
      (Pi.single (M := fun i : ℕ => ((Fin m → R) [⋀^Fin i]→ₗ[R] R)) m
        (Matrix.detRowAlternating (n := Fin m)))) 0 = 0 :=
    map_zero _
  rw [h0] at h1
  exact h1.symm

private theorem al_amitsur_levitzki_of_algebra_rat {R : Type*} [CommRing R] [Algebra ℚ R]
    (n : ℕ) (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
    (∑ σ : Equiv.Perm (Fin (2 * n)),
      (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod) = 0 := by
  have hR : ∀ k : ℕ, 0 < k → IsUnit (k : R) := by
    intro k hk
    have h1 : ((k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : IsUnit ((k : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr h1
    have h3 : ((k : ℕ) : R) = algebraMap ℚ R ((k : ℕ) : ℚ) := (map_natCast _ _).symm
    rw [h3]
    exact IsUnit.map _ h2
  obtain ⟨Y, hmap, htrace, hnil, hunits⟩ := al_grassmann_sq_matrix n M hR
  obtain ⟨hchar, hYn⟩ := al_pow_eq_zero_of_trace_pow_eq_zero n Y hunits hnil htrace
  have hX0 : (∑ i, (M i).map (fun r => r •
      (ExteriorAlgebra.ι R ((fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) i) :
        ExteriorAlgebra R (Fin (2 * n) → R)))) ^ (2 * n) = 0 := by
    have hmn := hmap n
    rw [hYn] at hmn
    have hzero : ((0 : Matrix (Fin n) (Fin n)
        (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R)))).map (Subtype.val :
        (Subalgebra.center R (ExteriorAlgebra R (Fin (2 * n) → R))) →
          (ExteriorAlgebra R (Fin (2 * n) → R)))) = 0 :=
      Matrix.map_zero _ rfl
    rw [hzero] at hmn
    exact hmn.symm
  have hN4 := al_grassmann_pow_top n M
  rw [hX0] at hN4
  apply Matrix.ext
  intro a b
  have hsmul : (((∑ σ : Equiv.Perm (Fin (2 * n)),
      (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod) : Matrix (Fin n) (Fin n) R) a b) •
      (ExteriorAlgebra.ιMulti R (2 * n))
        (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)) = 0 := by
    have h1 : (((∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod).map (fun r => r •
        (ExteriorAlgebra.ιMulti R (2 * n))
          (fun j : Fin (2 * n) => (Pi.single j (1 : R) : Fin (2 * n) → R)))) a b) = 0 := by
      rw [← hN4, Matrix.zero_apply]
    rwa [Matrix.map_apply] at h1
  have hgoal : (((∑ σ : Equiv.Perm (Fin (2 * n)),
      (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod) : Matrix (Fin n) (Fin n) R) a b) = 0 :=
    al_top_smul_cancel (2 * n) _ hsmul
  rwa [Matrix.zero_apply]

/--
The standard polynomial `S_{2n}` vanishes on `n × n` matrices over a commutative ring.
Source: A. S. Amitsur and J. Levitzki, Minimal identities for algebras, Proc. Amer. Math. Soc. 1
(1950), 449-463, DOI 10.1090/S0002-9939-1950-0036751-9; textbook in Rowen, Polynomial Identities in
Ring Theory.

Proves `Wanted` entry `amitsur_levitzki`.
-/
theorem amitsur_levitzki
    {R : Type*} [CommRing R] (n : ℕ)
    (M : Fin (2 * n) → Matrix (Fin n) (Fin n) R) :
    ∑ σ : Equiv.Perm (Fin (2 * n)),
      (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod = 0 := by
  set Mgen : Fin (2 * n) → Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ) :=
    fun i a b => MvPolynomial.X (i, a, b) with hMgen
  set φ : MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ →+*
      MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ) with hφ
  have hφinj : Function.Injective φ := by
    rw [hφ]
    exact MvPolynomial.map_injective _ Int.cast_injective
  have hN14 := al_amitsur_levitzki_of_algebra_rat (R := MvPolynomial
    (Fin (2 * n) × Fin n × Fin n) ℚ) n (fun i => φ.mapMatrix (Mgen i))
  have hN1φ := al_stdPoly_map φ (2 * n) n Mgen
  rw [hN14] at hN1φ
  have hmap0 : φ.mapMatrix (0 : Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ)) = 0 := by
    change (((0 : Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ)).map ⇑φ)) = 0
    exact Matrix.map_zero _ (map_zero _)
  have hminj : Function.Injective
      (fun MM : Matrix (Fin n) (Fin n)
        (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ) => φ.mapMatrix MM) := by
    change Function.Injective
      (fun MM : Matrix (Fin n) (Fin n)
        (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ) => MM.map ⇑φ)
    exact Matrix.map_injective hφinj
  have hgen0 : (∑ σ : Equiv.Perm (Fin (2 * n)),
      (σ.sign : ℤ) • (List.ofFn fun i => Mgen (σ i)).prod) = 0 :=
    hminj (by simp only []; rw [hN1φ, hmap0])
  set ev : MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (fun p : Fin (2 * n) × Fin n × Fin n => M p.1 p.2.1 p.2.2) with hev
  have hevM : ∀ i, ev.mapMatrix (Mgen i) = M i := by
    intro i
    ext a b
    rw [hMgen, hev]
    change ev (MvPolynomial.X (i, a, b)) = M i a b
    rw [MvPolynomial.eval₂Hom_X']
  have hev0 : ev.mapMatrix (0 : Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ)) = 0 := by
    change (((0 : Matrix (Fin n) (Fin n)
      (MvPolynomial (Fin (2 * n) × Fin n × Fin n) ℤ)).map ⇑ev)) = 0
    exact Matrix.map_zero _ (map_zero _)
  have hN1 := al_stdPoly_map ev (2 * n) n Mgen
  rw [hgen0, hev0] at hN1
  have hfin : (∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => ev.mapMatrix (Mgen (σ i))).prod)
      = (∑ σ : Equiv.Perm (Fin (2 * n)),
        (σ.sign : ℤ) • (List.ofFn fun i => M (σ i)).prod) := by
    apply Finset.sum_congr rfl
    intro σ _
    have hfi : (fun i => ev.mapMatrix (Mgen (σ i))) = (fun i => M (σ i)) :=
      funext (fun i => hevM (σ i))
    rw [hfi]
  rw [hfin] at hN1
  exact hN1.symm

end MathlibExt.Algebra.Algebra.AmitsurLevitzkiWanted
end
