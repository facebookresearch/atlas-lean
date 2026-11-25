/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.PicardGroup

/-!
# Schur decomposition

Every square complex matrix is unitarily similar to an upper-triangular matrix:
`Matrix.exists_unitaryGroup_isUpperTriangular`.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem schur_fin_aux : ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ),
  ∃ (U T : Matrix (Fin k) (Fin k) ℂ),
    U ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ T.IsUpperTriangular ∧ A = U * T * star U := by
  intro k
  induction k with
  | zero =>
    intro A
    refine ⟨1, A, ?_, ?_, ?_⟩
    · exact Submonoid.one_mem _
    · intro i
      exact Fin.elim0 i
    · simp
  | succ k ih =>
    intro A
    have hnt : Nontrivial (EuclideanSpace ℂ (Fin (k + 1))) := by
      apply nontrivial_of_ne (WithLp.toLp 2 (Pi.single (0 : Fin (k+1)) (1 : ℂ))) (WithLp.toLp 2 0)
      simp
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toEuclideanLin A)
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    rw [Module.End.hasEigenvector_iff] at hv
    obtain ⟨hmem, hne2⟩ := hv
    rw [Module.End.mem_eigenspace_iff] at hmem
    set v₀ : EuclideanSpace ℂ (Fin (k+1)) := (‖v‖⁻¹ : ℝ) • v with hv₀def
    have hv₀_norm : ‖v₀‖ = 1 := by
      rw [hv₀def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne2))]
      field_simp
    have hv₀defC : v₀ = ((‖v‖⁻¹ : ℝ) : ℂ) • v :=
      hv₀def.trans (RCLike.real_smul_eq_coe_smul _ _)
    have hv₀_eig : Matrix.toEuclideanLin A v₀ = μ • v₀ := by
      rw [hv₀defC, map_smul, hmem, smul_comm]
    have horth : Orthonormal ℂ ((Set.singleton (0 : Fin (k+1))).domRestrict (fun _ => v₀)) := by
      rw [orthonormal_iff_ite]
      intro a b
      have ha : (a : Fin (k+1)) = 0 := Set.mem_singleton_iff.mp a.property
      have hb : (b : Fin (k+1)) = 0 := Set.mem_singleton_iff.mp b.property
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst hab
      simp only [ite_true]
      change inner ℂ v₀ v₀ = 1
      rw [inner_self_eq_norm_sq_to_K, hv₀_norm]
      norm_num
    obtain ⟨b, hb0⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
      (E := EuclideanSpace ℂ (Fin (k+1))) (ι := Fin (k+1)) finrank_euclideanSpace horth
    have hb0' : b 0 = v₀ := hb0 0 (Set.mem_singleton 0)
    have hb_eig : Matrix.toEuclideanLin A (b 0) = μ • (b 0) := hb0' ▸ hv₀_eig
    -- U₁ and B
    set U₁ : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
      (EuclideanSpace.basisFun (Fin (k+1)) ℂ).toBasis.toMatrix b.toBasis with hU₁def
    have hU₁mem : U₁ ∈ Matrix.unitaryGroup (Fin (k+1)) ℂ :=
      (EuclideanSpace.basisFun (Fin (k+1)) ℂ).toMatrix_orthonormalBasis_mem_unitary b
    have hU₁eq : U₁ * star U₁ = 1 := Matrix.mem_unitaryGroup_iff.mp hU₁mem
    set B : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := star U₁ * A * U₁ with hBdef
    have hcol : U₁ *ᵥ Pi.single 0 1 = (b 0).ofLp := by
      rw [Matrix.mulVec_single_one]
      rfl
    have hA : A *ᵥ (b 0).ofLp = μ • (b 0).ofLp := by
      have h2 := congrArg WithLp.ofLp hb_eig
      rw [show Matrix.toEuclideanLin (𝕜 := ℂ) A (b 0) = WithLp.toLp 2 (A *ᵥ (b 0).ofLp) from
        Matrix.toLpLin_apply 2 2 A (b 0)] at h2
      simpa using h2
    have hstar : star U₁ *ᵥ (b 0).ofLp = Pi.single 0 1 := by
      rw [← hcol, Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp hU₁mem,
        Matrix.one_mulVec]
    have hBvec : B *ᵥ Pi.single 0 1 = μ • Pi.single (0 : Fin (k+1)) 1 := by
      change (star U₁ * A * U₁) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, hA, Matrix.mulVec_smul, hstar]
    have hB00 : B 0 0 = μ := by
      have h00 := congrFun hBvec 0
      rw [Matrix.mulVec_single_one] at h00
      simpa using h00
    have hb0 : ∀ x : Fin k, B x.succ 0 = 0 := by
      intro x
      have hx := congrFun hBvec x.succ
      rw [Matrix.mulVec_single_one] at hx
      simp at hx
      simpa using hx
    -- A' and induction
    set A' : Matrix (Fin k) (Fin k) ℂ := fun x y => B x.succ y.succ with hA'def
    have hA'def' : ∀ x y : Fin k, A' x y = B x.succ y.succ := fun x y => rfl
    obtain ⟨U', T', hU'mem, hT'tri, hA'eq⟩ := ih A'
    have hU'eq1 : U' * star U' = 1 := Matrix.mem_unitaryGroup_iff.mp hU'mem
    have hU'eq2 : star U' * U' = 1 := Matrix.mem_unitaryGroup_iff'.mp hU'mem
    -- V
    set V : Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
      Fin.cons (Pi.single 0 1) (fun i' => Fin.cons 0 (U' i')) with hVdef
    have e00 : V 0 0 = 1 := by simp [hVdef]
    have e0s : ∀ j : Fin k, V 0 j.succ = 0 := by intro j; simp [hVdef]
    have es0 : ∀ i : Fin k, V i.succ 0 = 0 := by intro i; simp [hVdef]
    have ess : ∀ i j : Fin k, V i.succ j.succ = U' i j := by intro i j; simp [hVdef]
    have s00 : star V 0 0 = 1 := by rw [Matrix.star_apply]; simp [hVdef]
    have s0s : ∀ j : Fin k, star V 0 j.succ = 0 := by
      intro j; rw [Matrix.star_apply]; simp [hVdef]
    have ss0 : ∀ i : Fin k, star V i.succ 0 = 0 := by
      intro i; rw [Matrix.star_apply]; simp [hVdef]
    have sss : ∀ i j : Fin k, star V i.succ j.succ = star U' i j := by
      intro i j; rw [Matrix.star_apply]; simp [hVdef, Matrix.star_apply]
    have hVmem : V ∈ Matrix.unitaryGroup (Fin (k+1)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      simp only [Matrix.mul_apply, Matrix.one_apply]
      obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
      · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
        · rw [Fin.sum_univ_succ, e00, s00, one_mul]
          have : ∀ x : Fin k, V 0 x.succ * star V x.succ 0 = 0 := by
            intro x; rw [e0s x, zero_mul]
          rw [Finset.sum_eq_zero (fun x _ => this x)]
          simp
        · rw [Fin.sum_univ_succ]
          have h1 : V 0 0 * star V 0 j'.succ = 0 := by rw [e00, s0s j', mul_zero]
          have h2 : ∀ x : Fin k, V 0 x.succ * star V x.succ j'.succ = 0 := by
            intro x; rw [e0s x, zero_mul]
          rw [h1, Finset.sum_eq_zero (fun x _ => h2 x), add_zero]
          have hc : (0 : Fin (k+1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
          simp [hc]
      · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
        · rw [Fin.sum_univ_succ]
          have h1 : V i'.succ 0 * star V 0 0 = 0 := by rw [es0 i', zero_mul]
          have h2 : ∀ x : Fin k, V i'.succ x.succ * star V x.succ 0 = 0 := by
            intro x; rw [ss0 x, mul_zero]
          rw [h1, Finset.sum_eq_zero (fun x _ => h2 x), add_zero]
          have hc : i'.succ ≠ (0 : Fin (k+1)) := Fin.succ_ne_zero i'
          simp [hc]
        · rw [Fin.sum_univ_succ]
          have h1 : V i'.succ 0 * star V 0 j'.succ = 0 := by rw [es0 i', zero_mul]
          rw [h1, zero_add]
          have htail : ∑ x : Fin k, V i'.succ x.succ * star V x.succ j'.succ
              = ∑ x : Fin k, U' i' x * star U' x j' := by
            apply Finset.sum_congr rfl
            intro x _
            rw [ess i' x, sss x j']
          rw [htail]
          have h := congrFun (congrFun hU'eq1 i') j'
          simp only [Matrix.mul_apply, Matrix.one_apply] at h
          simp only [Fin.succ_inj]
          exact h
    have hVeq : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
    -- U and T
    set U : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := U₁ * V with hUdef
    have hUmem : U ∈ Matrix.unitaryGroup (Fin (k+1)) ℂ :=
      Submonoid.mul_mem _ hU₁mem hVmem
    set T : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := star V * B * V with hTdef
    -- hSB facts
    have hSB0 : ∀ i : Fin k, (star V * B) i.succ 0 = 0 := by
      intro i
      rw [Matrix.mul_apply, Fin.sum_univ_succ, ss0 i, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro y _
      rw [sss i y, hb0 y, mul_zero]
    have hSBss : ∀ i x : Fin k, (star V * B) i.succ x.succ = (star U' * A') i x := by
      intro i x
      rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, ss0 i, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro y _
      rw [sss i y, hA'def' y x]
    -- T entries
    have hT0 : ∀ i : Fin k, T i.succ 0 = 0 := by
      intro i
      rw [hTdef, Matrix.mul_apply, Fin.sum_univ_succ, hSB0 i, zero_mul, zero_add]
      apply Finset.sum_eq_zero
      intro x _
      rw [hSBss i x, es0 x, mul_zero]
    have hTss_eq : ∀ i j : Fin k, T i.succ j.succ = (star U' * A' * U') i j := by
      intro i j
      rw [hTdef, Matrix.mul_apply, Fin.sum_univ_succ]
      have hhead : (star V * B) i.succ 0 * V 0 j.succ = 0 := by
        rw [hSB0 i, zero_mul]
      rw [hhead, zero_add]
      have htail : ∀ x : Fin k, (star V * B) i.succ x.succ * V x.succ j.succ
          = (star U' * A') i x * U' x j := by
        intro x
        rw [hSBss i x, ess x j]
      rw [Finset.sum_congr rfl (fun x _ => htail x)]
      rw [Matrix.mul_apply]
    -- T' recovery
    have hT'rec : star U' * A' * U' = T' := by
      calc star U' * A' * U'
          = star U' * (U' * T' * star U') * U' := by rw [hA'eq]
        _ = (star U' * U') * T' * (star U' * U') := by simp only [mul_assoc]
        _ = T' := by rw [hU'eq2, one_mul, mul_one]
    have hTss : ∀ i j : Fin k, T i.succ j.succ = T' i j := by
      intro i j
      rw [hTss_eq i j, hT'rec]
    have hTtri : T.IsUpperTriangular := by
      intro i j hij
      obtain rfl | ⟨i', rfl⟩ := Fin.eq_zero_or_eq_succ i
      · exact absurd hij (Fin.not_lt_zero j)
      · obtain rfl | ⟨j', rfl⟩ := Fin.eq_zero_or_eq_succ j
        · exact hT0 i'
        · rw [hTss i' j']
          apply hT'tri
          simpa using hij
    -- final equation A = U * T * star U
    have hfinal : A = U * T * star U := by
      have e1 : U₁ * B * star U₁ = A := by
        rw [hBdef]
        calc U₁ * (star U₁ * A * U₁) * star U₁
            = (U₁ * star U₁) * A * (U₁ * star U₁) := by simp only [mul_assoc]
          _ = A := by rw [hU₁eq, one_mul, mul_one]
      have e2 : (U₁ * V) * (star V * B * V) * (star V * star U₁) = U₁ * B * star U₁ := by
        calc (U₁ * V) * (star V * B * V) * (star V * star U₁)
            = U₁ * ((V * star V) * B * (V * star V)) * star U₁ := by simp only [mul_assoc]
          _ = U₁ * B * star U₁ := by rw [hVeq, one_mul, mul_one]
      rw [hUdef, hTdef, star_mul]
      rw [e2, e1]
    exact ⟨U, T, hUmem, hTtri, hfinal⟩

private noncomputable def orderIsoFin (m : Type*) [Fintype m] [DecidableEq m] [LinearOrder m] :
    m ≃o Fin (Fintype.card m) := by
  classical
  let e1 : Fin (Fintype.card m) ≃o ↥(Finset.univ : Finset m) :=
    Finset.orderIsoOfFin Finset.univ (by simp)
  let e2 : ↥(Finset.univ : Finset m) ≃o m := by
    apply StrictMono.orderIsoOfSurjective Subtype.val
    · intro a b hab
      exact hab
    · intro x
      exact ⟨⟨x, Finset.mem_univ x⟩, rfl⟩
  exact (e1.trans e2).symm

/--
**Schur decomposition of a complex square matrix.** Let $A$ be a square complex matrix whose rows
and columns are indexed by a finite linearly ordered type $n$. Then there are a unitary matrix $U$,
with conjugate transpose $U^*$, and a matrix $T$ that is upper triangular with respect to the order
on $n$ (that is, $T_{ij} = 0$ whenever $j < i$) such that $A = U T U^*$.

Source: I. Schur, Uber charakteristische Wurzeln, Math. Ann. 66 (1909), 488-510, DOI
10.1007/BF01450045.
Proves `Wanted` entry `schur_decomposition`, restated over `Matrix.unitaryGroup` in place of the
entry's `IsUnitaryMatrix`.
-/
theorem exists_unitaryGroup_isUpperTriangular (A : Matrix n n ℂ) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (T : Matrix n n ℂ),
      T.IsUpperTriangular ∧ A = (U : Matrix n n ℂ) * T * star (U : Matrix n n ℂ) := by
  classical
  let e : n ≃o Fin (Fintype.card n) := orderIsoFin n
  set A' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    Matrix.reindex e.toEquiv e.toEquiv A with hA'def
  obtain ⟨U', T', hU'mem, hT'tri, hA'eq⟩ := schur_fin_aux _ A'
  set U : Matrix n n ℂ :=
    Matrix.reindex e.symm.toEquiv e.symm.toEquiv U' with hUdef
  set T : Matrix n n ℂ :=
    Matrix.reindex e.symm.toEquiv e.symm.toEquiv T' with hTdef
  have hre_mul : ∀ M N : Matrix n n ℂ,
      Matrix.reindex e.toEquiv e.toEquiv (M * N)
        = Matrix.reindex e.toEquiv e.toEquiv M * Matrix.reindex e.toEquiv e.toEquiv N := by
    intro M N
    simp only [Matrix.reindex_apply]
    rw [← Matrix.submatrix_mul_equiv M N ⇑(e.toEquiv).symm (e.toEquiv).symm ⇑(e.toEquiv).symm]
  have hre_star : ∀ M : Matrix n n ℂ,
      star (Matrix.reindex e.toEquiv e.toEquiv M)
        = Matrix.reindex e.toEquiv e.toEquiv (star M) := by
    intro M
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.star_apply]
  have hre_one : Matrix.reindex e.toEquiv e.toEquiv (1 : Matrix n n ℂ) = 1 := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  have hRU : Matrix.reindex e.toEquiv e.toEquiv U = U' := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hUdef,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    simp
  have hRT : Matrix.reindex e.toEquiv e.toEquiv T = T' := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hTdef,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    simp
  have hRA : Matrix.reindex e.toEquiv e.toEquiv A = A' := hA'def.symm
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hinj : Function.Injective (Matrix.reindex e.toEquiv e.toEquiv :
        Matrix n n ℂ → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) :=
      (Matrix.reindex e.toEquiv e.toEquiv).injective
    apply hinj
    rw [hre_mul, ← hre_star, hRU, hre_one]
    exact Matrix.mem_unitaryGroup_iff.mp hU'mem
  have hTtri : T.IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    have eij : T i j = T' (e i) (e j) := by
      simp [hTdef, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [eij]
    apply hT'tri
    change e j < e i
    exact e.strictMono hij'
  have hfinal_star : A = U * T * star U := by
    have hinj : Function.Injective (Matrix.reindex e.toEquiv e.toEquiv :
        Matrix n n ℂ → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ) :=
      (Matrix.reindex e.toEquiv e.toEquiv).injective
    apply hinj
    rw [hRA, hre_mul, hre_mul, ← hre_star, hRU, hRT]
    exact hA'eq
  exact ⟨⟨U, hUmem⟩, T, hTtri, hfinal_star⟩

end Matrix
