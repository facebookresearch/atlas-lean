/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Rank increments from uniform matrix chains

Let R be a commutative ring, N a finite index type, A,C ∈ Mat(N,N;R), and v₀,…,vₖ ∈ R^N with
Av₀ = 0 and Avᵢ₊₁ = Cvᵢ for i < k. For p(X) = ∑ᵢ₌₀ᵏ (−X)^i vᵢ, the polynomial pencil satisfies
(A + XC)p(X) = (−1)^k X^(k+1) Cvₖ. Over a field, if Cvₖ ∉ im A, every finite scalar set S with
|S| > |N| contains t with rank(A+tC) > rank A.

## References

Gábor Ivanyos, Youming Qiao and K. V. Subrahmanyam, *Non-commutative Edmonds' problem and
matrix semi-invariants*, Fact 2.2 and Algorithm 2, lines 19–25.
-/

@[expose] public section

universe u v

namespace Matrix

open Polynomial

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] {k : ℕ}

private def weightedChainVector (t : R) (v : Fin (k + 1) → (n → R)) : n → R :=
  ∑ i : Fin (k + 1), (-t) ^ i.val • v i

private theorem weightedChainVector_spec (A C : Matrix n n R) (t : R)
    (k : ℕ) (v : Fin (k + 1) → (n → R)) (h0 : A *ᵥ v 0 = 0)
    (hstep : ∀ i : Fin k, A *ᵥ v i.succ = C *ᵥ v i.castSucc) :
    (A + t • C) *ᵥ weightedChainVector t v =
      (t * (-t) ^ k) • (C *ᵥ v (Fin.last k)) := by
  induction k with
  | zero =>
    have hv : weightedChainVector t v = v 0 := by
      unfold weightedChainVector
      rw [Fin.sum_univ_succ]
      simp
    rw [hv, add_mulVec, smul_mulVec, h0, zero_add]
    simp
  | succ k ih =>
    let v' : Fin (k + 1) → (n → R) := fun i => v i.castSucc
    have h0' : A *ᵥ v' 0 = 0 := h0
    have hs' : ∀ i : Fin k, A *ᵥ v' i.succ = C *ᵥ v' i.castSucc := by
      intro i
      simpa only [v', Fin.castSucc_succ] using hstep i.castSucc
    have hlast : A *ᵥ v (Fin.last (k + 1)) = C *ᵥ v' (Fin.last k) := by
      simpa only [show (Fin.last k).succ = Fin.last (k + 1) from rfl, v'] using hstep (Fin.last k)
    have hv : weightedChainVector t v =
        weightedChainVector t v' + (-t) ^ (k + 1) • v (Fin.last (k + 1)) := by
      unfold weightedChainVector
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hv, mulVec_add, mulVec_smul, ih v' h0' hs', add_mulVec, smul_mulVec, hlast]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    ring

/-- **The polynomial vector of a uniform chain.**

Let R be a commutative ring, N finite and v₀,…,vₖ ∈ R^N. Define p(X) ∈ (R[X])^N by p(X)ⱼ =
∑ᵢ₌₀ᵏ (−X)^i ι(vᵢⱼ), where ι : R → R[X] includes coefficients as constant polynomials.
-/
noncomputable def pencilChainPolynomial (v : Fin (k + 1) → (n → R)) : n → R[X] :=
  ∑ i : Fin (k + 1), (-(Polynomial.X : R[X])) ^ i.val • (fun j : n => Polynomial.C (v i j))

private theorem C_mulVec (A : Matrix n n R) (v : n → R) :
    A.map Polynomial.C *ᵥ (fun i : n => Polynomial.C (v i)) =
      (fun i : n => Polynomial.C ((A *ᵥ v) i)) := by
  funext i
  exact ((Polynomial.C : R →+* R[X]).map_mulVec A v i).symm

/-- **The uniform-chain polynomial identity.**

Let R be a commutative ring, N a finite index type, A,C ∈ Mat(N,N;R), and v₀,…,vₖ ∈ R^N with
Av₀ = 0 and Avᵢ₊₁ = Cvᵢ for i < k. Let ι : R → R[X] be constant-polynomial inclusion, applied
entrywise to matrices and vectors. For p(X) = ∑ᵢ₌₀ᵏ (−X)^i ι(vᵢ), one has (ι(A)+Xι(C))p(X) =
(−1)^k X^(k+1)ι(Cvₖ).
-/
theorem pencilChainPolynomial_spec (A C : Matrix n n R)
    (v : Fin (k + 1) → (n → R)) (h0 : A *ᵥ v 0 = 0)
    (hstep : ∀ i : Fin k, A *ᵥ v i.succ = C *ᵥ v i.castSucc) :
    (A.map Polynomial.C + (Polynomial.X : R[X]) • C.map Polynomial.C) *ᵥ pencilChainPolynomial v =
      ((-1 : R[X]) ^ k * (Polynomial.X : R[X]) ^ (k + 1)) •
        (fun i : n => Polynomial.C ((C *ᵥ v (Fin.last k)) i)) := by
  let v' : Fin (k + 1) → (n → R[X]) := fun i j => Polynomial.C (v i j)
  have h0' : A.map Polynomial.C *ᵥ v' 0 = 0 := by
    rw [C_mulVec, h0]
    funext i
    simp
  have hs' : ∀ i : Fin k, A.map Polynomial.C *ᵥ v' i.succ = C.map Polynomial.C *ᵥ v' i.castSucc := by
    intro i
    rw [C_mulVec, C_mulVec, hstep i]
  have h := weightedChainVector_spec (A.map Polynomial.C) (C.map Polynomial.C)
    (Polynomial.X : R[X]) k v' h0' hs'
  change (A.map Polynomial.C + (Polynomial.X : R[X]) • C.map Polynomial.C) *ᵥ pencilChainPolynomial v =
    ((Polynomial.X : R[X]) * (-(Polynomial.X : R[X])) ^ k) •
      (C.map Polynomial.C *ᵥ v' (Fin.last k)) at h
  rw [C_mulVec] at h
  have hc : (Polynomial.X : R[X]) * (-Polynomial.X) ^ k =
      (-1 : R[X]) ^ k * Polynomial.X ^ (k + 1) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ]
    ring
  rwa [hc] at h

/-- **Specialization of the uniform-chain polynomial.**

Let R be a commutative ring, N a finite index type, A,C ∈ Mat(N,N;R), and v₀,…,vₖ ∈ R^N with
Av₀ = 0 and Avᵢ₊₁ = Cvᵢ for i < k. Let p(X) = ∑ᵢ₌₀ᵏ (−X)^i vᵢ, with constant-polynomial vector
coefficients. For every t ∈ R, one has (A+tC)p(t) = (−1)^k t^(k+1) Cvₖ.
-/
theorem pencilChainPolynomial_eval_spec (A C : Matrix n n R)
    (v : Fin (k + 1) → (n → R)) (h0 : A *ᵥ v 0 = 0)
    (hstep : ∀ i : Fin k, A *ᵥ v i.succ = C *ᵥ v i.castSucc) (t : R) :
    (A + t • C) *ᵥ (fun i : n => (pencilChainPolynomial v i).eval t) =
      ((-1 : R) ^ k * t ^ (k + 1)) • (C *ᵥ v (Fin.last k)) := by
  have hv : (fun i : n => (pencilChainPolynomial v i).eval t) = weightedChainVector t v := by
    funext i
    simp only [pencilChainPolynomial, weightedChainVector, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    change (Polynomial.evalRingHom t)
        (∑ j : Fin (k + 1), (-(Polynomial.X : R[X])) ^ j.val * Polynomial.C (v j i)) =
      ∑ j : Fin (k + 1), (-t) ^ j.val * v j i
    rw [map_sum]
    simp
  rw [hv, weightedChainVector_spec A C t k v h0 hstep]
  have hc : t * (-t) ^ k = (-1 : R) ^ k * t ^ (k + 1) := by
    rw [neg_eq_neg_one_mul, mul_pow, pow_succ]
    ring
  rw [hc]

end Matrix

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- **A determinant degree bound with one constant column.**

Let R be a commutative ring and A,B square matrices of size r+1. If the last column of A is
zero, then the polynomial det(XA+B) has natural degree at most r.
-/
theorem natDegree_det_X_add_C_le_of_last_column_zero (r : ℕ)
    (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hA : ∀ i, A i (Fin.last r) = 0) :
    ((Polynomial.X : R[X]) • A.map Polynomial.C + B.map Polynomial.C).det.natDegree ≤ r := by
  classical
  rw [Matrix.det_succ_column _ (Fin.last r)]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  have hcol : ((Polynomial.X : R[X]) • A.map Polynomial.C + B.map Polynomial.C) i (Fin.last r) =
      Polynomial.C (B i (Fin.last r)) := by
    simp [hA]
  have hconst : (-1 : R[X]) ^ (i.val + r) * Polynomial.C (B i (Fin.last r)) =
      Polynomial.C ((-1 : R) ^ (i.val + r) * B i (Fin.last r)) := by
    simp
  rw [hcol]
  simp only [Fin.val_last]
  rw [hconst]
  calc
    _ ≤ (Polynomial.C ((-1 : R) ^ (i.val + r) * B i (Fin.last r))).natDegree +
        (((Polynomial.X : R[X]) • A.map Polynomial.C + B.map Polynomial.C).submatrix
          i.succAbove (Fin.last r).succAbove).det.natDegree := Polynomial.natDegree_mul_le
    _ = (((Polynomial.X : R[X]) • A.map Polynomial.C + B.map Polynomial.C).submatrix
          i.succAbove (Fin.last r).succAbove).det.natDegree := by rw [Polynomial.natDegree_C, zero_add]
    _ ≤ r := by
      have hsub : ((Polynomial.X : R[X]) • A.map Polynomial.C + B.map Polynomial.C).submatrix
          i.succAbove (Fin.last r).succAbove =
        (Polynomial.X : R[X]) • (A.submatrix i.succAbove (Fin.last r).succAbove).map Polynomial.C +
          (B.submatrix i.succAbove (Fin.last r).succAbove).map Polynomial.C := rfl
      rw [hsub]
      simpa only [Fintype.card_fin] using Polynomial.natDegree_det_X_add_C_le
        (A.submatrix i.succAbove (Fin.last r).succAbove) (B.submatrix i.succAbove (Fin.last r).succAbove)

end Polynomial

namespace Matrix

open Polynomial

variable {K : Type u} [Field K] {n : Type v} [Fintype n] [DecidableEq n]

private theorem normalForm_bottom_nonzero (A V U : Matrix n n K) (r s : ℕ)
    (e : n ≃ Fin r ⊕ Fin s) (hV : IsUnit V)
    (hN : V * A * U =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0 (0 : Matrix (Fin s) (Fin s) K)).submatrix e e)
    (y : n → K) (hy : y ∉ A.mulVecLin.range) :
    ∃ j : Fin s, (V *ᵥ y) (e.symm (Sum.inr j)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let z := V *ᵥ y
  let z' : Fin r ⊕ Fin s → K := z ∘ e.symm
  have hdiag : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      (0 : Matrix (Fin s) (Fin s) K) *ᵥ z' = z' := by
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact (h j).symm
  have hproj : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      (0 : Matrix (Fin s) (Fin s) K)).submatrix e e *ᵥ z = z := by
    rw [Matrix.submatrix_mulVec_equiv]
    change (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) K) 0 0
      (0 : Matrix (Fin s) (Fin s) K) *ᵥ z') ∘ e = z
    rw [hdiag]
    funext i
    simp only [z', Function.comp_apply, Equiv.symm_apply_apply]
  have hAy : A *ᵥ (U *ᵥ z) = y := by
    apply Matrix.mulVec_injective_of_isUnit hV
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN]
    exact hproj
  exact hy ⟨U *ᵥ z, hAy⟩

private theorem det_eq_last_entry {r : ℕ} (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hI : Q.submatrix Fin.castSucc Fin.castSucc = 1)
    (hzero : ∀ i : Fin r, Q (Fin.last r) i.castSucc = 0) :
    Q.det = Q (Fin.last r) (Fin.last r) := by
  rw [Matrix.det_succ_row Q (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · simp only [Fin.val_last, Fin.succAbove_last, hI, Matrix.det_one, mul_one]
    have hs : (-1 : K) ^ (r + r) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    rw [hs, one_mul]
  · intro i _ hi
    cases i using Fin.lastCases with
    | last => exact False.elim (hi rfl)
    | cast i => rw [hzero i]; simp
  · intro h
    exact False.elim (h (Finset.mem_univ _))

omit [DecidableEq n] in
private theorem exists_affine_image_minor (A C : Matrix n n K) (y : n → K)
    (hy : y ∉ A.mulVecLin.range) :
    ∃ (V : Matrix n n K) (u : Fin A.rank → (n → K)) (row : Fin (A.rank + 1) → n)
      (P Q : Matrix (Fin (A.rank + 1)) (Fin (A.rank + 1)) K),
      A.rank + 1 ≤ Fintype.card n ∧ Q.det ≠ 0 ∧
      (∀ i, P i (Fin.last A.rank) = 0) ∧
      (∀ (t : K) (a b : Fin (A.rank + 1)), (t • P + Q) a b =
        ((Fin.snoc (fun i : Fin A.rank => V *ᵥ ((A + t • C) *ᵥ u i)) (V *ᵥ y) :
          Fin (A.rank + 1) → (n → K)) b) (row a)) := by
  classical
  obtain ⟨V, U, e, hV, _hU, hN⟩ := Matrix.exists_rank_normal_form A
  obtain ⟨j, hj⟩ := normalForm_bottom_nonzero A V U A.rank
    (Fintype.card n - A.rank) e hV hN y hy
  have hr : A.rank + 1 ≤ Fintype.card n := by
    have hjs := j.isLt
    omega
  let u : Fin A.rank → (n → K) := fun i => U *ᵥ Pi.single (e.symm (Sum.inl i)) 1
  let row : Fin (A.rank + 1) → n :=
    Fin.snoc (fun i : Fin A.rank => e.symm (Sum.inl i)) (e.symm (Sum.inr j))
  let P : Matrix (Fin (A.rank + 1)) (Fin (A.rank + 1)) K := Matrix.of fun a b =>
    ((Fin.snoc (fun i : Fin A.rank => V *ᵥ (C *ᵥ u i)) (0 : n → K) :
      Fin (A.rank + 1) → (n → K)) b) (row a)
  let Q : Matrix (Fin (A.rank + 1)) (Fin (A.rank + 1)) K := Matrix.of fun a b =>
    ((Fin.snoc (fun i : Fin A.rank => V *ᵥ (A *ᵥ u i)) (V *ᵥ y) :
      Fin (A.rank + 1) → (n → K)) b) (row a)
  have hlead (i : Fin A.rank) : V *ᵥ (A *ᵥ u i) =
      (fun x : n => (Matrix.fromBlocks (1 : Matrix (Fin A.rank) (Fin A.rank) K) 0 0
        (0 : Matrix (Fin (Fintype.card n - A.rank)) (Fin (Fintype.card n - A.rank)) K)).submatrix e e
          x (e.symm (Sum.inl i))) := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN, Matrix.mulVec_single_one]
    funext x
    rfl
  have hQI : Q.submatrix Fin.castSucc Fin.castSucc = 1 := by
    ext a b
    change Q a.castSucc b.castSucc = (1 : Matrix (Fin A.rank) (Fin A.rank) K) a b
    simp only [Q, Matrix.of_apply, row, Fin.snoc_castSucc]
    rw [hlead b]
    simp
  have hQzero (i : Fin A.rank) : Q (Fin.last A.rank) i.castSucc = 0 := by
    simp only [Q, Matrix.of_apply, row, Fin.snoc_last, Fin.snoc_castSucc]
    rw [hlead i]
    simp
  have hQdet : Q.det ≠ 0 := by
    rw [det_eq_last_entry Q hQI hQzero]
    simpa only [Q, Matrix.of_apply, row, Fin.snoc_last] using hj
  have hPlast (i : Fin (A.rank + 1)) : P i (Fin.last A.rank) = 0 := by
    simp only [P, Matrix.of_apply, Fin.snoc_last, Pi.zero_apply]
  have hformula (t : K) (a b : Fin (A.rank + 1)) : (t • P + Q) a b =
      ((Fin.snoc (fun i : Fin A.rank => V *ᵥ ((A + t • C) *ᵥ u i)) (V *ᵥ y) :
        Fin (A.rank + 1) → (n → K)) b) (row a) := by
    change t * P a b + Q a b = _
    cases b using Fin.lastCases with
    | last =>
      simp only [P, Q, Matrix.of_apply, Fin.snoc_last,
        Pi.zero_apply, mul_zero, zero_add]
    | cast b =>
      simp only [P, Q, Matrix.of_apply, Fin.snoc_castSucc]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_comm _ _
  exact ⟨V, u, row, P, Q, hr, hQdet, hPlast, hformula⟩

omit [DecidableEq n] in
/-- **A higher-rank pencil at a prescribed scalar.**

Let K be a field, N finite, A,C ∈ Mat(N,N;K), and v₀,…,vₖ ∈ K^N with Av₀ = 0 and Avᵢ₊₁ = Cvᵢ
for i < k. Suppose Cvₖ ∉ im A. For any finite set S ⊆ K with |S| > |N|, there exists t ∈ S
such that rank A < rank(A+tC).
-/
theorem exists_rank_lt_add_smul_of_uniform_chain (A C : Matrix n n K)
    (k : ℕ) (v : Fin (k + 1) → (n → K)) (h0 : A *ᵥ v 0 = 0)
    (hstep : ∀ i : Fin k, A *ᵥ v i.succ = C *ᵥ v i.castSucc)
    (hout : C *ᵥ v (Fin.last k) ∉ A.mulVecLin.range)
    (S : Finset K) (hS : Fintype.card n < S.card) :
    ∃ t ∈ S, A.rank < (A + t • C).rank := by
  classical
  let y := C *ᵥ v (Fin.last k)
  obtain ⟨V, u, row, P, Q, hr, hQdet, hPlast, hformula⟩ := exists_affine_image_minor A C y hout
  let p : K[X] := ((Polynomial.X : K[X]) • P.map Polynomial.C + Q.map Polynomial.C).det
  have hp0 : p.coeff 0 ≠ 0 := by
    change (((Polynomial.X : K[X]) • P.map Polynomial.C + Q.map Polynomial.C).det).coeff 0 ≠ 0
    rwa [Polynomial.coeff_det_X_add_C_zero]
  have hp : p ≠ 0 := by
    intro h
    exact hp0 (by rw [h]; simp)
  have hXp : (Polynomial.X : K[X]) * p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hp
  have hdegp : p.natDegree ≤ A.rank :=
    Polynomial.natDegree_det_X_add_C_le_of_last_column_zero A.rank P Q hPlast
  have hdeg : ((Polynomial.X : K[X]) * p).natDegree ≤ Fintype.card n := by
    calc
      _ ≤ (Polynomial.X : K[X]).natDegree + p.natDegree := Polynomial.natDegree_mul_le
      _ = 1 + p.natDegree := by rw [Polynomial.natDegree_X]
      _ ≤ 1 + A.rank := Nat.add_le_add_left hdegp 1
      _ ≤ Fintype.card n := by omega
  have hex : ∃ t ∈ S, ((Polynomial.X : K[X]) * p).eval t ≠ 0 := by
    by_contra h
    push Not at h
    exact hXp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      ((Polynomial.X : K[X]) * p) S h (hdeg.trans_lt hS))
  obtain ⟨t, htS, hval⟩ := hex
  rw [Polynomial.eval_mul, Polynomial.eval_X] at hval
  have ht : t ≠ 0 := (mul_ne_zero_iff.mp hval).1
  have hpval : p.eval t ≠ 0 := (mul_ne_zero_iff.mp hval).2
  have hevaldet : p.eval t = (t • P + Q).det := by
    change (Polynomial.evalRingHom t)
      (((Polynomial.X : K[X]) • P.map Polynomial.C + Q.map Polynomial.C).det) = _
    rw [RingHom.map_det]
    congr 1
    ext a b
    simpa [Matrix.map_apply, smul_eq_mul] using (mul_comm (P a b) t)
  have hdet : (t • P + Q).det ≠ 0 := by rwa [hevaldet] at hpval
  let g : n → K := fun i => (pencilChainPolynomial v i).eval t
  let c : K := (-1 : K) ^ k * t ^ (k + 1)
  have hc : c ≠ 0 := mul_ne_zero
    (pow_ne_zero k (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero (k + 1) ht)
  have hchain : (A + t • C) *ᵥ g = c • y := pencilChainPolynomial_eval_spec A C v h0 hstep t
  have hpreimage : (A + t • C) *ᵥ (c⁻¹ • g) = y := by
    rw [Matrix.mulVec_smul, hchain, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let F : Matrix n (Fin (A.rank + 1)) K := Matrix.of fun a b =>
    ((Fin.snoc u (c⁻¹ • g) : Fin (A.rank + 1) → (n → K)) b) a
  let M := A + t • C
  let N := V * M * F
  have hfactor : t • P + Q = N.submatrix row id := by
    ext a b
    rw [hformula t a b]
    change ((Fin.snoc (fun i : Fin A.rank => V *ᵥ (M *ᵥ u i)) (V *ᵥ y) :
        Fin (A.rank + 1) → (n → K)) b) (row a) =
      ((V * M) *ᵥ ((Fin.snoc u (c⁻¹ • g) : Fin (A.rank + 1) → (n → K)) b)) (row a)
    rw [← Matrix.mulVec_mulVec]
    cases b using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      rw [hpreimage]
    | cast b => simp only [Fin.snoc_castSucc]
  have hRankQ : (t • P + Q).rank = A.rank + 1 := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have hlower : A.rank + 1 ≤ N.rank := by
    calc
      A.rank + 1 = (t • P + Q).rank := hRankQ.symm
      _ = (N.submatrix row id).rank := congrArg Matrix.rank hfactor
      _ ≤ N.rank := Matrix.rank_submatrix_le N row id
  have hupper : N.rank ≤ (A + t • C).rank :=
    (Matrix.rank_mul_le_left (V * M) F).trans (Matrix.rank_mul_le_right V M)
  exact ⟨t, htS, (Nat.lt_succ_self A.rank).trans_le (hlower.trans hupper)⟩

end Matrix
