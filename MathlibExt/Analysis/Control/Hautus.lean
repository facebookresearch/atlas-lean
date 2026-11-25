/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MathlibExt.Analysis.Control.LinearControllability

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# The Hautus (Popov–Belevitch–Hautus) test

For a real linear control system `ẋ = A x + B u` given by matrices `A ∈ ℝ^{n×n}` and
`B ∈ ℝ^{n×m}`, the Hautus test says that the system is controllable if and only if no complex
left eigenvector of `A` is annihilated by `B`; equivalently `rank [λ I - A, B] = n` for every
`λ ∈ ℂ` (Sontag, *Mathematical Control Theory*, 2nd ed., Lemma 3.3.7).

* `kalman_matrix_iff_hautus`: the Kalman condition in matrix form is equivalent to the Hautus
  condition;
* `isControllableOn_iff_hautus`: controllability on `[0, T]`, `T > 0`, of the system on Euclidean
  space defined by the matrices is equivalent to the Hautus condition.
-/

open Matrix

@[expose] public section

namespace MathlibExt.Analysis.Control

variable {n m : ℕ}

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Real and imaginary parts of `w ᵥ* M` for a real matrix `M`. -/
private theorem re_vecMul_map (w : Fin n → ℂ) (M : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) :
    (w ᵥ* M.map (↑) : Fin m → ℂ) j = (((fun i => (w i).re) ᵥ* M) j : ℂ) +
      (((fun i => (w i).im) ᵥ* M) j : ℂ) * Complex.I := by
  simp only [vecMul, dotProduct, map_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← Complex.re_add_im (w i)]
  ring

/-- **Kalman condition and Hautus test for real matrices** (Sontag, *Mathematical Control
Theory*, 2nd ed., Lemma 3.3.7, (a) ⇔ (b), in left-eigenvector form). For `A ∈ ℝ^{n×n}` and
`B ∈ ℝ^{n×m}`, the only real row vector `η` with `η A^k B = 0` for all `k` is `0` if and only if,
for every `λ ∈ ℂ`, the only complex row vector `w` with `w A = λ w` and `w B = 0` is `0`. The
right-hand side says that the rows of `[λ I - A, B]` are linearly independent, that is
`rank [λ I - A, B] = n`. -/
theorem kalman_matrix_iff_hautus (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (∀ η : Fin n → ℝ, (∀ k : ℕ, η ᵥ* (A ^ k * B) = 0) → η = 0) ↔
      ∀ (μ : ℂ) (w : Fin n → ℂ), w ᵥ* A.map (↑) = μ • w → w ᵥ* B.map (↑) = 0 → w = 0 := by
  set Ac : Matrix (Fin n) (Fin n) ℂ := A.map (↑) with hAc
  set Bc : Matrix (Fin n) (Fin m) ℂ := B.map (↑) with hBc
  have hpow : ∀ k : ℕ, (A ^ k * B).map ((↑) : ℝ → ℂ) = Ac ^ k * Bc := by
    intro k
    have h1 : (A ^ k * B).map (⇑Complex.ofRealHom) =
        (A ^ k).map (⇑Complex.ofRealHom) * B.map (⇑Complex.ofRealHom) := Matrix.map_mul
    have h2 : (A ^ k).map (⇑Complex.ofRealHom) = (A.map (⇑Complex.ofRealHom)) ^ k :=
      Complex.ofRealHom.mapMatrix.map_pow A k
    rw [h2] at h1
    exact h1
  constructor
  · intro hK μ w hw hwB
    have hwk : ∀ k : ℕ, w ᵥ* Ac ^ k = μ ^ k • w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, smul_vecMul, hw, smul_smul, pow_succ]
    have hzero : ∀ k : ℕ, w ᵥ* (A ^ k * B).map (↑) = 0 := by
      intro k
      rw [hpow, ← vecMul_vecMul, hwk, smul_vecMul, hwB, smul_zero]
    have hre : (fun i => (w i).re) = 0 := hK _ fun k => by
      funext j
      have := congrArg Complex.re (congrFun (hzero k) j)
      rw [re_vecMul_map] at this
      simpa using this
    have him : (fun i => (w i).im) = 0 := hK _ fun k => by
      funext j
      have := congrArg Complex.im (congrFun (hzero k) j)
      rw [re_vecMul_map] at this
      simpa using this
    funext i
    apply Complex.ext
    · exact congrFun hre i
    · exact congrFun him i
  · intro hH η hη
    by_contra hne
    let K : Submodule ℂ (Fin n → ℂ) := ⨅ k : ℕ, LinearMap.ker (vecMulLinear (Ac ^ k * Bc))
    have hmemK : ∀ w, w ∈ K ↔ ∀ k : ℕ, w ᵥ* (Ac ^ k * Bc) = 0 := by
      intro w
      simp [K, Submodule.mem_iInf]
    have hηK : (fun i => (η i : ℂ)) ∈ K := by
      rw [hmemK]
      intro k
      rw [← hpow]
      funext j
      rw [re_vecMul_map]
      have h0 : (fun _ : Fin n => (0 : ℝ)) = 0 := rfl
      simp [hη k, h0]
    have hmaps : Set.MapsTo (vecMulLinear Ac) K K := by
      intro w hw
      rw [SetLike.mem_coe, hmemK] at hw ⊢
      intro k
      have := hw (k + 1)
      rw [pow_succ', Matrix.mul_assoc, ← vecMul_vecMul] at this
      simpa using this
    let g : Module.End ℂ K := (vecMulLinear Ac).restrict hmaps
    have hnt : Nontrivial K := by
      refine ⟨⟨⟨_, hηK⟩, 0, ?_⟩⟩
      intro h
      apply hne
      funext i
      have := congrFun (congrArg Subtype.val h) i
      simpa using this
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hgv : g v = μ • v := hv.apply_eq_smul
    have hv0 : (v : Fin n → ℂ) ≠ 0 := fun h => hv.2 (Subtype.ext h)
    apply hv0
    apply hH μ
    · have := congrArg Subtype.val hgv
      exact this
    · have := (hmemK v).1 v.2 0
      simpa using this

/-- Inner products against the system of a pair of matrices, in coordinates. -/
private theorem inner_matrix_eq (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (η : EuclideanSpace ℝ (Fin n)) (k : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪η, (toEuclideanCLM (𝕜 := ℝ) A ^ k) ((toEuclideanLin B).toContinuousLinearMap v)⟫ =
      (WithLp.ofLp η ᵥ* (A ^ k * B)) ⬝ᵥ WithLp.ofLp v := by
  rw [← map_pow, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM]
  change (A ^ k *ᵥ (B *ᵥ WithLp.ofLp v)) ⬝ᵥ star (WithLp.ofLp η) = _
  rw [mulVec_mulVec, star_trivial, dotProduct_comm, dotProduct_mulVec]

/-- **Hautus test for controllability** (Hautus 1969; Sontag, *Mathematical Control Theory*,
2nd ed., Lemma 3.3.7). For `T > 0`, the real system `ẋ = A x + B u` on `ℝⁿ` with
`A ∈ ℝ^{n×n}`, `B ∈ ℝ^{n×m}` is controllable on `[0, T]` if and only if for every `λ ∈ ℂ`
no nonzero complex row vector `w` satisfies `w A = λ w` and `w B = 0`, that is,
`rank [λ I - A, B] = n` for every `λ ∈ ℂ`. -/
theorem isControllableOn_iff_hautus (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {T : ℝ} (hT : 0 < T) :
    IsControllableOn (toEuclideanCLM (𝕜 := ℝ) A) (toEuclideanLin B).toContinuousLinearMap T ↔
      ∀ (μ : ℂ) (w : Fin n → ℂ), w ᵥ* A.map (↑) = μ • w → w ᵥ* B.map (↑) = 0 → w = 0 := by
  rw [isControllableOn_iff_kalman _ _ hT, kalmanSubspace_eq_top_iff, ← kalman_matrix_iff_hautus]
  simp only [inner_matrix_eq]
  constructor
  · intro h η hη
    have := h (WithLp.toLp 2 η) fun k v => by rw [hη k, zero_dotProduct]
    simpa using congrArg WithLp.ofLp this
  · intro h η hη
    have : WithLp.ofLp η = 0 := h _ fun k => by
      funext j
      have := hη k (WithLp.toLp 2 (Pi.single j 1))
      simpa [dotProduct_single] using this
    simpa using congrArg (WithLp.toLp 2) this

end MathlibExt.Analysis.Control
