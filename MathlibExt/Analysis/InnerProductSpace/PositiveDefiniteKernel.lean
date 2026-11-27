/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Positive-definite kernels and feature maps

A real function `k` on `X × X` is a positive-definite kernel when all its kernel matrices are
symmetric positive semidefinite. Aronszajn's theorem identifies these kernels with the functions
`k(x, x') = ⟪φ(x), φ(x')⟫` given by a feature map `φ` into a Hilbert space; the feature space can be
taken to be the reproducing kernel Hilbert space of `k`. This is the starting point of kernel
methods in machine learning (F. Bach, *Learning Theory from First Principles*, MIT Press (2024),
Section 7.3).

The construction of the reproducing kernel Hilbert space of an operator-valued positive
semidefinite matrix is Mathlib's `RKHS.OfKernel` (Moore–Aronszajn); this file specializes it to
real scalar kernels in the form used in learning theory.

## Main results

- `IsPosDefKernel`: Bach's Definition 7.1.
- `isPosDefKernel_iff_exists_featureMap`: Aronszajn's theorem (Bach's Proposition 7.3).
-/

@[expose] public section

open scoped RealInnerProductSpace

universe u

namespace MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel

variable {X : Type*}

/-- A real function `k` on `X × X` is a **positive-definite kernel** if every kernel matrix
`(k(xᵢ, xⱼ))ᵢⱼ` built from finitely many points `x₁, …, xₙ ∈ X` is symmetric positive
semidefinite. No structure is assumed on `X`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 7.3,
Definition 7.1. -/
def IsPosDefKernel (k : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X), (Matrix.of fun i j => k (x i) (x j)).PosSemidef

/-- A positive-definite kernel, viewed as a matrix indexed by the whole set `X`, is positive
semidefinite in Mathlib's sense (`Matrix.PosSemidef`, quadratic forms of finitely supported
vectors): the finitely supported quadratic form is the quadratic form of the kernel matrix on the
support. -/
theorem posSemidef_of_isPosDefKernel {k : X → X → ℝ} (hk : IsPosDefKernel k) :
    (Matrix.of k).PosSemidef := by
  classical
  refine ⟨?_, fun v => ?_⟩
  · ext a b
    have h := (hk 2 ![a, b]).1
    have := congrFun (congrFun h 1) 0
    simpa [Matrix.conjTranspose_apply] using this.symm
  · set s := v.support
    let e : Fin s.card ≃ s := s.equivFin.symm
    have hM := (hk s.card fun i => (e i : X)).2 (Finsupp.equivFunOnFinite.symm fun i => v (e i))
    have hM' : 0 ≤ ∑ i, ∑ j, v (e i) * k (e i) (e j) * v (e j) := by
      rw [Finsupp.sum_fintype _ _ (by simp)] at hM
      convert hM using 2 with i _
      rw [Finsupp.sum_fintype _ _ (by simp)]
      simp
    unfold Finsupp.sum
    simp only [star_trivial]
    change 0 ≤ ∑ a ∈ s, ∑ b ∈ s, v a * k a b * v b
    have h1 : ∀ a, ∑ b ∈ s, v a * k a b * v b = ∑ j, v a * k a (e j) * v (e j) := by
      intro a
      rw [← Finset.sum_coe_sort s]
      exact (Equiv.sum_comp e (fun b : s => v a * k a b * v b)).symm
    simp_rw [h1]
    rw [← Finset.sum_coe_sort s]
    rw [← Equiv.sum_comp e (fun a : s => ∑ j, v a * k a (e j) * v (e j))]
    exact hM'


/-- **Aronszajn's theorem**, existence of a feature map. If `k` is a positive-definite kernel on
a set `X`, there are a real Hilbert space `H` and a map `φ : X → H` with
`k(x, x') = ⟪φ(x), φ(x')⟫` for all `x, x' ∈ X`. The space is the reproducing kernel Hilbert space
of `k` (Mathlib's `RKHS.OfKernel`, the completion of the finitely supported combinations of kernel
functions), and `φ(x)` is the kernel function `k(·, x)`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 7.3,
Proposition 7.3 (the direction proved in the source only partially); N. Aronszajn, Trans. Amer.
Math. Soc. 68 (1950), 337–404. -/
theorem exists_featureMap_of_isPosDefKernel {X : Type u} {k : X → X → ℝ}
    (hk : IsPosDefKernel k) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
      (φ : X → H), ∀ x y, k x y = ⟪φ x, φ y⟫ := by
  have hpsd := posSemidef_of_isPosDefKernel hk
  have hsymm : ∀ x y, k x y = k y x := fun x y => by
    have := congrFun (congrFun hpsd.1 y) x
    simpa [Matrix.conjTranspose_apply] using this
  set K : Matrix X X (ℝ →L[ℝ] ℝ) := Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ
    with hK
  have hKpsd : K.PosSemidef := by
    rw [RKHS.posSemidef_iff_re_sum_kernel']
    refine ⟨?_, fun vv => ?_⟩
    · ext x y
      simp [K, Matrix.conjTranspose_apply, hsymm x y, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_id]
    · have h := hpsd.2 vv
      simp only [star_trivial, Matrix.of_apply] at h
      simp only [K, Matrix.of_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, RCLike.re_to_real]
      rw [Finsupp.sum_comm] at h
      refine le_of_le_of_eq h (Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      ring
  have : Fact K.PosSemidef := ⟨hKpsd⟩
  refine ⟨RKHS.OfKernel K, inferInstance, inferInstance, inferInstance,
    fun x => RKHS.kerFun (RKHS.OfKernel K) x 1, fun x y => ?_⟩
  have h := RKHS.kernel_inner (H := RKHS.OfKernel K) x y (1 : ℝ) 1
  rw [RKHS.OfKernel.kernel_ofKernel] at h
  rw [real_inner_comm, ← h]
  simp [K]


/-- A kernel given by inner products of features, `k(x, x') = ⟪φ(x), φ(x')⟫`, is positive
definite: each kernel matrix is the Gram matrix of the features.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 7.3,
proof of Proposition 7.3 (the direction proved there). -/
theorem isPosDefKernel_of_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k : X → X → ℝ} (φ : X → H) (hk : ∀ x y, k x y = ⟪φ x, φ y⟫) : IsPosDefKernel k := by
  intro n x
  have : (Matrix.of fun i j => k (x i) (x j)) = Matrix.gram ℝ (fun i => φ (x i)) := by
    ext i j
    simp [Matrix.gram, hk]
  rw [this]
  exact Matrix.posSemidef_gram ℝ _

/-- **Aronszajn's theorem.** A real function `k` on `X × X` is a positive-definite kernel if and
only if there are a real Hilbert space `H` and a map `φ : X → H` with `k(x, x') = ⟪φ(x), φ(x')⟫`
for all `x, x' ∈ X`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 7.3,
Proposition 7.3; N. Aronszajn, Trans. Amer. Math. Soc. 68 (1950), 337–404. -/
theorem isPosDefKernel_iff_exists_featureMap {X : Type u} {k : X → X → ℝ} :
    IsPosDefKernel k ↔ ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (φ : X → H), ∀ x y, k x y = ⟪φ x, φ y⟫ := by
  refine ⟨exists_featureMap_of_isPosDefKernel, ?_⟩
  rintro ⟨H, _, _, _, φ, hφ⟩
  exact isPosDefKernel_of_eq_inner φ hφ

end MathlibExt.Analysis.InnerProductSpace.PositiveDefiniteKernel
