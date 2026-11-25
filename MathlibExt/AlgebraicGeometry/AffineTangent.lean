/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import MathlibExt.AlgebraicGeometry.TangentSpace

/-!
# Affine Zariski closures and tangent spaces

For a field `k` and a coordinate type `σ`, point sets of `σ → k` are handled through Mathlib's
`MvPolynomial.vanishingIdeal` and `MvPolynomial.zeroLocus`.

## Main definitions

* `zariskiClosure S`: the Zariski closure `V(I(S))` of a set of points.
* `differential f p`: for finite `σ`, the differential `v ↦ ∑ i, (∂f/∂xᵢ)(p) vᵢ` of a polynomial
  `f` at a point `p`.
* `tangentIdeal I p`: the common kernel of the differentials at `p` of the elements of the ideal
  `I`. When `p` lies on the zero locus of `I`, this is the Zariski tangent space at `p` of the
  closed subscheme of affine space cut out by `I`.
* `tangentSet S p`: `tangentIdeal` of the vanishing ideal `I(S)` of a set of `k`-points, i.e. the
  tangent space of the reduced closed subscheme defined by `I(S)`, whose `k`-points form
  `zariskiClosure S`. Over a field that is not algebraically closed, `I(S)` need not be the ideal
  of a given reduced scheme with these `k`-points.
* `additionImageClosure X Y`: the Zariski closure of the image `X + Y` of the addition map.

## Main results

* `tangentIdeal_span`: at a common zero of a set of polynomials, the tangent space of the ideal
  they generate is cut out by their differentials alone.
* `differential_eq_totalDerivativeAtLin` and `tangentIdeal_eq_tangentSpaceIdeal`: for `σ = Fin n`,
  `differential` and `tangentIdeal` are `MvPolynomial.totalDerivativeAtLin` and
  `MvPolynomial.tangentSpaceIdeal` from `MathlibExt.AlgebraicGeometry.TangentSpace`. They
  generalize that API from `Fin n` to an arbitrary finite coordinate type, such as the matrix
  coordinates `Fin m × Fin n`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffineTangent

open MvPolynomial
open scoped Pointwise

variable {k σ : Type*} [Field k]

/-- The Zariski closure `V(I(S))` of a set `S` of points of `σ → k`: the common zero locus of all
polynomials vanishing on `S`. It is the smallest set containing `S` that is the zero locus of an
ideal. -/
def zariskiClosure (S : Set (σ → k)) : Set (σ → k) :=
  zeroLocus k (vanishingIdeal k S)

theorem mem_zariskiClosure_iff {S : Set (σ → k)} {x : σ → k} :
    x ∈ zariskiClosure S ↔
      ∀ f : MvPolynomial σ k, (∀ y ∈ S, eval y f = 0) → eval x f = 0 := by
  simp [zariskiClosure]

theorem subset_zariskiClosure (S : Set (σ → k)) : S ⊆ zariskiClosure S :=
  zeroLocus_vanishingIdeal_le S

/-- The closure of `S` lies in every zero locus containing `S`. -/
theorem zariskiClosure_subset_zeroLocus {S : Set (σ → k)} {I : Ideal (MvPolynomial σ k)}
    (h : S ⊆ zeroLocus k I) : zariskiClosure S ⊆ zeroLocus k I :=
  zeroLocus_anti_mono (le_zeroLocus_iff_le_vanishingIdeal.mp h)

theorem zariskiClosure_mono {S T : Set (σ → k)} (h : S ⊆ T) :
    zariskiClosure S ⊆ zariskiClosure T :=
  zeroLocus_anti_mono (vanishingIdeal_anti_mono h)

/-- The zero locus of an ideal is Zariski closed. -/
theorem zariskiClosure_zeroLocus (I : Ideal (MvPolynomial σ k)) :
    zariskiClosure (zeroLocus k I) = zeroLocus k I :=
  (subset_zariskiClosure _).antisymm' (zeroLocus_anti_mono (le_vanishingIdeal_zeroLocus I))

theorem zariskiClosure_zariskiClosure (S : Set (σ → k)) :
    zariskiClosure (zariskiClosure S) = zariskiClosure S :=
  zariskiClosure_zeroLocus _

@[simp]
theorem zariskiClosure_empty : zariskiClosure (∅ : Set (σ → k)) = ∅ := by
  rw [zariskiClosure, vanishingIdeal_empty, zeroLocus_top]
  rfl

/-- The Zariski closure of the image `X + Y` of the addition map `X × Y → (σ → k)`. -/
def additionImageClosure (X Y : Set (σ → k)) : Set (σ → k) :=
  zariskiClosure (X + Y)

theorem add_subset_additionImageClosure (X Y : Set (σ → k)) :
    X + Y ⊆ additionImageClosure X Y :=
  subset_zariskiClosure _

variable [Fintype σ]

/-- The differential at `p` of a polynomial `f`: the linear form
`v ↦ ∑ i, (∂f/∂xᵢ)(p) * vᵢ` on `σ → k`. -/
def differential (f : MvPolynomial σ k) (p : σ → k) : (σ → k) →ₗ[k] k where
  toFun v := ∑ i : σ, eval p (pderiv i f) * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum, mul_left_comm]

theorem differential_apply (f : MvPolynomial σ k) (p v : σ → k) :
    differential f p v = ∑ i : σ, eval p (pderiv i f) * v i :=
  rfl

/-- The differential of a coordinate function is the coordinate projection. -/
@[simp]
theorem differential_X (i : σ) (p v : σ → k) : differential (X i) p v = v i := by
  rw [differential_apply, Finset.sum_eq_single i (fun j _ hji => by
    rw [pderiv_X_of_ne hji.symm, map_zero, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
    pderiv_X_self, map_one, one_mul]

@[simp]
theorem differential_C (a : k) (p : σ → k) : differential (C a) p = 0 := by
  ext v
  simp [differential_apply]

@[simp]
theorem differential_zero (p : σ → k) : differential (0 : MvPolynomial σ k) p = 0 := by
  simpa using differential_C (0 : k) p

@[simp]
theorem differential_one (p : σ → k) : differential (1 : MvPolynomial σ k) p = 0 := by
  simpa using differential_C (1 : k) p

theorem differential_add (f g : MvPolynomial σ k) (p : σ → k) :
    differential (f + g) p = differential f p + differential g p := by
  ext v
  simp [differential_apply, add_mul, Finset.sum_add_distrib]

theorem differential_neg (f : MvPolynomial σ k) (p : σ → k) :
    differential (-f) p = -differential f p := by
  ext v
  simp [differential_apply]

theorem differential_sub (f g : MvPolynomial σ k) (p : σ → k) :
    differential (f - g) p = differential f p - differential g p := by
  rw [sub_eq_add_neg, differential_add, differential_neg, ← sub_eq_add_neg]

/-- The Leibniz rule for the differential at a point. -/
theorem differential_mul (f g : MvPolynomial σ k) (p : σ → k) :
    differential (f * g) p = eval p f • differential g p + eval p g • differential f p := by
  ext v
  simp only [differential_apply, pderiv_mul, map_add, map_mul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The common kernel of the differentials at `p` of all elements of the ideal `I`. When `p` is a
common zero of `I`, this is the Zariski tangent space at `p` of the closed subscheme of `σ → k`
cut out by `I`. For `p` off the zero locus it is still defined, but it is not the tangent space of
that subscheme at a point. -/
def tangentIdeal (I : Ideal (MvPolynomial σ k)) (p : σ → k) : Submodule k (σ → k) :=
  ⨅ f ∈ I, LinearMap.ker (differential f p)

theorem mem_tangentIdeal_iff {I : Ideal (MvPolynomial σ k)} {p v : σ → k} :
    v ∈ tangentIdeal I p ↔ ∀ f ∈ I, differential f p v = 0 := by
  simp only [tangentIdeal, Submodule.mem_iInf, LinearMap.mem_ker]

/-- At a common zero `p` of a set `s` of polynomials, the tangent space of the ideal generated
by `s` is cut out by the differentials of the elements of `s`. -/
theorem tangentIdeal_span {s : Set (MvPolynomial σ k)} {p : σ → k}
    (hp : ∀ f ∈ s, eval p f = 0) :
    tangentIdeal (Ideal.span s) p = ⨅ f ∈ s, LinearMap.ker (differential f p) := by
  refine le_antisymm (le_iInf₂ fun f hf => iInf₂_le f (Ideal.subset_span hf)) fun v hv => ?_
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv
  refine mem_tangentIdeal_iff.mpr fun f hf => ?_
  suffices h : eval p f = 0 ∧ differential f p v = 0 from h.2
  induction hf using Submodule.span_induction with
  | mem g hg => exact ⟨hp g hg, hv g hg⟩
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add, differential_add, LinearMap.add_apply, hf.1, hg.1, hf.2, hg.2, add_zero]
    exact ⟨rfl, rfl⟩
  | smul a f _ hf =>
    rw [smul_eq_mul, map_mul, differential_mul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hf.1, hf.2]
    simp

/-- The tangent space at `p` of the reduced closed subscheme defined by the vanishing ideal `I(S)`
of a set `S` of `k`-points; its `k`-points form `zariskiClosure S`. It depends on `S` only through
`I(S)`, which over a field that is not algebraically closed need not be the ideal of a given
reduced scheme with these `k`-points: for the `𝔽₂`-points of the affine line, `X ^ 2 - X ∈ I(S)`
and the tangent space at `0` is zero. -/
def tangentSet (S : Set (σ → k)) (p : σ → k) : Submodule k (σ → k) :=
  tangentIdeal (vanishingIdeal k S) p

theorem mem_tangentSet_iff {S : Set (σ → k)} {p v : σ → k} :
    v ∈ tangentSet S p ↔
      ∀ f : MvPolynomial σ k, (∀ y ∈ S, eval y f = 0) → differential f p v = 0 := by
  simp [tangentSet, mem_tangentIdeal_iff]

/-- For `σ = Fin n`, `differential` is `MvPolynomial.totalDerivativeAtLin`. -/
theorem differential_eq_totalDerivativeAtLin {n : ℕ} (f : MvPolynomial (Fin n) k)
    (p : Fin n → k) : differential f p = totalDerivativeAtLin f p :=
  rfl

/-- For `σ = Fin n`, `tangentIdeal` is `MvPolynomial.tangentSpaceIdeal`. -/
theorem tangentIdeal_eq_tangentSpaceIdeal {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k))
    (p : Fin n → k) : tangentIdeal I p = tangentSpaceIdeal I p :=
  rfl

end MathlibExt.AlgebraicGeometry.AffineTangent
