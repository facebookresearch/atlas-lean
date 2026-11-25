/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The actual Hilbert sum of C-star representations

Every coordinate is an original nonunital star homomorphism on its original
complete complex Hilbert space. The bounded diagonal operator is the stock
lp.mapCLM on the same actual lp H2 carrier; its uniform coefficient bound
comes from the existing C-star map norm bound. The original map laws and
adjoint identity construct the actual direct-sum representation.

This strict constructor is needed by the original cyclic/zero-complement
decomposition and normal multiplication-operator statements. No chosen
diagonal operator, model, uniform-bound certificate, countability, unit,
nonzero or nondegeneracy premise is added. Empty indices and zero Hilbert
spaces retain their actual canonical sums and maps.

The coordinate construction and adjoint proof are by @toskua and Avocado.
The earlier fixed-coefficient `repOp` / `repHom` specialization is in
`MathlibExt/Analysis/CStarAlgebra/Landmark.lean`; its author credit is retained.
The shared nonunital core supports the original unital source through the
unital adapter below, whose only additional laws are preservation of one and
of the scalar algebra map. Both variants keep the same actual lp H2 carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace

namespace NonUnitalStarAlgHom

universe uA uI uH

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {I : Type uI} {H : I → Type uH}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- **Operator on the Hilbert direct sum.** Let `A` be a nonunital complex C*-algebra and let `(Hᵢ)ᵢ∈I`
be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be nonunital complex
star homomorphisms. For `a ∈ A`, the bounded operator on `⨁₂ Hᵢ` sends `(xᵢ)` to `(ρᵢ(a)(xᵢ))`. -/
def hilbertSumOperator (ρ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    lp H 2 →L[ℂ] lp H 2 :=
  lp.mapCLM 2 (fun i => ρ i a) (K := ‖a‖) (norm_nonneg a)
    (fun i => NonUnitalStarAlgHom.norm_apply_le (ρ i) a)

/-- **Coordinates of the Hilbert-sum operator.** Let `A` be a nonunital complex C*-algebra and let
`(Hᵢ)ᵢ∈I` be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be
nonunital complex star homomorphisms. For `a ∈ A` and `x ∈ ⨁₂ Hᵢ`, its `i` coordinate is
`ρᵢ(a)(xᵢ)`. -/
@[simp]
theorem hilbertSumOperator_apply (ρ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : I) :
    hilbertSumOperator ρ a x i = ρ i a (x i) := rfl

omit [∀ i, CompleteSpace (H i)] in
private theorem hilbertSumOperator_ext
    (T S : lp H 2 →L[ℂ] lp H 2)
    (h : ∀ (x : lp H 2) (i : I), T x i = S x i) : T = S :=
  ContinuousLinearMap.ext fun x => lp.ext (funext fun i => h x i)

/-- **Hilbert direct sum of representations.** Let `A` be a nonunital complex C*-algebra and let
`(Hᵢ)ᵢ∈I` be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be
nonunital complex star homomorphisms. The coordinatewise action defines a representation on the ℓ²
Hilbert direct sum of the `Hᵢ`, with its Hilbert norm. -/
def hilbertDirectSum (ρ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := hilbertSumOperator ρ
  map_zero' := by
    apply hilbertSumOperator_ext
    intro x i
    simp [hilbertSumOperator_apply]
  map_add' := by
    intro a b
    apply hilbertSumOperator_ext
    intro x i
    simp [hilbertSumOperator_apply]
  map_mul' := by
    intro a b
    apply hilbertSumOperator_ext
    intro x i
    simp [hilbertSumOperator_apply]
  map_smul' := by
    intro c a
    apply hilbertSumOperator_ext
    intro x i
    simp [hilbertSumOperator_apply]
  map_star' := by
    intro a
    change hilbertSumOperator ρ (star a) = star (hilbertSumOperator ρ a)
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    rw [hilbertSumOperator_apply, hilbertSumOperator_apply]
    have hstar : ρ i (star a) = ContinuousLinearMap.adjoint (ρ i a) := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact map_star (ρ i) a
    rw [hstar]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- **Coordinates of the Hilbert-sum representation.** Let `A` be a nonunital complex C*-algebra and let
`(Hᵢ)ᵢ∈I` be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be
nonunital complex star homomorphisms. For `a ∈ A`, `x ∈ ⨁₂ Hᵢ`, and `i ∈ I`, the direct-sum
representation has coordinate `ρᵢ(a)(xᵢ)`. -/
@[simp]
theorem hilbertDirectSum_apply (ρ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : I) :
    hilbertDirectSum ρ a x i = ρ i a (x i) := rfl

end NonUnitalStarAlgHom

namespace StarAlgHom

universe uA uI uH

variable {A : Type uA} [CStarAlgebra A]
variable {I : Type uI} {H : I → Type uH}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- **Hilbert direct sum of representations.** Let `A` be a unital complex C*-algebra and let `(Hᵢ)ᵢ∈I`
be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be unital complex
star homomorphisms. The coordinatewise action defines a representation on the ℓ² Hilbert direct sum
of the `Hᵢ`, with its Hilbert norm. -/
def hilbertDirectSum (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  __ := NonUnitalStarAlgHom.hilbertDirectSum (fun i => (ρ i).toNonUnitalStarAlgHom)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change ρ i (1 : A) (x i) = x i
    rw [map_one, one_apply_eq_self]
  commutes' := by
    intro c
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change ρ i (algebraMap ℂ A c) (x i) =
      (algebraMap ℂ (lp H 2 →L[ℂ] lp H 2) c x) i
    rw [AlgHomClass.commutes (ρ i) c]
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self,
      lp.coeFn_smul, Pi.smul_apply]

/-- **Coordinates of the Hilbert-sum representation.** Let `A` be a unital complex C*-algebra and let
`(Hᵢ)ᵢ∈I` be an arbitrary family of complete complex Hilbert spaces. Let `ρᵢ : A → B(Hᵢ)` be unital
complex star homomorphisms. For `a ∈ A`, `x ∈ ⨁₂ Hᵢ`, and `i ∈ I`, the direct-sum representation has
coordinate `ρᵢ(a)(xᵢ)`. -/
@[simp]
theorem hilbertDirectSum_apply (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : I) :
    hilbertDirectSum ρ a x i = ρ i a (x i) := rfl

end StarAlgHom

end
