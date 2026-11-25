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

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-!
# The symmetric algebra and PBW graded coordinates

For a chosen ordered basis of a Lie algebra over a commutative ring, sending each
symmetric-algebra generator to its degree-one symbol defines an algebra equivalence with the
PBW graded model.

Polynomial coordinates identify its underlying map with the universal symmetric-algebra lift
of the generator-symbol map.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

attribute [local instance] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The Lie generators, mapped to their degree-one symbols. -/
def generatorSymbol (b : Module.Basis I R L) : L →ₗ[R] AssociatedGraded b :=
  (symbol b 1).comp
    ((UniversalEnvelopingAlgebra.ι R : L →ₗ⁅R⁆ U).toLinearMap.codRestrict
      (UniversalEnvelopingAlgebra.degreeFiltration R L 1)
      (UniversalEnvelopingAlgebra.ι_mem_degreeFiltration R L))

@[simp]
theorem generatorSymbol_apply (b : Module.Basis I R L) (x : L) :
    generatorSymbol b x = symbol b 1 ⟨UniversalEnvelopingAlgebra.ι R x,
      UniversalEnvelopingAlgebra.ι_mem_degreeFiltration R L x⟩ := rfl

private theorem polynomialCoordinates_ι_basis (b : Module.Basis I R L) (i : I) :
    polynomialCoordinates b (UniversalEnvelopingAlgebra.ι R (b i)) = MvPolynomial.X i := by
  let xs : OrderedWord I := ⟨[i], by simp only [List.pairwise_singleton]⟩
  have h := polynomialCoordinates_orderedWord b xs
  change polynomialCoordinates b (UniversalEnvelopingAlgebra.ι R (b i) * 1) =
    MvPolynomial.monomial (wordExponent [i]) 1 at h
  simpa only [mul_one, wordExponent_singleton, MvPolynomial.X] using h

theorem associatedGradedAlgEquiv_generatorSymbol_basis (b : Module.Basis I R L) (i : I) :
    associatedGradedAlgEquiv b (generatorSymbol b (b i)) = MvPolynomial.X i := by
  rw [generatorSymbol_apply, associatedGradedAlgEquiv_symbol, polynomialCoordinates_ι_basis]
  change MvPolynomial.homogeneousComponent 1
    (MvPolynomial.monomial (Finsupp.single i 1) (1 : R)) = _
  rw [MvPolynomial.homogeneousComponent_of_mem
    (MvPolynomial.isHomogeneous_monomial (1 : R)
      (show (Finsupp.single i 1).degree = 1 by rw [Finsupp.degree_single])), if_pos rfl]
  rfl

/-- The symmetric/associated-graded algebra equivalence. -/
def symmetricPBWEquiv (b : Module.Basis I R L) :
    SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded b :=
  (SymmetricAlgebra.equivMvPolynomial b).trans (associatedGradedAlgEquiv b).symm

/-- The constructed algebra equivalence sends every symmetric generator to the symbol of the same
enveloping algebra generator. -/
theorem symmetricPBWEquiv_ι_apply (b : Module.Basis I R L) (x : L) :
    symmetricPBWEquiv b (SymmetricAlgebra.ι R L x) = generatorSymbol b x := by
  have h : (symmetricPBWEquiv b).toLinearMap.comp (SymmetricAlgebra.ι R L) =
      generatorSymbol b := by
    apply b.ext
    intro i
    apply (associatedGradedAlgEquiv b).injective
    change associatedGradedAlgEquiv b
      ((associatedGradedAlgEquiv b).symm
        (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R L (b i)))) = _
    rw [AlgEquiv.apply_symm_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply,
      associatedGradedAlgEquiv_generatorSymbol_basis]
  exact LinearMap.congr_fun h x

/-- The canonical symmetric lift is exactly the constructed PBW map. -/
theorem symmetricLift_generatorSymbol_eq (b : Module.Basis I R L) :
    SymmetricAlgebra.lift (generatorSymbol b) = (symmetricPBWEquiv b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change SymmetricAlgebra.lift (generatorSymbol b) (SymmetricAlgebra.ι R L x) =
    symmetricPBWEquiv b (SymmetricAlgebra.ι R L x)
  rw [SymmetricAlgebra.lift_ι_apply, symmetricPBWEquiv_ι_apply]

/-- PBW in its canonical symmetric-algebra form on the associated graded carrier. The input is
only a basis of the underlying module. -/
theorem symmetricLift_generatorSymbol_bijective (b : Module.Basis I R L) :
    Function.Bijective (SymmetricAlgebra.lift (generatorSymbol b)) := by
  rw [symmetricLift_generatorSymbol_eq]
  exact (symmetricPBWEquiv b).bijective

end UniversalEnvelopingAlgebra.PBW
