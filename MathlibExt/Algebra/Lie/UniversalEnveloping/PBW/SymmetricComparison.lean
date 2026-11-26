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
# The symmetric algebra in PBW graded coordinates

Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L an ordered basis. The
basis identifies Sym_R(L) with MvPolynomial I R, and the complete graded PBW coordinates
identify the associated graded quotient model with the same polynomial algebra.

Composing these equivalences gives Sym_R(L) ≃ₐ[R] PBW.AssociatedGraded(b). It sends each
symmetric generator x to the degree-one symbol of the enveloping generator ι(x), so its
forward map is the universal symmetric lift of that symbol map.
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

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I.
Define an R-linear map L → PBW.AssociatedGraded(b) by x ↦ symbol_1(ι(x)). The enveloping
generator ι(x) lies in D_1, and its class modulo the degree-zero stage is inserted in the
degree-one quotient component. -/
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

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R, compose
Sym_R(L) ≃ₐ[R] MvPolynomial I R with the inverse PBW graded polynomial equivalence. This gives
Sym_R(L) ≃ₐ[R] PBW.AssociatedGraded(b). The maps use the same basis variables and preserve the
R-algebra operations. -/
def symmetricPBWEquiv (b : Module.Basis I R L) :
    SymmetricAlgebra R L ≃ₐ[R] AssociatedGraded b :=
  (SymmetricAlgebra.equivMvPolynomial b).trans (associatedGradedAlgEquiv b).symm

/-- Let b : Basis I R L be an ordered basis over a commutative ring R and x ∈ L. The symmetric PBW
equivalence satisfies e_b(ι_Sym(x)) = generatorSymbol_b(x) = symbol_1(ι_U(x)). Thus the
symmetric and enveloping generators correspond through the degree-one quotient symbol of the
same Lie element. -/
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

/-- For an ordered basis b : Basis I R L of an R-Lie algebra over a commutative ring R,
SymmetricAlgebra.lift(generatorSymbol_b) equals the R-algebra homomorphism underlying the
symmetric PBW equivalence. Both have domain Sym_R(L), codomain PBW.AssociatedGraded(b), and
send the generator x to symbol_1(ι_U(x)). -/
theorem symmetricLift_generatorSymbol_eq (b : Module.Basis I R L) :
    SymmetricAlgebra.lift (generatorSymbol b) = (symmetricPBWEquiv b).toAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro x
  change SymmetricAlgebra.lift (generatorSymbol b) (SymmetricAlgebra.ι R L x) =
    symmetricPBWEquiv b (SymmetricAlgebra.ι R L x)
  rw [SymmetricAlgebra.lift_ι_apply, symmetricPBWEquiv_ι_apply]

/-- Let R be a commutative ring, L an R-Lie algebra, and b : Basis I R L with LinearOrder I. The
universal R-algebra map Sym_R(L) → PBW.AssociatedGraded(b) extending x ↦ symbol_1(ι_U(x)) is
bijective. This follows from its equality with the symmetric PBW equivalence; the chosen basis
is the only module-structure hypothesis. -/
theorem symmetricLift_generatorSymbol_bijective (b : Module.Basis I R L) :
    Function.Bijective (SymmetricAlgebra.lift (generatorSymbol b)) := by
  rw [symmetricLift_generatorSymbol_eq]
  exact (symmetricPBWEquiv b).bijective

end UniversalEnvelopingAlgebra.PBW
