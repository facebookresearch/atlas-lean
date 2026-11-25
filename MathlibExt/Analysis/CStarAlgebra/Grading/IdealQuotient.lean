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

public import MathlibExt.Analysis.CStarAlgebra.Grading
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient

import Mathlib.Tactic.FinCases

/-!
# Gradings on canonical closed-ideal quotients

An ideal invariant under the grading generator inherits the quotient grading
on its existing `Submodule.Quotient` carrier. The involutive generator
descends by the existing quotient-map API; the quotient's norm, star,
completeness and C-star structure are not reconstructed.

The convention is the usual `ℤ₂`-grading convention in Blackadar,
*K-Theory for Operator Algebras*, second edition, §§14.1 and 15.13: the
quotient action is induced by the action of the original graded algebra.
Only actual generator invariance is assumed. No quotient grading, output
equivalence, section, separability or unit is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra NonUnitalStarSubalgebra.Quotient

namespace CStarGrading

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable (gamma : CStarGrading A) (I : ClosedStarIdeal A)
variable (hI : ∀ a : A, a ∈ I → gamma.generatorAut a ∈ I)

/-- **Generator on a graded ideal quotient.** Let `A` be a nonunital complex C*-algebra with grading `γ`
and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. The
generator descends to the complex star-algebra automorphism `[a] ↦ [σ(a)]` of `A/I`. -/
def quotientGenerator :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    I.Quotient ≃⋆ₐ[ℂ] I.Quotient := by
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  have hInvariant : Set.MapsTo gamma.generatorAut.toNonUnitalStarAlgHom I.carrier I.carrier :=
    fun a ha => hI a ha
  let descended : I.Quotient →⋆ₙₐ[ℂ] I.Quotient :=
    NonUnitalStarSubalgebra.Quotient.map I.carrier I.carrier
      gamma.generatorAut.toNonUnitalStarAlgHom hInvariant
  have hSquare : descended.comp descended = NonUnitalStarAlgHom.id ℂ I.Quotient := by
    apply NonUnitalStarSubalgebra.Quotient.hom_ext I.carrier
    apply NonUnitalStarAlgHom.ext
    intro a
    change NonUnitalStarSubalgebra.Quotient.map I.carrier I.carrier
        gamma.generatorAut.toNonUnitalStarAlgHom hInvariant
        (NonUnitalStarSubalgebra.Quotient.map I.carrier I.carrier
          gamma.generatorAut.toNonUnitalStarAlgHom hInvariant
          (NonUnitalStarSubalgebra.Quotient.mk I.carrier a)) =
      NonUnitalStarSubalgebra.Quotient.mk I.carrier a
    rw [NonUnitalStarSubalgebra.Quotient.map_mk, NonUnitalStarSubalgebra.Quotient.map_mk]
    exact congrArg (NonUnitalStarSubalgebra.Quotient.mk I.carrier) (gamma.generator_involutive a)
  exact StarAlgEquiv.ofNonUnitalStarAlgHom descended descended hSquare hSquare

/-- **Formula for a quotient grading generator.** Let `A` be a nonunital complex C*-algebra with grading
`γ` and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. For
every `a ∈ A`, the descended generator sends its quotient class to `[σ(a)]`. -/
theorem quotientGenerator_quotientMap (a : A) :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    quotientGenerator gamma I hI (I.quotientMap a) = I.quotientMap (gamma.generatorAut a) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact NonUnitalStarSubalgebra.Quotient.map_mk I.carrier I.carrier
    gamma.generatorAut.toNonUnitalStarAlgHom (fun a ha => hI a ha) a

/-- **Grading on a closed star-ideal quotient.** Let `A` be a nonunital complex C*-algebra with grading
`γ` and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. The
descended generator defines a `ℤ/2ℤ` grading of `A/I` with its quotient C*-norm. -/
def quotient :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    CStarGrading I.Quotient := by
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact ofInvolution (quotientGenerator gamma I hI) (quotientGenerator gamma I hI).left_inv

/-- **Generator of the quotient grading.** Let `A` be a nonunital complex C*-algebra with grading `γ`
and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. The
degree-one automorphism of the quotient grading is the descended automorphism `[a] ↦ [σ(a)]`. -/
@[simp]
theorem quotient_generatorAut :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    (quotient gamma I hI).generatorAut = quotientGenerator gamma I hI := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact ofInvolution_generatorAut _ _

/-- **Graded quotient projection.** Let `A` be a nonunital complex C*-algebra with grading `γ` and
generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. The quotient
projection `A → A/I` is equivariant for the original and descended gradings. -/
def quotientProjection :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    Hom gamma (quotient gamma I hI) := by
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact
    { toNonUnitalStarAlgHom := I.quotientMap
      equivariant' := by
        intro n a
        fin_cases n
        · change I.quotientMap (PointNormCStarAddAction.aut gamma 0 a) =
            PointNormCStarAddAction.aut (quotient gamma I hI) 0 (I.quotientMap a)
          simp [PointNormCStarAddAction.aut_zero]
        · change I.quotientMap (gamma.generatorAut a) =
            (quotient gamma I hI).generatorAut (I.quotientMap a)
          rw [quotient_generatorAut]
          exact (quotientGenerator_quotientMap gamma I hI a).symm }

/-- **Underlying star map of a graded quotient projection.** Let `A` be a nonunital complex C*-algebra
with grading `γ` and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying
`σ(I) ⊆ I`. Forgetting grading equivariance leaves the canonical nonunital complex star quotient
homomorphism `a ↦ [a]`. -/
@[simp]
theorem quotientProjection_toNonUnitalStarAlgHom :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    (quotientProjection gamma I hI).toNonUnitalStarAlgHom = I.quotientMap := rfl

/-- **Every degree acts on quotient classes.** Let `A` be a nonunital complex C*-algebra with grading
`γ` and generator `σ`, and let `I ⊆ A` be a closed two-sided star ideal satisfying `σ(I) ⊆ I`. For
every `n ∈ ℤ/2ℤ` and `a ∈ A`, the quotient grading sends `[a]` to `[γ(n)a]`. -/
theorem quotientMap_equivariant (n : ZMod 2) (a : A) :
    letI : I.carrier.IsTwoSided := I.isTwoSided
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
    I.quotientMap (PointNormCStarAddAction.aut gamma n a) =
      PointNormCStarAddAction.aut (quotient gamma I hI) n (I.quotientMap a) := by
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact Hom.equivariant (quotientProjection gamma I hI) n a

end CStarGrading
