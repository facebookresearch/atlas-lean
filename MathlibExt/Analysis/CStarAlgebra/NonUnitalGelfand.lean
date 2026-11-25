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

public import MathlibExt.Analysis.Normed.Algebra.NonUnitalGelfand
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# The actual nonunital C-star Gelfand evaluation map

The existing C0-valued nonunital Gelfand map preserves star on a general
nonunital complex C-star algebra. Each original character is extended by
Unitization.lift to the actual C-star unitization; the stock unital character
star law then restricts back along the original inclusion. No unit,
commutativity, nonzero, selected model or isomorphism premise is required.
The pointwise star law also applies to arbitrary raw complex algebra homomorphisms,
including zero, without assuming continuity. This defining map asserts no
isometry or surjectivity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ZeroAtInfty

namespace WeakDual

universe uA
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Characters preserve the involution.** Let `A` be a nonunital complex C*-algebra. Every nonunital
complex algebra homomorphism `φ : A → ℂ` satisfies `φ(a*) = conjugate(φ(a))` for every `a ∈ A`. -/
theorem character_apply_star_of_nonunital (phi : A →ₙₐ[ℂ] ℂ) (a : A) :
    phi (star a) = star (phi a) := by
  let psi : characterSpace ℂ (Unitization ℂ A) :=
    CharacterSpace.equivAlgHom.symm (Unitization.lift phi)
  have hpsi (x : A) : psi (x : Unitization ℂ A) = phi x := by
    change (Unitization.lift phi) (x : Unitization ℂ A) = phi x
    change algebraMap ℂ ℂ 0 + phi x = phi x
    rw [map_zero, zero_add]
  calc
    phi (star a) = psi ((star a : A) : Unitization ℂ A) := (hpsi (star a)).symm
    _ = psi (star (a : Unitization ℂ A)) := congrArg psi (Unitization.inr_star a)
    _ = star (psi (a : Unitization ℂ A)) := map_star psi (a : Unitization ℂ A)
    _ = star (phi a) := congrArg star (hpsi a)

/-- **Nonunital Gelfand star transform.** Let `A` be a nonunital complex C*-algebra. Character
evaluation gives the nonunital complex star homomorphism `A → C₀(Δ(A),ℂ)`, where `Δ(A)` is the
pointwise-topologized space of nonzero complex characters. -/
def nonUnitalGelfandStarTransform : A →⋆ₙₐ[ℂ] C₀(characterSpace ℂ A, ℂ) :=
  { nonUnitalGelfandTransform (A := A) with
    map_star' a := by
      apply ZeroAtInftyContinuousMap.ext
      intro phi
      change phi (star a) = star (phi a)
      exact character_apply_star_of_nonunital (CharacterSpace.toNonUnitalAlgHom phi) a }

/-- **Algebra map of the nonunital Gelfand star transform.** Let `A` be a nonunital complex C*-algebra.
Forgetting preservation of star from the Gelfand star transform recovers the character-evaluation
nonunital complex algebra homomorphism. -/
@[simp]
theorem nonUnitalGelfandStarTransform_toNonUnitalAlgHom :
    (nonUnitalGelfandStarTransform (A := A)).toNonUnitalAlgHom =
      (nonUnitalGelfandTransform : A →ₙₐ[ℂ] C₀(characterSpace ℂ A, ℂ)) := rfl

/-- **Evaluation of the nonunital Gelfand transform.** Let `A` be a nonunital complex C*-algebra. For `a
∈ A` and a nonzero complex character `φ`, the Gelfand transform of `a` has value `φ(a)` at `φ`. -/
@[simp]
theorem nonUnitalGelfandStarTransform_apply (a : A) (phi : characterSpace ℂ A) :
    nonUnitalGelfandStarTransform a phi = phi a := rfl

end WeakDual

end
