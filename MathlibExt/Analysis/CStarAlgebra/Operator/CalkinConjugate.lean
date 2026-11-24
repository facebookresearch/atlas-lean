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

public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Actual unitary transport of Calkin classes

The original Hilbert unitary acts by the stock `conjStarAlgEquiv` on bounded
operators. Compactness is preserved by the stock two composition laws, so
the existing star-ideal quotient lift gives the actual unital Calkin map.
The quotient carrier and Hilbert dictionaries are unchanged.

This constructor is needed to descend continuous functional calculus to
the original compact-unitary Ext(X) quotient. No classification or
unitary-equivalence theorem is supplied as an input or used as a witness.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped Topology

namespace CalkinAlgebra

universe uH uK

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Hilbert-unitary conjugation preserves compactness on the original operator spaces. -/
theorem conjugate_compact (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) : IsCompactOperator (U.conjStarAlgEquiv T) := by
  rcases hT with ⟨C, hC, hTC⟩
  refine ⟨U '' C, hC.image U.continuous, ?_⟩
  have hcont : Filter.Tendsto (U.symm : K → H) (𝓝 (0 : K)) (𝓝 (0 : H)) := by
    simpa only [map_zero] using U.symm.continuous.tendsto (0 : K)
  exact Filter.mem_of_superset (hcont.eventually hTC) fun x hx =>
    ⟨T (U.symm x), hx, rfl⟩

/-- Actual unitary transport of the original Calkin classes, using the existing quotient lift. -/
def conjugateStarAlgHom (U : H ≃ₗᵢ[ℂ] K) :
    CalkinAlgebra ℂ H →⋆ₐ[ℂ] CalkinAlgebra ℂ K := by
  let I := compactEndomorphismClosedStarIdeal (H := H)
  letI : I.carrier.IsTwoSided := I.isTwoSided
  let f : (H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra ℂ K :=
    (classStarMap (H := K)).comp U.conjStarAlgEquiv.toStarAlgHom
  let g : CalkinAlgebra ℂ H →⋆ₙₐ[ℂ] CalkinAlgebra ℂ K :=
    NonUnitalStarSubalgebra.Quotient.lift I.carrier f.toNonUnitalStarAlgHom
    (fun T hT => by
      apply (classStarMap_eq_zero_iff (H := K) (U.conjStarAlgEquiv T)).mpr
      exact conjugate_compact U T (show IsCompactOperator T from hT))
  exact
    { __ := g
      map_one' := by
        rw [← map_one (classStarMap (H := H))]
        change f (1 : H →L[ℂ] H) = (1 : CalkinAlgebra ℂ K)
        exact map_one f
      commutes' := by
        intro z
        rw [← AlgHomClass.commutes (classStarMap (H := H)) z]
        change f (algebraMap ℂ (H →L[ℂ] H) z) = algebraMap ℂ (CalkinAlgebra ℂ K) z
        exact f.toAlgHom.commutes z }

/-- The descended map keeps the literal original unitary action on every operator representative. -/
@[simp]
theorem conjugateStarAlgHom_classStarMap (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    conjugateStarAlgHom U (classStarMap (H := H) T) =
      classStarMap (H := K) (U.conjStarAlgEquiv T) := rfl

/-- The actual Calkin transport is continuous by the canonical C-star contractivity bound. -/
theorem conjugateStarAlgHom_continuous (U : H ≃ₗᵢ[ℂ] K) :
    Continuous (conjugateStarAlgHom U) := by
  exact AddMonoidHomClass.continuous_of_bound (conjugateStarAlgHom U) 1 (by
    intro a
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (conjugateStarAlgHom U) a)

end CalkinAlgebra

end
