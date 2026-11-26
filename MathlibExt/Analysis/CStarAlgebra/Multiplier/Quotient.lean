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

public import MathlibExt.Analysis.CStarAlgebra.Multiplier.IdealInvariant
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Multipliers on a closed-ideal quotient

Let `I` be a closed two-sided star ideal of nonunital C-star `B` and `q : B → B/I` the quotient.
Ideal invariance lets each multiplier `m = (L_m,R_m)` descend by `L̄_m([b]) = [L_m b]` and
`R̄_m([b]) = [R_m b]`.

These maps form a multiplier of `B/I`, and the assignment `m ↦ (L̄_m,R̄_m)` is a unital complex
star-algebra homomorphism `M(B) → M(B/I)`. It uses the quotient C-star norm and includes the
zero quotient.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped MultiplierAlgebra Topology
namespace DoubleCentralizer
universe uB
variable {B : Type uB} [NonUnitalCStarAlgebra B]

/-- **Left centralizer on the quotient.** For nonunital complex C-star `B`, a closed two-sided
star ideal `I`, and `m : M(B)`, the continuous complex-linear map on `B/I` is `quotientFst I m
[b] = [m.fst b]`. -/
def quotientFst (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) : I.Quotient →L[ℂ] I.Quotient :=
  (NonUnitalStarSubalgebra.quotientSubmodule I.carrier).liftQL
    ((NonUnitalStarSubalgebra.quotientSubmodule I.carrier).mkQL.comp m.fst) (by
      intro x hx
      change (Submodule.Quotient.mk (m.fst x) : I.Quotient) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (NonUnitalStarSubalgebra.quotientSubmodule I.carrier)).2 (fst_mem_closedStarIdeal I m hx))

/-- **Right centralizer on the quotient.** For nonunital complex C-star `B`, a closed two-sided
star ideal `I`, and `m : M(B)`, the continuous complex-linear map on `B/I` is `quotientSnd I m
[b] = [m.snd b]`. -/
def quotientSnd (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) : I.Quotient →L[ℂ] I.Quotient :=
  (NonUnitalStarSubalgebra.quotientSubmodule I.carrier).liftQL
    ((NonUnitalStarSubalgebra.quotientSubmodule I.carrier).mkQL.comp m.snd) (by
      intro x hx
      change (Submodule.Quotient.mk (m.snd x) : I.Quotient) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (NonUnitalStarSubalgebra.quotientSubmodule I.carrier)).2 (snd_mem_closedStarIdeal I m hx))

/-- **Left quotient action on a representative.** For nonunital complex C-star `B`, a closed
two-sided star ideal `I`, and `m : M(B)`, `quotientFst I m (Submodule.Quotient.mk b) =
Submodule.Quotient.mk (m.fst b)`. -/
theorem quotientFst_mk (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    quotientFst I m (Submodule.Quotient.mk b) = (Submodule.Quotient.mk (m.fst b) : I.Quotient) := rfl

/-- **Right quotient action on a representative.** For nonunital complex C-star `B`, a closed
two-sided star ideal `I`, and `m : M(B)`, `quotientSnd I m (Submodule.Quotient.mk b) =
Submodule.Quotient.mk (m.snd b)`. -/
theorem quotientSnd_mk (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    quotientSnd I m (Submodule.Quotient.mk b) = (Submodule.Quotient.mk (m.snd b) : I.Quotient) := rfl

/-- **Multiplier induced on a coefficient quotient.** For nonunital complex C-star `B`, a closed
two-sided star ideal `I`, and `m : M(B)`, the pair of descended centralizers defines
`quotientMultiplier I m : M(B/I)`, with actions `[b] ↦ [m.fst b]` and `[b] ↦ [m.snd b]`. -/
def quotientMultiplier (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    𝓜(ℂ, I.Quotient) := by
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact
    { fst := quotientFst I m
      snd := quotientSnd I m
      central := by
        intro x y
        obtain ⟨a, rfl⟩ := I.quotientMap_surjective x
        obtain ⟨b, rfl⟩ := I.quotientMap_surjective y
        let q : B →⋆ₙₐ[ℂ] I.Quotient := I.quotientMap
        change q (m.snd a) * q b = q a * q (m.fst b)
        exact (map_mul q _ _).symm.trans ((congrArg q (m.central a b)).trans (map_mul q _ _)) }

/-- **Left component of a quotient multiplier.** For nonunital complex C-star `B`, a closed
two-sided star ideal `I`, and `m : M(B)`, for `q = I.quotientMap`, `(quotientMultiplier I
m).fst (q b) = q (m.fst b)`. -/
theorem quotientMultiplier_fst_quotientMap (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    (quotientMultiplier I m).fst (I.quotientMap b) = I.quotientMap (m.fst b) := rfl

/-- **Right component of a quotient multiplier.** For nonunital complex C-star `B`, a closed
two-sided star ideal `I`, and `m : M(B)`, for `q = I.quotientMap`, `(quotientMultiplier I
m).snd (q b) = q (m.snd b)`. -/
theorem quotientMultiplier_snd_quotientMap (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    (quotientMultiplier I m).snd (I.quotientMap b) = I.quotientMap (m.snd b) := rfl

/-- **Star homomorphism of quotient multipliers.** For a closed two-sided star ideal `I` of
nonunital C-star `B`, `quotientMultiplierHom I : M(B) → M(B/I)` is the unital complex
star-algebra homomorphism determined by the two descended centralizer actions. -/
def quotientMultiplierHom (I : ClosedStarIdeal B) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    𝓜(ℂ, B) →⋆ₐ[ℂ] 𝓜(ℂ, I.Quotient) := by
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  exact
    { toFun := quotientMultiplier I
      map_one' := by
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_fst_quotientMap, one_fst, one_apply_eq_self]
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_snd_quotientMap, one_snd, one_apply_eq_self]
      map_zero' := by
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_fst_quotientMap, zero_fst, ContinuousLinearMap.zero_apply, map_zero]
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_snd_quotientMap, zero_snd, ContinuousLinearMap.zero_apply, map_zero]
      map_add' := by
        intro m n
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_fst_quotientMap, add_fst, ContinuousLinearMap.add_apply, map_add]
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_snd_quotientMap, add_snd, ContinuousLinearMap.add_apply, map_add]
      map_mul' := by
        intro m n
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_fst_quotientMap, mul_fst, mul_apply_eq_comp]
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_snd_quotientMap, mul_snd, mul_apply_eq_comp]
      commutes' := by
        intro c
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_fst_quotientMap, algebraMap_fst,
            ContinuousLinearMap.algebraMap_apply, map_smul]
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          simp only [quotientMultiplier_snd_quotientMap, algebraMap_snd,
            ContinuousLinearMap.algebraMap_apply, map_smul]
      map_star' := by
        intro m
        apply DoubleCentralizer.ext ℂ I.Quotient
        apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro z
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          change I.quotientMap (star (m.snd (star b))) =
            star ((quotientMultiplier I m).snd (star (I.quotientMap b)))
          rw [← map_star I.quotientMap b, quotientMultiplier_snd_quotientMap]
          exact map_star I.quotientMap _
        · obtain ⟨b, rfl⟩ := I.quotientMap_surjective z
          change I.quotientMap (star (m.fst (star b))) =
            star ((quotientMultiplier I m).fst (star (I.quotientMap b)))
          rw [← map_star I.quotientMap b, quotientMultiplier_fst_quotientMap]
          exact map_star I.quotientMap _ }

end DoubleCentralizer
