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
# Actual multiplier descent to the original closed-ideal quotient

Both original continuous linear multiplier operators descend by the stock
submodule quotient lift. Their kernel condition is the proved ideal
invariance. The original centrality identity descends through the actual
quotient projection and supplies a genuine DoubleCentralizer. Every
zero/add/mul/star/unit/scalar law of the resulting map is computed on actual
quotient representatives. No quotient model, extended multiplier map or
nontriviality condition is an input; the zero quotient remains included.
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

/-- The descended first operator uses the actual quotient norm/topology and proved kernel condition. -/
def quotientFst (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) : I.Quotient →L[ℂ] I.Quotient :=
  (NonUnitalStarSubalgebra.quotientSubmodule I.carrier).liftQL
    ((NonUnitalStarSubalgebra.quotientSubmodule I.carrier).mkQL.comp m.fst) (by
      intro x hx
      change (Submodule.Quotient.mk (m.fst x) : I.Quotient) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (NonUnitalStarSubalgebra.quotientSubmodule I.carrier)).2 (fst_mem_closedStarIdeal I m hx))

/-- The descended second operator uses the same actual quotient structure and kernel condition. -/
def quotientSnd (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) : I.Quotient →L[ℂ] I.Quotient :=
  (NonUnitalStarSubalgebra.quotientSubmodule I.carrier).liftQL
    ((NonUnitalStarSubalgebra.quotientSubmodule I.carrier).mkQL.comp m.snd) (by
      intro x hx
      change (Submodule.Quotient.mk (m.snd x) : I.Quotient) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (NonUnitalStarSubalgebra.quotientSubmodule I.carrier)).2 (snd_mem_closedStarIdeal I m hx))

/-- The original first-component value is exactly preserved on every original quotient representative. -/
theorem quotientFst_mk (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    quotientFst I m (Submodule.Quotient.mk b) = (Submodule.Quotient.mk (m.fst b) : I.Quotient) := rfl

/-- The original second-component value is exactly preserved on every original quotient representative. -/
theorem quotientSnd_mk (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    quotientSnd I m (Submodule.Quotient.mk b) = (Submodule.Quotient.mk (m.snd b) : I.Quotient) := rfl

/-- The actual descended pair satisfies the original centrality identity on the quotient. -/
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

/-- The descended multiplier retains the original first operator on the canonical quotient map. -/
theorem quotientMultiplier_fst_quotientMap (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    (quotientMultiplier I m).fst (I.quotientMap b) = I.quotientMap (m.fst b) := rfl

/-- The descended multiplier retains the original second operator on the same quotient map. -/
theorem quotientMultiplier_snd_quotientMap (I : ClosedStarIdeal B) (m : 𝓜(ℂ, B)) (b : B) :
    letI : I.carrier.IsTwoSided := I.isTwoSided;
    letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra;
    (quotientMultiplier I m).snd (I.quotientMap b) = I.quotientMap (m.snd b) := rfl

/-- The actual closed-ideal multiplier quotient map is a unital star-algebra homomorphism. -/
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
