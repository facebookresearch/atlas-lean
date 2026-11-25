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

public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Quotient
public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Outer

/-!
# Multiplier functor for surjective coefficient maps

For a surjective complex nonunital star homomorphism `ρ : B → D`, the closed kernel identifies
`D` with `B/ker ρ`. Multiplier descent and this identification give a unital star map `M(ρ) :
M(B) → M(D)` satisfying `M(ρ)(m).fst (ρ b) = ρ(m.fst b)` and `M(ρ)(m).snd (ρ b) = ρ(m.snd b)`.

It sends the embedded coefficient `b` to the embedded `ρ(b)`, so it descends to a unital map
`Q(ρ) : Q(B) → Q(D)`. The multiplier and corona quotient square commutes. Surjectivity of `ρ`
identifies `D` with its coefficient quotient and supplies these two induced star homomorphisms.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped MultiplierAlgebra
namespace DoubleCentralizer
universe uB uD
variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable {D : Type uD} [NonUnitalCStarAlgebra D]

/-- **Multiplier map of a surjective coefficient homomorphism.** For a surjective complex
nonunital star homomorphism `ρ : B → D` of C-star algebras, the unital star homomorphism `M(ρ)
: M(B) → M(D)` is characterized by its left and right actions on the images `ρ(b)`. -/
def mapOfSurjective (rho : B →⋆ₙₐ[ℂ] D) (hrho : Function.Surjective rho) :
    𝓜(ℂ, B) →⋆ₐ[ℂ] 𝓜(ℂ, D) := by
  let I := ClosedStarIdeal.ker rho
  letI : I.carrier.IsTwoSided := I.isTwoSided
  letI : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  let e : I.Quotient ≃⋆ₐ[ℂ] D := NonUnitalStarAlgHom.quotientKerEquivOfSurjective rho hrho
  exact (DoubleCentralizer.congr e).toStarAlgHom.comp (quotientMultiplierHom I)

/-- **Left multiplier action under a coefficient quotient.** For a surjective complex nonunital
star homomorphism `ρ : B → D` of C-star algebras, `(mapOfSurjective ρ hρ m).fst (ρ b) =
ρ(m.fst b)`. -/
theorem mapOfSurjective_fst (rho : B →⋆ₙₐ[ℂ] D) (hrho : Function.Surjective rho)
    (m : 𝓜(ℂ, B)) (b : B) :
    (mapOfSurjective rho hrho m).fst (rho b) = rho (m.fst b) := by
  let I := ClosedStarIdeal.ker rho
  let : I.carrier.IsTwoSided := I.isTwoSided
  let : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  let e : I.Quotient ≃⋆ₐ[ℂ] D := NonUnitalStarAlgHom.quotientKerEquivOfSurjective rho hrho
  have he (x : B) : e (I.quotientMap x) = rho x :=
    NonUnitalStarAlgHom.quotientKerEquivOfSurjective_quotientMap rho hrho x
  have hb : e.symm (rho b) = I.quotientMap b := by
    calc
      e.symm (rho b) = e.symm (e (I.quotientMap b)) := congrArg e.symm (he b).symm
      _ = I.quotientMap b := e.symm_apply_apply _
  change (DoubleCentralizer.congr e (quotientMultiplier I m)).fst (rho b) = _
  rw [congr_apply_fst, hb, quotientMultiplier_fst_quotientMap, he]

/-- **Right multiplier action under a coefficient quotient.** For a surjective complex nonunital
star homomorphism `ρ : B → D` of C-star algebras, `(mapOfSurjective ρ hρ m).snd (ρ b) =
ρ(m.snd b)`. -/
theorem mapOfSurjective_snd (rho : B →⋆ₙₐ[ℂ] D) (hrho : Function.Surjective rho)
    (m : 𝓜(ℂ, B)) (b : B) :
    (mapOfSurjective rho hrho m).snd (rho b) = rho (m.snd b) := by
  let I := ClosedStarIdeal.ker rho
  let : I.carrier.IsTwoSided := I.isTwoSided
  let : NonUnitalCStarAlgebra I.Quotient := I.quotientCStarAlgebra
  let e : I.Quotient ≃⋆ₐ[ℂ] D := NonUnitalStarAlgHom.quotientKerEquivOfSurjective rho hrho
  have he (x : B) : e (I.quotientMap x) = rho x :=
    NonUnitalStarAlgHom.quotientKerEquivOfSurjective_quotientMap rho hrho x
  have hb : e.symm (rho b) = I.quotientMap b := by
    calc
      e.symm (rho b) = e.symm (e (I.quotientMap b)) := congrArg e.symm (he b).symm
      _ = I.quotientMap b := e.symm_apply_apply _
  change (DoubleCentralizer.congr e (quotientMultiplier I m)).snd (rho b) = _
  rw [congr_apply_snd, hb, quotientMultiplier_snd_quotientMap, he]

/-- **Coefficient embedding under multiplier transport.** For a surjective complex nonunital star
homomorphism `ρ : B → D` of C-star algebras, `mapOfSurjective ρ hρ (DoubleCentralizer.coeHom
b) = DoubleCentralizer.coeHom (ρ b)`. -/
theorem mapOfSurjective_coeHom (rho : B →⋆ₙₐ[ℂ] D) (hrho : Function.Surjective rho) (b : B) :
    mapOfSurjective rho hrho (DoubleCentralizer.coeHom (𝕜 := ℂ) b) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) (rho b) := by
  apply DoubleCentralizer.ext ℂ D
  apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro d
  · obtain ⟨a, rfl⟩ := hrho d
    rw [mapOfSurjective_fst]
    change rho (b * a) = rho b * rho a
    exact map_mul rho b a
  · obtain ⟨a, rfl⟩ := hrho d
    rw [mapOfSurjective_snd]
    change rho (a * b) = rho a * rho b
    exact map_mul rho a b

/-- **Coefficient ideal under multiplier transport.** For a surjective complex nonunital star
homomorphism `ρ : B → D` of C-star algebras, the multiplier map sends the embedded coefficient
ideal of `M(B)` into that of `M(D)`. -/
theorem mapOfSurjective_mem_coefficientIdeal (rho : B →⋆ₙₐ[ℂ] D)
    (hrho : Function.Surjective rho) {m : 𝓜(ℂ, B)} (hm : m ∈ coefficientIdeal B) :
    mapOfSurjective rho hrho m ∈ coefficientIdeal D := by
  rcases (mem_coefficientIdeal_iff m).1 hm with ⟨b, rfl⟩
  rw [mapOfSurjective_coeHom]
  exact coeHom_mem_coefficientIdeal _

/-- **Corona map of a coefficient quotient.** For a surjective complex nonunital star homomorphism
`ρ : B → D` of C-star algebras, the multiplier map descends to the unital complex star
homomorphism `Q(ρ) : Q(B) → Q(D)`. -/
def outerMapOfSurjective (rho : B →⋆ₙₐ[ℂ] D) (hrho : Function.Surjective rho) :
    letI : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B;
    letI : CStarAlgebra (OuterMultiplier D) := outerMultiplierCStarAlgebra D;
    OuterMultiplier B →⋆ₐ[ℂ] OuterMultiplier D := by
  letI : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B
  letI : CStarAlgebra (OuterMultiplier D) := outerMultiplierCStarAlgebra D
  letI : (coefficientIdeal B).carrier.IsTwoSided := (coefficientIdeal B).isTwoSided
  letI : (coefficientIdeal D).carrier.IsTwoSided := (coefficientIdeal D).isTwoSided
  let f : OuterMultiplier B →⋆ₙₐ[ℂ] OuterMultiplier D :=
    NonUnitalStarSubalgebra.Quotient.map (coefficientIdeal B).carrier (coefficientIdeal D).carrier
      (mapOfSurjective rho hrho).toNonUnitalStarAlgHom
      (fun m hm => mapOfSurjective_mem_coefficientIdeal rho hrho hm)
  have hf (m : 𝓜(ℂ, B)) : f (outerQuotientMap m) =
      outerQuotientMap (mapOfSurjective rho hrho m) := rfl
  have hOne : f 1 = 1 := by
    calc
      f 1 = f (outerQuotientMap (1 : 𝓜(ℂ, B))) :=
        congrArg f (map_one (outerQuotientMap (A := B))).symm
      _ = outerQuotientMap (mapOfSurjective rho hrho 1) := hf _
      _ = 1 := by rw [map_one, map_one]
  exact
    { toFun := f
      map_one' := hOne
      map_zero' := map_zero f
      map_add' := map_add f
      map_mul' := map_mul f
      commutes' := by
        intro c
        simp only [Algebra.algebraMap_eq_smul_one, map_smul, hOne]
      map_star' := map_star f }

/-- **Multiplier-corona quotient square.** For a surjective complex nonunital star homomorphism `ρ
: B → D` of C-star algebras, `outerMapOfSurjective ρ hρ (q_B m) = q_D (mapOfSurjective ρ hρ
m)` for every multiplier `m`. -/
theorem outerMapOfSurjective_outerQuotientMap (rho : B →⋆ₙₐ[ℂ] D)
    (hrho : Function.Surjective rho) (m : 𝓜(ℂ, B)) :
    letI : CStarAlgebra (OuterMultiplier B) := outerMultiplierCStarAlgebra B;
    letI : CStarAlgebra (OuterMultiplier D) := outerMultiplierCStarAlgebra D;
    outerMapOfSurjective rho hrho (outerQuotientMap m) =
      outerQuotientMap (mapOfSurjective rho hrho m) := rfl

end DoubleCentralizer
