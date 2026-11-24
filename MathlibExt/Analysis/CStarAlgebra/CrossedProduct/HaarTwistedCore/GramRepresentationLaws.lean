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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramOperatorExtension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Actual coefficient and unitary representation laws on the original Gram space

The computed bounded coefficient operators and isometric group operators act
on the actual essential Hilbert space. Equality on the original source
generators extends by their proved dense span. The literal Haar coefficient
and group identities then give their algebra laws and covariance.

The source mixed star product gives the coefficient adjoint law. The group
norm preservation and actual inverse composition give the group adjoint law
and unitary membership. These laws construct actual bundled representations.

Strong continuity of the group orbits and the integrated identity remain
separate prerequisites for a strongly continuous covariant model.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α)) (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

omit [μ.Regular] in
/-- The actual original-source Gram generators determine every bounded operator. -/
theorem gramOperator_ext (T S : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
    (h : ∀ (f : Carrier μ α) (ξ : ρ.essentialSpace),
      T (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
        S (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)) : T = S := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (p.dense_rawHilbertGramDomain H ρ).induction ?_
    (isClosed_eq T.continuous S.continuous) ξ
  intro η hη
  exact LinearMap.eqOn_span (f := T.toLinearMap) (g := S.toLinearMap)
    (by rintro _ ⟨⟨f, ζ⟩, rfl⟩; exact h f ζ) hη

omit [μ.Regular] in
/-- The actual source generators determine the adjoint identity of bounded operators. -/
theorem gramOperator_eq_star_of_inner_generators
    (T S : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
    (h : ∀ (f k : Carrier μ α) (ξ η : ρ.essentialSpace),
      ⟪T (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ),
        ρ.essentialRepresentation (p.toNonUnitalCompletion k) η⟫_ℂ =
      ⟪ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ,
        S (ρ.essentialRepresentation (p.toNonUnitalCompletion k) η)⟫_ℂ) :
    T = star S := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff T S).mpr
  intro ξ η
  refine (denseRange_gramEvaluation μ α p H ρ).induction_on₂
    (isClosed_eq ((T.continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner (S.continuous.comp continuous_snd))) ?_ ξ η
  intro x y
  simp only [gramEvaluation, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : ℂ => y i * z)
  apply Finset.sum_congr rfl
  intro j _
  rw [h j.1 i.1 j.2 i.2]

omit [μ.Regular] in
/-- The actual zero coefficient acts as the zero bounded operator. -/
theorem gramCoefficientOperator_zero :
    gramCoefficientOperator μ α p H ρ (0 : A) = 0 := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  rw [gramCoefficientOperator_apply_generator]
  have hzero : coefficientLeft μ α (0 : A) f = 0 :=
    congrArg (fun L : Module.End ℂ (Carrier μ α) => L f) (map_zero (coefficientLeftHom μ α))
  rw [hzero, map_zero, map_zero]
  rfl

omit [μ.Regular] in
/-- Original coefficient addition is preserved by the computed bounded operators. -/
theorem gramCoefficientOperator_add (a b : A) :
    gramCoefficientOperator μ α p H ρ (a + b) =
      gramCoefficientOperator μ α p H ρ a + gramCoefficientOperator μ α p H ρ b := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (a + b)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramCoefficientOperator μ α p H ρ a
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) +
      gramCoefficientOperator μ α p H ρ b
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    gramCoefficientOperator_apply_generator, coefficientLeft_add, LinearMap.add_apply,
    map_add, map_add]
  rfl

omit [μ.Regular] in
/-- Original complex coefficient scaling is preserved by the computed bounded operators. -/
theorem gramCoefficientOperator_smul (c : ℂ) (a : A) :
    gramCoefficientOperator μ α p H ρ (c • a) = c • gramCoefficientOperator μ α p H ρ a := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (c • a)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    c • gramCoefficientOperator μ α p H ρ a
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    coefficientLeft_smul, LinearMap.smul_apply, map_smul, map_smul]
  rfl

omit [μ.Regular] in
/-- Original coefficient multiplication is preserved by the computed bounded operators. -/
theorem gramCoefficientOperator_mul (a b : A) :
    gramCoefficientOperator μ α p H ρ (a * b) =
      gramCoefficientOperator μ α p H ρ a * gramCoefficientOperator μ α p H ρ b := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramCoefficientOperator μ α p H ρ (a * b)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramCoefficientOperator μ α p H ρ a
      (gramCoefficientOperator μ α p H ρ b
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator,
    gramCoefficientOperator_apply_generator, coefficientLeft_mul, LinearMap.comp_apply]

omit [μ.Regular] in
/-- The actual coefficient adjoint law follows from the original mixed star-convolution product. -/
theorem gramCoefficientOperator_star (a : A) :
    gramCoefficientOperator μ α p H ρ (star a) = star (gramCoefficientOperator μ α p H ρ a) := by
  apply gramOperator_eq_star_of_inner_generators μ α p H ρ
  intro f h ξ η
  rw [gramCoefficientOperator_apply_generator, gramCoefficientOperator_apply_generator]
  have hGram (u v : Carrier μ α) :
      ⟪ρ.essentialRepresentation (p.toNonUnitalCompletion u) ξ,
        ρ.essentialRepresentation (p.toNonUnitalCompletion v) η⟫_ℂ =
      ⟪ξ, ρ.essentialRepresentation (p.toNonUnitalCompletion (star u * v)) η⟫_ℂ := by
    exact p.rawHilbertGramGenerator_inner H ρ u v ξ η
  rw [hGram, hGram]
  have hStar : star (coefficientLeft μ α (star a) f) =
      coefficientRight μ α a (star f) := by
    change crossedStar μ α (coefficientLeft μ α (star a) f) =
      coefficientRight μ α a (crossedStar μ α f)
    simpa only [star_star] using crossedStar_coefficientLeft μ α (star a) f
  have hRaw : star (coefficientLeft μ α (star a) f) * h =
      star f * coefficientLeft μ α a h := by
    rw [hStar]
    exact (convolution_coefficientLeft μ α a (star f) h).symm
  rw [hRaw]

/-- The computed coefficient operators as their actual nonunital star-algebra representation. -/
def gramCoefficientRepresentation : A →⋆ₙₐ[ℂ] (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) where
  toFun := gramCoefficientOperator μ α p H ρ
  map_zero' := gramCoefficientOperator_zero μ α p H ρ
  map_add' := gramCoefficientOperator_add μ α p H ρ
  map_smul' := gramCoefficientOperator_smul μ α p H ρ
  map_mul' := gramCoefficientOperator_mul μ α p H ρ
  map_star' := gramCoefficientOperator_star μ α p H ρ

omit [μ.Regular] in
/-- The actual bundled coefficient representation retains its computed operator. -/
@[simp]
theorem gramCoefficientRepresentation_apply (a : A) :
    gramCoefficientRepresentation μ α p H ρ a = gramCoefficientOperator μ α p H ρ a := rfl

/-- The actual group identity acts as the identity bounded operator. -/
theorem gramGroupOperator_one : gramGroupOperator μ α p H ρ (1 : G) = 1 := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  rw [gramGroupOperator_apply_generator, groupLeft_one, LinearMap.id_apply]
  rfl

/-- Original group multiplication is preserved by the computed bounded operators. -/
theorem gramGroupOperator_mul (g h : G) :
    gramGroupOperator μ α p H ρ (g * h) =
      gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ h := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramGroupOperator μ α p H ρ (g * h)
      (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ) =
    gramGroupOperator μ α p H ρ g
      (gramGroupOperator μ α p H ρ h
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramGroupOperator_apply_generator, gramGroupOperator_apply_generator,
    gramGroupOperator_apply_generator, groupLeft_mul, LinearMap.comp_apply]

/-- The actual inverse group operator is a right inverse of the computed group operator. -/
theorem gramGroupOperator_mul_inv (g : G) :
    gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ g⁻¹ = 1 := by
  rw [← gramGroupOperator_mul, mul_inv_cancel, gramGroupOperator_one]

/-- The actual inverse group operator is a left inverse of the computed group operator. -/
theorem gramGroupOperator_inv_mul (g : G) :
    gramGroupOperator μ α p H ρ g⁻¹ * gramGroupOperator μ α p H ρ g = 1 := by
  rw [← gramGroupOperator_mul, inv_mul_cancel, gramGroupOperator_one]

/-- The computed group norm preservation gives its actual left adjoint inverse identity. -/
theorem gramGroupOperator_star_mul_self (g : G) :
    star (gramGroupOperator μ α p H ρ g) * gramGroupOperator μ α p H ρ g = 1 := by
  change (gramGroupOperator μ α p H ρ g).adjoint.comp (gramGroupOperator μ α p H ρ g) = 1
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
    (norm_gramGroupOperator_apply μ α p H ρ g)

/-- The actual group adjoint is precisely the computed inverse group operator. -/
theorem gramGroupOperator_star (g : G) :
    star (gramGroupOperator μ α p H ρ g) = gramGroupOperator μ α p H ρ g⁻¹ := by
  calc
    _ = star (gramGroupOperator μ α p H ρ g) * 1 := (mul_one _).symm
    _ = star (gramGroupOperator μ α p H ρ g) *
        (gramGroupOperator μ α p H ρ g * gramGroupOperator μ α p H ρ g⁻¹) := by
      rw [gramGroupOperator_mul_inv]
    _ = (star (gramGroupOperator μ α p H ρ g) * gramGroupOperator μ α p H ρ g) *
        gramGroupOperator μ α p H ρ g⁻¹ := (mul_assoc _ _ _).symm
    _ = gramGroupOperator μ α p H ρ g⁻¹ := by rw [gramGroupOperator_star_mul_self, one_mul]

/-- Every computed original-source group operator is genuinely unitary. -/
theorem gramGroupOperator_mem_unitary (g : G) :
    gramGroupOperator μ α p H ρ g ∈ unitary (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) := by
  exact ⟨gramGroupOperator_star_mul_self μ α p H ρ g,
    by rw [gramGroupOperator_star, gramGroupOperator_mul_inv]⟩

/-- The computed group operators as their actual unitary monoid homomorphism. -/
def gramGroupUnitaryRepresentation : G →* unitary (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) where
  toFun g := ⟨gramGroupOperator μ α p H ρ g, gramGroupOperator_mem_unitary μ α p H ρ g⟩
  map_one' := Subtype.ext (gramGroupOperator_one μ α p H ρ)
  map_mul' g h := Subtype.ext (gramGroupOperator_mul μ α p H ρ g h)

/-- The actual bundled unitary representation retains its computed group operator. -/
@[simp]
theorem gramGroupUnitaryRepresentation_apply_coe (g : G) :
    (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) =
      gramGroupOperator μ α p H ρ g := rfl

/-- Original group-coefficient covariance is preserved by the computed bounded operators. -/
theorem gramGroupOperator_mul_coefficient (g : G) (a : A) :
    gramGroupOperator μ α p H ρ g * gramCoefficientOperator μ α p H ρ a =
      gramCoefficientOperator μ α p H ρ (α g a) * gramGroupOperator μ α p H ρ g := by
  apply gramOperator_ext μ α p H ρ
  intro f ξ
  change gramGroupOperator μ α p H ρ g
      (gramCoefficientOperator μ α p H ρ a
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ)) =
    gramCoefficientOperator μ α p H ρ (α g a)
      (gramGroupOperator μ α p H ρ g
        (ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ))
  rw [gramCoefficientOperator_apply_generator, gramGroupOperator_apply_generator,
    gramGroupOperator_apply_generator, gramCoefficientOperator_apply_generator]
  have hRaw := congrArg (fun L : Module.End ℂ (Carrier μ α) => L f)
    (groupLeft_coefficientLeft μ α g a)
  change groupLeft μ α g (coefficientLeft μ α a f) =
    coefficientLeft μ α (α g a) (groupLeft μ α g f) at hRaw
  rw [hRaw]

/-- The actual coefficient and unitary operators satisfy the original conjugation covariance. -/
theorem gramRepresentation_covariance (g : G) (a : A) :
    (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) *
        gramCoefficientRepresentation μ α p H ρ a *
        star (gramGroupUnitaryRepresentation μ α p H ρ g : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) =
      gramCoefficientRepresentation μ α p H ρ (α g a) := by
  change gramGroupOperator μ α p H ρ g * gramCoefficientOperator μ α p H ρ a *
    star (gramGroupOperator μ α p H ρ g) = gramCoefficientOperator μ α p H ρ (α g a)
  rw [gramGroupOperator_mul_coefficient, mul_assoc, gramGroupOperator_star,
    gramGroupOperator_mul_inv, mul_one]

end

end HaarTwistedCore
