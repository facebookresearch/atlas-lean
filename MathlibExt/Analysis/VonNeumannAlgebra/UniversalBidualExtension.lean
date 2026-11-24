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

public import MathlibExt.Analysis.CStarAlgebra.GNS.UniversalRepresentation
public import MathlibExt.Analysis.InnerProductSpace.OperatorBidual
public import MathlibExt.Analysis.Normed.Operator.Arens
public import MathlibExt.Analysis.Normed.Module.StrongDualStar
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The original universal representation on the actual bidual

The canonical operator-bidual retraction is composed with the two bounded
strong-dual precomposition maps of the original all-state representation.
Its coefficient is exactly F(a ↦ ⟪η, π(a)ξ⟫), with the original A* and A**
operator norms. Both Arens products and the intrinsic bidual involution are
preserved by evaluating these original vector functionals.

No C-star or W-star structure on A** is assumed or selected. The original
algebra may be nonunital or zero, and its universal Hilbert sum is the existing
arbitrary-state-index completion. The future compatible bidual C-star/W-star
existence theorem remains a separate whole source obligation.

These constructors and characteristics provide the canonical operator-bidual
map used in Blackadar, *K-Theory for Operator Algebras*, Section 15.8.1(3).
The iterated Arens/coefficient formulas unpack that construction; they are
not additional formulas quoted verbatim from the printed theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped InnerProductSpace StrongDual

attribute [local instance]
  ContinuousLinearMap.arensDualSeminormed
  ContinuousLinearMap.arensDualNormedSpace
  ContinuousLinearMap.arensDualTargetSeminormed
  ContinuousLinearMap.arensDualTargetNormedSpace
  ContinuousLinearMap.arensDualTargetTopologicalAddGroup
  ContinuousLinearMap.arensMapSeminormed
  ContinuousLinearMap.arensMapNormedSpace
  ContinuousLinearMap.arensMapTopologicalAddGroup
  ContinuousLinearMap.arensBidualSeminormed
  ContinuousLinearMap.arensBidualNormedSpace
  ContinuousLinearMap.arensBidualMapSeminormed
  ContinuousLinearMap.arensBidualMapNormedSpace
  ContinuousLinearMap.arensBidualMapTopologicalAddGroup

namespace CStarAlgebra

universe uA

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- The original all-state coefficient map, bundled with its existing contraction bound. -/
def universalStateGNSRepresentationCLM :
    A →L[ℂ] (UniversalStateGNSpace A →L[ℂ] UniversalStateGNSpace A) :=
  LinearMap.mkContinuous
    ({ toFun := universalStateGNSRepresentation A
       map_add' := map_add (universalStateGNSRepresentation A)
       map_smul' := map_smul (universalStateGNSRepresentation A) } :
      A →ₗ[ℂ] (UniversalStateGNSpace A →L[ℂ] UniversalStateGNSpace A))
    1 fun a => by
      change ‖universalStateGNSRepresentation A a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using norm_universalStateGNSRepresentation_le A a

/-- The bounded coefficient map retains the original nonunital star-homomorphism value. -/
@[simp]
theorem universalStateGNSRepresentationCLM_apply (a : A) :
    universalStateGNSRepresentationCLM A a = universalStateGNSRepresentation A a := rfl

/-- The original universal coefficient map has operator norm at most one. -/
theorem norm_universalStateGNSRepresentationCLM_le :
    ‖universalStateGNSRepresentationCLM A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (universalStateGNSRepresentationCLM A) zero_le_one
  intro a
  rw [universalStateGNSRepresentationCLM_apply, one_mul]
  exact norm_universalStateGNSRepresentation_le A a

/-- The actual A* vector coefficient, formed by original bounded precomposition. -/
def universalStateGNSCoefficient (ξ η : UniversalStateGNSpace A) : StrongDual ℂ A :=
  (MathlibExt.Analysis.InnerProductSpace.operatorCoefficient ξ η).comp
    (universalStateGNSRepresentationCLM A)

/-- The actual coefficient functional evaluates the original representation and vectors. -/
@[simp]
theorem universalStateGNSCoefficient_apply (ξ η : UniversalStateGNSpace A) (a : A) :
    universalStateGNSCoefficient A ξ η a = ⟪η, universalStateGNSRepresentation A a ξ⟫_ℂ := by
  simp only [universalStateGNSCoefficient, ContinuousLinearMap.comp_apply,
    universalStateGNSRepresentationCLM_apply,
    MathlibExt.Analysis.InnerProductSpace.operatorCoefficient_apply]

/-- The original coefficient-functional norm is bounded by the original two vector norms. -/
theorem norm_universalStateGNSCoefficient_le (ξ η : UniversalStateGNSpace A) :
    ‖universalStateGNSCoefficient A ξ η‖ ≤ ‖ξ‖ * ‖η‖ := by
  calc
    ‖universalStateGNSCoefficient A ξ η‖ ≤
        ‖MathlibExt.Analysis.InnerProductSpace.operatorCoefficient ξ η‖ *
          ‖universalStateGNSRepresentationCLM A‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖ξ‖ * ‖η‖) * ‖universalStateGNSRepresentationCLM A‖ :=
      mul_le_mul_of_nonneg_right
        (MathlibExt.Analysis.InnerProductSpace.norm_operatorCoefficient_le ξ η)
        (ContinuousLinearMap.opNorm_nonneg (universalStateGNSRepresentationCLM A))
    _ ≤ (‖ξ‖ * ‖η‖) * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_universalStateGNSRepresentationCLM_le A)
        (mul_nonneg (norm_nonneg ξ) (norm_nonneg η))
    _ = ‖ξ‖ * ‖η‖ := mul_one _

/-- The canonical continuous linear extension on the literal original strong bidual.
`precomp` is the pinned Mathlib strong-dual map; applying it twice is π**. -/
def universalBidualExtension :
    StrongDual ℂ (StrongDual ℂ A) →L[ℂ]
      (UniversalStateGNSpace A →L[ℂ] UniversalStateGNSpace A) :=
  MathlibExt.Analysis.InnerProductSpace.operatorBidualRetraction.comp
    (((universalStateGNSRepresentationCLM A).precomp (G := ℂ)).precomp (G := ℂ))

/-- Every original bidual coefficient is the literal original A* evaluation. -/
theorem universalBidualExtension_inner (p : StrongDual ℂ (StrongDual ℂ A))
    (ξ η : UniversalStateGNSpace A) :
    ⟪η, universalBidualExtension A p ξ⟫_ℂ = p (universalStateGNSCoefficient A ξ η) := by
  change ⟪η, MathlibExt.Analysis.InnerProductSpace.operatorBidualRetraction
    ((((universalStateGNSRepresentationCLM A).precomp (G := ℂ)).precomp (G := ℂ)) p) ξ⟫_ℂ =
      p (universalStateGNSCoefficient A ξ η)
  rw [MathlibExt.Analysis.InnerProductSpace.operatorBidualRetraction_inner]
  simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- The canonical extension restricts to the original representation under η(a)(φ)=φ(a). -/
@[simp]
theorem universalBidualExtension_inclusionInDoubleDual (a : A) :
    universalBidualExtension A (NormedSpace.inclusionInDoubleDual ℂ A a) =
      universalStateGNSRepresentation A a := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  calc
    ⟪η, universalBidualExtension A (NormedSpace.inclusionInDoubleDual ℂ A a) ξ⟫_ℂ =
        NormedSpace.inclusionInDoubleDual ℂ A a (universalStateGNSCoefficient A ξ η) :=
      universalBidualExtension_inner A (NormedSpace.inclusionInDoubleDual ℂ A a) ξ η
    _ = universalStateGNSCoefficient A ξ η a :=
      NormedSpace.dual_def ℂ A a (universalStateGNSCoefficient A ξ η)
    _ = ⟪η, universalStateGNSRepresentation A a ξ⟫_ℂ :=
      universalStateGNSCoefficient_apply A ξ η a

/-- Every extension value is contractive for the original iterated-dual operator norm. -/
theorem norm_universalBidualExtension_apply_le (p : StrongDual ℂ (StrongDual ℂ A)) :
    ‖universalBidualExtension A p‖ ≤ ‖p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg p)
  intro ξ
  rw [← innerSL_apply_norm ℂ (universalBidualExtension A p ξ)]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg p) (norm_nonneg ξ))
  intro η
  calc
    ‖innerSL ℂ (universalBidualExtension A p ξ) η‖ =
        ‖⟪η, universalBidualExtension A p ξ⟫_ℂ‖ := by
      rw [innerSL_apply_apply, norm_inner_symm]
    _ = ‖p (universalStateGNSCoefficient A ξ η)‖ := by rw [universalBidualExtension_inner]
    _ ≤ ‖p‖ * ‖universalStateGNSCoefficient A ξ η‖ :=
      ContinuousLinearMap.le_opNorm (E := StrongDual ℂ A) (F := ℂ)
        (σ₁₂ := RingHom.id ℂ) p _
    _ ≤ ‖p‖ * (‖ξ‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (norm_universalStateGNSCoefficient_le A ξ η) (norm_nonneg p)
    _ = (‖p‖ * ‖ξ‖) * ‖η‖ := by rw [mul_assoc]

/-- The canonical continuous linear extension has operator norm at most one. -/
theorem norm_universalBidualExtension_le : ‖universalBidualExtension A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simpa only [one_mul] using norm_universalBidualExtension_apply_le A p

/-- Original left multiplication translates a vector functional through the actual adjoint. -/
theorem universalStateGNSCoefficient_mul_left (a : A) (ξ η : UniversalStateGNSpace A) :
    (ContinuousLinearMap.mul ℂ A).dualBilinear (universalStateGNSCoefficient A ξ η) a =
      universalStateGNSCoefficient A ξ (star (universalStateGNSRepresentation A a) η) := by
  apply ContinuousLinearMap.ext
  intro b
  rw [ContinuousLinearMap.dualBilinear_apply,
    universalStateGNSCoefficient_apply, universalStateGNSCoefficient_apply]
  change ⟪η, universalStateGNSRepresentation A (a * b) ξ⟫_ℂ =
    ⟪star (universalStateGNSRepresentation A a) η, universalStateGNSRepresentation A b ξ⟫_ℂ
  rw [map_mul]
  change ⟪η, universalStateGNSRepresentation A a (universalStateGNSRepresentation A b ξ)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left (universalStateGNSRepresentation A a)
    (universalStateGNSRepresentation A b ξ) η).symm

/-- Original right multiplication translates the original first vector, with no adjoint change. -/
theorem universalStateGNSCoefficient_mul_right (b : A) (ξ η : UniversalStateGNSpace A) :
    (ContinuousLinearMap.mul ℂ A).flip.dualBilinear
        (universalStateGNSCoefficient A ξ η) b =
      universalStateGNSCoefficient A (universalStateGNSRepresentation A b ξ) η := by
  apply ContinuousLinearMap.ext
  intro a
  rw [ContinuousLinearMap.dualBilinear_apply,
    universalStateGNSCoefficient_apply, universalStateGNSCoefficient_apply]
  change ⟪η, universalStateGNSRepresentation A (a * b) ξ⟫_ℂ =
    ⟪η, universalStateGNSRepresentation A a (universalStateGNSRepresentation A b ξ)⟫_ℂ
  rw [map_mul]
  rfl

/-- The first literal Arens product maps to the original operator product. -/
theorem universalBidualExtension_arensFirst (p q : StrongDual ℂ (StrongDual ℂ A)) :
    universalBidualExtension A ((ContinuousLinearMap.mul ℂ A).arensFirst p q) =
      universalBidualExtension A p * universalBidualExtension A q := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have hcoeff : (ContinuousLinearMap.mul ℂ A).dualBilinear.dualBilinear q
        (universalStateGNSCoefficient A ξ η) =
      universalStateGNSCoefficient A (universalBidualExtension A q ξ) η := by
    apply ContinuousLinearMap.ext
    intro a
    calc
      (ContinuousLinearMap.mul ℂ A).dualBilinear.dualBilinear q
          (universalStateGNSCoefficient A ξ η) a =
          q ((ContinuousLinearMap.mul ℂ A).dualBilinear
            (universalStateGNSCoefficient A ξ η) a) :=
        ContinuousLinearMap.dualBilinear_apply (ContinuousLinearMap.mul ℂ A).dualBilinear
          q (universalStateGNSCoefficient A ξ η) a
      _ = q (universalStateGNSCoefficient A ξ (star (universalStateGNSRepresentation A a) η)) :=
        congrArg q (universalStateGNSCoefficient_mul_left A a ξ η)
      _ = ⟪star (universalStateGNSRepresentation A a) η, universalBidualExtension A q ξ⟫_ℂ :=
        (universalBidualExtension_inner A q ξ (star (universalStateGNSRepresentation A a) η)).symm
      _ = ⟪η, universalStateGNSRepresentation A a (universalBidualExtension A q ξ)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint_inner_left (universalStateGNSRepresentation A a)
          (universalBidualExtension A q ξ) η
      _ = universalStateGNSCoefficient A (universalBidualExtension A q ξ) η a :=
        (universalStateGNSCoefficient_apply A (universalBidualExtension A q ξ) η a).symm
  calc
    ⟪η, universalBidualExtension A ((ContinuousLinearMap.mul ℂ A).arensFirst p q) ξ⟫_ℂ =
        (ContinuousLinearMap.mul ℂ A).arensFirst p q (universalStateGNSCoefficient A ξ η) :=
      universalBidualExtension_inner A ((ContinuousLinearMap.mul ℂ A).arensFirst p q) ξ η
    _ = p ((ContinuousLinearMap.mul ℂ A).dualBilinear.dualBilinear q
        (universalStateGNSCoefficient A ξ η)) :=
      ContinuousLinearMap.arensFirst_apply (ContinuousLinearMap.mul ℂ A) p q
        (universalStateGNSCoefficient A ξ η)
    _ = p (universalStateGNSCoefficient A (universalBidualExtension A q ξ) η) :=
      congrArg p hcoeff
    _ = ⟪η, universalBidualExtension A p (universalBidualExtension A q ξ)⟫_ℂ :=
      (universalBidualExtension_inner A p (universalBidualExtension A q ξ) η).symm
    _ = ⟪η, (universalBidualExtension A p * universalBidualExtension A q) ξ⟫_ℂ := by
      rw [mul_apply_eq_comp]

/-- The second literal Arens product has the same original operator-product image. -/
theorem universalBidualExtension_arensSecond (p q : StrongDual ℂ (StrongDual ℂ A)) :
    universalBidualExtension A ((ContinuousLinearMap.mul ℂ A).arensSecond p q) =
      universalBidualExtension A p * universalBidualExtension A q := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have h : (ContinuousLinearMap.mul ℂ A).flip.dualBilinear.dualBilinear p
        (universalStateGNSCoefficient A ξ η) =
      universalStateGNSCoefficient A ξ (star (universalBidualExtension A p) η) := by
    apply ContinuousLinearMap.ext
    intro b
    calc
      (ContinuousLinearMap.mul ℂ A).flip.dualBilinear.dualBilinear p
          (universalStateGNSCoefficient A ξ η) b =
          p ((ContinuousLinearMap.mul ℂ A).flip.dualBilinear
            (universalStateGNSCoefficient A ξ η) b) :=
        ContinuousLinearMap.dualBilinear_apply (ContinuousLinearMap.mul ℂ A).flip.dualBilinear
          p (universalStateGNSCoefficient A ξ η) b
      _ = p (universalStateGNSCoefficient A (universalStateGNSRepresentation A b ξ) η) :=
        congrArg p (universalStateGNSCoefficient_mul_right A b ξ η)
      _ = ⟪η, universalBidualExtension A p (universalStateGNSRepresentation A b ξ)⟫_ℂ :=
        (universalBidualExtension_inner A p (universalStateGNSRepresentation A b ξ) η).symm
      _ = ⟪star (universalBidualExtension A p) η,
          universalStateGNSRepresentation A b ξ⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint]
        exact (ContinuousLinearMap.adjoint_inner_left (universalBidualExtension A p)
          (universalStateGNSRepresentation A b ξ) η).symm
      _ = universalStateGNSCoefficient A ξ (star (universalBidualExtension A p) η) b :=
        (universalStateGNSCoefficient_apply A ξ (star (universalBidualExtension A p) η) b).symm
  calc
    ⟪η, universalBidualExtension A ((ContinuousLinearMap.mul ℂ A).arensSecond p q) ξ⟫_ℂ =
        (ContinuousLinearMap.mul ℂ A).arensSecond p q (universalStateGNSCoefficient A ξ η) :=
      universalBidualExtension_inner A ((ContinuousLinearMap.mul ℂ A).arensSecond p q) ξ η
    _ = q ((ContinuousLinearMap.mul ℂ A).flip.dualBilinear.dualBilinear p
        (universalStateGNSCoefficient A ξ η)) :=
      ContinuousLinearMap.arensSecond_apply (ContinuousLinearMap.mul ℂ A) p q
        (universalStateGNSCoefficient A ξ η)
    _ = q (universalStateGNSCoefficient A ξ (star (universalBidualExtension A p) η)) :=
      congrArg q h
    _ = ⟪star (universalBidualExtension A p) η, universalBidualExtension A q ξ⟫_ℂ :=
      (universalBidualExtension_inner A q ξ (star (universalBidualExtension A p) η)).symm
    _ = ⟪η, universalBidualExtension A p (universalBidualExtension A q ξ)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint_inner_left (universalBidualExtension A p)
        (universalBidualExtension A q ξ) η
    _ = ⟪η, (universalBidualExtension A p * universalBidualExtension A q) ξ⟫_ℂ := by
      rw [mul_apply_eq_comp]

/-- The original intrinsic A* involution interchanges the two actual vector coefficients. -/
@[simp]
theorem universalStateGNSCoefficient_star (ξ η : UniversalStateGNSpace A) :
    star (universalStateGNSCoefficient A ξ η) = universalStateGNSCoefficient A η ξ := by
  apply ContinuousLinearMap.ext
  intro a
  rw [StrongDual.star_apply, universalStateGNSCoefficient_apply,
    universalStateGNSCoefficient_apply, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.star_def] using
    (inner_conj_symm ξ (universalStateGNSRepresentation A a η))

/-- The literal original bidual involution maps to the original Hilbert-operator adjoint. -/
theorem universalBidualExtension_star (p : StrongDual ℂ (StrongDual ℂ A)) :
    universalBidualExtension A (star p) = star (universalBidualExtension A p) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [universalBidualExtension_inner, StrongDual.star_bidual_apply,
    universalStateGNSCoefficient_star, ← universalBidualExtension_inner A p η ξ,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.star_def] using
    (inner_conj_symm (universalBidualExtension A p η) ξ)

end CStarAlgebra
