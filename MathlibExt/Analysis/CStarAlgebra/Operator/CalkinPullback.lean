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
public import MathlibExt.Analysis.CStarAlgebra.Pullback
public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic
public import MathlibExt.Analysis.CStarAlgebra.Extension.Busby
public import MathlibExt.Analysis.InnerProductSpace.Operator.CompactOuterMultiplier
public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Actual Calkin pullbacks with operator-first coordinates

The coefficient is the actual closed star ideal of compact operators on H.
A nonunital star map A -> Q(H) has its literal closed pullback inside
End(H) x A, with compatibility pi(T)=phi(a). The compact inclusion and
quotient coordinate are strict maps. The existing compact multiplier
equivalences identify these literal coordinates with the canonical Busby
pullback; injectivity, surjectivity and exactness are transported from that API.
All H, including finite and zero Hilbert spaces, are allowed; neither phi nor
A is assumed unital, injective or separable. This strict coordinate
constructor serves the original concrete extension statements.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace CalkinAlgebra

universe uA uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original compact-operator coefficient has the literal closed-ideal subtype carrier. -/
abbrev CompactCoefficients (H : Type uH)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  (compactEndomorphismClosedStarIdeal (H := H)).carrier

/-- The actual compact coefficient reuses the strict existing closed-ideal C-star dictionary. -/
instance compactCoefficientsCStarAlgebra : NonUnitalCStarAlgebra (CompactCoefficients H) :=
  (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- The actual source pullback retains operator-first coordinates with its inherited product C-star norm. -/
abbrev operatorPullback (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :=
  NonUnitalCStarPullback.Pullback (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- Literal compact inclusion into the compatible original operator/coefficient pairs. -/
def operatorPullbackInclusion (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CompactCoefficients H →⋆ₙₐ[ℂ] operatorPullback φ := by
  let j : CompactCoefficients H →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
    NonUnitalStarSubalgebraClass.subtype (compactEndomorphismClosedStarIdeal (H := H)).carrier
  exact NonUnitalStarAlgHom.codRestrict
    (j.prod (0 : CompactCoefficients H →⋆ₙₐ[ℂ] A)) (operatorPullback φ) (fun k => by
      change classStarMap (H := H) (k : H →L[ℂ] H) = φ 0
      rw [map_zero]
      apply (classStarMap_eq_zero_iff _).mpr
      exact k.property)

/-- The original coefficient quotient is the actual second coordinate of the compatible pair. -/
def operatorPullbackQuotient (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    operatorPullback φ →⋆ₙₐ[ℂ] A :=
  NonUnitalCStarPullback.sndHom (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- The original operator representation is the actual first coordinate of the compatible pair. -/
def operatorPullbackRepresentation (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    operatorPullback φ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  NonUnitalCStarPullback.fstHom (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- The compact coefficient has its literal operator-first pair value. -/
theorem operatorPullbackInclusion_coe (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) :
    (operatorPullbackInclusion φ k : (H →L[ℂ] H) × A) = ((k : H →L[ℂ] H), 0) := rfl

/-- Every compatible pair retains its literal coefficient quotient value. -/
theorem operatorPullbackQuotient_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : operatorPullbackQuotient φ p = p.1.2 := rfl

/-- Every compatible pair retains its literal original operator value. -/
theorem operatorPullbackRepresentation_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : operatorPullbackRepresentation φ p = p.1.1 := rfl

/-- Transport the original Calkin map through the existing compact outer-multiplier equivalence. -/
def operatorBusbyMap (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CStarExtension.BusbyMap (A := A) (B := CompactCoefficients H) := by
  letI : CStarAlgebra (OuterMultiplier (CompactCoefficients H)) :=
    outerMultiplierCStarAlgebra (CompactCoefficients H)
  exact (DoubleCentralizer.compactOuterMultiplierEquiv (H := H)).symm.toNonUnitalStarAlgHom.comp φ

/-- The original operator-first pairs are the existing Busby pullback in compact-multiplier coordinates. -/
def operatorPullbackBusbyEquiv (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    operatorPullback φ ≃⋆ₐ[ℂ] CStarExtension.BusbyPullback (operatorBusbyMap φ) := by
  letI : CStarAlgebra (OuterMultiplier (CompactCoefficients H)) :=
    outerMultiplierCStarAlgebra (CompactCoefficients H)
  let m := DoubleCentralizer.compactMultiplierEquiv (H := H)
  let o := DoubleCentralizer.compactOuterMultiplierEquiv (H := H)
  let π := (outerQuotientMap (A := CompactCoefficients H)).toNonUnitalStarAlgHom
  have h : (operatorBusbyMap φ).comp (operatorPullbackQuotient φ) =
      π.comp (m.toNonUnitalStarAlgHom.comp (operatorPullbackRepresentation φ)) := by
    apply NonUnitalStarAlgHom.ext
    intro p
    change o.symm (φ p.1.2) = outerQuotientMap (m p.1.1)
    calc
      o.symm (φ p.1.2) = o.symm (classStarMap (H := H) p.1.1) :=
        congrArg o.symm p.property.symm
      _ = outerQuotientMap (m p.1.1) :=
        DoubleCentralizer.compactOuterMultiplierEquiv_symm_classStarMap (H := H) p.1.1
  let f := NonUnitalCStarPullback.lift (operatorBusbyMap φ) π
    (operatorPullbackQuotient φ) (m.toNonUnitalStarAlgHom.comp (operatorPullbackRepresentation φ)) h
  refine StarAlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q hpq
    have ha : p.1.2 = q.1.2 :=
      congrArg (fun x : CStarExtension.BusbyPullback (operatorBusbyMap φ) => x.1.1) hpq
    have hm : m p.1.1 = m q.1.1 :=
      congrArg (fun x : CStarExtension.BusbyPullback (operatorBusbyMap φ) => x.1.2) hpq
    exact Subtype.ext (Prod.ext (m.injective hm) ha)
  · intro p
    have hClass : classStarMap (H := H) (m.symm p.1.2) = φ p.1.1 := by
      have hp := p.property
      change o.symm (φ p.1.1) = outerQuotientMap p.1.2 at hp
      calc
        classStarMap (H := H) (m.symm p.1.2) = o (outerQuotientMap p.1.2) :=
          (DoubleCentralizer.compactOuterMultiplierEquiv_outerQuotientMap (H := H) p.1.2).symm
        _ = o (o.symm (φ p.1.1)) := congrArg o hp.symm
        _ = φ p.1.1 := o.apply_symm_apply _
    refine ⟨⟨(m.symm p.1.2, p.1.1), hClass⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl (m.apply_symm_apply p.1.2)

/-- The coordinate equivalence retains the actual quotient and bounded-operator multiplier values. -/
theorem operatorPullbackBusbyEquiv_coe (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) (p : operatorPullback φ) :
    (operatorPullbackBusbyEquiv φ p : A × DoubleCentralizer ℂ (CompactCoefficients H)) =
      (p.1.2, DoubleCentralizer.compactMultiplierEquiv (H := H) p.1.1) := rfl

/-- Transport identifies the literal compact endpoint with the canonical Busby inclusion. -/
theorem operatorPullbackBusbyEquiv_inclusion (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) :
    operatorPullbackBusbyEquiv φ (operatorPullbackInclusion φ k) =
      CStarExtension.pullbackInclusion (operatorBusbyMap φ) k := by
  letI : CStarAlgebra (OuterMultiplier (CompactCoefficients H)) :=
    outerMultiplierCStarAlgebra (CompactCoefficients H)
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change DoubleCentralizer.compactMultiplierEquiv (H := H) (k : H →L[ℂ] H) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) k
    rw [DoubleCentralizer.compactMultiplierEquiv_apply]
    change DoubleCentralizer.multiplierExtension (compactEndomorphismClosedStarIdeal (H := H))
      (StarAlgEquiv.refl ℂ (CompactCoefficients H)) (k : H →L[ℂ] H) =
        DoubleCentralizer.coeHom (𝕜 := ℂ) k
    exact DoubleCentralizer.multiplierExtension_idealEquiv _ _ k

/-- Transport fixes the original quotient algebra and its literal second-coordinate map. -/
theorem operatorPullbackBusbyEquiv_quotient (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) (p : operatorPullback φ) :
    CStarExtension.pullbackQuotient (operatorBusbyMap φ) (operatorPullbackBusbyEquiv φ p) =
      operatorPullbackQuotient φ p := rfl

/-- The original compact inclusion inherits injectivity from the canonical Busby inclusion. -/
theorem operatorPullbackInclusion_injective (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    Function.Injective (operatorPullbackInclusion φ) := by
  intro k l h
  apply Subtype.ext
  exact congrArg (fun p : operatorPullback φ => p.1.1) h

/-- The actual coefficient projection inherits surjectivity from the canonical Busby quotient. -/
theorem operatorPullbackQuotient_surjective (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    Function.Surjective (operatorPullbackQuotient φ) := by
  intro a
  obtain ⟨T, hT⟩ := classStarMap_surjective (H := H) (φ a)
  exact ⟨⟨(T, a), hT⟩, rfl⟩

/-- The original exact pair is transported from the existing canonical Busby exact pair. -/
theorem operatorPullback_exact (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    Function.Exact (operatorPullbackInclusion φ) (operatorPullbackQuotient φ) := by
  intro p
  change p.1.2 = 0 ↔ ∃ k, operatorPullbackInclusion φ k = p
  constructor
  · intro hp
    have hClass : classStarMap (H := H) p.1.1 = 0 := by
      calc
        classStarMap (H := H) p.1.1 = φ p.1.2 := p.property
        _ = φ 0 := congrArg φ hp
        _ = 0 := map_zero φ
    let k : CompactCoefficients H :=
      ⟨p.1.1, (classStarMap_eq_zero_iff p.1.1).mp hClass⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hp.symm
  · rintro ⟨k, rfl⟩
    rfl

/-- The original operator and coefficient projections have the same literal Calkin class. -/
theorem operatorPullback_compatibility (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) :
    classStarMap (H := H) (operatorPullbackRepresentation φ p) = φ (operatorPullbackQuotient φ p) :=
  p.property

/-- The original operator-first pullback constructs the existing normalized concrete extension. -/
def operatorExtension (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CStarExtension A (CompactCoefficients H) :=
  CStarExtension.ofExact (operatorPullbackInclusion φ) (operatorPullbackQuotient φ)
    (operatorPullbackInclusion_injective φ) (operatorPullbackQuotient_surjective φ)
    (operatorPullback_exact φ)

/-- The normalized extension retains the same original compact inclusion. -/
theorem operatorExtension_inclusion_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) : (operatorExtension φ).inclusion k = operatorPullbackInclusion φ k :=
  CStarExtension.ofExact_inclusion_apply _ _ _ _ _ k

/-- The normalized extension retains the same original coefficient quotient. -/
theorem operatorExtension_quotient_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : (operatorExtension φ).quotient p = operatorPullbackQuotient φ p :=
  CStarExtension.ofExact_quotient_apply _ _ _ _ _ p

/-- The operator-coordinate normalization is the existing Busby extension with both endpoints fixed. -/
def operatorExtensionBusbyEquiv (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CStarExtension.Equiv (operatorExtension φ) (CStarExtension.ofBusby (operatorBusbyMap φ)) where
  idealEquiv := StarAlgEquiv.refl ℂ (CompactCoefficients H)
  middleEquiv := operatorPullbackBusbyEquiv φ
  quotientEquiv := StarAlgEquiv.refl ℂ A
  inclusion_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro k
    change operatorPullbackBusbyEquiv φ ((operatorExtension φ).inclusion k) =
      (CStarExtension.ofBusby (operatorBusbyMap φ)).inclusion k
    exact (congrArg (operatorPullbackBusbyEquiv φ)
      (operatorExtension_inclusion_apply φ k)).trans
        ((operatorPullbackBusbyEquiv_inclusion φ k).trans
          (CStarExtension.ofBusby_inclusion (operatorBusbyMap φ) k).symm)
  quotient_commutes := by
    apply NonUnitalStarAlgHom.ext
    intro p
    change (CStarExtension.ofBusby (operatorBusbyMap φ)).quotient (operatorPullbackBusbyEquiv φ p) =
      (operatorExtension φ).quotient p
    exact (CStarExtension.ofBusby_quotient (operatorBusbyMap φ)
      (operatorPullbackBusbyEquiv φ p)).trans
        ((operatorPullbackBusbyEquiv_quotient φ p).trans
          (operatorExtension_quotient_apply φ p).symm)

end CalkinAlgebra

end
