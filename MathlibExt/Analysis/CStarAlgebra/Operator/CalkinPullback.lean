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
# Calkin pullback extensions in operator coordinates

Let `H` be a complex Hilbert space, `A` a nonunital C-star algebra and `φ : A → Q(H) =
B(H)/K(H)` a complex nonunital star-algebra homomorphism. Its closed pullback algebra is `P_φ =
{(T,a) ∈ B(H) × A | [T] = φ(a)}`, with the inherited product C-star norm. The compact inclusion
is `k ↦ (k,0)`, the quotient is `(T,a) ↦ a`, and the operator representation is `(T,a) ↦ T`.

The equivalence `B(H) ≃ M(K(H))` sends `T` to left and right composition on compact operators.
It identifies `P_φ` with the Busby pullback by `(T,a) ↦ (a,m_T)`, where `m_T` is that
multiplier. The resulting sequence `0 → K(H) → P_φ → A → 0` is exact. Finite-dimensional and
zero Hilbert spaces are included, and `φ` need not be injective or unital.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace CalkinAlgebra

universe uA uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Compact-operator coefficient algebra.** For a complex Hilbert space `H`,
`CompactCoefficients H` is the closed star ideal `K(H)` in `B(H)`, with its inherited operator
norm. -/
abbrev CompactCoefficients (H : Type uH)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  (compactEndomorphismClosedStarIdeal (H := H)).carrier

/-- **C-star structure on compact coefficients.** The compact operators on a complex Hilbert space
have their nonunital C-star algebra structure and operator norm, including finite-dimensional
and zero spaces. -/
instance compactCoefficientsCStarAlgebra : NonUnitalCStarAlgebra (CompactCoefficients H) :=
  (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- **Operator-coordinate Calkin pullback.** For a complex nonunital star homomorphism `φ : A →
Q(H)`, this closed C-star algebra consists of pairs `(T,a)` with `T ∈ B(H)`, `a ∈ A` and `[T]
= φ(a)`, with the product norm. -/
abbrev operatorPullback (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :=
  NonUnitalCStarPullback.Pullback (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- **Compact inclusion into the Calkin pullback.** For a complex nonunital star-algebra
homomorphism `φ : A → Q(H)`, the map `K(H) → P_φ` is the star homomorphism `k ↦ (k,0)`. -/
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

/-- **Quotient projection of the operator pullback.** The complex nonunital star homomorphism `P_φ
→ A` sends `(T,a)` to `a`. -/
def operatorPullbackQuotient (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    operatorPullback φ →⋆ₙₐ[ℂ] A :=
  NonUnitalCStarPullback.sndHom (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- **Operator projection of the Calkin pullback.** The complex nonunital star homomorphism `P_φ →
B(H)` sends a compatible pair `(T,a)` to `T`. -/
def operatorPullbackRepresentation (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    operatorPullback φ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  NonUnitalCStarPullback.fstHom (classStarMap (H := H)).toNonUnitalStarAlgHom φ

/-- **Pair formula for compact inclusion.** Under the product embedding,
`operatorPullbackInclusion φ k = ((k : B(H)),0)`. -/
theorem operatorPullbackInclusion_coe (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) :
    (operatorPullbackInclusion φ k : (H →L[ℂ] H) × A) = ((k : H →L[ℂ] H), 0) := rfl

/-- **Coefficient value of a compatible pair.** For `p : P_φ`, `operatorPullbackQuotient φ p =
p.1.2`, its `A` coordinate. -/
theorem operatorPullbackQuotient_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : operatorPullbackQuotient φ p = p.1.2 := rfl

/-- **Operator value of a compatible pair.** For `p : P_φ`, `operatorPullbackRepresentation φ p =
p.1.1`, its bounded-operator coordinate. -/
theorem operatorPullbackRepresentation_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : operatorPullbackRepresentation φ p = p.1.1 := rfl

/-- **Busby map in compact multiplier coordinates.** Transport the star homomorphism `φ : A →
Q(H)` through `Q(H) ≃ M(K(H))/K(H)`, induced by `T ↦ m_T`, to obtain a Busby homomorphism with
coefficient algebra `K(H)`. -/
def operatorBusbyMap (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CStarExtension.BusbyMap (A := A) (B := CompactCoefficients H) := by
  letI : CStarAlgebra (OuterMultiplier (CompactCoefficients H)) :=
    outerMultiplierCStarAlgebra (CompactCoefficients H)
  exact (DoubleCentralizer.compactOuterMultiplierEquiv (H := H)).symm.toNonUnitalStarAlgHom.comp φ

/-- **Operator and multiplier pullback equivalence.** The star-algebra equivalence from `P_φ` to
its compact-coefficient Busby pullback sends `(T,a)` to `(a,m_T)`, using `B(H) ≃ M(K(H))`. -/
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

/-- **Coordinates of the pullback equivalence.** The multiplier-coordinate image of `p` is
`(p.1.2, DoubleCentralizer.compactMultiplierEquiv p.1.1)` in `A × M(K(H))`. -/
theorem operatorPullbackBusbyEquiv_coe (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) (p : operatorPullback φ) :
    (operatorPullbackBusbyEquiv φ p : A × DoubleCentralizer ℂ (CompactCoefficients H)) =
      (p.1.2, DoubleCentralizer.compactMultiplierEquiv (H := H) p.1.1) := rfl

/-- **Compact inclusion under pullback equivalence.** The image of `(k,0)` under the
operator-to-Busby pullback equivalence is the Busby coefficient inclusion `(0,m_k)`. -/
theorem operatorPullbackBusbyEquiv_inclusion (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) :
    operatorPullbackBusbyEquiv φ (operatorPullbackInclusion φ k) =
      CStarExtension.pullbackInclusion (operatorBusbyMap φ) k := by
  let : CStarAlgebra (OuterMultiplier (CompactCoefficients H)) :=
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

/-- **Quotient compatibility of the pullback equivalence.** The Busby quotient of
`operatorPullbackBusbyEquiv φ p` equals `operatorPullbackQuotient φ p`, the coefficient
coordinate of `p`. -/
theorem operatorPullbackBusbyEquiv_quotient
    (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) (p : operatorPullback φ) :
    CStarExtension.pullbackQuotient (operatorBusbyMap φ) (operatorPullbackBusbyEquiv φ p) =
      operatorPullbackQuotient φ p := rfl

/-- **Injective compact inclusion.** For every complex nonunital star homomorphism `φ : A → Q(H)`,
the map `k ↦ (k,0)` into `P_φ` is injective. -/
theorem operatorPullbackInclusion_injective (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    Function.Injective (operatorPullbackInclusion φ) := by
  intro k l h
  apply Subtype.ext
  exact congrArg (fun p : operatorPullback φ => p.1.1) h

/-- **Surjective coefficient projection.** For every such `φ`, each `a : A` has a compatible
bounded-operator representative of `φ(a)`, so `(T,a) ↦ a` maps `P_φ` onto `A`. -/
theorem operatorPullbackQuotient_surjective (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    Function.Surjective (operatorPullbackQuotient φ) := by
  intro a
  obtain ⟨T, hT⟩ := classStarMap_surjective (H := H) (φ a)
  exact ⟨⟨(T, a), hT⟩, rfl⟩

/-- **Exact Calkin pullback sequence.** The image of `operatorPullbackInclusion φ` equals the
kernel of `operatorPullbackQuotient φ`, giving `0 → K(H) → P_φ → A → 0`. -/
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

/-- **Calkin compatibility of the two projections.** For `p : P_φ`,
`[operatorPullbackRepresentation φ p] = φ(operatorPullbackQuotient φ p)` in `Q(H)`. -/
theorem operatorPullback_compatibility (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) :
    classStarMap (H := H) (operatorPullbackRepresentation φ p) = φ (operatorPullbackQuotient φ p) :=
  p.property

/-- **C-star extension from an operator pullback.** The compatible-pair algebra `P_φ`, compact
inclusion `k ↦ (k,0)` and quotient `(T,a) ↦ a` define an extension of `A` by `K(H)`. -/
def operatorExtension (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H) :
    CStarExtension A (CompactCoefficients H) :=
  CStarExtension.ofExact (operatorPullbackInclusion φ) (operatorPullbackQuotient φ)
    (operatorPullbackInclusion_injective φ) (operatorPullbackQuotient_surjective φ)
    (operatorPullback_exact φ)

/-- **Inclusion of the operator extension.** `(operatorExtension φ).inclusion k =
operatorPullbackInclusion φ k` for each compact operator `k`. -/
theorem operatorExtension_inclusion_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (k : CompactCoefficients H) : (operatorExtension φ).inclusion k =
      operatorPullbackInclusion φ k :=
  CStarExtension.ofExact_inclusion_apply _ _ _ _ _ k

/-- **Quotient of the operator extension.** `(operatorExtension φ).quotient p =
operatorPullbackQuotient φ p`, the coefficient coordinate of the compatible pair. -/
theorem operatorExtension_quotient_apply (φ : A →⋆ₙₐ[ℂ] CalkinAlgebra ℂ H)
    (p : operatorPullback φ) : (operatorExtension φ).quotient p = operatorPullbackQuotient φ p :=
  CStarExtension.ofExact_quotient_apply _ _ _ _ _ p

/-- **Equivalence with the compact-coefficient Busby extension.** The operator extension and the
extension of `operatorBusbyMap φ` are equivalent by `(T,a) ↦ (a,m_T)`, with identity maps on
the coefficient `K(H)` and quotient `A`. -/
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
