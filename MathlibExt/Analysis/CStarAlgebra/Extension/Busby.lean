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

public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic
public import MathlibExt.Analysis.CStarAlgebra.Extension.BusbyDefs
public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Outer
public import MathlibExt.Analysis.CStarAlgebra.Pullback

/-!
# Busby invariants of C-star extensions

For a concrete extension of `A` by `B`, the middle algebra acts on its
distinguished ideal and therefore maps canonically into the multiplier
algebra of `B`.  Passing to the quotient gives the Busby invariant
`A → Q(B)`.  Conversely, a homomorphism `A → Q(B)` defines a concrete
extension by the literal pullback along `M(B) → Q(B)`.
-/

@[expose] public section

noncomputable section

open Set
open scoped CStarAlgebra MultiplierAlgebra

namespace CStarExtension

universe uA uB uE

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

attribute [local instance] CStarExtension.outerCStarAlgebra

/-- The canonical action of the middle algebra on the distinguished ideal,
viewed as a multiplier of the coefficient algebra. -/
noncomputable def multiplierMap
    (X : CStarExtension.{uA, uB, uE} A B) :
    X.Middle →⋆ₙₐ[ℂ] 𝓜(ℂ, B) :=
  DoubleCentralizer.multiplierExtension X.ideal X.idealEquiv

/-- The multiplier action restricts to the canonical coefficient embedding
on the distinguished ideal. -/
theorem multiplierMap_inclusion
    (X : CStarExtension.{uA, uB, uE} A B) (b : B) :
    X.multiplierMap (X.inclusion b) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) b := by
  change DoubleCentralizer.multiplierExtension X.ideal X.idealEquiv
      (X.idealEquiv b : X.Middle) =
    DoubleCentralizer.coeHom (𝕜 := ℂ) b
  exact DoubleCentralizer.multiplierExtension_idealEquiv
    X.ideal X.idealEquiv b

/-- The canonical multiplier action on literal ideal representatives. -/
@[simp]
theorem multiplierMap_idealEquiv_coe
    (X : CStarExtension.{uA, uB, uE} A B) (b : B) :
    X.multiplierMap (X.idealEquiv b : X.Middle) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) b := by
  exact X.multiplierMap_inclusion b

/-- The quotient of the canonical multiplier action vanishes on the
distinguished ideal. -/
theorem outerQuotient_multiplierMap_eq_zero
    (X : CStarExtension.{uA, uB, uE} A B)
    (e : X.Middle) (he : e ∈ X.ideal) :
    outerQuotientMap (X.multiplierMap e) = 0 := by
  obtain ⟨b, hb⟩ := X.idealEquiv.surjective ⟨e, he⟩
  have heq : X.inclusion b = e := congrArg Subtype.val hb
  rw [← heq, multiplierMap_inclusion, outerQuotientMap_coe]

/-- The Busby invariant of a concrete extension. -/
noncomputable def busby
    (X : CStarExtension.{uA, uB, uE} A B) :
    BusbyMap (A := A) (B := B) := by
  let _ : X.ideal.carrier.IsTwoSided := X.ideal.isTwoSided
  let _ : NonUnitalCStarAlgebra X.ideal.Quotient :=
    X.ideal.quotientCStarAlgebra
  let rho : X.Middle →⋆ₙₐ[ℂ] OuterMultiplier B :=
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom.comp X.multiplierMap
  let descended : X.ideal.Quotient →⋆ₙₐ[ℂ] OuterMultiplier B :=
    NonUnitalStarSubalgebra.Quotient.lift X.ideal.carrier rho
      fun e he ↦ outerQuotient_multiplierMap_eq_zero X e he
  exact descended.comp X.quotientEquiv.symm.toNonUnitalStarAlgHom

/-- The Busby invariant is characterized by the quotient of the canonical
multiplier action. -/
theorem busby_quotient
    (X : CStarExtension.{uA, uB, uE} A B) (e : X.Middle) :
    X.busby (X.quotient e) =
      outerQuotientMap (X.multiplierMap e) := by
  let _ : X.ideal.carrier.IsTwoSided := X.ideal.isTwoSided
  let _ : NonUnitalCStarAlgebra X.ideal.Quotient :=
    X.ideal.quotientCStarAlgebra
  change (NonUnitalStarSubalgebra.Quotient.lift X.ideal.carrier
      ((outerQuotientMap (A := B)).toNonUnitalStarAlgHom.comp
        X.multiplierMap)
      (fun e he ↦ outerQuotient_multiplierMap_eq_zero X e he))
      (X.quotientEquiv.symm (X.quotientEquiv
        (X.ideal.quotientMap e))) = _
  rw [X.quotientEquiv.symm_apply_apply]
  rfl

/-- The Busby formula on literal quotient representatives. -/
@[simp]
theorem busby_quotientEquiv_mk
    (X : CStarExtension.{uA, uB, uE} A B) (e : X.Middle) :
    X.busby (X.quotientEquiv (Submodule.Quotient.mk e)) =
      outerQuotientMap (X.multiplierMap e) := by
  exact X.busby_quotient e

/-- A Busby map belongs to an extension when it has the characteristic
quotient formula. -/
def IsBusbyInvariant
    (X : CStarExtension.{uA, uB, uE} A B)
    (τ : BusbyMap (A := A) (B := B)) : Prop :=
  ∀ e : X.Middle,
    τ (X.quotient e) = outerQuotientMap (X.multiplierMap e)

/-- The canonical Busby invariant satisfies its characteristic formula. -/
theorem busby_isBusbyInvariant
    (X : CStarExtension.{uA, uB, uE} A B) :
    IsBusbyInvariant X X.busby :=
  X.busby_quotient

/-- The characteristic quotient formula uniquely determines the Busby
invariant. -/
theorem busby_unique
    (X : CStarExtension.{uA, uB, uE} A B)
    (τ : BusbyMap (A := A) (B := B))
    (hτ : IsBusbyInvariant X τ) :
    τ = X.busby := by
  apply NonUnitalStarAlgHom.ext
  intro a
  obtain ⟨e, rfl⟩ := X.quotient_surjective a
  rw [hτ, busby_quotient]

/-! ## Pullback construction -/

/-- The literal pullback algebra associated to a Busby map. -/
abbrev BusbyPullback (τ : BusbyMap (A := A) (B := B)) :=
  NonUnitalCStarPullback.Pullback τ
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom

/-- The coefficient inclusion into the Busby pullback. -/
noncomputable def pullbackInclusion
    (τ : BusbyMap (A := A) (B := B)) :
    B →⋆ₙₐ[ℂ] BusbyPullback τ := by
  let π := (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
  let zero : B →⋆ₙₐ[ℂ] A := 0
  have h : τ.comp zero = π.comp
      (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B)) := by
    apply NonUnitalStarAlgHom.ext
    intro b
    change τ 0 = outerQuotientMap
      (DoubleCentralizer.coeHom (𝕜 := ℂ) b)
    rw [map_zero, outerQuotientMap_coe]
  exact NonUnitalCStarPullback.lift τ π zero
    (DoubleCentralizer.coeHom (𝕜 := ℂ) (A := B)) h

/-- The quotient projection from the Busby pullback. -/
noncomputable def pullbackQuotient
    (τ : BusbyMap (A := A) (B := B)) :
    BusbyPullback τ →⋆ₙₐ[ℂ] A :=
  NonUnitalCStarPullback.fstHom τ
    (outerQuotientMap (A := B)).toNonUnitalStarAlgHom

@[simp]
theorem pullbackInclusion_fst
    (τ : BusbyMap (A := A) (B := B)) (b : B) :
    NonUnitalCStarPullback.fst τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
        (pullbackInclusion τ b) = 0 :=
  rfl

@[simp]
theorem pullbackInclusion_snd
    (τ : BusbyMap (A := A) (B := B)) (b : B) :
    NonUnitalCStarPullback.snd τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
        (pullbackInclusion τ b) =
      DoubleCentralizer.coeHom (𝕜 := ℂ) b :=
  rfl

theorem pullbackInclusion_injective
    (τ : BusbyMap (A := A) (B := B)) :
    Function.Injective (pullbackInclusion τ) := by
  intro b c hbc
  apply DoubleCentralizer.coeHom_injective
  exact congrArg
    (NonUnitalCStarPullback.snd τ
      (outerQuotientMap (A := B)).toNonUnitalStarAlgHom) hbc

theorem pullbackQuotient_surjective
    (τ : BusbyMap (A := A) (B := B)) :
    Function.Surjective (pullbackQuotient τ) := by
  intro a
  obtain ⟨T, hT⟩ := outerQuotientMap_surjective (τ a)
  exact ⟨NonUnitalCStarPullback.mk τ
      (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
      a T hT.symm, rfl⟩

theorem pullback_exact
    (τ : BusbyMap (A := A) (B := B)) :
    Function.Exact (pullbackInclusion τ) (pullbackQuotient τ) := by
  intro p
  constructor
  · intro hp
    have hcondition := NonUnitalCStarPullback.condition τ
      (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p
    have hπ : outerQuotientMap
        (NonUnitalCStarPullback.snd τ
          (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p) = 0 := by
      calc
        outerQuotientMap
            (NonUnitalCStarPullback.snd τ
              (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p) =
          τ (pullbackQuotient τ p) := hcondition.symm
        _ = 0 := by rw [hp, map_zero]
    have hmem := (outerQuotientMap_eq_zero_iff _).1 hπ
    obtain ⟨b, hb⟩ :=
      (DoubleCentralizer.mem_coefficientIdeal_iff _).1 hmem
    refine ⟨b, ?_⟩
    apply NonUnitalCStarPullback.ext τ
      (outerQuotientMap (A := B)).toNonUnitalStarAlgHom
    · change (0 : A) = pullbackQuotient τ p
      exact hp.symm
    · exact hb
  · rintro ⟨b, rfl⟩
    rfl

/-- The concrete extension defined by a Busby map. -/
noncomputable def ofBusby
    (τ : BusbyMap (A := A) (B := B)) :
    CStarExtension A B :=
  CStarExtension.ofExact
    (pullbackInclusion τ) (pullbackQuotient τ)
    (pullbackInclusion_injective τ)
    (pullbackQuotient_surjective τ)
    (pullback_exact τ)

theorem ofBusby_inclusion
    (τ : BusbyMap (A := A) (B := B)) (b : B) :
    (ofBusby τ).inclusion b = pullbackInclusion τ b :=
  CStarExtension.ofExact_inclusion_apply _ _ _ _ _ b

/-- The ideal-equivalence inclusion of the literal Busby pullback. -/
@[simp]
theorem ofBusby_idealEquiv_coe
    (τ : BusbyMap (A := A) (B := B)) (b : B) :
    ((ofBusby τ).idealEquiv b : (ofBusby τ).Middle) =
      pullbackInclusion τ b := by
  exact ofBusby_inclusion τ b

@[simp]
theorem ofBusby_quotient
    (τ : BusbyMap (A := A) (B := B)) (p : BusbyPullback τ) :
    (ofBusby τ).quotient p = pullbackQuotient τ p :=
  CStarExtension.ofExact_quotient_apply _ _ _ _ _ p

/-- The Busby invariant of the pullback extension is the original map:
`ofBusby` is the converse of `busby`. -/
theorem ofBusby_busby
    (τ : BusbyMap (A := A) (B := B)) :
    (ofBusby τ).busby = τ := by
  have hM : ∀ p : BusbyPullback τ,
      (ofBusby τ).multiplierMap p =
        NonUnitalCStarPullback.snd τ
          (outerQuotientMap (A := B)).toNonUnitalStarAlgHom p := by
    intro p
    have h1 := DoubleCentralizer.multiplierExtension_fst
      (ofBusby τ).ideal (ofBusby τ).idealEquiv p
    have h2 := DoubleCentralizer.multiplierExtension_snd
      (ofBusby τ).ideal (ofBusby τ).idealEquiv p
    apply DoubleCentralizer.ext ℂ B
    apply Prod.ext <;> apply ContinuousLinearMap.ext <;> intro a
    · apply DoubleCentralizer.coeHom_injective
      have h1' : pullbackInclusion τ (((ofBusby τ).multiplierMap p).fst a) =
          p * pullbackInclusion τ a := h1 a
      have hcongr := congrArg (NonUnitalCStarPullback.snd τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom) h1'
      rw [pullbackInclusion_snd] at hcongr
      have hmul := map_mul (NonUnitalCStarPullback.sndHom τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom)
        p (pullbackInclusion τ a)
      simp only [NonUnitalCStarPullback.sndHom_apply,
        pullbackInclusion_snd] at hmul
      rw [hmul] at hcongr
      rw [hcongr]
      exact DoubleCentralizer.mul_coe _ _
    · apply DoubleCentralizer.coeHom_injective
      have h2' : pullbackInclusion τ (((ofBusby τ).multiplierMap p).snd a) =
          pullbackInclusion τ a * p := h2 a
      have hcongr := congrArg (NonUnitalCStarPullback.snd τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom) h2'
      rw [pullbackInclusion_snd] at hcongr
      have hmul := map_mul (NonUnitalCStarPullback.sndHom τ
        (outerQuotientMap (A := B)).toNonUnitalStarAlgHom)
        (pullbackInclusion τ a) p
      simp only [NonUnitalCStarPullback.sndHom_apply,
        pullbackInclusion_snd] at hmul
      rw [hmul] at hcongr
      rw [hcongr]
      exact DoubleCentralizer.coe_mul _ _
  apply NonUnitalStarAlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := (ofBusby τ).quotient_surjective a
  rw [busby_quotient _ p, hM p, ofBusby_quotient τ p]
  exact (NonUnitalCStarPullback.condition τ _ p).symm

end CStarExtension
