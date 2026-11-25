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

public import MathlibExt.Analysis.InnerProductSpace.Operator.CompactMultiplier
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient.ComapEquivalence
public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient.Equivalence

/-!
# The outer multiplier quotient of the compact operators

The inverse of the actual bounded-operator/multiplier equivalence pulls the
compact ideal back to the coefficient ideal. The existing quotient transports
therefore identify the outer multiplier quotient with the existing Calkin
algebra, with literal forward and inverse representative equations.

All carrier and quotient structures are the canonical existing structures.
Zero and finite-dimensional complex Hilbert spaces are included.
-/

@[expose] public section

noncomputable section

open scoped NonUnitalStarSubalgebra.Quotient

namespace DoubleCentralizer

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

Under the inverse bounded-operator/multiplier equivalence, the comap of the compact ideal is
exactly the coefficient ideal. -/
theorem compactMultiplierEquiv_symm_comap :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    ClosedStarIdeal.comap
        (compactMultiplierEquiv (H := H)).symm.toNonUnitalStarAlgHom J =
      coefficientIdeal J.carrier := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let EndH := H →L[ℂ] H
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  let e : EndH ≃⋆ₐ[ℂ] DoubleCentralizer ℂ K := compactMultiplierEquiv (H := H)
  change ClosedStarIdeal.comap e.symm.toNonUnitalStarAlgHom J = coefficientIdeal K
  have hCoeff (a : K) : e (a : EndH) = coeHom (𝕜 := ℂ) a := by
    calc
      e (a : EndH) = multiplierExtensionUnital J (StarAlgEquiv.refl ℂ K)
          (a : EndH) := compactMultiplierEquiv_apply (H := H) _
      _ = coeHom (𝕜 := ℂ) a := by
        change multiplierExtension J (StarAlgEquiv.refl ℂ K) (a : EndH) =
          coeHom (𝕜 := ℂ) a
        exact multiplierExtension_idealEquiv J (StarAlgEquiv.refl ℂ K) a
  have hInvCoeff (a : K) : e.symm (coeHom (𝕜 := ℂ) a) = (a : EndH) :=
    (congrArg e.symm (hCoeff a).symm).trans (e.symm_apply_apply (a : EndH))
  ext m
  change e.symm m ∈ J ↔ m ∈ coefficientIdeal K
  constructor
  · intro hm
    let a : K := ⟨e.symm m, hm⟩
    refine (mem_coefficientIdeal_iff m).mpr ⟨a, ?_⟩
    exact (hCoeff a).symm.trans (e.apply_symm_apply m)
  · intro hm
    obtain ⟨a, ha⟩ := (mem_coefficientIdeal_iff m).mp hm
    rw [← ha, hInvCoeff]
    exact a.property

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

The outer multiplier quotient of the compact ideal is star-algebra equivalent to the existing
Calkin algebra on the same quotient norms. -/
noncomputable def compactOuterMultiplierEquiv :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let _ : CStarAlgebra (OuterMultiplier J.carrier) :=
      outerMultiplierCStarAlgebra J.carrier;
    OuterMultiplier J.carrier ≃⋆ₐ[ℂ] CalkinAlgebra ℂ H := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  let _ : CStarAlgebra (OuterMultiplier K) := outerMultiplierCStarAlgebra K
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ K :=
    compactMultiplierEquiv (H := H)
  let C := coefficientIdeal K
  let I := ClosedStarIdeal.comap e.symm.toNonUnitalStarAlgHom J
  let _ : C.carrier.IsTwoSided := C.isTwoSided
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  have hI : I = C := compactMultiplierEquiv_symm_comap (H := H)
  let qEq : C.Quotient ≃⋆ₐ[ℂ] I.Quotient :=
    ClosedStarIdeal.quotientStarAlgEquivOfEq C I hI.symm
  let qComap : I.Quotient ≃⋆ₐ[ℂ] J.Quotient :=
    NonUnitalStarSubalgebra.quotientEquivComap e.symm J.carrier
  change C.Quotient ≃⋆ₐ[ℂ] J.Quotient
  exact qEq.trans qComap

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

A multiplier's outer class is sent to the Calkin class of its recovered bounded operator. -/
theorem compactOuterMultiplierEquiv_outerQuotientMap :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let _ : CStarAlgebra (OuterMultiplier J.carrier) :=
      outerMultiplierCStarAlgebra J.carrier;
    ∀ m : DoubleCentralizer ℂ J.carrier,
      compactOuterMultiplierEquiv (H := H) (outerQuotientMap (A := J.carrier) m) =
        CalkinAlgebra.classStarMap (H := H)
          ((compactMultiplierEquiv (H := H)).symm m) := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  let _ : CStarAlgebra (OuterMultiplier K) := outerMultiplierCStarAlgebra K
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ K :=
    compactMultiplierEquiv (H := H)
  let C := coefficientIdeal K
  let I := ClosedStarIdeal.comap e.symm.toNonUnitalStarAlgHom J
  let _ : C.carrier.IsTwoSided := C.isTwoSided
  let _ : I.carrier.IsTwoSided := I.isTwoSided
  let _ : J.carrier.IsTwoSided := J.isTwoSided
  have hI : I = C := compactMultiplierEquiv_symm_comap (H := H)
  let qEq : C.Quotient ≃⋆ₐ[ℂ] I.Quotient :=
    ClosedStarIdeal.quotientStarAlgEquivOfEq C I hI.symm
  let qComap : I.Quotient ≃⋆ₐ[ℂ] J.Quotient :=
    NonUnitalStarSubalgebra.quotientEquivComap e.symm J.carrier
  change ∀ m : DoubleCentralizer ℂ K,
    qComap (qEq (C.quotientMap m)) = J.quotientMap (e.symm m)
  intro m
  calc
    qComap (qEq (C.quotientMap m)) = qComap (I.quotientMap m) :=
      congrArg qComap
        (ClosedStarIdeal.quotientStarAlgEquivOfEq_quotientMap C I hI.symm m)
    _ = J.quotientMap (e.symm m) :=
      NonUnitalStarSubalgebra.quotientEquivComap_mk e.symm J.carrier m

/-- Let `H` be an arbitrary complete complex inner-product space, possibly the zero space. Its
compact endomorphisms form the closed ideal in the bounded operator algebra, with the inherited
operator norm; multipliers are bounded double centralizers of that ideal.

A bounded operator's Calkin class is sent back to the outer class of its universal multiplier. -/
theorem compactOuterMultiplierEquiv_symm_classStarMap :
    let J := compactEndomorphismClosedStarIdeal (H := H);
    let _ : NonUnitalCStarAlgebra J.carrier := J.carrierCStarAlgebra;
    let _ : CStarAlgebra (OuterMultiplier J.carrier) :=
      outerMultiplierCStarAlgebra J.carrier;
    ∀ T : H →L[ℂ] H,
      (compactOuterMultiplierEquiv (H := H)).symm
          (CalkinAlgebra.classStarMap (H := H) T) =
        outerQuotientMap (A := J.carrier) (compactMultiplierEquiv (H := H) T) := by
  let J := compactEndomorphismClosedStarIdeal (H := H)
  let K := J.carrier
  let _ : NonUnitalCStarAlgebra K := J.carrierCStarAlgebra
  let _ : CStarAlgebra (OuterMultiplier K) := outerMultiplierCStarAlgebra K
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] DoubleCentralizer ℂ K :=
    compactMultiplierEquiv (H := H)
  let Φ : OuterMultiplier K ≃⋆ₐ[ℂ] CalkinAlgebra ℂ H :=
    compactOuterMultiplierEquiv (H := H)
  change ∀ T : H →L[ℂ] H,
    Φ.symm (CalkinAlgebra.classStarMap (H := H) T) =
      outerQuotientMap (A := K) (e T)
  intro T
  have hForward := compactOuterMultiplierEquiv_outerQuotientMap (H := H) (e T)
  change Φ (outerQuotientMap (A := K) (e T)) =
    CalkinAlgebra.classStarMap (H := H) (e.symm (e T)) at hForward
  have hT : Φ (outerQuotientMap (A := K) (e T)) =
      CalkinAlgebra.classStarMap (H := H) T :=
    hForward.trans
      (congrArg (CalkinAlgebra.classStarMap (H := H)) (e.symm_apply_apply T))
  exact Φ.symm_apply_eq.mpr hT.symm

end DoubleCentralizer
