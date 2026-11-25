/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLatticeModels
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# General ramified Witt coefficients over a perfect residue field

The coefficient ring is a genuine complete discrete valuation ring,
finite over the original `W(k)`. Its displayed residue identification
commutes with the actual residue map and Witt constant coefficient.
The uniformizer and ramification index are fixed by the actual maximal
and principal ideals. The associated coefficient field is its native
fraction field, not a separately chosen field carrier.

This retains arbitrary perfect characteristic-p residue fields, rather
than restricting Zhu's geometry to finite extensions of `Q_p`.

Source: Zhu, arXiv:1407.8519v3, Section 0.5, pp. 6--7, and
Proposition 1.20, p. 16. No lattice representation or Satake conclusion
is included among these coefficient hypotheses.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
  (B : Type) [CommRing B] [IsDomain B] [Algebra (WittVector p k) B] (pi : B)

/-- The original complete, finite, totally ramified Witt coefficient data. -/
structure CoefficientData where
  [residueCharacteristic : CharP k p]
  perfect : Function.Bijective (fun x : k ↦ x ^ p)
  [discrete : IsDiscreteValuationRing B]
  [complete : IsAdicComplete (Ideal.span {pi}) B]
  [finite : Module.Finite (WittVector p k) B]
  uniformizer_nonzero : pi ≠ 0
  maximal : IsLocalRing.maximalIdeal B = Ideal.span {pi}
  residue : IsLocalRing.ResidueField B ≃+* k
  residue_normalized :
    (residue.toRingHom.comp (IsLocalRing.residue B)).comp
      (algebraMap (WittVector p k) B) = WittVector.constantCoeff
  ramification : ℕ
  ramification_positive : 0 < ramification
  ramification_ideal : Ideal.span {(p : B)} = Ideal.span {pi} ^ ramification

/-- The coefficient field is the actual fraction field of the given DVR. -/
abbrev CoefficientField := FractionRing B

/-- The original Witt fraction field, before the ramified extension. -/
abbrev WittFractionField := Localization.Away (p : WittVector p k)

end MathlibExt.AlgebraicGeometry.RelativeWittCoefficientDVRModels
