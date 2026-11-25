/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller
public import MathlibExt.AlgebraicGeometry.RelativeWittLoopTests

/-!
# Actual local-field coefficients for ramified Witt tests

The coefficient field is a native nonarchimedean local field containing
Q_p by a continuous finite-dimensional field embedding. O_E is its
actual valuation integer ring, and k is its actual residue field.
The uniformizer generates its actual maximal ideal.

The Cohen-Witt dictionary is normalized on the actual residue map,
every Teichmuller representative, and the p-adic ideals. Residue degree
and ramification are fixed by the actual cardinality and ideals.
Ramified Witt test rings then use the literal tensor ring from
RelativeWittLoopTests, with B = O_E and this scalar map.

Sources: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1;
Zhu, arXiv:1407.8519v3, Section 1.4. The Cohen-Witt dictionary is
completed-source integration data; no arbitrary residue or integer ring
is chosen independently of E.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ValuativeRel
open RelativeWittLoopTests

variable (p : ℕ) [Fact p.Prime]

/-- A genuine mixed-characteristic local coefficient field over Q_p. -/
structure MixedField where
  field : Type
  [fieldStructure : Field field]
  [characteristicZero : CharZero field]
  [relation : ValuativeRel field]
  [topology : TopologicalSpace field]
  [localField : IsNonarchimedeanLocalField field]
  [padicAlgebra : Algebra ℚ_[p] field]
  [finite : FiniteDimensional ℚ_[p] field]
  continuous_padic : Continuous (algebraMap ℚ_[p] field)

attribute [instance] MixedField.fieldStructure MixedField.characteristicZero
  MixedField.relation MixedField.topology MixedField.localField
  MixedField.padicAlgebra MixedField.finite

/-- The original valuation integer ring of E. -/
abbrev Integers (E : MixedField p) := ↥𝒪[E.field]

/-- The original residue field of that exact integer ring. -/
abbrev Residue (E : MixedField p) := IsLocalRing.ResidueField (Integers p E)

/-- Actual residue reduction, not a separate field or evaluation oracle. -/
def reduction (E : MixedField p) : Integers p E →+* Residue p E :=
  IsLocalRing.residue _

/-- The local coefficient dictionary is fixed by genuine uniformizer and Witt data. -/
structure CoefficientData (E : MixedField p) where
  [residueCharacteristic : CharP (Residue p E) p]
  uniformizer : Integers p E
  nonzero : (uniformizer : E.field) ≠ 0
  maximal : IsLocalRing.maximalIdeal (Integers p E) = Ideal.span {uniformizer}
  residueDegree : ℕ
  degree_positive : 0 < residueDegree
  residue_card : Nat.card (Residue p E) = p ^ residueDegree
  ramification : ℕ
  ramification_positive : 0 < ramification
  ramification_ideal : Ideal.span {(p : Integers p E)} =
    Ideal.span {uniformizer} ^ ramification
  cohen : WittVector p (Residue p E) →+* Integers p E
  residue_normalized : (reduction p E).comp cohen = WittVector.constantCoeff
  teichmuller_normalized : ∀ a : Residue p E,
    cohen (WittVector.teichmuller p a) ^ Nat.card (Residue p E) =
      cohen (WittVector.teichmuller p a)
  adic_normalized : ∀ n : ℕ, ∃ m : ℕ,
    Ideal.map cohen (Ideal.span {(p : WittVector p (Residue p E))} ^ m) ≤
      IsLocalRing.maximalIdeal (Integers p E) ^ n

/-- The scalar algebra on O_E uses exactly the displayed Cohen-Witt dictionary. -/
@[instance_reducible]
def coefficientAlgebra {E : MixedField p} (C : CoefficientData p E) :
    Algebra (WittVector p (Residue p E)) (Integers p E) := C.cohen.toAlgebra

/-- The actual ramified Witt ring of a perfect residue-algebra test. -/
abbrev RamifiedWitt {E : MixedField p} (C : CoefficientData p E)
    (R : PerfectAlgebra p (Residue p E)) :=
  letI := coefficientAlgebra p C
  Integral p (Residue p E) (Integers p E) R

/-- The actual rational ramified Witt ring, inverted at the true uniformizer. -/
abbrev RamifiedRational {E : MixedField p} (C : CoefficientData p E)
    (R : PerfectAlgebra p (Residue p E)) :=
  letI := coefficientAlgebra p C
  Rational p (Residue p E) (Integers p E) C.uniformizer R

/-- Every ramified scalar restriction is the actual tensor Witt map. -/
def ramifiedMap {E : MixedField p} (C : CoefficientData p E)
    {R S : PerfectAlgebra p (Residue p E)} (f : R ⟶ S) :
    RamifiedWitt p C R →+* RamifiedWitt p C S :=
  letI := coefficientAlgebra p C
  integralMap p (Residue p E) (Integers p E) f

/-- Every rational restriction is that same map after actual uniformizer inversion. -/
def ramifiedRationalMap {E : MixedField p} (C : CoefficientData p E)
    {R S : PerfectAlgebra p (Residue p E)} (f : R ⟶ S) :
    RamifiedRational p C R →+* RamifiedRational p C S :=
  letI := coefficientAlgebra p C
  rationalMap p (Residue p E) (Integers p E) C.uniformizer f

end MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
