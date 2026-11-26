/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels
public import MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
public import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesIntegralCoefficientSequenceExact
public import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesBocksteinEqReducedIntegral
public import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesModCoefficientSequenceExact

/-!
# Original finite-power quotient, cycle descent and coefficient requests

Factories construct the actual source-normalized quotient maps and the
unique relative cycles. Affine source tests guarantee effective relative
affine scheme descent; larger smooth sources may use a supplied quotient.
The two coefficient boundaries remain fixed by their own native cone
comparisons. No final power identity, Thom equivalence or arbitrary
Bockstein function is used as an input.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3 and Sections 6/9.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicFinitePowerCycles MotivicPowerQuotientModels MotivicPowerDescentModels
open MotivicBocksteinModels PointedMotivicModels ReducedMotivicCohomologyModels
open NisnevichTransferModels EffectiveMotivicComplexModels MotivicTorusClassModels

/-- Construct the actual free quotient of the original finite affine power times U. -/
def_wanted affinePowerQuotient (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (X : SmoothScheme k) [IsAffine X.scheme.left] : PowerQuotient P U r X

/-- Construct the vector quotient with every original affine coordinate and torsor frame fixed. -/
def_wanted vectorPowerQuotient (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (A : StandardSchemes P) (i : ℕ) :
    {V : VectorQuotient P U r A i // V.IsNormalized P U r}

/-- Descend the actual repeated-X diagonal along the same original U quotient. -/
def_wanted powerDiagonalDescent (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (X : SmoothScheme k) (Q : PowerQuotient P U r X) : DiagonalDescent P U r Q

/-- Construct the unique descended cycle of the literal external power and original target quotient. -/
def_wanted powerCycleDescent (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (X : SmoothScheme k) [IsAffine X.scheme.left] (Q : PowerQuotient P U r X)
    (D : CompositionSystem k) (G : GraphSystem k) (R : Type 1) [CommRing R]
    (A : StandardSchemes P) (i : ℕ) (V : VectorQuotient P U r A i)
    (hV : V.IsNormalized P U r)
    (z : CoefficientCycles X (A.affine i) R) (E : ExternalSystem P) :
    CycleDescent P U r Q D G R A i V z E

/-- Construct the native associated bundle pulled to the original X times U/G base. -/
def_wanted powerBundlePullback (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (X : SmoothScheme k) (A : StandardSchemes P) (i : ℕ)
    (V : VectorQuotient P U r A i) (hV : V.IsNormalized P U r) :
    PullbackPowerBundle P U r A i V (X := X)

/-- Lift the original descended diagonal cycle to that same actual relative bundle. -/
def_wanted relativePowerCycle (k H : Type) [Field k] [Group H] [Fintype H]
    [C : ConstantGroupGeometry (k := k) (H := H)] (P : SmoothProductSystem k)
    (U : FreeQuotient (k := k) (H := H)) (n : ℕ) (r : H →* Equiv.Perm (Fin n))
    (X : SmoothScheme k) [IsAffine X.scheme.left] (Q : PowerQuotient P U r X)
    (D : CompositionSystem k) (G : GraphSystem k) (R : Type 1) [CommRing R]
    (A : StandardSchemes P) (i : ℕ) (V : VectorQuotient P U r A i)
    (hV : V.IsNormalized P U r)
    (z : CoefficientCycles X (A.affine i) R) (E : ExternalSystem P)
    (B : CycleDescent P U r Q D G R A i V z E) (d : DiagonalDescent P U r Q)
    (W : PullbackPowerBundle P U r A i V (X := X)) : RelativePowerCycle P U r Q D G R A i V z B d W

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)

/-- For a prime ℓ, a weight $q \in \mathbb{Z}$ and the given coefficient complex system `B` (over a
field $k$, with Nisnevich sheafification and the correspondence laws and additivity): both
coefficient sequences $\mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/\ell$ (multiplication by ℓ,
reduction) and $\mathbb{Z}/\ell \to \mathbb{Z}/\ell^2 \to \mathbb{Z}/\ell$ ($n \mapsto \ell n$,
reduction) induce maps of weight-$q$ motivic complexes with zero composite, and the comparison map
from the mapping cone of the first map to the complex of the third term is a quasi-isomorphism. -/
theorem_wanted motivicCoefficientSequenceCones (ell : ℕ) [Fact ell.Prime] (q : ℤ) :
  CoefficientConeSource B (integralSequence ell) q ∧ CoefficientConeSource B (modSequence ell) q

end WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted
