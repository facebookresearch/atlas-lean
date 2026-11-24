/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPrimeClasses
public import MathlibExt.AlgebraicGeometry.MotivicCanonicalPowerModels
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Completed c/d coefficients of the canonical motivic total power

The coefficient carrier is the product of all integer-graded coefficient
groups, including infinitely many d powers. Reconstruction is a convergent
series of the native monomials in the topology induced by every original
geometric quotient stage. Both basis maps are fixed by actual external cup.

Equation 9.1 has C_(i+1,d)*c*d^i + D_(i,d)*d^i for i >= 0. Thus C_0 is zero.
Negative coefficient indices are zero by definition. The separate theorem
that negative operation indices vanish is not inferred from that convention.

P^j is D_(d-j,d), and B^j is the independent C_(d-j,d) coefficient.
The identity beta P^j = B^j is a theorem request, never the definition of B.

Source: Voevodsky, arXiv:math/0107109v1, Theorem 6.16,
Equation 9.1 and Lemmas 9.1--9.5, printed pp. 27 and 34--36.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerCoefficients

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicAffineQuotientModels MotivicAffineTateComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open GeneralMotivicBundleThom MotivicFinitePermutationModels
open MotivicGeometricClassifyingSpaces MotivicPrimeClassGeometry MotivicPrimeClasses
open MotivicBocksteinModels MotivicTorusClassModels MotivicCanonicalPowerModels

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D₀ G₀ P E} {A : StandardSchemes P}
  {R₀ : RepresentableSystem D₀ G₀} {S₀ : TransferSheafificationModel D₀ G₀}
  {T : CycleComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D₀) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (I : KInjectiveResolutionSystem k) (Q : PointedSimplicialModuleFunctor k)
  (F : ReducedFreeNisSystem k) (J : ReducedFreeAdjunction F Q)
  {Msec : ModuleSectionSystem Q}
  (V : AffineTateMapSystem (N := N) (B := B) (I := I) (Q := Q))
  (T₀ : AffineThomCycleSections (D₀ := D₀) (G := G₀) (P := P)
    (A := A) (R := R₀) (N := N) (Q := Q) (M := Msec))
  {ell : ℕ}
  [Gconst : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]
  {G : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}

/-- Every regular coefficient D_i and every c coefficient C_(i+1), with their exact integer degrees. -/
abbrev CompletedCoefficients (X : PointedSpaces (k := k)) (p q : ℤ) :=
  ((i : ℕ) → ReducedCohomology B F X (p - (i : ℤ) * dDegree ell)
    (q - (i : ℤ) * primeWeight ell) (ModCoefficients ell)) ×
  ((i : ℕ) → ReducedCohomology B F X (p - cDegree ell - (i : ℤ) * dDegree ell)
    (q - primeWeight ell - (i : ℤ) * primeWeight ell) (ModCoefficients ell))

/-- The actual restrictions to all original geometric quotient stages. -/
def stageRestriction (X : PointedSpaces (k := k)) (p q : ℤ)
    (u : ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q (ModCoefficients ell)) :
    (m : ℕ) → ReducedCohomology B F (smash X (representedPointed (G.step m).quotient.base))
      p q (ModCoefficients ell) :=
  fun m => ReducedMotivicCohomologyModels.pullback B F (smashMap (𝟙 X) (stageMap G m))
    p q (ModCoefficients ell) u

/-- Completion uses the topology of the actual entire quotient diagram. -/
@[instance_reducible] def stageTopology (X : PointedSpaces (k := k)) (p q : ℤ) :
    TopologicalSpace (ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q
      (ModCoefficients ell)) := by
  letI : (m : ℕ) → TopologicalSpace (ReducedCohomology B F
      (smash X (representedPointed (G.step m).quotient.base)) p q (ModCoefficients ell)) :=
    fun _ => ⊥
  exact TopologicalSpace.induced (stageRestriction (G := G) N B F X p q) inferInstance

variable {J₀ : TorusConcatenation A}
  {M₀ : SingularCycleProduct (S := S₀) N T J₀} {Z₀ : EilenbergZilberModel N}
  {V₀ : NegativeTensorComparison N}
  (K₀ : CoefficientMultiplicationSystem N T B M₀ Z₀ V₀)
  (F₀ : KFlatResolutionSystem N) (D : DerivedTensorSource N F₀)
  (S : DerivedTensorShifts N F₀ D) (M₁ : ReducedSmashComultiplication N F)
  (hF : IsFreeTensorComparison N F₀ D F)
  (Eprime : PrimeThomDiagram G) (point : BasedApproximation P G)
  (t : GlobalPrimeThomClass N B I Q F J V T₀ Eprime)
  (delta : CoefficientConeSource B (integralSequence ell) (primeWeight ell))
  (c : BasedIntegralLift N B I Q F J V T₀ Eprime point t delta)

/-- The D_i*d^i term uses the original native external cup. -/
def regularTerm (X : PointedSpaces (k := k)) (p q : ℤ) (i : ℕ)
    (a : ReducedCohomology B F X (p - (i : ℤ) * dDegree ell)
      (q - (i : ℤ) * primeWeight ell) (ModCoefficients ell)) :
    ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q (ModCoefficients ell) :=
  regrade N (B := B) (R₁ := F) (smash X (geometricClassifyingSpace G)) (ModCoefficients ell)
    (by ring) (by ring)
    (externalCup N B K₀ F₀ D S F M₁ hF X (geometricClassifyingSpace G)
      (p - (i : ℤ) * dDegree ell) (q - (i : ℤ) * primeWeight ell)
      ((i : ℤ) * dDegree ell) ((i : ℤ) * primeWeight ell) _ _ _
      (ringCoefficientMultiplication (ULift.{1} (ZMod ell))) a
      (dPower N B I Q F J V T₀ Eprime K₀ F₀ D S M₁ hF t i))

/-- The C_(i+1)*c*d^i term uses the same based lift and original native cup. -/
def oddTerm (X : PointedSpaces (k := k)) (p q : ℤ) (i : ℕ)
    (a : ReducedCohomology B F X (p - cDegree ell - (i : ℤ) * dDegree ell)
      (q - primeWeight ell - (i : ℤ) * primeWeight ell) (ModCoefficients ell)) :
    ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q (ModCoefficients ell) :=
  regrade N (B := B) (R₁ := F) (smash X (geometricClassifyingSpace G)) (ModCoefficients ell)
    (by ring) (by ring)
    (externalCup N B K₀ F₀ D S F M₁ hF X (geometricClassifyingSpace G)
      (p - cDegree ell - (i : ℤ) * dDegree ell)
      (q - primeWeight ell - (i : ℤ) * primeWeight ell)
      (cDegree ell + (i : ℤ) * dDegree ell)
      (primeWeight ell + (i : ℤ) * primeWeight ell) _ _ _
      (ringCoefficientMultiplication (ULift.{1} (ZMod ell))) a
      (cDPower N B I Q F J V T₀ Eprime K₀ F₀ D S M₁ hF point t delta c i))

/-- Equation 9.1's completed series term; the c coefficient is shifted by one. -/
def seriesTerm (X : PointedSpaces (k := k)) (p q : ℤ)
    (a : CompletedCoefficients (ell := ell) N B F X p q) (i : ℕ) :
    ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q (ModCoefficients ell) :=
  oddTerm N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q i (a.2 i) +
    regularTerm N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime t X p q i (a.1 i)

/-- Theorem 6.16 on the actual completed carrier and the native monomial basis. -/
structure CompletedBSDecomposition (X : PointedSpaces (k := k)) (p q : ℤ) where
  expand : ReducedCohomology B F (smash X (geometricClassifyingSpace G)) p q (ModCoefficients ell) ≃+
    CompletedCoefficients (ell := ell) N B F X p q
  regularBasis : ∀ (i : ℕ)
    (a : ReducedCohomology B F X (p - (i : ℤ) * dDegree ell)
      (q - (i : ℤ) * primeWeight ell) (ModCoefficients ell)),
    expand (regularTerm N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime t X p q i a) =
      (Pi.single i a, 0)
  oddBasis : ∀ (i : ℕ)
    (a : ReducedCohomology B F X (p - cDegree ell - (i : ℤ) * dDegree ell)
      (q - primeWeight ell - (i : ℤ) * primeWeight ell) (ModCoefficients ell)),
    expand (oddTerm N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q i a) =
      (0, Pi.single i a)
  reconstruction : ∀ u : ReducedCohomology B F (smash X (geometricClassifyingSpace G))
    p q (ModCoefficients ell),
    letI := stageTopology (G := G) N B F X p q
    HasSum (seriesTerm N B I Q F J V T₀ K₀ F₀ D S M₁ hF Eprime point t delta c X p q
      (expand u)) u

variable [Fact ell.Prime]

/-- The prime weight is ell-1 as an integer, without an unsigned subtraction error. -/
theorem ell_eq_weight_add_one : (ell : ℤ) = primeWeight ell + 1 := by
  have h := (Fact.out : ell.Prime).one_lt
  dsimp [primeWeight]
  omega

/-- A regular coefficient indexed by an arbitrary integer; negative indices are zero. -/
def DCoefficient (X : PointedSpaces (k := k)) (d : ℕ) (i : ℤ)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    ReducedCohomology B F X (2 * (d : ℤ) + 2 * ((d : ℤ) - i) * primeWeight ell)
      ((d : ℤ) + ((d : ℤ) - i) * primeWeight ell) (ModCoefficients ell) := by
  by_cases hi : 0 ≤ i
  · exact regrade N (B := B) (R₁ := F) X (ModCoefficients ell)
      (by rw [Int.toNat_of_nonneg hi]; push_cast; rw [ell_eq_weight_add_one (ell := ell)];
          dsimp [dDegree]; ring)
      (by rw [Int.toNat_of_nonneg hi]; push_cast; rw [ell_eq_weight_add_one (ell := ell)]; ring)
      (a.1 i.toNat)
  · exact 0

/-- C_i is the c*d^(i-1) coefficient. C_0 and every negative index are zero. -/
def CCoefficient (X : PointedSpaces (k := k)) (d : ℕ) (i : ℤ)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    ReducedCohomology B F X (2 * (d : ℤ) + 2 * ((d : ℤ) - i) * primeWeight ell + 1)
      ((d : ℤ) + ((d : ℤ) - i) * primeWeight ell) (ModCoefficients ell) := by
  by_cases hi : 1 ≤ i
  · have hn : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by omega
    exact regrade N (B := B) (R₁ := F) X (ModCoefficients ell)
      (by rw [hn]; push_cast; rw [ell_eq_weight_add_one (ell := ell)];
          dsimp [cDegree, dDegree]; ring)
      (by rw [hn]; push_cast; rw [ell_eq_weight_add_one (ell := ell)]; ring)
      (a.2 (i.toNat - 1))
  · exact 0

/-- Source bidegree shift of the reduced power operation. -/
abbrev pShift (ell : ℕ) (j : ℤ) : ℤ := 2 * j * primeWeight ell

/-- Source Tate shift, allowing all integer operation indices. -/
abbrev qShift (ell : ℕ) (j : ℤ) : ℤ := j * primeWeight ell

/-- P^j on the diagonal is D_(d-j,d), with its exact Tate shift. -/
def PDiagonal (X : PointedSpaces (k := k)) (d : ℕ) (j : ℤ)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    ReducedCohomology B F X (2 * (d : ℤ) + pShift ell j) ((d : ℤ) + qShift ell j)
      (ModCoefficients ell) :=
  regrade N (B := B) (R₁ := F) X (ModCoefficients ell) (by dsimp [pShift]; ring)
    (by dsimp [qShift]; ring) (DCoefficient N B F X d ((d : ℤ) - j) a)

/-- B^j on the diagonal is the independent C_(d-j,d) coefficient. -/
def BDiagonal (X : PointedSpaces (k := k)) (d : ℕ) (j : ℤ)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    ReducedCohomology B F X (2 * (d : ℤ) + pShift ell j + 1) ((d : ℤ) + qShift ell j)
      (ModCoefficients ell) :=
  regrade N (B := B) (R₁ := F) X (ModCoefficients ell) (by dsimp [pShift]; ring)
    (by dsimp [qShift]; ring) (CCoefficient N B F X d ((d : ℤ) - j) a)

omit [N.functor.Additive] [∀ H, (N.functor.obj H).Additive] Gconst in
/-- This is only the negative coefficient-index convention, not Theorem 9.3. -/
theorem D_negative_index (X : PointedSpaces (k := k)) (d : ℕ) (i : ℤ) (hi : i < 0)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    DCoefficient N B F X d i a = 0 := by
  simp [DCoefficient, show ¬0 ≤ i from by omega]

omit [N.functor.Additive] [∀ H, (N.functor.obj H).Additive] Gconst in
/-- C_0 and negative C coefficients are absent from the completed basis. -/
theorem C_nonpositive_index (X : PointedSpaces (k := k)) (d : ℕ) (i : ℤ) (hi : i ≤ 0)
    (a : CompletedCoefficients (ell := ell) N B F X
      (2 * ((ell * d : ℕ) : ℤ)) ((ell * d : ℕ) : ℤ)) :
    CCoefficient N B F X d i a = 0 := by
  simp [CCoefficient, show ¬1 ≤ i from by omega]

end MathlibExt.AlgebraicGeometry.MotivicPowerCoefficients
