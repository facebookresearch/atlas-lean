/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry
public import MathlibExt.AlgebraicGeometry.AffineCartierTraceIdeals
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Actual boundary-twisted Frobenius trace contracts

The untwisted module is the completed actual O((1-p^e)K_X) subsheaf.
Its finite-duality identification is pinned, on every nonempty open, to
a genuine Frobenius-basis coefficient operator and the actual canonical
top-form coefficient. The boundary map is then computed by the literal
divisor-sheaf inclusion followed by that fixed finite-duality counit.

Admissible boundary twists are the actual integral coefficients of
(1-p^e)(K+Delta); local principality is a proof on the actual sheaf.
Absolute Frobenius is used on schemes, without assuming it is k-linear.
The base field of a log pair is perfect (`LogPairs.CanonicalData.perfect`), so a
Frobenius basis of the function field is given by `n` parameters (a separating
transcendence basis is a p-basis), whose differentials also frame the top forms;
imperfect base fields are not modelled. Generic finite duality, O(D), Frobenius and
Cartier coefficient primitives are source integration; the geometric
normalization/localization bridge is the remaining construction boundary.

Sources: Schwede, arXiv0901.1154v4, Definition 2.12 and Theorem 5.2;
Hacon--Xu arXiv1302.0298v2, §2.3; Axiom finite duality and Tau O(D)
at the revisions recorded in the supporting completed modules.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RationalFunctionModules
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

/-- The actual scheme Frobenius iterate, preserving its scheme scalar twist. -/
def iterated (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (hp : IsInCharacteristic X p) :
    ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | e+1 => iterated X p hp e ≫ absoluteFrobenius X p hp

@[simp]
theorem iterated_preimage (X : Scheme.{0}) (p : ℕ) [Fact p.Prime]
    (hp : IsInCharacteristic X p) (e : ℕ) (U : X.Opens) :
    iterated X p hp e ⁻¹ᵁ U = U := by
  induction e with
  | zero => rfl
  | succ e ih =>
      simp only [iterated, Scheme.Hom.comp_preimage, absoluteFrobenius_preimage, ih]

/-- The actual field module with scalars restricted through the actual Frobenius iterate. -/
abbrev FieldFrobeniusModule (K : Type) [Field K] (p e : ℕ)
    [Fact p.Prime] [CharP K p] :=
  (ModuleCat.restrictScalars (iterateFrobenius K p e)).obj (ModuleCat.of K K)

/-- A genuine full Frobenius p^e-basis, normalized by actual field monomials. -/
structure FrobeniusFieldBasis (K : Type) [Field K] (p e d : ℕ)
    [Fact p.Prime] [CharP K p] where
  parameters : Fin d → K
  basis : Module.Basis (Fin d → Fin (p^e)) K (FieldFrobeniusModule K p e)
  normalized : ∀ a, (basis a : K) = ∏ i, parameters i ^ (a i).val

/-- The actual top exponent in the native Frobenius monomial basis. -/
def topExponent (p e : ℕ) [Fact p.Prime] : Fin (p^e) :=
  ⟨p^e-1, Nat.sub_lt (Nat.pow_pos (Fact.out : p.Prime).pos) (by decide)⟩

/-- Genuine Cartier coefficient extraction from the actual Frobenius module basis. -/
def fieldCoefficient {K : Type} [Field K] {p e d : ℕ}
    [Fact p.Prime] [CharP K p] (B : FrobeniusFieldBasis K p e d) (a : K) : K :=
  B.basis.repr (a : FieldFrobeniusModule K p e) (fun _ => topExponent p e)

/-- Matching the relative canonical form to the actual Frobenius basis: over the perfect base
field of a log pair, the `n` parameters of a Frobenius basis of the function field also give the
top form `dx₁ ∧ ⋯ ∧ dxₙ`. -/
structure CanonicalTraceFrame (P : LogPair k n) (p e : ℕ)
    [Fact p.Prime] [CharP (FunctionField P.variety) p] where
  fieldBasis : FrobeniusFieldBasis (FunctionField P.variety) p e n
  formBasis : Module.Basis Unit (FunctionField P.variety) (RationalTopForms P.variety)
  formNormalized :
    letI := fractionAlgebra P.variety
    formBasis () = exteriorPower.ιMulti (FunctionField P.variety) n
      (fun i => KaehlerDifferential.D k (FunctionField P.variety) (fieldBasis.parameters i))

/-- Corrected Cartier coefficient using the actual chosen canonical top-form coefficient. -/
def canonicalFieldTrace {P : LogPair k n} {p e : ℕ}
    [Fact p.Prime] [CharP (FunctionField P.variety) p]
    (F : CanonicalTraceFrame P p e) (a : FunctionField P.variety) : FunctionField P.variety :=
  fieldCoefficient F.fieldBasis
    (a / (F.formBasis.repr P.canonical.form () : FunctionField P.variety)^(p^e-1))

/-- The actual untwisted integral divisor (1-p^e)K. -/
def untwistedDivisor (P : LogPair k n) (p e : ℕ) : IntegerWeil P.variety :=
  ((1 : ℤ) - (p^e : ℤ)) • canonicalDivisor P.canonical

/-- Floor of the actual boundary-twist coefficients; admissibility requires exact equality. -/
def boundaryDivisor (P : LogPair k n) (p e : ℕ) : IntegerWeil P.variety :=
  Finsupp.mapRange Int.floor (by simp)
    (((1 : ℝ) - (p^e : ℝ)) • (realCast (canonicalDivisor P.canonical) + P.boundary))

variable (P : LogPair k n) (p e : ℕ) [Fact p.Prime]
  (hp : IsInCharacteristic P.variety.X.left p)
  [∀ x : PrimePoint P.variety, IsDiscreteValuationRing (LocalRing P.variety x.val)]
  [HasDerivedPushforwards.{0}]
  [(derivedPushforward (iterated P.variety.X.left p hp e)).IsLeftAdjoint]
  [CharP (FunctionField P.variety) p]

/-- The fixed trace with an untwisted divisorial identification. -/
def untwistedTrace (C : FiniteDualityEmbedding (iterated P.variety.X.left p hp e))
    (α : DivisorialModuleSheaves.sheaf P.variety (untwistedDivisor P p e) ≅
      relativeCanonicalModule (iterated P.variety.X.left p hp e) 0) :
    (Scheme.Modules.pushforward (iterated P.variety.X.left p hp e)).obj
      (DivisorialModuleSheaves.sheaf P.variety (untwistedDivisor P p e)) ⟶
        structureModule P.variety.X.left :=
  (Scheme.Modules.pushforward (iterated P.variety.X.left p hp e)).map α.hom ≫
    moduleTrace _ C

/-- The geometric finite-duality identification is pinned on all actual local sections. -/
structure UntwistedIdentification where
  frame : CanonicalTraceFrame P p e
  embedding : FiniteDualityEmbedding (iterated P.variety.X.left p hp e)
  comparison : DivisorialModuleSheaves.sheaf P.variety (untwistedDivisor P p e) ≅
    relativeCanonicalModule (iterated P.variety.X.left p hp e) 0
  normalized : ∀ (U : P.variety.X.left.Opens) [Nonempty U]
    (s : Γ((Scheme.Modules.pushforward (iterated P.variety.X.left p hp e)).obj
      (DivisorialModuleSheaves.sheaf P.variety (untwistedDivisor P p e)), U)),
    letI : Nonempty (iterated P.variety.X.left p hp e ⁻¹ᵁ U) := by
      rw [iterated_preimage]
      infer_instance
    P.variety.X.left.germToFunctionField U
      ((untwistedTrace P p e hp embedding comparison).app U s) =
        canonicalFieldTrace frame
          (rationalFunctionsEquiv (iterated P.variety.X.left p hp e ⁻¹ᵁ U)
            ((DivisorialModuleSheaves.inclusion P.variety (untwistedDivisor P p e)).app
              (iterated P.variety.X.left p hp e ⁻¹ᵁ U) s))

/-- Admissibility and exact coefficient containment for the actual boundary twist. -/
structure AdmissibleBoundary where
  positive : 0 < e
  integral : realCast (boundaryDivisor P p e) =
    ((1 : ℝ) - (p^e : ℝ)) • (realCast (canonicalDivisor P.canonical) + P.boundary)
  line : IsLineBundle (DivisorialModuleSheaves.sheaf P.variety (boundaryDivisor P p e))
  contained : ∀ x, boundaryDivisor P p e x ≤ untwistedDivisor P p e x

/-- Literal boundary inclusion followed by the normalized actual finite-duality counit. -/
def boundaryTrace (U : UntwistedIdentification P p e hp) (A : AdmissibleBoundary P p e) :
    (Scheme.Modules.pushforward (iterated P.variety.X.left p hp e)).obj
      (DivisorialModuleSheaves.sheaf P.variety (boundaryDivisor P p e)) ⟶
        structureModule P.variety.X.left :=
  (Scheme.Modules.pushforward (iterated P.variety.X.left p hp e)).map
    (DivisorialModuleSheaves.ofLE P.variety A.contained) ≫
      untwistedTrace P p e hp U.embedding U.comparison

/-- Actual global trace image in the structure-sheaf section module. -/
def sectionTraceImage (U : UntwistedIdentification P p e hp) (A : AdmissibleBoundary P p e) :=
  LinearMap.range ((GenericSectionMaps.sections P.variety.X).map
    (boundaryTrace P p e hp U A)).hom

end MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
