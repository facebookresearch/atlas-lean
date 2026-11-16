/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The native dictionary follows AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0),
EtaleCohomology/GroupCohomology/Continuous.lean and
EtaleCohomology/GaloisCohomology/MultiplicativeGroupGaloisModule.lean,
and TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9,
Brauer/Basic.lean and Brauer/Restriction.lean (Apache 2.0).
TauCeti copyright (c) 2026 The Tau Ceti contributors; authors:
The Tau Ceti contributors. The Axiom files have no individual author notice.
Modification: expose separately the actual source coefficient object,
injective-resolution derived carrier, continuous cocycles, and geometric
Ext pullback; none of the comparison constructors is postulated here.
-/
module

public import MathlibExt.AlgebraicGeometry.BrauerCoefficients
public import MathlibExt.AlgebraicGeometry.BrauerEvaluation
public import MathlibExt.RepresentationTheory.Continuous.DerivedDiscreteGModules
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Normalized source dictionaries for arithmetic Brauer evaluation

The derived model is Axiom's actual category of discrete continuous
integer modules and exact `rightDerivedPlus` realization. Its native
injective-resolution realization is kept distinct; their comparison is a
source integration obligation. The continuous side is Tau's actual Mathlib carrier.

The two field comparisons below have fixed mathematical endpoints. Their
constructors and their normalization on actual two-cocycle classes belong in
`WantedExt`. Evaluation itself is composed with the native scheme pullback.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerInteroperability

open CategoryTheory CategoryTheory.Limits
open BrauerCoefficients BrauerEvaluation DiscreteGModules
open scoped DiscreteGModules

variable (K : Type) [Field K]

/-- The action object underlying the actual separable-closure unit coefficients. -/
def unitsActionObject : Action (ModuleCat.{0} ℤ) (Field.absoluteGaloisGroup K) :=
  (Rep.RepToAction ℤ (Field.absoluteGaloisGroup K)).obj
    (Rep.of (unitsRep K).ρ.toRepresentation)

/-- The actual unit coefficients in Axiom's discrete continuous module category,
transported from separable Galois automorphisms by restriction. -/
def unitsGModule : ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K) :=
  ⟨⟨unitsActionObject K, by
      constructor
      change Continuous (fun p : Field.absoluteGaloisGroup K × SepUnits K =>
        unitAction K p.1 p.2)
      exact (unitsRepContinuousSMul K).continuous_smul⟩, ⟨rfl⟩⟩

/-- The actual second derived-invariants carrier; enough injectives is an
explicit source provider, rather than an unproved project instance. -/
abbrev DerivedH2 [EnoughInjectives
    (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))] :=
  (derivedCohomology (Field.absoluteGaloisGroup K) 2).obj (unitsGModule K)

/-- The exact Axiom bounded-below-derived realization on the same unit action. -/
abbrev AxiomDerivedH2 [EnoughInjectives
    (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))] :=
  (axiomDerivedCohomology (Field.absoluteGaloisGroup K) 2).obj (unitsGModule K)

/-- The geometric comparison is fixed on every actual finite-Galois Čech realization
of every native cocycle. Its Ext class is the fixed augmentation roof in `BrauerEvaluation`. -/
structure FieldGmComparison where
  realization : ∀ c : TwoCocycles K, GeometricCocycleRealization K c
  val : GmH2 (Spec (.of K)) ≃+ Br K
  normalized : ∀ (c : TwoCocycles K) (R : GeometricCocycleRealization K c),
    val (geometricCechClass R) = cocycleClass K c

/-- The same normalized field family is used at all native residue fields. -/
abbrev FieldComparisonFamily := ∀ (K : Type) [Field K], FieldGmComparison K

/-- The whole Axiom source factorization is separate from the fixed geometric bridge.
It preserves literal degree-zero units and agrees with the geometric Čech normalization
in degree two. No independently chosen derived-cocycle class map is stored. -/
structure AxiomFieldFactorization [EnoughInjectives
    (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))]
    (B : FieldGmComparison K) where
  etale : ∀ n : ℕ, GmH (Spec (.of K)) n ≃+
    (axiomDerivedCohomology (Field.absoluteGaloisGroup K) n).obj (unitsGModule K)
  continuous : ∀ n : ℕ,
    (axiomDerivedCohomology (Field.absoluteGaloisGroup K) n).obj (unitsGModule K) ≃+
      continuousCohomology n (unitsRep K)
  zero_units : ∀ u : Kˣ,
    ((ContinuousCohomology.zeroIso (unitsRep K)).hom
      (continuous 0 (etale 0 (fieldUnitZeroClass K u)))).val =
        Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)) u)
  two_agrees : (etale 2).trans (continuous 2) = B.val

/-- Compare the exact source realization with native injective-resolution homology. -/
abbrev InjectiveRealizationComparison [EnoughInjectives
    (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))] :=
  AxiomDerivedH2 K ≃+ DerivedH2 K

/-- Read the geometrically normalized native field comparison. -/
def fieldComparison (B : FieldGmComparison K) : GmH2 (Spec (.of K)) ≃+ Br K := B.val

/-- Geometric Brauer evaluation uses the actual scheme-point pullback, then
the field comparison. The two comparisons are explicit source dependencies. -/
def evaluate (B : FieldGmComparison K)
    {X : Scheme.{0}} (p : Spec (.of K) ⟶ X) : GmH2 X →+ Br K :=
  (fieldComparison K B).toAddMonoidHom.comp (pointPullback K p)

@[simp] theorem evaluate_apply (B : FieldGmComparison K)
    {X : Scheme.{0}} (p : Spec (.of K) ⟶ X) (a : GmH2 X) :
    evaluate K B p a = B.val (pointPullback K p a) := rfl

theorem fieldComparison_geometric (B : FieldGmComparison K)
    (c : TwoCocycles K) (R : GeometricCocycleRealization K c) :
    fieldComparison K B (geometricCechClass R) = cocycleClass K c := B.normalized c R

/-- Every cocycle has an actual geometric Ext class inside the normalized provider.
This is computed from its Čech roof, rather than being a separately supplied class map. -/
def fieldGeometricClass (B : FieldGmComparison K) (c : TwoCocycles K) :
    GmH2 (Spec (.of K)) := geometricCechClass (B.realization c)

/-- The former simultaneous-negation freedom is excluded on every class not killed by two.
The geometric Ext roof stays fixed; it is not another adjustable class map. -/
theorem geometric_normalization_rejects_negation (B : FieldGmComparison K)
    (c : TwoCocycles K) (R : GeometricCocycleRealization K c)
    (hc : 2 • cocycleClass K c ≠ 0) :
    -(fieldComparison K B (geometricCechClass R)) ≠ cocycleClass K c := by
  rw [fieldComparison_geometric]
  intro h
  have hzero : cocycleClass K c + cocycleClass K c = 0 := by
    calc
      cocycleClass K c + cocycleClass K c = cocycleClass K c + -(cocycleClass K c) :=
        congrArg (fun x => cocycleClass K c + x) h.symm
      _ = 0 := add_neg_cancel _
  exact hc (by simpa only [two_nsmul] using hzero)

section FieldExtension

variable {K} (L : Type) [Field L] [Algebra K L]
  (φ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)

/-- A compatible coefficient pair uses actual separable-closure embeddings.
The normalization on the base field and every Galois automorphism fixes its
meaning; it contains no cohomology map or evaluation field. -/
structure FieldCoefficientPair where
  embedding : SeparableClosure K →+* SeparableClosure L
  base : ∀ a : K,
    embedding (algebraMap K (SeparableClosure K) a) =
      algebraMap L (SeparableClosure L) (algebraMap K L a)
  equivariant : ∀ (g : Field.absoluteGaloisGroup L) (u : SeparableClosure K),
    embedding ((φ g).separableClosure u) = g.separableClosure (embedding u)

/-- The coefficient map is the actual map of units of the closure embedding. -/
def unitsMap (P : FieldCoefficientPair L φ) : SepUnits K →+ SepUnits L :=
  (Units.map P.embedding.toMonoidHom).toAdditive

/-- The actual compatible-pair morphism in `TopRep`, on the normalized unit map. -/
def coefficientMorphism (P : FieldCoefficientPair L φ) :
    TopRep.res (φ : _ →* _) (unitsRep K) ⟶ unitsRep L :=
  TopRep.ofHom {
    toLinearMap := (unitsMap L φ P).toIntLinearMap
    cont := continuous_of_discreteTopology
    isIntertwining' g := by
      ext u
      exact congrArg (fun x : SeparableClosure L => (x : AlgebraicClosure L))
        (P.equivariant g (u.toMul : (SeparableClosure K)ˣ).val) }

/-- Field restriction is the native continuous-cohomology map of that pair. -/
def restriction (P : FieldCoefficientPair L φ) : Br K →+ Br L :=
  (ContinuousCohomology.map φ (coefficientMorphism L φ P) 2).hom.toLinearMap.toAddMonoidHom

/-- Restriction of an actual cocycle is the native cocycle map of the same pair. -/
def restrictCocycle (P : FieldCoefficientPair L φ) : TwoCocycles K →+ TwoCocycles L :=
  (ContinuousCohomology.cocyclesMap φ (coefficientMorphism L φ P) 2).hom.toLinearMap.toAddMonoidHom

/-- The class-level restriction is already fixed on every actual cocycle. -/
theorem restriction_cocycleClass (P : FieldCoefficientPair L φ) (c : TwoCocycles K) :
    restriction L φ P (cocycleClass K c) =
      cocycleClass L (restrictCocycle L φ P c) :=
  ConcreteCategory.congr_hom
    (ContinuousCohomology.π_map φ (coefficientMorphism L φ P) 2) c

end FieldExtension

end AlgebraicGeometry.BrauerInteroperability
