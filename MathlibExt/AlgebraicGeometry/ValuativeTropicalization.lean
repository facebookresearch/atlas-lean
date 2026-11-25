/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import MathlibExt.AlgebraicGeometry.GeometricChow
/-!
# General valued torus points and initial degeneration contracts

All coordinate rings are the native Laurent monoid algebras K[Z^n]. Points
are actual K-algebra maps annihilating the whole ideal; their coordinates
are mapped units, and the induced quotient-Spec morphism is constructed.
Tropicalization over a chosen valued extension is the closure of the actual
coordinate valuation vectors, with the valuation and topology fixed by
Mathlib's `Valued` instance. No smoothness, hypersurface or genus restriction
is present in these definitions.

A normalizing torus point t gives the actual translated integral closure:
contract I through R[Z^n] → K[Z^n], sending X^a to t^(-a)X^a, then reduce
coefficients to the native valuation-ring residue field. Its quotient-Spec
is the initial scheme. Geometric multiplicity is the sum of the actual
initial-scheme generic-point local-ring lengths after residue algebraic closure.

Reference: W. Gubler, *A guide to tropicalizations*,
https://arxiv.org/abs/1108.6126, Definition5.1, Remark5.7 and Definition13.4.
Native valuation rings/residue maps, and public TauCeti weight-initial/flat
Rees and Newton--Puiseux primitives, are source-complete support. The new
geometric lifting and support comparisons are deferred separately.

Finite rational polyhedral/cone-complex construction, multiplicity independence,
balancing, intersections/proper images, relative family compatibility and
analytic-skeleton comparisons require additional typed providers/proofs.
These definitions allow broad task statements; they do not make those
providers or the complete tropical theory available as small paper glue.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.ValuativeTropicalization
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open scoped BigOperators
abbrev CharacterLattice (n : ℕ) := Fin n → ℤ
abbrev CoordinateRing (K : Type) [CommRing K] (n : ℕ) := AddMonoidAlgebra K (CharacterLattice n)

def characterUnit (K : Type) [CommRing K] (n : ℕ) (a : CharacterLattice n) :
    (CoordinateRing K n)ˣ :=
  ⟨AddMonoidAlgebra.single a 1, AddMonoidAlgebra.single (-a) 1,
    by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def],
    by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]⟩

def coordinateExponent {n : ℕ} (i : Fin n) : CharacterLattice n := Pi.single i 1

def torus (K : Type) [CommRing K] (n : ℕ) : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K n))))

def subscheme {K : Type} [CommRing K] {n : ℕ} (I : Ideal (CoordinateRing K n)) :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (torus K n).hom)

structure Point {K : Type} [CommRing K] {n : ℕ} (I : Ideal (CoordinateRing K n))
    (L : Type) [CommRing L] [Algebra K L] where
  hom : CoordinateRing K n →ₐ[K] L
  annihilates : I ≤ RingHom.ker hom.toRingHom

variable {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}

def coordinates {I : Ideal (CoordinateRing K n)} (p : Point I L) (i : Fin n) : Lˣ :=
  (characterUnit K n (coordinateExponent i)).map p.hom.toRingHom


def characterEval (t : Fin n → Kˣ) : Multiplicative (CharacterLattice n) →* Kˣ where
  toFun a := ∏ i, t i ^ a.toAdd i
  map_one' := by simp
  map_mul' a b := by simp [zpow_add, Finset.prod_mul_distrib]

def scaledMonomials (t : Fin n → Kˣ) :
    Multiplicative (CharacterLattice n) →* CoordinateRing K n where
  toFun a := AddMonoidAlgebra.single a.toAdd (characterEval t a : K)
  map_one' := by simp [characterEval, AddMonoidAlgebra.one_def]
  map_mul' a b := by simp [AddMonoidAlgebra.single_mul_single, map_mul]

def scale (t : Fin n → Kˣ) : CoordinateRing K n →ₐ[K] CoordinateRing K n :=
  AddMonoidAlgebra.lift K (CoordinateRing K n) (CharacterLattice n) (scaledMonomials t)

variable [Valued K NNReal]
abbrev valuationRing := (Valued.v : Valuation K NNReal).valuationSubring
abbrev Residue := IsLocalRing.ResidueField (valuationRing (K := K))

def integralEmbedding (t : Fin n → Kˣ) :
    CoordinateRing (valuationRing (K := K)) n →+* CoordinateRing K n :=
  (scale (fun i => (t i)⁻¹)).toRingHom.comp
    (AddMonoidAlgebra.mapRingHom (CharacterLattice n) (valuationRing (K := K)).toSubring.subtype)

def reduction : CoordinateRing (valuationRing (K := K)) n →+*
    CoordinateRing (Residue (K := K)) n :=
  AddMonoidAlgebra.mapRingHom (CharacterLattice n) (IsLocalRing.residue (valuationRing (K := K)))

def initialIdeal (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ) :
    Ideal (CoordinateRing (Residue (K := K)) n) :=
  (I.comap (integralEmbedding t)).map (reduction (K := K))

abbrev initialScheme (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ) :=
  subscheme (initialIdeal I t)


def quotientPoint {I : Ideal (CoordinateRing K n)} (p : Point I L) :
    CoordinateRing K n ⧸ I →ₐ[K] L :=
  Ideal.Quotient.liftₐ I p.hom (fun _a ha => p.annihilates ha)

def pointMorphism {I : Ideal (CoordinateRing K n)} (p : Point I L) :
    Spec (.of L) ⟶ (subscheme I).left :=
  Spec.map (CommRingCat.ofHom (quotientPoint p).toRingHom)

def baseChangeIdeal (I : Ideal (CoordinateRing K n)) : Ideal (CoordinateRing L n) :=
  I.map (AddMonoidAlgebra.mapRingHom (CharacterLattice n) (algebraMap K L))

def valuationVectorOver [Valued L NNReal] {I : Ideal (CoordinateRing K n)}
    (p : Point I L) : Fin n → ℝ :=
  fun i => -Real.log ((Valued.v : Valuation L NNReal) (coordinates p i : L) : ℝ)

def tropicalizationOver [Valued L NNReal] (I : Ideal (CoordinateRing K n)) : Set (Fin n → ℝ) :=
  closure (Set.range (valuationVectorOver (I := I) (L := L)))

def IsValuedExtension [Valued L NNReal] : Prop :=
  ∀ a : K, (Valued.v : Valuation L NNReal) (algebraMap K L a) =
    (Valued.v : Valuation K NNReal) a

def weightVector (t : Fin n → Kˣ) : Fin n → ℝ :=
  fun i => -Real.log ((Valued.v : Valuation K NNReal) (t i : K) : ℝ)

def geometricInitialIdeal (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ) :
    Ideal (CoordinateRing (AlgebraicClosure (Residue (K := K))) n) :=
  (initialIdeal I t).map (AddMonoidAlgebra.mapRingHom (CharacterLattice n)
    (algebraMap (Residue (K := K)) (AlgebraicClosure (Residue (K := K)))))

abbrev geometricInitialScheme (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ) :=
  subscheme (geometricInitialIdeal I t)

def tropicalMultiplicity (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ)
    [IsNoetherian (geometricInitialScheme I t).left] : ℕ := by
  classical
  let X := (geometricInitialScheme I t).left
  letI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents X)
  exact ∑ Z : irreducibleComponents X,
    MathlibExt.AlgebraicGeometry.GeometricChow.componentMultiplicity X Z

structure InitialPointLift (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ)
    (p : Point (initialIdeal I t) (Residue (K := K))) where
  point : Point I K
  units : Fin n → (valuationRing (K := K))ˣ
  coordinate_eq : ∀ i, coordinates point i =
    t i * (units i).map (valuationRing (K := K)).toSubring.subtype
  residue_eq : ∀ i, (units i).map (IsLocalRing.residue (valuationRing (K := K))) = coordinates p i


/-- Initial degeneration after an actual scalar extension to a valued field. -/
def initialSchemeOver {K L : Type} [Field K] [Field L] [Algebra K L]
    [Valued L NNReal] {n : ℕ} (I : Ideal (CoordinateRing K n)) (t : Fin n → Lˣ) :=
  initialScheme (baseChangeIdeal (L := L) I) t

/-- The length-weighted initial cycle uses the already completed generic
scheme-cycle API; weights are not supplied as an oracle. -/
def initialCycle (I : Ideal (CoordinateRing K n)) (t : Fin n → Kˣ)
    [IsNoetherian (geometricInitialScheme I t).left] :=
  MathlibExt.AlgebraicGeometry.GeometricChow.fundamentalCycle
    (geometricInitialScheme I t).left

end MathlibExt.AlgebraicGeometry.ValuativeTropicalization
