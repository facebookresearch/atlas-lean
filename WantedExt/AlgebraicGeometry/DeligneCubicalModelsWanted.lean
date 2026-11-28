/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.OpenDeligneSymbolSources

/-!
# Direct canonical cubical, filtered and rational symbol requests

Every source is the original scheme map, actual line bundle, actual
section/Cartier fraction, same affine subset presentation and native
cochain mate/connecting morphism. The cubical construction requests its
regular torsion normalization, symmetric cocycle and full scalar descent
together. Tensor and rational independence retain those same sources.
The algebraic cubical data is an upstream determinant construction; a
metric pairing, measure or height is never an input.

Sources: Yuan--Zhang, arXiv:2105.13587v9, Section4.2.1, pp107--110,
Theorem4.1.3; Knudsen--Mumford, Sections1--2; Ducrot's determinant
cubical structure and tensor quotient extension. Proofs may remain Wanted.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeligneCubicalModels

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeDeterminantPairings GlobalBoundedDeterminantModels
open DeligneSymbolModels DeligneCubicalModels OpenDeligneSymbolSources CanonicalKoszulDeterminants

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Construct canonical determinant/cubical data and the SAME full algebraic line.
The output includes the symmetric cocycle, source unit rigidity, regular
Koszul torsion normalization and all scalar/presentation coherence. -/
public def_wanted cubicalDeligne {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f n) (L : Fin (n+1) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a) :
    Σ I : DeterminantSources, Σ D : DeligneLine I f n L P, CubicalSources I f n

/-- The projective finite-Tor algebraic construction also covers nonflat
and nonreduced source schemes used in the original Cartier induction. -/
public def_wanted finiteTorCubicalDeligne {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (scope : FiniteTorRelativeScope f n) (L : Fin (n+1) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a) :
    Σ I : DeterminantSources, Σ D : DeligneLine I f n L P, CubicalSources I f n

/-- The entire filtered source is constructed at once; every native SES δ
and every shifted original graded comparison are in the output telescope. -/
public def_wanted fullKoszulAffine {X Y : Scheme.{0}} (f : X ⟶ Y) (m : ℕ)
    (L : Fin m → X.Modules) (s : ∀ i, Γ(L i,⊤)) (K : FullSectionKoszul L s)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P : Presentations f L R a) :
    FullKoszulAffineSource f L s K R a P

/-- Unit rigidity has a genuine full section Koszul source even when the
other line bundles have no nonzero global sections. -/
public def_wanted unitKoszul {X : Scheme.{0}} (m : ℕ) (L : Fin m → X.Modules)
    (hL : ∀ i, IsLineBundle (L i)) (j : Fin m) (h : L j = structureModule X) :
    FullSectionKoszul L (unitSections L j h)

/-- Native open mates and tensor/cochain comparisons are constructed on the original source. -/
public def_wanted openSources {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (scope : RelativeScope f n) (L : Fin (n+1) → X.Modules) (U : Y.Opens) : OpenSources f L U

/-- Construct the full canonical regular section, allowing its actual Cartier zeros
and a finite nonflat final flag. Dense normalization uses the SAME P and native δ.
The sections are regular in every order (`allOrders`, with the same sections): the
dense local generator restricts all orders, and an ordered tuple such as `(1, 0)` is
not regular in the swapped order on any nonempty open. -/
public def_wanted regularSection {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (scope : FiniteTorRelativeScope f n) (C : CubicalSources I f n)
    (L : Fin (n+1) → X.Modules)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (D : DeligneLine I f n L P) (s : StrongRegularTuple f n L)
    (allOrders : AllOrderRegularTuple f n L)
    (sameSections : allOrders.sectionValue = s.sectionValue) :
    CanonicalRegularSection I f n L P D s

/-- The full source regular section is independent on the original normal integral base. -/
public theorem_wanted regularSection_independent {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (scope : FiniteTorRelativeScope f n) (L : Fin (n+1) → X.Modules)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f L R a)
    (D : DeligneLine I f n L P) (s : StrongRegularTuple f n L)
    (S T : CanonicalRegularSection I f n L P D s) : S.sectionValue = T.sectionValue

/-- The canonical tensor comparator has literal shared-cube/exterior coefficient normalization. -/
public def_wanted tensorComparison {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (C : CubicalSources I f n) (N : Fin (n+1) → X.Modules)
    (hN : ∀ i, IsLineBundle (N i)) (j : Fin (n+1)) (B A : X.Modules)
    (hB : IsLineBundle B) (hA : IsLineBundle A)
    (e : CurvePositivity.moduleTensor X (N j) B ≅ A) : TensorComparisonSources I f n C N j B A e

/-- Same source tensors have a unique normalized comparator, including localization descent. -/
public theorem_wanted tensorComparison_independent {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (C : CubicalSources I f n) (N : Fin (n+1) → X.Modules)
    (j : Fin (n+1)) (B A : X.Modules) (e : CurvePositivity.moduleTensor X (N j) B ≅ A)
    (S T : TensorComparisonSources I f n C N j B A e)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y)
    (P : ∀ face : Fin 3, Presentations f (splitFaceLines n N j B A face) R a) :
    S.comparison R a P = T.comparison R a P

/-- Construct the tensor quotient source tree from every actual signed regular fraction branch. -/
public def_wanted rationalSymbols {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (scope : RelativeScope f n) (C : CubicalSources I f n)
    (N : Fin (n+1) → X.Modules) (q : ∀ i, RationalSection (N i))
    (F : FractionRegularTuple f n N q)
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f N R a) :
    Σ B : (∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Module.Basis Unit R (localPairing (P R a))),
      RationalExpression I f n C N q P B

/-- Independence includes fraction choices, insertion order, tensor association,
permutations and source isomorphisms; the original rational tuple and P stay fixed. -/
public theorem_wanted rationalExpression_independent {X Y : Scheme.{0}} (I : DeterminantSources)
    (f : X ⟶ Y) (n : ℕ) (scope : RelativeScope f n) (C : CubicalSources I f n)
    (N : Fin (n+1) → X.Modules) (q : ∀ i, RationalSection (N i))
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f N R a)
    (B D : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Module.Basis Unit R (localPairing (P R a)))
    (S : RationalExpression I f n C N q P B) (T : RationalExpression I f n C N q P D)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) : S.value R a = T.value R a

end WantedExt.AlgebraicGeometry.DeligneCubicalModels
