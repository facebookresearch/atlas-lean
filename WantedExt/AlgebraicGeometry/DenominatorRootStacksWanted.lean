/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks

/-!
# Actual general denominator-root family construction and algebraicity

Construct the fppf stack with the specified actual extension fibres,
native inverse images, source-generator composition normalizations and
restriction-preserving arrows. Algebraicity and the extra DM conclusion
are separate proof endpoints. Prime-to-characteristic is required only
for the latter conclusion.

Source: Niels Borne and Angelo Vistoli,
https://arxiv.org/abs/1001.0466v2, Definition 4.16 and Proposition 4.19.
The native sheaf-adjoint identity/composition maps are already constructed
in MathlibExt.AlgebraicGeometry.EtaleMonoidCoherence; ordinary category,
scheme and module operations retain their completed source attribution.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.MonoidSheafCharts

universe u

/-- Pull actual monoidal/cartesian DF comparisons along the fixed native functors. -/
def_wanted dfComparisonPullback
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (Y Z : Scheme.{u}) (f : Y ⟶ Z)
    (M N : DeligneFaltingsSheaves.MonoidSheaf Z) (k : M ⟶ N)
    (P : Structure M) (Q : Structure N) (h : ComparisonAlong k P Q) :
    PullbackComparison I f k P Q h

/-- The actual root stack over every parameter base Y, with all native family maps. -/
def_wanted denominatorRootStack
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (j : DenominatorSystem A B)
    (Y : Scheme.{u}) (b : Y ⟶ X) : Model I D j.map b

/-- Coherent denominators give the actual Artin-stack conclusion. -/
theorem_wanted denominatorRootArtin
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (j : DenominatorSystem A B)
    (Y : Scheme.{u}) (b : Y ⟶ X) (R : Model I D j.map b) : R.stack.IsArtinStack

/-- Local invertible Kummer exponents (a sufficient condition, stronger than Borne--Vistoli's
stalkwise criterion) give the distinct DM conclusion. -/
theorem_wanted denominatorRootDeligneMumford
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A B : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (j : DenominatorSystem A B)
    (hprime : PrimeToCharacteristics j.map)
    (Y : Scheme.{u}) (b : Y ⟶ X) (R : Model I D j.map b) : R.stack.IsDeligneMumfordStack
