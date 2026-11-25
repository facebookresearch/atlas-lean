/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PolarizedHiggsStability
public import MathlibExt.AlgebraicGeometry.BettiCharacteristicClasses

/-!
# Actual all-rational-Chern-zero Higgs bundles

Every positive rational Chern class is the existing normalized Betti class
obtained from the actual tautological line and projective-bundle inverse.
Neither a free Chern map nor equality of Hilbert coefficients is used.
Stability tests the actual invariant coherent torsion-free subsheaves.

Reference: Carlos Simpson, *The Hodge filtration on nonabelian cohomology*,
alg-geom/9604005v1, Theorem 2.3 and Proposition 4.1. Characteristic-class
source revision, license and normalization are retained in
`BettiCharacteristicClasses`; ordinary source providers remain independent.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalChernZeroHiggsBundles

open _root_.CategoryTheory _root_.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open BettiGysin AlgebraicBundleGeometry BettiCharacteristicClasses
open PolarizedHiggsStability ProjectiveLineSystems

structure ChernGeometry (X : ComplexScheme) (d n : ℕ) (E : X.left.Modules) where
  projectiveRank : ℕ
  rank_eq : n = projectiveRank + 1
  projective : ProjectiveBundle X d projectiveRank E
  tautologicalTotal : LineTotalSpace projective.total (d + projectiveRank) projective.tautological

variable
  (D : ∀ (X : ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
  (T : ProjectiveBundleTheory D P)
  {X : ComplexScheme} [IsComplexVariety X] {d n : ℕ} [SmoothOfRelativeDimension d X.hom]
  {E : X.left.Modules}

def AllRationalChernZero (G : ChernGeometry X d n E) : Prop :=
  ∀ i : ℕ, 0 < i → chern D P d G.projectiveRank E G.projective G.tautologicalTotal T i = 0

variable {H : LineBundle X.left} (N : HilbertNumerics X H d)

def SemistableChernZero (E : CoherentBundle X)
    (G : ChernGeometry X d E.bundle.rank E.bundle.module) : Prop :=
  IsSemistable N E ∧ AllRationalChernZero D P T G

def PolystableChernZero (E : CoherentBundle X)
    (G : ChernGeometry X d E.bundle.rank E.bundle.module) : Prop :=
  IsPolystable N E ∧ AllRationalChernZero D P T G

end MathlibExt.AlgebraicGeometry.RationalChernZeroHiggsBundles
