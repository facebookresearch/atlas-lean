/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialResolutionDiagram
public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient.Regular
public import MathlibExt.Algebra.Category.CommAlgCat.HigherAndreQuillenHomology
public import MathlibExt.Algebra.Category.ModuleCat.TensorRestriction.Compatible
public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization

/-!
# Higher André–Quillen homology on the second page

Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. For the canonical
simplicial polynomial resolution `P` of `B`, the higher-form diagram in degree `q` has terms
`B ⊗_{P_i} Λ^q_{P_i} Ω¹_{P_i/k}`. The exterior powers are formed in each simplicial degree,
and the resulting simplicial `B`-module is then normalized.

The regular coefficient module `B` identifies its coefficient-tensor complex with the
normalized higher-form complex. Restriction from `B` to `k` commutes with normalization.
Consequently, page two at `(p,q)` of the polynomial-resolution Hochschild spectral sequence is
isomorphic, as a `k`-module, to the restriction of `higherAndreQuillenHomology k B B q p`.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/-- For a commutative ring `k : Type u` and `B : CommAlgCat.{max u v} k`, the coefficient object
`regularCoefficient k B : ModuleCat.{max u v} B` is `ModuleCat.of B B`, with the
multiplication action of `B` on itself. -/
abbrev regularCoefficient : ModuleCat.{max u v} B := ModuleCat.of B B

/-- Let `k : Type u` be a commutative ring, `B : CommAlgCat.{max u v} k`, and `q : ℕ`. The
simplicial `B`-module `nativeFormDiagram k B q` is `CotangentPushout.higherSimplicial k B q
(resolution k B)`. At a polynomial-resolution term `P_i`, its module is `B ⊗_{P_i} Λ^q_{P_i}
Ω¹_{P_i/k}`. The higher forms are taken degreewise before normalization. -/
abbrev nativeFormDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v} B) :=
  CommAlgCat.CotangentPushout.higherSimplicial.{u, v, 0} k B q (resolution.{u, v} k B)

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, there is an isomorphism of
`B`-module chain complexes
`(higherCotangentCoefficientComplexFunctor k B q).obj (regularCoefficient k B) ≅
CanonicalHigherCotangentComparison.complex k B q`.
It is the regular-coefficient tensor unitor: in each degree, `b ⊗ x` maps to `b • x`, with inverse `x ↦ 1 ⊗ x`. -/
def canonicalHigherRegularIso (q : ℕ) :
    (CommAlgCat.higherCotangentCoefficientComplexFunctor k B q).obj (regularCoefficient k B) ≅
      CommAlgCat.CanonicalHigherCotangentComparison.complex k B q :=
  ChainComplex.TensorCoefficient.regularIso B
    (CommAlgCat.CanonicalHigherCotangentComparison.complex k B q)

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. For `p, q : ℕ`,
`higherAndreQuillenHomology k B (regularCoefficient k B) q p ≅ (CanonicalHigherCotangentComparison.complex k B
q).homology p`.
The isomorphism is induced on degree-`p` homology by the regular-coefficient tensor unitor of the normalized degreewise
higher-form complex. -/
def canonicalHigherRegularHomologyIso (p q : ℕ) :
    CommAlgCat.higherAndreQuillenHomology k B (regularCoefficient k B) q p ≅
      (CommAlgCat.CanonicalHigherCotangentComparison.complex k B q).homology p :=
  HomologicalComplex.homologyMapIso (canonicalHigherRegularIso k B q) p

/-- For a commutative ring `k : Type u`, `B : CommAlgCat.{max u v} k`, and `q : ℕ`, restricting the normalized
higher-form complex from `B` to `k` gives an isomorphism
`((ModuleCat.restrictScalars (algebraMap k B)).mapHomologicalComplex (.down ℕ)).obj
(CanonicalHigherCotangentComparison.complex k B q) ≅ (normalizedMooreComplex (ModuleCat.{max u v} k)).obj (formDiagram k
B q)`.
The source normalizes the simplicial `B`-module first; the target normalizes its restricted `k`-module diagram. -/
def groundHigherNormalizationIso (q : ℕ) :
    ((ModuleCat.restrictScalars.{max u v} (algebraMap k B)).mapHomologicalComplex (.down ℕ)).obj
        (CommAlgCat.CanonicalHigherCotangentComparison.complex k B q) ≅
      (normalizedMooreComplex (ModuleCat.{max u v} k)).obj (formDiagram k B q) :=
  ((AlgebraicTopology.NormalizedQuotient.mooreCompMapIso
    (ModuleCat.restrictScalars.{max u v} (algebraMap k B))).app (nativeFormDiagram k B q))

/-- Let `k : Type u` be a commutative ring and `B : CommAlgCat.{max u v} k`. For every `p, q : ℕ`, the second-page term
is isomorphic as a `k`-module to regular-coefficient higher André–Quillen homology:
`((spectralSequence k B).page 2).X (p,q) ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj (higherAndreQuillenHomology
k B (regularCoefficient k B) q p)`.
The higher-form degree is `q` and the homology degree is `p`. -/
def secondPageAndreQuillenIso (p q : ℕ) :
    ((spectralSequence k B).page 2).X (p, q) ≅
      (ModuleCat.restrictScalars.{max u v} (algebraMap k B)).obj
        (CommAlgCat.higherAndreQuillenHomology k B (regularCoefficient k B) q p) :=
  secondPageFormHomologyIso k B p q ≪≫
    ((DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := formDiagram k B q)).toHomologyIso p).symm ≪≫
    (HomologicalComplex.homologyMapIso (groundHigherNormalizationIso k B q) p).symm ≪≫
    ModuleCat.TensorRestriction.restrictHomologyIso k B
      (CommAlgCat.CanonicalHigherCotangentComparison.complex k B q) p ≪≫
    (ModuleCat.restrictScalars.{max u v} (algebraMap k B)).mapIso
      (canonicalHigherRegularHomologyIso k B p q).symm

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
