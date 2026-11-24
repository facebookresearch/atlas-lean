/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies
public import MathlibExt.AlgebraicGeometry.RationalChernZeroHiggsBundles

/-!
# Construction of normalized relative lambda families

Simpson, alg-geom/9604005v1, section 4 and Proposition 4.1.
The connection pullback is fixed on actual native pulled sections in both
degrees. The frame uses the actual section {x}×T, native pullback coherence,
and free-sheaf generators. The zero-fibre functor already uses the literal
connection operator and actual source-normalized differential forms.
Ordinary relative de Rham, tensor and module pullback providers are source
integration; these requests construct the normalized lambda-family layer.
Moduli representability and analytic correspondence remain separate goals.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeLambdaFamiliesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.RelativeDifferentialForms
open MathlibExt.AlgebraicGeometry.RelativeDeRhamDifferential
open MathlibExt.AlgebraicGeometry.AlgebraicLambdaConnections
open MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing
open MathlibExt.AlgebraicGeometry.LambdaZeroHiggsComparison
open MathlibExt.AlgebraicGeometry.RelativeFramedLambdaFamilies
open MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles

def_wanted connection_pullback {Y Y' T T' : Scheme.{0}}
    {pi : Y ⟶ T} {pi' : Y' ⟶ T'} (Q : RelativeSquare pi pi')
    (C : TensorPullbackComparison Q.total) (D : Differential pi) (D' : Differential pi')
    (F : FormBaseChange Q C D D') (lambda : Γ(T, ⊤))
    (N : LambdaConnection pi lambda D) : PulledConnection Q C F N

def_wanted framed_pullback (X : ComplexScheme) {S T : ComplexScheme}
    (x : 𝟙_ ComplexScheme ⟶ X) (f : S ⟶ T) (Q : ProductBaseChange X f)
    (C : TensorPullbackComparison Q.square.total) (n : ℕ) (I : FreePullbackComparison f n)
    (D : Differential (projection X T)) (D' : Differential (projection X S))
    (F : FormBaseChange Q.square C D D') (E : Family X x T D n) : PulledFamily X x f Q C I F E

def_wanted zero_fibre_equivalence (X : ComplexScheme) (D : Differential X.hom)
    (C : AbsoluteFormsComparison X) : ZeroEquivalence (D := D) C

end WantedExt.AlgebraicGeometry.RelativeLambdaFamiliesWanted
