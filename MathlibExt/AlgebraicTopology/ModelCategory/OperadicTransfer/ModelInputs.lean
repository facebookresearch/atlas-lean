/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.SourceBranches
import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductAxiom

/-!
# Operadic transfer with chosen monoidal model inputs

`SourceContext` supplies a chosen model structure and closed symmetric
tensor. The transfer statements in this file retain a pushout-product
hypothesis for that same model and tensor. One branch assumes
transfinite stability of weak equivalences; the other retains strong
admissible generation and actual free-cell source smallness at the
specified cardinal.

Pavlov--Scholbach, *Admissibility and rectification of colored symmetric
operads*, arXiv:1410.5675v4, Theorem 5.11(a) and Remark 5.13, uses a
monoidal-model convention without the unit axiom. These statements
therefore do not require unit replacement or unit cofibrancy.
-/

set_option autoImplicit false
noncomputable section
universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer

variable (S : SourceContext.{uW, v, u, us})
/-- The finite tensor of the exact selected source model context. -/
local instance modelInputFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance modelInputTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance modelInputProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

section WeakTransfinite
variable [(weakEquivalences S.C).IsStableUnderTransfiniteComposition.{us}]

/-- The weak-transfinite transfer retains the chosen model inputs.
 The source pushout-product hypothesis is retained although the more
general recognition and attachment proof works without it. The unit axiom is
not required by the adopted Pavlov--Scholbach admissibility source. -/
def fullOperadicModelTransferOfSourceModelWeakTransfinite
    (_hPP : MonoidalPushoutProductAxiom S.C)
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    [IsLocallyPresentable.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (κ₀ : Cardinal.{us}) [Fact κ₀.IsRegular]
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C) :
    FullOperadicModelTransfer S O I J κ₀ :=
  fullOperadicModelTransferOfWeakTransfinite S O I J hI hJ κ₀ h

end WeakTransfinite

/-- The compact-source transfer retains the original compact and free
source-Hom hypotheses. Its selected model is exactly the existing original-cardinal
model, with no change to its generating maps or model classes. The retained
source pushout-product hypothesis is an adopted source hypothesis. -/
@[instance_reducible]
def modelAtOriginalCardinalOfSourceModelCompactSources
    (_hPP : MonoidalPushoutProductAxiom S.C)
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hSourceI : ActualFreeCellSourceSmallness S O I κ)
    (hSourceJ : ActualFreeCellSourceSmallness S O J κ) : ModelCategory (Algebra O) :=
  modelAtOriginalCardinalOfCompactSources S O I J hI hJ hStrong h κ hSourceI hSourceJ

end HomotopicalAlgebra.OperadicTransfer
