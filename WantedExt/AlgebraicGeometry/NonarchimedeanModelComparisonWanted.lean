/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison
public import Batteries.Util.ProofWanted

/-!
# Normalized geometric Gauss valuations on a fixed proper model

Boucksom--Hisamoto--Jonsson, arXiv1504.06568v3, Definition 6.1.
The output has the literal model function field, actual scheme center
and all-polynomial coefficientwise normalization. Ring Gauss-valuation
primitives and the valuative criterion of properness are source-covered;
this requests their exact geometric comparison in the fixed model API.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison

open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels
open MathlibExt.AlgebraicGeometry.CenteredValuationSections

def_wanted gaussModelExtension
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (P : LogPair k n) (L : P.variety.X.left.Modules) (M : VerticalModel P L)
    (v : CenteredValuation P.variety) : GaussModelExtension M v

end MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison
