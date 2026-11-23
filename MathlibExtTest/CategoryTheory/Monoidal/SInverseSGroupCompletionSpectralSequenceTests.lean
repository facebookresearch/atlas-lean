/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSGroupCompletionSpectralSequence

/-! # Tests for the additive S-inverse-S homology spectral sequence -/

@[expose] public section

#check CategoryTheory.SInverseS.translationBKHomologySpectralSequence
#check CategoryTheory.SInverseS.translationBKSecondPageIso
#check CategoryTheory.SInverseS.translationBKTotalHomologyFiltration
#check CategoryTheory.SInverseS.translationBKTotalHomologyGradedPiece
#check CategoryTheory.SInverseS.translationBKStablePageGradedIso
#check CategoryTheory.SInverseS.translationBKAbutmentHomologyIso

#print axioms CategoryTheory.SInverseS.translationBKSecondPageIso
#print axioms CategoryTheory.SInverseS.translationBKStablePageGradedIso
#print axioms CategoryTheory.SInverseS.translationBKAbutmentHomologyIso

end
