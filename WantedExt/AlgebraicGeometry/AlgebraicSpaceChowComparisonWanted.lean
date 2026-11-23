/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AlgebraicSpaceChowComparison

/-!
# The ordinary algebraic-space to Kresch Chow comparison

Kresch, math/9810166v1, Theorem 2.1.12(i). The actual etale quotient
space, its whole coherent point diagram, finite-type diagonal scope and
zero-bundle/identity-stage cycle map are fixed before this theorem request.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AlgebraicSpaceChowComparisonWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackCycleRelations StackChowGroups
open AlgebraicSpaceChowComparison

theorem_wanted algebraic_space_comparison (k : Type) [Field k]
    (A : AlgebraicSpaceOver (Spec (.of k))) (X : Stack (Spec (.of k)))
    (M : SpaceDictionary A X) (hX : FiniteTypeArtin k X)
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) (C : CycleClassData D K X hX) (d : ℤ) :
    Function.Bijective (cycleComparison D K hX C d)

private def check_space_comparison (k : Type) [Field k]
    (A : AlgebraicSpaceOver (Spec (.of k))) (X : Stack (Spec (.of k)))
    (M : SpaceDictionary A X) (hX : FiniteTypeArtin k X)
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) (C : CycleClassData D K X hX) (d : ℤ) :
    ProofWanted (Function.Bijective (cycleComparison D K hX C d)) :=
  algebraic_space_comparison k A X M hX D K C d

end WantedExt.AlgebraicGeometry.AlgebraicSpaceChowComparisonWanted
