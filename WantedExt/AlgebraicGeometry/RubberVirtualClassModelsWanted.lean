/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RubberVirtualClassModels

/-!
# Li rubber virtual construction and independent graph comparison requests

The native source, all-coefficient lift/Cech complex, actual torus Lie
quotient, global family/frame descent, cotangent/cone coordinates, virtual recipe and proper epsilon
push are fixed in MathlibExt. The joint comparison constructs the Li
data and proves its DR comparison with the independently defined
graph-sum constant. The equality is an output, with balanced signed
weights and the full stable range retained.
Source: JPPZ arXiv:1602.04705v2, Theorem1 and Section0.2.4;
Jun Li arXiv:math/0110113v1, Sections1--2.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RubberVirtualClassModelsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackCycleRelations StackChowGroups RubberVirtualClassModels
open scoped BigOperators

def_wanted nativeRubberChowPoint (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D) :
    RubberVirtualClassModels.Point D K

def_wanted nativeLiRubberVirtualData (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (Q : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (stableRange : 2 * g + n > 2)
    (B : RubberModuliModel O P Q R S (g := g) a) (Z : RubberVirtualClassModels.Point D K) :
    VirtualData D K O P Q R S a B Z

def_wanted nativeProperRubberEpsilon (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (Q : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (stableRange : 2 * g + n > 2)
    (B : RubberModuliModel O P Q R S (g := g) a)
    (M : StableCurveStackModels.StableCurveStackModel (k := k) g n)
    (E : EpsilonData O P Q R S a B M) : ProperEpsilon D K O P Q R S a B M E

def_wanted nativeDoubleRamificationGraphComparison (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (Q : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (stableRange : 2 * g + n > 2)
    (B : RubberModuliModel O P Q R S (g := g) a) (Z : RubberVirtualClassModels.Point D K)
    (M : StableCurveStackModels.StableCurveStackModel (k := k) g n) (E : EpsilonData O P Q R S a B M)
    (L : PixtonChowPolynomialModels.GraphCatalogue g n)
    (G : PixtonChowPolynomialModels.CatalogueGeometry (D := D) (K := K) L M)
    (C : PixtonChowPolynomialModels.PixtonPolynomial (D := D) (K := K) L M G a g) :
    Σ V : VirtualData D K O P Q R S a B Z,
      {F : ProperEpsilon D K O P Q R S a B M E // Comparison D K O P Q R S a B Z M E L G C V F}

end WantedExt.AlgebraicGeometry.RubberVirtualClassModelsWanted
