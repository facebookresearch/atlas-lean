/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StackVirtualPullbacks

/-!
# Relative rational virtual pullback endpoints

Inputs are finite-type Artin stacks over a fixed field, an actual DM-type
morphism, a locally presented bundle stack, and its fixed intrinsic-cone
closed embedding. The source quotient stratification is explicit. The
recipe fixes the actual specialization/cone/zero-section maps; the
bivariant conclusion and independence of normalized choices are outputs.

Source: Manolache arXiv:0805.2065v2, Condition 3.3 p18,
Construction 3.6 p19 and Theorem 4.4 p28; Kresch
arXiv:math/9810166v1, Sections 4--5. This file does not assert an
unrestricted compatible-triple composition theorem without its derived
obstruction-theory hypotheses.
-/

@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.StackVirtualPullbacksWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackCycleRelations
open _root_.AlgebraicGeometry.StackFibreModels _root_.AlgebraicGeometry.StackChowGroups
open _root_.AlgebraicGeometry.StackBundleCones _root_.AlgebraicGeometry.StackVirtualPullbacks

public def_wanted specialization (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (DM : IsDMType f) (C : IntrinsicConeModel f)
    (hC : FiniteTypeArtin k C.total) : SpecializationData D K hF hG C hC

public def_wanted virtual_pullback_recipe (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total) :
    VirtualPullbackRecipe D K hF hG E hE star.cone hC star.embedding

public def_wanted relative_virtual_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total) : RelativeVirtualPullbackData D K hF hG f E star

public theorem_wanted virtual_pullback_bivariant (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F)
    (R : RelativeVirtualPullbackData D K hF hG f E star) :
    BivariantLaws D K f E.virtualRank (IsGlobalQuotient E) (relativeVirtualPullback R)

public def_wanted refined_gysin_square (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (P Q : TestFamily (scope := FiniteTypeArtin k) f)
    (p : TestPasting P Q) (c : ℕ) (normal : RegularNormalModel p.base c) :
    {N : GysinSquareData D K p c // N.normal = normal}

public theorem_wanted virtual_pullback_independent (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total)
    (R R' : VirtualPullbackRecipe D K hF hG E hE star.cone hC star.embedding) (d : ℤ) :
    virtualPullback R d = virtualPullback R' d

private def check_specialization (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (DM : IsDMType f) (C : IntrinsicConeModel f)
    (hC : FiniteTypeArtin k C.total) : DefWanted (SpecializationData D K hF hG C hC) :=
  specialization k D K F G hF hG f DM C hC

private def check_virtual_pullback_recipe (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total) :
    DefWanted (VirtualPullbackRecipe D K hF hG E hE star.cone hC star.embedding) :=
  virtual_pullback_recipe k D K F G hF hG f E star strata hE hC

private def check_relative_virtual_pullback (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total) :
    DefWanted (RelativeVirtualPullbackData D K hF hG f E star) :=
  relative_virtual_pullback k D K F G hF hG f E star strata hE hC

private def check_virtual_pullback_bivariant (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (R : RelativeVirtualPullbackData D K hF hG f E star) :
    ProofWanted (BivariantLaws D K f E.virtualRank (IsGlobalQuotient E) (relativeVirtualPullback R)) :=
  virtual_pullback_bivariant k D K F G hF hG f E star strata R

private def check_refined_gysin_square (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (P Q : TestFamily (scope := FiniteTypeArtin k) f)
    (p : TestPasting P Q) (c : ℕ) (normal : RegularNormalModel p.base c) :
    DefWanted {N : GysinSquareData D K p c // N.normal = normal} :=
  refined_gysin_square k D K F G hF hG f P Q p c normal

private def check_virtual_pullback_independent (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (F G : Stack (Spec (.of k))) (hF : FiniteTypeArtin k F) (hG : FiniteTypeArtin k G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E)
    (strata : QuotientStratification F) (hE : FiniteTypeArtin k E.total)
    (hC : FiniteTypeArtin k star.cone.total)
    (R R' : VirtualPullbackRecipe D K hF hG E hE star.cone hC star.embedding) (d : ℤ) :
    ProofWanted (virtualPullback R d = virtualPullback R' d) :=
  virtual_pullback_independent k D K F G hF hG f E star strata hE hC R R' d

end WantedExt.AlgebraicGeometry.StackVirtualPullbacksWanted
