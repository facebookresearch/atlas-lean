/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StackFirstChernSchemeComparison

/-!
# Native stack zero-section and first-Chern construction requests

The operators and ordinary scheme source maps are already fixed in
MathlibExt. These requests construct their stack adapters and compare them
on the actual scheme dictionary. They do not ask again for the source's
completed scheme Chow, zero-section, or line-bundle homotopy proofs.

References: Kresch, arXiv:math/9810166v1, Theorem 2.1.12;
Fulton, Intersection Theory, Section 3.3. Source revision and Apache
attribution for native scheme operations are in the imported modules.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.StackFirstChernOperatorsWanted

open CategoryTheory _root_.AlgebraicGeometry
open StackCycleGeometry StackCycleRelations StackFibreModels StackVectorBundles
open StackChowGroups StackFirstChernOperators StackFirstChernSchemeComparison
open IntegerSchemeChow IntegralOperationalChow

/-- **The zero section of a vector bundle on a stack.** For a scheme $S$, a stack $X$ over $S$ and a
vector bundle $E$ on $X$: a morphism of stacks $s : X \to E$ to the total space of $E$, with a
2-isomorphism from its composite with the projection $E \to X$ to the identity of $X$, which on
affine points of $X$ is identified with the zero sections of $E$, and which is a closed immersion
(over every scheme point of $E$ its fibre is represented by a closed immersion)
(`StackBundleCones.ZeroSection E`). -/
def_wanted stackZeroSection {S : Scheme.{0}} (X : Stack S) (E : VectorBundle X) :
    StackBundleCones.ZeroSection E

def_wanted stackFirstChernData (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) (X : Stack (Spec (.of k)))
    (hX : FiniteTypeArtin k X) (E : VectorBundle X) (rank_one : E.rank = 1) :
    FirstChernData D K hX E

theorem_wanted stackFirstChernCommutes (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) (X : Stack (Spec (.of k)))
    (hX : FiniteTypeArtin k X) (E F : VectorBundle X)
    (C : FirstChernData D K hX E) (B : FirstChernData D K hX F) (d : ℤ)
    (a : StackChowGroups.ChowGroup D K X hX d) :
    firstChern C (d - 1) (firstChern B d a) =
      firstChern B (d - 1) (firstChern C d a)

def_wanted stackSchemeChernComparison (k : Type) [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
    (K : KreschPresentation D) (X : Stack (Spec (.of k)))
    (hX : FiniteTypeArtin k X) (E : VectorBundle X)
    (C : FirstChernData D K hX E) (U : FieldScheme k)
    (dictionary : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX)
    (comparison : SchemeComparisonData D K U X hX dictionary classes)
    (O : CycleOperations (k := k)) (L : U.scheme.left.Modules)
    (source : SchemeLineSource O U L) (geometry : SchemeGeometry C.zero dictionary source) :
    StackFirstChernSchemeComparison.SchemeComparison D K hX C U dictionary
      classes comparison O L source

end WantedExt.AlgebraicGeometry.StackFirstChernOperatorsWanted
