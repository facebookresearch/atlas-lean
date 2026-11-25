/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing
public import Batteries.Util.ProofWanted

/-!
# Local unramified extension and integral Chow pairing

Schreieder arXiv1801.05397v5 §2.3 and Proposition 3.1.
The coefficient prime is invertible in the actual base field.
Local extension returns a class in the actual stalk-ring cohomology
which restricts to the given field class, and actual restriction
injectivity. The Chow pairing is the literal finite residue-evaluation
sum on the published integral principal-relation quotient.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.IntegerSchemeChow
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace

/-- **Finite flat transfers at the points of dimension zero.** Let $k$ be a field, $l$ a prime
invertible in $k$, `S` étale cohomology data with mod-$l$ Tate coefficients, $X$ a Noetherian
scheme of finite type over $k$, and `P` stalk comparison data for `S`, assuming for all schemes
and morphisms that sheafification exists on small étale sites, that étale base change is
continuous, and that derived global sections and derived direct images exist. Then there are
point transfers for $X$, whose stalk comparison data is `P` at every point: for every point $x$ of
dimension zero, a finite flat transfer along
$\operatorname{Spec} \kappa(x) \to \operatorname{Spec} k$, given by a coefficient trace normalized
by weighted sums over geometric fibres. -/
def_wanted nativePointTransferComparison
    [AllSheafificationSources] [AllContinuousSources]
    [AllDerivedSectionsSources] [AllDerivedPushSources]
    {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (invertible : IsUnit (l : k))
    (S : Data l) (X : FieldScheme k) (P : StalkSources S) :
    {T : PointTransfers S X // ∀ p, (T.transfer p).stalks = P}

def_wanted smoothPointLocalLift
    [AllSheafificationSources] [AllContinuousSources]
    [AllDerivedSectionsSources] [AllDerivedPushSources]
    {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (invertible : IsUnit (l : k))
    (S : System l) {n : ℕ} (V : NormalVariety k n) [LocallyOfFinitePresentation V.X.hom]
    (i : ℤ) (j : ℕ) (a : varietyUnramified S V invertible i j) (x : V.X.left)
    (smooth : x ∈ V.X.hom.smoothLocus) :
    {L : LocalLift S V invertible i j a x //
      Function.Injective (S.toData.restriction (localGenericMap V x) i j)}

def_wanted globalIntegralChowPairing
    [AllSheafificationSources] [AllContinuousSources]
    [AllDerivedSectionsSources] [AllDerivedPushSources]
    {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (invertible : IsUnit (l : k))
    (S : Data l) (X : FieldScheme k) [IsProper X.scheme.hom] [Smooth X.scheme.hom]
    (T : PointTransfers S X) (i : ℤ) (j : ℕ) :
    {pairing : S.H X.scheme.left i j →+ (ChowGroup X 0 →+ S.H (Spec (.of k)) i j) //
      ∀ a c, pairing a (cycleClass X 0 c) = globalCycleSum S X T i j a c}

def_wanted unramifiedIntegralChowPairing
    [AllSheafificationSources] [AllContinuousSources]
    [AllDerivedSectionsSources] [AllDerivedPushSources]
    {k : Type} [Field k] (l : ℕ) [Fact l.Prime] (invertible : IsUnit (l : k))
    (S : System l) {n : ℕ} (V : NormalVariety k n) [IsProper V.X.hom] [Smooth V.X.hom]
    (T : PointTransfers S.toData (varietyFieldScheme V)) (i : ℤ) (j : ℕ)
    (D : ∀ a : varietyUnramified S V invertible i j, LocalEvaluationData S V invertible i j a) :
    {pairing : varietyUnramified S V invertible i j →+
        (ChowGroup (varietyFieldScheme V) 0 →+ S.toData.H (Spec (.of k)) i j) //
      ∀ a c, pairing a (cycleClass (varietyFieldScheme V) 0 c) =
        unramifiedCycleSum S V T invertible i j a (D a) c}

end MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing
