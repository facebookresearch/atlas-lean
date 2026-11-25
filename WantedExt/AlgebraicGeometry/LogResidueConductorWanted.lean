/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
public import Batteries.Util.ProofWanted

/-!
# Fixed residue/different and conductor branch comparisons

Hacon--McKernan--Xu, arXiv1412.1186v2, normalization/gluing discussion
and §2.5. Generic normalization and Cartier operations are source-complete
inputs. The requested objects carry the exact computed residue and
two-branch diagrams; neither desired conclusion is an input hypothesis.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogResidueDifferent

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs

def_wanted normalizedResidueComparison
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (P : LogPair k (n+1)) (m : ℕ) (A : CartierLine P.variety)
    (S : NormalVariety k n) (C : CanonicalData S) (i : S.X ⟶ P.variety.X)
    (R : CartierRationalization A) (F : ResidueChart P m A S C i R) :
    ResidueComparison F

end MathlibExt.AlgebraicGeometry.LogResidueDifferent

namespace MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogResidueDifferent

def_wanted normalizedConductorInvolution
    {k : Type} [Field k] [CharZero k]
    (X : CategoryTheory.Over (Spec (.of k))) [IsNoetherian X.left] [IsReduced X.left]
    [LocallyOfFiniteType X.hom] (hs2 : IsS2 X.left) (hnode : IsNodalInCodimensionOne X.left)
    (G : ComponentGenerics X.left)
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    [IsFinite (normalizationMap G)]
    (C : ConductorSheaf (normalizationMap G))
    (H : ComponentGenerics (reducedConductor (normalizationMap G) C))
    [QuasiCompact (genericMap H)] [QuasiSeparated (genericMap H)] :
    BranchInvolution (normalizationMap G) C H

end MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
