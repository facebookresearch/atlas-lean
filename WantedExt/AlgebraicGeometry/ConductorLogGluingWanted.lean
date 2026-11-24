/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConductorLogGluing
public import Batteries.Util.ProofWanted

/-!
# Different invariance for actual demi-normal log pluricanonical data

Hacon--McKernan--Xu arXiv1412.1186v2, normalization/gluing discussion
and §2.5. The global log module is computed from proper duality and the
actual divisorial boundary ideal. Its being a line is the m(K+B)-Cartier
condition on that fixed module. The actual branch/involution residue
comparisons and ideal-order normalizations determine both differents.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConductorLogGluing

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
open MathlibExt.AlgebraicGeometry.FourierMukai

theorem_wanted conductor_different_invariance
    {k : Type} [Field k] [CharZero k] {d : ℕ}
    (X : Over (Spec (.of k))) [IsNoetherian X.left] [IsReduced X.left]
    [LocallyOfFiniteType X.hom]
    (hdim : PureDimension X.left (d+1))
    (hs2 : IsS2 X.left) (hnode : IsNodalInCodimensionOne X.left)
    (F : ComponentGenerics X.left)
    [QuasiCompact (genericMap F)] [QuasiSeparated (genericMap F)]
    [IsFinite (normalizationMap F)]
    (C : LogResidueDifferent.ConductorSheaf (normalizationMap F))
    (G : ComponentGenerics (reducedConductor (normalizationMap F) C))
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    (T : BranchInvolution (normalizationMap F) C G)
    [HasDerivedPushforwards.{0}] (P : ProperReference X.hom)
    (I : X.left.IdealSheafData) (E : Biduality (idealModule X.left I)) [IsIso E.map]
    (m : ℕ) (hm : 0 < m) (hline : IsLineBundle (logPower P I (d+1) m))
    (S₁ S₂ : ConductorResidueBranch (k := k) (d := d) (normalizationMap F) C G)
    (L₁ : LogAdjointBranch P I m S₁) (L₂ : LogAdjointBranch P I m S₂)
    (R : DifferentTransport T S₁ S₂) :
    PreservesDifferent R

end MathlibExt.AlgebraicGeometry.ConductorLogGluing
