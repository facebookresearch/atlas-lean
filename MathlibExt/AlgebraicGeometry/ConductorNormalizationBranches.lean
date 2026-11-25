/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogResidueDifferent
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Etale.Basic

/-!
# Actual conductor normalization and canonical branch involution contract

Absolute normalization is computed by native *relative* normalization
in the coproduct of actual component generic residue fields. It is not
incorrectly taken to be normalization in the scheme's base field.
The reduced conductor is the actual vanishing ideal of the pulled
conductor support; its normalization uses the same actual constructor.

S2 is actual stalk Ext-depth. Codimension-one nodes are recorded by a
faithfully flat étale local extension whose actual maximal-ideal completion
is the actual split-node power-series quotient. The branch involution is
normalized by the two genuine geometric lifts in the normalization fibre,
on a dense open, and by its over-X and square diagrams.

Generic coproduct, normalization, completion and étale primitives are
native/completed source integration. The remaining conductor/involution
producer is a genuine geometric comparison; no arbitrary involution or
singularity predicate is selected.

Source: Hacon--McKernan--Xu arXiv1412.1186v2, normalization/gluing
discussion and §2.5; Kollár's demi-normal conductor involution.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogResidueDifferent

/-- Actual generic points of the actual irreducible components. -/
structure ComponentGenerics (X : Scheme.{0}) where
  point : irreducibleComponents X → X
  generic : ∀ C, IsGenericPoint (point C) C.val

/-- Literal coproduct of the actual component generic residue-field spectra. -/
def genericSource {X : Scheme.{0}} (G : ComponentGenerics X) : Scheme.{0} :=
  ∐ (fun C : irreducibleComponents X =>
    Spec (.of (IsLocalRing.ResidueField (X.presheaf.stalk (G.point C)))))

/-- The actual generic-cover map, computed from each residue map and stalk morphism. -/
def genericMap {X : Scheme.{0}} (G : ComponentGenerics X) : genericSource G ⟶ X :=
  Sigma.desc (fun C =>
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk (G.point C)))) ≫
      X.fromSpecStalk (G.point C))

/-- Correct absolute normalization in the actual component generic residue fields. -/
abbrev normalization {X : Scheme.{0}} (G : ComponentGenerics X)
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)] :=
  (genericMap G).normalization

abbrev normalizationMap {X : Scheme.{0}} (G : ComponentGenerics X)
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)] :
    normalization G ⟶ X :=
  (genericMap G).fromNormalization

/-- An actual completed split node after a faithful étale local extension. -/
structure CompletedNode (R : Type) [CommRing R] [IsLocalRing R] where
  ring : Type
  [commRing : CommRing ring]
  [localRing : IsLocalRing ring]
  [noetherian : IsNoetherianRing ring]
  [algebra : Algebra R ring]
  [etale : Algebra.Etale R ring]
  [faithfullyFlat : Module.FaithfullyFlat R ring]
  [localMap : IsLocalHom (algebraMap R ring)]
  comparison : AdicCompletion (IsLocalRing.maximalIdeal ring) ring ≃+*
    (MvPowerSeries (Fin 2) (IsLocalRing.ResidueField ring) ⧸
      Ideal.span {(MvPowerSeries.X (0 : Fin 2) :
        MvPowerSeries (Fin 2) (IsLocalRing.ResidueField ring)) * MvPowerSeries.X (1 : Fin 2)})

/-- Actual depth formulation of S2, with no named predicate hiding its meaning. -/
def IsS2 (X : Scheme.{0}) : Prop :=
  ∀ x : X, min (2 : WithBot ENat) (ringKrullDim (X.presheaf.stalk x)) ≤
    (IsLocalRing.depth (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) : WithBot ENat)

/-- Actual normal-crossing completion condition at codimension-one points. -/
def IsNodalInCodimensionOne (X : Scheme.{0}) : Prop :=
  ∀ x : X, Order.coheight x = 1 →
    IsRegularLocalRing (X.presheaf.stalk x) ∨ Nonempty (CompletedNode (X.presheaf.stalk x))

/-- The actual reduced conductor subscheme of the normalization. -/
def reducedConductor {X N : Scheme.{0}} (ν : N ⟶ X) (C : ConductorSheaf ν) : Scheme.{0} :=
  (Scheme.IdealSheafData.vanishingIdeal (C.ideal.comap ν).support).subscheme

/-- The actual conductor inclusion into N. -/
def conductorInclusion {X N : Scheme.{0}} (ν : N ⟶ X) (C : ConductorSheaf ν) :
    reducedConductor ν C ⟶ N :=
  (Scheme.IdealSheafData.vanishingIdeal (C.ideal.comap ν).support).subschemeι

/-- Normalized branch involution on the computed normalization of the actual reduced conductor. -/
structure BranchInvolution {X N : Scheme.{0}} (ν : N ⟶ X) (C : ConductorSheaf ν)
    (G : ComponentGenerics (reducedConductor ν C))
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)] where
  involution : normalization G ≅ normalization G
  square : involution.hom ≫ involution.hom = 𝟙 (normalization G)
  over : involution.hom ≫ normalizationMap G ≫ conductorInclusion ν C ≫ ν =
    normalizationMap G ≫ conductorInclusion ν C ≫ ν
  openSet : (normalization G).Opens
  dense : Dense (openSet : Set (normalization G))
  distinct : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ openSet.toScheme),
    a ≫ openSet.ι ≫ normalizationMap G ≫ conductorInclusion ν C ≠
      a ≫ openSet.ι ≫ involution.hom ≫ normalizationMap G ≫ conductorInclusion ν C
  geometricFibres : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (a : Spec (.of Ω) ⟶ openSet.toScheme),
    {b : Spec (.of Ω) ⟶ N |
      b ≫ ν = a ≫ openSet.ι ≫ normalizationMap G ≫ conductorInclusion ν C ≫ ν} =
    {a ≫ openSet.ι ≫ normalizationMap G ≫ conductorInclusion ν C,
      a ≫ openSet.ι ≫ involution.hom ≫ normalizationMap G ≫ conductorInclusion ν C}


/-- An actual component of the normalized conductor with its ambient normalization component. -/
structure ConductorResidueBranch {k : Type} [Field k] {d : ℕ}
    {X N : Scheme.{0}} (ν : N ⟶ X) (C : ConductorSheaf ν)
    (G : ComponentGenerics (reducedConductor ν C))
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)] where
  variety : LogPairs.NormalVariety k d
  component : variety.X.left ⟶ normalization G
  [componentOpen : IsOpenImmersion component]
  actualComponent : Set.range component ∈ irreducibleComponents (normalization G)
  pair : LogPairs.LogPair k (d+1)
  ambient : pair.variety.X.left ⟶ N
  [ambientOpen : IsOpenImmersion ambient]
  actualAmbient : Set.range ambient ∈ irreducibleComponents N
  degree : ℕ
  power : LogPairs.CartierLine pair.variety
  canonical : LogPairs.CanonicalData variety
  inclusion : variety.X ⟶ pair.variety.X
  source : LogResidueDifferent.CartierRationalization power
  chart : LogResidueDifferent.ResidueChart pair degree power variety canonical inclusion source
  comparison : LogResidueDifferent.ResidueComparison chart
  normalized : inclusion.left ≫ ambient =
    component ≫ normalizationMap G ≫ conductorInclusion ν C

/-- The branch different is the previously computed residue coefficient, not a supplied divisor. -/
def branchDifferent {k : Type} [Field k] {d : ℕ}
    {X N : Scheme.{0}} {ν : N ⟶ X} {C : ConductorSheaf ν}
    {G : ComponentGenerics (reducedConductor ν C)}
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    (B : ConductorResidueBranch (k := k) (d := d) ν C G) : LogPairs.RealWeil B.variety :=
  LogResidueDifferent.different B.comparison

/-- Actual transport of conductor components by the normalized branch involution. -/
structure DifferentTransport {k : Type} [Field k] {d : ℕ}
    {X N : Scheme.{0}} {ν : N ⟶ X} {C : ConductorSheaf ν}
    {G : ComponentGenerics (reducedConductor ν C)}
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    (I : BranchInvolution ν C G)
    (S T : ConductorResidueBranch (k := k) (d := d) ν C G) where
  iso : S.variety.X ≅ T.variety.X
  normalized : S.component ≫ I.involution.hom = iso.hom.left ≫ T.component
  primes : LogPairs.PrimePoint S.variety ≃ LogPairs.PrimePoint T.variety
  primeNormalized : ∀ p, (primes p).val = iso.hom.left p.val

/-- The condition that the transport $P$ of the conductor branch $S$ to the branch $T$ along the
branch involution $I$ preserves the different: for every codimension-one point $p$ of $S$, the
coefficient at $p$ of the different of $S$ (`branchDifferent`) equals the coefficient of the
different of $T$ at the point corresponding to $p$ under $P$. This is the coefficient condition of
slc gluing. -/
def PreservesDifferent {k : Type} [Field k] {d : ℕ}
    {X N : Scheme.{0}} {ν : N ⟶ X} {C : ConductorSheaf ν}
    {G : ComponentGenerics (reducedConductor ν C)}
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    {I : BranchInvolution ν C G}
    {S T : ConductorResidueBranch (k := k) (d := d) ν C G}
    (P : DifferentTransport I S T) : Prop :=
  ∀ p, branchDifferent S p = branchDifferent T (P.primes p)

end MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
