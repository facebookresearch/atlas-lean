/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
public import MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
public import MathlibExt.AlgebraicGeometry.RationalResolution
public import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# Actual log pluricanonical module and conductor-gluing normalization

The boundary is an actual divisorial ideal I_(mB). Its module is the kernel
of the actual structure unit to its closed subscheme. The log power is the
literal bidual of Hom(I_(mB), omega_X^[m]), with omega_X given by actual
proper quasi-coherent duality. A free log-canonical line is not supplied.

On each actual normalization component, the boundary coefficients are
fixed by the actual pulled ideal orders plus the actual conductor orders.
The Cartier line comparison uses the same global computed log power.
These are the normalized inputs for conductor-different invariance; that
invariance is a conclusion, not a data field assumed as a proof.

Source: Hacon--McKernan--Xu arXiv1412.1186v2, normalization/gluing discussion
and §2.5; Kollár's slc normalization/conductor adjunction.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ConductorLogGluing

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.ConductorNormalizationBranches
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.FourierMukai

/-- The actual ideal module, defined by the native closed-subscheme structure map. -/
def idealModule (X : Scheme.{0}) (I : X.IdealSheafData) : X.Modules :=
  kernel (RationalResolution.structureUnit I.subschemeι)

/-- The order of an ideal along a prime divisor of a normal variety: the least order of a
nonzero local section on an affine open containing the prime. For an ideal vanishing near the
prime the set is empty and the value is `0` by the `sInf` convention, so this is only meaningful
for ideals that are nonzero at the prime. -/
def idealOrder {k : Type} [Field k] {d : ℕ} (V : NormalVariety k d)
    (I : V.X.left.IdealSheafData) (p : PrimePoint V) : ℤ :=
  sInf {a | ∃ (U : V.X.left.Opens) (hU : IsAffineOpen U) (hp : p.val ∈ U),
    letI : Nonempty U := ⟨⟨p.val,hp⟩⟩
    ∃ s : Γ(V.X.left,U), s ≠ 0 ∧ s ∈ I.ideal ⟨U,hU⟩ ∧
      a = V.X.left.ord (V.X.left.germToFunctionField U s) p.val}

variable [HasDerivedPushforwards.{0}]

/-- Actual log pluricanonical module associated with I_(mB), with no free canonical carrier. -/
def logPower {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f)
    (I : X.IdealSheafData) (n m : ℕ) : X.Modules :=
  dual (dual (BundleTrace.homSheaf X (idealModule X I) (canonicalPower P n m)))

/-- Pure dimension on every actual irreducible component. -/
def PureDimension (X : Scheme.{0}) (n : ℕ) : Prop :=
  ∀ C : irreducibleComponents X, topologicalKrullDim C.val = (n : ℕ)

/-- Source-normalized identification of a branch's actual adjoint Cartier power
with the pullback of the same global computed log pluricanonical module. -/
structure LogAdjointBranch {k : Type} [Field k] {d : ℕ}
    {X : Over (Spec (.of k))} {N : Scheme.{0}} {ν : N ⟶ X.left}
    {C : LogResidueDifferent.ConductorSheaf ν}
    {G : ComponentGenerics (reducedConductor ν C)}
    [QuasiCompact (genericMap G)] [QuasiSeparated (genericMap G)]
    (P : ProperReference X.hom) (I : X.left.IdealSheafData) (m : ℕ)
    (S : ConductorResidueBranch (k := k) (d := d) ν C G) where
  degree : S.degree = m
  over : S.ambient ≫ ν ≫ X.hom = S.pair.variety.X.hom
  boundary : ∀ p : PrimePoint S.pair.variety,
    (m : ℝ) * (S.pair.boundary p -
      (idealOrder S.pair.variety (C.ideal.comap (S.ambient ≫ ν)) p : ℝ)) =
        (idealOrder S.pair.variety (I.comap (S.ambient ≫ ν)) p : ℝ)
  avoidsConductor : ∀ p : PrimePoint S.pair.variety,
    0 < idealOrder S.pair.variety (C.ideal.comap (S.ambient ≫ ν)) p →
      idealOrder S.pair.variety (I.comap (S.ambient ≫ ν)) p = 0
  comparison : (Scheme.Modules.pullback (S.ambient ≫ ν)).obj (logPower P I (d+1) m) ≅
    S.power.line.val

end MathlibExt.AlgebraicGeometry.ConductorLogGluing
