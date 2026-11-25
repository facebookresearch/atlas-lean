/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapPicardDegrees
public import Mathlib.Data.Rat.Defs

/-!
# Native section orders and rational quasimap lengths

A section order is the infimum of actual stalk quotient lengths in all
local line trivializations. The rational ratios use a positive power
and a descended invariant section whose whole torsor pullback equals
the original section. The length contract is the minimum of this
specific set, exactly as in Definition 7.1.1.

Degree-one generation is homogeneous generation over the actual
invariant ring; no integral ideal-length formula is assumed without it.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
Definition 7.1.1, equations (7.1.1)–(7.1.2), and Remark 7.1.4.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapSectionLengths

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GroupTorsorGeometry LinearizedLineBundles LineBundleTaskContracts CoherentCurveLinearSeries
open QuasimapBasepointDefects QuasimapPicardDegrees

universe u

/-- The regular coefficient of a local section under an actual line trivialization. -/
def localCoefficient {C : Scheme.{u}} {L : C.Modules} (s : Section L)
    (U : C.Opens) (e : (Scheme.Modules.pullback U.ι).obj L ≅ structureModule U) : Γ(U, ⊤) :=
  (pullbackSection U.ι s ≫ e.hom).val.app (op ⊤) (1 : Γ(U, ⊤))

/-- The actual local quotient length of that coefficient at the specified point. -/
def localSectionOrder {C : Scheme.{u}} {L : C.Modules} (s : Section L)
    (U : C.Opens) (x : U) (e : (Scheme.Modules.pullback U.ι).obj L ≅ structureModule U) : ℕ∞ :=
  Module.length (U.toScheme.presheaf.stalk x)
    ((U.toScheme.presheaf.stalk x) ⧸ Ideal.span
      {U.toScheme.presheaf.germ ⊤ x (by trivial) (localCoefficient s U e)})

/-- The native vanishing order, with no freely selected valuation function. -/
def sectionOrder {C : Scheme.{u}} {L : C.Modules} (s : Section L) (x : C) : ℕ∞ :=
  sInf {r | ∃ (U : C.Opens) (hx : x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ structureModule U),
    localSectionOrder s U ⟨x,hx⟩ e = r}

variable {S : Scheme.{u}} (G W : Over S) [GrpObj G] [ModObj G W]

/-- The equivariant structure is the actual tensor-power action comparison. -/
structure PolarizationPower (L : CharacterPolarization G W) (m : ℕ) where
  line : IsLineBundle (power L.line.module m)
  linearization : Linearization G W (power L.line.module m)
  normalized : linearization.comparison =
    powerComparison G W L.line.linearization L.actionPowers L.projectionPowers m

def PolarizationPower.bundle {L : CharacterPolarization G W} {m : ℕ}
    (P : PolarizationPower G W L m) : LinearizedLineBundle G W :=
  ⟨power L.line.module m, P.line, P.linearization⟩

/-- The invariant section descends through the same actual torsor comparison. -/
structure InvariantSectionLift {T : Over S} (P : QuotientObject G W T)
    (L : CharacterPolarization G W) (m : ℕ)
    (V : PolarizationPower G W L m) (s : Section (power L.line.module m)) where
  line : QuotientLineDescentModels.DescendedLine G W P (V.bundle G W)
  sectionMap : Section line.module
  normalized : pullbackSection P.torsor.projection.left sectionMap ≫ line.comparison.hom =
    pullbackSection P.map.left s

/-- The precise rational ratio set: positive m, invariant s, nonzero native
descended section, and finite actual local quotient order. -/
def ratios {T : Over S} (P : QuotientObject G W T)
    (L : CharacterPolarization G W) (x : T.left) : Set ℚ :=
  {r | ∃ (m : ℕ), 0 < m ∧ ∃ (V : PolarizationPower G W L m)
    (s : Section (power L.line.module m)),
    IsInvariantPowerSection G W L.line.linearization L.actionPowers L.projectionPowers m s ∧
      ∃ (D : InvariantSectionLift G W P L m V s), D.sectionMap ≠ 0 ∧
        ∃ a : ℕ, sectionOrder D.sectionMap x = (a : ℕ∞) ∧ r = (a : ℚ) / m}

/-- The length is the minimum of the actual source ratios. -/
structure BasepointLength {T : Over S} (P : QuotientObject G W T)
    (L : CharacterPolarization G W) (x : T.left) where
  value : ℚ
  attained : value ∈ ratios G W P L x
  least : ∀ r ∈ ratios G W P L x, value ≤ r

theorem BasepointLength.unique {T : Over S} {P : QuotientObject G W T}
    {L : CharacterPolarization G W} {x : T.left}
    (D E : BasepointLength G W P L x) : D.value = E.value :=
  le_antisymm (D.least E.value E.attained) (E.least D.value D.attained)

theorem BasepointLength.nonneg {T : Over S} {P : QuotientObject G W T}
    {L : CharacterPolarization G W} {x : T.left}
    (D : BasepointLength G W P L x) : 0 ≤ D.value := by
  obtain ⟨m, _, _, _, _, _, _, a, _, h⟩ := D.attained
  rw [h]
  exact div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg m)

/-- The invariant regular-function coefficient ring. -/
def invariantRing : Subring Γ(W.left, ⊤) :=
  RingHom.eqLocus (action G W).appTop.hom (projection G W).appTop.hom

/-- Homogeneous products of exactly m degree-one invariant coefficients. -/
def degreeOneProducts (L : CharacterPolarization G W) (m : ℕ) : Set Γ(W.left, ⊤) :=
  {r | ∃ f : Fin m → Section (power L.line.module 1),
    (∀ i, IsInvariantPowerSection G W L.line.linearization L.actionPowers L.projectionPowers
      1 (f i)) ∧ r = ∏ i, invariantCoefficient L 1 (f i)}

/-- The source homogeneous generation condition over the actual invariant ring. -/
def DegreeOneGeneration (L : CharacterPolarization G W) : Prop :=
  ∀ (m : ℕ) (s : Section (power L.line.module m)),
    IsInvariantPowerSection G W L.line.linearization L.actionPowers L.projectionPowers m s →
      invariantCoefficient L m s ∈
        Submodule.span (invariantRing G W) (degreeOneProducts G W L m)

end MathlibExt.AlgebraicGeometry.QuasimapSectionLengths
