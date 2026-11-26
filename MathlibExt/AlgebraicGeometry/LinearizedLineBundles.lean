/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks
(https://github.com/AxiomMath/Stacks), revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no individual copyright or author notice.

* `StacksFrontier/AlgebraicGeometry/GroupScheme/Pullback.lean`: `reindexHom`;
* in `StacksFrontier/AlgebraicGeometry/Groupoids/GroupSchemeProperties/`:
  `EquivariantModule.lean` (`IsDescentCocycle`) and `EquivariantQuasicoherentModule.lean`
  (the action-coordinate cocycle and the identity normalization).

Modifications: the equivariant comparison is specialized to an invertible module isomorphism,
with the scheme pullbacks and canonical comparison maps kept; the invariant-section interface
is new.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Mod
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# General group-scheme actions, line linearizations and quotient signatures

The acting group and scheme are actual objects over an arbitrary scheme.
Linearization is the actual pullback isomorphism with its unit and cocycle
diagrams. Powers and invariant sections use fixed ordinary tensor and
pullback maps. A categorical quotient is specified by actual scheme maps
and their universal property; no quotient existence is asserted without
the required geometric assumptions.

References: Stacks Project, Tag 03LF; Mumford--Fogarty--Kirwan,
*Geometric Invariant Theory*, §1.3 (linearizations) and §1.4 (quotients).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LinearizedLineBundles

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

universe u

/-- The completed canonical reindexing of a map between module pullbacks. -/
def reindexHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules} (α : (Scheme.Modules.pullback g).obj F ⟶
      (Scheme.Modules.pullback h).obj F) :
    (Scheme.Modules.pullback (f ≫ g)).obj F ⟶ (Scheme.Modules.pullback (f ≫ h)).obj F :=
  (Scheme.Modules.pullbackComp f g).inv.app F ≫ (Scheme.Modules.pullback f).map α ≫
    (Scheme.Modules.pullbackComp f h).hom.app F

/-- The actual descent cocycle, including its canonical pullback comparisons. -/
def IsDescentCocycle {D R U : Scheme.{u}} (p q c : D ⟶ R) (t s : R ⟶ U)
    (ht : c ≫ t = p ≫ t) (hm : p ≫ s = q ≫ t) (hs : c ≫ s = q ≫ s) {F : U.Modules}
    (α : (Scheme.Modules.pullback t).obj F ⟶ (Scheme.Modules.pullback s).obj F) : Prop :=
  (Scheme.Modules.pullbackCongr ht).hom.app F ≫ reindexHom p α ≫
      (Scheme.Modules.pullbackCongr hm).hom.app F ≫ reindexHom q α ≫
      (Scheme.Modules.pullbackCongr hs.symm).hom.app F = reindexHom c α

variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]

/-- The actual scheme action map. -/
abbrev action : (G ⊗ X).left ⟶ X.left := γ[G,X].left

/-- The actual projection in the action diagram. -/
abbrev projection : (G ⊗ X).left ⟶ X.left := (snd G X).left

/-- The actual unit section of the action. -/
def unitAction : X ⟶ G ⊗ X := (λ_ X).inv ≫ (η[G] ▷ X)

theorem unitAction_action : unitAction G X ≫ γ[G,X] = 𝟙 X := by
  rw [unitAction, Category.assoc]
  have h : (η[G] ▷ X) ≫ γ[G,X] = (λ_ X).hom := ModObj.one_smul (M := G) (X := X)
  rw [h, Iso.inv_hom_id]

omit [ModObj G X] in
theorem unitAction_projection : unitAction G X ≫ snd G X = 𝟙 X := by
  simp [unitAction]

theorem multiplication_action :
    ((α_ G G X).inv ≫ μ[G] ▷ X) ≫ γ[G,X] = (G ◁ γ[G,X]) ≫ γ[G,X] := by
  rw [Category.assoc]
  exact (Iso.inv_comp_eq _).2 (ModObj.mul_smul (M := G) (X := X))

theorem action_projection :
    (G ◁ γ[G,X]) ≫ snd G X = snd G (G ⊗ X) ≫ γ[G,X] :=
  whiskerLeft_snd _ _

omit [ModObj G X] in
theorem multiplication_projection :
    ((α_ G G X).inv ≫ μ[G] ▷ X) ≫ snd G X = snd G (G ⊗ X) ≫ snd G X := by
  simp

/-- The normalized cocycle on the actual G×G×X action diagram. -/
def IsActionCocycle {L : X.left.Modules}
    (α : (Scheme.Modules.pullback (action G X)).obj L ⟶
      (Scheme.Modules.pullback (projection G X)).obj L) : Prop :=
  IsDescentCocycle (G ◁ γ[G,X]).left (snd G (G ⊗ X)).left
    ((α_ G G X).inv ≫ μ[G] ▷ X).left (action G X) (projection G X)
    (congrArg Over.Hom.left (multiplication_action G X))
    (congrArg Over.Hom.left (action_projection G X))
    (congrArg Over.Hom.left (multiplication_projection G X)) α

/-- Restrict a linearization along the actual unit section. -/
def identityComparison {L : X.left.Modules}
    (α : (Scheme.Modules.pullback (action G X)).obj L ⟶
      (Scheme.Modules.pullback (projection G X)).obj L) : L ⟶ L :=
  (Scheme.Modules.pullbackId X.left).inv.app L ≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (unitAction_action G X)).symm).hom.app L ≫
        reindexHom (unitAction G X).left α ≫
          (Scheme.Modules.pullbackCongr
            (congrArg Over.Hom.left (unitAction_projection G X))).hom.app L ≫
              (Scheme.Modules.pullbackId X.left).hom.app L

/-- A `G`-linearization of a module `L` on `X`, for a group scheme `G` over `S` acting on `X`: an
isomorphism `σ^* L ≅ pr₂^* L` on `G ×_S X`, where `σ` is the action and `pr₂` the projection
(`comparison`), satisfying the cocycle condition on `G ×_S G ×_S X` (`cocycle`) and restricting to
the identity of `L` along the unit section (`unit`). -/
structure Linearization (L : X.left.Modules) where
  /-- The actual action/projection pullback isomorphism. -/
  comparison : (Scheme.Modules.pullback (action G X)).obj L ≅
    (Scheme.Modules.pullback (projection G X)).obj L
  /-- The action-coordinate cocycle. -/
  cocycle : IsActionCocycle G X comparison.hom
  /-- The comparison is the identity on the unit section. -/
  unit : identityComparison G X comparison.hom = 𝟙 L

/-- A general linearized invertible sheaf over the specified action. -/
structure LinearizedLineBundle where
  module : X.left.Modules
  line : IsLineBundle module
  linearization : Linearization G X module

/-- The induced comparison on the actual nth power. Ordinary power/pullback
comparisons are explicit dependencies on fixed native operations. -/
def powerComparison {L : X.left.Modules} (A : Linearization G X L)
    (PA : PullbackPowers (action G X)) (PP : PullbackPowers (projection G X)) (n : ℕ) :
    (Scheme.Modules.pullback (action G X)).obj (power L n) ≅
      (Scheme.Modules.pullback (projection G X)).obj (power L n) :=
  (PA.comparison n).app L ≪≫ (powerFunctor (G ⊗ X).left n).mapIso A.comparison ≪≫
    ((PP.comparison n).app L).symm

/-- Invariance of the prescribed actual section of an actual tensor power. -/
def IsInvariantPowerSection {L : X.left.Modules} (A : Linearization G X L)
    (PA : PullbackPowers (action G X)) (PP : PullbackPowers (projection G X))
    (n : ℕ) (s : Section (power L n)) : Prop :=
  pullbackSection (action G X) s ≫ (powerComparison G X A PA PP n).hom =
    pullbackSection (projection G X) s

/-- The invariant nonvanishing-section input used in GIT semistability.
Its definition alone asserts no reductivity, ampleness or quotient theorem. -/
def HasInvariantNonvanishingPower {L : X.left.Modules} (A : Linearization G X L)
    (PA : PullbackPowers (action G X)) (PP : PullbackPowers (projection G X))
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X.left) : Prop :=
  ∃ (n : ℕ), 0 < n ∧ ∃ s : Section (power L n),
    IsInvariantPowerSection G X A PA PP n s ∧ pullbackSection x s ≠ 0

/-- A categorical quotient in actual schemes over the prescribed base.
This is a typed mathematical universal-property interface, not a claim
that every action has such a scheme quotient. -/
structure CategoricalQuotient (Y : Over S) where
  quotient : X ⟶ Y
  invariant : γ[G,X] ≫ quotient = snd G X ≫ quotient
  universal : ∀ (Z : Over S) (f : X ⟶ Z),
    γ[G,X] ≫ f = snd G X ≫ f → ∃! g : Y ⟶ Z, quotient ≫ g = f

namespace CategoricalQuotient

variable {G X} {Y : Over S} (Q : CategoricalQuotient G X Y)

/-- Descend an invariant actual scheme map by the stated universal property. -/
def descend {Z : Over S} (f : X ⟶ Z) (hf : γ[G,X] ≫ f = snd G X ≫ f) : Y ⟶ Z :=
  (Q.universal Z f hf).choose

theorem quotient_descend {Z : Over S} (f : X ⟶ Z)
    (hf : γ[G,X] ≫ f = snd G X ≫ f) : Q.quotient ≫ Q.descend f hf = f :=
  (Q.universal Z f hf).choose_spec.1

end CategoricalQuotient

end MathlibExt.AlgebraicGeometry.LinearizedLineBundles
