/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.FieldChowOperators

/-!
# General global bundle/zero-section signature contracts

The coefficient field, base scheme and finite locally free sheaf are arbitrary.
The Chow endpoints use absolute rational Chow homology of schemes locally of
finite type over that field; no Betti or characteristic-zero input occurs. The bundle
model represents actual pulled-back sections, with a normalized universal
section. Its zero section is chosen from the zero-section universal property,
not as a freely named map. The zero-section class operator is the inverse of
the fixed native bundle-cycle pullback after the actual closed-cycle push.
Thus its operator and cone-image input cycle are computed on actual Chow groups.

These are the global bundle/Gysin ingredients of a virtual-cycle recipe.
A global intrinsic POT cone and its normalized embedding/presentation are
additional required objects; an arbitrary closed cycle is not declared to be
such a cone. Source-complete ordinary bundle/virtual-normal/Gysin constructions
are AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleOfModule.lean and
Chow/BivariantLemmas/VirtualNormalBundleClassConstruction.lean (Apache 2.0).
They are reused/ported dependencies, not new Wanted operations.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow
open MathlibExt.AlgebraicGeometry.RelativeCurveClasses
open MathlibExt.AlgebraicGeometry.FieldChowOperators

variable {k : Type} [Field k]

/-- The actual section pulled along an over-base map, for any coefficient field. -/
def pulledSection {X T V : SchemeOver k} (E : X.left.Modules)
    (p : V ⟶ X) (s : SheafOfModules.unit V.left.ringCatSheaf ⟶
      (Scheme.Modules.pullback p.left).obj E)
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :=
  pullbackSection g.left ((Scheme.Modules.pullback p.left).obj E) s ≫
    (Scheme.Modules.pullbackComp g.left p.left).hom.app E ≫
      (Scheme.Modules.pullbackCongr (congrArg (fun v : T ⟶ X => v.left) h)).hom.app E

/-- Actual global vector-bundle sections with their universal comparison. -/
structure VectorBundleModel (X : SchemeOver k) (E : X.left.Modules) (r : ℕ) where
  locallyFree : IsBundle E r
  total : SchemeOver k
  projection : total ⟶ X
  universalSection : SheafOfModules.unit total.left.ringCatSheaf ⟶
    (Scheme.Modules.pullback projection.left).obj E
  universal : ∀ (T : SchemeOver k) (f : T ⟶ X)
    (s : SheafOfModules.unit T.left.ringCatSheaf ⟶ (Scheme.Modules.pullback f.left).obj E),
    ∃! g : T ⟶ total, ∃ h : g ≫ projection = f,
      s = pulledSection E projection universalSection f g h

variable {X : SchemeOver k} {E : X.left.Modules} {r : ℕ} (B : VectorBundleModel X E r)

def zeroSection : X ⟶ B.total :=
  Classical.choose (B.universal X (𝟙 X) 0)

theorem zeroSection_projection : zeroSection B ≫ B.projection = 𝟙 X := by
  exact (Classical.choose_spec (B.universal X (𝟙 X) 0)).1.choose

variable [LocallyOfFiniteType X.hom] [LocallyOfFiniteType B.total.hom]
    [IsNoetherian X.left] [IsNoetherian B.total.left]
    {C : SchemeOver k} [LocallyOfFiniteType C.hom] [IsNoetherian C.left]
    (i : C ⟶ B.total) [IsClosedImmersion i.left]
    (D : ChowPullbackEquivalence X B.total B.projection r)
    (J : ClosedCycleDescent B.total i)

/-- The computed global zero-section Gysin recipe in every integer degree. -/
def zeroSectionPullback (d : ℤ) : gradedChow C d →ₗ[ℚ] gradedChow X (d - r) :=
  (pullbackEquiv X B.total B.projection r D (d - r)).symm.toLinearMap ∘ₗ
    gradedChowCast B.total (by omega) ∘ₗ gradedClosedPush B.total i J d

/-- A class from an actual length-weighted cycle in the actual global bundle. -/
def classFromClosedScheme (d : ℕ) : gradedChow X ((d : ℤ) - r) :=
  zeroSectionPullback B i D J d
    ((positiveChowIso C d (by omega)).toLinearEquiv.symm
      ((relations C d).mkQ (fundamentalCycleOfDimension C.left d)))

end MathlibExt.AlgebraicGeometry.GlobalZeroSectionRecipe
