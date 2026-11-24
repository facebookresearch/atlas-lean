/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Restrict
public import MathlibExt.AlgebraicGeometry.CurvePositivity

/-!
# Local finite-cover comparisons assembled from actual module functors

The open base-change map is the actual mate built from Mathlib's module
pullback/pushforward units, counits, composition isomorphisms and the
commutative restriction square. A local chart records ordinary line
trivializations over the base open and its actual inverse image, together
with invertibility of that fixed mate. It contains no rank conclusion.

The complete rank assembly is useful with the public Axiom source's
finite locally free pushforward and local-free rank inputs:
StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyFiniteLocallyFree.lean,
FiberRank/GenericPoint.lean and FiniteLocallyFree/Finrank.lean, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b. Those inputs are explicit here;
their whole dependency closure is not imported or re-requested.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries CurveVectorBundles CurvePositivity

universe u

/-- Restriction of the actual cover to the actual inverse-image open. -/
def restrictedMap {X Z : Scheme.{u}} (q : Z ⟶ X) (U : X.Opens) :
    (q ⁻¹ᵁ U).toScheme ⟶ U.toScheme := q.resLE U (q ⁻¹ᵁ U) le_rfl

theorem restriction_square {X Z : Scheme.{u}} (q : Z ⟶ X) (U : X.Opens) :
    (q ⁻¹ᵁ U).ι ≫ q = restrictedMap q U ≫ U.ι :=
  (Scheme.Hom.resLE_comp_ι q (U := U) (V := q ⁻¹ᵁ U) le_rfl).symm

/-- The actual open base-change mate. Invertibility is a genuine toolbox
condition, not a freely supplied comparison isomorphism. -/
def openBaseChangeMap {X Z : Scheme.{u}} (q : Z ⟶ X) (U : X.Opens) (M : Z.Modules) :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward q).obj M) ⟶
      (Scheme.Modules.pushforward (restrictedMap q U)).obj
        ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M) :=
  let a := (q ⁻¹ᵁ U).ι
  let b := restrictedMap q U
  let N := (Scheme.Modules.pullback a).obj M
  (Scheme.Modules.pullback U.ι).map
    ((Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) ≫
      (Scheme.Modules.pushforwardComp a q).hom.app N ≫
      (Scheme.Modules.pushforwardCongr (restriction_square q U)).hom.app N ≫
      (Scheme.Modules.pushforwardComp b U.ι).inv.app N) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).counit.app
      ((Scheme.Modules.pushforward b).obj N)

/-- The canonical structure-module comparison under actual module
pullback. The map, rather than an arbitrary unit isomorphism, is fixed. -/
def pullbackStructureIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X := by
  have : (Opens.map f.base).Final := by infer_instance
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint := by
    change (Scheme.Modules.pushforward f).IsRightAdjoint
    infer_instance
  let m : (Scheme.Modules.pullback f).obj (structureModule Y) ⟶ structureModule X :=
    SheafOfModules.pullbackObjUnitToUnit (F := Opens.map f.base) f.toRingCatSheafHom
  have : IsIso m := by
    dsimp [m]
    exact SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := Opens.map f.base) f.toRingCatSheafHom
  exact asIso m

/-- A local chart for rank assembly. These are ordinary rank-one line
trivializations on an actual base open and its inverse image, with the
actual base-change mates invertible. No pushforward-rank result is input. -/
structure FiniteLineChart {X Z : Scheme.{u}} (q : Z ⟶ X) {n : ℕ}
    (L : Fin n → X.Modules) (M : Z.Modules) (x : X) where
  U : X.Opens
  contains : x ∈ U
  preimageLine : Nonempty
    ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M ≅ structureModule (q ⁻¹ᵁ U))
  baseLines : ∀ i, Nonempty ((Scheme.Modules.pullback U.ι).obj (L i) ≅ structureModule U)
  baseChangeLine : IsIso (openBaseChangeMap q U M)
  baseChangeStructure : IsIso (openBaseChangeMap q U (structureModule Z))

/-- The local comparison of the line's actual pushforward with the
structure module's pushforward, through the exact prescribed mates. -/
def linePushforwardLocalIso {X Z : Scheme.{u}} (q : Z ⟶ X) {n : ℕ}
    (L : Fin n → X.Modules) (M : Z.Modules) (x : X) (c : FiniteLineChart q L M x) :
    (Scheme.Modules.pullback c.U.ι).obj ((Scheme.Modules.pushforward q).obj M) ≅
      (Scheme.Modules.pullback c.U.ι).obj
        ((Scheme.Modules.pushforward q).obj (structureModule Z)) := by
  have := c.baseChangeLine
  have := c.baseChangeStructure
  exact asIso (openBaseChangeMap q c.U M) ≪≫
    (Scheme.Modules.pushforward (restrictedMap q c.U)).mapIso c.preimageLine.some ≪≫
    (Scheme.Modules.pushforward (restrictedMap q c.U)).mapIso
      (pullbackStructureIso (q ⁻¹ᵁ c.U).ι).symm ≪≫
    (asIso (openBaseChangeMap q c.U (structureModule Z))).symm

/-- The complete local rank-n assembly from an actual split algebra and
ordinary rank-one chart data. -/
theorem pushforward_rank_from_charts {X Z : Scheme.{u}} (q : Z ⟶ X) {n : ℕ}
    (L : Fin n → X.Modules) (M : Z.Modules)
    (split : (Scheme.Modules.pushforward q).obj (structureModule Z) ≅ ∐ L)
    (charts : ∀ x : X, FiniteLineChart q L M x) :
    IsVectorBundle ((Scheme.Modules.pushforward q).obj M) n := by
  classical
  intro x
  let c := charts x
  refine ⟨c.U, c.contains, ⟨?_⟩⟩
  exact linePushforwardLocalIso q L M x c ≪≫
    (Scheme.Modules.pullback c.U.ι).mapIso split ≪≫
    (asIso (sigmaComparison (Scheme.Modules.pullback c.U.ι) L)).symm ≪≫
    Sigma.mapIso (fun i ↦ (c.baseLines i).some)

end MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
