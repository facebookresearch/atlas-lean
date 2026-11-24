/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientSources
public import MathlibExt.AlgebraicGeometry.AlgebraicWeightBundleModels
public import MathlibExt.AlgebraicGeometry.StackChowGroups
public import MathlibExt.AlgebraicGeometry.StackBundleCones
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Algebraic equivariant Chow from the actual quotient stack

The quotient fibres are the original fppf torsors and equivariant maps.
A_i^Gm(X) is the native rational Kresch group CH_(i-1)([X/Gm]).
Character lines are fixed on all affine points by equivariant regular
functions on their actual torsors. Their first Chern cap is the native
zero-section push followed by inverse vector-bundle pullback.

Reference: Graber--Pandharipande alg-geom/9708001v2, Sections1--3;
Kresch math/9810166v1, quotient-stack/equivariant comparison.
The quotient-stack and character inputs (`EquivariantSource`, `CharacterChernData`) are taken as
data here; the requests in this layer cover the operations on them, not their construction from a
scheme with a torus action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AlgebraicEquivariantChowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open GroupTorsorGeometry ThetaQuotientSources AlgebraicWeightBundleModels
open StackCycleGeometry StackAffineModules StackVectorBundles StackChowGroups StackBundleCones
open StackCycleRelations StackProjectiveModels
open scoped TensorProduct

variable (X : Over base) [ModObj Gm X]

/-- An actual quotient-stack source, with its finite-type Artin scope proof. -/
structure EquivariantSource where
  quotient : QuotientSource ℂ (G := Gm) (W := X)
  inScope : FiniteTypeArtin ℂ quotient.stack

variable (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
  {X}

/-- Dimension is shifted by the dimension-one acting torus. -/
abbrev EquivariantChow (Q : EquivariantSource X) (i : ℤ) :=
  RationalChowGroup D K Q.quotient.stack Q.inScope (i-1)

/-- An equivariant map changes the original quotient point by postcomposition. -/
def quotientPointMap {Y : Over base} [ModObj Gm Y] (f : X ⟶ Y)
    (hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]) (T : Over base) :
    QuotientObject Gm X T ⥤ QuotientObject Gm Y T where
  obj P := {
    torsor := P.torsor
    map := P.map ≫ f
    equivariant := by
      rw [← Category.assoc, P.equivariant, Category.assoc, hf,
        ← Category.assoc, ← whiskerLeft_comp] }
  map a := {
    iso := a.iso
    over := a.over
    equivariant := a.equivariant
    target := by rw [← Category.assoc, a.target] }
  map_id P := by apply QuotientIso.ext; rfl
  map_comp a b := by apply QuotientIso.ext; rfl

/-- The quotient stack map is coupled to those original point functors on every test. -/
structure EquivariantMap {Y : Over base} [ModObj Gm Y] (Q : EquivariantSource X)
    (R : EquivariantSource Y) (f : X ⟶ Y)
    (hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]) where
  map : StackHom Q.quotient.stack R.quotient.stack
  fibre : ∀ T : Over base,
    StackCycleGeometry.component map T ⋙ (R.quotient.fibre T).functor ≅
      (Q.quotient.fibre T).functor ⋙ quotientPointMap f hf T

  reindex : ∀ {T V : Over base} (a : V ⟶ T) (q : Q.quotient.stack.Fibre T),
    ((fibre V).hom.app ((pull Q.quotient.stack a).obj q)).iso.hom ≫
      (Q.quotient.restriction a q).iso.hom ≫ (Q.quotient.reindex a q).original Gm =
    ((R.quotient.fibre V).functor.map
      ((Cat.Hom.toNatIso (map.naturality a.op.toLoc)).hom.app q)).iso.hom ≫
      (R.quotient.restriction a ((StackCycleGeometry.component map T).obj q)).iso.hom ≫
      (R.quotient.reindex a ((StackCycleGeometry.component map T).obj q)).original Gm ≫
      ((fibre T).hom.app q).iso.hom

/-- Projective equivariant push uses composition of actual Kresch representatives. -/
def equivariantProjectivePush {Y : Over base} [ModObj Gm Y]
    {Q : EquivariantSource X} {R : EquivariantSource Y} {f : X ⟶ Y}
    {hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]}
    {M : EquivariantMap Q R f hf}
    (P : ProjectiveChowPushData D K Q.inScope R.inScope M.map) (i : ℤ) :
    EquivariantChow D K Q i →ₗ[ℚ] EquivariantChow D K R i := rationalMap (P.map (i-1))

/-- Properness is tested on the actual represented scheme fibres of the same quotient map. -/
structure RepresentableProper {Y : Over base} [ModObj Gm Y]
    {Q : EquivariantSource X} {R : EquivariantSource Y} {f : X ⟶ Y}
    {hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]}
    (M : EquivariantMap Q R f hf) where
  fibre : ∀ (T : Over base) (y : R.quotient.stack.Fibre T),
    StackFibreModels.SchemeFibreModel M.map T y
  proper : ∀ (T : Over base) (y : R.quotient.stack.Fibre T), IsProper (fibre T y).scheme.hom

/-- The proper envelope uses actual projective Chow representatives; BGm need not be DM. -/
structure ProperEnvelope {Y : Over base} [ModObj Gm Y]
    {Q : EquivariantSource X} {R : EquivariantSource Y} {f : X ⟶ Y}
    {hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]}
    (M : EquivariantMap Q R f hf) where
  proper : RepresentableProper M
  cover : RationalChowCover D K Q.quotient.stack Q.inScope
  composite : ProjectiveMorphism (Pseudofunctor.StrongTrans.vcomp cover.stage.map M.map)

/-- The proper map is fixed on every element of the native surjective Chow envelope. -/
structure ProperPushData {Y : Over base} [ModObj Gm Y]
    {Q : EquivariantSource X} {R : EquivariantSource Y} {f : X ⟶ Y}
    {hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]}
    {M : EquivariantMap Q R f hf} (P : ProperEnvelope D K M) where
  map : ∀ i : ℤ, EquivariantChow D K Q i →ₗ[ℚ] EquivariantChow D K R i
  normalized : ∀ (i : ℤ) (a : TensorProduct ℤ ℚ
    (BundleChowGroup D K.bundle P.cover.stage.source P.cover.stage.inScope (i-1))),
    map i (rationalMap (projectiveClass D K Q.quotient.stack Q.inScope (i-1) P.cover.stage) a) =
      rationalMap (projectiveClass D K R.quotient.stack R.inScope (i-1)
        ⟨P.cover.stage.source, P.cover.stage.inScope,
          Pseudofunctor.StrongTrans.vcomp P.cover.stage.map M.map, P.composite⟩) a

/-- Equivariant flat pullback uses the native stage-normalized Kresch pullback. -/
def equivariantFlatPull {Y : Over base} [ModObj Gm Y]
    {Q : EquivariantSource X} {R : EquivariantSource Y} {f : X ⟶ Y}
    {hf : γ[Gm,X] ≫ f = (Gm ◁ f) ≫ γ[Gm,Y]}
    {M : EquivariantMap Q R f hf} {r : ℤ}
    (P : FlatChowPullData D K Q.inScope R.inScope M.map r) (i : ℤ) :
    EquivariantChow D K R i →ₗ[ℚ] EquivariantChow D K Q (i+r) :=
  (rationalMap (chowRegrade D K Q.quotient.stack Q.inScope (by omega))).comp
    (rationalMap (P.map (i-1)))

end MathlibExt.AlgebraicGeometry.AlgebraicEquivariantChowModels
