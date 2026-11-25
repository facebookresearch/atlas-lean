/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual small-étale base change and Kummer coefficient maps

The site functor is native scheme base change. The unit coefficient map
is computed from the actual pullback projection on regular functions.
The μ_l map is the canonical kernel lift and inverse kernel-comparison
map; no torsion restriction operator is freely supplied.

Continuity and kernel preservation are completed source/native geometric
morphism inputs, with the functors and comparison maps fixed.
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
native-small-site KummerTheory and Galois cohomology coefficient maps,
Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The native base-change functor on actual small étale objects. -/
def baseChange {Y X : Scheme.{0}} (f : Y ⟶ X) : X.Etale ⥤ Y.Etale := by
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{0}) f :=
    ⟨fun _ _ => inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{0}) f :=
    ⟨fun h hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback h hf⟩
  exact MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{0}) ⊤ f

abbrev schemeForget (X : Scheme.{0}) := Scheme.Etale.forget X ⋙ Over.forget X

/-- Actual projection of each scheme fibre product to its original étale scheme. -/
def projection {Y X : Scheme.{0}} (f : Y ⟶ X) :
    baseChange f ⋙ schemeForget Y ⟶ schemeForget X where
  app U := pullback.fst U.hom f
  naturality U V g := by
    change ((baseChange f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left
    exact pullback.lift_fst _ _ _

/-- Fixed regular-unit coefficient functor used in the multiplicative sheaf. -/
abbrev unitCoefficients := unitCoefficientFunctor

attribute [local irreducible] unitCoefficientFunctor
set_option backward.isDefEq.respectTransparency false in
/-- The actual pullback-of-functions map on unit presheaves. -/
def unitsPresheafMap {Y X : Scheme.{0}} (f : Y ⟶ X) :
    multiplicativePresheaf X ⟶ (baseChange f).op ⋙ multiplicativePresheaf Y where
  app U := unitCoefficients.map (pullback.fst U.unop.hom f).op
  naturality U V g := by
    change unitCoefficients.map g.unop.left.op ≫
        unitCoefficients.map (pullback.fst V.unop.hom f).op =
      unitCoefficients.map (pullback.fst U.unop.hom f).op ≫
        unitCoefficients.map (((baseChange f).map g.unop).left).op
    have h : ((baseChange f).map g.unop).left ≫ pullback.fst U.unop.hom f =
        pullback.fst V.unop.hom f ≫ g.unop.left := pullback.lift_fst _ _ _
    simpa only [op_comp, Functor.map_comp] using
      congrArg (fun h => unitCoefficients.map h.op)
        h.symm

variable {Y X : Scheme.{0}} (f : Y ⟶ X)
  [(baseChange f).IsContinuous X.smallEtaleTopology Y.smallEtaleTopology]

/-- Actual continuous sheaf direct image on the fixed coefficient category. -/
abbrev pushforward : Coefficients Y ⥤ Coefficients X :=
  (baseChange f).sheafPushforwardContinuous (ModuleCat.{1} Scalar)
    X.smallEtaleTopology Y.smallEtaleTopology

instance pushforward_additive : (pushforward f).Additive where
  map_add := by intros; rfl

/-- Actual G_m direct-image coefficient map, fixed by scheme pullback of regular functions. -/
def unitsPushforward (GX : MultiplicativeNormalization X) (GY : MultiplicativeNormalization Y) :
    multiplicativeSheaf X GX ⟶ (pushforward f).obj (multiplicativeSheaf Y GY) :=
  ObjectProperty.homMk (unitsPresheafMap f)

/-- Naturality of actual pullback with the actual power maps. -/
theorem power_naturality (GX : MultiplicativeNormalization X) (GY : MultiplicativeNormalization Y)
    (l : ℕ) :
    unitsPushforward f GX GY ≫ (pushforward f).map (powerMap Y GY l) =
      powerMap X GX l ≫ unitsPushforward f GX GY := by
  simp only [powerMap, Functor.map_nsmul]
  erw [(pushforward f).map_id (multiplicativeSheaf Y GY)]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
    Category.comp_id]

/-- The μ_l coefficient map is the actual kernel lift/comparison of the unit map. -/
def rootsPushforward (GX : MultiplicativeNormalization X) (GY : MultiplicativeNormalization Y)
    (l : ℕ) (h : IsIso (kernelComparison (powerMap Y GY l) (pushforward f))) :
    rootsSheaf X GX l ⟶ (pushforward f).obj (rootsSheaf Y GY l) := by
  letI := h
  exact kernel.lift ((pushforward f).map (powerMap Y GY l))
    (kernel.ι (powerMap X GX l) ≫ unitsPushforward f GX GY)
    (by rw [Category.assoc, power_naturality, ← Category.assoc, kernel.condition,
        zero_comp]) ≫
      inv (kernelComparison (powerMap Y GY l) (pushforward f))

end MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality
