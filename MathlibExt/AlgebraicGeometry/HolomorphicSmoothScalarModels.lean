/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The real-smooth complex ring instance adapts the native field instance at
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Geometry/Manifold/Algebra/Structures.lean.
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: Nicolò Cavalleri.
Modification: use complex multiplication as a real normed-algebra map.
The native smooth-function sheaf is Geometry/Manifold/Sheaf/Smooth.lean,
Copyright (c) 2023 Heather Macbeth; authors Heather Macbeth and Adam Topaz,
Apache 2.0.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Actual smooth scalar extension of holomorphic module sheaves

The target ring is Mathlib's literal sheaf of smooth complex-valued
functions. The source inclusion is fixed by equality of the underlying
functions on every open. Scalar extension is the native presheaf inverse
image followed by native sheafification, with the actual adjunction unit.

Smooth bundle sections take values in the native original bundle fibres.
Their module action is multiplication by the native smooth functions.
A realization compares this literal module to the same native scalar
extension of E. No freely chosen geometric functor or bundle label is used.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels

open CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open scoped Manifold ContDiff

/-- Complex multiplication is real-smooth; use the native normed-space proof. -/
instance complexRealSmoothRing : ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ :=
  { (inferInstance : LieAddGroup 𝓘(ℝ, ℂ) ∞ ℂ) with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]

/-- The literal native sheaf of real-smooth complex-valued functions. -/
def smoothStructureRing : Sheaf (Opens.grothendieckTopology M) RingCat.{0} :=
  smoothSheafRing 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℂ) M ℂ

abbrev SmoothScalars (U : Opens M) := (smoothStructureRing (n := n) (M := M)).obj.obj (op U)

variable [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]

/-- The scalar inclusion is fixed by every actual function value. -/
structure HolomorphicSmoothInclusionSource where
  map : holomorphicStructureRing (n := n) (M := M) ⟶ smoothStructureRing (n := n) (M := M)
  normalized : ∀ (U : Opens M) (f : HolomorphicScalars (n := n) U) (x : U),
    ((show SmoothScalars (n := n) U →+* (U → ℂ) from ContMDiffMap.coeFnRingHom)
      ((map.hom.app (op U)) f)) x = f.val x

/-- The same literal ring map, normalized through the identity site's native unitor. -/
def scalarPresheafMap (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) :
    (holomorphicStructureRing (n := n) (M := M)).obj ⟶
      (𝟭 (Opens M)).op ⋙ (smoothStructureRing (n := n) (M := M)).obj :=
  S.map.hom ≫ (Functor.leftUnitor (smoothStructureRing (n := n) (M := M)).obj).inv

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Native actual scalar extension, without an independent choice of left adjoint. -/
def smoothScalarExtension (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) :
    SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) ⥤
      SheafOfModules.{0} (smoothStructureRing (n := n) (M := M)) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.pullback (F := 𝟭 (Opens M)) (scalarPresheafMap S) ⋙
    PresheafOfModules.sheafification (𝟙 (smoothStructureRing (n := n) (M := M)).obj)

/-- An actual source section enters scalar extension through the two native adjunction units. -/
def smoothExtensionSection (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (E : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))) (U : Opens M)
    (s : E.val.obj (op U)) : ((smoothScalarExtension S).obj E).val.obj (op U) :=
  let P := (PresheafOfModules.pullback (F := 𝟭 (Opens M)) (scalarPresheafMap S)).obj E.val
  let a := ((PresheafOfModules.pullbackPushforwardAdjunction (scalarPresheafMap S)).unit.app E.val).app (op U)
  let b := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (smoothStructureRing (n := n) (M := M)).obj)).unit.app P).app (op U)
  b.hom (a.hom s)

variable {r : ℕ} (B : SmoothComplexBundle n M r)

/-- Native smooth functions act on the same actual bundle fibres by pointwise multiplication. -/
instance roughSectionSmoothModule (U : Opens M) : Module (SmoothScalars (n := n) U) (RoughSection B U) :=
  Module.compHom (RoughSection B U)
    (show SmoothScalars (n := n) U →+* (U → ℂ) from ContMDiffMap.coeFnRingHom)

/-- Ordinary multiplication calculus refers only to these fixed native smooth functions and bundle sections. -/
class SmoothSectionMultiplication : Prop where
  smooth : ∀ (U : Opens M) (f : SmoothScalars (n := n) U) (s : RoughSection B U),
    IsSmoothSection B U s → IsSmoothSection B U (f • s)

variable [SectionCalculus B 0] [SmoothSectionMultiplication B]

/-- The actual smooth sections as a module over the native smooth scalar ring. -/
def smoothSectionModule (U : Opens M) : Submodule (SmoothScalars (n := n) U) (RoughSection B U) where
  carrier := {s | IsSmoothSection B U s}
  zero_mem' := SectionCalculus.smooth_zero (B := B) (A := 0) U
  add_mem' hs ht := SectionCalculus.smooth_add (B := B) (A := 0) U _ _ hs ht
  smul_mem' f s hs := SmoothSectionMultiplication.smooth U f s hs

/-- The native section module presheaf has literal restriction of the same bundle section. -/
def smoothSectionPresheaf : PresheafOfModules.{0} (smoothStructureRing (n := n) (M := M)).obj where
  obj U := ModuleCat.of (SmoothScalars (n := n) U.unop) (smoothSectionModule B U.unop)
  map {U V} a := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((smoothStructureRing (n := n) (M := M)).obj.map a).hom).obj
      (ModuleCat.of (SmoothScalars (n := n) V.unop) (smoothSectionModule B V.unop))) {
    toFun s := ⟨restrictSection B a.unop.le s.val,
      SectionCalculus.smooth_restrict (B := B) (A := 0) U.unop V.unop a.unop.le s.val s.property⟩
    map_add' _ _ := by apply Subtype.ext; rfl
    map_smul' _ _ := by apply Subtype.ext; rfl }
  map_id U := by apply ModuleCat.hom_ext; ext s; rfl
  map_comp a b := by apply ModuleCat.hom_ext; ext s; rfl

/-- Ordinary local gluing of the prescribed native smooth bundle sections. -/
class SmoothBundleSheafCondition : Prop where
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology M) (smoothSectionPresheaf B).presheaf

/-- The native bundle's actual smooth section sheaf. -/
def smoothBundleModule [SmoothBundleSheafCondition B] :
    SheafOfModules.{0} (smoothStructureRing (n := n) (M := M)) :=
  ⟨smoothSectionPresheaf B, SmoothBundleSheafCondition.isSheaf⟩

/-- A physical bundle realizes the same actual smooth scalar extension of the given holomorphic sheaf. -/
structure SmoothModuleRealization (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (E : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))) where
  bundle : SmoothComplexBundle n M r
  calculus : SectionCalculus bundle 0
  multiplication : SmoothSectionMultiplication bundle
  gluing : letI := calculus; letI := multiplication; SmoothBundleSheafCondition bundle
  comparison : letI := calculus; letI := multiplication; letI := gluing
    (smoothScalarExtension S).obj E ≅ smoothBundleModule bundle

end MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
