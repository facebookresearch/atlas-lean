/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
public import MathlibExt.AlgebraicGeometry.CompactifiedPoincareKernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Actual line-bundle powers and sections for geometric task interfaces

These operations use the existing ordinary tensor of module sheaves:
the sectionwise presheaf tensor followed by sheafification. A section is
an actual module morphism from the structure sheaf. No tensor, section,
or line-bundle carrier is supplied as an arbitrary operation.

The normalization of pullback powers is a separate typed contract, to be
used by root-stack and linearization tasks before a provider is ported.
Mathlib already supplies the ordinary module pullback and its coherence.
References: Stacks Project, Tags 01CY and 01CR.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

/- The tensor powers are the shared `SchemeModulesTensor.power`
(`L^{⊗ 0} = 𝒪_X`, `L^{⊗ (n + 1)} = L^{⊗ n} ⊗ L`), re-exported for users of this
namespace. -/
export _root_.MathlibExt.AlgebraicGeometry.SchemeModulesTensor (power)

universe u

/-- The actual presheaf category with its sectionwise tensor. -/
abbrev ModulePresheaves (X : Scheme.{u}) :=
  PresheafOfModulesOfCommRing.{u} X.sheaf.obj

/-- Forgetting the sheaf condition, with the commutative-ring carrier explicit. -/
abbrev forgetModules (X : Scheme.{u}) : X.Modules ⥤ ModulePresheaves X :=
  SheafOfModules.forget X.ringCatSheaf

/-- Sheafification of those actual module presheaves. -/
abbrev sheafifyModules (X : Scheme.{u}) : ModulePresheaves X ⥤ X.Modules :=
  @PresheafOfModules.sheafification.{u, u, u, u} X.Opens inferInstance
    (Opens.grothendieckTopology X) X.ringCatSheaf.obj X.ringCatSheaf
    (𝟙 X.ringCatSheaf.obj) inferInstance inferInstance inferInstance inferInstance

/-- The actual structure-sheaf morphisms, equivalently global sections. -/
abbrev Section {X : Scheme.{u}} (L : X.Modules) := structureModule X ⟶ L

/-- The tensor of two actual module morphisms, followed by sheafification. -/
abbrev tensorMap {X : Scheme.{u}} {L L' M M' : X.Modules}
    (f : L ⟶ L') (g : M ⟶ M') : moduleTensor X L M ⟶ moduleTensor X L' M' :=
  CompactifiedPoincareKernels.moduleTensorMap f g

/-- The existing curried tensor map is the native tensor map after sheafification. -/
theorem tensorMap_eq {X : Scheme.{u}} {L L' M M' : X.Modules}
    (f : L ⟶ L') (g : M ⟶ M') :
    tensorMap f g = (sheafifyModules X).map
      ((forgetModules X).map f ⊗ₘ (forgetModules X).map g) := by
  dsimp only [tensorMap, CompactifiedPoincareKernels.moduleTensorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def]

@[simp] theorem tensorMap_id (X : Scheme.{u}) (L M : X.Modules) :
    tensorMap (𝟙 L) (𝟙 M) = 𝟙 (moduleTensor X L M) := by
  rw [tensorMap_eq]
  erw [(forgetModules X).map_id L, (forgetModules X).map_id M,
    id_tensorHom_id (C := ModulePresheaves X)]
  exact (sheafifyModules X).map_id _

@[simp] theorem tensorMap_comp {X : Scheme.{u}} {L L' L'' M M' M'' : X.Modules}
    (f : L ⟶ L') (f' : L' ⟶ L'') (g : M ⟶ M') (g' : M' ⟶ M'') :
    tensorMap (f ≫ f') (g ≫ g') = tensorMap f g ≫ tensorMap f' g' := by
  rw [tensorMap_eq, tensorMap_eq, tensorMap_eq]
  erw [(forgetModules X).map_comp f f', (forgetModules X).map_comp g g',
    ← tensorHom_comp_tensorHom (C := ModulePresheaves X)]
  exact (sheafifyModules X).map_comp _ _

/-- The actual functorial map on the tensor power. -/
def powerMap {X : Scheme.{u}} {L M : X.Modules} (f : L ⟶ M) :
    (n : ℕ) → power L n ⟶ power M n
  | 0 => 𝟙 (structureModule X)
  | n + 1 => tensorMap (powerMap f n) f

@[simp] theorem powerMap_id {X : Scheme.{u}} (L : X.Modules) (n : ℕ) :
    powerMap (𝟙 L) n = 𝟙 (power L n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [powerMap, ih, power]

@[simp] theorem powerMap_comp {X : Scheme.{u}} {L M N : X.Modules}
    (f : L ⟶ M) (g : M ⟶ N) (n : ℕ) :
    powerMap (f ≫ g) n = powerMap f n ≫ powerMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih => simp only [powerMap, ih, tensorMap_comp]

/-- Tensor powers as an actual endofunctor on module sheaves. -/
def powerFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ X.Modules where
  obj L := power L n
  map f := powerMap f n
  map_id L := powerMap_id L n
  map_comp f g := powerMap_comp f g n

/-- The canonical structure-sheaf map into its tensor square. -/
def unitDiagonal (X : Scheme.{u}) :
    structureModule X ⟶ moduleTensor X (structureModule X) (structureModule X) :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  (asIso (adj.counit.app (structureModule X))).inv ≫
    (sheafifyModules X).map
      (λ_ ((forgetModules X).obj (structureModule X))).inv

/-- The tensor of actual sections, using the canonical unit diagonal. -/
def tensorSection {X : Scheme.{u}} {L M : X.Modules}
    (s : Section L) (t : Section M) : Section (moduleTensor X L M) :=
  unitDiagonal X ≫ tensorMap s t

/-- The actual tensor power of a section, including the exponent-zero unit. -/
def sectionPower {X : Scheme.{u}} {L : X.Modules} (s : Section L) :
    (n : ℕ) → Section (power L n)
  | 0 => 𝟙 (structureModule X)
  | n + 1 => tensorSection (sectionPower s n) s

@[simp] theorem sectionPower_natural {X : Scheme.{u}} {L M : X.Modules}
    (s : Section L) (f : L ⟶ M) (n : ℕ) :
    sectionPower (s ≫ f) n = sectionPower s n ≫ powerMap f n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
      simp only [sectionPower, powerMap, tensorSection, ih, tensorMap_comp, Category.assoc]

/-- The canonical pullback of a section, with its source fixed by the
actual adjunction-induced structure-sheaf comparison. -/
def pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (s : Section L) : Section ((Scheme.Modules.pullback f).obj L) := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).inv ≫
    (Scheme.Modules.pullback f).map s

/-- A normalized comparison of the *fixed* pullback and tensor-power
operations. This records reusable comparison data, not a power oracle. -/
structure PullbackPowers {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- Natural comparison for every exponent and actual module. -/
  comparison (n : ℕ) :
    powerFunctor Y n ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ powerFunctor X n
  /-- The comparison sends the actual pulled-back section power to the
  actual power of the pulled-back section. -/
  section_normalization : ∀ (L : Y.Modules) (s : Section L) (n : ℕ),
    pullbackSection f (sectionPower s n) ≫ (comparison n).hom.app L =
      sectionPower (pullbackSection f s) n

end MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
