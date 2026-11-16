/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
public import MathlibExt.AlgebraicGeometry.ModuleInternalHom
public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Actual holomorphic sheaf Higgs objects and determinant modules

The sheaves are native O_X-modules and finite local freeness is tested by
actual section isomorphisms over all smaller opens. Tensor arrows use
native presheaf tensor and sheafification. The exterior square of theta
is its literal tensor composition followed by the normalized cotangent
wedge. Determinants use the native exterior-power presheaf followed by
the actual double internal dual, rather than a selected line bundle.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicSheafHiggsModels

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open KahlerClassGeometry HolomorphicCoefficientSheaves HarmonicHolomorphicModuleModels
open HolomorphicCotangentModuleModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

abbrev HolomorphicModules := SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))

/-- All actual module arrows act on the native tensor presheaf and sheafification. -/
def tensorMap {E E' F F' : HolomorphicModules (n := n) (M := M)}
    (a : E ⟶ E') (b : F ⟶ F') : holomorphicTensor E F ⟶ holomorphicTensor E' F' :=
  (PresheafOfModules.sheafification (𝟙 (holomorphicStructureRing (n := n) (M := M)).obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := holomorphicCommutativePresheaf (n := n) (M := M)) a.val b.val)

/-- The local finite free presentation is an actual section isomorphism on every smaller open. -/
structure LocalFreePresentation (E : HolomorphicModules (n := n) (M := M)) (V : Opens M) (r : ℕ) where
  coordinates : ∀ (U : Opens M), U ≤ V →
    E.val.obj (op U) ≃ₗ[HolomorphicScalars (n := n) U] (Fin r → HolomorphicScalars (n := n) U)
  restriction : ∀ (U W : Opens M) (a : U ≤ V) (b : W ≤ V) (c : W ≤ U)
    (s : E.val.obj (op U)) (j : Fin r),
    coordinates W b ((E.val.map (homOfLE c).op).hom s) j =
      HolomorphicCoefficientSheaves.restriction (Coordinates n) M c (coordinates U a s j)

/-- Local freeness and rank are genuine properties of the actual O-module. -/
def IsLocallyFreeRank (E : HolomorphicModules (n := n) (M := M)) (r : ℕ) : Prop :=
  ∀ x : M, ∃ V : Opens M, x ∈ V ∧ Nonempty (LocalFreePresentation E V r)

/-- The generic rank is tested on an actual dense open with local finite free presentations. -/
def HasGenericRank (E : HolomorphicModules (n := n) (M := M)) (r : ℕ) : Prop :=
  ∃ U : Opens M, Dense (U : Set M) ∧
    ∀ x : U, ∃ V : Opens M, x.val ∈ V ∧ V ≤ U ∧ Nonempty (LocalFreePresentation E V r)

/-- Native tensor association is fixed on every actual triple pure section. -/
structure TensorAssociatorSource where
  iso : ∀ E F G : HolomorphicModules (n := n) (M := M),
    holomorphicTensor (holomorphicTensor E F) G ≅ holomorphicTensor E (holomorphicTensor F G)
  normalized : ∀ (E F G : HolomorphicModules (n := n) (M := M)) (U : Opens M)
    (e : E.val.obj (op U)) (f : F.val.obj (op U)) (g : G.val.obj (op U)),
    (((iso E F G).hom.val.app (op U)).hom
      (holomorphicTensorSection (holomorphicTensor E F) G U
        (holomorphicTensorSection E F U e f) g)) =
      holomorphicTensorSection E (holomorphicTensor F G) U e (holomorphicTensorSection F G U f g)

/-- The actual cotangent wedge is fixed on every native tensor generator and tangent tuple. -/
structure CotangentWedgeSource where
  map : holomorphicTensor (holomorphicOmega (n := n) (M := M) 1)
    (holomorphicOmega (n := n) (M := M) 1) ⟶ holomorphicOmega (n := n) (M := M) 2
  normalized : ∀ (U : Opens M) (α β : holomorphicFormModule (n := n) (M := M) U 1)
    (x : U) (u v : Coordinates n),
    (((map.val.app (op U)).hom (holomorphicTensorSection
      (holomorphicOmega (n := n) (M := M) 1) (holomorphicOmega (n := n) (M := M) 1) U α β)).val x) ![u, v] =
      α.val x ![u] * β.val x ![v] - α.val x ![v] * β.val x ![u]

/-- Theta squared is the actual tensor composition on the bundle factor followed by cotangent wedge. -/
def higgsSquare (A : TensorAssociatorSource (n := n) (M := M))
    (W : CotangentWedgeSource (n := n) (M := M))
    {E : HolomorphicModules (n := n) (M := M)}
    (θ : E ⟶ holomorphicTensor E (holomorphicOmega (n := n) (M := M) 1)) :
    E ⟶ holomorphicTensor E (holomorphicOmega (n := n) (M := M) 2) :=
  θ ≫ tensorMap θ (𝟙 _) ≫ (A.iso E (holomorphicOmega (n := n) (M := M) 1)
    (holomorphicOmega (n := n) (M := M) 1)).hom ≫ tensorMap (𝟙 E) W.map

/-- The general holomorphic Higgs object uses actual finite free O-modules and the actual square map. -/
structure HiggsModule (A : TensorAssociatorSource (n := n) (M := M))
    (W : CotangentWedgeSource (n := n) (M := M)) where
  module : HolomorphicModules (n := n) (M := M)
  rank : ℕ
  locallyFree : IsLocallyFreeRank module rank
  theta : module ⟶ holomorphicTensor module (holomorphicOmega (n := n) (M := M) 1)
  integrable : higgsSquare A W theta = 0

/-- Actual O-linear Higgs arrows retain the full theta commuting square. -/
structure HiggsHom {A : TensorAssociatorSource (n := n) (M := M)}
    {W : CotangentWedgeSource (n := n) (M := M)} (E F : HiggsModule A W) where
  map : E.module ⟶ F.module
  commutes : map ≫ F.theta = E.theta ≫ tensorMap map (𝟙 _)

/-- The actual sheaf exterior power is the native sectionwise exterior algebra and sheafification. -/
def exteriorSheaf (E : HolomorphicModules (n := n) (M := M)) (r : ℕ) :
    HolomorphicModules (n := n) (M := M) :=
  (PresheafOfModules.sheafification (𝟙 (holomorphicStructureRing (n := n) (M := M)).obj)).obj
    (PresheafOfModules.extPow (O := holomorphicCommutativePresheaf (n := n) (M := M)) r E.val)

/-- Internal dual uses the completed native sheaf of actual local O-linear module morphisms. -/
def dualSheaf (E : HolomorphicModules (n := n) (M := M)) : HolomorphicModules (n := n) (M := M) :=
  ⟨ModuleInternalHom.internalHom (holomorphicCommutativePresheaf (n := n) (M := M)) E.val
      (SheafOfModules.unit (holomorphicStructureRing (n := n) (M := M))).val,
    ModuleInternalHom.internalHom_isSheaf _ _ _ (SheafOfModules.unit _).isSheaf⟩

/-- Reflexive determinant is the actual double dual of the actual top exterior power. -/
def determinantSheaf (E : HolomorphicModules (n := n) (M := M)) (r : ℕ) :
    HolomorphicModules (n := n) (M := M) :=
  dualSheaf (dualSheaf (exteriorSheaf E r))

end MathlibExt.AlgebraicGeometry.HolomorphicSheafHiggsModels
