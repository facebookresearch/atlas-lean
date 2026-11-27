/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Actual holomorphic coefficient modules from harmonic kernels

The coefficient ring consists of the actual holomorphic functions on each
open. Multiplication on sections is pointwise in the original bundle fibres.
The local Leibniz and gluing adapters below refer to these fixed formulas;
they contain no harmonic existence or Hodge correspondence conclusion.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels

open CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HolomorphicCoefficientSheaves HarmonicHolomorphicSectionKernels
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

abbrev HolomorphicScalars (U : Opens M) := holomorphicAlgebra (Coordinates n) M U

/-- The ordinary action is multiplication by the actual scalar-valued function in each fibre. -/
instance sectionHolomorphicModule (U : Opens M) :
    Module (HolomorphicScalars (n := n) U) (RoughSection B U) :=
  Module.compHom (RoughSection B U) (holomorphicAlgebra (Coordinates n) M U).val.toRingHom

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- The value of the coefficient action retains its literal section formula. -/
theorem holomorphic_smul_apply (U : Opens M) (f : HolomorphicScalars (n := n) U)
    (s : RoughSection B U) (x : U) : (f • s) x = f.val x • s x := rfl

/-- Ordinary holomorphic-function Leibniz facts for the prescribed full bar derivative. -/
class BarMultiplicationCalculus (h : HermitianMetric B) (A : SmoothConnection B) : Prop where
  smooth : ∀ (U : Opens M) (f : HolomorphicScalars (n := n) U) (s : RoughSection B U),
    IsSmoothSection B U s → IsSmoothSection B U (f • s)
  bar : ∀ (U : Opens M) (f : HolomorphicScalars (n := n) U) (s : RoughSection B U),
    IsSmoothSection B U s → ∀ i (x : U), x.val ∈ B.core.baseSet i → ∀ u,
      barConnectionValue B h A i U (f • s) x u = f.val x • barConnectionValue B h A i U s x u

variable (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]

/-- The same kernel is now an actual module over holomorphic functions. -/
def holomorphicKernel (U : Opens M) :
    Submodule (HolomorphicScalars (n := n) U) (RoughSection B U) where
  carrier := {s | IsBarHolomorphic B h A U s}
  zero_mem' := (barKernel B h A U).zero_mem
  add_mem' hs ht := (barKernel B h A U).add_mem hs ht
  smul_mem' f s hs := by
    refine ⟨BarMultiplicationCalculus.smooth (B := B) (h := h) (A := A) U f s hs.1, ?_⟩
    intro i x hx u
    rw [BarMultiplicationCalculus.bar (B := B) (h := h) (A := A) U f s hs.1 i x hx u,
      hs.2 i x hx u, smul_zero]

/-- Restriction is the actual restricted bundle section, semilinear over function restriction. -/
def holomorphicRestriction {U V : Opens M} (a : V ≤ U) :
    holomorphicKernel B h A U →ₛₗ[(restriction (Coordinates n) M a).toRingHom]
      holomorphicKernel B h A V where
  toFun s := ⟨restrictSection B a s.val, (barRestriction B h A a ⟨s.val, s.property⟩).property⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- The public presheaf of O-modules retains every actual holomorphic scalar and restriction. -/
def holomorphicModulePresheaf : PresheafOfModules.{0} (ringPresheaf (Coordinates n) M) where
  obj U := ModuleCat.of (HolomorphicScalars (n := n) U.unop) (holomorphicKernel B h A U.unop)
  map {U V} a := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((ringPresheaf (Coordinates n) M).map a).hom).obj
      (ModuleCat.of (HolomorphicScalars (n := n) V.unop) (holomorphicKernel B h A V.unop))) {
    toFun := holomorphicRestriction B h A a.unop.le
    map_add' := (holomorphicRestriction B h A a.unop.le).map_add
    map_smul' := by intro f s; apply Subtype.ext; rfl }
  map_id U := by apply ModuleCat.hom_ext; ext s; rfl
  map_comp a b := by apply ModuleCat.hom_ext; ext s; rfl

/-- The ordinary sheaf condition is for the actual kernel presheaf, independently of integrability. -/
class KernelSheafCondition : Prop where
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology M)
    (holomorphicModulePresheaf B h A).presheaf

variable [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]

/-- The native structure sheaf is the prescribed ring of actual holomorphic functions. -/
def holomorphicStructureRing : Sheaf (Opens.grothendieckTopology M) RingCat.{0} :=
  ⟨ringPresheaf (Coordinates n) M, HolomorphicCoefficientSheaves.SheafCondition.isSheaf⟩

/-- The holomorphic bundle sheaf is the same actual smooth-section kernel on every open. -/
def holomorphicModule [KernelSheafCondition B h A] :
    SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) :=
  ⟨holomorphicModulePresheaf B h A, KernelSheafCondition.isSheaf⟩

end MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
