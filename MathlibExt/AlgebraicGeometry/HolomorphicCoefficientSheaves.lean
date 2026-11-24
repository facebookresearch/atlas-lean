/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Analysis.Complex.Basic

/-!
# Actual holomorphic coefficient rings on every manifold open

A section is an actual complex-valued function whose actual chart expression
is holomorphic. Restriction is function restriction. Native sheafification
constructs the ring sheaf; a separate ordinary sheaf-condition comparison
can identify its sections with the displayed functions. There is no freely
chosen ring named O_X. This is coefficient support for local D-module,
lambda-connection and Hodge/period interfaces on arbitrary complex manifolds.

Ordinary differentiability and ring/sheaf primitives are Mathlib support at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves

open CategoryTheory Opposite TopologicalSpace ManifoldDifferentialForms
open scoped Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def chartFunction {U : Opens M} (f : U → ℂ) (a : M) : E → ℂ := by
  classical
  exact fun z ↦ if h : z ∈ chartDomain ℂ E M U a then
    f ⟨(extChartAt 𝓘(ℂ, E) a).symm z, h.2⟩ else 0

def IsHolomorphic {U : Opens M} (f : U → ℂ) : Prop :=
  ∀ a : M, ContDiffOn ℂ ∞ (chartFunction E M f a) (chartDomain ℂ E M U a)

def holomorphicAlgebra (U : Opens M) : Subalgebra ℂ (U → ℂ) where
  carrier := {f | IsHolomorphic E M f}
  zero_mem' := by
    intro a
    have he : chartFunction E M (0 : U → ℂ) a = fun _ ↦ 0 := by
      classical
      funext z
      by_cases hz : z ∈ chartDomain ℂ E M U a <;> simp [chartFunction, hz]
    rw [he]
    exact contDiffOn_const
  one_mem' := by
    intro a
    apply (contDiffOn_const : ContDiffOn ℂ ∞ (fun _ : E ↦ (1 : ℂ))
      (chartDomain ℂ E M U a)).congr
    intro z hz
    simp [chartFunction, hz]
  add_mem' := by
    intro f g hf hg a
    have he : chartFunction E M (f + g) a =
        chartFunction E M f a + chartFunction E M g a := by
      classical
      funext z
      by_cases hz : z ∈ chartDomain ℂ E M U a <;> simp [chartFunction, hz]
    rw [he]
    exact (hf a).add (hg a)
  mul_mem' := by
    intro f g hf hg a
    have he : chartFunction E M (f * g) a =
        chartFunction E M f a * chartFunction E M g a := by
      classical
      funext z
      by_cases hz : z ∈ chartDomain ℂ E M U a <;> simp [chartFunction, hz]
    rw [he]
    exact (hf a).mul (hg a)
  algebraMap_mem' c := by
    intro a
    apply (contDiffOn_const : ContDiffOn ℂ ∞ (fun _ : E ↦ c)
      (chartDomain ℂ E M U a)).congr
    intro z hz
    simp [chartFunction, hz]

def restriction {U V : Opens M} (h : V ≤ U) :
    holomorphicAlgebra E M U →ₐ[ℂ] holomorphicAlgebra E M V where
  toFun f := ⟨fun x ↦ f.val ⟨x.val, h x.property⟩, by
    intro a
    have hd : chartDomain ℂ E M V a ⊆ chartDomain ℂ E M U a :=
      fun _ hz ↦ ⟨hz.1, h hz.2⟩
    apply ((f.property a).mono hd).congr
    intro z hz
    simp [chartFunction, hz, hd hz]⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The presheaf of holomorphic functions on a complex manifold: functions that
are holomorphic in every chart. The holomorphic atlas makes this the structure
sheaf of the complex manifold. -/
def coefficientPresheaf [IsManifold 𝓘(ℂ, E) ∞ M] :
    (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ where
  obj U := CommAlgCat.of ℂ (holomorphicAlgebra E M U.unop)
  map f := CommAlgCat.ofHom (restriction E M f.unop.le)
  map_id U := by ext f x; rfl
  map_comp f g := by ext a x; rfl

variable [IsManifold 𝓘(ℂ, E) ∞ M]

def ringPresheaf : (Opens M)ᵒᵖ ⥤ RingCat.{0} :=
  coefficientPresheaf E M ⋙ forget₂ (CommAlgCat.{0} ℂ) CommRingCat.{0} ⋙
    forget₂ CommRingCat.{0} RingCat.{0}

def ringSheaf [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}] :
    TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).obj (ringPresheaf E M)

/-- Ordinary holomorphic-function gluing, kept as a proof input for this
fixed native ring presheaf rather than an unspecified coefficient carrier. -/
class SheafCondition [IsManifold 𝓘(ℂ, E) ∞ M] : Prop where
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology M) (ringPresheaf E M)

end MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves

