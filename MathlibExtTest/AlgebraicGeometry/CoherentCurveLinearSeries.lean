/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

universe u

section Cohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

-- Global sections are additive on every scheme over `k`, so cohomology is defined.
example : (sectionsFunctor f).Additive := inferInstance

noncomputable example (F : X.Modules) (n : ℕ) : ModuleCat.{u} k := cohomology f F n

-- The `k`-module structure on global sections is restricted along `globalScalarMap f`.
example (F : X.Modules) (c : k) (s : (sectionsFunctor f).obj F) :
    c • s = ((show X.ringCatSheaf.obj.obj (op ⊤) from globalScalarMap f c) •
      (show F.val.obj (op ⊤) from s) : F.val.obj (op ⊤)) :=
  rfl

-- Global sections are left exact, so `H⁰` is global sections.
example : PreservesFiniteLimits (sectionsFunctor f) := inferInstance

-- The structure sheaf is invertible.
example : IsLineBundle (structureModule X) := isLineBundle_structureModule X

-- With only constant global functions, `h⁰(𝒪_X) = 1`.
example [HasConstantGlobalSections f] :
    Module.finrank k (cohomology f (structureModule X) 0) = 1 :=
  finrank_cohomology_zero_structureModule f

end Cohomology

section SpecField

variable (k : Type u) [Field k]

-- On `Spec k` over itself, the scalar map is the canonical identification `k ≅ Γ(Spec k, ⊤)`.
example : globalScalarMap (𝟙 (Spec (.of k))) = (Scheme.ΓSpecIso (.of k)).inv.hom := by
  simp [globalScalarMap]

-- `Spec k` has only constant global functions, for every field `k`.
example : HasConstantGlobalSections (𝟙 (Spec (.of k))) where
  bijective := by
    rw [show globalScalarMap (𝟙 (Spec (.of k))) = (Scheme.ΓSpecIso (.of k)).inv.hom by
      simp [globalScalarMap]]
    exact (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective

-- Over an algebraically closed field, the instance for integral universally closed schemes
-- applies.
example [IsAlgClosed k] : HasConstantGlobalSections (𝟙 (Spec (.of k))) := inferInstance

-- `Spec k` has dimension zero, so it is not a proper curve.
example : ¬ IsProperCurve (𝟙 (Spec (.of k))) := fun h ↦ by
  have := h.topologicalKrullDim_eq_one
  rw [show topologicalKrullDim (Spec (.of k)) = 0 from
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := k)).trans
      (ringKrullDim_eq_zero_of_field k)] at this
  exact zero_ne_one this

end SpecField

section SmoothCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

-- Every nonempty smooth proper scheme of relative dimension one is a proper curve.
example [IsProper f] [SmoothOfRelativeDimension 1 f] [Nonempty X] : IsProperCurve f :=
  inferInstance

-- For a smooth proper integral curve over an algebraically closed field, the genus is defined
-- from the standard hypotheses alone.
noncomputable example [IsAlgClosed k] [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] : ℕ :=
  genus f

end SmoothCurve

section ProperCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProperCurve f]

-- A proper curve is proper and one-dimensional.
example : IsProper f := inferInstance

example : topologicalKrullDim X = 1 := IsProperCurve.topologicalKrullDim_eq_one (f := f)

-- The degree is the Euler-characteristic difference `χ(L) - χ(𝒪_X)`; `𝒪_X` has degree zero.
example (L : X.Modules) (hL : IsLineBundle L) :
    degree f L hL =
      ((Module.finrank k (cohomology f L 0) : ℤ) - Module.finrank k (cohomology f L 1)) -
        ((Module.finrank k (cohomology f (structureModule X) 0) : ℤ) -
          Module.finrank k (cohomology f (structureModule X) 1)) := by
  rw [degree]
  ring

example : degree f (structureModule X) (isLineBundle_structureModule X) = 0 := by simp

-- The genus is `dim H¹(X, 𝒪_X)`.
example [HasConstantGlobalSections f] :
    genus f = Module.finrank k (cohomology f (structureModule X) 1) :=
  rfl

-- A linear series is an invertible sheaf of the given degree with a subspace of sections of
-- the given dimension.
example (d r : ℕ) (L : X.Modules) (hL : IsLineBundle L) (hd : degree f L hL = d)
    (V : Submodule k (cohomology f L 0)) (hV : Module.finrank k V = r + 1) :
    LinearSeries f d r :=
  ⟨L, hL, hd, V, hV⟩

-- Every proper curve with only constant global functions carries the linear series `g^0_0`
-- given by `𝒪_X` and all of `H⁰(X, 𝒪_X)`.
noncomputable example [HasConstantGlobalSections f] : LinearSeries f 0 0 :=
  ⟨structureModule X, isLineBundle_structureModule X, by simp, ⊤, by
    simp [finrank_cohomology_zero_structureModule]⟩

-- Its selected space of sections is finite-dimensional.
example (d r : ℕ) (D : LinearSeries f d r) : FiniteDimensional k D.V :=
  Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)

-- The degree of a linear series is nonnegative.
example (d r : ℕ) (D : LinearSeries f d r) : 0 ≤ degree f D.L D.isLineBundle := by
  rw [D.degree_eq]; exact Int.natCast_nonneg d

end ProperCurve

section BrillNoetherNumber

-- `brillNoetherNumber g d r = g - (r + 1)(g - d + r)` uses integer subtraction: negative values
-- are kept.
example : brillNoetherNumber 0 0 0 = 0 := by norm_num [brillNoetherNumber]

example : brillNoetherNumber 1 0 1 = -3 := by norm_num [brillNoetherNumber]

example : brillNoetherNumber 3 2 1 = -1 := by norm_num [brillNoetherNumber]

example : brillNoetherNumber 4 3 1 = 0 := by norm_num [brillNoetherNumber]

-- `r = 0`: every effective degree `d` has `ρ = d`.
example (g d : ℕ) : brillNoetherNumber g d 0 = d := by
  simp [brillNoetherNumber]

-- Pencils (`r = 1`): `ρ = 2d - g - 2`.
example (g d : ℕ) : brillNoetherNumber g d 1 = 2 * (d : ℤ) - g - 2 := by
  simp [brillNoetherNumber]
  ring

-- The canonical series `g^{g-1}_{2g-2}` has `ρ = 0`.
example (n : ℕ) : brillNoetherNumber (n + 1) (2 * n) n = 0 := by
  simp [brillNoetherNumber]
  ring

end BrillNoetherNumber

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
