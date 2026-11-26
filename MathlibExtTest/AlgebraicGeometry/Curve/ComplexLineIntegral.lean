/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.ComplexLineIntegral
import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver

@[expose] public section

open scoped Manifold Topology

namespace AlgebraicCurve

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F]

-- The coordinate differential at a place is the differential of the uniformizer, which has order
-- one there.
example (v : Place ℂ F) : v.dCoord = KaehlerDifferential.D ℂ F v.uniformizer := rfl

example (v : Place ℂ F) : v.ord v.uniformizer = 1 := v.ord_uniformizer

-- Every place of a complex curve is rational, and evaluation there takes the residue.
example (v : Place ℂ F) : v.IsRational := v.isRational_of_isCurveOver

example (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt v.isRational_of_isCurveOver f) :=
  v.hasValueAt_evalAt _ hf

-- Without a holomorphic atlas, neither differentials nor primitives can be read.
example [∀ v : Place ℂ F, v.DCoordGenerates] (_v : Place ℂ F) (_ω : Ω[F⁄ℂ])
    (_γ : Path _v _v) : True := by
  fail_if_success have := _v.readDifferential _ω
  fail_if_success have := IsPrimitiveAlong _ω _γ fun _ => 0
  trivial

variable [IsHolomorphicAtlas F]

-- A function regular at a place reads analytically at the centre of the chart at that place, and
-- the uniformizer reads with nonzero derivative there.
example (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    AnalyticAt ℂ (v.chartRead f) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  v.analyticAt_chartRead hf

example (v : Place ℂ F) : deriv (v.chartRead v.uniformizer) (extChartAt 𝓘(ℂ, ℂ) v v) ≠ 0 :=
  IsHolomorphicAtlas.deriv_chartRead_uniformizer_ne_zero v

variable [∀ v : Place ℂ F, v.DCoordGenerates]

-- The differential `f • dCoord` reads as the reading of `f` times the derivative of the reading
-- of the uniformizer, and the zero differential reads as zero.
example (v : Place ℂ F) (f : F) (z : ℂ) :
    v.readDifferential (f • v.dCoord) z =
      v.chartRead f z * deriv (v.chartRead v.uniformizer) z := by
  unfold Place.readDifferential
  rw [v.differentialCoeff_unique rfl]

example (v : Place ℂ F) (z : ℂ) : v.readDifferential 0 z = 0 := by
  simp

-- The line integral is the increment of any primitive, so a primitive with distinct end values
-- gives a nonzero integral.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) : pathIntegral ω γ ⟨g, hg⟩ = g 1 - g 0 := by
  unfold pathIntegral
  exact (⟨g, hg⟩ : ∃ g, IsPrimitiveAlong ω γ g).choose_spec.sub_eq_sub hg

example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) (h01 : g 1 ≠ g 0) : pathIntegral ω γ ⟨g, hg⟩ ≠ 0 := by
  rw [hg.pathIntegral_eq]
  exact sub_ne_zero.mpr h01

-- Reversal changes the sign of the increment, and concatenation adds increments.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ)
    (hg : IsPrimitiveAlong ω γ g) : pathIntegral ω γ.symm ⟨_, hg.symm⟩ = g 0 - g 1 := by
  rw [hg.symm.pathIntegral_eq, Function.comp_apply, Function.comp_apply, unitInterval.symm_one,
    unitInterval.symm_zero]

example (ω : Ω[F⁄ℂ]) {P Q R : Place ℂ F} (γ : Path P Q) (γ' : Path Q R)
    (g g' : unitInterval → ℂ) (hg : IsPrimitiveAlong ω γ g) (hg' : IsPrimitiveAlong ω γ' g')
    (h : ∃ k, IsPrimitiveAlong ω (γ.trans γ') k) :
    pathIntegral ω (γ.trans γ') h = (g 1 - g 0) + (g' 1 - g' 0) := by
  rw [pathIntegral_trans ⟨g, hg⟩ ⟨g', hg'⟩ h, hg.pathIntegral_eq, hg'.pathIntegral_eq]

-- Going along a path and back gives the integral zero.
example (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (h : ∃ g, IsPrimitiveAlong ω γ g)
    (h' : ∃ g, IsPrimitiveAlong ω (γ.trans γ.symm) g) :
    pathIntegral ω (γ.trans γ.symm) h' = 0 := by
  rw [pathIntegral_trans h (exists_isPrimitiveAlong_symm h) h', pathIntegral_symm h,
    add_neg_cancel]

-- Boundary examples: the zero differential along any path, and any differential along a constant
-- path, have zero integral.
example {P Q : Place ℂ F} (γ : Path P Q) : pathIntegral 0 γ ⟨0, isPrimitiveAlong_zero γ⟩ = 0 :=
  pathIntegral_zero γ _

example (ω : Ω[F⁄ℂ]) (P : Place ℂ F) (h : ∃ g, IsPrimitiveAlong ω (Path.refl P) g) :
    pathIntegral ω (Path.refl P) h = 0 :=
  pathIntegral_refl ω P h

-- The Abel-Jacobi vector collects the line integrals of the family, and vanishes for the zero
-- family.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ P : Place ℂ F} (γ : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) (i : Fin n) :
    abelJacobiVec b γ h i = pathIntegral (b i) γ (h i) :=
  rfl

example {n : ℕ} {P₀ P : Place ℂ F} (γ : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong ((fun _ : Fin n => (0 : Ω[F⁄ℂ])) i) γ g) :
    abelJacobiVec (fun _ : Fin n => (0 : Ω[F⁄ℂ])) γ h = 0 :=
  abelJacobiVec_zero γ h

-- A loop gives a period, and two paths with the same endpoints differ by a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F} (γ : Path P P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) : abelJacobiVec b γ h ∈ periodSubgroup b :=
  AddSubgroup.subset_closure ⟨P, γ, h, rfl⟩

example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ P : Place ℂ F} (γ γ' : Path P₀ P)
    (h : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ g) (h' : ∀ i, ∃ g, IsPrimitiveAlong (b i) γ' g) :
    abelJacobiVec b γ h - abelJacobiVec b γ' h' ∈ periodSubgroup b :=
  abelJacobiVec_sub_mem_periodSubgroup b γ γ' h h'

-- The Abel-Jacobi map sends a multiple of a place to the multiple of its Abel-Jacobi vector, and
-- other choices of paths change it by a period.
example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ : Place ℂ F} (γ : ∀ P, Path P₀ P)
    (h : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ P) g) (v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b γ h (Finsupp.single v m) = m • abelJacobiVec b (γ v) (h v) := by
  simp [abelJacobiDiv]

example {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P₀ : Place ℂ F} (γ γ' : ∀ P, Path P₀ P)
    (h : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ P) g)
    (h' : ∀ P i, ∃ g, IsPrimitiveAlong (b i) (γ' P) g) (D : Divisor ℂ F) :
    abelJacobiDiv b γ h D - abelJacobiDiv b γ' h' D ∈ periodSubgroup b :=
  abelJacobiDiv_sub_mem_periodSubgroup b γ γ' h h' D

end AlgebraicCurve
