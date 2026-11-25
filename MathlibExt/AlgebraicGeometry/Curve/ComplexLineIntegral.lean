/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean`,
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`,
`Definitions/Def_ModularCurve_CanonicalDivisor.lean`,
`Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean` and
`Definitions/Def_AlgebraicCurve_RegularDifferentials.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Connected.PathConnected
public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Complex line integrals and Abel-Jacobi vectors on an algebraic curve

Places, their residue fields, divisors and the curve hypothesis `IsCurveOver` come from the
curve layer in `MathlibExt/AlgebraicGeometry/Curve/`. This file adds a uniformizer and its
coordinate differential at a place, evaluation of functions at rational places, and, for a
complex function field, the reading of a differential in a local chart.

Evaluation into the base field takes a proof that the place is rational. Over an algebraically
closed base, every place of a curve (`IsCurveOver`) is rational, so charts of a complex curve
read functions through the residue map. A differential is read through its coefficient with
respect to the coordinate differential, which requires `DCoordGenerates`; there is no fallback
value for differentials outside that span.

`pathIntegral` is the difference of the values of a chosen local primitive along a path when
such a primitive exists, and zero otherwise. The Abel-Jacobi vector of a place relative to a
base place collects these integrals for a family of differentials. No path-independence
assertion is made for this choice-based construction; the zero differential and constant
paths have zero integral.
-/

@[expose] public section

noncomputable section

open IsLocalRing KaehlerDifferential
open scoped Manifold Topology

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

variable (v : Place K F)

def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer

class DCoordGenerates : Prop where
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 := by
  intro h0
  have htop := DCoordGenerates.span_eq_top (v := v)
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hx_mem : x ∈ Submodule.span F {v.dCoord} := htop ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hx_mem
  exact hx hx_mem

theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

-- The coefficient of a differential with respect to `v.dCoord`. It is only defined when
-- `v.dCoord` spans the differentials, so no differential is read with a fallback value.
def differentialCoeff [v.DCoordGenerates] (ω : Ω[F⁄K]) : F :=
  (v.exists_eq_smul_dCoord ω).choose

theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω :=
  (v.exists_eq_smul_dCoord ω).choose_spec.symm

theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f := by
  have key : (v.differentialCoeff ω - f) • v.dCoord = 0 := by
    rw [sub_smul, v.differentialCoeff_smul_dCoord ω, hf, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h v.dCoord_ne_zero

@[simp]
theorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff v.dCoord = 1 :=
  v.differentialCoeff_unique (one_smul F v.dCoord).symm

@[simp]
theorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=
  v.differentialCoeff_unique (zero_smul F v.dCoord).symm

theorem differentialCoeff_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : F) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = c * v.differentialCoeff ω :=
  v.differentialCoeff_unique
    (by rw [mul_smul, v.differentialCoeff_smul_dCoord])

def ordDifferential [v.DCoordGenerates] (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.ordDifferential v.dCoord = 0 := by
  rw [ordDifferential, v.differentialCoeff_dCoord, v.ord_one]

theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :
    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω := by
  rw [ordDifferential, ordDifferential, v.differentialCoeff_smul, v.ord_mul hc hω]


def IsRational : Prop := Function.Surjective (algebraMap K v.ResidueField)

theorem algebraMap_residueField_injective :
    Function.Injective (algebraMap K v.ResidueField) :=
  (algebraMap K v.ResidueField).injective

theorem isRational_of_isAlgClosed [IsAlgClosed K] [Module.Finite K v.ResidueField] :
    v.IsRational :=
  v.surjective_algebraMap_residueField_of_isAlgClosed

-- Every place of a curve over an algebraically closed field is rational.
theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] : v.IsRational :=
  have := IsCurveOver.finiteResidueField v
  v.isRational_of_isAlgClosed

-- At a rational place the residue map identifies the base field with the residue field.
def residueEquiv (hv : v.IsRational) : K ≃+* v.ResidueField :=
  RingEquiv.ofBijective (algebraMap K v.ResidueField) ⟨v.algebraMap_residueField_injective, hv⟩

-- The value at a rational place of a function regular there; functions with a pole at the
-- place are sent to `0`.
open Classical in
def evalAt (hv : v.IsRational) (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    (v.residueEquiv hv).symm (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt hv f = (v.residueEquiv hv).symm (residue v.toValuationSubring ⟨f, hf⟩) :=
  dite_eq_left hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt hv f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hv hf]
  exact (v.residueEquiv hv).apply_symm_apply _

theorem hasValueAt_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValueAt f (v.evalAt hv f) :=
  (v.hasValueAt_iff_residue hf _).mpr (v.algebraMap_evalAt hv hf).symm

@[simp]
theorem evalAt_one (hv : v.IsRational) : v.evalAt hv (1 : F) = 1 := by
  rw [v.evalAt_of_mem hv (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, map_one]

@[simp]
theorem evalAt_zero (hv : v.IsRational) : v.evalAt hv (0 : F) = 0 := by
  rw [v.evalAt_of_mem hv (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, map_zero]


theorem exists_ord_eq_one_and_dCoord_eq (v : Place K F) :
    ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

def dCoordFn (v : Place K F) : F :=
  Classical.choose v.exists_ord_eq_one_and_dCoord_eq

theorem ord_dCoordFn (v : Place K F) : v.ord v.dCoordFn = 1 :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).1

theorem dCoord_eq_D_dCoordFn (v : Place K F) :
    v.dCoord = KaehlerDifferential.D K F v.dCoordFn :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).2


variable {F : Type*} [Field F] [Algebra ℂ F]

private theorem nontrivial_kaehlerDifferential [IsCurveOver ℂ F] : Nontrivial Ω[F⁄ℂ] :=
  Module.nontrivial_of_finrank_pos (R := F)
    (by rw [(IsCurveOver.kaehler_free_rank_one (K := ℂ) (F := F)).2]; exact one_pos)

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F]

def chartRead (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  fun z => ((extChartAt 𝓘(ℂ, ℂ) v).symm z).evalAt (isRational_of_isCurveOver _) f

theorem chartRead_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    v.chartRead f z =
      ((extChartAt 𝓘(ℂ, ℂ) v).symm z).evalAt (isRational_of_isCurveOver _) f := rfl

@[simp]
theorem chartRead_zero (v : Place ℂ F) : v.chartRead 0 = 0 := by
  funext z
  simp [chartRead_apply]

def readDifferential (v : Place ℂ F) [v.DCoordGenerates] (ω : Ω[F⁄ℂ]) : ℂ → ℂ :=
  fun z => v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z

theorem readDifferential_apply (v : Place ℂ F) [v.DCoordGenerates] (ω : Ω[F⁄ℂ]) (z : ℂ) :
    v.readDifferential ω z =
      v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z := rfl

-- The differential `f • v.dCoord` is read through its coefficient `f`.
theorem readDifferential_smul_dCoord (v : Place ℂ F) [v.DCoordGenerates] (f : F) :
    v.readDifferential (f • v.dCoord) =
      fun z => v.chartRead f z * deriv (v.chartRead v.dCoordFn) z := by
  have := nontrivial_kaehlerDifferential (F := F)
  funext z
  rw [readDifferential_apply, v.differentialCoeff_unique rfl]

@[simp]
theorem readDifferential_zero (v : Place ℂ F) [v.DCoordGenerates] :
    v.readDifferential 0 = 0 := by
  have := nontrivial_kaehlerDifferential (F := F)
  funext z
  simp [readDifferential_apply]

end Place

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [IsCurveOver ℂ F]
variable [∀ v : Place ℂ F, v.DCoordGenerates]

def IsPrimitiveAlong (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ) :
    Prop :=
  ∀ t₀ : unitInterval, ∃ Φ : ℂ → ℂ,
    (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)),
        HasDerivAt Φ ((γ t₀).readDifferential ω z) z) ∧
      ∀ᶠ t in 𝓝 t₀, g t = Φ (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t))

open Classical in
def pathIntegral (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) : ℂ :=
  if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0

open Classical in
theorem pathIntegral_def (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral ω γ = if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0 :=
  rfl

private theorem pathIntegral_eq_zero_of_locallyConstant {ω : Ω[F⁄ℂ]} {P Q : Place ℂ F}
    {γ : Path P Q}
    (h : ∀ g, IsPrimitiveAlong ω γ g → ∀ t₀, ∀ᶠ t in 𝓝 t₀, g t = g t₀) :
    pathIntegral ω γ = 0 := by
  classical
  rw [pathIntegral_def]
  split_ifs with hg
  · rw [sub_eq_zero]
    exact ((IsLocallyConstant.iff_eventually_eq _).mpr
      (h _ hg.choose_spec)).apply_eq_of_preconnectedSpace 1 0
  · rfl

theorem pathIntegral_zero {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral (0 : Ω[F⁄ℂ]) γ = 0 := by
  refine pathIntegral_eq_zero_of_locallyConstant fun g hg t₀ => ?_
  obtain ⟨Φ, hΦ, hgΦ⟩ := hg t₀
  set x₀ := extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)
  simp only [Place.readDifferential_zero, Pi.zero_apply] at hΦ
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hΦ
  have hconst : ∀ z ∈ Metric.ball x₀ ε, Φ z = Φ x₀ := fun z hz =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x₀ ε).isPreconnected
      (fun w hw => (hball w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hball w hw).deriv) hz (Metric.mem_ball_self hε)
  have hnear : ∀ᶠ t in 𝓝 t₀, extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t) ∈ Metric.ball x₀ ε :=
    ((continuousAt_extChartAt (γ t₀)).comp γ.continuous.continuousAt).eventually_mem
      (Metric.ball_mem_nhds x₀ hε)
  filter_upwards [hgΦ, hnear] with t ht htx
  rw [ht, hconst _ htx, hgΦ.self_of_nhds]

theorem pathIntegral_refl (ω : Ω[F⁄ℂ]) (P : Place ℂ F) :
    pathIntegral ω (Path.refl P) = 0 := by
  refine pathIntegral_eq_zero_of_locallyConstant fun g hg t₀ => ?_
  obtain ⟨Φ, -, hgΦ⟩ := hg t₀
  filter_upwards [hgΦ] with t ht
  rw [ht, hgΦ.self_of_nhds, Path.refl_apply, Path.refl_apply]

open Classical in
def abelJacobiVec {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) : Fin n → ℂ :=
  if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0

open Classical in
theorem abelJacobiVec_def {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) :
    abelJacobiVec b P₀ P =
      if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0 :=
  rfl

theorem abelJacobiVec_zero {n : ℕ} (P₀ P : Place ℂ F) :
    abelJacobiVec (0 : Fin n → Ω[F⁄ℂ]) P₀ P = 0 := by
  classical
  rw [abelJacobiVec_def]
  split_ifs
  · funext i
    exact pathIntegral_zero _
  · rfl

def abelJacobiDiv {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor ℂ F →+ (Fin n → ℂ) :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Fin n → ℂ) (abelJacobiVec b P₀ v)

@[simp]
theorem abelJacobiDiv_single {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b P₀ (Finsupp.single v m) = m • abelJacobiVec b P₀ v := by
  simp [abelJacobiDiv]

theorem abelJacobiDiv_apply {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) (D : Divisor ℂ F) :
    abelJacobiDiv b P₀ D = D.sum fun v m => m • abelJacobiVec b P₀ v := by
  simp only [abelJacobiDiv, Finsupp.liftAddHom_apply]
  rfl

def pathPeriodLattice {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) : Submodule ℤ (Fin n → ℂ) :=
  Submodule.span ℤ {u | ∃ (P : Place ℂ F) (γ : Path P P), u = fun i => pathIntegral (b i) γ}

theorem mem_pathPeriodLattice_of_loop {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F}
    (γ : Path P P) : (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b :=
  Submodule.subset_span ⟨P, γ, rfl⟩


end AlgebraicCurve
