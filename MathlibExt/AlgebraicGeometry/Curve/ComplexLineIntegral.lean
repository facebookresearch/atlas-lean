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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Connected.PathConnected

/-!
# Complex line integrals and Abel-Jacobi vectors on an algebraic curve

A place of a function field `F` over `K` is a discrete valuation subring
of `F` containing the image of `K`. For a complex function field, a
differential is read in a local chart at a place; `pathIntegral` is the
difference of the values of a chosen local primitive along a path when
such a primitive exists, and zero otherwise. The Abel-Jacobi vector of a
place relative to a base place collects these integrals for a family of
differentials. No path-independence assertion is made for this
choice-based construction.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped Manifold Topology

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A place of the function field `F` over `K`: a discrete valuation
subring of `F` containing the image of `K`. -/
structure Place where
  toValuationSubring : ValuationSubring F
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  ne_top' : toValuationSubring ≠ ⊤
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring

theorem _root_.ValuationSubring.not_isField_of_ne_top {A : ValuationSubring F} (hA : A ≠ ⊤) :
    ¬IsField A := by
  intro hf
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  by_cases hx : x ∈ A
  · exact hx
  ·

    exfalso
    have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hxi0 : (⟨x⁻¹, hxi⟩ : A) ≠ 0 := by
      simp only [ne_eq, Subtype.ext_iff]
      exact inv_ne_zero hx0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hxi0
    have hb' : x⁻¹ * (b : F) = 1 := by
      have h := congrArg (Subtype.val) hb
      simpa using h
    have hbx : (b : F) = x := by
      field_simp at hb'
      exact hb'
    exact hx (hbx ▸ b.2)

namespace Place

variable {K F}

theorem toValuationSubring_injective :
    Function.Injective (toValuationSubring (K := K) (F := F)) := by
  rintro ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ (rfl : a = b)
  rfl

@[ext]
theorem ext {v w : Place K F} (h : v.toValuationSubring = w.toValuationSubring) : v = w :=
  toValuationSubring_injective h

variable (v : Place K F)

instance : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'

instance : IsDiscreteValuationRing v.toValuationSubring where
  not_a_field' := by
    rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact ValuationSubring.not_isField_of_ne_top F v.ne_top'

instance : Algebra K v.toValuationSubring :=
  ((algebraMap K F).codRestrict v.toValuationSubring.toSubring v.algebraMap_mem').toAlgebra

@[simp]
theorem coe_algebraMap (a : K) :
    (algebraMap K v.toValuationSubring a : F) = algebraMap K F a := rfl

instance : IsScalarTower K v.toValuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun a => (v.coe_algebraMap a).symm

abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

def deg : ℕ := Module.finrank K v.ResidueField

class FiniteResidue : Prop where
  finite : Module.Finite K v.ResidueField

def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _

@[simp]
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring := rfl

def adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F

theorem adicValuation_ne_zero {f : F} (hf : f ≠ 0) : v.adicValuation f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem adicValuation_coe (a : v.toValuationSubring) :
    v.adicValuation (a : F) = v.heightOneSpectrum.intValuation a := by
  simpa [adicValuation] using v.heightOneSpectrum.valuation_of_algebraMap (K := F) a

theorem adicValuation_coe_eq_one_iff (a : v.toValuationSubring) :
    v.adicValuation (a : F) = 1 ↔ IsUnit a := by
  rw [v.adicValuation_coe, HeightOneSpectrum.intValuation_eq_one_iff, heightOneSpectrum_asIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem adicValuation_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.adicValuation (π : F) = exp (-1 : ℤ) := by
  rw [v.adicValuation_coe]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero
    (by rw [heightOneSpectrum_asIdeal, hπ.maximalIdeal_eq])

def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))

@[simp]
theorem ord_zero : v.ord (0 : F) = 0 := by simp [ord]

@[simp]
theorem ord_one : v.ord (1 : F) = 0 := by simp [ord]

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g) = v.ord f + v.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul (v.adicValuation_ne_zero hf) (v.adicValuation_ne_zero hg)]
  ring

theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · simp only [ord, map_inv₀, WithZero.log_inv, neg_neg]

theorem ord_coe_unit (u : v.toValuationSubringˣ) :
    v.ord ((u : v.toValuationSubring) : F) = 0 := by
  simp [ord, (v.adicValuation_coe_eq_one_iff _).mpr u.isUnit]

theorem ord_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.ord (π : F) = 1 := by
  simp [ord, v.adicValuation_coe_irreducible hπ]

theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  simp only [ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem ord_unit_smul_zpow (u : v.toValuationSubringˣ) {π : v.toValuationSubring}
    (hπ : Irreducible π) (n : ℤ) :
    v.ord (((u : v.toValuationSubring) : F) * ((π : F) ^ n)) = n := by
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hu : ((u : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  rw [v.ord_mul hu (zpow_ne_zero n hπF), v.ord_coe_unit u, zero_add,
    v.ord_zpow _ _, v.ord_coe_irreducible hπ, mul_one]

theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}
    (hπ : Irreducible π) :
    ∃ u : v.toValuationSubringˣ,
      f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord f)) := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := F) hπ hf
  rw [Units.smul_def, Algebra.smul_def] at hu
  have hcoe : algebraMap v.toValuationSubring F (u : v.toValuationSubring)
      = ((u : v.toValuationSubring) : F) := rfl
  have hcoe' : algebraMap v.toValuationSubring F π = (π : F) := rfl
  rw [hcoe, hcoe'] at hu
  have hn : v.ord f = n := by rw [hu]; exact v.ord_unit_smul_zpow u hπ n
  exact ⟨u, by rw [hn, hu]⟩


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

def differentialCoeff (ω : Ω[F⁄K]) : F :=
  letI := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0

theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω := by
  rw [differentialCoeff, dif_pos (v.exists_eq_smul_dCoord ω)]
  exact (v.exists_eq_smul_dCoord ω).choose_spec.symm

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

def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

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

def residueInv : v.ResidueField → K :=
  Function.invFun (algebraMap K v.ResidueField)

theorem algebraMap_residueInv (hv : v.IsRational) (x : v.ResidueField) :
    algebraMap K v.ResidueField (v.residueInv x) = x :=
  Function.invFun_eq (hv x)

theorem residueInv_algebraMap (a : K) : v.residueInv (algebraMap K v.ResidueField a) = a :=
  Function.leftInverse_invFun v.algebraMap_residueField_injective a

open Classical in

def evalAt (f : F) : K :=
  if hf : f ∈ v.toValuationSubring then
    v.residueInv (residue v.toValuationSubring ⟨f, hf⟩)
  else 0

theorem evalAt_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = v.residueInv (residue v.toValuationSubring ⟨f, hf⟩) :=
  dif_pos hf

theorem algebraMap_evalAt (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    algebraMap K v.ResidueField (v.evalAt f)
      = residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring) := by
  rw [v.evalAt_of_mem hf]
  exact v.algebraMap_residueInv hv _

@[simp]
theorem evalAt_one : v.evalAt (1 : F) = 1 := by
  rw [v.evalAt_of_mem (one_mem _)]
  have h1 : (⟨(1 : F), one_mem _⟩ : v.toValuationSubring) = 1 := rfl
  rw [h1, map_one, ← map_one (algebraMap K v.ResidueField), v.residueInv_algebraMap]


theorem exists_ord_eq_one_and_dCoord_eq (v : Place K F) :
    ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec


end Place

abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Place

def dCoordFn (v : Place K F) : F :=
  Classical.choose v.exists_ord_eq_one_and_dCoord_eq

theorem ord_dCoordFn (v : Place K F) : v.ord v.dCoordFn = 1 :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).1

theorem dCoord_eq_D_dCoordFn (v : Place K F) :
    v.dCoord = KaehlerDifferential.D K F v.dCoordFn :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).2


variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def chartRead (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  fun z => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f

theorem chartRead_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    v.chartRead f z = Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f := rfl

def readDifferential (v : Place ℂ F) (ω : Ω[F⁄ℂ]) : ℂ → ℂ :=
  fun z => v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z

theorem readDifferential_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) (z : ℂ) :
    v.readDifferential ω z =
      v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z := rfl

end Place

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

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

open Classical in

def abelJacobiVec {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) : Fin n → ℂ :=
  if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0

open Classical in
theorem abelJacobiVec_def {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) :
    abelJacobiVec b P₀ P =
      if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0 :=
  rfl

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
