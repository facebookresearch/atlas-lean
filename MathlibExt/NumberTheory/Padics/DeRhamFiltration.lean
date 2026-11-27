/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RepresentationTheory.Intertwining
public import MathlibExt.NumberTheory.Padics.HodgeTate.Representation
public import MathlibExt.NumberTheory.Padics.PotentiallySemistable
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Filtration

/-!
# The filtrations of `B_dR` and of `D_dR(V)`

Let `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`, a complete discrete valuation ring with residue map
Fontaine's `θ : B_dR^+ → ℂ_p`, and `B_dR = BDeRham 𝓞_ℂ_[p] p` its fraction field, on which
`G = Gal(ℚ̄_p/ℚ_p)` acts by `PadicComplexInt.galoisBDeRham`. Let `t = log [ε]`
(`PadicComplexInt.logTeichmuller p (PadicComplexInt.untilt_epsilon p)`) for Fontaine's element
`ε = (1, ζ_p, ζ_{p²}, …)` of the tilt of `𝓞_ℂ_[p]`. Following J.-M. Fontaine, *Le corps des
périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.4–1.5.5 pp. 72–73 and §1.5.7 p. 74,
we show:

* `t = ([ε] - 1) v` with `θ(v) = 1`
  (`PadicComplexInt.exists_logTeichmuller_eq_teichmuller_sub_one_mul`), so
  `t` is a uniformizer of `B_dR^+` (`PadicComplexInt.irreducible_logTeichmuller_epsilon`), and
  `σ(t) = χ(σ) t` for the `p`-adic cyclotomic character `χ`
  (`PadicComplexInt.galoisBDeRhamPlus_logTeichmuller_epsilon`);
* the **filtration** `Fil^i B_dR = t^i B_dR^+`, `i ∈ ℤ` (`PadicComplexInt.filBDeRham`), is
  decreasing, multiplicative, exhaustive and separated, with `Fil^0 B_dR = B_dR^+`, and it is
  stable under `G`;
* `gr^i B_dR = Fil^i B_dR / Fil^{i+1} B_dR ≅ ℂ_p(i)` as representations of `G`, through
  `x ↦ θ(t^{-i} x)` (`PadicComplexInt.grBDeRhamEquiv`).

For `K` finite over `ℚ_p` inside `ℚ̄_p`, `B_dR^{G_K} = K`
(`PadicComplexInt.deRhamFixedSubalgebraEquiv`). For a `ℚ_p`-linear representation `ρ` of `G` on
`V`, with `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}` (`Representation.periods`), following J.-M. Fontaine,
*Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §3.7 pp. 141–142, we
define

* `Fil^i D_dR(V) = (Fil^i B_dR ⊗_{ℚ_p} V)^{G_K}` (`Representation.deRhamFiltration`), the
  `K`-subspaces of `D_dR(V)` of the invariants lying in the image of
  `Fil^i B_dR ⊗_{ℚ_p} V ⊆ B_dR ⊗_{ℚ_p} V` (`PadicComplexInt.filBDeRhamTensor`);
* `gr^i D_dR(V) = Fil^i D_dR(V) / Fil^{i+1} D_dR(V)` (`Representation.deRhamGraded`),

and show that `gr^i B_dR ≅ ℂ_p(i)` induces an injective map
`gr^i D_dR(V) → (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}` (`Representation.deRhamGradedToTwistPeriods`), the
inclusion `gr D_dR(V) ⊆ D_HT(V)` of Fontaine, *op. cit.*, §3.7 p. 142, degree by degree.

## Implementation notes

The filtration of `B_dR` is decreasing, as in Fontaine's work, while Mathlib's `IsFiltration` is
increasing. The subspaces `Fil^i B_dR` are `B_dR^+`-submodules of `B_dR`; their `ℚ_p`-structure
is that of `Submodule.restrictScalars`. The filtration of `D_dR(V)` and its graded pieces are the
general constructions `Representation.periodsFiltration` and `Representation.periodsGraded` for
the filtration of `B_dR`. As in
`MathlibExt.RepresentationTheory.AdmissibleRepresentation`, the actions are abstract group
actions: no topology on `G` is involved.
-/

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.HodgeTateComparison
open scoped TensorProduct

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p
local notation "𝕥" => logTeichmuller p (untilt_epsilon p)

/-! ### The period `t = log [ε]` -/

/-- The logarithm series is `X g` with `g = 1 + X h`: it has no constant term and its linear
coefficient is `1`. -/
private theorem exists_logSeries_eq_X_mul :
    ∃ g h : PowerSeries 𝔸ₚ, logSeries p = PowerSeries.X * g ∧ g = 1 + PowerSeries.X * h := by
  have h0 : PowerSeries.constantCoeff (logSeries p) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logSeries, PowerSeries.coeff_mk,
      ite_eq_left rfl]
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr h0
  have h1 : PowerSeries.constantCoeff g = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_succ_X_mul, ← hg,
      logSeries, PowerSeries.coeff_mk, ite_eq_right (by omega)]
    norm_num
  obtain ⟨h, hh⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (g - 1) = 0 by rw [map_sub, h1, map_one, sub_self])
  exact ⟨g, h, hg, by linear_combination hh⟩

/-- The value of `X` at `y` is the image of `y` in `B_dR^+`. -/
private theorem evalBDeRhamPlus_X {y : 𝔸ₚ} (hy : y ∈ 𝕀) :
    evalBDeRhamPlus p hy PowerSeries.X = algebraMap 𝔸ₚ 𝔹⁺ y :=
  AdicCompletion.evalPowerSeries_X 𝕀 hy

/-- `θ` vanishes on the image in `B_dR^+` of the kernel of `θ` with `p` inverted. -/
private theorem fontaineThetaBDeRhamPlus_algebraMap_of_mem {y : 𝔸ₚ} (hy : y ∈ 𝕀) :
    fontaineThetaBDeRhamPlus p (algebraMap 𝔸ₚ 𝔹⁺ y) = 0 := by
  rw [fontaineThetaBDeRhamPlus_algebraMap, RingHom.mem_ker.mp hy, map_zero]

/-- **`log(1 + y) = y v` with `θ(v) = 1`**: for `y` in the kernel of `θ` with `p` inverted, there is
`v ∈ B_dR^+` with `log(1 + y) = y v` in `B_dR^+` and `θ(v) = 1`, since `log(1 + X) = X g(X)` with
`g(0) = 1`. -/
theorem exists_logOneAdd_eq_mul {y : 𝔸ₚ} (hy : y ∈ 𝕀) :
    ∃ v : 𝔹⁺, logOneAdd p hy = algebraMap 𝔸ₚ 𝔹⁺ y * v ∧ fontaineThetaBDeRhamPlus p v = 1 := by
  obtain ⟨g, h, hg, hh⟩ := exists_logSeries_eq_X_mul p
  refine ⟨evalBDeRhamPlus p hy g, ?_, ?_⟩
  · rw [logOneAdd, hg, map_mul, evalBDeRhamPlus_X]
  · rw [hh, map_add, map_one, map_mul, evalBDeRhamPlus_X, map_add, map_one, map_mul,
      fontaineThetaBDeRhamPlus_algebraMap_of_mem p hy, zero_mul, add_zero]

/-- **`log [ε] = ([ε] - 1) v` with `θ(v) = 1`**: for `ε` in the tilt of `𝓞_ℂ_[p]` with `ε♯ = 1`,
there is `v ∈ B_dR^+` with `log [ε] = ([ε] - 1) v` in `B_dR^+` and `θ(v) = 1`. -/
theorem exists_logTeichmuller_eq_teichmuller_sub_one_mul {ε : PreTilt 𝓞_ℂ_[p] p}
    (h : ε.untilt = 1) :
    ∃ v : 𝔹⁺, logTeichmuller p h = algebraMap 𝔸 𝔹⁺ (WittVector.teichmuller p ε - 1) * v ∧
      fontaineThetaBDeRhamPlus p v = 1 := by
  obtain ⟨v, hv, hθ⟩ := exists_logOneAdd_eq_mul p (algebraMap_teichmuller_sub_one_mem_ker p h)
  refine ⟨v, ?_, hθ⟩
  rw [logTeichmuller, hv, ← IsScalarTower.algebraMap_apply]

/-- **`t = log [ε]` is a uniformizer of `B_dR^+`** (Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223, Exposé II, §1.5.4 pp. 72–73): for Fontaine's `ε = (1, ζ_p, ζ_{p²}, …)`, `log [ε]` is
an irreducible element of the discrete valuation ring `B_dR^+`, as a unit multiple of the
uniformizer `[ε] - 1`. -/
theorem irreducible_logTeichmuller_epsilon : Irreducible 𝕥 := by
  obtain ⟨v, hv, hθ⟩ := exists_logTeichmuller_eq_teichmuller_sub_one_mul p (untilt_epsilon p)
  have hu : IsUnit v :=
    isUnit_of_fontaineThetaBDeRhamPlus_ne_zero p (by rw [hθ]; exact one_ne_zero)
  rw [hv]
  exact (irreducible_mul_isUnit hu).mpr (irreducible_algebraMap_teichmuller_epsilon_sub_one p)

/-- **`σ(t) = χ(σ) t`** in `B_dR^+`, for `σ ∈ Gal(ℚ̄_p/ℚ_p)`, `t = log [ε]` and the image
`χ(σ) = cyclotomicScalar p σ` in `ℚ_[p]` of the `p`-adic cyclotomic character of `σ`. Indeed
`σ(t) = log [σ(ε)] = a t` for some `a ∈ ℤ_p`, and `σ([ε] - 1) = ([ε] - 1) w` with `θ(w) = χ(σ)`;
writing `t = ([ε] - 1) v` with `θ(v) = 1` gives `w σ(v) = a v`, and applying `θ` gives
`a = χ(σ)`. -/
theorem galoisBDeRhamPlus_logTeichmuller_epsilon (σ : Galois p) :
    galoisBDeRhamPlus p σ 𝕥 = cyclotomicScalar p σ • 𝕥 := by
  obtain ⟨v, hv, hθv⟩ := exists_logTeichmuller_eq_teichmuller_sub_one_mul p (untilt_epsilon p)
  obtain ⟨w, hw, hθw⟩ := exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one p σ
  have h' : (PreTilt.map p (integralGalois p σ).toRingHom (epsilon p)).untilt = 1 := by
    rw [PreTilt.untilt_map, untilt_epsilon, map_one]
  obtain ⟨a, ha⟩ := exists_logTeichmuller_eq_mul p (untilt_epsilon p)
    (isPrimitiveRoot_untilt_frobeniusEquiv_symm_epsilon p) h'
  have hσ := (galoisBDeRhamPlus_logTeichmuller p σ (untilt_epsilon p) h').trans ha
  have hwv : w * galoisBDeRhamPlus p σ v = algebraMap ℚ_[p] 𝔹⁺ (a : ℚ_[p]) * v := by
    refine mul_left_cancel₀ (irreducible_algebraMap_teichmuller_epsilon_sub_one p).ne_zero ?_
    have e := hσ
    rw [hv, map_mul, hw] at e
    linear_combination e
  have hθ := congrArg (fontaineThetaBDeRhamPlus p) hwv
  rw [map_mul, map_mul, fontaineThetaBDeRhamPlus_galoisBDeRhamPlus, hθv, map_one, hθw,
    AlgHom.commutes, mul_one, mul_one] at hθ
  have hχ : cyclotomicScalar p σ = (a : ℚ_[p]) := (algebraMap ℚ_[p] ℂ_[p]).injective hθ
  rw [Algebra.smul_def, hχ]
  exact hσ

/-- The image of `t` in `B_dR` is nonzero. -/
theorem algebraMap_logTeichmuller_epsilon_ne_zero : algebraMap 𝔹⁺ 𝔹 𝕥 ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap_bDeRham_injective p)).2
    (logTeichmuller_ne_zero p _ (epsilon_ne_one p))

/-- `σ(t) = χ(σ) t` in `B_dR`. -/
theorem galoisBDeRham_algebraMap_logTeichmuller_epsilon (σ : Galois p) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 𝕥) = cyclotomicScalar p σ • algebraMap 𝔹⁺ 𝔹 𝕥 := by
  rw [galoisBDeRham_algebraMap, galoisBDeRhamPlus_logTeichmuller_epsilon, Algebra.smul_def,
    map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]

/-- `σ(tⁱ) = χ(σ)ⁱ tⁱ` in `B_dR`, for `i ∈ ℤ`. -/
theorem galoisBDeRham_algebraMap_logTeichmuller_epsilon_zpow (σ : Galois p) (i : ℤ) :
    galoisBDeRham p σ (algebraMap 𝔹⁺ 𝔹 𝕥 ^ i) =
      cyclotomicScalar p σ ^ i • algebraMap 𝔹⁺ 𝔹 𝕥 ^ i := by
  rw [map_zpow₀, galoisBDeRham_algebraMap_logTeichmuller_epsilon, Algebra.smul_def,
    Algebra.smul_def, mul_zpow, map_zpow₀]

/-- **Every nonzero element of `B_dR` is `u tⁿ`** for a unit `u` of `B_dR^+` and `n ∈ ℤ`. -/
theorem exists_eq_units_mul_zpow {x : 𝔹} (hx : x ≠ 0) :
    ∃ (u : 𝔹⁺ˣ) (n : ℤ), x = algebraMap 𝔹⁺ 𝔹 u * algebraMap 𝔹⁺ 𝔹 𝕥 ^ n := by
  have hT := irreducible_logTeichmuller_epsilon p
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective 𝔹⁺ x
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx (by rw [map_zero, zero_div])
  obtain ⟨j, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hT
  obtain ⟨k, ub, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hT
  have hT0 := algebraMap_logTeichmuller_epsilon_ne_zero p
  refine ⟨ua * ub⁻¹, (j : ℤ) - k, ?_⟩
  rw [zpow_sub₀ hT0, zpow_natCast, zpow_natCast]
  simp only [Units.val_mul, map_mul, map_units_inv, map_pow]
  field_simp

/-! ### `B_dR^{G_K} = K` -/

/-- **`B_dR^{G_K} = K`** as `ℚ_[p]`-subalgebras of `B_dR` (Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223, Exposé II, §1.5.7 p. 74): for `K` finite over `ℚ_p` inside `ℚ̄_p`, the
ring of invariants of `Gal(ℚ̄_p/K)` acting on `B_dR` by `galoisBDeRham p` is the image of `K` under
`ℚ̄_p ⊆ B_dR^+ ⊆ B_dR` (`PadicComplexInt.fixedPoints_bDeRham_eq_range`). -/
theorem fixedSubalgebra_galoisBDeRham (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    Representation.fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup =
      ((IsScalarTower.toAlgHom ℚ_[p] 𝔹⁺ 𝔹).comp
        ((padicAlgClToBDeRhamPlus p).comp K.val)).range := by
  ext x
  rw [Representation.mem_fixedSubalgebra, AlgHom.mem_range]
  have h := Set.ext_iff.1 (fixedPoints_bDeRham_eq_range p K) x
  simp only [Set.mem_ofPred_eq, Set.mem_range] at h
  rw [h]
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IntermediateField.coe_val]

/-- **`B_dR^{G_K} ≅ K`**: for `K` finite over `ℚ_p` inside `ℚ̄_p`, the inclusion
`K ⊆ ℚ̄_p ⊆ B_dR^+ ⊆ B_dR` induces an isomorphism of `ℚ_[p]`-algebras from `K` onto the ring of
invariants of `Gal(ℚ̄_p/K)` in `B_dR`. -/
def deRhamFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    K ≃ₐ[ℚ_[p]] Representation.fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup :=
  (AlgEquiv.ofInjective _ (RingHom.injective _)).trans
    (Subalgebra.equivOfEq _ _ (fixedSubalgebra_galoisBDeRham p K).symm)

/-- `deRhamFixedSubalgebraEquiv p K y` is the image of `y` under `ℚ̄_p ⊆ B_dR^+ ⊆ B_dR`. -/
@[simp]
theorem coe_deRhamFixedSubalgebraEquiv (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (y : K) :
    (deRhamFixedSubalgebraEquiv p K y : 𝔹) = algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) :=
  rfl

/-! ### The filtration of `B_dR` -/

/-- **The filtration of `B_dR`** (Fontaine, *Le corps des périodes p-adiques*, Astérisque 223,
Exposé II, §1.5.5 p. 73): `Fil^i B_dR = tⁱ B_dR^+` for `i ∈ ℤ`, the `B_dR^+`-submodule of `B_dR`
spanned by `tⁱ`, where `t = log [ε]` is a uniformizer of `B_dR^+`. Equivalently, `Fil^i B_dR` is
the set of `b ∈ B_dR` of valuation at least `i` (`PadicComplexInt.mem_filBDeRham_iff_le`). -/
def filBDeRham (i : ℤ) : Submodule 𝔹⁺ 𝔹 :=
  Submodule.span 𝔹⁺ {algebraMap 𝔹⁺ 𝔹 𝕥 ^ i}

/-- `x ∈ Fil^i B_dR` if and only if `x = y tⁱ` for some `y ∈ B_dR^+`. -/
theorem mem_filBDeRham {i : ℤ} {x : 𝔹} :
    x ∈ filBDeRham p i ↔ ∃ y : 𝔹⁺, algebraMap 𝔹⁺ 𝔹 y * algebraMap 𝔹⁺ 𝔹 𝕥 ^ i = x := by
  simp only [filBDeRham, Submodule.mem_span_singleton, Algebra.smul_def]

/-- `y tⁱ ∈ Fil^i B_dR` for `y ∈ B_dR^+`. -/
theorem algebraMap_mul_zpow_mem_filBDeRham (i : ℤ) (y : 𝔹⁺) :
    algebraMap 𝔹⁺ 𝔹 y * algebraMap 𝔹⁺ 𝔹 𝕥 ^ i ∈ filBDeRham p i :=
  (mem_filBDeRham p).2 ⟨y, rfl⟩

/-- **`Fil^0 B_dR = B_dR^+`**: the `B_dR^+`-submodule `1` of `B_dR`, the image of `B_dR^+`. -/
theorem filBDeRham_zero : filBDeRham p 0 = 1 := by
  rw [filBDeRham, zpow_zero, ← Submodule.one_eq_span]

/-- `x ∈ Fil^0 B_dR` if and only if `x` lies in the image of `B_dR^+`. -/
theorem mem_filBDeRham_zero {x : 𝔹} : x ∈ filBDeRham p 0 ↔ ∃ y : 𝔹⁺, algebraMap 𝔹⁺ 𝔹 y = x := by
  simp only [mem_filBDeRham, zpow_zero, mul_one]

/-- **The filtration is multiplicative**: `Fil^{i+j} B_dR = Fil^i B_dR · Fil^j B_dR`. -/
theorem filBDeRham_add (i j : ℤ) : filBDeRham p (i + j) = filBDeRham p i * filBDeRham p j := by
  rw [filBDeRham, filBDeRham, filBDeRham, Submodule.span_mul_span, Set.singleton_mul_singleton,
    zpow_add₀ (algebraMap_logTeichmuller_epsilon_ne_zero p)]

/-- **The filtration is decreasing**: `Fil^j B_dR ⊆ Fil^i B_dR` for `i ≤ j`. -/
theorem filBDeRham_antitone : Antitone (filBDeRham p) := by
  intro i j hij x hx
  obtain ⟨n, rfl⟩ := Int.le.dest hij
  obtain ⟨y, rfl⟩ := (mem_filBDeRham p).1 hx
  refine (mem_filBDeRham p).2 ⟨y * 𝕥 ^ n, ?_⟩
  rw [zpow_add₀ (algebraMap_logTeichmuller_epsilon_ne_zero p), zpow_natCast, map_mul, map_pow]
  ring

/-- `u tⁿ ∈ Fil^i B_dR`, for a unit `u` of `B_dR^+`, if and only if `i ≤ n`. -/
theorem units_mul_zpow_mem_filBDeRham_iff (u : 𝔹⁺ˣ) {n i : ℤ} :
    algebraMap 𝔹⁺ 𝔹 u * algebraMap 𝔹⁺ 𝔹 𝕥 ^ n ∈ filBDeRham p i ↔ i ≤ n := by
  refine ⟨fun h => ?_, fun h => filBDeRham_antitone p h
    (algebraMap_mul_zpow_mem_filBDeRham p n u)⟩
  by_contra hlt
  obtain ⟨y, hy⟩ := (mem_filBDeRham p).1 h
  obtain ⟨m, hm⟩ := Int.le.dest (not_le.1 hlt)
  have hT0 := algebraMap_logTeichmuller_epsilon_ne_zero p
  have hu : (u : 𝔹⁺) = y * 𝕥 ^ (m + 1) := by
    refine algebraMap_bDeRham_injective p (mul_right_cancel₀ (zpow_ne_zero n hT0) ?_)
    rw [← hy, ← hm, map_mul, map_pow,
      show n + 1 + (m : ℤ) = n + ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_add₀ hT0,
      zpow_natCast]
    ring
  refine (irreducible_logTeichmuller_epsilon p).not_isUnit (isUnit_of_dvd_unit ?_ u.isUnit)
  exact Dvd.intro_left (y * 𝕥 ^ m) (by rw [hu, pow_succ]; ring)

/-- **`Fil^i B_dR` is the set of elements of valuation at least `i`**: a nonzero `x = u tⁿ ∈ B_dR`,
with `u` a unit of `B_dR^+`, lies in `Fil^i B_dR` if and only if `i ≤ n`. -/
theorem mem_filBDeRham_iff_le {x : 𝔹} {u : 𝔹⁺ˣ} {n : ℤ}
    (hx : x = algebraMap 𝔹⁺ 𝔹 u * algebraMap 𝔹⁺ 𝔹 𝕥 ^ n) (i : ℤ) :
    x ∈ filBDeRham p i ↔ i ≤ n :=
  hx ▸ units_mul_zpow_mem_filBDeRham_iff p u

/-- Every element of `B_dR` lies in some `Fil^i B_dR`. -/
theorem exists_mem_filBDeRham (x : 𝔹) : ∃ i, x ∈ filBDeRham p i := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ zero_mem _⟩
  obtain ⟨u, n, rfl⟩ := exists_eq_units_mul_zpow p hx
  exact ⟨n, algebraMap_mul_zpow_mem_filBDeRham p n u⟩

/-- **The filtration is exhaustive**: `⋃ᵢ Fil^i B_dR = B_dR`. -/
theorem iSup_filBDeRham : ⨆ i, filBDeRham p i = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨i, hi⟩ := exists_mem_filBDeRham p x
  exact Submodule.mem_iSup_of_mem i hi

/-- **The filtration is separated**: `⋂ᵢ Fil^i B_dR = 0`. -/
theorem iInf_filBDeRham : ⨅ i, filBDeRham p i = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Submodule.mem_bot]
  by_contra hx0
  obtain ⟨u, n, rfl⟩ := exists_eq_units_mul_zpow p hx0
  have := (units_mul_zpow_mem_filBDeRham_iff p u).1 ((Submodule.mem_iInf _).1 hx (n + 1))
  omega

/-- **The filtration is stable under `Gal(ℚ̄_p/ℚ_p)`**: `σ(Fil^i B_dR) ⊆ Fil^i B_dR`, since
`σ(y tⁱ) = χ(σ)ⁱ σ(y) tⁱ`. -/
theorem galoisBDeRham_mem_filBDeRham (σ : Galois p) {i : ℤ} {x : 𝔹} (hx : x ∈ filBDeRham p i) :
    galoisBDeRham p σ x ∈ filBDeRham p i := by
  obtain ⟨y, rfl⟩ := (mem_filBDeRham p).1 hx
  refine (mem_filBDeRham p).2 ⟨cyclotomicScalar p σ ^ i • galoisBDeRhamPlus p σ y, ?_⟩
  rw [map_mul, galoisBDeRham_algebraMap, galoisBDeRham_algebraMap_logTeichmuller_epsilon_zpow,
    Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  ring

/-! ### `gr^i B_dR ≅ ℂ_p(i)` -/

/-- **`Fil^i B_dR` as a representation**: the `ℚ_[p]`-linear representation of `Gal(ℚ̄_p/ℚ_p)` on
the `ℚ_[p]`-subspace `Fil^i B_dR` of `B_dR`, by restriction of `galoisBDeRham p`. -/
def filBDeRhamRepresentation (i : ℤ) :
    Representation ℚ_[p] (Galois p) ((filBDeRham p i).restrictScalars ℚ_[p]) :=
  Representation.subrepresentation (AlgHom.toEnd.comp (galoisBDeRhamHom p)) _ fun σ _ hx =>
    galoisBDeRham_mem_filBDeRham p σ hx

/-- `σ` acts on `Fil^i B_dR` by `galoisBDeRham p σ`. -/
@[simp]
theorem coe_filBDeRhamRepresentation_apply (i : ℤ) (σ : Galois p)
    (x : (filBDeRham p i).restrictScalars ℚ_[p]) :
    (filBDeRhamRepresentation p i σ x : 𝔹) = galoisBDeRham p σ x :=
  rfl

/-- **`B_dR^+ ≅ Fil^i B_dR`**: the `ℚ_[p]`-linear isomorphism `y ↦ tⁱ y`. -/
def filBDeRhamEquiv (i : ℤ) : 𝔹⁺ ≃ₗ[ℚ_[p]] (filBDeRham p i).restrictScalars ℚ_[p] :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict ((filBDeRham p i).restrictScalars ℚ_[p])
      (LinearMap.mulRight ℚ_[p] (algebraMap 𝔹⁺ 𝔹 𝕥 ^ i) ∘ₗ
        (IsScalarTower.toAlgHom ℚ_[p] 𝔹⁺ 𝔹).toLinearMap)
      fun y => algebraMap_mul_zpow_mem_filBDeRham p i y)
    ⟨fun y z h => algebraMap_bDeRham_injective p (mul_right_cancel₀
      (zpow_ne_zero i (algebraMap_logTeichmuller_epsilon_ne_zero p)) (congrArg Subtype.val h)),
      fun x => by
        obtain ⟨y, hy⟩ := (mem_filBDeRham p).1 x.2
        exact ⟨y, Subtype.ext hy⟩⟩

/-- `filBDeRhamEquiv p i y = y tⁱ`. -/
@[simp]
theorem coe_filBDeRhamEquiv (i : ℤ) (y : 𝔹⁺) :
    (filBDeRhamEquiv p i y : 𝔹) = algebraMap 𝔹⁺ 𝔹 y * algebraMap 𝔹⁺ 𝔹 𝕥 ^ i :=
  rfl

/-- **The map `θᵢ : Fil^i B_dR → ℂ_p`, `x ↦ θ(t^{-i} x)`**: the `ℚ_[p]`-linear map sending
`y tⁱ` to `θ(y)`, for `y ∈ B_dR^+`. -/
def filBDeRhamTheta (i : ℤ) : (filBDeRham p i).restrictScalars ℚ_[p] →ₗ[ℚ_[p]] ℂ_[p] :=
  (fontaineThetaBDeRhamPlus p).toLinearMap ∘ₗ (filBDeRhamEquiv p i).symm.toLinearMap

/-- `θᵢ(y tⁱ) = θ(y)`. -/
@[simp]
theorem filBDeRhamTheta_filBDeRhamEquiv (i : ℤ) (y : 𝔹⁺) :
    filBDeRhamTheta p i (filBDeRhamEquiv p i y) = fontaineThetaBDeRhamPlus p y := by
  simp [filBDeRhamTheta]

/-- `θᵢ(y tⁱ) = θ(y)`, for `y tⁱ` as an element of `Fil^i B_dR`. -/
theorem filBDeRhamTheta_mk (i : ℤ) (y : 𝔹⁺) (h) :
    filBDeRhamTheta p i ⟨algebraMap 𝔹⁺ 𝔹 y * algebraMap 𝔹⁺ 𝔹 𝕥 ^ i, h⟩ =
      fontaineThetaBDeRhamPlus p y := by
  rw [show (⟨_, h⟩ : (filBDeRham p i).restrictScalars ℚ_[p]) = filBDeRhamEquiv p i y from
    Subtype.ext (coe_filBDeRhamEquiv p i y).symm, filBDeRhamTheta_filBDeRhamEquiv]

/-- `θᵢ : Fil^i B_dR → ℂ_p` is surjective. -/
theorem filBDeRhamTheta_surjective (i : ℤ) : Function.Surjective (filBDeRhamTheta p i) :=
  (fontaineThetaBDeRhamPlus_surjective p).comp (filBDeRhamEquiv p i).symm.surjective

/-- **The kernel of `θᵢ` is `Fil^{i+1} B_dR`**: `θ(t^{-i} x) = 0` if and only if
`x ∈ Fil^{i+1} B_dR`, for `x ∈ Fil^i B_dR`. -/
theorem filBDeRhamTheta_eq_zero_iff {i : ℤ} (x : (filBDeRham p i).restrictScalars ℚ_[p]) :
    filBDeRhamTheta p i x = 0 ↔ (x : 𝔹) ∈ filBDeRham p (i + 1) := by
  obtain ⟨y, rfl⟩ := (filBDeRhamEquiv p i).surjective x
  have hT0 := algebraMap_logTeichmuller_epsilon_ne_zero p
  rw [filBDeRhamTheta_filBDeRhamEquiv, ← RingHom.mem_ker,
    ker_fontaineThetaBDeRhamPlus_eq_maximalIdeal,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1
      (irreducible_logTeichmuller_epsilon p), Ideal.mem_span_singleton', coe_filBDeRhamEquiv,
    mem_filBDeRham]
  refine exists_congr fun z => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← h, map_mul, zpow_add₀ hT0, zpow_one]
    ring
  · refine algebraMap_bDeRham_injective p (mul_right_cancel₀ (zpow_ne_zero i hT0) ?_)
    rw [← h, map_mul, zpow_add₀ hT0, zpow_one]
    ring

/-- **`θᵢ` is equivariant for the action on `ℂ_p(i)`**: `θᵢ(σ x) = χ(σ)ⁱ σ(θᵢ x)` for
`x ∈ Fil^i B_dR` and `σ ∈ Gal(ℚ̄_p/ℚ_p)`, with `χ(σ) = cyclotomicScalar p σ`. -/
theorem filBDeRhamTheta_filBDeRhamRepresentation (i : ℤ) (σ : Galois p)
    (x : (filBDeRham p i).restrictScalars ℚ_[p]) :
    filBDeRhamTheta p i (filBDeRhamRepresentation p i σ x) =
      cyclotomicScalar p σ ^ i • completionGalois p σ (filBDeRhamTheta p i x) := by
  obtain ⟨y, rfl⟩ := (filBDeRhamEquiv p i).surjective x
  have h : filBDeRhamRepresentation p i σ (filBDeRhamEquiv p i y) =
      filBDeRhamEquiv p i (cyclotomicScalar p σ ^ i • galoisBDeRhamPlus p σ y) := by
    refine Subtype.ext ?_
    rw [coe_filBDeRhamRepresentation_apply, coe_filBDeRhamEquiv, coe_filBDeRhamEquiv, map_mul,
      galoisBDeRham_algebraMap, galoisBDeRham_algebraMap_logTeichmuller_epsilon_zpow,
      Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  rw [h, filBDeRhamTheta_filBDeRhamEquiv, filBDeRhamTheta_filBDeRhamEquiv, map_smul,
    fontaineThetaBDeRhamPlus_galoisBDeRhamPlus]

/-- `Fil^{i+1} B_dR`, as a `ℚ_[p]`-subspace of `Fil^i B_dR`. -/
abbrev filBDeRhamSucc (i : ℤ) : Submodule ℚ_[p] ((filBDeRham p i).restrictScalars ℚ_[p]) :=
  ((filBDeRham p (i + 1)).restrictScalars ℚ_[p]).comap
    ((filBDeRham p i).restrictScalars ℚ_[p]).subtype

/-- **`gr^i B_dR = Fil^i B_dR / Fil^{i+1} B_dR`**, as a `ℚ_[p]`-vector space. -/
abbrev grBDeRham (i : ℤ) : Type :=
  (filBDeRham p i).restrictScalars ℚ_[p] ⧸ filBDeRhamSucc p i

/-- **The action of `Gal(ℚ̄_p/ℚ_p)` on `gr^i B_dR`**, induced by its action on `Fil^i B_dR`
(Fontaine, *Le corps des périodes p-adiques*, Astérisque 223, Exposé II, §1.5.7 p. 74). -/
def grBDeRhamRepresentation (i : ℤ) : Representation ℚ_[p] (Galois p) (grBDeRham p i) :=
  (filBDeRhamRepresentation p i).quotient (filBDeRhamSucc p i) fun σ _ hx =>
    galoisBDeRham_mem_filBDeRham p σ hx

/-- The kernel of `θᵢ` is `Fil^{i+1} B_dR`, as subspaces of `Fil^i B_dR`. -/
theorem filBDeRhamSucc_eq_ker (i : ℤ) :
    filBDeRhamSucc p i = LinearMap.ker (filBDeRhamTheta p i) := by
  ext x
  rw [LinearMap.mem_ker, filBDeRhamTheta_eq_zero_iff]
  rfl

/-- **`gr^i B_dR ≅ ℂ_p(i)` as representations of `Gal(ℚ̄_p/ℚ_p)`** (Fontaine, *Le corps des
périodes p-adiques*, Astérisque 223, Exposé II, §1.5.5 p. 73 and §1.5.7 p. 74): the map
`x ↦ θ(t^{-i} x)` induces an isomorphism from `gr^i B_dR`, with the action induced by
`galoisBDeRham p`, onto `ℂ_p(i)`, the Tate twist of `ℂ_p` with its action
`PadicComplex.galoisAlgHom p`, on which `σ` acts by `c ↦ χ(σ)ⁱ σ(c)`. -/
def grBDeRhamEquiv (i : ℤ) :
    (grBDeRhamRepresentation p i).Equiv
      (Representation.tateTwist (AlgHom.toEnd.comp (PadicComplex.galoisAlgHom p)) i) :=
  Representation.Equiv.mk
    ((Submodule.quotEquivOfEq _ _ (filBDeRhamSucc_eq_ker p i)).trans
      (LinearMap.quotKerEquivOfSurjective _ (filBDeRhamTheta_surjective p i)))
    fun σ => by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        LinearEquiv.coe_coe, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
        LinearMap.quotKerEquivOfSurjective_apply_mk, grBDeRhamRepresentation,
        Representation.tateTwist_apply, LinearMap.smul_apply, MonoidHom.coe_comp,
        AlgHom.toEnd_apply, AlgHom.toLinearMap_apply, PadicComplex.galoisAlgHom_apply]
      exact filBDeRhamTheta_filBDeRhamRepresentation p i σ x

/-- `gr^i B_dR ≅ ℂ_p(i)` sends the class of `x ∈ Fil^i B_dR` to `θᵢ(x) = θ(t^{-i} x)`. -/
@[simp]
theorem grBDeRhamEquiv_mk (i : ℤ) (x : (filBDeRham p i).restrictScalars ℚ_[p]) :
    grBDeRhamEquiv p i (Submodule.Quotient.mk x) = filBDeRhamTheta p i x :=
  rfl

/-! ### `Fil^i B_dR ⊗ V` -/

/-- `Fil^j B_dR ⊆ Fil^i B_dR` for `i ≤ j`, as `ℚ_[p]`-subspaces. -/
theorem restrictScalars_filBDeRham_le {i j : ℤ} (h : i ≤ j) :
    (filBDeRham p j).restrictScalars ℚ_[p] ≤ (filBDeRham p i).restrictScalars ℚ_[p] :=
  fun _ hx => filBDeRham_antitone p h hx

/-- `Fil^i B_dR` is decreasing in `i`, as `ℚ_[p]`-subspaces of `B_dR`. -/
theorem restrictScalars_filBDeRham_antitone :
    Antitone fun i => (filBDeRham p i).restrictScalars ℚ_[p] :=
  fun _ _ h => restrictScalars_filBDeRham_le p h

/-- **`Fil^i B_dR` is separated**, in the form used by `Representation.periodsFiltration`: an
element of every `Fil^i B_dR` is `0`. -/
theorem eq_zero_of_forall_mem_filBDeRham (x : 𝔹)
    (hx : ∀ i, x ∈ (filBDeRham p i).restrictScalars ℚ_[p]) : x = 0 := by
  have h : x ∈ ⨅ i, filBDeRham p i := (Submodule.mem_iInf _).2 hx
  rwa [iInf_filBDeRham, Submodule.mem_bot] at h

/-- **`Fil^i B_dR` is stable under multiplication by `B_dR^{G_K} = K`** for `K` finite over `ℚ_p`
inside `ℚ̄_p`, since `K ⊆ B_dR^+`. -/
theorem fixedSubalgebra_mul_mem_filBDeRham (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (i : ℤ) :
    ∀ c ∈ Representation.fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup,
      ∀ x ∈ (filBDeRham p i).restrictScalars ℚ_[p],
        c * x ∈ (filBDeRham p i).restrictScalars ℚ_[p] := by
  intro c hc x hx
  rw [fixedSubalgebra_galoisBDeRham p K] at hc
  obtain ⟨y, rfl⟩ := hc
  change algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) * x ∈
    (filBDeRham p i).restrictScalars ℚ_[p]
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem (filBDeRham p i) _ hx

variable (V : Type*) [AddCommGroup V] [Module ℚ_[p] V]

/-- **`Fil^i B_dR ⊗_{ℚ_p} V` inside `B_dR ⊗_{ℚ_p} V`**: the image of the injective map
`Fil^i B_dR ⊗_{ℚ_p} V → B_dR ⊗_{ℚ_p} V` (`PadicComplexInt.rTensor_filBDeRham_injective`). -/
def filBDeRhamTensor (i : ℤ) : Submodule ℚ_[p] (𝔹 ⊗[ℚ_[p]] V) :=
  LinearMap.range (LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype)

/-- The map `Fil^i B_dR ⊗_{ℚ_p} V → B_dR ⊗_{ℚ_p} V` is injective, `V` being flat over `ℚ_p`. -/
theorem rTensor_filBDeRham_injective (i : ℤ) :
    Function.Injective (LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

/-- The map `Fil^j B_dR ⊗ V → B_dR ⊗ V` factors through `Fil^i B_dR ⊗ V` for `i ≤ j`. -/
theorem rTensor_filBDeRham_subtype_comp_inclusion {i j : ℤ} (h : i ≤ j) :
    LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype ∘ₗ
        LinearMap.rTensor V (Submodule.inclusion (restrictScalars_filBDeRham_le p h)) =
      LinearMap.rTensor V ((filBDeRham p j).restrictScalars ℚ_[p]).subtype := by
  rw [← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion]

/-- The isomorphism `Fil^i B_dR ⊗_{ℚ_p} V ≃ Fil^i B_dR ⊗ V ⊆ B_dR ⊗_{ℚ_p} V`. -/
def filBDeRhamTensorEquiv (i : ℤ) :
    ((filBDeRham p i).restrictScalars ℚ_[p]) ⊗[ℚ_[p]] V ≃ₗ[ℚ_[p]] filBDeRhamTensor p V i :=
  LinearEquiv.ofInjective _ (rTensor_filBDeRham_injective p V i)

/-- `filBDeRhamTensorEquiv p V i y` is the image of `y` in `B_dR ⊗_{ℚ_p} V`. -/
@[simp]
theorem coe_filBDeRhamTensorEquiv (i : ℤ)
    (y : ((filBDeRham p i).restrictScalars ℚ_[p]) ⊗[ℚ_[p]] V) :
    (filBDeRhamTensorEquiv p V i y : 𝔹 ⊗[ℚ_[p]] V) =
      LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype y :=
  rfl

/-- **The map `θᵢ ⊗ V : Fil^i B_dR ⊗ V → ℂ_p ⊗_{ℚ_p} V`**, `x ⊗ v ↦ θ(t^{-i} x) ⊗ v`. -/
def filBDeRhamTensorTheta (i : ℤ) : filBDeRhamTensor p V i →ₗ[ℚ_[p]] ℂ_[p] ⊗[ℚ_[p]] V :=
  LinearMap.rTensor V (filBDeRhamTheta p i) ∘ₗ (filBDeRhamTensorEquiv p V i).symm.toLinearMap

/-- `(θᵢ ⊗ V)(x ⊗ v) = θᵢ(x) ⊗ v`, on the image of `y ∈ Fil^i B_dR ⊗_{ℚ_p} V`. -/
theorem filBDeRhamTensorTheta_filBDeRhamTensorEquiv (i : ℤ)
    (y : ((filBDeRham p i).restrictScalars ℚ_[p]) ⊗[ℚ_[p]] V) :
    filBDeRhamTensorTheta p V i (filBDeRhamTensorEquiv p V i y) =
      LinearMap.rTensor V (filBDeRhamTheta p i) y := by
  simp only [filBDeRhamTensorTheta, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The pair `Fil^{i+1} B_dR → Fil^i B_dR → ℂ_p` (inclusion and `θᵢ`) is exact. -/
theorem exact_inclusion_filBDeRhamTheta (i : ℤ) :
    Function.Exact (Submodule.inclusion (restrictScalars_filBDeRham_le p (Int.le_add_one le_rfl)))
      (filBDeRhamTheta p i) := fun x =>
  (filBDeRhamTheta_eq_zero_iff p x).trans
    ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-- **The kernel of `θᵢ ⊗ V` is `Fil^{i+1} B_dR ⊗ V`**, by the right exactness of `⊗ V`. -/
theorem filBDeRhamTensorTheta_eq_zero_iff {i : ℤ} (z : filBDeRhamTensor p V i) :
    filBDeRhamTensorTheta p V i z = 0 ↔ (z : 𝔹 ⊗[ℚ_[p]] V) ∈ filBDeRhamTensor p V (i + 1) := by
  obtain ⟨y, rfl⟩ := (filBDeRhamTensorEquiv p V i).surjective z
  have hex := rTensor_exact V (exact_inclusion_filBDeRhamTheta p i)
    (filBDeRhamTheta_surjective p i)
  have hcomp := rTensor_filBDeRham_subtype_comp_inclusion p V (Int.le_add_one (le_refl i))
  rw [filBDeRhamTensorTheta_filBDeRhamTensorEquiv, hex y, coe_filBDeRhamTensorEquiv]
  constructor
  · rintro ⟨y', rfl⟩
    exact ⟨y', (LinearMap.congr_fun hcomp y').symm⟩
  · rintro ⟨y', hy'⟩
    refine ⟨y', rTensor_filBDeRham_injective p V i ?_⟩
    rw [← hy', ← LinearMap.congr_fun hcomp y', LinearMap.comp_apply]

/-- `σ ⊗ ρ(σ)` maps `Fil^i B_dR ⊗ V` to itself, through `σ|_{Fil^i} ⊗ ρ(σ)`. -/
theorem map_rTensor_filBDeRham (ρ : Representation ℚ_[p] (Galois p) V) (σ : Galois p) (i : ℤ)
    (y : ((filBDeRham p i).restrictScalars ℚ_[p]) ⊗[ℚ_[p]] V) :
    TensorProduct.map (galoisBDeRham p σ).toLinearMap (ρ σ)
        (LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype y) =
      LinearMap.rTensor V ((filBDeRham p i).restrictScalars ℚ_[p]).subtype
        (TensorProduct.map (filBDeRhamRepresentation p i σ) (ρ σ) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul f v =>
    rw [LinearMap.rTensor_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.rTensor_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `θᵢ ⊗ V` intertwines `σ|_{Fil^i} ⊗ ρ(σ)` with the action `χ(σ)ⁱ σ ⊗ ρ(σ)` on
`ℂ_p(i) ⊗_{ℚ_p} V`. -/
theorem rTensor_filBDeRhamTheta_map (ρ : Representation ℚ_[p] (Galois p) V) (σ : Galois p)
    (i : ℤ) (y : ((filBDeRham p i).restrictScalars ℚ_[p]) ⊗[ℚ_[p]] V) :
    LinearMap.rTensor V (filBDeRhamTheta p i)
        (TensorProduct.map (filBDeRhamRepresentation p i σ) (ρ σ) y) =
      cyclotomicScalar p σ ^ i • TensorProduct.map (completionGalois p σ).toLinearMap (ρ σ)
        (LinearMap.rTensor V (filBDeRhamTheta p i) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul f v =>
    rw [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.map_tmul, filBDeRhamTheta_filBDeRhamRepresentation, TensorProduct.smul_tmul',
      AlgEquiv.toLinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

end PadicComplexInt

/-! ### The filtration of `D_dR(V)` -/

namespace Representation

open PadicComplexInt

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Galois p) V) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-- **The filtration of `D_dR(V)`** (Fontaine, *Représentations p-adiques semi-stables*,
Astérisque 223, Exposé III, §3.7 p. 141): for a representation `ρ` of `Gal(ℚ̄_p/ℚ_p)` on `V`, `K`
finite over `ℚ_p` inside `ℚ̄_p` and `i ∈ ℤ`, `Fil^i D_dR(V) = (Fil^i B_dR ⊗_{ℚ_p} V)^{G_K}`: the
elements of `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}` lying in the image of `Fil^i B_dR ⊗_{ℚ_p} V`
(`Representation.periodsFiltration` for the filtration `PadicComplexInt.filBDeRham`), a subspace
over `B_dR^{G_K} = K` (`PadicComplexInt.deRhamFixedSubalgebraEquiv`). -/
abbrev deRhamFiltration (i : ℤ) :
    Submodule (fixedSubalgebra 𝔹 (galoisBDeRham p) K.fixingSubgroup) (𝔹 ⊗[ℚ_[p]] V) :=
  ρ.periodsFiltration (galoisBDeRham p) K.fixingSubgroup
    (fun i => (filBDeRham p i).restrictScalars ℚ_[p]) (fixedSubalgebra_mul_mem_filBDeRham p K) i

/-- **`gr^i D_dR(V) = Fil^i D_dR(V) / Fil^{i+1} D_dR(V)`**, a vector space over
`B_dR^{G_K} = K` (`Representation.periodsGraded`). -/
abbrev deRhamGraded (i : ℤ) : Type _ :=
  ρ.periodsGraded (galoisBDeRham p) K.fixingSubgroup
    (fun i => (filBDeRham p i).restrictScalars ℚ_[p]) (fixedSubalgebra_mul_mem_filBDeRham p K) i

/-- `x ∈ Fil^i D_dR(V)` if and only if `x ∈ D_dR(V)` and `x` lies in the image of
`Fil^i B_dR ⊗_{ℚ_p} V`. -/
theorem mem_deRhamFiltration {i : ℤ} {x : 𝔹 ⊗[ℚ_[p]] V} :
    x ∈ ρ.deRhamFiltration K i ↔
      x ∈ ρ.periods (galoisBDeRham p) K.fixingSubgroup ∧ x ∈ filBDeRhamTensor p V i :=
  Iff.rfl

/-- `Fil^i D_dR(V) ⊆ D_dR(V)`. -/
theorem deRhamFiltration_le_periods (i : ℤ) :
    ρ.deRhamFiltration K i ≤ ρ.periods (galoisBDeRham p) K.fixingSubgroup :=
  ρ.periodsFiltration_le_periods _ _ _ _ i

/-- **The filtration of `D_dR(V)` is decreasing.** -/
theorem deRhamFiltration_antitone : Antitone (ρ.deRhamFiltration K) :=
  ρ.periodsFiltration_antitone _ _ _ _ (restrictScalars_filBDeRham_antitone p)

omit [FiniteDimensional ℚ_[p] K] in
/-- For `x ∈ D_dR(V)` lying in `Fil^i B_dR ⊗ V`, `(θᵢ ⊗ V)(x)` lies in
`(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`: if `x` is the image of `y ∈ Fil^i B_dR ⊗ V`, then `y` is fixed by
`σ|_{Fil^i} ⊗ ρ(σ)` for `σ ∈ G_K`, and `θᵢ ⊗ V` intertwines this action with that on
`ℂ_p(i) ⊗ V`. -/
theorem filBDeRhamTensorTheta_mem_twistPeriods {i : ℤ} {x : 𝔹 ⊗[ℚ_[p]] V}
    (hx : x ∈ ρ.periods (galoisBDeRham p) K.fixingSubgroup)
    (hx' : x ∈ filBDeRhamTensor p V i) :
    filBDeRhamTensorTheta p V i ⟨x, hx'⟩ ∈ ρ.twistPeriods K i := by
  obtain ⟨y, hy⟩ := (filBDeRhamTensorEquiv p V i).surjective ⟨x, hx'⟩
  rw [← hy, filBDeRhamTensorTheta_filBDeRhamTensorEquiv, mem_twistPeriods]
  intro σ hσ
  have hfix : TensorProduct.map (filBDeRhamRepresentation p i σ) (ρ σ) y = y := by
    refine rTensor_filBDeRham_injective p V i ?_
    rw [← map_rTensor_filBDeRham, ← coe_filBDeRhamTensorEquiv, hy]
    exact mem_periods.1 hx σ hσ
  rw [← rTensor_filBDeRhamTheta_map, hfix]

/-- **The map `Fil^i D_dR(V) → (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`** induced by `θᵢ : Fil^i B_dR → ℂ_p(i)`,
`x ↦ θ(t^{-i} x)`: the restriction of `θᵢ ⊗ V` (`PadicComplexInt.filBDeRhamTensorTheta`). -/
def deRhamFiltrationToTwistPeriods (i : ℤ) :
    ρ.deRhamFiltration K i →ₗ[ℚ_[p]] ρ.twistPeriods K i where
  toFun x := ⟨filBDeRhamTensorTheta p V i ⟨x, x.2.2⟩,
    filBDeRhamTensorTheta_mem_twistPeriods ρ K x.2.1 x.2.2⟩
  map_add' x y := Subtype.ext (map_add (filBDeRhamTensorTheta p V i) ⟨_, x.2.2⟩ ⟨_, y.2.2⟩)
  map_smul' c x := Subtype.ext (map_smul (filBDeRhamTensorTheta p V i) c ⟨_, x.2.2⟩)

/-- `deRhamFiltrationToTwistPeriods ρ K i x` is `(θᵢ ⊗ V)(x)`. -/
theorem coe_deRhamFiltrationToTwistPeriods (i : ℤ) (x : ρ.deRhamFiltration K i) :
    (deRhamFiltrationToTwistPeriods ρ K i x : ℂ_[p] ⊗[ℚ_[p]] V) =
      filBDeRhamTensorTheta p V i ⟨x, x.2.2⟩ :=
  rfl

/-- **The kernel of `Fil^i D_dR(V) → (ℂ_p(i) ⊗ V)^{G_K}` is `Fil^{i+1} D_dR(V)`.** -/
theorem deRhamFiltrationToTwistPeriods_eq_zero_iff {i : ℤ} (x : ρ.deRhamFiltration K i) :
    deRhamFiltrationToTwistPeriods ρ K i x = 0 ↔
      (x : 𝔹 ⊗[ℚ_[p]] V) ∈ ρ.deRhamFiltration K (i + 1) := by
  rw [← Subtype.coe_inj, coe_deRhamFiltrationToTwistPeriods, ZeroMemClass.coe_zero,
    filBDeRhamTensorTheta_eq_zero_iff]
  exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩

/-- **The inclusion `gr^i D_dR(V) → (ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`** (Fontaine, *Représentations
p-adiques semi-stables*, Astérisque 223, Exposé III, §3.7 p. 142): the `ℚ_[p]`-linear map induced by
`Fil^i D_dR(V) → (ℂ_p(i) ⊗ V)^{G_K}`, `x ↦ (θᵢ ⊗ V)(x)`, whose kernel is `Fil^{i+1} D_dR(V)`. It is
injective (`Representation.deRhamGradedToTwistPeriods_injective`). -/
def deRhamGradedToTwistPeriods (i : ℤ) : ρ.deRhamGraded K i →ₗ[ℚ_[p]] ρ.twistPeriods K i :=
  ρ.periodsGradedLift _ _ _ _ (deRhamFiltrationToTwistPeriods ρ K i)
    fun x hx => (deRhamFiltrationToTwistPeriods_eq_zero_iff ρ K x).2 hx

/-- The map `gr^i D_dR(V) → (ℂ_p(i) ⊗ V)^{G_K}` sends the class of `x ∈ Fil^i D_dR(V)` to
`(θᵢ ⊗ V)(x)`. -/
@[simp]
theorem deRhamGradedToTwistPeriods_periodsGradedMk (i : ℤ) (x : ρ.deRhamFiltration K i) :
    deRhamGradedToTwistPeriods ρ K i (ρ.periodsGradedMk _ _ _ _ i x) =
      deRhamFiltrationToTwistPeriods ρ K i x :=
  rfl

/-- **`gr^i D_dR(V)` embeds in `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_K}`**: the map
`Representation.deRhamGradedToTwistPeriods` is injective. -/
theorem deRhamGradedToTwistPeriods_injective (i : ℤ) :
    Function.Injective (deRhamGradedToTwistPeriods ρ K i) :=
  periodsGradedLift_injective _ _ fun x => (deRhamFiltrationToTwistPeriods_eq_zero_iff ρ K x).1

end Representation
