/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/G9/KerTheta.lean`,
`ZInQKernel/Contrib/G9/BdREmb.lean`, `ZInQKernel/Contrib/G9/I4Layer.lean` and
`ZInQKernel/OneProof/H/LPrefix.lean` (https://github.com/Deicyde/diophantine-z-q), compared with
the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingBasic
public import MathlibExt.RingTheory.Perfectoid.FontaineThetaKernel
public import MathlibExt.RingTheory.Perfectoid.Functoriality
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# The de Rham period ring of `ℂ_p`

Let `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` be Mathlib's de Rham period ring of `ℂ_p`: the completion
of `W(𝓞_ℂ_[p]♭)[1/p]` along the kernel of Fontaine's map `θ` with `p` inverted, and let
`B_dR = BDeRham 𝓞_ℂ_[p] p`. Write `ξ = p - [p♭]` (`PadicComplexInt.xi`), which generates the
kernel of `θ` (`PadicComplexInt.ker_fontaineTheta_eq_span_xi`). We show:

* `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]` and `θ[1/p]` are surjective, and the kernel of `θ[1/p]` is a
  maximal ideal of `W(𝓞_ℂ_[p]♭)[1/p]`;
* `B_dR^+` is a complete discrete valuation ring with uniformizer `ξ`
  (`PadicComplexInt.isDiscreteValuationRing_bDeRhamPlus`,
  `PadicComplexInt.maximalIdeal_bDeRhamPlus`);
* `B_dR` is the localization of `B_dR^+` away from `ξ` and its fraction field, hence a field
  (`PadicComplexInt.instFieldBDeRham`);
* `θ` extends to a surjective `ℚ_[p]`-algebra map `θ : B_dR^+ → ℂ_[p]` with kernel `(ξ)`
  (`PadicComplexInt.fontaineThetaBDeRhamPlus`), for the `ℚ_[p]`-algebra structure of `B_dR^+`
  coming from `ℤ_[p] = W(𝔽_p) → W(𝓞_ℂ_[p]♭)`.

These are the properties of `B_dR^+` and `B_dR` stated in J.-M. Fontaine, *Le corps des
périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.1–1.5.2 p. 71 and §1.5.5 p. 73, and
the first two items of the TODO list of `Mathlib.RingTheory.Perfectoid.BDeRham` for
`R = 𝓞_ℂ_[p]`.

## Main definitions

* `PadicComplexInt.padicToLocalizationAway`: the ring map `ℚ_[p] → W(𝓞_ℂ_[p]♭)[1/p]`, which
  makes `W(𝓞_ℂ_[p]♭)[1/p]`, `B_dR^+` and `B_dR` into `ℚ_[p]`-algebras.
* `PadicComplexInt.localizationAwayEquiv`: `𝓞_ℂ_[p][1/p] ≃ ℂ_[p]`.
* `PadicComplexInt.fontaineThetaBDeRhamPlus`: Fontaine's map `θ : B_dR^+ → ℂ_[p]`.
-/

@[expose] public noncomputable section

open Ideal WittVector

/-! ### `B_dR^+` as a `W(R♭)`-algebra -/

namespace BDeRhamPlus

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R]

/-- The `W(R♭)`-algebra structure of `B_dR^+(R)`, through `W(R♭) → W(R♭)[1/p] → B_dR^+(R)`. -/
instance instAlgebraWittVector : Algebra (WittVector p (PreTilt R p)) (BDeRhamPlus R p) :=
  inferInstanceAs (Algebra _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) _))

/-- The map `W(R♭) → B_dR^+(R)` is the composite of `W(R♭) → W(R♭)[1/p]` and
`W(R♭)[1/p] → B_dR^+(R)`. -/
instance isScalarTower_wittVector :
    IsScalarTower (WittVector p (PreTilt R p))
      (Localization.Away (p : WittVector p (PreTilt R p))) (BDeRhamPlus R p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end BDeRhamPlus

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝕀" => RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-! ### Surjectivity of `θ` -/

/-- The Frobenius of `𝓞_ℂ_[p] ⧸ p` is surjective, since every element of `ℂ_[p]` has a `p`-th
root. -/
theorem frobenius_modP_surjective : Function.Surjective (frobenius (ModP 𝓞_ℂ_[p] p) p) := by
  intro x
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x' : ℂ_[p]) hp.out.pos
  have hy1 : ‖y‖ ≤ 1 := by
    have h := norm_le_one p x'
    rw [← hy, norm_pow] at h
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).mp h
  refine ⟨Ideal.Quotient.mk _ ⟨y, (mem_iff_norm_le_one p _).mpr hy1⟩, ?_⟩
  rw [_root_.frobenius_def, ← map_pow]
  congr 1
  exact Subtype.ext (by simpa using hy)

/-- Fontaine's map `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]` is surjective. -/
theorem fontaineTheta_surjective : Function.Surjective (fontaineTheta 𝓞_ℂ_[p] p) :=
  surjective_fontaineTheta (frobenius_modP_surjective p)

/-- `𝓞_ℂ_[p][1/p]` is a fraction field of `𝓞_ℂ_[p]`. -/
instance isFractionRing_localizationAway :
    IsFractionRing 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) := by
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (p : 𝓞_ℂ_[p])) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    fun x hx => ?_
  have hx0 : (x : ℂ_[p]) ≠ 0 := fun h0 => nonZeroDivisors.ne_zero hx (Subtype.ext h0)
  obtain ⟨m, hm⟩ :=
    exists_pow_lt_of_lt_one (norm_pos_iff.mpr hx0) (PadicComplex.norm_p_lt_one p)
  have hc : ‖(p : ℂ_[p]) ^ m / (x : ℂ_[p])‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hm.le (norm_nonneg _)
  refine ⟨(p : 𝓞_ℂ_[p]) ^ m, ⟨m, rfl⟩,
    ⟨⟨(p : ℂ_[p]) ^ m / (x : ℂ_[p]), (mem_iff_norm_le_one p _).mpr hc⟩, ?_⟩⟩
  apply Subtype.ext
  have hp' : ((p : 𝓞_ℂ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := rfl
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, hp']
  field_simp

/-- The isomorphism `𝓞_ℂ_[p][1/p] ≃ ℂ_[p]` of fraction fields of `𝓞_ℂ_[p]`. -/
def localizationAwayEquiv : Localization.Away (p : 𝓞_ℂ_[p]) ≃ₐ[𝓞_ℂ_[p]] ℂ_[p] :=
  IsLocalization.algEquiv (nonZeroDivisors 𝓞_ℂ_[p]) _ _

/-- `localizationAwayEquiv p` maps the image of `x ∈ 𝓞_ℂ_[p]` to `x`. -/
@[simp]
theorem localizationAwayEquiv_algebraMap (x : 𝓞_ℂ_[p]) :
    localizationAwayEquiv p (algebraMap _ _ x) = (x : ℂ_[p]) :=
  (localizationAwayEquiv p).commutes x

/-- Fontaine's map with `p` inverted, `θ : W(𝓞_ℂ_[p]♭)[1/p] → 𝓞_ℂ_[p][1/p]`, is surjective. -/
theorem fontaineThetaInvertP_surjective :
    Function.Surjective (fontaineThetaInvertP 𝓞_ℂ_[p] p) := by
  intro t
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (p : 𝓞_ℂ_[p])) t
  obtain ⟨w, rfl⟩ := fontaineTheta_surjective p r
  refine ⟨IsLocalization.mk' _ w (⟨(p : 𝔸) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝔸)), ?_⟩
  have hu : IsUnit (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) ((p : 𝓞_ℂ_[p]) ^ n)) :=
    IsLocalization.map_units _ (⟨(p : 𝓞_ℂ_[p]) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝓞_ℂ_[p]))
  apply hu.mul_right_cancel
  have h1 := IsLocalization.mk'_spec 𝔸ₚ w (⟨(p : 𝔸) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝔸))
  have h2 := IsLocalization.mk'_spec (Localization.Away (p : 𝓞_ℂ_[p]))
    (fontaineTheta 𝓞_ℂ_[p] p w) (⟨(p : 𝓞_ℂ_[p]) ^ n, n, rfl⟩ : Submonoid.powers (p : 𝓞_ℂ_[p]))
  dsimp only at h1 h2
  rw [h2]
  have h3 := congrArg (fontaineThetaInvertP 𝓞_ℂ_[p] p) h1
  rw [map_mul, fontaineThetaInvertP_algebraMap, fontaineThetaInvertP_algebraMap, map_pow,
    map_natCast] at h3
  exact h3

/-- The kernel of Fontaine's map with `p` inverted is a maximal ideal of
`W(𝓞_ℂ_[p]♭)[1/p]`. -/
instance isMaximal_ker_fontaineThetaInvertP :
    (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)).IsMaximal := by
  let _ : Field (Localization.Away (p : 𝓞_ℂ_[p])) := IsFractionRing.toField 𝓞_ℂ_[p]
  exact RingHom.ker_isMaximal_of_surjective _ (fontaineThetaInvertP_surjective p)

/-! ### `B_dR^+` is a discrete valuation ring with uniformizer `ξ` -/

/-- The kernel of `θ` with `p` inverted is finitely generated. -/
private theorem ker_fg : (𝕀).FG :=
  ⟨{algebraMap 𝔸 𝔸ₚ (xi p)}, by rw [Finset.coe_singleton, ker_fontaineThetaInvertP_eq_span_xi]⟩

/-- The image of `ξ` in `W(𝓞_ℂ_[p]♭)[1/p]` is nonzero. -/
private theorem algebraMap_localizationAway_xi_ne_zero : algebraMap 𝔸 𝔸ₚ (xi p) ≠ 0 := fun h =>
  xi_ne_zero p (IsLocalization.injective (M := Submonoid.powers (p : 𝔸)) 𝔸ₚ
    (powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_ne_zero p _))
    (h.trans (map_zero _).symm))

/-- The kernel of `θ` with `p` inverted generates the ideal `(ξ)` of `B_dR^+`. -/
theorem map_ker_fontaineThetaInvertP :
    Ideal.map (algebraMap 𝔸ₚ 𝔹⁺) 𝕀 = span {algebraMap 𝔸 𝔹⁺ (xi p)} := by
  rw [ker_fontaineThetaInvertP_eq_span_xi, Ideal.map_span, Set.image_singleton,
    ← IsScalarTower.algebraMap_apply]

/-- No power of the image of `ξ` in `B_dR^+` vanishes. -/
theorem algebraMap_xi_pow_ne_zero (n : ℕ) : algebraMap 𝔸 𝔹⁺ (xi p) ^ n ≠ 0 := by
  intro h
  have h1 : AdicCompletion.evalₐ 𝕀 (n + 1)
      (AdicCompletion.of 𝕀 𝔸ₚ (algebraMap 𝔸 𝔸ₚ (xi p) ^ n)) = 0 := by
    have e : AdicCompletion.of 𝕀 𝔸ₚ (algebraMap 𝔸 𝔸ₚ (xi p) ^ n) =
        algebraMap 𝔸 𝔹⁺ (xi p) ^ n := by
      rw [IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺, ← map_pow (algebraMap 𝔸ₚ 𝔹⁺)]
      rfl
    rw [e, h]
    exact map_zero _
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem,
    ker_fontaineThetaInvertP_pow_eq_span_xi_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : c * algebraMap 𝔸 𝔸ₚ (xi p) = 1 := by
    have : algebraMap 𝔸 𝔸ₚ (xi p) ^ n * (c * algebraMap 𝔸 𝔸ₚ (xi p) - 1) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero n (algebraMap_localizationAway_xi_ne_zero p))
    · exact sub_eq_zero.mp h
  apply (isMaximal_ker_fontaineThetaInvertP p).ne_top
  rw [ker_fontaineThetaInvertP_eq_span_xi, Ideal.span_singleton_eq_top]
  exact isUnit_iff_exists_inv.mpr ⟨c, by rw [mul_comm]; exact h2⟩

/-- The image of `ξ` in `B_dR^+` is nonzero. -/
theorem algebraMap_xi_ne_zero : algebraMap 𝔸 𝔹⁺ (xi p) ≠ 0 := by
  simpa using algebraMap_xi_pow_ne_zero p 1

/-- `B_dR^+` is `ξ`-adically complete. -/
instance isAdicComplete_bDeRhamPlus : IsAdicComplete (span {algebraMap 𝔸 𝔹⁺ (xi p)}) 𝔹⁺ := by
  rw [← map_ker_fontaineThetaInvertP]
  exact AdicCompletion.isAdicComplete_self _ (ker_fg p)

/-- The ideal `(ξ)` of `B_dR^+` is maximal. -/
instance isMaximal_span_xi : (span {algebraMap 𝔸 𝔹⁺ (xi p)} : Ideal 𝔹⁺).IsMaximal := by
  rw [← map_ker_fontaineThetaInvertP]
  exact AdicCompletion.isMaximal_map_of_le _ _ le_rfl (ker_fg p)

/-- `B_dR^+` is a local ring. -/
instance isLocalRing_bDeRhamPlus : IsLocalRing 𝔹⁺ :=
  isLocalRing_of_isAdicComplete_maximal (span {algebraMap 𝔸 𝔹⁺ (xi p)})

/-- The maximal ideal of `B_dR^+` is `(ξ)`. -/
theorem maximalIdeal_bDeRhamPlus :
    IsLocalRing.maximalIdeal 𝔹⁺ = span {algebraMap 𝔸 𝔹⁺ (xi p)} :=
  (IsLocalRing.eq_maximalIdeal (isMaximal_span_xi p)).symm

/-- Every nonzero element of `B_dR^+` is a power of `ξ` times a unit. -/
theorem exists_eq_xi_pow_mul_unit {x : 𝔹⁺} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝔹⁺ˣ), x = algebraMap 𝔸 𝔹⁺ (xi p) ^ n * u := by
  set ϖ := algebraMap 𝔸 𝔹⁺ (xi p)
  have hex : ∃ n, x ∉ (span {ϖ ^ n} : Ideal 𝔹⁺) := by
    by_contra hcon
    push Not at hcon
    apply hx
    apply IsHausdorff.haus' (I := (span {ϖ} : Ideal 𝔹⁺)) x
    intro n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hcon n
  classical
  obtain ⟨N, hN, hmin⟩ : ∃ N, x ∉ (span {ϖ ^ N} : Ideal 𝔹⁺) ∧
      ∀ m < N, x ∈ (span {ϖ ^ m} : Ideal 𝔹⁺) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := by
    refine Nat.exists_eq_add_one_of_ne_zero fun h0 => hN ?_
    rw [h0, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (hmin M M.lt_succ_self)
  have hu' : IsUnit u := by
    by_contra hnu
    have : u ∈ IsLocalRing.maximalIdeal 𝔹⁺ := hnu
    rw [maximalIdeal_bDeRhamPlus] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    exact hN (Ideal.mem_span_singleton'.mpr ⟨c, by rw [← hu, ← hc]; ring⟩)
  exact ⟨M, hu'.unit, by rw [IsUnit.unit_spec, ← hu, mul_comm]⟩

/-- `B_dR^+` is an integral domain. -/
instance isDomain_bDeRhamPlus : IsDomain 𝔹⁺ := by
  have : NoZeroDivisors 𝔹⁺ := ⟨fun {x y} hxy => by
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    rcases eq_or_ne y 0 with hy | hy
    · exact Or.inr hy
    obtain ⟨a, u, rfl⟩ := exists_eq_xi_pow_mul_unit p hx
    obtain ⟨b, v, rfl⟩ := exists_eq_xi_pow_mul_unit p hy
    refine absurd ?_ (algebraMap_xi_pow_ne_zero p (a + b))
    rw [← (u * v).isUnit.mul_left_eq_zero, ← hxy, Units.val_mul, pow_add]
    ring⟩
  exact NoZeroDivisors.to_isDomain _

/-- **`B_dR^+` is a discrete valuation ring.** -/
instance isDiscreteValuationRing_bDeRhamPlus : IsDiscreteValuationRing 𝔹⁺ := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap 𝔸 𝔹⁺ (xi p), ?_, fun {x} hx => ?_⟩
  · exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (algebraMap_xi_ne_zero p) (maximalIdeal_bDeRhamPlus p)
  · obtain ⟨n, u, rfl⟩ := exists_eq_xi_pow_mul_unit p hx
    exact ⟨n, u, rfl⟩

/-- The image of `ξ` is a uniformizer of `B_dR^+`. -/
theorem irreducible_algebraMap_xi : Irreducible (algebraMap 𝔸 𝔹⁺ (xi p)) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ (algebraMap_xi_ne_zero p)
    (maximalIdeal_bDeRhamPlus p)

/-! ### `B_dR` is the fraction field of `B_dR^+` -/

/-- `B_dR = B_dR^+[1/ξ]`: Mathlib's `BDeRham 𝓞_ℂ_[p] p`, which inverts all the generators of the
kernel of `θ`, is the localization of `B_dR^+` away from `ξ`. -/
theorem isLocalization_away_xi : IsLocalization.Away (algebraMap 𝔸 𝔹⁺ (xi p)) 𝔹 := by
  have hk := ker_fontaineThetaInvertP_eq_span_xi p
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (algebraMap 𝔸 𝔹⁺ (xi p)))
    (BDeRham.submonoid 𝓞_ℂ_[p] p) ?_ fun n hn => ?_).mpr inferInstance
  · rw [Submonoid.powers_le, IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺]
    exact BDeRham.algebraMap_mem_submonoid p hk
  induction hn using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have : algebraMap 𝔸 𝔸ₚ (xi p) ∈ span {a} := by
      rw [← (show 𝕀 = span {a} from ha), hk]
      exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨_, ⟨1, rfl⟩, ?_⟩
    change algebraMap 𝔸ₚ 𝔹⁺ a ∣ algebraMap 𝔸 𝔹⁺ (xi p) ^ 1
    rw [pow_one, IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺, ← hc, map_mul]
    exact dvd_mul_left _ _
  | one => exact ⟨1, Submonoid.one_mem _, one_dvd _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hy
    refine ⟨_, ⟨i + j, rfl⟩, ?_⟩
    change x * y ∣ algebraMap 𝔸 𝔹⁺ (xi p) ^ (i + j)
    rw [pow_add]
    exact mul_dvd_mul hi hj

/-- `B_dR` is a fraction field of `B_dR^+`. -/
instance isFractionRing_bDeRham : IsFractionRing 𝔹⁺ 𝔹 := by
  have := isLocalization_away_xi p
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (algebraMap 𝔸 𝔹⁺ (xi p))) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (algebraMap_xi_ne_zero p)) fun n hn => ?_
  obtain ⟨k, u, rfl⟩ := exists_eq_xi_pow_mul_unit p (nonZeroDivisors.ne_zero hn)
  exact ⟨_, ⟨k, rfl⟩, Units.mul_right_dvd.mpr dvd_rfl⟩

/-- **`B_dR` is a field**: the field structure of the fraction field of the discrete valuation
ring `B_dR^+`. -/
instance instFieldBDeRham : Field 𝔹 := IsFractionRing.toField 𝔹⁺

/-- The map `B_dR^+ → B_dR` is injective. -/
theorem algebraMap_bDeRham_injective : Function.Injective (algebraMap 𝔹⁺ 𝔹) :=
  IsFractionRing.injective 𝔹⁺ 𝔹

/-! ### The `ℚ_[p]`-algebra structures -/

/-- The map `ℤ_[p] → W(𝓞_ℂ_[p]♭)` is fixed by the map of Witt vectors induced by any ring map of
the tilt. -/
@[simp]
theorem map_padicIntToAinf (f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p) (z : ℤ_[p]) :
    WittVector.map f (padicIntToAinf p z) = padicIntToAinf p z := by
  ext n
  simp only [padicIntToAinf, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) _)) _

/-- The ring map `ℚ_[p] → W(𝓞_ℂ_[p]♭)[1/p]` extending `ℤ_[p] → W(𝓞_ℂ_[p]♭)`: `ℚ_[p]` is the
fraction field of `ℤ_[p]`, and every nonzero element of `ℤ_[p]` is a unit times a power of `p`,
which becomes a unit in `W(𝓞_ℂ_[p]♭)[1/p]`. -/
def padicToLocalizationAway : ℚ_[p] →+* 𝔸ₚ :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p])
    (g := (algebraMap 𝔸 𝔸ₚ).comp (padicIntToAinf p)) fun x => by
      obtain ⟨x, hx⟩ := x
      have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
      change IsUnit (((algebraMap 𝔸 𝔸ₚ).comp (padicIntToAinf p)) x)
      rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast]
      refine ((PadicInt.unitCoeff hx0).isUnit.map _).mul (IsUnit.pow _ ?_)
      simpa using IsLocalization.Away.algebraMap_isUnit (p : 𝔸)

/-- `padicToLocalizationAway p` extends `ℤ_[p] → W(𝓞_ℂ_[p]♭)`. -/
@[simp]
theorem padicToLocalizationAway_coe (z : ℤ_[p]) :
    padicToLocalizationAway p (z : ℚ_[p]) = algebraMap 𝔸 𝔸ₚ (padicIntToAinf p z) :=
  IsLocalization.lift_eq _ z

/-- The `ℚ_[p]`-algebra structure of `W(𝓞_ℂ_[p]♭)[1/p]`, through
`padicToLocalizationAway p`. -/
instance instAlgebraPadicLocalizationAway : Algebra ℚ_[p] 𝔸ₚ :=
  (padicToLocalizationAway p).toAlgebra

/-- The `ℚ_[p]`-algebra structure of `B_dR^+`, through `W(𝓞_ℂ_[p]♭)[1/p]`. -/
instance instAlgebraPadicBDeRhamPlus : Algebra ℚ_[p] 𝔹⁺ :=
  inferInstanceAs (Algebra ℚ_[p] (AdicCompletion 𝕀 𝔸ₚ))

/-- The map `ℚ_[p] → B_dR^+` factors through `W(𝓞_ℂ_[p]♭)[1/p]`. -/
instance isScalarTower_padic_localizationAway : IsScalarTower ℚ_[p] 𝔸ₚ 𝔹⁺ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The `ℚ_[p]`-algebra structure of `B_dR`, through `B_dR^+`. -/
instance instAlgebraPadicBDeRham : Algebra ℚ_[p] 𝔹 :=
  ((algebraMap 𝔹⁺ 𝔹).comp (algebraMap ℚ_[p] 𝔹⁺)).toAlgebra

/-- The map `ℚ_[p] → B_dR` factors through `B_dR^+`. -/
instance isScalarTower_padic_bDeRhamPlus : IsScalarTower ℚ_[p] 𝔹⁺ 𝔹 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! ### Fontaine's map `θ` on `B_dR^+` -/

/-- `θ` maps the image of `z ∈ ℤ_[p]` in `W(𝓞_ℂ_[p]♭)` to `z`: the two ring maps
`ℤ_[p] → ℂ_[p]` agree on the natural numbers and take values of norm at most `1`, and the natural
numbers are dense in `ℤ_[p]`. -/
private theorem fontaineTheta_padicIntToAinf (z : ℤ_[p]) :
    ((fontaineTheta 𝓞_ℂ_[p] p (padicIntToAinf p z) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] z := by
  set g₁ : ℤ_[p] →+* ℂ_[p] :=
    (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp ((fontaineTheta 𝓞_ℂ_[p] p).comp (padicIntToAinf p))
  set g₂ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  change g₁ z = g₂ z
  have hb₁ (w : ℤ_[p]) : ‖g₁ w‖ ≤ 1 := norm_le_one p _
  have hb₂ (w : ℤ_[p]) : ‖g₂ w‖ ≤ 1 := by
    change ‖algebraMap ℚ_[p] ℂ_[p] (w : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact PadicInt.norm_le_one w
  by_contra hne
  have hd : 0 < ‖g₁ z - g₂ z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hd) (PadicComplex.norm_p_lt_one p)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = ((z.appr n : ℕ) : ℤ_[p]) + w * (p : ℤ_[p]) ^ n := by
    rw [hw]
    ring
  have hdiff : g₁ z - g₂ z = (g₁ w - g₂ w) * (p : ℂ_[p]) ^ n := by
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  have hle : ‖g₁ z - g₂ z‖ ≤ 2 * ‖(p : ℂ_[p])‖ ^ n := by
    rw [hdiff, norm_mul, norm_pow]
    have : ‖g₁ w - g₂ w‖ ≤ 2 :=
      calc ‖g₁ w - g₂ w‖ ≤ ‖g₁ w‖ + ‖g₂ w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hb₁ w) (hb₂ w)
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

/-- The ring map underlying Fontaine's map `θ : B_dR^+ → ℂ_[p]`. -/
private def fontaineThetaAux : 𝔹⁺ →+* ℂ_[p] :=
  (localizationAwayEquiv p).toRingEquiv.toRingHom.comp
    ((RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p)).toRingHom.comp
      (AdicCompletion.evalOneₐ 𝕀).toRingHom)

/-- The ring map underlying `θ : B_dR^+ → ℂ_[p]` extends `θ` with `p` inverted. -/
private theorem fontaineThetaAux_algebraMap (x : 𝔸ₚ) :
    fontaineThetaAux p (algebraMap 𝔸ₚ 𝔹⁺ x) =
      localizationAwayEquiv p (fontaineThetaInvertP 𝓞_ℂ_[p] p x) :=
  rfl

/-- The ring map underlying `θ : B_dR^+ → ℂ_[p]` is `ℚ_[p]`-linear. -/
private theorem fontaineThetaAux_comp_algebraMap :
    (fontaineThetaAux p).comp (algebraMap ℚ_[p] 𝔹⁺) = algebraMap ℚ_[p] ℂ_[p] := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun z => ?_)
  change fontaineThetaAux p (algebraMap 𝔸ₚ 𝔹⁺ (padicToLocalizationAway p z)) =
    algebraMap ℚ_[p] ℂ_[p] z
  rw [padicToLocalizationAway_coe, fontaineThetaAux_algebraMap, fontaineThetaInvertP_algebraMap,
    localizationAwayEquiv_algebraMap]
  exact fontaineTheta_padicIntToAinf p z

/-- **Fontaine's map `θ : B_dR^+ → ℂ_[p]`**: the reduction of `B_dR^+` modulo the kernel of `θ`
with `p` inverted, followed by the isomorphisms
`W(𝓞_ℂ_[p]♭)[1/p] ⧸ ker θ ≃ 𝓞_ℂ_[p][1/p] ≃ ℂ_[p]` induced by `θ`. It is a `ℚ_[p]`-algebra
map. -/
def fontaineThetaBDeRhamPlus : 𝔹⁺ →ₐ[ℚ_[p]] ℂ_[p] :=
  { (localizationAwayEquiv p).toRingEquiv.toRingHom.comp
      ((RingHom.quotientKerEquivOfSurjective (fontaineThetaInvertP_surjective p)).toRingHom.comp
        (AdicCompletion.evalOneₐ 𝕀).toRingHom) with
    commutes' := by exact RingHom.congr_fun (fontaineThetaAux_comp_algebraMap p) }

/-- On the image of `x ∈ W(𝓞_ℂ_[p]♭)[1/p]`, `θ` is `θ x ∈ 𝓞_ℂ_[p][1/p] ≃ ℂ_[p]`. -/
theorem fontaineThetaBDeRhamPlus_algebraMap (x : 𝔸ₚ) :
    fontaineThetaBDeRhamPlus p (algebraMap 𝔸ₚ 𝔹⁺ x) =
      localizationAwayEquiv p (fontaineThetaInvertP 𝓞_ℂ_[p] p x) :=
  fontaineThetaAux_algebraMap p x

/-- On the image of `w ∈ W(𝓞_ℂ_[p]♭)`, `θ` is `θ w ∈ 𝓞_ℂ_[p] ⊆ ℂ_[p]`. -/
@[simp]
theorem fontaineThetaBDeRhamPlus_algebraMap_wittVector (w : 𝔸) :
    fontaineThetaBDeRhamPlus p (algebraMap 𝔸 𝔹⁺ w) = (fontaineTheta 𝓞_ℂ_[p] p w : ℂ_[p]) := by
  rw [IsScalarTower.algebraMap_apply 𝔸 𝔸ₚ 𝔹⁺, fontaineThetaBDeRhamPlus_algebraMap,
    fontaineThetaInvertP_algebraMap, localizationAwayEquiv_algebraMap]

/-- `θ : B_dR^+ → ℂ_[p]` is surjective. -/
theorem fontaineThetaBDeRhamPlus_surjective : Function.Surjective (fontaineThetaBDeRhamPlus p) := by
  intro y
  obtain ⟨t, rfl⟩ := (localizationAwayEquiv p).surjective y
  obtain ⟨x, rfl⟩ := fontaineThetaInvertP_surjective p t
  exact ⟨algebraMap 𝔸ₚ 𝔹⁺ x, fontaineThetaBDeRhamPlus_algebraMap p x⟩

/-- The kernel of `θ : B_dR^+ → ℂ_[p]` is `(ξ)`. -/
theorem ker_fontaineThetaBDeRhamPlus :
    RingHom.ker (fontaineThetaBDeRhamPlus p) = span {algebraMap 𝔸 𝔹⁺ (xi p)} := by
  have h : RingHom.ker (fontaineThetaBDeRhamPlus p) =
      RingHom.ker (AdicCompletion.evalOneₐ 𝕀).toRingHom := by
    ext x
    exact (_root_.map_eq_zero_iff (localizationAwayEquiv p) (AlgEquiv.injective _)).trans
      (_root_.map_eq_zero_iff (RingHom.quotientKerEquivOfSurjective
        (fontaineThetaInvertP_surjective p)) (RingEquiv.injective _))
  rw [h, AdicCompletion.ker_evalOneₐ_eq_map _ (ker_fg p)]
  exact map_ker_fontaineThetaInvertP p

/-- The kernel of `θ : B_dR^+ → ℂ_[p]` is the maximal ideal of `B_dR^+`. -/
theorem ker_fontaineThetaBDeRhamPlus_eq_maximalIdeal :
    RingHom.ker (fontaineThetaBDeRhamPlus p) = IsLocalRing.maximalIdeal 𝔹⁺ := by
  rw [ker_fontaineThetaBDeRhamPlus, maximalIdeal_bDeRhamPlus]

/-- An element of `B_dR^+` whose image under `θ` is nonzero is a unit. -/
theorem isUnit_of_fontaineThetaBDeRhamPlus_ne_zero {x : 𝔹⁺}
    (hx : fontaineThetaBDeRhamPlus p x ≠ 0) : IsUnit x := by
  by_contra h
  have hm : x ∈ IsLocalRing.maximalIdeal 𝔹⁺ := h
  rw [← ker_fontaineThetaBDeRhamPlus_eq_maximalIdeal] at hm
  exact hx hm

end PadicComplexInt
