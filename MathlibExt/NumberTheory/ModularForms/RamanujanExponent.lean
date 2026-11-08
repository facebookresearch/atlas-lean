/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local-exponent framework toward the GL2 Ramanujan exponent
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import MathlibExt.NumberTheory.NumberField.Place
public import MathlibExt.NumberTheory.ModularForms.SelbergSpectralGap

@[expose] public section

open scoped MatrixGroups NumberField

namespace MathlibExt.NumberTheory.RamanujanExponent

open MathlibExt.NumberTheory.SelbergSpectralGap

/-!
# Local-exponent framework toward the GL2 Ramanujan exponent

For a cuspidal automorphic representation `π` of `GL₂` over a number
field and a place `v`, the Langlands classification produces a local
exponent `m(π, v) ∈ [0, 1/2]`. Catalogue constant C56a is
`δ₂ = sup_{π,v} m(π, v)`, equivalently the least admissible exponent in
Hypothesis `H₂(δ)`.

Mathlib does not yet have cuspidal automorphic representations,
parabolic induction, the Langlands classification, or Satake parameters.
This file therefore formalizes the numerical layer for an explicitly
supplied family of local exponents, together with the one archimedean
anchor currently available in this repository: exceptional eigenvalues
for congruence subgroups, through `SelbergSpectralGap.selbergConstant`.

It deliberately does not define a fixed real by taking a supremum over
all values of an arbitrary exponent structure. Such a structure could be
manufactured with exponent `1/2`, making the resulting constant an
artifact and the Kim--Sarnak/Blomer--Brumley bound `7/64` false for the
model. A fixed `δ₂` should be introduced only when the index family is
the genuine family of cuspidal local components.

Source: Optimization Problems, `constants/56a.md`, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`.
-/

/-- A family of local Langlands exponents, indexed by an arbitrary type
of local components. The two fields record the pointwise range
`0 ≤ m ≤ 1/2`; the upper bound is the Jacquet--Shalika range for genuine
cuspidal data. The index type is part of the data, so this is an
exponent-of-a-family construction rather than a purported fixed `δ₂`. -/
structure LocalExponentFamily (ι : Type*) where
  exponent : ι → ℝ
  exponent_nonneg : ∀ i, 0 ≤ exponent i
  exponent_le_half : ∀ i, exponent i ≤ 1 / 2

/-- The set of exponents occurring in a family, with `0` adjoined. The
adjoined zero makes the supremum the correct value for an empty family
and for the tempered case. -/
def exponentSet {ι : Type*} (F : LocalExponentFamily ι) : Set ℝ :=
  {0} ∪ Set.range F.exponent

/-- The Ramanujan exponent of an explicitly supplied local-exponent
family: the supremum of its local exponents. For the eventual genuine
family of cuspidal local components this will be catalogue constant
`δ₂`; for other families the name records the construction, not an
identification. -/
noncomputable def ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) : ℝ :=
  sSup (exponentSet F)

/-- Hypothesis `H₂(δ)` for one explicit family: every local exponent is
at most `δ`. -/
def IsAdmissible {ι : Type*} (F : LocalExponentFamily ι) (δ : ℝ) : Prop :=
  ∀ i, F.exponent i ≤ δ

/-- The Generalized Ramanujan conclusion for one explicit family: every
local exponent is zero. -/
def GeneralizedRamanujanFor {ι : Type*}
    (F : LocalExponentFamily ι) : Prop :=
  ∀ i, F.exponent i = 0

theorem exponentSet_nonempty {ι : Type*} (F : LocalExponentFamily ι) :
    (exponentSet F).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem exponentSet_bddAbove {ι : Type*} (F : LocalExponentFamily ι) :
    BddAbove (exponentSet F) := by
  refine ⟨1 / 2, ?_⟩
  rintro y (rfl | ⟨i, rfl⟩)
  · norm_num
  · exact F.exponent_le_half i

theorem zero_le_ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) : 0 ≤ ramanujanExponentOf F :=
  le_csSup (exponentSet_bddAbove F) (Or.inl rfl)

theorem ramanujanExponentOf_le_half {ι : Type*}
    (F : LocalExponentFamily ι) : ramanujanExponentOf F ≤ 1 / 2 := by
  apply csSup_le (exponentSet_nonempty F)
  rintro y (rfl | ⟨i, rfl⟩)
  · norm_num
  · exact F.exponent_le_half i

/-- Every local exponent is bounded by the family's Ramanujan exponent. -/
theorem exponent_le_ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) (i : ι) :
    F.exponent i ≤ ramanujanExponentOf F :=
  le_csSup (exponentSet_bddAbove F) (Or.inr ⟨i, rfl⟩)

/-- The family's Ramanujan exponent is itself admissible. -/
theorem isAdmissible_ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) :
    IsAdmissible F (ramanujanExponentOf F) :=
  fun i => exponent_le_ramanujanExponentOf F i

/-- Every admissible nonnegative exponent bounds the family's Ramanujan
exponent. -/
theorem ramanujanExponentOf_le_of_isAdmissible {ι : Type*}
    (F : LocalExponentFamily ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : IsAdmissible F δ) : ramanujanExponentOf F ≤ δ := by
  apply csSup_le (exponentSet_nonempty F)
  rintro y (rfl | ⟨i, rfl⟩)
  · exact hδ
  · exact h i

/-- For nonnegative `δ`, admissibility is exactly the bound by the
family's Ramanujan exponent. -/
theorem isAdmissible_iff_ramanujanExponentOf_le {ι : Type*}
    (F : LocalExponentFamily ι) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsAdmissible F δ ↔ ramanujanExponentOf F ≤ δ :=
  ⟨ramanujanExponentOf_le_of_isAdmissible F hδ,
    fun h i => (exponent_le_ramanujanExponentOf F i).trans h⟩

/-- The exponent of a family vanishes exactly in the tempered case. -/
theorem ramanujanExponentOf_eq_zero_iff {ι : Type*}
    (F : LocalExponentFamily ι) :
    ramanujanExponentOf F = 0 ↔ GeneralizedRamanujanFor F := by
  constructor
  · intro h i
    refine le_antisymm ?_ (F.exponent_nonneg i)
    rw [← h]
    exact exponent_le_ramanujanExponentOf F i
  · intro h
    refine le_antisymm ?_ (zero_le_ramanujanExponentOf F)
    apply ramanujanExponentOf_le_of_isAdmissible F le_rfl
    intro i
    rw [h i]

/-- The admissible nonnegative exponents for a family. -/
def admissibleExponents {ι : Type*} (F : LocalExponentFamily ι) : Set ℝ :=
  {δ | 0 ≤ δ ∧ IsAdmissible F δ}

/-- The supremum definition agrees with the infimum-of-admissible
exponents formulation of Hypothesis `H₂(δ)`. -/
theorem ramanujanExponentOf_eq_sInf_admissibleExponents {ι : Type*}
    (F : LocalExponentFamily ι) :
    ramanujanExponentOf F = sInf (admissibleExponents F) := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨1 / 2, by norm_num, F.exponent_le_half⟩
    · intro δ hδ
      exact ramanujanExponentOf_le_of_isAdmissible F hδ.1 hδ.2
  · apply csInf_le
    · exact ⟨0, fun δ hδ => hδ.1⟩
    · exact ⟨zero_le_ramanujanExponentOf F,
        isAdmissible_ramanujanExponentOf F⟩

/-- A pair of complex numbers is in arithmetic Satake normalization with
local exponent `t` at residue cardinality `N` when `|αβ| = 1` and the two
magnitudes are `N^t` and `N^{-t}`. -/
def IsSatakePair (N t : ℝ) (α β : ℂ) : Prop :=
  ‖α * β‖ = 1 ∧ ‖α‖ = N ^ t ∧ ‖β‖ = N ^ (-t)

/-- The Hecke eigenvalue bound forced by one Satake pair. The catalogue
also records the sharper expression `N^δ + N^{-δ}`; the bound proved
here is its displayed consequence `2N^δ`. -/
theorem hecke_norm_le_two_mul_rpow_of_isSatakePair {N t δ : ℝ}
    {α β : ℂ} (hN : 1 ≤ N) (ht0 : 0 ≤ t) (ht : t ≤ δ)
    (h : IsSatakePair N t α β) : ‖α + β‖ ≤ 2 * N ^ δ := by
  calc
    ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
    _ = N ^ t + N ^ (-t) := by rw [h.2.1, h.2.2]
    _ ≤ N ^ δ + N ^ δ :=
      add_le_add
        (Real.rpow_le_rpow_of_exponent_le hN ht)
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    _ = 2 * N ^ δ := by ring

/-- The Satake Hecke bound at an actual finite place, with
`N = N(v)` supplied by the residue norm. -/
theorem hecke_norm_le_two_mul_residueNorm_rpow_of_isSatakePair
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {t δ : ℝ}
    {α β : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ δ)
    (h : IsSatakePair v.residueNorm t α β) :
    ‖α + β‖ ≤ 2 * v.residueNorm ^ δ :=
  hecke_norm_le_two_mul_rpow_of_isSatakePair
    v.one_le_residueNorm ht0 ht h

/-- An exceptional-eigenvalue witness in the Selberg provider: a
congruence subgroup and an eigenvalue in `(0, 1/4)`. Morally, these are
archimedean local components over `ℚ`; the identification with genuine
cuspidal automorphic local components is part of the Selberg provider's
recorded model scope. -/
def SelbergWitness : Type :=
  {x : Subgroup SL(2, ℤ) × ℝ // IsCongruenceSubgroup x.1 ∧
    IsEigenvalue x.1 x.2 ∧ 0 < x.2 ∧ x.2 < 1 / 4}

/-- The archimedean local exponent forced by an exceptional eigenvalue:
if `λ = 1/4 - θ²`, this is `θ = √(1/4 - λ)`. -/
noncomputable def selbergGap (w : SelbergWitness) : ℝ :=
  Real.sqrt (1 / 4 - w.1.2)

/-- The canonical family of Selberg archimedean exponents. -/
noncomputable def selbergFamily : LocalExponentFamily SelbergWitness where
  exponent := selbergGap
  exponent_nonneg := fun w => Real.sqrt_nonneg _
  exponent_le_half := by
    intro w
    apply le_half_of_mem_exceptionalGaps
    exact Or.inr ⟨w.1.2, w.2.2.1, w.2.2.2.1, w.2.2.2.2, rfl⟩

/-- A local-exponent family dominates the Selberg archimedean slice when
every exceptional-eigenvalue gap occurs as one of its local exponents.
This is the precise anchor needed for the comparison with Selberg's
constant; it is a hypothesis on a proposed genuine family, not a
definition of one. -/
def DominatesSelberg {ι : Type*} (F : LocalExponentFamily ι) : Prop :=
  ∀ w : SelbergWitness, ∃ i, selbergGap w = F.exponent i

theorem dominatesSelberg_selbergFamily :
    DominatesSelberg selbergFamily :=
  fun w => ⟨w, rfl⟩

/-- An exceptional eigenvalue bounds every Selberg-dominating family's
exponent from below. -/
theorem sqrt_le_ramanujanExponentOf_of_dominatesSelberg {ι : Type*}
    (F : LocalExponentFamily ι) (hdom : DominatesSelberg F)
    {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ) {lam : ℝ}
    (hlam : IsEigenvalue Γ lam) (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ ramanujanExponentOf F := by
  obtain ⟨i, hi⟩ := hdom ⟨⟨Γ, lam⟩, hΓ, hlam, hpos, hlt⟩
  calc
    Real.sqrt (1 / 4 - lam) = F.exponent i := hi
    _ ≤ ramanujanExponentOf F := exponent_le_ramanujanExponentOf F i

/-- Selberg's constant is at most the exponent of every
Selberg-dominating family. For the genuine cuspidal family this is the
archimedean comparison `C₆₁ ≤ δ₂`; it is not an equality of constants. -/
theorem selbergConstant_le_of_dominatesSelberg {ι : Type*}
    (F : LocalExponentFamily ι) (hdom : DominatesSelberg F) :
    selbergConstant ≤ ramanujanExponentOf F := by
  apply csSup_le selbergGaps_nonempty
  rintro y ⟨Γ, hΓ, rfl⟩
  apply csSup_le (exceptionalGaps_nonempty Γ)
  intro t ht
  rcases ht with rfl | ⟨lam, hlam, hpos, hlt, rfl⟩
  · exact zero_le_ramanujanExponentOf F
  · exact sqrt_le_ramanujanExponentOf_of_dominatesSelberg
      F hdom hΓ hlam hpos hlt

/-- The canonical Selberg family's exponent is exactly Selberg's
constant. This identifies the currently anchored archimedean slice; it
does not identify that slice with the full Ramanujan exponent. -/
theorem ramanujanExponentOf_selbergFamily :
    ramanujanExponentOf selbergFamily = selbergConstant := by
  apply le_antisymm
  · apply ramanujanExponentOf_le_of_isAdmissible
      selbergFamily zero_le_selbergConstant
    intro w
    exact sqrt_le_selbergConstant w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2
  · exact selbergConstant_le_of_dominatesSelberg
      selbergFamily dominatesSelberg_selbergFamily

end MathlibExt.NumberTheory.RamanujanExponent
