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

/-- **Family of local exponents.** A local-exponent family indexed by a type $\iota$ is a function
$m : \iota \to \mathbb{R}$, the local Langlands exponents, with $0 \le m(i) \le 1/2$ for every
$i \in \iota$.

The upper bound $1/2$ is the Jacquet--Shalika range for genuine cuspidal data. The index type is
part of the data, so the exponent of such a family is a construction attached to the family, not
a definition of the fixed Ramanujan exponent $\delta_2$ of $\mathrm{GL}_2$. -/
structure LocalExponentFamily (ι : Type*) where
  exponent : ι → ℝ
  exponent_nonneg : ∀ i, 0 ≤ exponent i
  exponent_le_half : ∀ i, exponent i ≤ 1 / 2

/-- **Exponent set of a local-exponent family.** For a local-exponent family $F$ indexed by a type
$\iota$, with local exponents $m(i)$ for $i \in \iota$, the exponent set of $F$ is the set of real
numbers $\{0\} \cup \{m(i) : i \in \iota\}$.

The adjoined $0$ makes the supremum of this set the correct value when $\iota$ is empty and in the
tempered case, where every local exponent is $0$. -/
def exponentSet {ι : Type*} (F : LocalExponentFamily ι) : Set ℝ :=
  {0} ∪ Set.range F.exponent

/-- **Ramanujan exponent of a local-exponent family.** The Ramanujan exponent of a local-exponent
family $F$ with local exponents $m(i)$, $i \in \iota$, is the supremum of the set
$\{0\} \cup \{m(i) : i \in \iota\}$. It is the supremum of the local exponents when $\iota$ is
nonempty, and $0$ when $\iota$ is empty.

For the eventual genuine family of cuspidal local components of $\mathrm{GL}_2$ this will be the
Ramanujan exponent $\delta_2$; for other families it is only the supremum of the given
exponents. -/
noncomputable def ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) : ℝ :=
  sSup (exponentSet F)

/-- **Admissibility of an exponent for a local-exponent family.** A local-exponent family $F$ is
admissible at a real number $\delta$ (Hypothesis $H_2(\delta)$ for $F$) when every local exponent
$m_i$ of $F$ ($i \in \iota$) is at most $\delta$. -/
def IsAdmissible {ι : Type*} (F : LocalExponentFamily ι) (δ : ℝ) : Prop :=
  ∀ i, F.exponent i ≤ δ

/-- **Generalized Ramanujan conjecture for a family.** A local-exponent family $F$ satisfies the
Generalized Ramanujan conclusion when every local exponent $m_i$ of $F$ ($i \in \iota$) is zero. -/
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

/-- **Local exponents are bounded by the Ramanujan exponent.** For every local-exponent family $F$
and every index $i$, the local exponent $m_i$ of $F$ at $i$ is at most the Ramanujan exponent of
$F$. -/
theorem exponent_le_ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) (i : ι) :
    F.exponent i ≤ ramanujanExponentOf F :=
  le_csSup (exponentSet_bddAbove F) (Or.inr ⟨i, rfl⟩)

/-- **The Ramanujan exponent is admissible.** For every local-exponent family $F$, $F$ is admissible
at its Ramanujan exponent: every local exponent of $F$ is at most the Ramanujan exponent of $F$. -/
theorem isAdmissible_ramanujanExponentOf {ι : Type*}
    (F : LocalExponentFamily ι) :
    IsAdmissible F (ramanujanExponentOf F) :=
  fun i => exponent_le_ramanujanExponentOf F i

/-- **Admissible exponents bound the Ramanujan exponent.** Let $F$ be a local-exponent family and
let $\delta \ge 0$ be a real number. If $\delta$ is admissible for $F$, that is, every local
exponent of $F$ is at most $\delta$, then the Ramanujan exponent of $F$ is at most $\delta$. -/
theorem ramanujanExponentOf_le_of_isAdmissible {ι : Type*}
    (F : LocalExponentFamily ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : IsAdmissible F δ) : ramanujanExponentOf F ≤ δ := by
  apply csSup_le (exponentSet_nonempty F)
  rintro y (rfl | ⟨i, rfl⟩)
  · exact hδ
  · exact h i

/-- **Admissibility is a bound by the Ramanujan exponent.** For every local-exponent family $F$ and
every real $\delta \ge 0$, $F$ is admissible at $\delta$ if and only if the Ramanujan exponent of
$F$ is at most $\delta$. -/
theorem isAdmissible_iff_ramanujanExponentOf_le {ι : Type*}
    (F : LocalExponentFamily ι) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsAdmissible F δ ↔ ramanujanExponentOf F ≤ δ :=
  ⟨ramanujanExponentOf_le_of_isAdmissible F hδ,
    fun h i => (exponent_le_ramanujanExponentOf F i).trans h⟩

/-- **The Ramanujan exponent vanishes exactly in the tempered case.** For every local-exponent
family $F$, the Ramanujan exponent of $F$ is $0$ if and only if $F$ satisfies the generalized
Ramanujan conclusion, that is, every local exponent of $F$ is $0$. -/
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

/-- **Admissible exponents of a local-exponent family.** For a local-exponent family $F$ with
local exponents $m_i$ ($i \in \iota$), the set of admissible exponents of $F$ is the set of real
numbers $\delta \ge 0$ such that $F$ is admissible at $\delta$, that is, $m_i \le \delta$ for
every index $i$. -/
def admissibleExponents {ι : Type*} (F : LocalExponentFamily ι) : Set ℝ :=
  {δ | 0 ≤ δ ∧ IsAdmissible F δ}

/-- **The Ramanujan exponent is the infimum of the admissible exponents.** For every
local-exponent family $F$, the Ramanujan exponent of $F$ equals the infimum of the admissible
exponents of $F$, that is, of the set of real numbers $\delta \ge 0$ such that every local
exponent of $F$ is at most $\delta$. -/
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

/-- **Satake pairs with a given local exponent.** For real numbers $N$ and $t$, a pair
$(\alpha, \beta)$ of complex numbers is in arithmetic Satake normalization with local exponent $t$
at residue cardinality $N$ when $|\alpha\beta| = 1$, $|\alpha| = N^t$ and $|\beta| = N^{-t}$. -/
def IsSatakePair (N t : ℝ) (α β : ℂ) : Prop :=
  ‖α * β‖ = 1 ∧ ‖α‖ = N ^ t ∧ ‖β‖ = N ^ (-t)

/-- **Hecke bound from a Satake pair.** Let $N \ge 1$ and $t, \delta$ be real numbers with
$0 \le t \le \delta$. If complex numbers $\alpha, \beta$ form a Satake pair with local exponent
$t$ at residue cardinality $N$, then $|\alpha + \beta| \le 2 N^\delta$.

The catalogue also records the sharper expression $N^\delta + N^{-\delta}$; the bound proved here
is its displayed consequence $2N^\delta$. -/
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

/-- **Hecke bound from a Satake pair at a finite place.** Let $K$ be a number field, $v$ a finite
place of $K$ with residue norm $N(v)$, and $t, \delta$ real numbers with $0 \le t \le \delta$. If
complex numbers $\alpha, \beta$ form a Satake pair with local exponent $t$ at residue cardinality
$N(v)$, then $|\alpha + \beta| \le 2 N(v)^\delta$. -/
theorem hecke_norm_le_two_mul_residueNorm_rpow_of_isSatakePair
    {K : Type*} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) {t δ : ℝ}
    {α β : ℂ} (ht0 : 0 ≤ t) (ht : t ≤ δ)
    (h : IsSatakePair v.residueNorm t α β) :
    ‖α + β‖ ≤ 2 * v.residueNorm ^ δ :=
  hecke_norm_le_two_mul_rpow_of_isSatakePair
    v.one_le_residueNorm ht0 ht h

/-- **Exceptional Selberg eigenvalue witnesses.** The type of pairs $(\Gamma, \lambda)$ where
$\Gamma$ is a congruence subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and $\lambda$ is a real
eigenvalue of the hyperbolic Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ with
$0 < \lambda < 1/4$.

Morally, these pairs index archimedean local components over $\mathbb{Q}$; their
identification with genuine cuspidal automorphic local components is a modelling assumption
and is not formalized here. -/
def SelbergWitness : Type :=
  {x : Subgroup SL(2, ℤ) × ℝ // IsCongruenceSubgroup x.1 ∧
    IsEigenvalue x.1 x.2 ∧ 0 < x.2 ∧ x.2 < 1 / 4}

/-- **Selberg gap of an exceptional eigenvalue.** For an exceptional-eigenvalue witness, a
congruence subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ with a Laplace eigenvalue
$\lambda \in (0, 1/4)$, the Selberg gap is $\sqrt{1/4 - \lambda}$: the archimedean local exponent
$\theta$ forced by $\lambda$, written as $\lambda = 1/4 - \theta^2$. -/
noncomputable def selbergGap (w : SelbergWitness) : ℝ :=
  Real.sqrt (1 / 4 - w.1.2)

/-- **Selberg family of archimedean exponents.** The Selberg family is the local-exponent family
indexed by the exceptional-eigenvalue witnesses, the pairs $(\Gamma, \lambda)$ of a congruence
subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ and a Laplace eigenvalue $\lambda \in (0, 1/4)$
of $\Gamma$, whose local exponent at $(\Gamma, \lambda)$ is $\sqrt{1/4 - \lambda}$. -/
noncomputable def selbergFamily : LocalExponentFamily SelbergWitness where
  exponent := selbergGap
  exponent_nonneg := fun w => Real.sqrt_nonneg _
  exponent_le_half := by
    intro w
    apply le_half_of_mem_exceptionalGaps
    exact Or.inr ⟨w.1.2, w.2.2.1, w.2.2.2.1, w.2.2.2.2, rfl⟩

/-- **Families dominating the Selberg exceptional spectrum.** A local-exponent family $F$ with
local exponents $m_i$ ($i \in \iota$) dominates the Selberg archimedean slice when, for every
congruence subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ and every eigenvalue $\lambda$ of the
hyperbolic Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ with $0 < \lambda < 1/4$, there is an
index $i$ with $m_i = \sqrt{1/4 - \lambda}$.

This is the precise anchor needed for the comparison with Selberg's constant; it is a hypothesis
on a proposed genuine family, not a definition of one. -/
def DominatesSelberg {ι : Type*} (F : LocalExponentFamily ι) : Prop :=
  ∀ w : SelbergWitness, ∃ i, selbergGap w = F.exponent i

theorem dominatesSelberg_selbergFamily :
    DominatesSelberg selbergFamily :=
  fun w => ⟨w, rfl⟩

/-- **Exceptional eigenvalues bound Selberg-dominating exponents from below.** Let $F$ be a
local-exponent family that dominates the Selberg archimedean slice. If $\Gamma$ is a congruence
subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and $\lambda$ is a real eigenvalue of the hyperbolic
Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ with $0 < \lambda < 1/4$, then
$\sqrt{1/4 - \lambda}$ is at most the Ramanujan exponent of $F$. -/
theorem sqrt_le_ramanujanExponentOf_of_dominatesSelberg {ι : Type*}
    (F : LocalExponentFamily ι) (hdom : DominatesSelberg F)
    {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ) {lam : ℝ}
    (hlam : IsEigenvalue Γ lam) (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ ramanujanExponentOf F := by
  obtain ⟨i, hi⟩ := hdom ⟨⟨Γ, lam⟩, hΓ, hlam, hpos, hlt⟩
  calc
    Real.sqrt (1 / 4 - lam) = F.exponent i := hi
    _ ≤ ramanujanExponentOf F := exponent_le_ramanujanExponentOf F i

/-- **Selberg's constant is at most every dominating family's exponent.** Let $F$ be a
local-exponent family that dominates the Selberg archimedean slice, that is, for every
congruence subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ and every Laplace eigenvalue
$\lambda \in (0, 1/4)$ of $\Gamma$, the gap $\sqrt{1/4 - \lambda}$ is one of the local exponents
of $F$. Then Selberg's constant is at most the Ramanujan exponent of $F$.

For the genuine cuspidal family this is the archimedean comparison of Selberg's constant with the
Ramanujan exponent $\delta_2$; it is not an equality of constants. -/
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

/-- **The Selberg family's exponent is Selberg's constant.** The Ramanujan exponent of the
canonical Selberg family of archimedean exponents is exactly Selberg's congruence spectral-gap
constant.

This identifies the currently anchored archimedean slice; it does not identify that slice with
the full Ramanujan exponent. -/
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
