/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
/-!

# Mass spectrometry and isotope patterns

Nominal isotope patterns are coefficients of products of polynomials, exact-mass spectra are
convolutions of finite mass distributions, and the nitrogen rule holds in an explicit valence
model of neutral molecules.

## i. Overview

*Nominal patterns.* An atom has finitely many isotopes `j`, each with an exact abundance weight
`a j` (a natural or rational number, not necessarily normalized) and a nominal mass shift
`shift j : ℕ`, supplied by the caller in the general definitions and theorems. Its
generating polynomial is `∑ j, C (a j) * X ^ shift j` (`atomPattern`), and the nominal pattern of a
molecule is the product of the polynomials of its atoms or atom groups (`nominalPattern`). The
coefficient of `X ^ k` is the unnormalized relative intensity of the nominal shift `k`: the total
weight of the isotopologues whose shifts add up to `k` (`coeff_nominalPattern`). Joining two
disjoint atom groups multiplies their polynomials, so the coefficients of the whole are the
Cauchy product of the coefficients of the parts (`coeff_nominalPattern_union`). Nonnegative
weights give nonnegative coefficients (`coeff_nominalPattern_nonneg`). The physical shift of an
isotope `j` of the set is `isotopeShift`, its nucleon number `A j` minus `isotopeMin`, the least
nucleon number over the isotope set, which a lightest isotope attains
(`exists_mem_eq_isotopeMin`). The nucleon number of each isotope of the set is `isotopeMin` plus
its shift (`eq_isotopeMin_add_isotopeShift`), and a lightest isotope has shift `0`
(`isotopeShift_eq_zero_of_eq`, `isotopeShift_eq_zero_of_forall_le`). With these shifts the
generating polynomial is `∑ j, C (a j) * X ^ (A j - isotopeMin)` (`atomPattern_isotopeShift`),
and the coefficient of `X ^ k` is the total weight of the isotopes of nucleon number
`isotopeMin + k` (`coeff_atomPattern_isotopeShift`).

*Exact-mass spectra.* Exact masses are real numbers, and they are never polynomial exponents.
The exponents of `R[X]` are natural numbers. A real mass only appears in the support of a
`FiniteMassDist`, a finite set of masses with positive weights summing to `1`. The convolution of
two such distributions (`FiniteMassDist.conv`) has the convolution sums as weights. It is
supported exactly on the sumset of the two supports, and its weights again sum to `1`. Its
weighted mean mass is the sum of the two weighted means (`FiniteMassDist.mean_conv`), so the
average mass of a molecule is the sum of the average masses of its atoms. This isotope-weighted
mean is re-derived here from Mathlib finite sums. The module does not import or depend on any
other ATLAS chemistry module.

*Binomial patterns.* Consider `n` atoms of an element with a light isotope of weight `a` and a
heavy isotope of weight `b` at nominal shift `d > 0`. Their pattern is `(a + b X ^ d) ^ n`
(`twoIsotopePattern`). The `k`-heavy peak sits at shift `d * k` with weight
`C(n, k) a ^ (n - k) b ^ k` (`coeff_twoIsotopePattern_mul`), and shifts that are not multiples
of `d` have weight `0`. Take `n` carbon atoms with ¹³C fraction `p` (so `d = 1`), and assume
`p ≠ 1`. The exact ratio of the `M + 1` peak to the monoisotopic peak is then
`C(n, 1) p (1 - p) ^ (n - 1) / (1 - p) ^ n = n p / (1 - p)` (`mPlusOneRatio_eq`). Only the carbon
atoms are modeled. The first-order value `n p` (`mPlusOneFirstOrder`) falls short of the exact
ratio by exactly `n p ^ 2 / (1 - p)`. Abundances are measured, uncertain quantities. Here they
are exact parameters, and numerical values, such as `p ≈ 0.011` for ¹³C or the chlorine and
bromine ratios `3 : 1` and `1 : 1`, appear only in the tests.

*Masses.* Masses are numerical values in the unified atomic mass unit `u`. The nominal mass
(`nominalMass`) is the sum of the nucleon numbers of the atoms. It comes from counting, so it is
an exact natural number. The exact mass (`exactMass`) is the sum of the real isotope masses,
which are measured and need not be integers. The difference of the two is the sum of the
per-atom mass defects `m i - A i` (`exactMass_sub_nominalMass`). It is bounded by any per-atom
bounds supplied as hypotheses (`abs_exactMass_sub_nominalMass_le`); no numerical bound is
asserted. The resolving power `R = m / Δm` (`resolution`) takes a proof of `Δm ≠ 0` as an
argument, so it is not defined at `Δm = 0`.

*Nitrogen rule.* The rule is a theorem about a model, not an unconditional law. The model
hypotheses are:

- (M1) every atom is C, H, N, O, S, F, Cl, Br or I, counted in the nominal mass with the nucleon
  number of ¹²C, ¹H, ¹⁴N, ¹⁶O, ³²S, ¹⁹F, ³⁵Cl, ⁷⁹Br or ¹²⁷I (`Element.massNumber`);
- (M2) every atom has a common valence of its element: C 4, H 1, N 3 or 5, O 2, S 2, 4 or 6, and
  1 for the halogens (`Element.commonValences`);
- (M3) valence balance: the valences of all atoms have an even sum.

Under (M1)–(M3) the nominal mass is odd exactly when the number of nitrogen atoms is odd
(`nitrogenRule_of_even_sum_valence`). (M2) alone does not determine this parity, and (M3) is the
additional hypothesis that does. The reason is that the nucleon number and the valence of an atom
have the same parity for every element except nitrogen (14 is even, 3 and 5 are odd). For a
molecule given as a bond graph, where the valence of an atom is the total order of its bonds,
(M3) is a theorem: the valences add up to twice the total bond order (`BondGraph.sum_valence`).
Neutrality (charge `0`), together with the absence of unpaired electrons, is the intended
interpretation of the nitrogen rule (section E): a model assumption, not a consequence of the
valence premises. A bond graph carries no charge or electron data beyond its bond orders, so the
valence premises alone do not exclude ions or radicals. Ground-state O₂ is an explicit
out-of-model case that the premises do not exclude: its double-bond graph satisfies (M1)–(M3),
with both oxygen atoms at the common valence 2, but the molecule is a triplet radical.
`BondGraph.nitrogenRule` needs only (M2), and it has no hypothesis on charges or electrons. The
valence 5 of nitrogen and the valences 4 and 6 of sulfur are formal valences of structures drawn
with expanded valence shells, such as a nitro group with two N=O bonds. Ions such as NH₄⁺ and
radicals such as NO fall outside the intended interpretation. The tests include this ion and this
radical: their nitrogen atoms have the valences 4 and 2, so both also violate (M2), and the rule
fails for both.

The results are algebraic. They do not model instruments, ionization, fragmentation or charge
states `m/z`. They contain no abundance or exact-mass tables. They never place a real mass in a
polynomial exponent: the exponents of `R[X]` are natural numbers, and real masses occur only in
the support of a `FiniteMassDist`. They do not claim that the nitrogen rule holds for ions or
for valences outside the model.

## ii. Key results

- `coeff_nominalPattern` : the coefficient of `X ^ k` in a nominal pattern is the total weight of
  the isotopologues of nominal shift `k`.
- `coeff_nominalPattern_union` : the pattern of two disjoint atom groups is the Cauchy product of
  their patterns.
- `coeff_nominalPattern_nonneg` : nonnegative abundance weights give nonnegative coefficients.
- `isotopeShift` : the physical shift of an isotope, its nucleon number minus the least nucleon
  number `isotopeMin` over the isotope set (`isotopeMin_le`), which a lightest isotope attains
  (`exists_mem_eq_isotopeMin`).
- `eq_isotopeMin_add_isotopeShift` : the nucleon number of each isotope of the set is
  `isotopeMin` plus its shift.
- `isotopeShift_eq_zero_of_eq`, `isotopeShift_eq_zero_of_forall_le` : a lightest isotope has
  shift `0`.
- `atomPattern_isotopeShift`, `coeff_atomPattern_isotopeShift` : with the physical shifts, the
  coefficient of `X ^ k` in `atomPattern` is the total weight of the isotopes of nucleon number
  `isotopeMin + k`.
- `FiniteMassDist.weight_conv_pos_iff`, `FiniteMassDist.sum_weight_conv` : the convolution of two
  exact-mass distributions is supported exactly on the sumset of the supports, and its weights
  sum to `1`.
- `FiniteMassDist.mean_conv` : the weighted mean mass of a convolution is the sum of the means.
- `coeff_twoIsotopePattern_mul` : the `k`-heavy peak of `n` two-isotope atoms has weight
  `C(n, k) a ^ (n - k) b ^ k`.
- `mPlusOneRatio_eq` : the exact `(M+1)/M` ratio of `n` carbon atoms is `n p / (1 - p)`.
- `mPlusOneRatio_eq_firstOrder_add` : it exceeds the first-order value `n p` by
  `n p ^ 2 / (1 - p)`.
- `resolution_eq_iff` : the resolving power `R = m / Δm`, defined for `Δm ≠ 0`, is the unique `R`
  with `m = R * Δm`.
- `abs_exactMass_sub_nominalMass_le` : exact minus nominal mass is bounded by hypothesized
  per-atom mass-defect bounds.
- `nitrogenRule_of_even_sum_valence` : under (M1)–(M3) the nominal mass and the number of
  nitrogen atoms have the same parity.
- `BondGraph.nitrogenRule` : the same for a bond graph at common valences, with (M3) derived.

## iii. Table of contents

- A. Nominal isotope patterns
- B. Exact-mass distributions
- C. Binomial patterns and the `(M+1)/M` ratio
- D. Resolution, nominal mass and exact mass
- E. The nitrogen rule

## iv. References

- OpenStax, *Chemistry 2e*, §2.3, "Atomic Structure and Symbolism".
- OpenStax, *Chemistry 2e*, §3.1, "Formula Mass and the Mole Concept".
- OpenStax, *Chemistry 2e*, §1.5, "Measurement Uncertainty, Accuracy, and Precision".
- OpenStax, *Chemistry 2e*, §1.6, "Mathematical Treatment of Measurement Results".
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book).

-/

@[expose] public section

namespace Chemistry.Spectrometry

open Polynomial Pointwise

/-!

## A. Nominal isotope patterns

-/

/-- The nominal generating polynomial `∑ j ∈ iso, C (a j) * X ^ shift j` of one atom (or atom
group) whose isotopes `j ∈ iso` have abundance weights `a j` and nominal mass shifts `shift j`. -/
noncomputable def atomPattern {R ι : Type*} [Semiring R] (iso : Finset ι) (a : ι → R)
    (shift : ι → ℕ) : R[X] :=
  ∑ j ∈ iso, C (a j) * X ^ shift j

/-- The nominal pattern polynomial of a molecule whose atoms (or atom groups) are the `i ∈ s`:
the product of their generating polynomials. Atom `i` has the isotopes `iso i`, with abundance
weights `a i j` and nominal mass shifts `shift i j`. -/
noncomputable def nominalPattern {R κ ι : Type*} [CommSemiring R] (s : Finset κ)
    (iso : κ → Finset ι) (a : κ → ι → R) (shift : κ → ι → ℕ) : R[X] :=
  ∏ i ∈ s, atomPattern (iso i) (a i) (shift i)

/-- The coefficient of `X ^ k` in the polynomial of one atom is the total weight of its isotopes
of nominal shift `k`. -/
lemma coeff_atomPattern {R ι : Type*} [Semiring R] (iso : Finset ι) (a : ι → R)
    (shift : ι → ℕ) (k : ℕ) :
    (atomPattern iso a shift).coeff k = ∑ j ∈ iso with shift j = k, a j := by
  rw [atomPattern, finsetSum_coeff, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ =>
    (coeff_C_mul_X_pow _ _ _).trans (if_congr eq_comm rfl rfl)

/-- The coefficient of `X ^ k` in the nominal pattern of a molecule is the total (unnormalized)
weight of its isotopologues of nominal shift `k`. It is the sum, over the choices `σ` of one
isotope per atom whose shifts add up to `k`, of the products of the abundance weights. -/
theorem coeff_nominalPattern {R κ ι : Type*} [CommSemiring R] [Fintype κ] [DecidableEq κ]
    (iso : κ → Finset ι) (a : κ → ι → R) (shift : κ → ι → ℕ) (k : ℕ) :
    (nominalPattern Finset.univ iso a shift).coeff k =
      ∑ σ ∈ Fintype.piFinset iso with ∑ i, shift i (σ i) = k, ∏ i, a i (σ i) := by
  rw [nominalPattern]
  simp only [atomPattern]
  rw [Finset.prod_univ_sum, finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_prod, coeff_C_mul_X_pow]
  exact if_congr eq_comm rfl rfl

/-- The nominal pattern of the union of two disjoint atom groups is the product of their
patterns. -/
theorem nominalPattern_union {R κ ι : Type*} [CommSemiring R] [DecidableEq κ] {s t : Finset κ}
    (hst : Disjoint s t) (iso : κ → Finset ι) (a : κ → ι → R) (shift : κ → ι → ℕ) :
    nominalPattern (s ∪ t) iso a shift =
      nominalPattern s iso a shift * nominalPattern t iso a shift :=
  Finset.prod_union hst

/-- The coefficients of the nominal pattern of two disjoint atom groups are the Cauchy product
(convolution) of the coefficients of the two group patterns. -/
theorem coeff_nominalPattern_union {R κ ι : Type*} [CommSemiring R] [DecidableEq κ]
    {s t : Finset κ} (hst : Disjoint s t) (iso : κ → Finset ι) (a : κ → ι → R)
    (shift : κ → ι → ℕ) (k : ℕ) :
    (nominalPattern (s ∪ t) iso a shift).coeff k =
      ∑ x ∈ Finset.antidiagonal k,
        (nominalPattern s iso a shift).coeff x.1 * (nominalPattern t iso a shift).coeff x.2 := by
  rw [nominalPattern_union hst, coeff_mul]

/-- With nonnegative abundance weights, every coefficient of a nominal pattern is nonnegative. -/
theorem coeff_nominalPattern_nonneg {R κ ι : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] (s : Finset κ) (iso : κ → Finset ι) (a : κ → ι → R) (shift : κ → ι → ℕ)
    (ha : ∀ i ∈ s, ∀ j ∈ iso i, 0 ≤ a i j) (k : ℕ) :
    0 ≤ (nominalPattern s iso a shift).coeff k := by
  revert k
  refine Finset.prod_induction (fun i => atomPattern (iso i) (a i) (shift i))
    (fun q : R[X] => ∀ n, 0 ≤ q.coeff n) ?_ ?_ ?_
  · intro p q hp hq n
    rw [coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)
  · intro n
    rw [coeff_one]
    split_ifs <;> simp
  · intro i hi n
    rw [coeff_atomPattern]
    exact Finset.sum_nonneg fun j hj => ha i hi j (Finset.mem_filter.1 hj).1

/-- The least nucleon number over a nonempty isotope set `iso` whose isotopes `j` have nucleon
numbers `A j`: the nucleon number of a lightest isotope. -/
def isotopeMin {ι : Type*} (iso : Finset ι) (hiso : iso.Nonempty) (A : ι → ℕ) : ℕ :=
  (iso.image A).min' (hiso.image A)

/-- The physical nominal mass shift of an isotope `j ∈ iso`: its nucleon number `A j` minus the
least nucleon number `isotopeMin iso hiso A` over the isotope set. -/
def isotopeShift {ι : Type*} (iso : Finset ι) (hiso : iso.Nonempty) (A : ι → ℕ) (j : ι) : ℕ :=
  A j - isotopeMin iso hiso A

/-- The least nucleon number is at most the nucleon number of every isotope of the set. -/
lemma isotopeMin_le {ι : Type*} {iso : Finset ι} (hiso : iso.Nonempty) (A : ι → ℕ) {j : ι}
    (hj : j ∈ iso) : isotopeMin iso hiso A ≤ A j :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem A hj)

/-- Some isotope of the set attains the least nucleon number: a lightest isotope exists. -/
lemma exists_mem_eq_isotopeMin {ι : Type*} {iso : Finset ι} (hiso : iso.Nonempty) (A : ι → ℕ) :
    ∃ j ∈ iso, A j = isotopeMin iso hiso A :=
  Finset.mem_image.1 (Finset.min'_mem _ _)

/-- An isotope attaining the least nucleon number has shift `0`. -/
theorem isotopeShift_eq_zero_of_eq {ι : Type*} {iso : Finset ι} {hiso : iso.Nonempty}
    {A : ι → ℕ} {j : ι} (hj : A j = isotopeMin iso hiso A) : isotopeShift iso hiso A j = 0 := by
  rw [isotopeShift, hj, Nat.sub_self]

/-- A lightest isotope, one whose nucleon number is at most that of every isotope of the set, has
shift `0`. -/
theorem isotopeShift_eq_zero_of_forall_le {ι : Type*} {iso : Finset ι} (hiso : iso.Nonempty)
    {A : ι → ℕ} {j : ι} (hj : j ∈ iso) (hmin : ∀ i ∈ iso, A j ≤ A i) :
    isotopeShift iso hiso A j = 0 :=
  isotopeShift_eq_zero_of_eq
    ((Finset.le_min' _ _ _ (Finset.forall_mem_image.2 hmin)).antisymm (isotopeMin_le hiso A hj))

/-- The nucleon number of every isotope of the set is the least nucleon number plus its shift. The
truncated subtraction in `isotopeShift` loses nothing, since `isotopeMin_le` gives
`isotopeMin iso hiso A ≤ A j`. -/
theorem eq_isotopeMin_add_isotopeShift {ι : Type*} {iso : Finset ι} (hiso : iso.Nonempty)
    (A : ι → ℕ) {j : ι} (hj : j ∈ iso) :
    A j = isotopeMin iso hiso A + isotopeShift iso hiso A j :=
  (Nat.add_sub_of_le (isotopeMin_le hiso A hj)).symm

/-- With the physical shifts, the generating polynomial of an atom is
`∑ j ∈ iso, C (a j) * X ^ (A j - isotopeMin iso hiso A)`. -/
theorem atomPattern_isotopeShift {R ι : Type*} [Semiring R] (iso : Finset ι)
    (hiso : iso.Nonempty) (a : ι → R) (A : ι → ℕ) :
    atomPattern iso a (isotopeShift iso hiso A) =
      ∑ j ∈ iso, C (a j) * X ^ (A j - isotopeMin iso hiso A) :=
  rfl

/-- With the physical shifts, the coefficient of `X ^ k` in the polynomial of an atom is the total
weight of its isotopes of nucleon number `isotopeMin iso hiso A + k`. -/
theorem coeff_atomPattern_isotopeShift {R ι : Type*} [Semiring R] (iso : Finset ι)
    (hiso : iso.Nonempty) (a : ι → R) (A : ι → ℕ) (k : ℕ) :
    (atomPattern iso a (isotopeShift iso hiso A)).coeff k =
      ∑ j ∈ iso with A j = isotopeMin iso hiso A + k, a j := by
  rw [coeff_atomPattern]
  refine Finset.sum_congr (Finset.filter_congr fun j hj => ?_) fun _ _ => rfl
  have := eq_isotopeMin_add_isotopeShift hiso A hj
  omega

/-!

## B. Exact-mass distributions

-/

/-- A finite exact-mass distribution: finitely many real masses (in `u`) with positive weights
summing to `1`. Masses outside the support have weight `0`. -/
structure FiniteMassDist where
  /-- The masses that occur. -/
  support : Finset ℝ
  /-- The weight (fractional abundance) of each mass. -/
  weight : ℝ → ℝ
  /-- Every mass in the support has positive weight. -/
  weight_pos : ∀ m ∈ support, 0 < weight m
  /-- Masses outside the support have weight `0`. -/
  weight_eq_zero : ∀ m ∉ support, weight m = 0
  /-- The weights sum to `1`. -/
  sum_weight : ∑ m ∈ support, weight m = 1

/-- The support of a finite mass distribution is exactly the set of masses of positive weight. -/
theorem FiniteMassDist.mem_support_iff (d : FiniteMassDist) (m : ℝ) :
    m ∈ d.support ↔ 0 < d.weight m :=
  ⟨d.weight_pos m, fun h => by_contra fun hm => h.ne' (d.weight_eq_zero m hm)⟩

/-- The convolution weight at the mass `m`: the sum of `w₁ x * w₂ y` over the pairs
`(x, y) ∈ s₁ ×ˢ s₂` with `x + y = m`. -/
noncomputable def convWeight (s₁ s₂ : Finset ℝ) (w₁ w₂ : ℝ → ℝ) (m : ℝ) : ℝ :=
  ∑ p ∈ s₁ ×ˢ s₂ with p.1 + p.2 = m, w₁ p.1 * w₂ p.2

/-- The convolution weight vanishes off the sumset. -/
lemma convWeight_eq_zero_of_notMem {s₁ s₂ : Finset ℝ} {w₁ w₂ : ℝ → ℝ} {m : ℝ}
    (hm : m ∉ s₁ + s₂) : convWeight s₁ s₂ w₁ w₂ m = 0 := by
  refine Finset.sum_eq_zero fun p hp => absurd ?_ hm
  obtain ⟨hp', rfl⟩ := Finset.mem_filter.1 hp
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp'
  exact Finset.add_mem_add h₁ h₂

/-- With positive weights on the supports, the convolution weight is positive on the sumset. -/
lemma convWeight_pos {s₁ s₂ : Finset ℝ} {w₁ w₂ : ℝ → ℝ} (h₁ : ∀ x ∈ s₁, 0 < w₁ x)
    (h₂ : ∀ y ∈ s₂, 0 < w₂ y) {m : ℝ} (hm : m ∈ s₁ + s₂) :
    0 < convWeight s₁ s₂ w₁ w₂ m := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hm
  refine Finset.sum_pos (fun p hp => ?_)
    ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩⟩
  obtain ⟨hp', -⟩ := Finset.mem_filter.1 hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.1 hp'
  exact mul_pos (h₁ _ hp₁) (h₂ _ hp₂)

/-- The convolution weights over the sumset add up to the product of the two total weights. -/
lemma sum_convWeight (s₁ s₂ : Finset ℝ) (w₁ w₂ : ℝ → ℝ) :
    ∑ m ∈ s₁ + s₂, convWeight s₁ s₂ w₁ w₂ m = (∑ x ∈ s₁, w₁ x) * ∑ y ∈ s₂, w₂ y := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.add_mem_add
    (Finset.mem_product.1 hp).1 (Finset.mem_product.1 hp).2) _

/-- The convolution of two exact-mass distributions, the exact-mass distribution of a molecule
made of two parts with independent isotope compositions. It is supported on the sumset of the
two supports, with the convolution weights. -/
noncomputable def FiniteMassDist.conv (d₁ d₂ : FiniteMassDist) : FiniteMassDist where
  support := d₁.support + d₂.support
  weight := convWeight d₁.support d₂.support d₁.weight d₂.weight
  weight_pos _ hm := convWeight_pos d₁.weight_pos d₂.weight_pos hm
  weight_eq_zero _ hm := convWeight_eq_zero_of_notMem hm
  sum_weight := by rw [sum_convWeight, d₁.sum_weight, d₂.sum_weight, one_mul]

/-- The support of a convolution is the sumset of the supports. -/
theorem FiniteMassDist.support_conv (d₁ d₂ : FiniteMassDist) :
    (d₁.conv d₂).support = d₁.support + d₂.support :=
  rfl

/-- The weights of a convolution are the convolution sums. -/
theorem FiniteMassDist.weight_conv (d₁ d₂ : FiniteMassDist) (m : ℝ) :
    (d₁.conv d₂).weight m =
      ∑ p ∈ d₁.support ×ˢ d₂.support with p.1 + p.2 = m, d₁.weight p.1 * d₂.weight p.2 :=
  rfl

/-- A convolution has positive weight exactly on the sumset of the supports. -/
theorem FiniteMassDist.weight_conv_pos_iff (d₁ d₂ : FiniteMassDist) (m : ℝ) :
    0 < (d₁.conv d₂).weight m ↔ m ∈ d₁.support + d₂.support :=
  ((d₁.conv d₂).mem_support_iff m).symm

/-- The weights of a convolution sum to `1`. -/
theorem FiniteMassDist.sum_weight_conv (d₁ d₂ : FiniteMassDist) :
    ∑ m ∈ d₁.support + d₂.support, (d₁.conv d₂).weight m = 1 :=
  (d₁.conv d₂).sum_weight

/-- The weighted mean mass `∑ m ∈ support, weight m * m`. For the isotope distribution of an
element, it is the average atomic mass, the sum of the isotopic masses times their fractional
abundances. -/
noncomputable def FiniteMassDist.mean (d : FiniteMassDist) : ℝ :=
  ∑ m ∈ d.support, d.weight m * m

/-- The weighted mean mass of a convolution is the sum of the two weighted means. -/
theorem FiniteMassDist.mean_conv (d₁ d₂ : FiniteMassDist) :
    (d₁.conv d₂).mean = d₁.mean + d₂.mean := by
  have key : ∀ m ∈ d₁.support + d₂.support,
      convWeight d₁.support d₂.support d₁.weight d₂.weight m * m =
        ∑ p ∈ d₁.support ×ˢ d₂.support with p.1 + p.2 = m,
          d₁.weight p.1 * d₂.weight p.2 * (p.1 + p.2) := by
    intro m _
    rw [convWeight, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2]
  change ∑ m ∈ d₁.support + d₂.support,
      convWeight d₁.support d₂.support d₁.weight d₂.weight m * m = _
  rw [Finset.sum_congr rfl key, Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.add_mem_add
    (Finset.mem_product.1 hp).1 (Finset.mem_product.1 hp).2), Finset.sum_product]
  calc ∑ x ∈ d₁.support, ∑ y ∈ d₂.support, d₁.weight x * d₂.weight y * (x + y)
      = (∑ x ∈ d₁.support, d₁.weight x * x) * ∑ y ∈ d₂.support, d₂.weight y
        + (∑ x ∈ d₁.support, d₁.weight x) * ∑ y ∈ d₂.support, d₂.weight y * y := by
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = d₁.mean + d₂.mean := by
        rw [d₁.sum_weight, d₂.sum_weight, mul_one, one_mul]
        rfl

/-!

## C. Binomial patterns and the `(M+1)/M` ratio

-/

/-- The nominal pattern `(a + b X ^ d) ^ n` of `n` atoms of an element with a light isotope of
weight `a` and a heavy isotope of weight `b` at nominal shift `d`. -/
noncomputable def twoIsotopePattern {R : Type*} [CommSemiring R] (a b : R) (d n : ℕ) : R[X] :=
  (C a + C b * X ^ d) ^ n

/-- The two-isotope pattern is the nominal pattern of `n` identical two-isotope atoms. -/
lemma twoIsotopePattern_eq_nominalPattern {R : Type*} [CommSemiring R] (a b : R) (d n : ℕ) :
    twoIsotopePattern a b d n =
      nominalPattern (Finset.range n) (fun _ => (Finset.univ : Finset (Fin 2)))
        (fun _ => ![a, b]) (fun _ => ![0, d]) := by
  simp [twoIsotopePattern, nominalPattern, atomPattern, Fin.sum_univ_two]

/-- The binomial expansion of the two-isotope pattern: the isotopologues with `k` heavy atoms
contribute `C(n, k) a ^ (n - k) b ^ k` at the nominal shift `d * k`. -/
lemma twoIsotopePattern_eq_sum {R : Type*} [CommSemiring R] (a b : R) (d n : ℕ) :
    twoIsotopePattern a b d n =
      ∑ k ∈ Finset.range (n + 1), C (n.choose k * a ^ (n - k) * b ^ k) * X ^ (d * k) := by
  rw [twoIsotopePattern, add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul, mul_pow]
  ring

/-- The `k`-heavy peak: for `d > 0`, the coefficient of `X ^ (d * k)` in the pattern of `n`
two-isotope atoms is `C(n, k) a ^ (n - k) b ^ k`. -/
theorem coeff_twoIsotopePattern_mul {R : Type*} [CommSemiring R] (a b : R) {d : ℕ} (hd : 0 < d)
    (n k : ℕ) :
    (twoIsotopePattern a b d n).coeff (d * k) = n.choose k * a ^ (n - k) * b ^ k := by
  rw [twoIsotopePattern_eq_sum, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Nat.mul_left_cancel_iff hd]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

/-- A nominal shift that is not a multiple of `d` has weight `0` in a two-isotope pattern. -/
theorem coeff_twoIsotopePattern_of_not_dvd {R : Type*} [CommSemiring R] (a b : R) {d m : ℕ}
    (hm : ¬ d ∣ m) (n : ℕ) : (twoIsotopePattern a b d n).coeff m = 0 := by
  rw [twoIsotopePattern_eq_sum, finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right_iff]
  rintro rfl
  exact absurd (Dvd.intro k rfl) hm

/-- The exact `(M+1)/M` ratio of `n` carbon atoms whose heavy isotope ¹³C has fractional
abundance `p`. It is the ratio of the `X ^ 1` and `X ^ 0` coefficients of `((1 - p) + p X) ^ n`.
Only the carbon atoms are modeled. -/
noncomputable def mPlusOneRatio {K : Type*} [Field K] (p : K) (n : ℕ) : K :=
  (twoIsotopePattern (1 - p) p 1 n).coeff 1 / (twoIsotopePattern (1 - p) p 1 n).coeff 0

/-- The binomial form `C(n, 1) p (1 - p) ^ (n - 1) / (1 - p) ^ n` of the exact `(M+1)/M`
ratio. -/
theorem mPlusOneRatio_eq_choose {K : Type*} [Field K] (p : K) (n : ℕ) :
    mPlusOneRatio p n = n.choose 1 * p * (1 - p) ^ (n - 1) / (1 - p) ^ n := by
  have h1 := coeff_twoIsotopePattern_mul (1 - p) p one_pos n 1
  have h0 := coeff_twoIsotopePattern_mul (1 - p) p one_pos n 0
  rw [one_mul] at h1
  rw [mul_zero] at h0
  rw [mPlusOneRatio, h1, h0]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one, Nat.sub_zero,
    pow_one]
  ring

/-- For `p ≠ 1`, the exact `(M+1)/M` ratio of `n` carbon atoms is `n p / (1 - p)`. -/
theorem mPlusOneRatio_eq {K : Type*} [Field K] {p : K} (hp : p ≠ 1) (n : ℕ) :
    mPlusOneRatio p n = n * p / (1 - p) := by
  have h : 1 - p ≠ 0 := sub_ne_zero.2 hp.symm
  rw [mPlusOneRatio_eq_choose, Nat.choose_one_right]
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- The first-order approximation `n p` of the `(M+1)/M` ratio of `n` carbon atoms. -/
def mPlusOneFirstOrder {K : Type*} [Field K] (p : K) (n : ℕ) : K :=
  n * p

/-- For `p ≠ 1`, the exact `(M+1)/M` ratio is the first-order value `n p` plus the remainder
`n p ^ 2 / (1 - p)`, which is of second order in `p`. -/
theorem mPlusOneRatio_eq_firstOrder_add {K : Type*} [Field K] {p : K} (hp : p ≠ 1) (n : ℕ) :
    mPlusOneRatio p n = mPlusOneFirstOrder p n + n * p ^ 2 / (1 - p) := by
  have h : 1 - p ≠ 0 := sub_ne_zero.2 hp.symm
  rw [mPlusOneRatio_eq hp, mPlusOneFirstOrder]
  field_simp
  ring

/-- For `p < 1`, the first-order value `n p` does not exceed the exact `(M+1)/M` ratio. -/
theorem mPlusOneFirstOrder_le_mPlusOneRatio {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {p : K} (hp1 : p < 1) (n : ℕ) :
    mPlusOneFirstOrder p n ≤ mPlusOneRatio p n := by
  rw [mPlusOneRatio_eq_firstOrder_add hp1.ne, le_add_iff_nonneg_right]
  exact div_nonneg (mul_nonneg n.cast_nonneg (sq_nonneg p)) (sub_nonneg.2 hp1.le)

/-!

## D. Resolution, nominal mass and exact mass

-/

/-- The resolving power `R = m / Δm` at the mass `m`, where `Δm` is the mass difference of two
peaks that are just resolved. The definition takes a proof of `Δm ≠ 0`, so it is not defined at
`Δm = 0`; division in `ℝ` is total (`m / 0 = 0`), and without this argument that value would be
returned. Both masses are numerical values in the same unit, so `R` is a pure number. -/
noncomputable def resolution (m Δm : ℝ) (_hΔm : Δm ≠ 0) : ℝ :=
  m / Δm

/-- The resolving power is the unique `R` with `m = R * Δm`. -/
theorem resolution_eq_iff {m Δm R : ℝ} (hΔm : Δm ≠ 0) :
    resolution m Δm hΔm = R ↔ m = R * Δm :=
  div_eq_iff hΔm

/-- The resolving power is positive for `m > 0` and `Δm > 0`. -/
theorem resolution_pos {m Δm : ℝ} (hm : 0 < m) (hΔm : 0 < Δm) :
    0 < resolution m Δm hΔm.ne' :=
  div_pos hm hΔm

/-- The nominal mass of the atoms `i ∈ s`: the sum of their nucleon numbers `A i`. -/
def nominalMass {ι : Type*} (s : Finset ι) (A : ι → ℕ) : ℕ :=
  ∑ i ∈ s, A i

/-- The exact mass of the atoms `i ∈ s`: the sum of their isotope masses `m i` in `u`. -/
noncomputable def exactMass {ι : Type*} (s : Finset ι) (m : ι → ℝ) : ℝ :=
  ∑ i ∈ s, m i

/-- The nominal mass is an integer. -/
theorem nominalMass_mem_range_intCast {ι : Type*} (s : Finset ι) (A : ι → ℕ) :
    (nominalMass s A : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) :=
  ⟨nominalMass s A, Int.cast_natCast _⟩

/-- Exact minus nominal mass is the sum of the per-atom mass defects `m i - A i`. -/
theorem exactMass_sub_nominalMass {ι : Type*} (s : Finset ι) (m : ι → ℝ) (A : ι → ℕ) :
    exactMass s m - nominalMass s A = ∑ i ∈ s, (m i - A i) := by
  rw [exactMass, nominalMass, Nat.cast_sum, Finset.sum_sub_distrib]

/-- If every per-atom mass defect is bounded, `|m i - A i| ≤ δ i`, then exact minus nominal
mass is bounded by `∑ i ∈ s, δ i`. The bounds `δ` are hypotheses, not data of this module. -/
theorem abs_exactMass_sub_nominalMass_le {ι : Type*} (s : Finset ι) (m : ι → ℝ) (A : ι → ℕ)
    (δ : ι → ℝ) (hδ : ∀ i ∈ s, |m i - A i| ≤ δ i) :
    |exactMass s m - nominalMass s A| ≤ ∑ i ∈ s, δ i := by
  rw [exactMass_sub_nominalMass]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hδ)

/-!

## E. The nitrogen rule

-/

/-- The elements of the nitrogen-rule model. -/
inductive Element
  /-- Carbon. -/
  | C
  /-- Hydrogen. -/
  | H
  /-- Nitrogen. -/
  | N
  /-- Oxygen. -/
  | O
  /-- Sulfur. -/
  | S
  /-- Fluorine. -/
  | F
  /-- Chlorine. -/
  | Cl
  /-- Bromine. -/
  | Br
  /-- Iodine. -/
  | I
  deriving DecidableEq

/-- The nucleon number counted for an atom of each element in the nominal mass of the model,
that of ¹²C, ¹H, ¹⁴N, ¹⁶O, ³²S, ¹⁹F, ³⁵Cl, ⁷⁹Br or ¹²⁷I. Only the parities enter the nitrogen
rule: hydrogen and the halogens are odd, the other elements even. -/
def Element.massNumber : Element → ℕ
  | .C => 12
  | .H => 1
  | .N => 14
  | .O => 16
  | .S => 32
  | .F => 19
  | .Cl => 35
  | .Br => 79
  | .I => 127

/-- The common valences of the model: C 4, H 1, N 3 or 5, O 2, S 2, 4 or 6, and 1 for each
halogen. -/
def Element.commonValences : Element → Finset ℕ
  | .C => {4}
  | .H => {1}
  | .N => {3, 5}
  | .O => {2}
  | .S => {2, 4, 6}
  | .F => {1}
  | .Cl => {1}
  | .Br => {1}
  | .I => {1}

/-- At a common valence `v`, the sum of the nucleon number and `v` is odd exactly for nitrogen:
for every other element the nucleon number and the valence have the same parity. -/
lemma Element.massNumber_add_mod_two {e : Element} {v : ℕ} (hv : v ∈ e.commonValences) :
    (e.massNumber + v) % 2 = if e = .N then 1 else 0 := by
  cases e <;> simp [Element.commonValences, Element.massNumber] at hv ⊢ <;> omega

open Finset in
/-- The nitrogen rule from the valence-balance hypothesis. Suppose every atom `i ∈ s` has a common
valence `v i` of its element (M2), and the valences have an even sum (M3). Then the nominal mass
is odd exactly when the number of nitrogen atoms is odd. -/
theorem nitrogenRule_of_even_sum_valence {ι : Type*} (s : Finset ι) (el : ι → Element)
    (v : ι → ℕ) (hv : ∀ i ∈ s, v i ∈ (el i).commonValences) (hbal : Even (∑ i ∈ s, v i)) :
    Odd (nominalMass s fun i => (el i).massNumber) ↔ Odd #{i ∈ s | el i = .N} := by
  have key : (nominalMass s (fun i => (el i).massNumber) + ∑ i ∈ s, v i) % 2 =
      #{i ∈ s | el i = .N} % 2 := by
    rw [nominalMass, ← Finset.sum_add_distrib, Finset.sum_nat_mod, Finset.card_filter]
    congr 1
    exact Finset.sum_congr rfl fun i hi => Element.massNumber_add_mod_two (hv i hi)
  rw [Nat.even_iff] at hbal
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- A bond graph of a molecule: atoms labeled by elements, and bonds, each joining two distinct
atoms with a bond order. The valence of an atom is the total order of its bonds
(`BondGraph.valence`). -/
structure BondGraph (ι β : Type*) where
  /-- The atoms. -/
  atoms : Finset ι
  /-- The element of each atom. -/
  element : ι → Element
  /-- The bonds. -/
  bonds : Finset β
  /-- The first atom of each bond. -/
  src : β → ι
  /-- The second atom of each bond. -/
  tgt : β → ι
  /-- The bond order: `1` for a single bond, `2` for a double bond, `3` for a triple bond. -/
  order : β → ℕ
  /-- Every bond starts at an atom of the molecule. -/
  src_mem : ∀ b ∈ bonds, src b ∈ atoms
  /-- Every bond ends at an atom of the molecule. -/
  tgt_mem : ∀ b ∈ bonds, tgt b ∈ atoms
  /-- Every bond joins two distinct atoms. -/
  src_ne_tgt : ∀ b ∈ bonds, src b ≠ tgt b

/-- The valence of the atom `i`: the total order of the bonds at `i`. A bond counts once at each
of its two distinct atoms. -/
def BondGraph.valence {ι β : Type*} [DecidableEq ι] (G : BondGraph ι β) (i : ι) : ℕ :=
  ∑ b ∈ G.bonds with G.src b = i, G.order b + ∑ b ∈ G.bonds with G.tgt b = i, G.order b

/-- Valence balance: the valences of a bond graph add up to twice the total bond order, because
each bond contributes its order to both of its atoms. -/
theorem BondGraph.sum_valence {ι β : Type*} [DecidableEq ι] (G : BondGraph ι β) :
    ∑ i ∈ G.atoms, G.valence i = 2 * ∑ b ∈ G.bonds, G.order b := by
  simp only [BondGraph.valence, Finset.sum_add_distrib]
  rw [Finset.sum_fiberwise_of_maps_to G.src_mem, Finset.sum_fiberwise_of_maps_to G.tgt_mem,
    two_mul]

open Finset in
/-- The nitrogen rule for a neutral molecule given as a bond graph. If every atom is bonded at a
common valence of its element, the nominal mass is odd exactly when the number of nitrogen atoms
is odd. The valence balance (M3) is not assumed: it follows from `BondGraph.sum_valence`. -/
theorem BondGraph.nitrogenRule {ι β : Type*} [DecidableEq ι] (G : BondGraph ι β)
    (hv : ∀ i ∈ G.atoms, G.valence i ∈ (G.element i).commonValences) :
    Odd (nominalMass G.atoms fun i => (G.element i).massNumber) ↔
      Odd #{i ∈ G.atoms | G.element i = .N} :=
  nitrogenRule_of_even_sum_valence G.atoms G.element G.valence hv
    ⟨_, G.sum_valence.trans (two_mul _)⟩

end Chemistry.Spectrometry
