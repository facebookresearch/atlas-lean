/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Spectrometry.IsotopePatterns
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!

# Tests for mass spectrometry and isotope patterns

Every abundance and exact mass below is an approximate empirical input. It is used only in this
file, never in a general theorem:

- the ¹³C fraction `p = 0.011` (`p13C`), the textbook value of about 1.1 % (the isotope table of
  OpenStax *Chemistry 2e*, §2.3, lists 1.11 %);
- the relative abundances ³⁵Cl : ³⁷Cl = 3 : 1 and ⁷⁹Br : ⁸¹Br = 1 : 1 (`brClWeight`,
  `coeff_chlorine`, `coeff_bromine`);
- the chlorine fractions 0.7576 and 0.2424 of the worked example in §2.3 (`chlorineFraction`);
- the boron isotopes ¹⁰B, 10.0129 u, fraction 0.199, and ¹¹B, 11.0093 u, fraction 0.801, from §2.3
  (`boron`);
- the isotope masses ¹H 1.0078 u, ¹²C 12.0000 u, ¹⁴N 14.0031 u, ¹⁶O 15.9949 u and ¹⁹F 18.9984 u
  from the table in §2.3.

-/

@[expose] public section

open Polynomial Pointwise Chemistry.Spectrometry

namespace PhyslibExtTest.Chemistry.Spectrometry

/-!

## A. A worked nominal pattern: BrCl

-/

/-- Abundance weights of BrCl. Atom `0` is Br with ⁷⁹Br : ⁸¹Br = 1 : 1, atom `1` is Cl with
³⁵Cl : ³⁷Cl = 3 : 1 (empirical inputs). Isotope `0` is the light one, isotope `1` the heavy one. -/
def brClWeight : Fin 2 → Fin 2 → ℕ :=
  ![![1, 1], ![3, 1]]

/-- Nominal shifts of BrCl: the heavy isotope of each atom is two nucleons heavier. -/
def brClShift : Fin 2 → Fin 2 → ℕ :=
  fun _ => ![0, 2]

/-- The nominal pattern `(1 + X ^ 2) * (3 + X ^ 2)` of BrCl. -/
noncomputable def brClPattern : ℕ[X] :=
  nominalPattern Finset.univ (fun _ => Finset.univ) brClWeight brClShift

/-! The coefficients `3, 0, 4, 0, 1` of BrCl, read off isotopologue by isotopologue. -/

example : brClPattern.coeff 0 = 3 := by
  rw [brClPattern, coeff_nominalPattern]
  decide

example : brClPattern.coeff 1 = 0 := by
  rw [brClPattern, coeff_nominalPattern]
  decide

example : brClPattern.coeff 2 = 4 := by
  rw [brClPattern, coeff_nominalPattern]
  decide

example : brClPattern.coeff 3 = 0 := by
  rw [brClPattern, coeff_nominalPattern]
  decide

example : brClPattern.coeff 4 = 1 := by
  rw [brClPattern, coeff_nominalPattern]
  decide

/-! The `M + 2` coefficient again, as the Cauchy product `1 * 1 + 0 * 0 + 1 * 3` of the Br and
Cl patterns. -/

example : brClPattern.coeff 2 = 4 := by
  rw [brClPattern, show (Finset.univ : Finset (Fin 2)) = {0} ∪ {1} by decide,
    coeff_nominalPattern_union (by decide)]
  simp only [nominalPattern, Finset.prod_singleton, coeff_atomPattern]
  decide

/-- The chlorine fractions 0.7576 and 0.2424 of ³⁵Cl and ³⁷Cl (empirical input). -/
def chlorineFraction : Fin 2 → ℚ :=
  ![0.7576, 0.2424]

/-! Two chlorine atoms with these rational fractions have nonnegative pattern coefficients. -/

example (k : ℕ) :
    0 ≤ (nominalPattern (Finset.univ : Finset (Fin 2)) (fun _ => (Finset.univ : Finset (Fin 2)))
      (fun _ => chlorineFraction) (fun _ => ![0, 2])).coeff k := by
  refine coeff_nominalPattern_nonneg _ _ _ _ (fun _ _ => ?_) k
  simp only [Finset.mem_univ, true_implies, Fin.forall_fin_two]
  norm_num [chlorineFraction]

/-- The nucleon numbers 35 and 37 of ³⁵Cl and ³⁷Cl. -/
def chlorineNucleon : Fin 2 → ℕ :=
  ![35, 37]

/-! The physical shifts of chlorine. The least nucleon number is `35`, so the lightest isotope
³⁵Cl has shift `0` and ³⁷Cl has shift `2`. -/

lemma isotopeMin_chlorineNucleon :
    isotopeMin Finset.univ Finset.univ_nonempty chlorineNucleon = 35 := by
  decide

example : isotopeShift Finset.univ Finset.univ_nonempty chlorineNucleon 0 = 0 ∧
    isotopeShift Finset.univ Finset.univ_nonempty chlorineNucleon 1 = 2 := by
  decide

/-! For any weights `w`, the coefficient at the physical shift `2` is the weight `w 1` of the heavy
isotope ³⁷Cl. -/

example {R : Type*} [Semiring R] (w : Fin 2 → R) :
    (atomPattern Finset.univ w
      (isotopeShift Finset.univ Finset.univ_nonempty chlorineNucleon)).coeff 2 = w 1 := by
  rw [coeff_atomPattern_isotopeShift, isotopeMin_chlorineNucleon,
    show Finset.univ.filter (fun j => chlorineNucleon j = 35 + 2) = {1} by decide,
    Finset.sum_singleton]

/-! An isotope of least nucleon number has shift `0`: ¹⁶O among ¹⁶O, ¹⁷O and ¹⁸O. -/

example : isotopeShift Finset.univ Finset.univ_nonempty ![16, 17, 18] 0 = 0 :=
  isotopeShift_eq_zero_of_forall_le _ (Finset.mem_univ _) (by decide)

/-!

## B. Binomial patterns: chlorine and bromine

-/

/-- `n` chlorine atoms with ³⁵Cl : ³⁷Cl = 3 : 1 (empirical input): the `k`-heavy peak at nominal
shift `2 k` has weight `C(n, k) 3 ^ (n - k)`. -/
lemma coeff_chlorine (n k : ℕ) :
    (twoIsotopePattern (3 : ℕ) 1 2 n).coeff (2 * k) = n.choose k * 3 ^ (n - k) := by
  rw [coeff_twoIsotopePattern_mul _ _ two_pos, one_pow, mul_one, Nat.cast_id]

/-- `n` bromine atoms with ⁷⁹Br : ⁸¹Br = 1 : 1 (empirical input): the `k`-heavy peak at nominal
shift `2 k` has weight `C(n, k)`. -/
lemma coeff_bromine (n k : ℕ) :
    (twoIsotopePattern (1 : ℕ) 1 2 n).coeff (2 * k) = n.choose k := by
  rw [coeff_twoIsotopePattern_mul _ _ two_pos, one_pow, one_pow, mul_one, mul_one, Nat.cast_id]

/-! One chlorine atom: `M : M + 2 = 3 : 1`. -/

example : (twoIsotopePattern (3 : ℕ) 1 2 1).coeff 0 = 3 := by
  simpa using coeff_chlorine 1 0

example : (twoIsotopePattern (3 : ℕ) 1 2 1).coeff 2 = 1 := by
  simpa using coeff_chlorine 1 1

/-! Two chlorine atoms: `M : M + 2 : M + 4 = 9 : 6 : 1`, and nothing at `M + 1`. -/

example : (twoIsotopePattern (3 : ℕ) 1 2 2).coeff 0 = 9 := by
  simpa using coeff_chlorine 2 0

example : (twoIsotopePattern (3 : ℕ) 1 2 2).coeff 2 = 6 := by
  simpa using coeff_chlorine 2 1

example : (twoIsotopePattern (3 : ℕ) 1 2 2).coeff 4 = 1 := by
  simpa using coeff_chlorine 2 2

example : (twoIsotopePattern (3 : ℕ) 1 2 2).coeff 1 = 0 :=
  coeff_twoIsotopePattern_of_not_dvd _ _ (by decide) _

/-! The three chlorine atoms of CHCl₃: `27 : 27 : 9 : 1`. -/

example : (twoIsotopePattern (3 : ℕ) 1 2 3).coeff 0 = 27 ∧
    (twoIsotopePattern (3 : ℕ) 1 2 3).coeff 2 = 27 ∧
    (twoIsotopePattern (3 : ℕ) 1 2 3).coeff 4 = 9 ∧
    (twoIsotopePattern (3 : ℕ) 1 2 3).coeff 6 = 1 :=
  ⟨by simpa using coeff_chlorine 3 0, by simpa using coeff_chlorine 3 1,
    by simpa using coeff_chlorine 3 2, by simpa using coeff_chlorine 3 3⟩

/-! One bromine atom: `M : M + 2 = 1 : 1`. -/

example : (twoIsotopePattern (1 : ℕ) 1 2 1).coeff 0 = 1 := by
  simpa using coeff_bromine 1 0

example : (twoIsotopePattern (1 : ℕ) 1 2 1).coeff 2 = 1 := by
  simpa using coeff_bromine 1 1

/-! Two bromine atoms: `M : M + 2 : M + 4 = 1 : 2 : 1`. -/

example : (twoIsotopePattern (1 : ℕ) 1 2 2).coeff 0 = 1 := by
  simpa using coeff_bromine 2 0

example : (twoIsotopePattern (1 : ℕ) 1 2 2).coeff 2 = 2 := by
  simpa using coeff_bromine 2 1

example : (twoIsotopePattern (1 : ℕ) 1 2 2).coeff 4 = 1 := by
  simpa using coeff_bromine 2 2

/-! The pattern of two chlorine atoms is the nominal pattern of two identical atoms. -/

example : twoIsotopePattern (3 : ℕ) 1 2 2 =
    nominalPattern (Finset.range 2) (fun _ => Finset.univ) (fun _ => ![3, 1]) (fun _ => ![0, 2]) :=
  twoIsotopePattern_eq_nominalPattern _ _ _ _

/-!

## C. The `(M+1)/M` ratio

-/

/-- The ¹³C fractional abundance `p = 0.011`, an approximate empirical input. -/
def p13C : ℚ :=
  0.011

/-! Six carbon atoms (benzene, C₆H₆). The exact ratio is `6 p / (1 - p) = 66 / 989 ≈ 0.0667`. -/

example : mPlusOneRatio p13C (by norm_num [p13C]) 6 = 66 / 989 := by
  rw [mPlusOneRatio_eq (by norm_num [p13C])]
  norm_num [p13C]

/-! The first-order value is `6 × 1.1 % = 0.066`, and in general `n × 1.1 %`. -/

example : mPlusOneFirstOrder p13C 6 = 0.066 := by
  norm_num [mPlusOneFirstOrder, p13C]

example (n : ℕ) : mPlusOneFirstOrder p13C n = n * (1.1 / 100) := by
  norm_num [mPlusOneFirstOrder, p13C]

/-! The two differ by the second-order remainder `6 p ^ 2 / (1 - p)`, so the first-order value is
strictly smaller. -/

example : mPlusOneRatio p13C (by norm_num [p13C]) 6 - mPlusOneFirstOrder p13C 6 = 6 * p13C ^ 2 / (1 - p13C) := by
  rw [mPlusOneRatio_eq_firstOrder_add (by norm_num [p13C])]
  push_cast
  ring

example : mPlusOneFirstOrder p13C 6 < mPlusOneRatio p13C (by norm_num [p13C]) 6 := by
  rw [mPlusOneRatio_eq (by norm_num [p13C])]
  norm_num [mPlusOneFirstOrder, p13C]

example : mPlusOneFirstOrder p13C 6 ≤ mPlusOneRatio p13C (by norm_num [p13C]) 6 :=
  mPlusOneFirstOrder_le_mPlusOneRatio (by norm_num [p13C]) 6

/-! The binomial form: the `M + 1` and `M` peaks of six carbon atoms. -/

example : (twoIsotopePattern (1 - p13C) p13C 1 6).coeff 1 = 6 * (1 - p13C) ^ 5 * p13C := by
  simpa using coeff_twoIsotopePattern_mul (1 - p13C) p13C one_pos 6 1

example : mPlusOneRatio p13C (by norm_num [p13C]) 6 = 6 * p13C * (1 - p13C) ^ 5 / (1 - p13C) ^ 6 := by
  simpa using mPlusOneRatio_eq_choose p13C (by norm_num [p13C]) 6

/-! Boundary: at `p = 1` the monoisotopic coefficient is `0`, so the `(M+1)/M` ratio
is undefined there. That is why `mPlusOneRatio` takes a proof of `p ≠ 1`. -/

example : (twoIsotopePattern (1 - (1 : ℚ)) 1 1 1).coeff 0 = 0 := by
  have h := coeff_twoIsotopePattern_mul (1 - (1 : ℚ)) 1 one_pos 1 0
  simpa using h

/-!

## D. Resolution, nominal mass and exact mass

-/

/-! One ¹H atom has nominal mass `1` and exact mass `1.0078 u`, which is not an integer. -/

example : nominalMass Finset.univ (fun _ : Unit => 1) = 1 := by
  decide

example : exactMass Finset.univ (fun _ : Unit => (1.0078 : ℝ)) ≠
    nominalMass Finset.univ (fun _ : Unit => 1) := by
  norm_num [exactMass, nominalMass]

example : exactMass Finset.univ (fun _ : Unit => (1.0078 : ℝ)) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  simp only [exactMass, Finset.univ_unique, Finset.sum_singleton] at hz
  have h1 : (1 : ℝ) < z := by rw [hz]; norm_num
  have h2 : (z : ℝ) < 2 := by rw [hz]; norm_num
  have h1' : 1 < z := by exact_mod_cast h1
  have h2' : z < 2 := by exact_mod_cast h2
  omega

example : (nominalMass Finset.univ (fun _ : Unit => 1) : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) :=
  nominalMass_mem_range_intCast _ _

/-! CO and N₂ have the same nominal mass `28`, but exact masses `27.9949 u` and `28.0062 u`. -/

/-- The exact masses of ¹²C and ¹⁶O, the atoms of CO. -/
noncomputable def massesCO : Fin 2 → ℝ :=
  ![12.0000, 15.9949]

/-- The exact masses of the two ¹⁴N atoms of N₂. -/
noncomputable def massesN2 : Fin 2 → ℝ :=
  ![14.0031, 14.0031]

example : nominalMass Finset.univ ![12, 16] = 28 ∧ nominalMass Finset.univ ![14, 14] = 28 := by
  decide

lemma exactMass_CO : exactMass Finset.univ massesCO = 27.9949 := by
  norm_num [exactMass, massesCO, Fin.sum_univ_two]

lemma exactMass_N2 : exactMass Finset.univ massesN2 = 28.0062 := by
  norm_num [exactMass, massesN2, Fin.sum_univ_two]

/-! Separating them at `m = 28` takes `R = 28 / 0.0113 ≈ 2478`. -/

example (h : exactMass Finset.univ massesN2 - exactMass Finset.univ massesCO ≠ 0) :
    resolution 28 (exactMass Finset.univ massesN2 - exactMass Finset.univ massesCO) h =
      280000 / 113 := by
  rw [resolution_eq_iff, exactMass_N2, exactMass_CO]
  norm_num

example : 0 < resolution 28 0.0113 (by norm_num) :=
  resolution_pos (by norm_num) (by norm_num)

/-! The defect bounds `|12.0000 - 12| ≤ 0` and `|15.9949 - 16| ≤ 0.0051` give
`|27.9949 - 28| ≤ 0.0051`. -/

example : |exactMass Finset.univ massesCO - nominalMass Finset.univ ![12, 16]| ≤ 0 + 0.0051 := by
  have hδ : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      |massesCO i - ((![12, 16] : Fin 2 → ℕ) i : ℝ)| ≤ (![0, 0.0051] : Fin 2 → ℝ) i := by
    simp only [Finset.mem_univ, true_implies, Fin.forall_fin_two]
    norm_num [massesCO]
  refine (abs_exactMass_sub_nominalMass_le _ _ _ _ hδ).trans_eq ?_
  simp [Fin.sum_univ_two]

/-! The boundary case `Δm = 0` is excluded. `resolution m 0 h` would need a proof
`h : (0 : ℝ) ≠ 0`, and there is none, so `resolution m 0` has no value at all. -/

example (m : ℝ) : IsEmpty {R : ℝ // ∃ h : (0 : ℝ) ≠ 0, resolution m 0 h = R} :=
  ⟨fun ⟨_, h, _⟩ => h rfl⟩

/-! The guard matters: the total division of `ℝ` gives `m / 0 = 0`, and for `m ≠ 0` this value
violates the defining relation `m = R * Δm` of `resolution_eq_iff`. -/

example (m : ℝ) (hm : m ≠ 0) : m ≠ m / 0 * 0 := by
  simpa using hm

example (m Δm : ℝ) (h : Δm ≠ 0) : m = resolution m Δm h * Δm :=
  (resolution_eq_iff h).1 rfl

/-!

## E. Exact-mass distributions

-/

/-- The exact-mass distribution of boron: ¹⁰B at 10.0129 u with fraction 0.199 and ¹¹B at
11.0093 u with fraction 0.801 (empirical inputs). -/
noncomputable def boron : FiniteMassDist where
  support := {10.0129, 11.0093}
  weight m := if m = 10.0129 then 0.199 else if m = 11.0093 then 0.801 else 0
  weight_pos m hm := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> norm_num
  weight_eq_zero m hm := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [hm.1, hm.2]
  sum_weight := by
    rw [Finset.sum_pair (by norm_num)]
    norm_num

/-- The exact-mass distribution of fluorine: ¹⁹F at 18.9984 u with fraction 1 (empirical
input). -/
noncomputable def fluorine : FiniteMassDist where
  support := {18.9984}
  weight m := if m = 18.9984 then 1 else 0
  weight_pos m hm := by
    rw [Finset.mem_singleton] at hm
    simp [hm]
  weight_eq_zero m hm := by
    rw [Finset.mem_singleton] at hm
    simp [hm]
  sum_weight := by
    simp

/-- The average atomic mass of boron, `0.199 × 10.0129 + 0.801 × 11.0093 = 10.8110164`
(≈ 10.81 u). -/
lemma boron_mean : boron.mean = 10.8110164 := by
  rw [FiniteMassDist.mean, show boron.support = {10.0129, 11.0093} from rfl,
    Finset.sum_pair (by norm_num)]
  norm_num [boron]

lemma fluorine_mean : fluorine.mean = 18.9984 := by
  rw [FiniteMassDist.mean, show fluorine.support = {18.9984} from rfl, Finset.sum_singleton]
  norm_num [fluorine]

/-! Boron monofluoride BF: its average mass is the sum of the average atomic masses. -/

example : (boron.conv fluorine).mean = 29.8094164 := by
  rw [FiniteMassDist.mean_conv, boron_mean, fluorine_mean]
  norm_num

/-! The convolution has positive weight at the sum `10.0129 + 18.9984` of two support masses, its
weight there is the convolution sum, and its weights sum to `1`. -/

example : 0 < (boron.conv fluorine).weight (10.0129 + 18.9984) := by
  rw [FiniteMassDist.weight_conv_pos_iff]
  exact Finset.add_mem_add (by simp [boron]) (by simp [fluorine])

example : (boron.conv fluorine).weight (10.0129 + 18.9984) =
    ∑ p ∈ boron.support ×ˢ fluorine.support with p.1 + p.2 = 10.0129 + 18.9984,
      boron.weight p.1 * fluorine.weight p.2 :=
  FiniteMassDist.weight_conv _ _ _

example : ∑ m ∈ boron.support + fluorine.support, (boron.conv fluorine).weight m = 1 :=
  FiniteMassDist.sum_weight_conv _ _

/-! A mass that is not a sum of support masses has weight `0`. -/

example : (boron.conv fluorine).weight 29.5 = 0 := by
  refine ((boron.conv fluorine).weight_eq_zero _ ?_)
  rw [FiniteMassDist.support_conv, Finset.mem_add]
  rintro ⟨x, hx, y, hy, hxy⟩
  simp only [boron, fluorine, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> subst hy <;> norm_num at hxy

/-! The boron support masses are not natural numbers, so neither can be an exponent of `X`. -/

example : ∀ m ∈ boron.support, m ∉ Set.range (Nat.cast : ℕ → ℝ) := by
  rintro m hm ⟨n, rfl⟩
  simp only [boron, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h
  · have h1 : (10 : ℝ) < n := by rw [h]; norm_num
    have h2 : (n : ℝ) < 11 := by rw [h]; norm_num
    have h1' : 10 < n := by exact_mod_cast h1
    have h2' : n < 11 := by exact_mod_cast h2
    omega
  · have h1 : (11 : ℝ) < n := by rw [h]; norm_num
    have h2 : (n : ℝ) < 12 := by rw [h]; norm_num
    have h1' : 11 < n := by exact_mod_cast h1
    have h2' : n < 12 := by exact_mod_cast h2
    omega

/-!

## F. The nitrogen rule

-/

/-- Methane CH₄: atom `0` is C, atoms `1` to `4` are H, and bond `b` joins C to atom `b + 1`. -/
def methane : BondGraph (Fin 5) (Fin 4) where
  atoms := Finset.univ
  element := ![.C, .H, .H, .H, .H]
  bonds := Finset.univ
  src _ := 0
  tgt b := b.succ
  order _ := 1
  src_mem := by simp
  tgt_mem := by simp
  src_ne_tgt := by decide

lemma methane_valence :
    ∀ i ∈ methane.atoms, methane.valence i ∈ (methane.element i).commonValences := by
  decide

/-! CH₄ has no nitrogen and the even nominal mass `16`. -/

example : nominalMass methane.atoms (fun i => (methane.element i).massNumber) = 16 := by
  decide

example : Even (nominalMass methane.atoms fun i => (methane.element i).massNumber) := by
  rw [← Nat.not_odd_iff_even, methane.nitrogenRule methane_valence]
  decide

/-- Ammonia NH₃: atom `0` is N, atoms `1` to `3` are H, and bond `b` joins N to atom `b + 1`. -/
def ammonia : BondGraph (Fin 4) (Fin 3) where
  atoms := Finset.univ
  element := ![.N, .H, .H, .H]
  bonds := Finset.univ
  src _ := 0
  tgt b := b.succ
  order _ := 1
  src_mem := by simp
  tgt_mem := by simp
  src_ne_tgt := by decide

lemma ammonia_valence :
    ∀ i ∈ ammonia.atoms, ammonia.valence i ∈ (ammonia.element i).commonValences := by
  decide

/-! NH₃ has one nitrogen and the odd nominal mass `17`. -/

example : nominalMass ammonia.atoms (fun i => (ammonia.element i).massNumber) = 17 := by
  decide

example : Odd (nominalMass ammonia.atoms fun i => (ammonia.element i).massNumber) := by
  rw [ammonia.nitrogenRule ammonia_valence]
  decide

/-- Hydrogen cyanide H–C≡N: bond `0` is the single bond H–C, bond `1` the triple bond C≡N. -/
def hydrogenCyanide : BondGraph (Fin 3) (Fin 2) where
  atoms := Finset.univ
  element := ![.H, .C, .N]
  bonds := Finset.univ
  src := ![0, 1]
  tgt := ![1, 2]
  order := ![1, 3]
  src_mem := by simp
  tgt_mem := by simp
  src_ne_tgt := by decide

lemma hydrogenCyanide_valence : ∀ i ∈ hydrogenCyanide.atoms,
    hydrogenCyanide.valence i ∈ (hydrogenCyanide.element i).commonValences := by
  decide

/-! HCN has one nitrogen and the odd nominal mass `27`. -/

example : Odd (nominalMass hydrogenCyanide.atoms fun i =>
    (hydrogenCyanide.element i).massNumber) := by
  rw [hydrogenCyanide.nitrogenRule hydrogenCyanide_valence]
  decide

/-- The ammonium ion NH₄⁺, of charge `+1`: nitrogen bonded to four hydrogen atoms. -/
def ammonium : BondGraph (Fin 5) (Fin 4) where
  atoms := Finset.univ
  element := ![.N, .H, .H, .H, .H]
  bonds := Finset.univ
  src _ := 0
  tgt b := b.succ
  order _ := 1
  src_mem := by simp
  tgt_mem := by simp
  src_ne_tgt := by decide

/-! The ion is outside the model, since its nitrogen has valence `4`. The rule fails for it: the
nominal mass `18` is even, but there is one nitrogen atom. -/

example : ammonium.valence 0 ∉ (ammonium.element 0).commonValences := by
  decide

example : ¬ (Odd (nominalMass ammonium.atoms fun i => (ammonium.element i).massNumber) ↔
    Odd (ammonium.atoms.filter fun i => ammonium.element i = .N).card) := by
  decide

/-- Nitric oxide N=O, a neutral radical with one double bond. -/
def nitricOxide : BondGraph (Fin 2) (Fin 1) where
  atoms := Finset.univ
  element := ![.N, .O]
  bonds := Finset.univ
  src _ := 0
  tgt _ := 1
  order _ := 2
  src_mem := by simp
  tgt_mem := by simp
  src_ne_tgt := by decide

/-! The radical is outside the model, since its nitrogen has valence `2`. The rule fails for it:
the nominal mass `30` is even, but there is one nitrogen atom. -/

example : nitricOxide.valence 0 ∉ (nitricOxide.element 0).commonValences := by
  decide

example : ¬ (Odd (nominalMass nitricOxide.atoms fun i => (nitricOxide.element i).massNumber) ↔
    Odd (nitricOxide.atoms.filter fun i => nitricOxide.element i = .N).card) := by
  decide

/-- The elements N, H, H, H, H. -/
def nh4Elements : Fin 5 → Element :=
  ![.N, .H, .H, .H, .H]

/-- The valences 3, 1, 1, 1, 1, each a common valence of its element. -/
def nh4Valences : Fin 5 → ℕ :=
  ![3, 1, 1, 1, 1]

/-! The common valences (M2) alone do not fix the parity. These five atoms satisfy (M2), but their
valence sum `7` is odd, so (M3) fails and so does the conclusion. -/

example : (∀ i ∈ Finset.univ, nh4Valences i ∈ (nh4Elements i).commonValences) ∧
    ¬ Even (∑ i, nh4Valences i) ∧
    ¬ (Odd (nominalMass Finset.univ fun i => (nh4Elements i).massNumber) ↔
      Odd (Finset.univ.filter fun i => nh4Elements i = .N).card) := by
  decide

end PhyslibExtTest.Chemistry.Spectrometry

#print axioms Chemistry.Spectrometry.atomPattern
#print axioms Chemistry.Spectrometry.nominalPattern
#print axioms Chemistry.Spectrometry.coeff_atomPattern
#print axioms Chemistry.Spectrometry.coeff_nominalPattern
#print axioms Chemistry.Spectrometry.nominalPattern_union
#print axioms Chemistry.Spectrometry.coeff_nominalPattern_union
#print axioms Chemistry.Spectrometry.coeff_nominalPattern_nonneg
#print axioms Chemistry.Spectrometry.isotopeMin
#print axioms Chemistry.Spectrometry.isotopeShift
#print axioms Chemistry.Spectrometry.isotopeMin_le
#print axioms Chemistry.Spectrometry.exists_mem_eq_isotopeMin
#print axioms Chemistry.Spectrometry.isotopeShift_eq_zero_of_eq
#print axioms Chemistry.Spectrometry.isotopeShift_eq_zero_of_forall_le
#print axioms Chemistry.Spectrometry.eq_isotopeMin_add_isotopeShift
#print axioms Chemistry.Spectrometry.atomPattern_isotopeShift
#print axioms Chemistry.Spectrometry.coeff_atomPattern_isotopeShift
#print axioms Chemistry.Spectrometry.FiniteMassDist
#print axioms Chemistry.Spectrometry.FiniteMassDist.support
#print axioms Chemistry.Spectrometry.FiniteMassDist.weight
#print axioms Chemistry.Spectrometry.FiniteMassDist.weight_pos
#print axioms Chemistry.Spectrometry.FiniteMassDist.weight_eq_zero
#print axioms Chemistry.Spectrometry.FiniteMassDist.sum_weight
#print axioms Chemistry.Spectrometry.FiniteMassDist.mem_support_iff
#print axioms Chemistry.Spectrometry.convWeight
#print axioms Chemistry.Spectrometry.convWeight_eq_zero_of_notMem
#print axioms Chemistry.Spectrometry.convWeight_pos
#print axioms Chemistry.Spectrometry.sum_convWeight
#print axioms Chemistry.Spectrometry.FiniteMassDist.conv
#print axioms Chemistry.Spectrometry.FiniteMassDist.support_conv
#print axioms Chemistry.Spectrometry.FiniteMassDist.weight_conv
#print axioms Chemistry.Spectrometry.FiniteMassDist.weight_conv_pos_iff
#print axioms Chemistry.Spectrometry.FiniteMassDist.sum_weight_conv
#print axioms Chemistry.Spectrometry.FiniteMassDist.mean
#print axioms Chemistry.Spectrometry.FiniteMassDist.mean_conv
#print axioms Chemistry.Spectrometry.twoIsotopePattern
#print axioms Chemistry.Spectrometry.twoIsotopePattern_eq_nominalPattern
#print axioms Chemistry.Spectrometry.twoIsotopePattern_eq_sum
#print axioms Chemistry.Spectrometry.coeff_twoIsotopePattern_mul
#print axioms Chemistry.Spectrometry.coeff_twoIsotopePattern_of_not_dvd
#print axioms Chemistry.Spectrometry.mPlusOneRatio
#print axioms Chemistry.Spectrometry.mPlusOneRatio_eq_choose
#print axioms Chemistry.Spectrometry.mPlusOneRatio_eq
#print axioms Chemistry.Spectrometry.mPlusOneFirstOrder
#print axioms Chemistry.Spectrometry.mPlusOneRatio_eq_firstOrder_add
#print axioms Chemistry.Spectrometry.mPlusOneFirstOrder_le_mPlusOneRatio
#print axioms Chemistry.Spectrometry.resolution
#print axioms Chemistry.Spectrometry.resolution_eq_iff
#print axioms Chemistry.Spectrometry.resolution_pos
#print axioms Chemistry.Spectrometry.nominalMass
#print axioms Chemistry.Spectrometry.exactMass
#print axioms Chemistry.Spectrometry.nominalMass_mem_range_intCast
#print axioms Chemistry.Spectrometry.exactMass_sub_nominalMass
#print axioms Chemistry.Spectrometry.abs_exactMass_sub_nominalMass_le
#print axioms Chemistry.Spectrometry.Element
#print axioms Chemistry.Spectrometry.Element.massNumber
#print axioms Chemistry.Spectrometry.Element.commonValences
#print axioms Chemistry.Spectrometry.instDecidableEqElement
#print axioms Chemistry.Spectrometry.Element.massNumber_add_mod_two
#print axioms Chemistry.Spectrometry.nitrogenRule_of_even_sum_valence
#print axioms Chemistry.Spectrometry.BondGraph
#print axioms Chemistry.Spectrometry.BondGraph.atoms
#print axioms Chemistry.Spectrometry.BondGraph.element
#print axioms Chemistry.Spectrometry.BondGraph.bonds
#print axioms Chemistry.Spectrometry.BondGraph.src
#print axioms Chemistry.Spectrometry.BondGraph.tgt
#print axioms Chemistry.Spectrometry.BondGraph.order
#print axioms Chemistry.Spectrometry.BondGraph.src_mem
#print axioms Chemistry.Spectrometry.BondGraph.tgt_mem
#print axioms Chemistry.Spectrometry.BondGraph.src_ne_tgt
#print axioms Chemistry.Spectrometry.BondGraph.valence
#print axioms Chemistry.Spectrometry.BondGraph.sum_valence
#print axioms Chemistry.Spectrometry.BondGraph.nitrogenRule
#print axioms PhyslibExtTest.Chemistry.Spectrometry.chlorineFraction
#print axioms PhyslibExtTest.Chemistry.Spectrometry.chlorineNucleon
#print axioms PhyslibExtTest.Chemistry.Spectrometry.isotopeMin_chlorineNucleon
#print axioms PhyslibExtTest.Chemistry.Spectrometry.coeff_chlorine
#print axioms PhyslibExtTest.Chemistry.Spectrometry.coeff_bromine
#print axioms PhyslibExtTest.Chemistry.Spectrometry.exactMass_CO
#print axioms PhyslibExtTest.Chemistry.Spectrometry.exactMass_N2
#print axioms PhyslibExtTest.Chemistry.Spectrometry.boron
#print axioms PhyslibExtTest.Chemistry.Spectrometry.fluorine
#print axioms PhyslibExtTest.Chemistry.Spectrometry.boron_mean
#print axioms PhyslibExtTest.Chemistry.Spectrometry.fluorine_mean
#print axioms PhyslibExtTest.Chemistry.Spectrometry.methane_valence
#print axioms PhyslibExtTest.Chemistry.Spectrometry.ammonia_valence
#print axioms PhyslibExtTest.Chemistry.Spectrometry.hydrogenCyanide_valence
