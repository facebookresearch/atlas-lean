/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/RingTheory/CyclicCohomology/Periodicity/Comparison.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicPeriodicity
public import MathlibExt.RingTheory.CyclicPeriodicityCochains
import MathlibExt.Algebra.Algebra.CyclicNatCast

/-!
# Comparison of Connes' periodicity operator with the bicomplex shift

Connes' periodicity operator `S : HCⁿ(A; M) → HCⁿ⁺²(A; M)` sends the class of a cyclic cocycle `φ`
to `[S₀ φ]`, whereas the periodicity map `TauCeti.cyclicTotalHomologyPeriodicity` of the cyclic
bicomplex shifts every component of a total cocycle two columns to the right.

For a cyclic `n`-cocycle `φ` over any commutative ring `R`, consider the total cochain of degree
`n + 1` with component `H' (b' φ)` in row `n + 1` (column zero) and `(n + 2) • φ` in row `n`
(column one), where `H' = TauCeti.cyclicRowHomotopySum` satisfies `(1 - λ) H' = (n + 2) - N`. Its
total differential has:

* `b (H' (b' φ)) = S₀ φ` in row `n + 2` (column zero), by
  `TauCeti.hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles`;
* `-(n + 2) • b' φ + (1 - λ) (H' (b' φ)) = -N (b' φ) = -b (N φ) = 0` in row `n + 1` (column one);
* `N ((n + 2) • φ) = ((n + 1) * (n + 2)) • φ` in row `n` (column two).

Thus `S₀ φ` in column zero and `-((n + 1) * (n + 2)) • φ` in column two represent the same class in
`Hⁿ⁺²(Tot)`. Over a `ℚ`-algebra, where the inclusion of cyclic cochains into column zero is a
quasi-isomorphism (`TauCeti.quasiIso_cyclicCochainComplexToTotal`), Connes' operator `S` on cyclic
cohomology therefore corresponds under this quasi-isomorphism to `-((n + 1) * (n + 2))` times the
bicomplex periodicity map. Because `-(n + 1) * (n + 2)` is a unit in `R`, this transfers the
exactness of `Hᵐ(Tot) → Hᵐ⁺²(Tot) → HHᵐ⁺²` (`Periodicity.Basic`) to Connes' operator `S` and `I` on
cyclic cohomology.

## Main results

* `TauCeti.exists_cyclicTotalDifferential_eq_cyclicCocyclesPeriodicity_add`: the explicit total
  coboundary relating `S₀ φ` in column zero to `((n + 1) * (n + 2)) • φ` in column two.
* `TauCeti.cyclicTotalHomologyMk_cyclicCocyclesPeriodicity`: in `Hⁿ⁺²(Tot)`, `[S₀ φ] =
  -((n + 1) * (n + 2)) • S_Tot [φ]` over every commutative ring.
* `TauCeti.cyclicCohomology.periodicity_comp_homologyMap_cyclicCochainComplexToTotal`: compatibility
  of `cyclicCohomology.periodicity` with `cyclicTotalHomologyPeriodicity` over a `ℚ`-algebra.
* `TauCeti.cyclicCohomology.periodicity_comp_toHochschild`: `I ∘ S = 0` on cyclic cohomology.
* `TauCeti.cyclicCohomology.exact_periodicity_toHochschild`: exactness of
  `HCᵐ(A; M) →S HCᵐ⁺²(A; M) →I HHᵐ⁺²(A, Hom_R(A, M))` for a unital algebra over a `ℚ`-algebra.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.2, Theorem 2.2.7.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

/-! ### Total coboundary comparing `S₀` with the bicomplex shift -/

section TotalHomotopy

variable {R : Type*} {A : Type u} {M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M] {n : ℕ}

/-- The total `(n + 1)`-cochain `H' (b' φ) + (n + 2) • φ` in columns zero and one whose total
differential relates `S₀ φ` in column zero to `((n + 1) * (n + 2)) • φ` in column two. -/
private def cyclicTotalPeriodicityHomotopy (φ : cyclicCocycles R A M n) :
    cyclicTotalCochains R A M (n + 1) :=
  ⟨Pi.single (n + 1) (cyclicRowHomotopySum R A M (n + 1) (barCoboundary R A M n φ.1.1)) +
      Pi.single n ((n + 2 : R) • φ.1.1),
    add_mem (single_mem_cyclicTotalCochains le_rfl _)
      (single_mem_cyclicTotalCochains (Nat.le_succ n) _)⟩

/-- **Cochain comparison between `S₀` and the bicomplex shift.** For every cyclic `n`-cocycle `φ`,
the sum of `S₀ φ` in column zero and `((n + 1) * (n + 2)) • φ` in column two is a total
coboundary. -/
theorem exists_cyclicTotalDifferential_eq_cyclicCocyclesPeriodicity_add
    (φ : cyclicCocycles R A M n) :
    ∃ z : cyclicTotalCochains R A M (n + 1),
      cyclicTotalDifferential R A M (n + 1) z =
        cyclicCochainsToTotal R A M (n + 2) (cyclicCocyclesPeriodicity R A M n φ).1 +
          ((n + 1 : R) * (n + 2 : R)) •
            cyclicTotalPeriodicity R A M n (cyclicCochainsToTotal R A M n φ.1) := by
  refine ⟨cyclicTotalPeriodicityHomotopy φ, Subtype.ext (funext fun q ↦ ?_)⟩
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Pi.add_apply, Pi.smul_apply,
    coe_cyclicCochainsToTotal_apply, coe_cyclicTotalPeriodicity_apply,
    coe_cyclicCocyclesPeriodicity_apply]
  obtain hq | rfl | rfl | rfl | hq :
      q < n ∨ q = n ∨ q = n + 1 ∨ q = n + 2 ∨ n + 2 < q := by omega
  · rw [Pi.single_eq_of_ne (by omega), Pi.single_eq_of_ne hq.ne, smul_zero, add_zero]
    cases q with
    | zero =>
      simp [cyclicTotalPeriodicityHomotopy, Pi.single_eq_of_ne (show 0 ≠ n by omega)]
    | succ k =>
      simp [cyclicTotalPeriodicityHomotopy,
        Pi.single_eq_of_ne (show k ≠ n + 1 by omega),
        Pi.single_eq_of_ne (show k ≠ n by omega),
        Pi.single_eq_of_ne (show k + 1 ≠ n + 1 by omega),
        Pi.single_eq_of_ne (show k + 1 ≠ n by omega)]
  · rw [Pi.single_eq_of_ne (by omega), Pi.single_eq_same, zero_add]
    cases q with
    | zero =>
      rw [cyclicTotalDifferential_apply_zero,
        cyclicBicomplexHorizontal_of_odd (show Odd (0 + 1) from odd_one)]
      simp only [cyclicTotalPeriodicityHomotopy, Pi.add_apply,
        Pi.single_eq_of_ne (show 0 ≠ 0 + 1 by omega), Pi.single_eq_same, zero_add]
      rw [map_smul, cyclicNorm_apply_of_mem_cyclicCochains φ.1.2, smul_smul, mul_comm]
    | succ k =>
      have hcol : k + 1 + 1 - (k + 1) = 1 := by omega
      rw [cyclicTotalDifferential_apply_succ, hcol, cyclicBicomplexHorizontal_of_odd odd_one]
      simp only [cyclicTotalPeriodicityHomotopy, Pi.add_apply,
        Pi.single_eq_of_ne (show k ≠ k + 1 + 1 by omega),
        Pi.single_eq_of_ne (show k ≠ k + 1 by omega),
        Pi.single_eq_of_ne (show k + 1 ≠ k + 1 + 1 by omega),
        Pi.single_eq_same, add_zero, zero_add, map_zero]
      rw [map_smul, cyclicNorm_apply_of_mem_cyclicCochains φ.1.2, smul_smul, mul_comm]
  · rw [Pi.single_eq_of_ne (by omega), Pi.single_eq_of_ne (by omega), smul_zero, add_zero,
      cyclicTotalDifferential_apply_succ]
    have h₁ : n + 1 - n = 1 := by omega
    rw [h₁, Nat.sub_self, cyclicBicomplexVertical_of_odd odd_one,
      cyclicBicomplexHorizontal_of_even Even.zero]
    simp only [cyclicTotalPeriodicityHomotopy, Pi.add_apply,
      Pi.single_eq_of_ne (show n ≠ n + 1 by omega),
      Pi.single_eq_of_ne (show n + 1 ≠ n by omega),
      Pi.single_eq_same, zero_add, add_zero, LinearMap.neg_apply, map_smul]
    rw [one_sub_cyclicOperator_apply_cyclicRowHomotopySum,
      ← LinearMap.comp_apply (cyclicNorm R A M (n + 1)), ← hochschildCoboundary_comp_cyclicNorm,
      LinearMap.comp_apply, cyclicNorm_apply_of_mem_cyclicCochains φ.1.2, map_smul,
      (mem_cyclicCocycles_iff R A M).1 φ.2, smul_zero, sub_zero,
      show ((n + 1 : ℕ) + 1 : R) = (n + 2 : R) by push_cast; ring, smul_neg, neg_add_cancel]
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne (by omega), smul_zero, add_zero,
      cyclicTotalDifferential_apply_succ, Nat.sub_self, cyclicBicomplexVertical_of_even Even.zero]
    simp only [cyclicTotalPeriodicityHomotopy, Pi.add_apply,
      Pi.single_eq_of_ne (show n + 1 ≠ n by omega),
      Pi.single_eq_of_ne (show n + 1 + 1 ≠ n + 1 by omega),
      Pi.single_eq_of_ne (show n + 1 + 1 ≠ n by omega),
      Pi.single_eq_same, add_zero, map_zero]
    exact hochschildCoboundary_cyclicRowHomotopySum_barCoboundary_of_mem_cyclicCocycles φ.2
  · rw [Pi.single_eq_of_ne hq.ne', Pi.single_eq_of_ne (by omega), smul_zero, add_zero]
    exact coe_cyclicTotalCochains_apply_of_lt _ hq

/-- In the cohomology of the total cyclic bicomplex over any commutative ring `R`, the class of
`S₀ φ` in column zero equals `-((n + 1) * (n + 2))` times the bicomplex periodicity map applied to
the class of `φ`. -/
theorem cyclicTotalHomologyMk_cyclicCocyclesPeriodicity (φ : cyclicCocycles R A M n) :
    cyclicTotalHomologyMk R A M (n + 2)
        ⟨_, cyclicCochainsToTotal_mem_ker (cyclicCocyclesPeriodicity R A M n φ)⟩ =
      -((n + 1 : R) * (n + 2 : R)) •
        cyclicTotalHomologyPeriodicity R A M n
          (cyclicTotalHomologyMk R A M n ⟨_, cyclicCochainsToTotal_mem_ker φ⟩) := by
  rw [cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk, neg_smul, eq_neg_iff_add_eq_zero,
    ← map_smul, ← map_add, cyclicTotalHomologyMk_succ_eq_zero_iff]
  exact exists_cyclicTotalDifferential_eq_cyclicCocyclesPeriodicity_add φ

end TotalHomotopy

/-! ### Comparison on cyclic cohomology and exactness of `HC^m →S HC^{m+2} →I HH^{m+2}` -/

section CyclicCohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

variable {R A M} in
/-- Including cyclic cochains into the total complex sends `[S₀ φ]` to `-((n + 1) * (n + 2))` times
the bicomplex periodicity map on `[φ]`, over any commutative ring `R`. -/
theorem homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity {n : ℕ}
    (φ : cyclicCocycles R A M n) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2)
        (cyclicCohomology.mk R A M (n + 2) (cyclicCocyclesPeriodicity R A M n φ)) =
      -((n + 1 : R) * (n + 2 : R)) •
        cyclicTotalHomologyPeriodicity R A M n
          (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n
            (cyclicCohomology.mk R A M n φ)) := by
  rw [homologyMap_cyclicCochainComplexToTotal_mk, homologyMap_cyclicCochainComplexToTotal_mk,
    cyclicTotalHomologyMk_cyclicCocyclesPeriodicity]

namespace cyclicCohomology

section Rational

variable [Algebra ℚ R]

/-- Under the quasi-isomorphism `cyclicCochainComplexToTotal`, Connes' periodicity map on cyclic
cohomology corresponds to `-((n + 1) * (n + 2))` times the periodicity map of the total cyclic
bicomplex. -/
@[reassoc, elementwise]
theorem periodicity_comp_homologyMap_cyclicCochainComplexToTotal (n : ℕ) :
    periodicity R A M n ≫
        HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (n + 2) =
      -((n + 1 : R) * (n + 2 : R)) •
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n ≫
          cyclicTotalHomologyPeriodicity R A M n) := by
  refine ModuleCat.hom_ext <| linearMap_ext <| LinearMap.ext fun φ ↦ ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_smul, LinearMap.comp_apply,
    LinearMap.smul_apply, periodicity_mk]
  exact homologyMap_cyclicCochainComplexToTotal_mk_cyclicCocyclesPeriodicity φ

/-- The composite `I ∘ S : HCⁿ(A; M) → HCⁿ⁺²(A; M) → HHⁿ⁺²(A, Hom_R(A, M))` vanishes. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem periodicity_comp_toHochschild (n : ℕ) :
    periodicity R A M n ≫ toHochschild R A M (n + 2) = 0 := by
  rw [← homologyMap_cyclicCochainComplexToTotal_comp_homologyMap_cyclicTotalComplexToHochschild,
    periodicity_comp_homologyMap_cyclicCochainComplexToTotal_assoc,
    Linear.smul_comp, Category.assoc,
    cyclicTotalHomologyPeriodicity_comp_homologyMap_cyclicTotalComplexToHochschild,
    Limits.comp_zero, smul_zero]

/-- **Exactness of `HCᵐ →S HCᵐ⁺² →I HHᵐ⁺²`.** For a unital algebra over a ring containing `ℚ`, a
cyclic cohomology class in degree `m + 2` lies in the image of Connes' periodicity map `S` if and
only if its image under `I : HCᵐ⁺² → HHᵐ⁺²` vanishes. -/
theorem exact_periodicity_toHochschild (m : ℕ) :
    Function.Exact (periodicity R A M m) (toHochschild R A M (m + 2)) := by
  have hbij₀ := bijective_homologyMap_cyclicCochainComplexToTotal R A M m
  have hbij₂ := bijective_homologyMap_cyclicCochainComplexToTotal R A M (m + 2)
  have hu : IsUnit (-((m + 1 : R) * (m + 2 : R))) := by
    simpa using ((isUnit_natCast_add_one (K := R) m).mul
      (isUnit_natCast_add_of_ne_zero (K := R) m two_ne_zero)).neg
  intro x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hx' : HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)
        (HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) (m + 2) x) = 0 := by
      rwa [← ModuleCat.comp_apply,
        homologyMap_cyclicCochainComplexToTotal_comp_homologyMap_cyclicTotalComplexToHochschild]
    obtain ⟨c, hc⟩ :=
      (exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild R A M m _).1
        hx'
    obtain ⟨y, rfl⟩ := hbij₀.2 c
    refine ⟨(↑hu.unit⁻¹ : R) • y, hbij₂.1 (hu.smul_left_cancel.1 ?_)⟩
    rw [map_smul, map_smul, smul_smul, hu.mul_val_inv, one_smul,
      periodicity_comp_homologyMap_cyclicCochainComplexToTotal_apply, ← neg_smul, hc]
  · rintro ⟨y, rfl⟩
    exact periodicity_comp_toHochschild_apply R A M m y

end Rational

end cyclicCohomology

end CyclicCohomology

end TauCeti
