/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.FilteredKoszulComparison

/-!
# Positive exactness from the total-degree enveloping filtration

Let L have a basis indexed by a linearly ordered type over a commutative ring R. Filter C_n =
⋀[R]^n L ⊗[R] U(L) by the sum of exterior degree n and enveloping coefficient degree. The
leading part of a positive-degree cycle is a polynomial-variable Koszul cycle in the
corresponding basis coordinates.

A lifted Koszul boundary corrects the cycle inside the same total stage, leaving its remainder
in stage p−1. Induction on the finite total stage produces a boundary of every positive-degree
cycle. The resulting freeness formulation assumes Module.Free R L and permits infinite bases.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace ChevalleyEilenberg

attribute [local instance] rightRegularLieRingModule rightRegularLieModule

open UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation:max "C" n:max => ((⋀[R]^n L) ⊗[R] regularCoefficients R L)
local notation:max "F" n:max => (Set.powersetCard I n →₀ P)

/-- Let R be a commutative ring, L an R-Lie algebra, U its universal enveloping algebra, ι its
Lie-generator map and ε : U →ₐ[R] R its augmentation. Give U the coefficient Lie action ⁅x,a⁆
= −a*ι(x), and put C_n = ⋀[R]^n L ⊗[R] U. Let I be a linearly ordered index type and b :
Module.Basis I R L. Let F_p C_n be the R-submodule spanned by decomposable words w ⊗ a with a
in UEA degree q and q + n ≤ p. For p, k : ℕ and z : C_(k+1) with z ∈ F_p C_(k+1) and
coefficientDifferential k z = 0, there exists w : C_(k+2) in F_p C_(k+2) such that z −
coefficientDifferential (k + 1) w lies in F_(p−1) C_(k+1). The subtraction p−1 is
natural-number subtraction. -/
theorem enveloping_cycle_correction (b : Module.Basis I R L) (p k : ℕ)
    (z : C (k + 1)) (hz : z ∈ envelopingFiltration R L p (k + 1))
    (hcycle : coefficientDifferential R L (regularCoefficients R L) k z = 0) :
    ∃ w : C (k + 2), w ∈ envelopingFiltration R L p (k + 2) ∧
      z - coefficientDifferential R L (regularCoefficients R L) (k + 1) w ∈
        envelopingFiltration R L (p - 1) (k + 1) := by
  classical
  by_cases hkp : k + 1 ≤ p
  · let c : F (k + 1) := envelopingCoefficientCoordinates R L b (k + 1) z
    have hc : c ∈ KoszulComplex.polynomialCoefficientFiltration R (k + 1) p :=
      envelopingCoefficientCoordinates_mem_filtration R L b (k + 1) p hz
    have hdifference := envelopingKoszulDefect_mem_lowerFiltration R L b p k hz
    have hdelta : KoszulComplex.polynomialCoefficientDifferential R k c ∈
        KoszulComplex.polynomialCoefficientFiltration R k (p - 1) := by
      have hneg : -KoszulComplex.polynomialCoefficientDifferential R k c ∈
          KoszulComplex.polynomialCoefficientFiltration R k (p - 1) := by
        have hDef : envelopingKoszulDefect R L b k z =
            -KoszulComplex.polynomialCoefficientDifferential R k c := by
          change envelopingCoefficientCoordinates R L b k
              (coefficientDifferential R L (regularCoefficients R L) k z) -
            KoszulComplex.polynomialCoefficientDifferential R k c = _
          rw [hcycle, map_zero, zero_sub]
        exact hDef ▸ hdifference
      simpa only [neg_neg] using
        (KoszulComplex.polynomialCoefficientFiltration R k (p - 1)).neg_mem hneg
    have hleadingCycle (d : ℕ) (hd : p - (k + 1) = d) :
        KoszulComplex.polynomialCoefficientDifferential R k
          (KoszulComplex.polynomialCoefficientHomogeneousPart R (k + 1) d c) = 0 := by
      have hzero := KoszulComplex.polynomialCoefficientHomogeneousPart_zero_of_filtration
        R k (p - 1) (d + 1) (by omega) hdelta
      exact (KoszulComplex.polynomialCoefficientHomogeneousPart_differential R k d c).symm.trans hzero
    cases hd : p - (k + 1) with
    | zero =>
        have hp : p = k + 1 := by omega
        have hzero := KoszulComplex.polynomialCoefficient_homogeneous_zero_cycle R k
          (KoszulComplex.polynomialCoefficientHomogeneousPart R (k + 1) 0 c)
          (hleadingCycle 0 hd)
          (KoszulComplex.polynomialCoefficientHomogeneousPart_isHomogeneous R (k + 1) 0 c)
        have hcbase : c ∈ KoszulComplex.polynomialCoefficientFiltration R (k + 1) (k + 1) := by
          simpa only [hp] using hc
        have hc0 : c = 0 :=
          (KoszulComplex.polynomialCoefficientHomogeneousPart_zero_eq_self R (k + 1) hcbase).symm.trans hzero
        have hz0 : z = 0 := by
          apply (envelopingCoefficientCoordinates R L b (k + 1)).injective
          rw [map_zero]
          exact hc0
        refine ⟨0, (envelopingFiltration R L p (k + 2)).zero_mem, ?_⟩
        rw [hz0, map_zero, sub_self]
        exact (envelopingFiltration R L (p - 1) (k + 1)).zero_mem
    | succ d =>
        let leading := KoszulComplex.polynomialCoefficientHomogeneousPart R (k + 1) (d + 1) c
        obtain ⟨wF, hwHom, hw⟩ := KoszulComplex.polynomialCoefficient_homogeneous_exact_cycles R k d
          leading (hleadingCycle (d + 1) hd)
          (KoszulComplex.polynomialCoefficientHomogeneousPart_isHomogeneous R (k + 1) (d + 1) c)
        have hp : p = d + (k + 2) := by omega
        have hwF : wF ∈ KoszulComplex.polynomialCoefficientFiltration R (k + 2) p := by
          rw [hp]
          exact KoszulComplex.polynomialCoefficient_mem_filtration_of_isHomogeneous R (k + 2) d wF hwHom
        let wC : C (k + 2) := (envelopingCoefficientCoordinates R L b (k + 2)).symm wF
        have hwC : wC ∈ envelopingFiltration R L p (k + 2) :=
          envelopingCoefficientCoordinates_symm_mem_filtration R L b (k + 2) p hwF
        have hwCoords : envelopingCoefficientCoordinates R L b (k + 2) wC = wF :=
          (envelopingCoefficientCoordinates R L b (k + 2)).apply_symm_apply wF
        have hnext := envelopingKoszulDefect_mem_lowerFiltration R L b p (k + 1) hwC
        have hcTop : c ∈ KoszulComplex.polynomialCoefficientFiltration R (k + 1)
            ((d + 1) + (k + 1)) := by
          have hdegree : p = (d + 1) + (k + 1) := by omega
          simpa only [hdegree] using hc
        have hremoved : c - leading ∈
            KoszulComplex.polynomialCoefficientFiltration R (k + 1) (p - 1) := by
          have h := KoszulComplex.polynomialCoefficient_sub_highest_mem_lower R (k + 1) d hcTop
          have hdegree : d + (k + 1) = p - 1 := by omega
          simpa only [hdegree] using h
        have hremaining : (c - leading) - envelopingKoszulDefect R L b (k + 1) wC ∈
            KoszulComplex.polynomialCoefficientFiltration R (k + 1) (p - 1) :=
          (KoszulComplex.polynomialCoefficientFiltration R (k + 1) (p - 1)).sub_mem hremoved hnext
        have hkoszul : KoszulComplex.polynomialCoefficientDifferential R (k + 1)
            (envelopingCoefficientCoordinates R L b (k + 2) wC) = leading := by
          rw [hwCoords]
          exact hw
        have hcoordinates : envelopingCoefficientCoordinates R L b (k + 1)
            (z - coefficientDifferential R L (regularCoefficients R L) (k + 1) wC) =
              (c - leading) - envelopingKoszulDefect R L b (k + 1) wC := by
          simp only [map_sub, envelopingKoszulDefect, LinearMap.sub_apply, LinearMap.comp_apply]
          change c - envelopingCoefficientCoordinates R L b (k + 1)
              (coefficientDifferential R L (regularCoefficients R L) (k + 1) wC) =
            (c - leading) -
              (envelopingCoefficientCoordinates R L b (k + 1)
                  (coefficientDifferential R L (regularCoefficients R L) (k + 1) wC) -
                KoszulComplex.polynomialCoefficientDifferential R (k + 1)
                  (envelopingCoefficientCoordinates R L b (k + 2) wC))
          rw [hkoszul]
          dsimp only [c]
          abel
        refine ⟨wC, hwC, ?_⟩
        apply (envelopingCoefficientCoordinates_mem_filtration_iff R L b (k + 1) (p - 1) _).mp
        rw [hcoordinates]
        exact hremaining
  · have hz0 : z = 0 := by
      rw [envelopingFiltration_eq_bot_of_lt R L p (k + 1) (Nat.lt_of_not_ge hkp),
        Submodule.mem_bot] at hz
      exact hz
    refine ⟨0, (envelopingFiltration R L p (k + 2)).zero_mem, ?_⟩
    rw [hz0, map_zero, sub_self]
    exact (envelopingFiltration R L (p - 1) (k + 1)).zero_mem

private theorem enveloping_exact_cycles_at_stage (b : Module.Basis I R L) (k p : ℕ) :
    ∀ z : C (k + 1), z ∈ envelopingFiltration R L p (k + 1) →
      coefficientDifferential R L (regularCoefficients R L) k z = 0 →
        ∃ w : C (k + 2), coefficientDifferential R L (regularCoefficients R L) (k + 1) w = z := by
  induction p with
  | zero =>
      intro z hz hcycle
      rw [envelopingFiltration_zero_succ R L k, Submodule.mem_bot] at hz
      subst z
      exact ⟨0, map_zero _⟩
  | succ p ih =>
      intro z hz hcycle
      obtain ⟨w, hw, hremaining⟩ := enveloping_cycle_correction R L b (p + 1) k z hz hcycle
      have hcycleRemaining : coefficientDifferential R L (regularCoefficients R L) k
          (z - coefficientDifferential R L (regularCoefficients R L) (k + 1) w) = 0 := by
        rw [map_sub, hcycle]
        have hsquare := LinearMap.congr_fun
          (coefficientDifferential_comp_differential R L (regularCoefficients R L) k) w
        have hzero : coefficientDifferential R L (regularCoefficients R L) k
            (coefficientDifferential R L (regularCoefficients R L) (k + 1) w) = 0 := by
          simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hsquare
        rw [hzero, sub_self]
      obtain ⟨w₀, hw₀⟩ := ih
        (z - coefficientDifferential R L (regularCoefficients R L) (k + 1) w)
        (by simpa only [Nat.add_sub_cancel] using hremaining) hcycleRemaining
      refine ⟨w₀ + w, ?_⟩
      rw [map_add, hw₀, sub_add_cancel]

/-- Let R be a commutative ring, L an R-Lie algebra, U its universal enveloping algebra, ι its
Lie-generator map and ε : U →ₐ[R] R its augmentation. Give U the coefficient Lie action ⁅x,a⁆
= −a*ι(x), and put C_n = ⋀[R]^n L ⊗[R] U. Let I be a linearly ordered index type and b :
Module.Basis I R L. For k : ℕ and z : C_(k+1) with coefficientDifferential k z = 0, there
exists w : C_(k+2) satisfying coefficientDifferential (k + 1) w = z. The basis index type I
need not be finite. -/
theorem enveloping_exact_cycles (b : Module.Basis I R L) (k : ℕ) (z : C (k + 1))
    (hcycle : coefficientDifferential R L (regularCoefficients R L) k z = 0) :
    ∃ w : C (k + 2), coefficientDifferential R L (regularCoefficients R L) (k + 1) w = z := by
  obtain ⟨p, hp⟩ := envelopingFiltration_exhaustive R L (k + 1) z
  exact enveloping_exact_cycles_at_stage R L b k p z hp hcycle

/-- Let R be a commutative ring, L an R-Lie algebra, U its universal enveloping algebra, ι its
Lie-generator map and ε : U →ₐ[R] R its augmentation. Give U the coefficient Lie action ⁅x,a⁆
= −a*ι(x), and put C_n = ⋀[R]^n L ⊗[R] U. Assume Module.Free R L. For k : ℕ and z : C_(k+1)
killed by coefficientDifferential k, there exists w : C_(k+2) with coefficientDifferential (k
+ 1) w = z. -/
theorem enveloping_exact_cycles_of_free [Module.Free R L] (k : ℕ) (z : C (k + 1))
    (hcycle : coefficientDifferential R L (regularCoefficients R L) k z = 0) :
    ∃ w : C (k + 2), coefficientDifferential R L (regularCoefficients R L) (k + 1) w = z := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := linearOrderOfSTO WellOrderingRel
  exact enveloping_exact_cycles R L (Module.Free.chooseBasis R L) k z hcycle

end ChevalleyEilenberg
