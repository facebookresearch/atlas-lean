/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.CoefficientCoordinates

/-!
# The leading Koszul differential of enveloping chains

Let `R` be a commutative ring and let `L` have an ordered `R`-basis `b : I → L`. Exterior-
basis coordinates and PBW polynomial coordinates identify degree-`n` regular-coefficient
chains with finitely supported families of polynomials indexed by `n`-element subsets of `I`.

In these coordinates the action boundary deletes one exterior basis index and multiplies its
polynomial coefficient by the corresponding variable, with sign `(-1)^i`. The difference from
the polynomial Koszul differential consists of the bracket boundary and the lower-degree PBW
right-multiplication defects. It therefore sends total filtration stage `p` into stage `p-1`.

Reference: Weibel, *An Introduction to Homological Algebra*, Chapter 7.
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
local notation:max "F" n:max => (Set.powersetCard I n →₀ P)

private abbrev erasedExteriorIndex (n : ℕ) (s : Set.powersetCard I (n + 1))
    (i : Fin (n + 1)) : Set.powersetCard I n :=
  KoszulComplex.polynomialEraseIndex n s i

private theorem exteriorBasis_erased (b : Module.Basis I R L) (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (i : Fin (n + 1)) :
    b.exteriorPower n (erasedExteriorIndex n s i) =
      exteriorPower.ιMulti R n
        (fun q => b (Set.powersetCard.ofFinEmbEquiv.symm s (i.succAbove q))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    erasedExteriorIndex, KoszulComplex.polynomialEraseIndex, Equiv.symm_apply_apply]
  rfl

private theorem polynomialCoefficientDifferential_single (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (p : P) :
    KoszulComplex.polynomialCoefficientDifferential R n (Finsupp.single s p) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        Finsupp.single (erasedExteriorIndex n s i)
          (p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) :=
  KoszulComplex.polynomialCoefficientDifferential_single R n s p

private theorem envelopingAction_coordinates_basis (b : Module.Basis I R L) (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (u : regularCoefficients R L) :
    envelopingCoefficientCoordinates R L b n
        (coefficientActionBoundary R L (regularCoefficients R L) n
          (b.exteriorPower (n + 1) s ⊗ₜ[R] u)) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        Finsupp.single (erasedExteriorIndex n s i)
          (polynomialCoordinates b
            (u * UniversalEnvelopingAlgebra.ι R
              (b (Set.powersetCard.ofFinEmbEquiv.symm s i)))) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    envelopingActionBoundary_apply_ιMulti_tmul, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1 : R) ^ i.val • envelopingCoefficientCoordinates R L b n
    (exteriorPower.ιMulti R n
      (fun q => b (Set.powersetCard.ofFinEmbEquiv.symm s (i.succAbove q))) ⊗ₜ[R]
      (u * UniversalEnvelopingAlgebra.ι R (b (Set.powersetCard.ofFinEmbEquiv.symm s i)))) = _
  rw [← exteriorBasis_erased, envelopingCoefficientCoordinates_basis_tmul]

/-- The differential defect of the enveloping-to-polynomial coordinates.

For an ordered basis `b`, let `c_n` be the exterior/PBW coefficient coordinates. This map is
`c_n ∘ d_CE - d_Koszul ∘ c_(n+1)`, from degree-`n+1` regular-coefficient chains to polynomial
families indexed by `n`-element basis subsets. -/
def envelopingKoszulDefect (b : Module.Basis I R L) (n : ℕ) :
    (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L →ₗ[R] F n :=
  (envelopingCoefficientCoordinates R L b n).toLinearMap.comp
      (coefficientDifferential R L (regularCoefficients R L) n) -
    (KoszulComplex.polynomialCoefficientDifferential R n).comp
      (envelopingCoefficientCoordinates R L b (n + 1)).toLinearMap

private theorem envelopingKoszulDefect_basis (b : Module.Basis I R L) (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (u : regularCoefficients R L) :
    envelopingKoszulDefect R L b n (b.exteriorPower (n + 1) s ⊗ₜ[R] u) =
      envelopingCoefficientCoordinates R L b n
          (differential R L n (b.exteriorPower (n + 1) s) ⊗ₜ[R] u) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          Finsupp.single (erasedExteriorIndex n s i)
            (rightMultiplicationDefect b (Set.powersetCard.ofFinEmbEquiv.symm s i) u) := by
  rw [envelopingKoszulDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, coefficientDifferential_eq_bracket_add_action,
    LinearMap.add_apply, LinearMap.rTensor_tmul, map_add]
  change envelopingCoefficientCoordinates R L b n
      (differential R L n (b.exteriorPower (n + 1) s) ⊗ₜ[R] u) +
    envelopingCoefficientCoordinates R L b n
      (coefficientActionBoundary R L (regularCoefficients R L) n
        (b.exteriorPower (n + 1) s ⊗ₜ[R] u)) -
    KoszulComplex.polynomialCoefficientDifferential R n
      (envelopingCoefficientCoordinates R L b (n + 1) (b.exteriorPower (n + 1) s ⊗ₜ[R] u)) = _
  rw [envelopingAction_coordinates_basis, envelopingCoefficientCoordinates_basis_tmul,
    polynomialCoefficientDifferential_single, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← smul_sub, ← Finsupp.single_sub]
  rfl

private theorem envelopingKoszulDefect_basis_mem (b : Module.Basis I R L)
    (n q : ℕ) (s : Set.powersetCard I (n + 1)) (u : regularCoefficients R L)
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    envelopingKoszulDefect R L b n (b.exteriorPower (n + 1) s ⊗ₜ[R] u) ∈
      KoszulComplex.polynomialCoefficientFiltration R n (q + n) := by
  rw [envelopingKoszulDefect_basis]
  apply (KoszulComplex.polynomialCoefficientFiltration R n (q + n)).add_mem
  · apply envelopingCoefficientCoordinates_mem_filtration R L b n (q + n)
    exact tmul_mem_envelopingFiltration R L (q + n) n q
      (differential R L n (b.exteriorPower (n + 1) s)) u le_rfl hu
  · apply (KoszulComplex.polynomialCoefficientFiltration R n (q + n)).sum_mem
    intro i hi
    apply (KoszulComplex.polynomialCoefficientFiltration R n (q + n)).smul_mem
    apply KoszulComplex.polynomialCoefficientFiltration_single R n (q + n) (by omega)
      (erasedExteriorIndex n s i)
    simpa only [Nat.add_sub_cancel] using
      rightMultiplicationDefect_mem_degree b
        (Set.powersetCard.ofFinEmbEquiv.symm s i) q hu

private theorem envelopingKoszulDefect_tmul_mem (b : Module.Basis I R L) (n q : ℕ)
    (x : ⋀[R]^(n + 1) L) (u : regularCoefficients R L)
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L q) :
    envelopingKoszulDefect R L b n (x ⊗ₜ[R] u) ∈
      KoszulComplex.polynomialCoefficientFiltration R n (q + n) := by
  rw [← (b.exteriorPower (n + 1)).linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul', map_sum, map_smul]
  apply (KoszulComplex.polynomialCoefficientFiltration R n (q + n)).sum_mem
  intro s hs
  apply (KoszulComplex.polynomialCoefficientFiltration R n (q + n)).smul_mem
  exact envelopingKoszulDefect_basis_mem R L b n q s u hu

/-- The lower total degree of the enveloping–Koszul defect.

For every ordered `R`-basis `b` and chain `z` in total enveloping filtration stage `p` of
degree `n+1`, the defect `c_n(d_CE z) - d_Koszul(c_(n+1) z)` lies in polynomial coefficient
filtration stage `p-1` of degree `n`. -/
theorem envelopingKoszulDefect_mem_lowerFiltration (b : Module.Basis I R L) (p n : ℕ)
    {z : (⋀[R]^(n + 1) L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p (n + 1)) :
    envelopingKoszulDefect R L b n z ∈
      KoszulComplex.polynomialCoefficientFiltration R n (p - 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, v, u, hq, hu, rfl⟩ := hz
      apply KoszulComplex.polynomialCoefficientFiltration_mono R n
        (show q + n ≤ p - 1 by omega)
      exact envelopingKoszulDefect_tmul_mem R L b n q (exteriorPower.ιMulti R (n + 1) v) u hu
  | zero =>
      rw [map_zero]
      exact (KoszulComplex.polynomialCoefficientFiltration R n (p - 1)).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (KoszulComplex.polynomialCoefficientFiltration R n (p - 1)).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (KoszulComplex.polynomialCoefficientFiltration R n (p - 1)).smul_mem r ih

end ChevalleyEilenberg
