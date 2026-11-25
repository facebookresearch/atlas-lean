/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexPairCoordinates
public import MathlibExt.Algebra.Homology.KoszulComplexPairEuler
public import MathlibExt.Algebra.Homology.ElementEuler
public import MathlibExt.Algebra.Homology.ElementEulerPrimeFiltration
import Mathlib.Tactic.Ring

/-!
# Two-generator Koszul homology after a regular first element

When multiplication by `f` is injective, degree-one homology of the Koszul
complex on `(f,g)` identifies with the kernel of multiplication by `g` on
`R/(f)`.  The construction is first carried out on the explicit coordinate
short complex.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace KoszulComplex

universe u

variable (R : Type u) [CommRing R]

/-- Cycles in the coordinate degree-one two-generator Koszul complex. -/
abbrev pairCoordinateCycles (f g : R) :=
  LinearMap.ker (familyFunctional R (pairFamily R f g))

/-- Coordinate top boundary, with codomain restricted to degree-one cycles. -/
noncomputable def pairCoordinateToCycles (f g : R) :
    R →ₗ[R] pairCoordinateCycles R f g :=
  (LinearMap.toSpanSingleton R (Fin 2 → R)
    (pairTopBoundaryVector R f g)).codRestrict _ fun c => by
      rw [LinearMap.mem_ker]
      simp [familyFunctional, Fintype.linearCombination_apply,
        Fin.sum_univ_two]
      ring

@[simp]
theorem pairCoordinateToCycles_apply (f g c : R) (j : Fin 2) :
    ((pairCoordinateToCycles R f g c : pairCoordinateCycles R f g) :
      Fin 2 → R) j = c * pairTopBoundaryVector R f g j :=
  rfl

/-- Degree-one coordinate homology as cycles modulo top boundaries. -/
abbrev pairCoordinateHomology (f g : R) :=
  pairCoordinateCycles R f g ⧸
    LinearMap.range (pairCoordinateToCycles R f g)

/-- Kernel of multiplication by `g` on `R/(f)`. -/
abbrev pairQuotientKernel (f g : R) :=
  LinearMap.ker (LinearMap.lsmul R (R ⧸ Ideal.span {f}) g)

/-- A degree-one cycle maps to its second coordinate modulo `f`. -/
noncomputable def pairCycleToQuotientKernel (f g : R) :
    pairCoordinateCycles R f g →ₗ[R] pairQuotientKernel R f g := by
  let I := Ideal.span ({f} : Set R)
  let q : pairCoordinateCycles R f g →ₗ[R] (R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp
      ((LinearMap.proj 1).comp
        (pairCoordinateCycles R f g).subtype)
  apply q.codRestrict (pairQuotientKernel R f g)
  intro x
  rw [LinearMap.mem_ker]
  change Ideal.Quotient.mk I (g * x.1 1) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hx := LinearMap.mem_ker.mp x.property
  simp [familyFunctional, Fintype.linearCombination_apply,
    Fin.sum_univ_two] at hx
  refine ⟨-x.1 0, ?_⟩
  linear_combination hx

@[simp]
theorem pairCycleToQuotientKernel_apply (f g : R)
    (x : pairCoordinateCycles R f g) :
    ((pairCycleToQuotientKernel R f g x : pairQuotientKernel R f g) :
      R ⧸ Ideal.span ({f} : Set R)) =
        Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (x.1 1) :=
  by
    change (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set R))).toLinearMap
      (x.1 1) = _
    rfl

/-- Top boundaries map to zero in the quotient kernel. -/
theorem pairCycleToQuotientKernel_comp_toCycles (f g : R) :
    (pairCycleToQuotientKernel R f g).comp
      (pairCoordinateToCycles R f g) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  simp only [LinearMap.comp_apply, pairCycleToQuotientKernel_apply,
    pairCoordinateToCycles_apply, pairTopBoundaryVector_one,
    LinearMap.zero_apply, Submodule.coe_zero]
  change Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (c * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨c, by ring⟩

/-- The cycle map descends to coordinate degree-one homology. -/
noncomputable def pairCoordinateHomologyToQuotientKernel (f g : R) :
    pairCoordinateHomology R f g →ₗ[R] pairQuotientKernel R f g :=
  (LinearMap.range (pairCoordinateToCycles R f g)).liftQ
    (pairCycleToQuotientKernel R f g)
    (LinearMap.range_le_ker_iff.mpr
      (pairCycleToQuotientKernel_comp_toCycles R f g))

@[simp]
theorem pairCoordinateHomologyToQuotientKernel_mk (f g : R)
    (x : pairCoordinateCycles R f g) :
    pairCoordinateHomologyToQuotientKernel R f g
        (Submodule.Quotient.mk x) =
      pairCycleToQuotientKernel R f g x :=
  rfl

/-- The coordinate degree-one homology map is bijective when `f` acts
injectively. -/
theorem pairCoordinateHomologyToQuotientKernel_bijective
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    Function.Bijective (pairCoordinateHomologyToQuotientKernel R f g) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro x hx
    have hxOne : x.1 1 ∈ Ideal.span ({f} : Set R) := by
      have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      rw [pairCycleToQuotientKernel_apply] at hx'
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx'
    rw [Ideal.mem_span_singleton] at hxOne
    obtain ⟨c, hc⟩ := hxOne
    have hcycle : x.1 0 * f + x.1 1 * g = 0 := by
      simpa only [familyFunctional, Fintype.linearCombination_apply,
        Fin.sum_univ_two, pairFamily_zero, pairFamily_one,
        smul_eq_mul] using LinearMap.mem_ker.mp x.property
    rw [hc] at hcycle
    have hxZero : x.1 0 = -g * c := by
      apply hf
      change f * x.1 0 = f * (-g * c)
      linear_combination hcycle
    refine ⟨c, ?_⟩
    apply Subtype.ext
    funext j
    fin_cases j
    · simp [hxZero, mul_comm]
    · simp [hc, mul_comm]
  · intro y
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective y.1
    have hy := LinearMap.mem_ker.mp y.property
    have hy' : Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (g * b) = 0 := by
      calc
        Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (g * b) =
            g • Ideal.Quotient.mk (Ideal.span ({f} : Set R)) b := rfl
        _ = g • y.1 := congrArg (fun z => g • z) hb
        _ = 0 := hy
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hy'
    obtain ⟨a, ha⟩ := hy'
    let v : Fin 2 → R := pairFamily R (-a) b
    have hv : v ∈ pairCoordinateCycles R f g := by
      rw [LinearMap.mem_ker]
      simp only [v, familyFunctional, Fintype.linearCombination_apply,
        Fin.sum_univ_two, pairFamily_zero, pairFamily_one]
      simp only [smul_eq_mul]
      linear_combination ha
    refine ⟨Submodule.Quotient.mk ⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    rw [pairCoordinateHomologyToQuotientKernel_mk,
      pairCycleToQuotientKernel_apply]
    exact hb

/-- Coordinate degree-one homology is linearly equivalent to the quotient
multiplication kernel. -/
noncomputable def pairCoordinateHomologyEquivQuotientKernel
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    pairCoordinateHomology R f g ≃ₗ[R] pairQuotientKernel R f g :=
  LinearEquiv.ofBijective
    (pairCoordinateHomologyToQuotientKernel R f g)
    (pairCoordinateHomologyToQuotientKernel_bijective R f g hf)

/-- The cokernel of multiplication by `g` on `R/(f)` is the quotient
`R/(f,g)`. -/
noncomputable def pairQuotientCokernelEquiv (f g : R) :
    ((R ⧸ Ideal.span ({f} : Set R)) ⧸
        (LinearMap.lsmul R (R ⧸ Ideal.span ({f} : Set R)) g).range) ≃ₗ[R]
      R ⧸ Ideal.span ({f, g} : Set R) := by
  let I := Ideal.span ({f} : Set R)
  let J := Ideal.span ({g} : Set R)
  have hmap : J.map (Ideal.Quotient.mkₐ R I) =
      Ideal.span {(Ideal.Quotient.mkₐ R I) g} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
  have hrange :
      (LinearMap.lsmul R (R ⧸ I) g).range =
        (J.map (Ideal.Quotient.mkₐ R I)).restrictScalars R := by
    rw [hmap]
    ext x
    rw [Module.range_lsmul_eq_smul_top,
      Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and]
    have hmem : x ∈
        (Ideal.span {(Ideal.Quotient.mkₐ R I) g}).restrictScalars R ↔
      x ∈ Ideal.span {(Ideal.Quotient.mkₐ R I) g} := Iff.rfl
    rw [hmem, Ideal.mem_span_singleton]
    constructor <;> rintro ⟨y, hy⟩ <;>
      exact ⟨y, by simpa [Algebra.smul_def] using hy.symm⟩
  have hsup : I ⊔ J = Ideal.span ({f, g} : Set R) := by
    rw [Ideal.span_insert]
  exact Submodule.quotEquivOfEq _ _ hrange ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R
      (J.map (Ideal.Quotient.mkₐ R I)) ≪≫ₗ
        (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv ≪≫ₗ
          (Ideal.quotientEquivAlgOfEq R hsup).toLinearEquiv

/-- The abstract homology of the coordinate short complex is its explicit
cycle quotient. -/
noncomputable def pairCoordinateHomologyIso (f g : R) :
    (pairCoordinateShortComplex R f g).homology ≅
      ModuleCat.of R (pairCoordinateHomology R f g) :=
  (pairCoordinateShortComplex R f g).moduleCatHomologyIso

/-- Abstract degree-one two-generator Koszul homology identifies with the
kernel of multiplication by `g` on `R/(f)` when `f` acts injectively. -/
noncomputable def pairHomologyOneIsoQuotientKernel
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    (familyComplex R (pairFamily R f g)).homology 1 ≅
      ModuleCat.of R (pairQuotientKernel R f g) :=
  ShortComplex.homologyMapIso (pairCoordinateShortComplexIso R f g) ≪≫
    pairCoordinateHomologyIso R f g ≪≫
      (pairCoordinateHomologyEquivQuotientKernel R f g hf).toModuleIso

/-- Length form of the regular-first-generator degree-one homology
identification. -/
theorem pair_homology_one_length_eq_quotientKernel
    (f g : R) (hf : Function.Injective (LinearMap.lsmul R R f)) :
    Module.length R
        ((familyComplex R (pairFamily R f g)).homology 1) =
      Module.length R (pairQuotientKernel R f g) :=
  (pairHomologyOneIsoQuotientKernel R f g hf).toLinearEquiv.length_eq

/-- Finite-length data for multiplication by `g` on `R/(f)`, obtained from
the two-generator quotient and regularity of `f`. -/
theorem pairElementEulerFiniteLength
    [IsNoetherianRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    Module.ElementEulerFiniteLength R (R ⧸ Ideal.span ({f} : Set R)) g where
  kernel_ne_top := by
    rw [← pair_homology_one_length_eq_quotientKernel R f g hf]
    exact pairHomology_length_ne_top_of_quotient R f g 1 hquot
  cokernel_ne_top := by
    rw [(pairQuotientCokernelEquiv R f g).length_eq]
    exact hquot

/-- Intrinsic one-element Euler finiteness data on the first principal
quotient. -/
theorem pairQuotientElementEulerFiniteLength
    [IsNoetherianRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    Module.ElementEulerFiniteLength
      (R ⧸ Ideal.span ({f} : Set R))
      (R ⧸ Ideal.span ({f} : Set R))
      (algebraMap R (R ⧸ Ideal.span ({f} : Set R)) g) :=
  (pairElementEulerFiniteLength R f g hf hquot).changeRingOfSurjective
    R (R ⧸ Ideal.span ({f} : Set R)) g Ideal.Quotient.mk_surjective

/-- Transport the intrinsic quotient Euler data across a ring equivalence. -/
theorem pairRingEquivElementEulerFiniteLength
    [IsNoetherianRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤)
    {B : Type u} [CommRing B]
    (e : (R ⧸ Ideal.span ({f} : Set R)) ≃+* B) :
    Module.ElementEulerFiniteLength B B
      (e (algebraMap R (R ⧸ Ideal.span ({f} : Set R)) g)) :=
  (pairQuotientElementEulerFiniteLength R f g hf hquot).ringEquiv e _

/-- With a regular first generator, the two-generator Koszul Euler
characteristic is the one-element Euler characteristic on the first
quotient. -/
theorem pairEulerCharacteristicOfQuotient_eq_elementEuler
    [IsNoetherianRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤) :
    pairEulerCharacteristicOfQuotient R f g hquot =
      Module.elementEulerCharacteristic R
        (R ⧸ Ideal.span ({f} : Set R)) g
        (pairElementEulerFiniteLength R f g hf hquot) := by
  have htwo := pair_homology_two_isZero R f g hf
  have htwoLength : Module.length R
      ((familyComplex R (pairFamily R f g)).homology 2) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ModuleCat.isZero_iff_subsingleton.mp htwo
  rw [pairEulerCharacteristicOfQuotient_eq,
    pair_homology_one_length_eq_quotientKernel R f g hf, htwoLength]
  unfold Module.elementEulerCharacteristic
  rw [(pairQuotientCokernelEquiv R f g).length_eq]
  simp

/-- With a regular first generator, the pair Euler characteristic becomes
the intrinsic one-element Euler characteristic after any identification of
the first principal quotient with another ring. -/
theorem pairEulerCharacteristicOfQuotient_eq_ringEquivElementEuler
    [IsNoetherianRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤)
    {B : Type u} [CommRing B]
    (e : (R ⧸ Ideal.span ({f} : Set R)) ≃+* B) :
    pairEulerCharacteristicOfQuotient R f g hquot =
      Module.elementEulerCharacteristic B B
        (e (algebraMap R (R ⧸ Ideal.span ({f} : Set R)) g))
        (pairRingEquivElementEulerFiniteLength R f g hf hquot e) := by
  let hA := pairElementEulerFiniteLength R f g hf hquot
  let hQ := pairQuotientElementEulerFiniteLength R f g hf hquot
  calc
    pairEulerCharacteristicOfQuotient R f g hquot =
        Module.elementEulerCharacteristic R
          (R ⧸ Ideal.span ({f} : Set R)) g hA :=
      pairEulerCharacteristicOfQuotient_eq_elementEuler R f g hf hquot
    _ = Module.elementEulerCharacteristic
        (R ⧸ Ideal.span ({f} : Set R))
        (R ⧸ Ideal.span ({f} : Set R))
        (algebraMap R (R ⧸ Ideal.span ({f} : Set R)) g) hQ :=
      Module.elementEulerCharacteristic_changeRingOfSurjective
        R (R ⧸ Ideal.span ({f} : Set R)) g
          Ideal.Quotient.mk_surjective hA
    _ = Module.elementEulerCharacteristic B B
        (e (algebraMap R (R ⧸ Ideal.span ({f} : Set R)) g))
        (pairRingEquivElementEulerFiniteLength R f g hf hquot e) :=
      Module.elementEulerCharacteristic_ringEquiv e _ hQ

open Classical in
/-- The regular two-generator Koszul Euler characteristic admits the explicit
one-dimensional local prime-filtration formula. -/
theorem exists_pairEulerPrimeDecomposition
    [IsNoetherianRing R] [IsLocalRing R] (f g : R)
    (hf : Function.Injective (LinearMap.lsmul R R f))
    (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hquot : Module.length R (R ⧸ Ideal.span ({f, g} : Set R)) ≠ ⊤)
    (hdim : Module.supportDim R (R ⧸ Ideal.span ({f} : Set R)) ≤ 1) :
    ∃ d : Module.ElementEulerPrimeDecomposition R
        (R ⧸ Ideal.span ({f} : Set R)) g,
      pairEulerCharacteristicOfQuotient R f g hquot =
        ∑ factor ∈ d.factors.toFinset,
          ((Module.length (Localization.AtPrime factor.prime.asIdeal)
            (LocalizedModule factor.prime.asIdeal.primeCompl
              (R ⧸ Ideal.span ({f} : Set R)))).toNat : ℤ) *
              ((if g ∈ factor.prime.asIdeal then 0 else
                (Module.length R
                  ((R ⧸ factor.prime.asIdeal) ⧸
                    (LinearMap.lsmul R (R ⧸ factor.prime.asIdeal) g).range)).toNat :
                  ℕ) : ℤ) := by
  let hElement := pairElementEulerFiniteLength R f g hf hquot
  obtain ⟨d⟩ := Module.exists_elementEulerPrimeDecomposition R
    (R ⧸ Ideal.span ({f} : Set R)) g hElement.cokernel_ne_top
  refine ⟨d, ?_⟩
  calc
    pairEulerCharacteristicOfQuotient R f g hquot =
        Module.elementEulerCharacteristic R
          (R ⧸ Ideal.span ({f} : Set R)) g hElement :=
      pairEulerCharacteristicOfQuotient_eq_elementEuler R f g hf hquot
    _ = _ := by
      simpa only using
        d.eq_sum_localizedLength_mul_ite_of_supportDim_le_one R hg hdim

end KoszulComplex
