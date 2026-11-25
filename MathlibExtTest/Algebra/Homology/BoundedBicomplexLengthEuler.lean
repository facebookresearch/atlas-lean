/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.BoundedBicomplexLengthEuler
public import MathlibExt.Algebra.Homology.FirstQuadrantEdge
public import MathlibExtTest.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import Mathlib.RingTheory.Artinian.Module

/-! An actual bounded integer bicomplex with infinite-length terms and nonzero first homology. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject BigOperators

namespace BoundedBicomplexLengthEulerTests

/-- The original free integer coefficient with its actual scalar action. -/
abbrev Z := NativeTorBoundaryTests.Z

/-- The original integral mod-two quotient coefficient. -/
abbrev Q := NativeTorBoundaryTests.Q

/-- The actual original vertical term family. -/
abbrev VObj (q : ℕ) : ModuleCat ℤ := match q with
  | 0 => Z
  | 1 => Z
  | .succ (.succ _) => 0

/-- A two-term zero-differential vertical complex with original integer terms. -/
abbrev V : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of VObj (fun _ => 0) (by intro q; simp)

/-- The actual original horizontal term family. -/
abbrev BObj (p : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := match p with
  | 0 => V
  | 1 => V
  | .succ (.succ _) => 0

/-- The original horizontal differential is twice the identity in the retained degree. -/
abbrev BDiff (p : ℕ) : BObj (p + 1) ⟶ BObj p := match p with
  | 0 => (2 : ℕ) • (𝟙 V)
  | .succ _ => 0

/-- The actual two-column bicomplex whose horizontal map is twice the identity. -/
abbrev B : HomologicalComplex₂ (ModuleCat ℤ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of BObj BDiff (by intro p; cases p <;> simp [BDiff])

theorem V_d_zero (i j : ℕ) : V.d i j = 0 := by
  change ChainComplex.of.d VObj (fun _ => 0) i j = 0
  dsimp only [ChainComplex.of.d]
  split_ifs <;> simp only [comp_zero]

/-- Canonical actual homology of the vertical zero differential is the original term. -/
def vHomologyIsoX (q : ℕ) : V.homology q ≅ V.X q :=
  (ShortComplex.HomologyData.ofZeros (V.sc q)
    (V_d_zero _ _) (V_d_zero _ _)).left.homologyIso

theorem integer_length_top : Module.length ℤ Z = ⊤ := by
  by_contra h
  have hfin : IsFiniteLength ℤ ℤ := Module.length_ne_top_iff.mp h
  have : IsArtinian ℤ ℤ := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have hinj : Function.Injective NativeTorBoundaryTests.mulTwo.hom :=
    NativeTorBoundaryTests.integralShortComplex_shortExact.moduleCat_injective_f
  have hsur := IsArtinian.surjective_of_injective_endomorphism
    NativeTorBoundaryTests.mulTwo.hom hinj
  obtain ⟨z, hz⟩ := hsur 1
  change (2 : ℤ) * z = 1 at hz
  omega

theorem original_term_has_infinite_length : Module.length ℤ ((B.X 0).X 0) = ⊤ := by
  change Module.length ℤ Z = ⊤
  exact integer_length_top

theorem B_bound (p q : ℕ) (h : 1 < p ∨ 1 < q) : IsZero ((B.X p).X q) := by
  rcases h with hp | hq
  · obtain ⟨p, rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
    change IsZero ((0 : ChainComplex (ModuleCat ℤ) ℕ).X q)
    exact (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) q).map_isZero
      (isZero_zero (ChainComplex (ModuleCat ℤ) ℕ))
  · cases p with
    | zero =>
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
      change IsZero (0 : ModuleCat ℤ)
      exact isZero_zero (ModuleCat ℤ)
    | succ p =>
      cases p with
      | zero =>
        obtain ⟨q, rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
        change IsZero (0 : ModuleCat ℤ)
        exact isZero_zero (ModuleCat ℤ)
      | succ p =>
        change IsZero ((0 : ChainComplex (ModuleCat ℤ) ℕ).X q)
        exact (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) q).map_isZero
          (isZero_zero (ChainComplex (ModuleCat ℤ) ℕ))

/-- Actual vertical homology is the original integer module in each retained row. -/
def vHomologyIsoZ (q : ℕ) (hq : q ≤ 1) : V.homology q ≅ Z := by
  cases q with
  | zero => exact vHomologyIsoX 0
  | succ q =>
    have hq0 : q = 0 := by omega
    subst q
    exact vHomologyIsoX 1

theorem B_verticalHomology_d (q : ℕ) :
    (B.verticalHomologyComplex q).d 1 0 = (2 : ℕ) • (𝟙 (V.homology q)) := by
  rw [HomologicalComplex₂.verticalHomologyComplex_d]
  have hb : B.d 1 0 = (2 : ℕ) • (𝟙 V) := ChainComplex.of_d BObj BDiff 0
  rw [hb]
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q).map
    ((2 : ℕ) • (𝟙 V)) = _
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) q
  change F.map ((2 : ℕ) • (𝟙 V)) = (2 : ℕ) • (𝟙 (V.homology q))
  rw [Functor.map_nsmul]
  have hi : F.map (𝟙 V) = 𝟙 (V.homology q) := F.map_id V
  exact congrArg (fun f => (2 : ℕ) • f) hi

theorem mulTwo_eq_nsmul : NativeTorBoundaryTests.mulTwo = (2 : ℕ) • (𝟙 Z) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp [NativeTorBoundaryTests.mulTwo, ModuleCat.hom_id, two_smul]

/-- The original integral exact presentation computes the actual cokernel. -/
def mulTwoCokernelIsoQ :
    (cokernel (C := ModuleCat ℤ) NativeTorBoundaryTests.mulTwo) ≅ Q :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit
    (parallelPair NativeTorBoundaryTests.mulTwo (0 : Z ⟶ Z)))
    NativeTorBoundaryTests.integralShortComplex_shortExact.gIsCokernel

/-- The actual first horizontal homology in column zero is the original mod-two quotient. -/
def iteratedZeroIsoQ (q : ℕ) (hq : q ≤ 1) :
    (B.verticalHomologyComplex q).homology 0 ≅ Q := by
  let C := B.verticalHomologyComplex q
  let S := C.sc' 1 0 ((ComplexShape.down ℕ).next 0)
  let e₀ : C.X 0 ≅ Z := by
    change V.homology q ≅ Z
    exact vHomologyIsoZ q hq
  let e₁ : C.X 1 ≅ Z := by
    change V.homology q ≅ Z
    exact vHomologyIsoZ q hq
  have hg : S.g = 0 := C.shape 0 _ (by simp)
  let eS : C.homology 0 ≅ S.homology :=
    C.homologyIsoSc' 1 0 _ ((ComplexShape.down ℕ).prev_eq' (by simp)) rfl
  let eH : S.homology ≅ (cokernel (C := ModuleCat ℤ) S.f) :=
    (ShortComplex.HomologyData.ofHasCokernel S hg).left.homologyIso
  have hw : e₁.hom ≫ NativeTorBoundaryTests.mulTwo = S.f ≫ e₀.hom := by
    change e₁.hom ≫ NativeTorBoundaryTests.mulTwo = C.d 1 0 ≫ e₀.hom
    rw [B_verticalHomology_d, mulTwo_eq_nsmul]
    change (vHomologyIsoZ q hq).hom ≫ ((2 : ℕ) • (𝟙 Z)) =
      ((2 : ℕ) • (𝟙 (V.homology q))) ≫ (vHomologyIsoZ q hq).hom
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id]
  exact eS ≪≫ eH ≪≫ cokernel.mapIso S.f NativeTorBoundaryTests.mulTwo e₁ e₀ hw.symm ≪≫
    mulTwoCokernelIsoQ

theorem iteratedOne_isZero (q : ℕ) (hq : q ≤ 1) :
    IsZero ((B.verticalHomologyComplex q).homology 1) := by
  let C := B.verticalHomologyComplex q
  let S := C.sc' 2 1 0
  let e₀ : C.X 0 ≅ Z := by
    change V.homology q ≅ Z
    exact vHomologyIsoZ q hq
  let e₁ : C.X 1 ≅ Z := by
    change V.homology q ≅ Z
    exact vHomologyIsoZ q hq
  have hw : C.d 1 0 ≫ e₀.hom = e₁.hom ≫ NativeTorBoundaryTests.mulTwo := by
    rw [B_verticalHomology_d, mulTwo_eq_nsmul]
    change ((2 : ℕ) • (𝟙 (V.homology q))) ≫ (vHomologyIsoZ q hq).hom =
      (vHomologyIsoZ q hq).hom ≫ ((2 : ℕ) • (𝟙 Z))
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id]
  have : Mono NativeTorBoundaryTests.mulTwo :=
    NativeTorBoundaryTests.integralShortComplex_shortExact.mono_f
  have hm : Mono (C.d 1 0) := mono_of_mono_fac hw
  have hginj : Function.Injective S.g := (ModuleCat.mono_iff_injective _).mp hm
  have hExact : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx0 : x = 0 := hginj (by simpa only [map_zero] using hx)
    exact ⟨0, by simp only [hx0, map_zero]⟩
  have hzero : IsZero S.homology := S.exact_iff_isZero_homology.mp hExact
  exact hzero.of_iso (C.homologyIsoSc' 2 1 0
    ((ComplexShape.down ℕ).prev_eq' (by simp)) ((ComplexShape.down ℕ).next_eq' (by simp)))

/-- The actual surviving second-page object is the original integral mod-two quotient. -/
def secondPageZeroIsoQ (q : ℕ) (hq : q ≤ 1) :
    ((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence B).page 2).X (0, q) ≅ Q :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso B 0 q ≪≫
    iteratedZeroIsoQ q hq

theorem secondPage_positive_isZero (p q : ℕ) (hp : 1 ≤ p) :
    IsZero (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence B).page 2).X
      (p, q)) := by
  by_cases hp1 : p = 1
  · subst p
    by_cases hq : q ≤ 1
    · exact (iteratedOne_isZero q hq).of_iso
        (HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso B 1 q)
    · exact HomologicalComplex₂.horizontalSecondPage_isZero_of_term_isZero B 1 q
        (B_bound 1 q (Or.inr (Nat.lt_of_not_ge hq)))
  · exact HomologicalComplex₂.horizontalSecondPage_isZero_of_term_isZero B p q
      (B_bound p q (Or.inl (by omega)))

theorem iterated_length_finite (p : ℕ) (hp : p ≤ 1) (q : ℕ) (hq : q ≤ 1) :
    Module.length ℤ ((B.verticalHomologyComplex q).homology p) ≠ ⊤ := by
  by_cases hp0 : p = 0
  · subst p
    rw [(iteratedZeroIsoQ q hq).toLinearEquiv.length_eq, NativeTorBoundaryTests.length_Q]
    exact ENat.one_ne_top
  · have hp1 : p = 1 := by omega
    subst p
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
      (iteratedOne_isZero q hq))]
    exact ENat.zero_ne_top

/-- The actual degree-one total homology is the nonzero integral mod-two module. -/
def totalH1IsoQ : (B.total (ComplexShape.down ℕ)).homology 1 ≅ Q :=
  (HomologicalComplex₂.horizontalSecondPageZeroColumnTotalHomologyIso B 1
    secondPage_positive_isZero).symm ≪≫ secondPageZeroIsoQ 1 (by omega)

theorem totalH1_length : Module.length ℤ ((B.total (ComplexShape.down ℕ)).homology 1) = 1 :=
  totalH1IsoQ.toLinearEquiv.length_eq.trans NativeTorBoundaryTests.length_Q

theorem totalH1_nonzero : ¬ IsZero ((B.total (ComplexShape.down ℕ)).homology 1) := by
  intro h
  have hz : Module.length ℤ ((B.total (ComplexShape.down ℕ)).homology 1) = 0 :=
    Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp h)
  rw [totalH1_length] at hz
  exact one_ne_zero hz

example : Module.length ℤ ((HomologicalComplex₂.horizontalTotalHomologyFiltration B 1).obj
    ((0 : ℤ) : EInt)) = 1 :=
  (HomologicalComplex₂.horizontalTotalHomologyFiltrationZeroTotalIso B 1
    secondPage_positive_isZero ≪≫ totalH1IsoQ).toLinearEquiv.length_eq.trans
      NativeTorBoundaryTests.length_Q

example : IsZero ((HomologicalComplex₂.horizontalTotalHomologyFiltration B 1).obj
    ((-1 : ℤ) : EInt)) :=
  HomologicalComplex₂.horizontalTotalHomologyFiltration_obj_isZero_of_neg B (-1) (by omega) 1

example : IsZero (HomologicalComplex₂.horizontalTotalHomologyGradedPiece B 1 0) :=
  HomologicalComplex₂.isZero_horizontalTotalHomologyGradedPiece_of_secondPage B 1 0
    (secondPage_positive_isZero 1 0 (by omega))

example (j : ℕ) (hj : 3 ≤ j) : IsZero ((B.total (ComplexShape.down ℕ)).homology j) :=
  (HomologicalComplex₂.boundedBicomplexFiniteLengthHomologyData B 1 1 B_bound
    iterated_length_finite).vanishes j (by
      dsimp only [HomologicalComplex₂.boundedBicomplexFiniteLengthHomologyData]
      exact hj)

example : HomologicalComplex.finiteLengthEulerCharacteristic ℤ
    (HomologicalComplex₂.boundedBicomplexFiniteLengthHomologyData B 1 1 B_bound
      iterated_length_finite) = 0 := by
  rw [HomologicalComplex₂.boundedBicomplex_euler_eq_iterated]
  have h₀ (q : ℕ) (hq : q ≤ 1) :
      Module.length ℤ ((B.verticalHomologyComplex q).homology 0) = 1 :=
    (iteratedZeroIsoQ q hq).toLinearEquiv.length_eq.trans NativeTorBoundaryTests.length_Q
  have h₁ (q : ℕ) (hq : q ≤ 1) :
      Module.length ℤ ((B.verticalHomologyComplex q).homology 1) = 0 :=
    Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp (iteratedOne_isZero q hq))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h₀ 0 (by omega), h₀ 1 (by omega), h₁ 0 (by omega), h₁ 1 (by omega)]
  norm_num

end BoundedBicomplexLengthEulerTests
