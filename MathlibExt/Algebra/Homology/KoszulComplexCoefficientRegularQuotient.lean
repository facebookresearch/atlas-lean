/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.Algebra.Homology.HomotopyCofiberDownNatQuasiIso
public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientSnoc
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Native cofiber comparison for an actual coefficient quotient

The existing generic homotopy-cofiber projection and its down-Nat
quasi-isomorphism theorem supply the actual coefficient-quotient map.
The original Koszul regular-coefficient projection retains its tensor values.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v


namespace KoszulComplex

open scoped Pointwise

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The original scalar map and the original quotient by its image form
an actual coefficient short complex. -/
def scalarCoefficientQuotientShortComplex (r : R) (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (r • 𝟙 M) (ModuleCat.ofHom (r • (⊤ : Submodule R M)).mkQ) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (Submodule.Quotient.mk (r • m) : QuotSMulTop r M) = 0
    exact (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R M))).mpr
      (Submodule.smul_mem_pointwise_smul m r ⊤ trivial))

/-- Regularity of the actual scalar action earns short exactness of the
original coefficient quotient sequence. -/
theorem scalarCoefficientQuotientShortComplex_shortExact
    (r : R) (M : ModuleCat.{v} R) (hr : IsSMulRegular M r) :
    (scalarCoefficientQuotientShortComplex R r M).ShortExact := by
  let S := scalarCoefficientQuotientShortComplex R r M
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff S).mpr
    intro m hm
    change (Submodule.Quotient.mk m : QuotSMulTop r M) = 0 at hm
    have hmem := (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R M))).mp hm
    obtain ⟨x, _, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists (R := R) (M := M) m r (⊤ : Submodule R M)).mp hmem
    exact ⟨x, hx⟩
  · exact (ModuleCat.mono_iff_injective _).mpr hr
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The native projection removes an actual last scalar coefficient and
uses the actual quotient module as the remaining coefficient. -/
def familyTensorCoefficientRegularQuotientProjection
    (a : Fin (n + 1) → R) (M : ModuleCat.{v} R) :
    familyTensorCoefficientComplex R a M ⟶
      familyTensorCoefficientComplex R (fun i : Fin n => a i.castSucc)
        (ModuleCat.of R (QuotSMulTop (a (Fin.last n)) M)) :=
  (familyTensorCoefficientSnocConeIso R a M).hom ≫
    HomologicalComplex.homotopyCofiber.descShortComplex
      (familyTensorCoefficientShortComplex R (fun i : Fin n => a i.castSucc)
        (scalarCoefficientQuotientShortComplex R (a (Fin.last n)) M))

/-- An actual regular last coefficient gives the native quotient
quasi-isomorphism, without any finiteness premise on intermediate homology. -/
theorem familyTensorCoefficientRegularQuotientProjection_quasiIso
    (a : Fin (n + 1) → R) (M : ModuleCat.{v} R) (hr : IsSMulRegular M (a (Fin.last n))) :
    QuasiIso (familyTensorCoefficientRegularQuotientProjection R a M) := by
  let S := familyTensorCoefficientShortComplex R (fun i : Fin n => a i.castSucc)
    (scalarCoefficientQuotientShortComplex R (a (Fin.last n)) M)
  have hS : S.ShortExact := familyTensorCoefficientShortComplex_shortExact R _ _
    (scalarCoefficientQuotientShortComplex_shortExact R _ M hr)
  let e : familyTensorCoefficientComplex R a M ≅ HomologicalComplex.homotopyCofiber S.f :=
    familyTensorCoefficientSnocConeIso R a M
  let : QuasiIso (HomologicalComplex.homotopyCofiber.descShortComplex S) :=
    HomologicalComplex.homotopyCofiber.quasiIso_descShortComplex_downNat S hS
  change QuasiIso (e.hom ≫ HomologicalComplex.homotopyCofiber.descShortComplex S)
  exact quasiIso_comp e.hom (HomologicalComplex.homotopyCofiber.descShortComplex S)

/-- Every original homology degree is identified with the actual smaller
family homology on the actual regular scalar quotient. -/
def familyTensorCoefficientRegularQuotientHomologyIso
    (a : Fin (n + 1) → R) (M : ModuleCat.{v} R) (hr : IsSMulRegular M (a (Fin.last n))) (j : ℕ) :
    (familyTensorCoefficientComplex R a M).homology j ≅
      (familyTensorCoefficientComplex R (fun i : Fin n => a i.castSucc)
        (ModuleCat.of R (QuotSMulTop (a (Fin.last n)) M))).homology j := by
  letI : QuasiIso (familyTensorCoefficientRegularQuotientProjection R a M) :=
    familyTensorCoefficientRegularQuotientProjection_quasiIso R a M hr
  exact asIso (HomologicalComplex.homologyMap (familyTensorCoefficientRegularQuotientProjection R a M) j)

/-- The original full-family finite quotient earns the smaller-family
finite quotient after reducing the actual coefficient module by its last scalar. -/
theorem familyTensorCoefficientQuotient_length_ne_top
    (a : Fin (n + 1) → R) (M : ModuleCat.{v} R)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    Module.length R (R ⧸ (Ideal.span (Set.range (fun i : Fin n => a i.castSucc)) ⊔
      Module.annihilator R (QuotSMulTop (a (Fin.last n)) M))) ≠ ⊤ := by
  let Q := QuotSMulTop (a (Fin.last n)) M
  let J := Ideal.span (Set.range (fun i : Fin n => a i.castSucc)) ⊔ Module.annihilator R Q
  have hAnn : Module.annihilator R M ≤ Module.annihilator R Q :=
    ((a (Fin.last n) • (⊤ : Submodule R M)).mkQ).annihilator_le_of_surjective
      (Submodule.mkQ_surjective _)
  have hI : Ideal.span (Set.range a) ≤ J := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact Submodule.mem_sup_right (QuotSMulTop.mem_annihilator M (a (Fin.last n)))
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_range_self k))
  exact Module.length_ne_top_of_finite_of_ideal_le_annihilator R (R ⧸ J)
    (Ideal.span (Set.range a) ⊔ Module.annihilator R M)
    (by rw [Ideal.annihilator_quotient]; exact sup_le hI (hAnn.trans le_sup_right)) hquot

/-- Removing an actual regular last coefficient preserves the actual
full-family Euler invariant and its original alternating sign convention. -/
theorem familyTensorCoefficientEuler_eq_of_last_regular
    [IsNoetherianRing R] (a : Fin (n + 1) → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hr : IsSMulRegular M (a (Fin.last n)))
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    familyTensorCoefficientEuler R a M hquot =
      familyTensorCoefficientEuler R (fun i : Fin n => a i.castSucc)
        (ModuleCat.of R (QuotSMulTop (a (Fin.last n)) M))
          (familyTensorCoefficientQuotient_length_ne_top R a M hquot) := by
  let Q := ModuleCat.of R (QuotSMulTop (a (Fin.last n)) M)
  let b : Fin n → R := fun i => a i.castSucc
  have hzero : IsZero ((familyTensorCoefficientComplex R b Q).homology (n + 1)) :=
    (HomologicalComplex.ExactAt.of_isZero
      (familyTensorCoefficientComplex_isZero_above R b Q (n + 1) (Nat.lt_succ_self n))).isZero_homology
  have hlength : Module.length R ((familyTensorCoefficientComplex R a M).homology (n + 1)) = 0 := by
    rw [(familyTensorCoefficientRegularQuotientHomologyIso R a M hr (n + 1)).toLinearEquiv.length_eq]
    exact Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hzero)
  rw [familyTensorCoefficientEuler_eq, familyTensorCoefficientEuler_eq, Finset.sum_range_succ]
  rw [hlength]
  simp only [ENat.toNat_zero, Nat.cast_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [(familyTensorCoefficientRegularQuotientHomologyIso R a M hr j).toLinearEquiv.length_eq]

end KoszulComplex
