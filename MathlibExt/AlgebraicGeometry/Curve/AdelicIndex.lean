/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_AdelicIndex.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.Repartitions
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.CompletePartialOrder

/-!
# Adelic index, Weil differentials and the genus

This file defines the adèle space, the adelic index of specialty, Weil differentials, and the
predicate `StichtenothGenusExists` expressing that `deg D - ℓ(D)` is bounded above and attains its
maximum. The Riemann-Roch spaces `LSpace D`, their dimensions `ell D` and the predicate
`ConstantsAreBase` come from `MathlibExt.AlgebraicGeometry.Curve.LPolynomial`.

The adèle space `adeleSpace K F` is defined directly as the functions on places that are integral
at all but finitely many places. When every nonzero function has a principal divisor
(`HasPrincipalDivisors K F`), it is the repartition algebra `repartitions K F`
(`mem_adeleSpace_iff_mem_repartitions`); under that identification, `repartitionsEquivAdeleSpace`,
the bounded and the principal repartitions correspond to `adeleBdd D` and `globalSub K F`, so
`H1 K F D` is the quotient whose dimension is `indexOfSpecialty D` (`h1EquivAdeleQuotient`,
`finrank_h1_eq_indexOfSpecialty`), and `genusFF K F = indexOfSpecialty 0`.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {D E : Divisor K F}

theorem lSpace_mono (hDE : D ≤ E) : LSpace D ≤ LSpace E := fun _ hf v =>
  (hf v).trans (WithZero.exp_le_exp.mpr (hDE v))

theorem algebraMap_mem_lSpace_zero (c : K) :
    algebraMap K F c ∈ LSpace (0 : Divisor K F) := fun v => by
  rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
  exact v.adicValuation_algebraMap_le_one c

theorem one_mem_lSpace_zero : (1 : F) ∈ LSpace (0 : Divisor K F) := by
  simpa using algebraMap_mem_lSpace_zero (K := K) (F := F) 1

def adeleBdd (D : Divisor K F) : Submodule K (Place K F → F) where
  carrier := {α | ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v)}
  add_mem' := fun {α β} hα hβ v =>
    (v.adicValuation.map_add (α v) (β v)).trans (max_le (hα v) (hβ v))
  zero_mem' := fun v => by rw [Pi.zero_apply, Valuation.map_zero]; exact zero_le
  smul_mem' := fun c α hα v => by
    rw [Pi.smul_apply, Algebra.smul_def, Valuation.map_mul]
    calc v.adicValuation (algebraMap K F c) * v.adicValuation (α v)
        ≤ 1 * v.adicValuation (α v) := by gcongr; exact v.adicValuation_algebraMap_le_one c
      _ = v.adicValuation (α v) := one_mul _
      _ ≤ WithZero.exp (D v) := hα v

variable {D E : Divisor K F}

@[simp]
theorem mem_adeleBdd {α : Place K F → F} :
    α ∈ adeleBdd D ↔ ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v) := Iff.rfl

theorem adeleBdd_mono (hDE : D ≤ E) : adeleBdd D ≤ adeleBdd E := fun _ hα v =>
  (hα v).trans (WithZero.exp_le_exp.mpr (hDE v))

variable (K F) in
def diagonalHom : F →ₗ[K] (Place K F → F) where
  toFun f := fun _ => f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem diagonalHom_apply (f : F) (v : Place K F) : diagonalHom K F f v = f := rfl

theorem diagonalHom_injective [Nonempty (Place K F)] :
    Function.Injective (diagonalHom K F) := fun f g h => by
  simpa using congrFun h (Classical.arbitrary (Place K F))

theorem diagonal_mem_adeleBdd_iff {f : F} :
    diagonalHom K F f ∈ adeleBdd D ↔ f ∈ LSpace D := by
  simp only [mem_adeleBdd, diagonalHom_apply, mem_lSpace_iff]

variable (K F) in
def adeleSpace : Submodule K (Place K F → F) where
  carrier := {α | {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite}
  add_mem' := fun {α β} hα hβ => (hα.union hβ).subset fun v hv => by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h hv
    exact hv ((Valuation.map_add _ _ _).trans (max_le h.1 h.2))
  zero_mem' := by simp
  smul_mem' := fun c α hα => hα.subset fun v hv h => hv (by
    change v.adicValuation (c • α v) ≤ 1
    rw [Algebra.smul_def, map_mul]
    exact mul_le_one' (v.adicValuation_algebraMap_le_one c) h)

theorem mem_adeleSpace_iff_finite {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite := Iff.rfl

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F :=
  mem_repartitions_of_finite hα

theorem adeleBdd_le_adeleSpace : adeleBdd D ≤ adeleSpace K F := fun α hα =>
  D.support.finite_toSet.subset fun v hv => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hD0
    exact hv ((hα v).trans (by rw [hD0]; simp))

private theorem exists_diagonal_mem_adeleBdd [HasPrincipalDivisors K F] (f : F) :
    ∃ D : Divisor K F, diagonalHom K F f ∈ adeleBdd D := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by rw [map_zero]; exact (adeleBdd 0).zero_mem⟩
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    refine ⟨-P, fun v => ?_⟩
    rw [diagonalHom_apply,
      show ((-P : Divisor K F) v) = -v.ord f by rw [Finsupp.neg_apply, hPord v]]
    exact le_of_eq (by rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)])

theorem diagonal_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) :
    diagonalHom K F f ∈ adeleSpace K F :=
  let ⟨_, hD⟩ := exists_diagonal_mem_adeleBdd (K := K) f
  adeleBdd_le_adeleSpace hD

variable (K F) in
def globalSub : Submodule K (Place K F → F) := LinearMap.range (diagonalHom K F)

theorem diagonal_mem_globalSub (f : F) : diagonalHom K F f ∈ globalSub K F :=
  LinearMap.mem_range_self _ f

theorem map_diagonal_lSpace (D : Divisor K F) :
    (LSpace D).map (diagonalHom K F) = adeleBdd D ⊓ globalSub K F := by
  ext α
  rw [Submodule.mem_map, Submodule.mem_inf]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨diagonal_mem_adeleBdd_iff.mpr hf, diagonal_mem_globalSub f⟩
  · rintro ⟨hbdd, hglob⟩
    obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hglob
    exact ⟨f, diagonal_mem_adeleBdd_iff.mp (by rw [hf]; exact hbdd), hf⟩

def lSpaceEquivAdeleBddInfGlobal [Nonempty (Place K F)] (D : Divisor K F) :
    LSpace D ≃ₗ[K] (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) :=
  (Submodule.equivMapOfInjective (diagonalHom K F) diagonalHom_injective (LSpace D)).trans
    (LinearEquiv.ofEq _ _ (map_diagonal_lSpace D))

theorem finrank_adeleBdd_inf_global_eq_ell [Nonempty (Place K F)] (D : Divisor K F) :
    Module.finrank K (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) = ell D :=
  ((lSpaceEquivAdeleBddInfGlobal D).finrank_eq).symm

def indexOfSpecialty (D : Divisor K F) : ℕ :=
  Module.finrank K
    ((adeleSpace K F) ⧸
      ((adeleBdd D).comap (adeleSpace K F).subtype ⊔
        (globalSub K F).comap (adeleSpace K F).subtype))

theorem adeleBdd_directed :
    Directed (· ≤ ·) (adeleBdd (K := K) (F := F)) := fun D E =>
  ⟨D ⊔ E, adeleBdd_mono le_sup_left, adeleBdd_mono le_sup_right⟩

private theorem exists_mem_adeleBdd_of_finite {α : Place K F → F}
    (hα : {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite) :
    ∃ D : Divisor K F, α ∈ adeleBdd D := by
  classical
  refine ⟨Finsupp.onFinset hα.toFinset
    (fun v => if v.adicValuation (α v) ≤ 1 then 0 else -v.ord (α v)) fun v hv => ?_, fun v => ?_⟩
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro h
    simp [h] at hv
  · rw [Finsupp.onFinset_apply]
    split_ifs with h
    · simpa using h
    · rw [Place.adicValuation_le_exp_iff, neg_neg]
      exact Or.inr le_rfl

private theorem exists_mem_adeleBdd_of_mem_repartitions [HasPrincipalDivisors K F]
    {α : Place K F → F} (hα : α ∈ repartitions K F) : ∃ D : Divisor K F, α ∈ adeleBdd D := by
  refine Algebra.adjoin_induction (p := fun β _ => ∃ D : Divisor K F, β ∈ adeleBdd D)
    (fun β hβ => exists_mem_adeleBdd_of_finite hβ)
    (fun f => exists_diagonal_mem_adeleBdd (K := K) f) ?_ ?_ hα
  · rintro β γ - - ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    exact ⟨D₁ ⊔ D₂, add_mem (adeleBdd_mono le_sup_left h₁) (adeleBdd_mono le_sup_right h₂)⟩
  · rintro β γ - - ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, WithZero.exp_add]
    exact mul_le_mul' (h₁ v) (h₂ v)

theorem mem_adeleSpace_iff {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ ∃ D : Divisor K F, α ∈ adeleBdd D :=
  ⟨exists_mem_adeleBdd_of_finite, fun ⟨_, hD⟩ => adeleBdd_le_adeleSpace hD⟩

theorem mem_adeleSpace_iff_mem_repartitions [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F :=
  ⟨mem_repartitions_of_mem_adeleSpace, fun hα =>
    let ⟨_, hD⟩ := exists_mem_adeleBdd_of_mem_repartitions hα
    adeleBdd_le_adeleSpace hD⟩

variable (K F) in
abbrev adeleBddPrincipal (D : Divisor K F) : Submodule K (adeleSpace K F) :=
  (adeleBdd D).comap (adeleSpace K F).subtype ⊔
    (globalSub K F).comap (adeleSpace K F).subtype

theorem indexOfSpecialty_eq (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := rfl

section Repartitions

/-! ### The adèle space as the repartition algebra, given principal divisors -/

variable [HasPrincipalDivisors K F]

variable (K F) in
def repartitionsEquivAdeleSpace : repartitions K F ≃ₗ[K] adeleSpace K F where
  toFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mpr α.2⟩
  invFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mp α.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_repartitionsEquivAdeleSpace (α : repartitions K F) :
    (repartitionsEquivAdeleSpace K F α : Place K F → F) = α := rfl

@[simp]
theorem coe_repartitionsEquivAdeleSpace_symm (α : adeleSpace K F) :
    ((repartitionsEquivAdeleSpace K F).symm α : Place K F → F) = α := rfl

theorem map_repartitionsOf_repartitionsEquivAdeleSpace (D : Divisor K F) :
    (repartitionsOf K F D).map (repartitionsEquivAdeleSpace K F).toLinearMap =
      (adeleBdd D).comap (adeleSpace K F).subtype := by
  ext α
  rw [Submodule.mem_map_equiv, Submodule.mem_comap]
  exact Iff.rfl

theorem map_principalRepartitions_repartitionsEquivAdeleSpace :
    (principalRepartitions K F).map (repartitionsEquivAdeleSpace K F).toLinearMap =
      (globalSub K F).comap (adeleSpace K F).subtype := by
  ext α
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, mem_principalRepartitions_iff,
    coe_repartitionsEquivAdeleSpace_symm, Submodule.coe_subtype]
  exact (exists_congr fun f => eq_comm).trans (LinearMap.mem_range (f := diagonalHom K F)).symm

theorem map_repartitionsOf_sup_principalRepartitions (D : Divisor K F) :
    (repartitionsOf K F D ⊔ principalRepartitions K F).map
        (repartitionsEquivAdeleSpace K F).toLinearMap = adeleBddPrincipal K F D := by
  rw [Submodule.map_sup, map_repartitionsOf_repartitionsEquivAdeleSpace,
    map_principalRepartitions_repartitionsEquivAdeleSpace]

def h1EquivAdeleQuotient (D : Divisor K F) :
    H1 K F D ≃ₗ[K] adeleSpace K F ⧸ adeleBddPrincipal K F D :=
  Submodule.Quotient.equiv _ _ (repartitionsEquivAdeleSpace K F)
    (map_repartitionsOf_sup_principalRepartitions D)

@[simp]
theorem h1EquivAdeleQuotient_mk (D : Divisor K F) (α : repartitions K F) :
    h1EquivAdeleQuotient D (Submodule.Quotient.mk α) =
      Submodule.Quotient.mk (repartitionsEquivAdeleSpace K F α) := rfl

theorem finrank_h1_eq_indexOfSpecialty (D : Divisor K F) :
    Module.finrank K (H1 K F D) = indexOfSpecialty D :=
  (h1EquivAdeleQuotient D).finrank_eq

variable (K F) in
theorem genusFF_eq_indexOfSpecialty : genusFF K F = indexOfSpecialty (0 : Divisor K F) :=
  finrank_h1_eq_indexOfSpecialty 0

end Repartitions

def omegaSpace (D : Divisor K F) : Submodule K (Module.Dual K (adeleSpace K F)) :=
  (adeleBddPrincipal K F D).dualAnnihilator

theorem omegaSpace_vanishBdd {D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace D) {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd D) :
    φ α = 0 :=
  (Submodule.mem_dualAnnihilator φ).mp hφ α (Submodule.mem_sup_left hα)

theorem omegaSpace_vanishGlobal {D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace D) {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ globalSub K F) :
    φ α = 0 :=
  (Submodule.mem_dualAnnihilator φ).mp hφ α (Submodule.mem_sup_right hα)

theorem omegaSpace_antitone {D E : Divisor K F} (hDE : D ≤ E) :
    omegaSpace E ≤ omegaSpace D :=
  Submodule.dualAnnihilator_anti
    (sup_le_sup_right (Submodule.comap_mono (adeleBdd_mono hDE)) _)

def omegaSpaceEquivIndexDual (D : Divisor K F) :
    omegaSpace D ≃ₗ[K] Module.Dual K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
  (Submodule.dualQuotEquivDualAnnihilator (adeleBddPrincipal K F D)).symm

theorem finrank_omegaSpace_eq_indexOfSpecialty (D : Divisor K F) :
    Module.finrank K (omegaSpace D) = indexOfSpecialty D := by
  rw [indexOfSpecialty_eq, (omegaSpaceEquivIndexDual D).finrank_eq,
    Subspace.dual_finrank_eq]

variable (K F) in
def weilDifferentialModule : Submodule K (Module.Dual K (adeleSpace K F)) :=
  ⨆ D : Divisor K F, omegaSpace D

theorem omegaSpace_le_weilDifferentialModule (D : Divisor K F) :
    omegaSpace D ≤ weilDifferentialModule K F := le_iSup omegaSpace D

theorem omegaSpace_directed :
    Directed (· ≤ ·) (omegaSpace (K := K) (F := F)) := fun D E =>
  ⟨D ⊓ E, omegaSpace_antitone inf_le_left, omegaSpace_antitone inf_le_right⟩

theorem mem_weilDifferentialModule_iff {φ : Module.Dual K (adeleSpace K F)} :
    φ ∈ weilDifferentialModule K F ↔ ∃ D : Divisor K F, φ ∈ omegaSpace D := by
  unfold weilDifferentialModule
  exact Submodule.mem_iSup_of_directed _ omegaSpace_directed

variable (K) in
def mulAdele (f : F) : (Place K F → F) →ₗ[K] (Place K F → F) where
  toFun α := fun v => f * α v
  map_add' α β := funext fun v => mul_add f (α v) (β v)
  map_smul' c α := funext fun v => by
    simp only [Pi.smul_apply, Algebra.smul_def, RingHom.id_apply]; ring

@[simp]
theorem mulAdele_apply (f : F) (α : Place K F → F) (v : Place K F) :
    mulAdele K f α v = f * α v := rfl

@[simp]
theorem mulAdele_one : mulAdele K (1 : F) = LinearMap.id :=
  LinearMap.ext fun α => funext fun v => one_mul (α v)

theorem mulAdele_mul (f g : F) :
    mulAdele K (f * g) = (mulAdele K f).comp (mulAdele K g) :=
  LinearMap.ext fun α => funext fun v => mul_assoc f g (α v)

theorem mulAdele_mem_adeleBdd_sub {f : F} (hf : f ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord f) {D : Divisor K F} {α : Place K F → F}
    (hα : α ∈ adeleBdd D) : mulAdele K f α ∈ adeleBdd (D - P) := by
  intro v
  rw [mulAdele_apply, Valuation.map_mul, Finsupp.sub_apply, hP v,
    show v.adicValuation f = WithZero.exp (-v.ord f) by
      rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]]
  calc WithZero.exp (-v.ord f) * v.adicValuation (α v)
      ≤ WithZero.exp (-v.ord f) * WithZero.exp (D v) := by gcongr; exact hα v
    _ = WithZero.exp (D v - v.ord f) := by rw [← WithZero.exp_add]; ring_nf

theorem mulAdele_globalSub_le (f : F) :
    (globalSub K F).map (mulAdele K f) ≤ globalSub K F := by
  rintro _ ⟨α, ⟨g, rfl⟩, rfl⟩
  exact ⟨f * g, funext fun v => by simp⟩

theorem mulAdele_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) {α : Place K F → F}
    (hα : α ∈ adeleSpace K F) : mulAdele K f α ∈ adeleSpace K F := by
  rcases eq_or_ne f 0 with rfl | hf
  · have h0 : mulAdele K (0 : F) α = 0 := funext fun v => by simp
    rw [h0]; exact (adeleSpace K F).zero_mem
  · obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
    obtain ⟨P, hP, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    exact adeleBdd_le_adeleSpace (D := D - P) (mulAdele_mem_adeleBdd_sub hf hP hD)

variable (K F) in
def adeleSpaceMul [HasPrincipalDivisors K F] (f : F) :
    adeleSpace K F →ₗ[K] adeleSpace K F :=
  (mulAdele K f).restrict fun _ => mulAdele_mem_adeleSpace f

@[simp]
theorem adeleSpaceMul_coe [HasPrincipalDivisors K F] (f : F) (α : adeleSpace K F) :
    (adeleSpaceMul K F f α : Place K F → F) = mulAdele K f (α : Place K F → F) := rfl

variable (K F) in
def weilSmul [HasPrincipalDivisors K F] (f : F) :
    Module.Dual K (adeleSpace K F) →ₗ[K] Module.Dual K (adeleSpace K F) :=
  (adeleSpaceMul K F f).dualMap

@[simp]
theorem weilSmul_apply [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) (α : adeleSpace K F) :
    weilSmul K F f φ α = φ (adeleSpaceMul K F f α) := rfl

theorem adeleSpaceMul_one [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (1 : F) = LinearMap.id := by
  refine LinearMap.ext fun α => Subtype.ext ?_
  change mulAdele K (1 : F) (α : Place K F → F) = (α : Place K F → F)
  rw [mulAdele_one, LinearMap.id_apply]

theorem adeleSpaceMul_mul [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f * g) = (adeleSpaceMul K F f).comp (adeleSpaceMul K F g) := by
  refine LinearMap.ext fun α => Subtype.ext ?_
  change mulAdele K (f * g) (α : Place K F → F) = mulAdele K f (mulAdele K g (α : Place K F → F))
  rw [mulAdele_mul, LinearMap.comp_apply]

@[simp]
theorem weilSmul_one [HasPrincipalDivisors K F] :
    weilSmul K F (1 : F) = LinearMap.id := by
  unfold weilSmul; rw [adeleSpaceMul_one]; ext; simp

theorem weilSmul_mul [HasPrincipalDivisors K F] (f g : F) :
    weilSmul K F (f * g) = (weilSmul K F g).comp (weilSmul K F f) := by
  unfold weilSmul; rw [adeleSpaceMul_mul, LinearMap.dualMap_comp_dualMap]

theorem weilSmul_injective [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    Function.Injective (weilSmul K F f) := by
  apply Function.LeftInverse.injective (g := weilSmul K F f⁻¹)
  intro φ
  rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf, weilSmul_one,
    LinearMap.id_apply]

theorem weilSmul_mem_omegaSpace_add [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    {P : Divisor K F} (hP : ∀ v, P v = v.ord f) {D : Divisor K F}
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace D) :
    weilSmul K F f φ ∈ omegaSpace (D + P) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilSmul_apply, weilSmul_apply]
  have hβ' : (adeleSpaceMul K F f β : Place K F → F) ∈ adeleBdd D := by
    rw [adeleSpaceMul_coe]
    have h := mulAdele_mem_adeleBdd_sub hf hP (D := D + P) (Submodule.mem_comap.mp hβ)
    rwa [add_sub_cancel_right] at h
  have hγ' : (adeleSpaceMul K F f γ : Place K F → F) ∈ globalSub K F :=
    mulAdele_globalSub_le f ⟨_, Submodule.mem_comap.mp hγ, rfl⟩
  rw [omegaSpace_vanishBdd hφ hβ', omegaSpace_vanishGlobal hφ hγ', add_zero]

theorem weilSmul_mem_omegaSpace_of_mem_lSpace [HasPrincipalDivisors K F]
    {W D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W)
    {g : F} (hg : g ∈ LSpace (W - D)) :
    weilSmul K F g φ ∈ omegaSpace D := by
  rcases eq_or_ne g 0 with rfl | hg0
  · have h0 : weilSmul K F (0 : F) φ = 0 := by
      ext α; simp only [weilSmul_apply]
      refine omegaSpace_vanishBdd hφ ?_
      intro v
      simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, Valuation.map_zero]
      exact zero_le
    rw [h0]; exact (omegaSpace D).zero_mem
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
    refine omegaSpace_antitone ?_ (weilSmul_mem_omegaSpace_add hg0 hPord hφ)
    intro v
    rw [Finsupp.add_apply, hPord v]
    have hgL := (mem_lSpace_iff_ord.mp hg).resolve_left hg0 v
    rw [Finsupp.sub_apply] at hgL
    linarith

variable (K F) in
def residuePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) :
    LSpace (W - D) →ₗ[K] omegaSpace D where
  toFun g := ⟨weilSmul K F (g : F) φ, weilSmul_mem_omegaSpace_of_mem_lSpace hφ g.2⟩
  map_add' g₁ g₂ := by
    refine Subtype.ext ?_
    change weilSmul K F ((g₁ : F) + (g₂ : F)) φ
      = weilSmul K F (g₁ : F) φ + weilSmul K F (g₂ : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.add_apply]
    rw [← map_add]; congr 1
    exact Subtype.ext (funext fun v => by simp [add_mul])
  map_smul' c g := by
    refine Subtype.ext ?_
    change weilSmul K F (c • (g : F)) φ = c • weilSmul K F (g : F) φ
    ext α; simp only [weilSmul_apply, LinearMap.smul_apply]
    rw [← map_smul]; congr 1
    exact Subtype.ext (funext fun v => by simp [Algebra.smul_def]; ring)

@[simp]
theorem residuePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (g : LSpace (W - D)) :
    (residuePairing K F W D hφ g : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ := rfl

theorem residuePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    Function.Injective (residuePairing K F W D hφ) := by
  have hsub : ∀ g₁ g₂ : F, adeleSpaceMul K F (g₁ - g₂)
      = adeleSpaceMul K F g₁ - adeleSpaceMul K F g₂ := fun g₁ g₂ => by
    refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
    simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.sub_apply,
      Submodule.coe_sub, Pi.sub_apply, sub_mul]
  intro g₁ g₂ hg
  have hg' : weilSmul K F ((g₁ : F) - (g₂ : F)) φ = 0 := by
    have h := congrArg Subtype.val hg
    simp only [residuePairing_apply_coe] at h
    ext α
    simp only [weilSmul_apply, hsub, LinearMap.sub_apply, map_sub, LinearMap.zero_apply,
      sub_eq_zero]
    exact LinearMap.congr_fun h α
  rcases eq_or_ne ((g₁ : F) - (g₂ : F)) 0 with hd | hd
  · exact Subtype.ext (sub_eq_zero.mp hd)
  · exact absurd (weilSmul_injective hd (by rw [hg', map_zero])) hφ0

theorem ell_sub_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)] :
    ell (W - D) ≤ indexOfSpecialty D := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact LinearMap.finrank_le_finrank_of_injective (residuePairing_injective W D hφ hφ0)

variable (K F)

def WeilDifferentialRankOne [HasPrincipalDivisors K F] : Prop :=
  ∀ {φ : Module.Dual K (adeleSpace K F)}, φ ∈ weilDifferentialModule K F → φ ≠ 0 →
    ∀ {μ : Module.Dual K (adeleSpace K F)}, μ ∈ weilDifferentialModule K F →
      ∃! f : F, μ = weilSmul K F f φ

def HasWeilCanonicalDivisor : Prop :=
  ∀ {φ : Module.Dual K (adeleSpace K F)}, φ ∈ weilDifferentialModule K F → φ ≠ 0 →
    ∃ W : Divisor K F, φ ∈ omegaSpace W ∧ ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ W

variable {K F}

structure RiemannGenusReachedAt (γ : ℤ) (D₀ : Divisor K F) : Prop where
  finite : FiniteDimensional K (LSpace D₀)
  eq : Divisor.degree D₀ - (ell D₀ : ℤ) = γ - 1
  isMax : ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1

variable (K F) in
def RiemannGenusReached (γ : ℤ) : Prop :=
  Nonempty (Place K F) ∧ FiniteDimensional K (LSpace (0 : Divisor K F)) ∧
    ∃ D₀ : Divisor K F, RiemannGenusReachedAt γ D₀

variable (K F) in
def StichtenothGenusExists : Prop :=
  Nonempty (Place K F) ∧ FiniteDimensional K (LSpace (0 : Divisor K F)) ∧
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀

variable (K F) in
def RiemannGenusBounded : Prop :=
  ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ

variable (K F) in
def IndexOfSpecialtyFinite : Prop :=
  ∃ D₀ : Divisor K F, Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀)

theorem indexOfSpecialtyFinite_iff_exists_finite_h1 [HasPrincipalDivisors K F] :
    IndexOfSpecialtyFinite K F ↔ ∃ D₀ : Divisor K F, Module.Finite K (H1 K F D₀) :=
  exists_congr fun D₀ =>
    ⟨fun _ => Module.Finite.equiv (h1EquivAdeleQuotient D₀).symm,
      fun _ => Module.Finite.equiv (h1EquivAdeleQuotient D₀)⟩

end AlgebraicCurve

end
