/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedRetractAcyclicity
public import MathlibExt.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Positive continuous cohomology of actual injective field modules

The coefficient is the same discrete continuous module in the common
universe. Its actual constant-function inclusion into compact-open
coinduction splits by injectivity. The existing coinduced contraction then
makes every positive homogeneous cochain cycle an actual boundary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The stock identity comparison retains the actual coinduced coefficient module. -/
def fieldCoinductionTopRepIso (I : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteAbelianAction.toTopRep.obj (DiscreteAbelianAction.coind.{u, w}.obj I) ≅
      (DiscreteAbelianAction.toTopRep.obj I).coind₁ :=
  TopRep.toActionFromAction (DiscreteAbelianAction.toTopRep.obj I).coind₁

/-- The actual discrete constant inclusion is the original TopRep constant inclusion. -/
theorem fieldCoinductionTopRepIso_iota (I : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteAbelianAction.toTopRep.map (DiscreteAbelianAction.coindIota.{u, w}.app I) ≫
        (fieldCoinductionTopRepIso.{u, w} k Ω I).hom =
      TopRep.coind₁ι.app (DiscreteAbelianAction.toTopRep.obj I) := by
  rfl

/-- Injectivity supplies a genuine equivariant module retraction of the same inclusion. -/
def fieldInjectiveCoinducedRetraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    DiscreteAbelianAction.coind.{u, w}.obj I ⟶ I :=
  Injective.factorThru (𝟙 I) (DiscreteAbelianAction.coindIota.{u, w}.app I)

/-- The splitting equation holds in the original discrete continuous action category. -/
theorem fieldInjectiveCoinduced_iota_retraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    DiscreteAbelianAction.coindIota.{u, w}.app I ≫
        fieldInjectiveCoinducedRetraction.{u, w} k Ω I = 𝟙 I :=
  Injective.comp_factorThru (𝟙 I) (DiscreteAbelianAction.coindIota.{u, w}.app I)

/-- Retain the actual splitting arrow through the stock coefficient comparison. -/
def fieldInjectiveTopRepRetraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    (DiscreteAbelianAction.toTopRep.obj I).coind₁ ⟶
      DiscreteAbelianAction.toTopRep.obj I :=
  (fieldCoinductionTopRepIso.{u, w} k Ω I).inv ≫
    DiscreteAbelianAction.toTopRep.map (fieldInjectiveCoinducedRetraction.{u, w} k Ω I)

/-- The transported arrow splits the SAME original TopRep constant inclusion. -/
theorem fieldInjectiveTopRep_iota_retraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    TopRep.coind₁ι.app (DiscreteAbelianAction.toTopRep.obj I) ≫
        fieldInjectiveTopRepRetraction.{u, w} k Ω I =
      𝟙 (DiscreteAbelianAction.toTopRep.obj I) := by
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let e := fieldCoinductionTopRepIso.{u, w} k Ω I
  let i := DiscreteAbelianAction.coindIota.{u, w}.app I
  let r := fieldInjectiveCoinducedRetraction.{u, w} k Ω I
  have hP : P.map i ≫ P.map r = 𝟙 (P.obj I) :=
    (P.map_comp i r).symm.trans
      ((congrArg P.map (fieldInjectiveCoinduced_iota_retraction.{u, w} k Ω I)).trans
        (P.map_id I))
  have hi : P.map i ≫ e.hom = TopRep.coind₁ι.app (P.obj I) :=
    fieldCoinductionTopRepIso_iota.{u, w} k Ω I
  change TopRep.coind₁ι.app (P.obj I) ≫ (e.inv ≫ P.map r) = 𝟙 (P.obj I)
  calc
    _ = (P.map i ≫ e.hom) ≫ (e.inv ≫ P.map r) :=
      congrArg (fun f => f ≫ (e.inv ≫ P.map r)) hi.symm
    _ = P.map i ≫ P.map r := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = 𝟙 (P.obj I) := hP

/-- Every positive degree of the EXISTING continuous homogeneous cohomology is zero. -/
theorem fieldInjectiveContinuousCohomology_succ_isZero
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ) :
    IsZero (continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj I)) := by
  let : LocallyCompactSpace Gal(Ω/k) := by
    change LocallyCompactSpace (InfiniteGalois.profiniteGalGrp k Ω)
    infer_instance
  exact ContinuousCohomology.isZero_succ_of_coinduced_retract.{0, u, w}
    (DiscreteAbelianAction.toTopRep.obj I)
    (fieldInjectiveTopRepRetraction.{u, w} k Ω I)
    (fieldInjectiveTopRep_iota_retraction.{u, w} k Ω I) n

/-- Every actual positive-degree cohomology element is the original zero element. -/
theorem fieldInjectiveContinuousCohomology_eq_zero
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ)
    (x : continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj I)) : x = 0 := by
  let A := continuousCohomology.{0, u, w} (n + 1)
    (DiscreteAbelianAction.toTopRep.obj I)
  have h : (𝟙 A : A ⟶ A) = 0 :=
    (fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I n).eq_of_tgt _ _
  exact congrArg (fun f : A ⟶ A => f.hom x) h

/-- Every original positive homogeneous cycle is the differential of a predecessor cochain. -/
theorem fieldInjectiveContinuousCohomology_cycle_boundary
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ)
    (z : (TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).cycles (n + 1)) :
    ∃ b : (TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).X n,
      ((TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).d n (n + 1)).hom b =
        ((TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).iCycles
          (n + 1)).hom z := by
  let K := TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)
  have hz : K.homologyπ (n + 1) z = 0 :=
    fieldInjectiveContinuousCohomology_eq_zero.{u, w} k Ω I n _
  obtain ⟨b, hb⟩ :=
    (K.homologyπ_eq_zero_iff_exists_boundary n (n + 1) (by simp) z).mp hz
  exact ⟨b, hb.symm⟩

/-- All splitting and original homogeneous cochain laws for the same actual injective. -/
def OriginalFieldInjectiveContinuousCochainAcyclicityLaws
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] : Prop :=
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let C := DiscreteAbelianAction.coind.{u, w} (G := Gal(Ω/k))
  let i := DiscreteAbelianAction.coindIota.{u, w}.app I
  let r := fieldInjectiveCoinducedRetraction.{u, w} k Ω I
  let e := fieldCoinductionTopRepIso.{u, w} k Ω I
  let s := fieldInjectiveTopRepRetraction.{u, w} k Ω I
  let K := TopRep.homogeneousCochains (P.obj I)
  Mono i ∧
  ((P.obj I).V : Type (max u w)) = DiscreteAbelianAction.underlying I ∧
  (DiscreteAbelianAction.underlying (C.obj I) : Type (max u w)) =
    C(Gal(Ω/k), DiscreteAbelianAction.underlying I) ∧
  (∀ (m : DiscreteAbelianAction.underlying I) (g : Gal(Ω/k)),
    DiscreteAbelianAction.coindFunction.{u, w} I (DiscreteAbelianAction.homToAdd i m) g = m) ∧
  i ≫ r = 𝟙 I ∧
  (∀ m : DiscreteAbelianAction.underlying (C.obj I),
    (P.map r).hom m = DiscreteAbelianAction.homToAdd r m) ∧
  P.map i ≫ e.hom = TopRep.coind₁ι.app (P.obj I) ∧
  TopRep.coind₁ι.app (P.obj I) ≫ s = 𝟙 (P.obj I) ∧
  (∀ n : ℕ, IsZero (continuousCohomology.{0, u, w} (n + 1) (P.obj I))) ∧
  ∀ (n : ℕ) (z : K.cycles (n + 1)),
    ∃ b : K.X n, (K.d n (n + 1)).hom b = (K.iCycles (n + 1)).hom z

/-- The whole all-field, independent-coefficient, all-positive-degree acyclicity source unit. -/
theorem original_field_injective_continuous_cochain_acyclicity
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    OriginalFieldInjectiveContinuousCochainAcyclicityLaws.{u, w} k Ω I := by
  refine ⟨inferInstance, DiscreteAbelianAction.toTopRep_obj I,
    DiscreteAbelianAction.coind_obj I, DiscreteAbelianAction.coindIota_apply I,
    fieldInjectiveCoinduced_iota_retraction.{u, w} k Ω I,
    (fun m => DiscreteAbelianAction.toTopRep_map_apply _ m),
    fieldCoinductionTopRepIso_iota.{u, w} k Ω I,
    fieldInjectiveTopRep_iota_retraction.{u, w} k Ω I,
    fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I,
    fieldInjectiveContinuousCohomology_cycle_boundary.{u, w} k Ω I⟩

end AlgebraicGeometry.Scheme.DerivedSections
