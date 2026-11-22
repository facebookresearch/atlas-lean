/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepFromExternal
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepUnit

/-!
# The complete compatible one-step and ordinary sphere-module equivalence

Both original diagram and morphism functions are preserved. The source
one-step unit and every original tensor-power coefficient are recovered.
The unit and counit maps are actual original diagram identities.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Spectra.Symmetric.OneStepSpectrum

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- The complete one-step reconstruction recovers each original one-step map. -/
theorem externalUnit_bonding (X : OneStepSpectrum T) (n : ℕ) :
    (fromExternal X.externalData).bonding n = X.bonding n := by
  have h := congrArg (fun t => ((λ_ T).inv ▷ X.diagram.obj (idx n)) ≫
      X.toOneStep.iterated 1 n ≫ t)
    (eqToHom_map X.diagram (congrArg idx (Nat.one_add n)))
  exact h.trans (X.toOneStep.recover_bonding n)

/-- The entire original one-step object is recovered by the identity diagram maps. -/
def externalUnitIsoApp (X : OneStepSpectrum T) :
    X ≅ (fromExternalFunctor (T := T)).obj ((toExternalFunctor (T := T)).obj X) where
  hom :=
    { map := 𝟙 X.diagram
      bonding_comm n := by
        have h := externalUnit_bonding X n
        have hi : (T ◁ 𝟙 (X.diagram.obj (idx n))) ≫ (fromExternal X.externalData).bonding n =
            (fromExternal X.externalData).bonding n :=
          (congrArg (fun t => t ≫ (fromExternal X.externalData).bonding n)
            (whiskerLeft_id T (X.diagram.obj (idx n)))).trans (Category.id_comp _)
        exact hi.trans (h.trans (Category.comp_id _).symm) }
  inv :=
    { map := 𝟙 X.diagram
      bonding_comm n := by
        have h := externalUnit_bonding X n
        have hi : (T ◁ 𝟙 (X.diagram.obj (idx n))) ≫ X.bonding n = X.bonding n :=
          (congrArg (fun t => t ≫ X.bonding n)
            (whiskerLeft_id T (X.diagram.obj (idx n)))).trans (Category.id_comp _)
        exact hi.trans (h.symm.trans (Category.comp_id _).symm) }
  hom_inv_id := by apply Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply Hom.ext; exact Category.id_comp _

/-- Every original external coefficient object is recovered by the identity diagram maps. -/
def externalCounitIsoApp (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) :
    (toExternalFunctor (T := T)).obj ((fromExternalFunctor (T := T)).obj d) ≅ d where
  hom :=
    { map := 𝟙 d.diagram
      comm a n := by
        have h : (fromExternal d).externalData.action.app (a, n) = d.action.app (a, n) :=
          fromExternal_iterated d a n
        have hi : ((genericSphereDayMonoid T).X.functor.obj a ◁ 𝟙 (d.diagram.obj n)) ≫
            d.action.app (a, n) = d.action.app (a, n) :=
          (congrArg (fun t => t ≫ d.action.app (a, n))
            (whiskerLeft_id _ _)).trans (Category.id_comp _)
        exact (Category.comp_id _).trans (h.trans hi.symm) }
  inv :=
    { map := 𝟙 d.diagram
      comm a n := by
        have h : (fromExternal d).externalData.action.app (a, n) = d.action.app (a, n) :=
          fromExternal_iterated d a n
        have hi : ((genericSphereDayMonoid T).X.functor.obj a ◁ 𝟙 (d.diagram.obj n)) ≫
            (fromExternal d).externalData.action.app (a, n) =
            (fromExternal d).externalData.action.app (a, n) :=
          (congrArg (fun t => t ≫ (fromExternal d).externalData.action.app (a, n))
            (whiskerLeft_id _ _)).trans (Category.id_comp _)
        exact (Category.comp_id _).trans (h.symm.trans hi.symm) }
  hom_inv_id := by apply DayFunctor.ExternalModule.Data.Hom.ext; exact Category.id_comp _
  inv_hom_id := by apply DayFunctor.ExternalModule.Data.Hom.ext; exact Category.id_comp _

/-- The original one-step recovery maps are natural in every original one-step morphism. -/
def externalUnitIso : 𝟭 (OneStepSpectrum T) ≅ toExternalFunctor ⋙ fromExternalFunctor :=
  NatIso.ofComponents externalUnitIsoApp (by
    intro X Y f
    apply Hom.ext
    exact (Category.comp_id f.map).trans (Category.id_comp f.map).symm)

/-- The original all-coefficient recovery maps are natural in every original external-data morphism. -/
def externalCounitIso : fromExternalFunctor ⋙ toExternalFunctor ≅
    𝟭 (DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) :=
  NatIso.ofComponents externalCounitIsoApp (by
    intro X Y f
    apply DayFunctor.ExternalModule.Data.Hom.ext
    exact (Category.comp_id f.map).trans (Category.id_comp f.map).symm)

/-- Compatible one-step data and complete external sphere-module actions are actually equivalent. -/
def externalEquivalence : OneStepSpectrum T ≌
    DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X where
  functor := toExternalFunctor
  inverse := fromExternalFunctor
  unitIso := externalUnitIso
  counitIso := externalCounitIso
  functor_unitIso_comp X := by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    exact Category.id_comp _

/-- The complete original one-step presentation is equivalent to the unchanged sphere-module carrier. -/
def moduleEquivalence (T : V) : OneStepSpectrum T ≌ SymmetricSpectrum (genericSphereDayMonoid T) :=
  (externalEquivalence (T := T)).trans
    (DayFunctor.ExternalModule.equivalence (genericSphereDayMonoid T).X)

/-- The full forward object function retains the entire original finite-index diagram. -/
theorem moduleEquivalence_functor_diagram (T : V) (X : OneStepSpectrum T) :
    ((moduleEquivalence T).functor.obj X).X.functor = X.diagram := rfl

/-- The full forward morphism function retains the entire original natural transformation. -/
theorem moduleEquivalence_functor_map (T : V) {X Y : OneStepSpectrum T} (f : X ⟶ Y) :
    ((moduleEquivalence T).functor.map f).hom.natTrans = f.map := rfl

/-- The full inverse object function retains the entire original spectrum diagram. -/
theorem moduleEquivalence_inverse_diagram (T : V) (M : SymmetricSpectrum (genericSphereDayMonoid T)) :
    ((moduleEquivalence T).inverse.obj M).diagram = M.X.functor := rfl

/-- The full inverse morphism function retains every original spectrum morphism component. -/
theorem moduleEquivalence_inverse_map (T : V)
    {M N : SymmetricSpectrum (genericSphereDayMonoid T)} (f : M ⟶ N) :
    ((moduleEquivalence T).inverse.map f).map = f.hom.natTrans := rfl

/-- Every original full tensor-power coefficient is recovered by the original one-step data. -/
theorem moduleEquivalence_inverse_iterated (T : V) (M : SymmetricSpectrum (genericSphereDayMonoid T))
    (p n : ℕ) :
    ((moduleEquivalence T).inverse.obj M).toOneStep.iterated p n =
      DayFunctor.ExternalModule.pair (genericSphereDayMonoid T).X M (idx p) (idx n) :=
  fromExternal_iterated (DayFunctor.ExternalModule.ofModule (genericSphereDayMonoid T).X M) (idx p) (idx n)

end CategoryTheory.Spectra.Symmetric.OneStepSpectrum
