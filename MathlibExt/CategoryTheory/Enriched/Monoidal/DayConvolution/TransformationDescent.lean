/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ActionFromTransformation

/-!
# Genuine enriched descent of the original continuous Day action

The complete output Hom action respects the descended contraction. Curry
and the original coend generators prove this equality on whole Hom objects.
The original Day output functor therefore carries a genuine transformation
to the supplied output diagram, with precisely the selected descended maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ActionFromTransformation

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  (X : EnrichedFunctor V K V)
  (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (F.externalTensor G) (T.comp V X))
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The entire curried output action respects the selected descended contraction. -/
theorem desc_output_action (k l : K) :
    MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l) ≫
        desc T F G X t l =
      ((k ⟶[V] l) ◁ desc T F G X t k) ≫ targetAction X k l := by
  apply MonoidalClosed.curry_injective
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  let H : V := k ⟶[V] l
  let γ := EnrichedDayKernel.gen T F G k a
  have hLeft : (H ◁ γ) ≫
      MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l) =
        EnrichedDayKernel.Output.actionGenerator T F G k l a :=
    (MonoidalClosed.uncurry_natural_left γ
      (EnrichedDayKernel.Output.actionDesc T F G k l)).symm.trans
        ((congrArg MonoidalClosed.uncurry
          (EnrichedDayKernel.Output.gen_actionDesc T F G k l a)).trans
            (MonoidalClosed.uncurry_curry _))
  have hRight : (H ◁ γ) ≫ (H ◁ desc T F G X t k) =
      H ◁ generator T F G X t k a :=
    (whiskerLeft_comp H γ (desc T F G X t k)).symm.trans
      (congrArg (fun z => H ◁ z) (gen_desc T F G X t k a))
  have hMiddle : EnrichedDayKernel.Output.actionGenerator T F G k l a ≫
      desc T F G X t l =
    EnrichedDayKernel.Output.outputAction (T.obj a) k l
      ((F.externalTensor G).obj a) ≫ generator T F G X t l a :=
    (Category.assoc (EnrichedDayKernel.Output.outputAction (T.obj a) k l
      ((F.externalTensor G).obj a)) (EnrichedDayKernel.gen T F G l a)
        (desc T F G X t l)).trans
      (congrArg (fun z => EnrichedDayKernel.Output.outputAction (T.obj a) k l
        ((F.externalTensor G).obj a) ≫ z) (gen_desc T F G X t l a))
  have hChain : (H ◁ γ) ≫
      MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l) ≫
        desc T F G X t l =
    (H ◁ γ) ≫ (H ◁ desc T F G X t k) ≫ targetAction X k l :=
    (Category.assoc (H ◁ γ)
      (MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l))
      (desc T F G X t l)).symm.trans
        ((congrArg (fun z => z ≫ desc T F G X t l) hLeft).trans
          (hMiddle.trans ((generator_output_naturality T F G X t k l a).trans
            ((congrArg (fun z => z ≫ targetAction X k l) hRight.symm).trans
              (Category.assoc (H ◁ γ) (H ◁ desc T F G X t k) (targetAction X k l))))))
  exact hChain

/-- The descended maps satisfy full enriched naturality for the original output functor. -/
theorem desc_full_naturality (k l : K) :
    MonoidalClosed.uncurry ((EnrichedDayKernel.Output.functor T F G).map k l) ≫
        desc T F G X t l =
      (desc T F G X t k ⊗ₘ 𝟙 (k ⟶[V] l)) ≫ MonoidalClosed.uncurry (X.map k l) := by
  let H : V := k ⟶[V] l
  let E := EnrichedDayKernel.obj T F G k
  let q := desc T F G X t k
  have hNatural : (β_ H E).hom ≫ (q ⊗ₘ 𝟙 H) ≫
      MonoidalClosed.uncurry (X.map k l) = (H ◁ q) ≫ targetAction X k l := by
    simpa only [E, q, targetAction, id_tensorHom] using
      (braiding_naturality_assoc (𝟙 H) q (MonoidalClosed.uncurry (X.map k l))).symm
  apply (cancel_epi (β_ H E).hom).1
  change (β_ H E).hom ≫ MonoidalClosed.uncurry
      (EnrichedDayKernel.Output.map T F G k l) ≫ desc T F G X t l =
    (β_ H E).hom ≫ (q ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (X.map k l)
  rw [EnrichedDayKernel.Output.map_uncurry]
  calc
    _ = MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l) ≫
        desc T F G X t l := by
      simpa only [Category.assoc] using Iso.hom_inv_id_assoc (β_ H E)
        (MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k l) ≫
          desc T F G X t l)
    _ = (H ◁ q) ≫ targetAction X k l := desc_output_action T F G X t k l
    _ = _ := hNatural.symm

/-- The actual original Day output functor carries the selected genuine contraction. -/
def transformation :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (EnrichedDayKernel.Output.functor T F G) X :=
  GradedNatTrans.unitOfComponents (fun k => desc T F G X t k)
    (desc_full_naturality T F G X t)

/-- Its complete ordinary component is precisely the original selected coend descent. -/
theorem transformation_component (k : K) :
    (eHomEquiv V).symm ((transformation T F G X t).app k) = desc T F G X t k :=
  GradedNatTrans.unitOfComponents_component _ _ k

/-- The entire component function retains the original selected descended maps. -/
theorem transformation_component_function :
    (fun k => (eHomEquiv V).symm ((transformation T F G X t).app k)) =
      (fun k => desc T F G X t k) := by
  funext k
  exact transformation_component T F G X t k

/-- Every entire original Day generator maps to the supplied contraction family. -/
theorem gen_transformation (k : K) (a : C × D) :
    EnrichedDayKernel.gen T F G k a ≫
        (eHomEquiv V).symm ((transformation T F G X t).app k) =
      generator T F G X t k a := by
  rw [transformation_component, gen_desc]

end CategoryTheory.EnrichedDayKernel.ActionFromTransformation
