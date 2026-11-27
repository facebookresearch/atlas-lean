/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.TransformationDescent
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Generators
public import MathlibExt.CategoryTheory.Enriched.Restriction

/-!
# Recovery of a genuine Day action from its external generators

Pull a genuine map from the original Day output back along the canonical
identity-weight generator transformation. Descending that extraction recovers
the original whole map. Full output-Hom naturality and every coend generator
prove recovery, without a separator or an ordinary structure on any index.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ActionFromTransformation
open Limits
attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  (X : EnrichedFunctor V K V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- Pull the full original Day action back along the canonical generator transformation. -/
def extract (m : (⟨Output.functor T F G⟩ : EnrichedFunctorCat V K) ⟶ ⟨X⟩) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (F.externalTensor G) (T.comp V X) :=
  GradedNatTrans.unitComp (Generators.transformation T F G)
    (EnrichedFunctorCat.restrictionMap T m)

/-- The extracted component is the actual identity-weight generator followed by the whole action. -/
theorem extract_component
    (m : (⟨Output.functor T F G⟩ : EnrichedFunctorCat V K) ⟶ ⟨X⟩) (a : C × D) :
    component T F G X (extract T F G X m) a =
      Generators.point T F G a ≫ EnrichedFunctorCat.component m (T.obj a) := by
  have h₀ := GradedNatTrans.unitComp_component (Generators.transformation T F G)
    (EnrichedFunctorCat.restrictionMap T m) a
  have h₁ := Generators.transformation_component T F G a
  have h₂ := EnrichedFunctorCat.restrictionMap_component T m a
  exact h₀.trans (congrArg₂ (fun f g => f ≫ g) h₁ h₂)

/-- Every original full Day generator reconstructs its original action. -/
theorem gen_extract
    (m : (⟨Output.functor T F G⟩ : EnrichedFunctorCat V K) ⟶ ⟨X⟩)
    (k : K) (a : C × D) :
    generator T F G X (extract T F G X m) k a =
      EnrichedDayKernel.gen T F G k a ≫ EnrichedFunctorCat.component m k := by
  let W : V := T.obj a ⟶[V] k
  let Q : V := (F.externalTensor G).obj a
  let R := Output.functor T F G
  let p : Q ⟶ R.obj (T.obj a) := Generators.point T F G a
  let f : R.obj (T.obj a) ⟶ X.obj (T.obj a) := EnrichedFunctorCat.component m (T.obj a)
  let q : R.obj k ⟶ X.obj k := EnrichedFunctorCat.component m k
  let r : R.obj (T.obj a) ⊗ W ⟶ R.obj k := MonoidalClosed.uncurry (R.map (T.obj a) k)
  let z : X.obj (T.obj a) ⊗ W ⟶ X.obj k := MonoidalClosed.uncurry (X.map (T.obj a) k)
  let γ : W ⊗ Q ⟶ R.obj k := EnrichedDayKernel.gen T F G k a
  have hn : r ≫ q = (f ▷ W) ≫ z := by
    exact (m.uncurriedNaturality (T.obj a) k).trans
      (congrArg (fun w => w ≫ z) (tensorHom_id f W))
  have hp : (p ▷ W) ≫ r = (β_ W Q).inv ≫ γ := by
    have h := Generators.point_output T F G a k (𝟙 W)
    change (p ⊗ₘ 𝟙 W) ≫ (R.obj (T.obj a) ◁ 𝟙 W) ≫ r =
      (β_ W Q).inv ≫ (𝟙 W ⊗ₘ 𝟙 Q) ≫ γ at h
    have h' : (p ▷ W) ≫ r = (β_ W Q).inv ≫ (𝟙 W ⊗ₘ 𝟙 Q) ≫ γ := by
      simpa only [whiskerLeft_id, Category.id_comp, tensorHom_id] using h
    have hi := id_tensorHom_id W Q
    exact h'.trans ((congrArg (fun w => (β_ W Q).inv ≫ w ≫ γ) hi).trans
      (congrArg (fun w => (β_ W Q).inv ≫ w) (Category.id_comp γ)))
  have hbp : (W ◁ p) ≫ (β_ W (R.obj (T.obj a))).hom =
      (β_ W Q).hom ≫ (p ▷ W) := braiding_naturality_right W p
  have hbf : (W ◁ f) ≫ (β_ W (X.obj (T.obj a))).hom =
      (β_ W (R.obj (T.obj a))).hom ≫ (f ▷ W) :=
    braiding_naturality_right W f
  have hpr : (W ◁ p) ≫ (β_ W (R.obj (T.obj a))).hom ≫ r = γ := by
    calc
      _ = (β_ W Q).hom ≫ (p ▷ W) ≫ r := by
        simpa only [Category.assoc] using congrArg (fun w => w ≫ r) hbp
      _ = (β_ W Q).hom ≫ (β_ W Q).inv ≫ γ := congrArg (fun w => (β_ W Q).hom ≫ w) hp
      _ = γ := Iso.hom_inv_id_assoc (β_ W Q) γ
  rw [generator_eq, extract_component]
  change (W ◁ (p ≫ f)) ≫ (β_ W (X.obj (T.obj a))).hom ≫ z = γ ≫ q
  rw [whiskerLeft_comp, Category.assoc]
  calc
    _ = (W ◁ p) ≫ (β_ W (R.obj (T.obj a))).hom ≫ (f ▷ W) ≫ z := by
      simpa only [Category.assoc] using congrArg (fun w => (W ◁ p) ≫ w ≫ z) hbf
    _ = (W ◁ p) ≫ (β_ W (R.obj (T.obj a))).hom ≫ r ≫ q := by
      simpa only [Category.assoc] using congrArg
        (fun w => (W ◁ p) ≫ (β_ W (R.obj (T.obj a))).hom ≫ w) hn.symm
    _ = γ ≫ q := by
      simpa only [Category.assoc] using congrArg (fun w => w ≫ q) hpr

/-- Descending the extracted genuine transformation recovers the entire original Day map. -/
theorem transformation_extract
    (m : (⟨Output.functor T F G⟩ : EnrichedFunctorCat V K) ⟶ ⟨X⟩) :
    transformation T F G X (extract T F G X m) = m := by
  apply EnrichedFunctorCat.hom_ext
  intro k
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  exact (gen_transformation T F G X (extract T F G X m) k a).trans
    (gen_extract T F G X m k a)

end CategoryTheory.EnrichedDayKernel.ActionFromTransformation
