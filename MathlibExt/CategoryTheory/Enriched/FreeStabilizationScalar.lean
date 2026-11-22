/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.FreeStabilizationKan
import MathlibExt.CategoryTheory.Enriched.FreeLifting
import MathlibExt.CategoryTheory.Enriched.ScalarFreeEvaluation
import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientAlgebra

/-!
# Scalar tensoring and composition of free stabilizations

In a braided monoidal closed category, scalar tensoring of a free stabilization is expressed
by the corresponding free extension and coefficient unitor. Composition of these maps is
controlled by enriched composition, including compatibility with supplied coefficient
multiplication maps and the identity formula. For the stated symmetric enriched index and
lax braided sphere data, the unit-coefficient specialization satisfies the corresponding
composition law.
-/

set_option autoImplicit false
noncomputable section
universe uV vV uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree
open CategoryTheory.EnrichedFunctorCat

section

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Scalar suspension of the existing stabilization is the original full free extension,
including the two actual scalar/free comparisons and the original coefficient unitor. -/
theorem stabilization_scalar (a b : A) (M K : V) (D : K ⟶ (a ⟶[V] b)) :
    (Free.scalarFreeIso M K b).inv ≫
        (EnrichedFunctorCat.tensorLeft M).map (stabilization a b K D) ≫
        (Free.scalarFreeIso M (𝟙_ V) a).hom ≫ Free.coefficientMap a (ρ_ M).hom =
      Free.extend b (M ⊗ K) (Free.object a M) (M ◁ D) := by
  apply EnrichedFunctorCat.hom_ext
  intro c
  let H := a ⟶[V] b
  let P := b ⟶[V] c
  let T := a ⟶[V] c
  let e : H ⊗ P ⟶ T := eComp V a b c
  have hD : (α_ M K P).hom ≫ M ◁ (D ▷ P) =
      ((M ◁ D) ▷ P) ≫ (α_ M H P).hom :=
    (associator_naturality_middle M D P).symm
  have hE : (M ◁ ((𝟙_ V) ◁ e)) ≫ (α_ M (𝟙_ V) T).inv ≫ ((ρ_ M).hom ▷ T) =
      (α_ M (𝟙_ V) (H ⊗ P)).inv ≫ ((ρ_ M).hom ▷ (H ⊗ P)) ≫ M ◁ e := by
    rw [← Category.assoc, associator_inv_naturality_right,
      Category.assoc, whisker_exchange, ← Category.assoc]
  have hPad :
      (M ◁ ((λ_ H).inv ▷ P)) ≫ M ◁ (α_ (𝟙_ V) H P).hom ≫
        (α_ M (𝟙_ V) (H ⊗ P)).inv ≫ ((ρ_ M).hom ▷ (H ⊗ P)) =
      𝟙 (M ⊗ (H ⊗ P)) := by monoidal
  change component ((Free.scalarFreeIso M K b).inv ≫ tensorLeftMap M (stabilization a b K D) ≫
      (Free.scalarFreeIso M (𝟙_ V) a).hom ≫ Free.coefficientMap a (ρ_ M).hom) c = _
  rw [component_comp, component_comp, component_comp,
    Free.scalarFreeIso_inv_component, Free.scalarFreeIso_hom_component,
    Free.coefficientMap_component, tensorLeftMap_component, Free.extend_component]
  dsimp only [Free.extensionComponent]
  simp only [tensorHom_id]
  change (α_ M K P).hom ≫ (M ◁ component (stabilization a b K D) c) ≫
      (α_ M (𝟙_ V) T).inv ≫ ((ρ_ M).hom ▷ T) =
    ((M ◁ D) ▷ P) ≫ MonoidalClosed.uncurry ((Free.object a M).toEnrichedFunctor.map b c)
  rw [stabilization_component, Free.object_uncurry_map]
  simp only [Free.action, tensorHom_id, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  change (α_ M K P).hom ≫ M ◁ (D ▷ P) ≫ M ◁ ((λ_ H).inv ▷ P) ≫
      M ◁ (α_ (𝟙_ V) H P).hom ≫ M ◁ ((𝟙_ V) ◁ e) ≫
      (α_ M (𝟙_ V) T).inv ≫ ((ρ_ M).hom ▷ T) =
    ((M ◁ D) ▷ P) ≫ (α_ M H P).hom ≫ M ◁ e
  rw [← Category.assoc (α_ M K P).hom (M ◁ (D ▷ P)), hD]
  simp only [Category.assoc]
  rw [show M ◁ ((𝟙_ V) ◁ e) ≫ (α_ M (𝟙_ V) T).inv ≫ ((ρ_ M).hom ▷ T) =
      (α_ M (𝟙_ V) (H ⊗ P)).inv ≫ ((ρ_ M).hom ▷ (H ⊗ P)) ≫ M ◁ e from hE]
  have h := congrArg
    (fun q => ((M ◁ D) ▷ P) ≫ (α_ M H P).hom ≫ q ≫ M ◁ e) hPad
  simpa only [Category.assoc, Category.id_comp] using h

/-- An original scalar step followed by gamma uses the entire original enriched Hom composition. -/
theorem stabilization_comp_step (z a b : A) (X K : V)
    (f : X ⟶ (z ⟶[V] a)) (D : K ⟶ (a ⟶[V] b)) :
    Free.extend b (X ⊗ K) (Free.object a X) (X ◁ D) ≫ stabilization z a X f =
      stabilization z b (X ⊗ K) ((f ⊗ₘ D) ≫ eComp V z a b) := by
  rw [Free.extend_postcomp]
  apply (Free.homEquiv b (X ⊗ K) (Free.object z (𝟙_ V))).injective
  change Free.evaluate b (X ⊗ K) (Free.object z (𝟙_ V))
      (Free.extend b (X ⊗ K) (Free.object z (𝟙_ V))
        ((X ◁ D) ≫ (evaluation b).map (stabilization z a X f))) =
    Free.evaluate b (X ⊗ K) (Free.object z (𝟙_ V))
      (stabilization z b (X ⊗ K) ((f ⊗ₘ D) ≫ eComp V z a b))
  rw [Free.evaluate_extend, evaluation_map, stabilization_evaluate, stabilization_component]
  let H := z ⟶[V] a
  let P := a ⟶[V] b
  let T := z ⟶[V] b
  let e : H ⊗ P ⟶ T := eComp V z a b
  have hPad : ((λ_ H).inv ▷ P) ≫ (α_ (𝟙_ V) H P).hom =
      (λ_ (H ⊗ P)).inv := by monoidal
  have hUnit : (λ_ (H ⊗ P)).inv ≫ (𝟙_ V ◁ e) = e ≫ (λ_ T).inv :=
    (leftUnitor_inv_naturality e).symm
  simp only [Free.action, tensorHom_id, comp_whiskerRight, Category.assoc]
  change (X ◁ D) ≫ (f ▷ P) ≫ ((λ_ H).inv ▷ P) ≫
      (α_ (𝟙_ V) H P).hom ≫ (𝟙_ V ◁ e) = (f ⊗ₘ D) ≫ e ≫ (λ_ T).inv
  rw [← Category.assoc (X ◁ D) (f ▷ P), ← tensorHom_def',
    ← Category.assoc ((λ_ H).inv ▷ P) (α_ (𝟙_ V) H P).hom, hPad]
  rw [hUnit]

omit [BraidedCategory V] [MonoidalClosed V] in
private theorem scalarUnit_middle (K H : V) :
    (K ◁ (λ_ H).inv) ≫ (α_ K (𝟙_ V) H).inv ≫ ((ρ_ K).hom ⊗ₘ 𝟙 H) =
      𝟙 (K ⊗ H) := by
  monoidal

omit [BraidedCategory V] [MonoidalClosed V] in
private theorem leftUnit_comp_middle {K L H J T : V}
    (u : K ⟶ H) (v : L ⟶ J) (w : H ⊗ J ⟶ T) :
    K ◁ (v ≫ (λ_ J).inv) ≫
        (α_ K (𝟙_ V) J).inv ≫ ((ρ_ K).hom ⊗ₘ 𝟙 J) ≫
        ((u ≫ (λ_ H).inv) ⊗ₘ 𝟙 J) ≫
        (α_ (𝟙_ V) H J).hom ≫ (𝟙_ V) ◁ w =
      ((u ⊗ₘ v) ≫ w) ≫ (λ_ T).inv := by
  have hu : ((u ≫ (λ_ H).inv) ⊗ₘ 𝟙 J) =
      (u ⊗ₘ 𝟙 J) ≫ ((λ_ H).inv ⊗ₘ 𝟙 J) := by
    simpa only [Category.comp_id] using
      (tensorHom_comp_tensorHom u (𝟙 J) (λ_ H).inv (𝟙 J)).symm
  have huv : (K ◁ v) ≫ (u ⊗ₘ 𝟙 J) = u ⊗ₘ v := by
    rw [← id_tensorHom]
    simpa only [Category.id_comp, Category.comp_id] using
      tensorHom_comp_tensorHom (𝟙 K) v u (𝟙 J)
  have hp : ((λ_ H).inv ⊗ₘ 𝟙 J) ≫ (α_ (𝟙_ V) H J).hom =
      (λ_ (H ⊗ J)).inv := by
    monoidal
  calc
    _ = (K ◁ v) ≫ ((K ◁ (λ_ J).inv) ≫
        (α_ K (𝟙_ V) J).inv ≫ ((ρ_ K).hom ⊗ₘ 𝟙 J)) ≫
        (u ⊗ₘ 𝟙 J) ≫ (((λ_ H).inv ⊗ₘ 𝟙 J) ≫ (α_ (𝟙_ V) H J).hom) ≫
        (𝟙_ V) ◁ w := by
      rw [whiskerLeft_comp, hu]
      simp only [Category.assoc]
    _ = (u ⊗ₘ v) ≫ (λ_ (H ⊗ J)).inv ≫ (𝟙_ V) ◁ w := by
      rw [scalarUnit_middle, hp, Category.id_comp, ← Category.assoc (K ◁ v), huv]
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun z => (u ⊗ₘ v) ≫ z) (leftUnitor_inv_naturality w)).symm

/-- The complete original scalar/free composition retains every source
coefficient map and the full enriched Hom multiplication. -/
theorem scalarStabilization_comp (a b c : A) (K L : V)
    (u : K ⟶ (a ⟶[V] b)) (v : L ⟶ (b ⟶[V] c)) :
    tensorLeftMap K (stabilization b c L v) ≫
        (Free.scalarFreeIso K (𝟙_ V) b).hom ≫
        Free.coefficientMap b (ρ_ K).hom ≫ stabilization a b K u =
      (Free.scalarFreeIso K L c).hom ≫
        stabilization a c (K ⊗ L) ((u ⊗ₘ v) ≫ eComp V a b c) := by
  apply (cancel_epi (Free.scalarFreeIso K L c).inv).mp
  simpa only [EnrichedFunctorCat.tensorLeft, Category.assoc, Iso.inv_hom_id_assoc] using
    (congrArg (fun f => f ≫ stabilization a b K u)
      (stabilization_scalar b c K L v)).trans
        (stabilization_comp_step a b c K L u v)

/-- The complete original scalar/free composition carries any whole coefficient product,
with both scalar/free maps and the original coefficient unitor retained. -/
theorem scalarStabilization_comp_coefficient (a b c : A) (K L T : V)
    (u : K ⟶ (a ⟶[V] b)) (v : L ⟶ (b ⟶[V] c))
    (w : T ⟶ (a ⟶[V] c)) (μ : K ⊗ L ⟶ T)
    (hComp : (u ⊗ₘ v) ≫ eComp V a b c = μ ≫ w) :
    tensorLeftMap K (stabilization b c L v) ≫
        ((Free.scalarFreeIso K (𝟙_ V) b).hom ≫ Free.coefficientMap b (ρ_ K).hom) ≫
        stabilization a b K u =
      ((Free.scalarFreeIso K L c).hom ≫ Free.coefficientMap c μ) ≫
        stabilization a c T w := by
  have h := scalarStabilization_comp a b c K L u v
  rw [hComp] at h
  have hMap : stabilization a c (K ⊗ L) (μ ≫ w) =
      Free.coefficientMap c μ ≫ stabilization a c T w :=
    (stabilization_coefficient a c μ w).symm
  have hFinal := h.trans
    (congrArg (fun z => (Free.scalarFreeIso K L c).hom ≫ z) hMap)
  simpa only [Category.assoc] using hFinal

/-- The initial coefficient is the original enriched identity, giving the actual full free identity. -/
theorem stabilization_eId (a : A) :
    stabilization a a (𝟙_ V) (eId V a) = 𝟙 (Free.object a (𝟙_ V)) := by
  apply (Free.homEquiv a (𝟙_ V) (Free.object a (𝟙_ V))).injective
  change Free.evaluate a (𝟙_ V) (Free.object a (𝟙_ V))
      (stabilization a a (𝟙_ V) (eId V a)) =
    Free.evaluate a (𝟙_ V) (Free.object a (𝟙_ V)) (𝟙 (Free.object a (𝟙_ V)))
  rw [stabilization_evaluate, Free.evaluate, component_id, Category.comp_id]
  simpa only [unitors_inv_equal] using leftUnitor_inv_naturality (eId V a)

end

section OriginalUnitCoefficientComposition

open CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uA} [Category I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (Enriched.weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (Enriched.weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (Enriched.weightedCoend.leftMap (weight d n k) S)
    (Enriched.weightedCoend.rightMap (weight d n k) S)]

/-- The full original nu stabilization and unit-source gamma compose through
the actual scalar/free isomorphisms and sphere coefficient product. Every
unit, index label, coend inclusion and enriched Hom map is retained. -/
theorem scalarNu_unitCoefficient_comp (hB : EnrichedFunctor.LaxBraidedData L) (n a : I) :
    let i : OperatorIndex d S L := ⟨𝟙_ I⟩
    let j : OperatorIndex d S L := ⟨n⟩
    let k : OperatorIndex d S L := ⟨n ⊗ a⟩
    let u := coefficientHom d S (𝟙_ I) n n (ρ_ n).hom
    let v := coefficientHom d S n (n ⊗ a) a (β_ a n).hom
    let w := coefficientHom d S (𝟙_ I) (n ⊗ a) (n ⊗ a) (ρ_ (n ⊗ a)).hom
    tensorLeftMap (S.obj n) (stabilization j k (S.obj a) v) ≫
        (Free.scalarFreeIso (S.obj n) (𝟙_ V) j).hom ≫
        Free.coefficientMap j (ρ_ (S.obj n)).hom ≫
        stabilization i j (S.obj n) u =
      (Free.scalarFreeIso (S.obj n) (S.obj a) k).hom ≫
        Free.coefficientMap k (L.mu n a) ≫
          stabilization i k (S.obj (n ⊗ a)) w := by
  let i : OperatorIndex d S L := ⟨𝟙_ I⟩
  let j : OperatorIndex d S L := ⟨n⟩
  let k : OperatorIndex d S L := ⟨n ⊗ a⟩
  let u := coefficientHom d S (𝟙_ I) n n (ρ_ n).hom
  let v := coefficientHom d S n (n ⊗ a) a (β_ a n).hom
  let w := coefficientHom d S (𝟙_ I) (n ⊗ a) (n ⊗ a) (ρ_ (n ⊗ a)).hom
  have hComp : (u ⊗ₘ v) ≫ eComp V i j k = L.mu n a ≫ w := by
    rw [operatorIndex_comp]
    exact coefficientUnit_comp d S L hB n a
  simpa only [Category.assoc] using
    scalarStabilization_comp_coefficient i j k (S.obj n) (S.obj a) (S.obj (n ⊗ a))
      u v w (L.mu n a) hComp

end OriginalUnitCoefficientComposition

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree





#lint only unusedArguments
