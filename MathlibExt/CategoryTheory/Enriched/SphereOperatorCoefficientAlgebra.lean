/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightAction
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexGeneratorPoint

/-!
# Full coefficient algebra of the original operator inclusions

The two coefficient objects remain entire objects of the enriched base.
Their original inclusion maps compose by the actual late-first sphere
multiplication and the actual source label. The coefficient-index relation
uses the original weighted coend, and keeps every original ordinary index
arrow and its full coefficient action. These laws are prerequisites for the
continuous module reconstruction; no module or Day coherence law is supplied.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI uA

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits Opposite

section TensorInsertion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]

private theorem coefficientInsertion_pair_delta {H K A B : V}
    (p : (𝟙_ V) ⟶ H) (q : (𝟙_ V) ⟶ K) :
    (((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) ⊗ₘ ((λ_ B).inv ≫ (q ⊗ₘ 𝟙 B))) ≫
      tensorδ H K A B =
    (λ_ (A ⊗ B)).inv ≫
      (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ⊗ₘ 𝟙 (A ⊗ B)) := by
  let U := 𝟙_ V
  let i : A ⊗ B ⟶ (U ⊗ A) ⊗ (U ⊗ B) := (λ_ A).inv ⊗ₘ (λ_ B).inv
  let o : (U ⊗ A) ⊗ (U ⊗ B) ⟶ A ⊗ B := (λ_ A).hom ⊗ₘ (λ_ B).hom
  let delta := tensorδ U U A B
  let mu := tensorμ U U A B
  let unitPad : U ⊗ (A ⊗ B) ⟶ (U ⊗ U) ⊗ (A ⊗ B) :=
    (λ_ U).inv ▷ (A ⊗ B)
  have hPair : o ≫ i = 𝟙 ((U ⊗ A) ⊗ (U ⊗ B)) := by
    dsimp only [o, i]
    rw [tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, id_tensorHom_id]
  have hUnit : (λ_ (A ⊗ B)).hom = unitPad ≫ mu ≫ o := tensor_left_unitality A B
  have hLeft : (λ_ (A ⊗ B)).hom ≫ i ≫ delta = unitPad := by
    calc
      _ = unitPad ≫ mu ≫ o ≫ i ≫ delta := by
        simpa only [Category.assoc] using congrArg (fun z => z ≫ i ≫ delta) hUnit
      _ = unitPad ≫ mu ≫ delta := by
        rw [← Category.assoc o i delta, hPair, Category.id_comp]
      _ = unitPad := by
        rw [tensorμ_tensorδ, Category.comp_id]
  have hPad : i ≫ delta = (λ_ (A ⊗ B)).inv ≫ unitPad := by
    apply (cancel_epi (λ_ (A ⊗ B)).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hLeft
  have hNat :
      ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫ tensorδ H K A B =
        delta ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by
    have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
      (show (U, U) ⟶ (H, K) from (p, q))
      (show (A, B) ⟶ (A, B) from (𝟙 A, 𝟙 B))
    simp only [MonoidalCategory.tensor_δ] at h
    change delta ≫ ((p ⊗ₘ q) ⊗ₘ (𝟙 A ⊗ₘ 𝟙 B)) =
      ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫ tensorδ H K A B at h
    simpa only [id_tensorHom_id] using h.symm
  have hEntry :
      (((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) ⊗ₘ ((λ_ B).inv ≫ (q ⊗ₘ 𝟙 B))) =
        i ≫ ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) :=
    (tensorHom_comp_tensorHom (λ_ A).inv (λ_ B).inv (p ⊗ₘ 𝟙 A) (q ⊗ₘ 𝟙 B)).symm
  calc
    _ = i ≫ ((p ⊗ₘ 𝟙 A) ⊗ₘ (q ⊗ₘ 𝟙 B)) ≫ tensorδ H K A B := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ tensorδ H K A B) hEntry
    _ = i ≫ delta ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by rw [hNat]
    _ = (λ_ (A ⊗ B)).inv ≫ unitPad ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (A ⊗ B))) hPad
    _ = _ := by
      dsimp only [unitPad]
      rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]

end TensorInsertion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- Two complete original coefficient inclusions retain the actual source label and product. -/
theorem coefficientHom_comp (n k l a b : I) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (coefficientHom d S n k a f ⊗ₘ coefficientHom d S k l b g) ≫
        composition d S L n k l =
      ((β_ (S.obj a) (S.obj b)).hom ≫ L.mu b a) ≫
        coefficientHom d S n l (b ⊗ a) ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  let H := (a ⊗ n) ⟶[V] k
  let K := (b ⊗ k) ⟶[V] l
  let A := S.obj a
  let B := S.obj b
  let T := ((b ⊗ a) ⊗ n) ⟶[V] l
  let C := S.obj (b ⊗ a)
  let pf := eHomEquiv V f
  let pg := eHomEquiv V g
  let p : A ⟶ H ⊗ A := (λ_ A).inv ≫ (pf ⊗ₘ 𝟙 A)
  let q : B ⟶ K ⊗ B := (λ_ B).inv ≫ (pg ⊗ₘ 𝟙 B)
  let i : H ⊗ A ⟶ Hom d S n k := weightedCoend.ι (weight d n k) S a
  let j : K ⊗ B ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S b
  let z : T ⊗ C ⟶ Hom d S n l := weightedCoend.ι (weight d n l) S (b ⊗ a)
  let w : (𝟙_ V) ⟶ H ⊗ K := (λ_ (𝟙_ V)).inv ≫ (pf ⊗ₘ pg)
  let gamma : H ⊗ K ⟶ T := indexGenerator d n k l a b
  let m : A ⊗ B ⟶ C := (β_ A B).hom ≫ L.mu b a
  let label := (α_ b a n).hom ≫ (b ◁ f) ≫ g
  have hEntry :
      (coefficientHom d S n k a f ⊗ₘ coefficientHom d S k l b g) =
        (p ⊗ₘ q) ≫ (i ⊗ₘ j) :=
    (tensorHom_comp_tensorHom p q i j).symm
  have hGenerator :
      (i ⊗ₘ j) ≫ composition d S L n k l =
        tensorδ H K A B ≫ (𝟙 (H ⊗ K) ⊗ₘ (β_ A B).hom) ≫
          (gamma ⊗ₘ L.mu b a) ≫ z := composition_generator d S L n k l a b
  have hShuffle :
      (p ⊗ₘ q) ≫ tensorδ H K A B = (λ_ (A ⊗ B)).inv ≫ (w ⊗ₘ 𝟙 (A ⊗ B)) :=
    coefficientInsertion_pair_delta pf pg
  have hIndex : w ≫ gamma = eHomEquiv V label :=
    (Category.assoc (λ_ (𝟙_ V)).inv (pf ⊗ₘ pg) gamma).trans
      (indexGenerator_point d n k l a b f g)
  have hProduct :
      (w ⊗ₘ 𝟙 (A ⊗ B)) ≫ (𝟙 (H ⊗ K) ⊗ₘ (β_ A B).hom) ≫
        (gamma ⊗ₘ L.mu b a) = (w ≫ gamma) ⊗ₘ m := by
    simp only [m, tensorHom_comp_tensorHom, Category.id_comp]
  have hResult : coefficientHom d S n l (b ⊗ a) label =
      ((λ_ C).inv ≫ (eHomEquiv V label ⊗ₘ 𝟙 C)) ≫ z := rfl
  calc
    _ = (p ⊗ₘ q) ≫ (i ⊗ₘ j) ≫ composition d S L n k l := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ composition d S L n k l) hEntry
    _ = (p ⊗ₘ q) ≫ tensorδ H K A B ≫
        (𝟙 (H ⊗ K) ⊗ₘ (β_ A B).hom) ≫ (gamma ⊗ₘ L.mu b a) ≫ z := by
      rw [hGenerator]
    _ = (λ_ (A ⊗ B)).inv ≫ (w ⊗ₘ 𝟙 (A ⊗ B)) ≫
        (𝟙 (H ⊗ K) ⊗ₘ (β_ A B).hom) ≫ (gamma ⊗ₘ L.mu b a) ≫ z := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (𝟙 (H ⊗ K) ⊗ₘ (β_ A B).hom) ≫ (gamma ⊗ₘ L.mu b a) ≫ z) hShuffle
    _ = (λ_ (A ⊗ B)).inv ≫ ((w ≫ gamma) ⊗ₘ m) ≫ z := by
      simpa only [Category.assoc] using congrArg (fun t => (λ_ (A ⊗ B)).inv ≫ t ≫ z) hProduct
    _ = (λ_ (A ⊗ B)).inv ≫ (eHomEquiv V label ⊗ₘ m) ≫ z :=
      congrArg (fun t => (λ_ (A ⊗ B)).inv ≫ (t ⊗ₘ m) ≫ z) hIndex
    _ = m ≫ (λ_ C).inv ≫ (eHomEquiv V label ⊗ₘ 𝟙 C) ≫ z := by
      simpa only [tensorHom_id, Category.assoc] using congrArg
        (fun t => t ≫ z) (leftUnitor_inv_comp_tensorHom (eHomEquiv V label) m)
    _ = m ≫ (((λ_ C).inv ≫ (eHomEquiv V label ⊗ₘ 𝟙 C)) ≫ z) :=
      congrArg (fun t => m ≫ t)
        (Category.assoc (λ_ C).inv (eHomEquiv V label ⊗ₘ 𝟙 C) z).symm
    _ = _ := congrArg (fun t => m ≫ t) hResult.symm

/-- The original coend relation transfers each entire coefficient along its actual index map. -/
theorem coefficientHom_relation (n k a b : I) (u : a ⟶ b) (g : b ⊗ n ⟶ k) :
    coefficientHom d S n k a ((u ▷ n) ≫ g) =
      ((ρ_ (S.obj a)).inv ≫ S.obj a ◁ eHomEquiv V u ≫
        MonoidalClosed.uncurry (S.map a b)) ≫ coefficientHom d S n k b g := by
  let H := (b ⊗ n) ⟶[V] k
  let A := S.obj a
  let B := S.obj b
  let p : (𝟙_ V) ⟶ H := eHomEquiv V g
  let pre := eHomWhiskerRight V (u ▷ n) k
  let s : A ⟶ B := (ρ_ A).inv ≫ A ◁ eHomEquiv V u ≫ MonoidalClosed.uncurry (S.map a b)
  let i := weightedCoend.ι (weight d n k) S a
  let j := weightedCoend.ι (weight d n k) S b
  have hRel : (pre ⊗ₘ 𝟙 A) ≫ i = (𝟙 H ⊗ₘ s) ≫ j := by
    have h := weightedCoend.condition_unitPoint (weight d n k) S a b (eHomEquiv V u)
    rw [weight_point_pre, tensorHom_id] at h
    exact h
  have hp : p ≫ pre = eHomEquiv V ((u ▷ n) ≫ g) :=
    eHomEquiv_comp_eHomWhiskerRight (V := V) (C := I) (u ▷ n) g
  have hTensor :
      (p ⊗ₘ 𝟙 A) ≫ (pre ⊗ₘ 𝟙 A) = (p ≫ pre) ⊗ₘ 𝟙 A := by
    simpa only [Category.id_comp] using tensorHom_comp_tensorHom p (𝟙 A) pre (𝟙 A)
  have hTensorMap : (p ⊗ₘ 𝟙 A) ≫ (𝟙 H ⊗ₘ s) = p ⊗ₘ s := by
    simpa only [Category.comp_id, Category.id_comp] using
      tensorHom_comp_tensorHom p (𝟙 A) (𝟙 H) s
  have hInsert :
      (λ_ A).inv ≫ (p ⊗ₘ s) = s ≫ (λ_ B).inv ≫ (p ⊗ₘ 𝟙 B) := by
    rw [tensorHom_id]
    exact leftUnitor_inv_comp_tensorHom p s
  have hCohA : coefficientHom d S n k a ((u ▷ n) ≫ g) =
      ((λ_ A).inv ≫ (eHomEquiv V ((u ▷ n) ≫ g) ⊗ₘ 𝟙 A)) ≫ i := rfl
  have hCohB : coefficientHom d S n k b g =
      ((λ_ B).inv ≫ (p ⊗ₘ 𝟙 B)) ≫ j := rfl
  calc
    _ = ((λ_ A).inv ≫ ((p ≫ pre) ⊗ₘ 𝟙 A)) ≫ i :=
      hCohA.trans (congrArg (fun t => ((λ_ A).inv ≫ (t ⊗ₘ 𝟙 A)) ≫ i) hp.symm)
    _ = (λ_ A).inv ≫ (((p ≫ pre) ⊗ₘ 𝟙 A) ≫ i) := Category.assoc _ _ _
    _ = (λ_ A).inv ≫ (((p ⊗ₘ 𝟙 A) ≫ (pre ⊗ₘ 𝟙 A)) ≫ i) :=
      congrArg (fun t => (λ_ A).inv ≫ (t ≫ i)) hTensor.symm
    _ = (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ ((pre ⊗ₘ 𝟙 A) ≫ i) :=
      congrArg (fun t => (λ_ A).inv ≫ t) (Category.assoc _ _ _)
    _ = (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ ((𝟙 H ⊗ₘ s) ≫ j) :=
      congrArg (fun t => (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ t) hRel
    _ = (λ_ A).inv ≫ (((p ⊗ₘ 𝟙 A) ≫ (𝟙 H ⊗ₘ s)) ≫ j) :=
      congrArg (fun t => (λ_ A).inv ≫ t) (Category.assoc _ _ _).symm
    _ = (λ_ A).inv ≫ ((p ⊗ₘ s) ≫ j) :=
      congrArg (fun t => (λ_ A).inv ≫ (t ≫ j)) hTensorMap
    _ = ((λ_ A).inv ≫ (p ⊗ₘ s)) ≫ j := (Category.assoc _ _ _).symm
    _ = (s ≫ (λ_ B).inv ≫ (p ⊗ₘ 𝟙 B)) ≫ j := congrArg (fun t => t ≫ j) hInsert
    _ = s ≫ (((λ_ B).inv ≫ (p ⊗ₘ 𝟙 B)) ≫ j) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => s ≫ t) hCohB.symm

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits

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

omit [SymmetricCategory V] [MonoidalCategory I] [SymmetricCategory I] in
private theorem pointAction_eq_homImage (a b : I) (f : a ⟶ b) :
    (ρ_ (S.obj a)).inv ≫ S.obj a ◁ eHomEquiv V f ≫ MonoidalClosed.uncurry (S.map a b) =
      (eHomEquiv V).symm (eHomEquiv V f ≫ S.map a b) := by
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  dsimp only [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left]

/-- The whole unit-source coefficient and original nu generator compose by
actual sphere multiplication, with both source-index and coefficient braids
and all original unit/coend maps retained. -/
theorem coefficientUnit_comp (hB : EnrichedFunctor.LaxBraidedData L) (n a : I) :
    (coefficientHom d S (𝟙_ I) n n (ρ_ n).hom ⊗ₘ
      coefficientHom d S n (n ⊗ a) a (β_ a n).hom) ≫ composition d S L (𝟙_ I) n (n ⊗ a) =
    L.mu n a ≫ coefficientHom d S (𝟙_ I) (n ⊗ a) (n ⊗ a) (ρ_ (n ⊗ a)).hom := by
  rw [coefficientHom_comp]
  have hLabel : (α_ a n (𝟙_ I)).hom ≫ a ◁ (ρ_ n).hom ≫ (β_ a n).hom =
      ((β_ a n).hom ▷ (𝟙_ I)) ≫ (ρ_ (n ⊗ a)).hom := by
    have h : (α_ a n (𝟙_ I)).hom ≫ a ◁ (ρ_ n).hom = (ρ_ (a ⊗ n)).hom := by monoidal
    rw [← Category.assoc, h]
    exact (rightUnitor_naturality (β_ a n).hom).symm
  rw [hLabel, coefficientHom_relation, pointAction_eq_homImage]
  have hProduct : ((β_ (S.obj n) (S.obj a)).hom ≫ L.mu a n) ≫
      (eHomEquiv V).symm (eHomEquiv V (β_ a n).hom ≫ S.map (a ⊗ n) (n ⊗ a)) = L.mu n a := by
    calc
      _ = (β_ (S.obj n) (S.obj a)).hom ≫
          ((β_ (S.obj a) (S.obj n)).hom ≫ L.mu n a) := by
        rw [Category.assoc, hB.braided]
      _ = L.mu n a := by
        rw [SymmetricCategory.braiding_swap_eq_inv_braiding, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hProduct]

end OriginalUnitCoefficientComposition

end CategoryTheory.Enriched.SphereOperator
