/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoid

/-!
# The original enriched lax tensorator satisfies Day associativity

Both entire triple-generator maps are computed using the actual flat-to-nested
isomorphisms. The full output Hom is transported by the original index
associator, while the original external tensorator supplies coefficient
associativity.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.LaxMonoid

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- Every full left flat triple generator computes the original two successive tensorators. -/
theorem leftFlat_multiply (k : I) (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d S S S k X ≫
        AssociatorFlattening.flatToNested d S S S k ≫
        Input.mapAt d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k ≫
        EnrichedFunctorCat.component (multiply d S L) k =
      (𝟙 (((X.1.1 ⊗ X.1.2) ⊗ X.2) ⟶[V] k) ⊗ₘ
        ((L.mu X.1.1 X.1.2 ▷ S.obj X.2) ≫ L.mu (X.1.1 ⊗ X.1.2) X.2)) ≫
        ActionFromTransformation.targetAction S ((X.1.1 ⊗ X.1.2) ⊗ X.2) k := by
  let a := X.1.1
  let b := X.1.2
  let c := X.2
  let A : V := S.obj a
  let B : V := S.obj b
  let C : V := S.obj c
  let ab : I := a ⊗ b
  let N : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S ab
  let H : V := (ab ⊗ c) ⟶[V] k
  let P : V := AssociatorFlat.leftPoint d S S S k
  let D : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor S S) S k
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k
  let γ : H ⊗ ((A ⊗ B) ⊗ C) ⟶ P := AssociatorFlat.leftGenerator d S S S k X
  let f : P ⟶ D := AssociatorFlattening.flatToNested d S S S k
  let δ : H ⊗ (N ⊗ C) ⟶ D :=
    gen d.tensorEnrichedFunctor (Output.functor d.tensorEnrichedFunctor S S) S k (ab, c)
  let t : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k
  let δ' : H ⊗ (S.obj ab ⊗ C) ⟶ E := gen d.tensorEnrichedFunctor S S k (ab, c)
  let m : E ⟶ S.obj k := EnrichedFunctorCat.component (multiply d S L) k
  let u : A ⊗ B ⟶ N := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S (a, b)
  let n : N ⟶ S.obj ab := EnrichedFunctorCat.component (multiply d S L) ab
  let q : A ⊗ B ⟶ S.obj ab := L.mu a b
  let r : S.obj ab ⊗ C ⟶ S.obj (ab ⊗ c) := L.mu ab c
  let z : H ⊗ S.obj (ab ⊗ c) ⟶ S.obj k := ActionFromTransformation.targetAction S (ab ⊗ c) k
  have hf : γ ≫ f = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ δ :=
    AssociatorFlattening.leftGenerator_flatToNested d S S S k X
  have ht : δ ≫ t = (𝟙 H ⊗ₘ (n ⊗ₘ 𝟙 C)) ≫ δ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (multiply d S L)
      (GradedNatTrans.unitId S) k (ab, c)).trans
      (congrArg (fun v => (𝟙 H ⊗ₘ (n ⊗ₘ v)) ≫ δ') (GradedNatTrans.unitId_component S c))
  have hm : δ' ≫ m = (𝟙 H ⊗ₘ r) ≫ z := gen_multiply d S L k (ab, c)
  have hu : u ≫ n = q := unitGenerator_multiply d S L (a, b)
  have hinner : (u ⊗ₘ 𝟙 C) ≫ (n ⊗ₘ 𝟙 C) = q ⊗ₘ 𝟙 C := by
    rw [tensorHom_comp_tensorHom, hu]
    simp only [Category.id_comp]
  have houter : (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ (n ⊗ₘ 𝟙 C)) =
      𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C) := by
    rw [tensorHom_comp_tensorHom, hinner]
    simp only [Category.id_comp]
  have hfinal : (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ r) = 𝟙 H ⊗ₘ ((q ▷ C) ≫ r) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, tensorHom_id]
  change γ ≫ f ≫ t ≫ m = (𝟙 H ⊗ₘ ((q ▷ C) ≫ r)) ≫ z
  calc
    _ = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ δ ≫ t ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫ t ≫ m) hf
    _ = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ (n ⊗ₘ 𝟙 C)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ v ≫ m) ht
    _ = (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫ δ' ≫ m) houter
    _ = (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ r) ≫ z :=
      congrArg (fun v => (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ v) hm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun v => v ≫ z) hfinal

/-- Every full right flat triple generator computes the original opposite parenthesization. -/
theorem rightFlat_multiply (k : I) (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d S S S k X ≫
        AssociatorRightFlattening.flatToNested d S S S k ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k ≫
        EnrichedFunctorCat.component (multiply d S L) k =
      (𝟙 ((X.1.1 ⊗ (X.1.2 ⊗ X.2)) ⟶[V] k) ⊗ₘ
        ((S.obj X.1.1 ◁ L.mu X.1.2 X.2) ≫ L.mu X.1.1 (X.1.2 ⊗ X.2))) ≫
        ActionFromTransformation.targetAction S (X.1.1 ⊗ (X.1.2 ⊗ X.2)) k := by
  let a := X.1.1
  let b := X.1.2
  let c := X.2
  let A : V := S.obj a
  let B : V := S.obj b
  let C : V := S.obj c
  let bc : I := b ⊗ c
  let N : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S bc
  let H : V := (a ⊗ bc) ⟶[V] k
  let P : V := AssociatorFlat.rightPoint d S S S k
  let D : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S
    (Output.functor d.tensorEnrichedFunctor S S) k
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k
  let γ : H ⊗ (A ⊗ (B ⊗ C)) ⟶ P := AssociatorFlat.rightGenerator d S S S k X
  let f : P ⟶ D := AssociatorRightFlattening.flatToNested d S S S k
  let δ : H ⊗ (A ⊗ N) ⟶ D :=
    gen d.tensorEnrichedFunctor S (Output.functor d.tensorEnrichedFunctor S S) k (a, bc)
  let t : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k
  let δ' : H ⊗ (A ⊗ S.obj bc) ⟶ E := gen d.tensorEnrichedFunctor S S k (a, bc)
  let m : E ⟶ S.obj k := EnrichedFunctorCat.component (multiply d S L) k
  let u : B ⊗ C ⟶ N := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S (b, c)
  let n : N ⟶ S.obj bc := EnrichedFunctorCat.component (multiply d S L) bc
  let q : B ⊗ C ⟶ S.obj bc := L.mu b c
  let r : A ⊗ S.obj bc ⟶ S.obj (a ⊗ bc) := L.mu a bc
  let z : H ⊗ S.obj (a ⊗ bc) ⟶ S.obj k := ActionFromTransformation.targetAction S (a ⊗ bc) k
  have hf : γ ≫ f = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ δ :=
    AssociatorRightFlattening.rightGenerator_flatToNested d S S S k X
  have ht : δ ≫ t = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ n)) ≫ δ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S)
      (multiply d S L) k (a, bc)).trans
      (congrArg (fun v => (𝟙 H ⊗ₘ (v ⊗ₘ n)) ≫ δ') (GradedNatTrans.unitId_component S a))
  have hm : δ' ≫ m = (𝟙 H ⊗ₘ r) ≫ z := gen_multiply d S L k (a, bc)
  have hu : u ≫ n = q := unitGenerator_multiply d S L (b, c)
  have hinner : (𝟙 A ⊗ₘ u) ≫ (𝟙 A ⊗ₘ n) = 𝟙 A ⊗ₘ q := by
    rw [tensorHom_comp_tensorHom, hu]
    simp only [Category.id_comp]
  have houter : (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ n)) =
      𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q) := by
    rw [tensorHom_comp_tensorHom, hinner]
    simp only [Category.id_comp]
  have hfinal : (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)) ≫ (𝟙 H ⊗ₘ r) = 𝟙 H ⊗ₘ ((A ◁ q) ≫ r) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, id_tensorHom]
  change γ ≫ f ≫ t ≫ m = (𝟙 H ⊗ₘ ((A ◁ q) ≫ r)) ≫ z
  calc
    _ = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ δ ≫ t ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫ t ≫ m) hf
    _ = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ n)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ v ≫ m) ht
    _ = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun v => v ≫ δ' ≫ m) houter
    _ = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)) ≫ (𝟙 H ⊗ₘ r) ≫ z :=
      congrArg (fun v => (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)) ≫ v) hm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun v => v ≫ z) hfinal

/-- The complete selected Day multiplication satisfies the constructed associator equation. -/
theorem multiply_assoc_component (k : I) :
    Input.mapAt d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k ≫
        EnrichedFunctorCat.component (multiply d S L) k =
      (AssociatorConstruction.componentIso d S S S k).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k ≫
        EnrichedFunctorCat.component (multiply d S L) k := by
  apply (cancel_epi (AssociatorFlattening.iso d S S S k).hom).1
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d k)
    (Associator.leftCoefficients S S S)
  intro X
  let a := X.1.1
  let b := X.1.2
  let c := X.2
  let i : I := (a ⊗ b) ⊗ c
  let j : I := a ⊗ (b ⊗ c)
  let Q : V := (S.obj a ⊗ S.obj b) ⊗ S.obj c
  let R : V := S.obj a ⊗ (S.obj b ⊗ S.obj c)
  let H : V := i ⟶[V] k
  let K : V := j ⟶[V] k
  let P : V := AssociatorFlat.leftPoint d S S S k
  let P' : V := AssociatorFlat.rightPoint d S S S k
  let D : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor
    (Output.functor d.tensorEnrichedFunctor S S) S k
  let D' : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S
    (Output.functor d.tensorEnrichedFunctor S S) k
  let E : V := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S k
  let γ : H ⊗ Q ⟶ P := AssociatorFlat.leftGenerator d S S S k X
  let δ : K ⊗ R ⟶ P' := AssociatorFlat.rightGenerator d S S S k X
  let f : P ⟶ D := AssociatorFlattening.flatToNested d S S S k
  let r : P' ⟶ D' := AssociatorRightFlattening.flatToNested d S S S k
  let α : D ⟶ D' := (AssociatorConstruction.componentIso d S S S k).hom
  let l : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor (multiply d S L) (GradedNatTrans.unitId S) k
  let n : D' ⟶ E := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId S) (multiply d S L) k
  let m : E ⟶ S.obj k := EnrichedFunctorCat.component (multiply d S L) k
  let p : Q ⟶ S.obj i := (L.mu a b ▷ S.obj c) ≫ L.mu (a ⊗ b) c
  let q : R ⟶ S.obj j := (S.obj a ◁ L.mu b c) ≫ L.mu a (b ⊗ c)
  let z : H ⊗ S.obj i ⟶ S.obj k := ActionFromTransformation.targetAction S i k
  let z' : K ⊗ S.obj j ⟶ S.obj k := ActionFromTransformation.targetAction S j k
  let w : H ⟶ K := eHomWhiskerRight V (α_ a b c).inv k
  let v : Q ⟶ R := (α_ (S.obj a) (S.obj b) (S.obj c)).hom
  let g : S.obj i ⟶ S.obj j := S.toOrdinaryFunctor.map (α_ a b c).hom
  have hleft : γ ≫ f ≫ l ≫ m = (𝟙 H ⊗ₘ p) ≫ z := leftFlat_multiply d S L k X
  have hright : δ ≫ r ≫ n ≫ m = (𝟙 K ⊗ₘ q) ≫ z' := rightFlat_multiply d S L k X
  have hα : γ ≫ f ≫ α = (w ⊗ₘ v) ≫ δ ≫ r :=
    AssociatorConstruction.tripleGenerator_hom d S S S k X
  have hc : p ≫ g = v ≫ q :=
    (Category.assoc (L.mu a b ▷ S.obj c) (L.mu (a ⊗ b) c) g).trans (L.assoc a b c)
  have hs : (𝟙 H ⊗ₘ p) ≫ z = ((𝟙 H ≫ w) ⊗ₘ (p ≫ g)) ≫ z' :=
    targetAction_sourceIso S (α_ a b c) k p (𝟙 H)
  have hid : ((𝟙 H ≫ w) ⊗ₘ (p ≫ g)) ≫ z' = (w ⊗ₘ (p ≫ g)) ≫ z' :=
    congrArg (fun h => (h ⊗ₘ (p ≫ g)) ≫ z') (Category.id_comp w)
  have ht : (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ q) = w ⊗ₘ (v ≫ q) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have ha : (𝟙 H ⊗ₘ p) ≫ z = (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ q) ≫ z' :=
    hs.trans (hid.trans ((congrArg (fun h => (w ⊗ₘ h) ≫ z') hc).trans
      (by simpa only [Category.assoc] using congrArg (fun h => h ≫ z') ht.symm)))
  have hr : γ ≫ f ≫ α ≫ n ≫ m = (w ⊗ₘ v) ≫ (𝟙 K ⊗ₘ q) ≫ z' := by
    calc
      _ = (w ⊗ₘ v) ≫ δ ≫ r ≫ n ≫ m := by
        simpa only [Category.assoc] using congrArg (fun h => h ≫ n ≫ m) hα
      _ = _ := congrArg (fun h => (w ⊗ₘ v) ≫ h) hright
  change γ ≫ f ≫ l ≫ m = γ ≫ f ≫ α ≫ n ≫ m
  exact hleft.trans (ha.trans hr.symm)

end CategoryTheory.EnrichedDayKernel.LaxMonoid
