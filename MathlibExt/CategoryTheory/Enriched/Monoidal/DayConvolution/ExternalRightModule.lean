/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.LaxMonoidAssembly
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ActionReconstruction
public import MathlibExt.CategoryTheory.Monoidal.RightModulePresentation

/-!
# External right actions and stock modules for actual Day convolution

The external action is the original identity-weight Day generator followed by
the stock action. Its unit and associativity laws are the source formulas for
diagram spectra. Full coend and triple-generator characteristics compare these
formulas with the stock right-module laws, using the actual Day coherence maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe uV vV uI vI

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.ExternalRightModule

open EnrichedFunctorCat
attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

/-- The original whole Day-action morphism type. -/
abbrev Action (R : EnrichedFunctorCat V I) :=
  (⟨Output.functor d.tensorEnrichedFunctor R.toEnrichedFunctor S⟩ : EnrichedFunctorCat V I) ⟶ R

/-- The complete genuine external transformation extracted from a Day action. -/
def external (R : EnrichedFunctorCat V I) (a : Action d S R) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (R.toEnrichedFunctor.externalTensor S) (d.tensorEnrichedFunctor.comp V R.toEnrichedFunctor) :=
  ActionFromTransformation.extract d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R.toEnrichedFunctor a

/-- The literal source external action on every pair of index objects. -/
def sigma (R : EnrichedFunctorCat V I) (a : Action d S R) (n j : I) :
    R.toEnrichedFunctor.obj n ⊗ S.obj j ⟶ R.toEnrichedFunctor.obj (n ⊗ j) :=
  Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫ component a (n ⊗ j)

/-- The entire component of the extracted genuine transformation is the literal source action. -/
theorem external_component (R : EnrichedFunctorCat V I) (a : Action d S R) (n j : I) :
    (eHomEquiv V).symm ((external d S R a).app (n, j)) = sigma d S R a n j :=
  ActionFromTransformation.extract_component _ _ _ _ _ _

/-- The source action retains every full output-Hom Day generator. -/
@[reassoc]
theorem gen_action (R : EnrichedFunctorCat V I) (a : Action d S R) (k n j : I) :
    gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n, j) ≫ component a k =
      (𝟙 ((n ⊗ j) ⟶[V] k) ⊗ₘ sigma d S R a n j) ≫
        ActionFromTransformation.targetAction R.toEnrichedFunctor (n ⊗ j) k :=
  (ActionFromTransformation.gen_extract _ _ _ _ a k (n, j)).symm.trans
    (congrArg (fun r => (𝟙 ((n ⊗ j) ⟶[V] k) ⊗ₘ r) ≫
      ActionFromTransformation.targetAction R.toEnrichedFunctor (n ⊗ j) k)
        (external_component d S R a n j))

/-- Every source-labelled generator recovers the literal action followed by the original map. -/
@[reassoc]
theorem labelled_action (R : EnrichedFunctorCat V I) (a : Action d S R)
    (n j : I) {k : I} (f : n ⊗ j ⟶ k) :
    (λ_ (R.toEnrichedFunctor.obj n ⊗ S.obj j)).inv ≫
        (eHomEquiv V f ⊗ₘ 𝟙 (R.toEnrichedFunctor.obj n ⊗ S.obj j)) ≫
        gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n, j) ≫ component a k =
      sigma d S R a n j ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map f := by
  let Q := R.toEnrichedFunctor.obj n ⊗ S.obj j
  let H : V := (n ⊗ j) ⟶[V] k
  let p := eHomEquiv V f
  let c := sigma d S R a n j
  let z := ActionFromTransformation.targetAction R.toEnrichedFunctor (n ⊗ j) k
  have hgen := gen_action d S R a k n j
  have ht : (p ⊗ₘ 𝟙 Q) ≫ (𝟙 H ⊗ₘ c) = p ⊗ₘ c :=
    (tensorHom_comp_tensorHom p (𝟙 Q) (𝟙 H) c).trans
      (congrArg₂ (fun r s => r ⊗ₘ s) (Category.comp_id p) (Category.id_comp c))
  have hu : (λ_ Q).inv ≫ (p ⊗ₘ c) =
      c ≫ (λ_ (R.toEnrichedFunctor.obj (n ⊗ j))).inv ≫
        (p ⊗ₘ 𝟙 (R.toEnrichedFunctor.obj (n ⊗ j))) :=
    (leftUnitor_inv_comp_tensorHom p c).trans
      (congrArg (fun r => c ≫ (λ_ (R.toEnrichedFunctor.obj (n ⊗ j))).inv ≫ r)
        (tensorHom_id p (R.toEnrichedFunctor.obj (n ⊗ j))).symm)
  let A := R.toEnrichedFunctor.obj (n ⊗ j)
  have hAssoc : ((λ_ Q).inv ≫ (p ⊗ₘ c)) ≫ z = c ≫ (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) ≫ z :=
    (congrArg (fun r => r ≫ z) hu).trans
      ((Category.assoc c ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) z).trans
        (congrArg (fun r => c ≫ r) (Category.assoc (λ_ A).inv (p ⊗ₘ 𝟙 A) z)))
  have hFirst : (λ_ Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ (𝟙 H ⊗ₘ c) ≫ z =
      ((λ_ Q).inv ≫ (p ⊗ₘ c)) ≫ z :=
    (congrArg (fun r => (λ_ Q).inv ≫ r) (Category.assoc (p ⊗ₘ 𝟙 Q) (𝟙 H ⊗ₘ c) z).symm).trans
      ((congrArg (fun r => (λ_ Q).inv ≫ r ≫ z) ht).trans (Category.assoc _ _ _).symm)
  exact (congrArg (fun r => (λ_ Q).inv ≫ (p ⊗ₘ 𝟙 Q) ≫ r) hgen).trans
    (hFirst.trans (hAssoc.trans
      (congrArg (fun r => c ≫ r) (LaxMonoid.targetAction_point R.toEnrichedFunctor f))))

/-- The actual Day descent of a genuine source transformation. -/
def descend (R : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (R.toEnrichedFunctor.externalTensor S) (d.tensorEnrichedFunctor.comp V R.toEnrichedFunctor)) :
    Action d S R :=
  ActionFromTransformation.transformation d.tensorEnrichedFunctor R.toEnrichedFunctor S
      R.toEnrichedFunctor t

/-- Descending the extracted transformation recovers the whole original Day action. -/
theorem descend_external (R : EnrichedFunctorCat V I) (a : Action d S R) :
    descend d S R (external d S R a) = a :=
  ActionFromTransformation.transformation_extract _ _ _ _ _

/-- Descending a genuine source transformation recovers each literal source action. -/
theorem sigma_descend (R : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (R.toEnrichedFunctor.externalTensor S) (d.tensorEnrichedFunctor.comp V R.toEnrichedFunctor))
    (n j : I) : sigma d S R (descend d S R t) n j = (eHomEquiv V).symm (t.app (n, j)) := by
  let x : I := n ⊗ j
  let Q : V := R.toEnrichedFunctor.obj n ⊗ S.obj j
  let A : V := R.toEnrichedFunctor.obj x
  let c : Q ⟶ A := (eHomEquiv V).symm (t.app (n, j))
  let γ := gen d.tensorEnrichedFunctor R.toEnrichedFunctor S x (n, j)
  let u := AssociatorUnit.identityInsert (V := V) x Q
  let u' := AssociatorUnit.identityInsert (V := V) x A
  let z := ActionFromTransformation.targetAction R.toEnrichedFunctor x x
  have hgen : γ ≫ component (descend d S R t) x = ((x ⟶[V] x) ◁ c) ≫ z :=
    (ActionFromTransformation.gen_transformation _ _ _ _ t x (n, j)).trans
      (ActionFromTransformation.generator_eq _ _ _ _ t x (n, j))
  have hi : u ≫ ((x ⟶[V] x) ◁ c) = c ≫ u' := AssociatorUnit.identityInsert_naturality x c
  have hz : u' ≫ z = 𝟙 A :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => (λ_ A).inv ≫ (r ⊗ₘ 𝟙 A) ≫ z) (eHomEquiv_id V x)).symm.trans
        ((LaxMonoid.targetAction_point R.toEnrichedFunctor (𝟙 x)).trans
          (R.toEnrichedFunctor.toOrdinaryFunctor.map_id x)))
  have hp : Generators.point d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) = u ≫ γ :=
    (Category.assoc _ _ _).symm
  exact (congrArg (fun r => r ≫ component (descend d S R t) x) hp).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun r => u ≫ r) hgen).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun r => r ≫ z) hi).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun r => c ≫ r) hz).trans (Category.comp_id c)))))))

/-- Both directions retain the whole genuine source transformation. -/
theorem external_descend (R : EnrichedFunctorCat V I)
    (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (R.toEnrichedFunctor.externalTensor S) (d.tensorEnrichedFunctor.comp V R.toEnrichedFunctor)) :
    external d S R (descend d S R t) = t := by
  apply GradedNatTrans.ext
  funext q
  apply (eHomEquiv V).symm.injective
  exact (external_component d S R (descend d S R t) q.1 q.2).trans (sigma_descend d S R t q.1 q.2)

omit [SymmetricCategory V] [MonoidalClosed V] [HasColimitsOfSize.{uI, uI} V]
  [MonoidalCategory I] [EnrichedOrdinaryCategory V I] in
private theorem rightInsert (A B E H : V) (p : 𝟙_ V ⟶ H) (i : 𝟙_ V ⟶ B) (e : B ⟶ E) :
    (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) ≫
        (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)) =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)) ≫ (λ_ (A ⊗ E)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ E)) := by
  let g := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ i)
  let q := 𝟙 A ⊗ₘ e
  have hg : g ≫ q = (ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun r => (ρ_ A).inv ≫ r)
        ((tensorHom_comp_tensorHom (𝟙 A) i (𝟙 A) e).trans
          (congrArg (fun r => r ⊗ₘ (i ≫ e)) (Category.id_comp (𝟙 A)))))
  have ht : (p ⊗ₘ g) ≫ (𝟙 H ⊗ₘ q) = p ⊗ₘ (g ≫ q) :=
    (tensorHom_comp_tensorHom p g (𝟙 H) q).trans
      (congrArg (fun r => r ⊗ₘ (g ≫ q)) (Category.comp_id p))
  have hUnitor := leftUnitor_inv_comp_tensorHom p ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e)))
  exact (congrArg (fun r => (λ_ A).inv ≫ r) ht).trans
      ((congrArg (fun r => (λ_ A).inv ≫ (p ⊗ₘ r)) hg).trans
        (hUnitor.trans ((congrArg (fun r => ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ (i ≫ e))) ≫
          (λ_ (A ⊗ E)).inv ≫ r) (tensorHom_id p (A ⊗ E)).symm).trans
            (Category.assoc _ _ _))))

/-- The complete actual right-unitor inverse computes the source unit composite. -/
theorem rightInv_unit_action (R : EnrichedFunctorCat V I) (a : Action d S R) (k : I) :
    (Unitors.rightInvComponent d R.toEnrichedFunctor k ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
            (LaxMonoid.unit d S L) k) ≫
        component a k =
      ((ρ_ (R.toEnrichedFunctor.obj k)).inv ≫ (R.toEnrichedFunctor.obj k ◁ L.epsilon)) ≫
        (sigma d S R a k (𝟙_ I) ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom) := by
  let A := R.toEnrichedFunctor.obj k
  let B : V := (𝟙_ I) ⟶[V] (𝟙_ I)
  let E := S.obj (𝟙_ I)
  let H : V := (k ⊗ (𝟙_ I)) ⟶[V] k
  let p := eHomEquiv V (ρ_ k).hom
  let i := eId V (𝟙_ I)
  let e := component (LaxMonoid.unit d S L) (𝟙_ I)
  let γ := gen d.tensorEnrichedFunctor R.toEnrichedFunctor
      (GradedYoneda.representable (𝟙_ I)) k (k, 𝟙_ I)
  let γ' := gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (k, 𝟙_ I)
  let f := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
      (LaxMonoid.unit d S L) k
  let m := component a k
  let q : A ⟶ H ⊗ (A ⊗ B) := (λ_ A).inv ≫ (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i)))
  let b : H ⊗ (A ⊗ B) ⟶ H ⊗ (A ⊗ E) := 𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)
  let lbl : A ⊗ E ⟶ H ⊗ (A ⊗ E) := (λ_ (A ⊗ E)).inv ≫ (p ⊗ₘ 𝟙 (A ⊗ E))
  let c : A ⟶ A ⊗ E := (ρ_ A).inv ≫ (𝟙 A ⊗ₘ L.epsilon)
  have hMap : γ ≫ f = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ e)) ≫ γ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
        (LaxMonoid.unit d S L) k (k, 𝟙_ I)).trans
      (congrArg (fun r => (𝟙 H ⊗ₘ (r ⊗ₘ e)) ≫ γ')
          (GradedNatTrans.unitId_component R.toEnrichedFunctor k))
  have hUnit : i ≫ e = L.epsilon := LaxMonoid.unit_epsilon d S L
  have hLabel : lbl ≫ (γ' ≫ m) = sigma d S R a k (𝟙_ I) ≫
      R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom :=
    (Category.assoc _ _ _).trans (labelled_action d S R a k (𝟙_ I) (ρ_ k).hom)
  have hInv : Unitors.rightInvComponent d R.toEnrichedFunctor k = q ≫ γ :=
    (Category.assoc _ _ _).symm
  have hQB : q ≫ b = c ≫ lbl :=
    (Category.assoc (λ_ A).inv (p ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ i))) b).trans
    ((rightInsert A B E H p i e).trans
      ((Category.assoc (ρ_ A).inv (𝟙 A ⊗ₘ (i ≫ e)) lbl).symm.trans
        (congrArg (fun r => ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ r)) ≫ lbl) hUnit)))
  have hCF : c = (ρ_ A).inv ≫ (A ◁ L.epsilon) :=
    congrArg (fun r => (ρ_ A).inv ≫ r) (id_tensorHom A L.epsilon)
  exact (congrArg (fun r => (r ≫ f) ≫ m) hInv).trans
    ((congrArg (fun r => r ≫ m) (Category.assoc q γ f)).trans
      ((congrArg (fun r => (q ≫ r) ≫ m) hMap).trans
        ((congrArg (fun r => r ≫ m) (Category.assoc q b γ').symm).trans
          ((congrArg (fun r => (r ≫ γ') ≫ m) hQB).trans
            ((Category.assoc (c ≫ lbl) γ' m).trans
              ((Category.assoc c lbl (γ' ≫ m)).trans
                ((congrArg (fun r => c ≫ r) hLabel).trans
                  (congrArg (fun r => r ≫ (sigma d S R a k (𝟙_ I) ≫
                    R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom)) hCF))))))))

/-- The identity generator in the constructed associator is the same literal external action. -/
theorem unitGenerator_sigma (R : EnrichedFunctorCat V I) (a : Action d S R) (n j : I) :
    AssociatorUnit.unitGenerator d.tensorEnrichedFunctor R.toEnrichedFunctor S (n, j) ≫
        component a (n ⊗ j) = sigma d S R a n j :=
  congrArg (fun r => r ≫ component a (n ⊗ j)) (Category.assoc _ _ _)

/-- Every full left triple generator computes two successive external module actions. -/
theorem leftFlat_action (R : EnrichedFunctorCat V I) (a : Action d S R)
    (k : I) (x : (I × I) × I) :
    AssociatorFlat.leftGenerator d R.toEnrichedFunctor S S k x ≫
        AssociatorFlattening.flatToNested d R.toEnrichedFunctor S S k ≫
        Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k ≫ component a k =
      (𝟙 (((x.1.1 ⊗ x.1.2) ⊗ x.2) ⟶[V] k) ⊗ₘ
        ((sigma d S R a x.1.1 x.1.2 ▷ S.obj x.2) ≫ sigma d S R a (x.1.1 ⊗ x.1.2) x.2)) ≫
        ActionFromTransformation.targetAction R.toEnrichedFunctor ((x.1.1 ⊗ x.1.2) ⊗ x.2) k := by
  let n := x.1.1
  let j := x.1.2
  let b := x.2
  let A := R.toEnrichedFunctor.obj n
  let B := S.obj j
  let C := S.obj b
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor S (n ⊗ j)
  let H : V := ((n ⊗ j) ⊗ b) ⟶[V] k
  let P := AssociatorFlat.leftPoint d R.toEnrichedFunctor S S k
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor R.toEnrichedFunctor S) S k
  let E := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor S k
  let γ : H ⊗ ((A ⊗ B) ⊗ C) ⟶ P := AssociatorFlat.leftGenerator d R.toEnrichedFunctor S S k x
  let f : P ⟶ D := AssociatorFlattening.flatToNested d R.toEnrichedFunctor S S k
  let δ : H ⊗ (N ⊗ C) ⟶ D := gen d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor R.toEnrichedFunctor S) S k (n ⊗ j, b)
  let t : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k
  let δ' : H ⊗ (R.toEnrichedFunctor.obj (n ⊗ j) ⊗ C) ⟶ E :=
      gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n ⊗ j, b)
  let m := component a k
  let u : A ⊗ B ⟶ N := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor
      R.toEnrichedFunctor S (n, j)
  let v := component a (n ⊗ j)
  let q := sigma d S R a n j
  let r := sigma d S R a (n ⊗ j) b
  let z := ActionFromTransformation.targetAction R.toEnrichedFunctor ((n ⊗ j) ⊗ b) k
  have hf : γ ≫ f = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ δ :=
      AssociatorFlattening.leftGenerator_flatToNested d R.toEnrichedFunctor S S k x
  have ht : δ ≫ t = (𝟙 H ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ δ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k (n ⊗ j, b)).trans
      (congrArg (fun s => (𝟙 H ⊗ₘ (v ⊗ₘ s)) ≫ δ') (GradedNatTrans.unitId_component S b))
  have hm : δ' ≫ m = (𝟙 H ⊗ₘ r) ≫ z := gen_action d S R a k (n ⊗ j) b
  have hu : u ≫ v = q := unitGenerator_sigma d S R a n j
  have hinner : (u ⊗ₘ 𝟙 C) ≫ (v ⊗ₘ 𝟙 C) = q ⊗ₘ 𝟙 C :=
    (tensorHom_comp_tensorHom u (𝟙 C) v (𝟙 C)).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) hu (Category.id_comp (𝟙 C)))
  have houter : (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ (v ⊗ₘ 𝟙 C)) = 𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C) :=
    (tensorHom_comp_tensorHom (𝟙 H) (u ⊗ₘ 𝟙 C) (𝟙 H) (v ⊗ₘ 𝟙 C)).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Category.id_comp (𝟙 H)) hinner)
  have hfinal : (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ r) = 𝟙 H ⊗ₘ ((q ▷ C) ≫ r) :=
    (tensorHom_comp_tensorHom (𝟙 H) (q ⊗ₘ 𝟙 C) (𝟙 H) r).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Category.id_comp (𝟙 H))
        (congrArg (fun s => s ≫ r) (tensorHom_id q C)))
  change γ ≫ f ≫ t ≫ m = (𝟙 H ⊗ₘ ((q ▷ C) ≫ r)) ≫ z
  calc
    _ = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ δ ≫ t ≫ m := by
      simpa only [Category.assoc] using congrArg (fun s => s ≫ t ≫ m) hf
    _ = (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ (v ⊗ₘ 𝟙 C)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun s => (𝟙 H ⊗ₘ (u ⊗ₘ 𝟙 C)) ≫ s ≫ m) ht
    _ = (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ δ' ≫ m := by
      simpa only [Category.assoc] using congrArg (fun s => s ≫ δ' ≫ m) houter
    _ = (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ (𝟙 H ⊗ₘ r) ≫ z := congrArg (fun s => (𝟙 H ⊗ₘ (q ⊗ₘ 𝟙 C)) ≫ s) hm
    _ = _ := by simpa only [Category.assoc] using congrArg (fun s => s ≫ z) hfinal

/-- Every full right triple generator computes the original sphere product followed by the external
action. -/
theorem rightFlat_action (R : EnrichedFunctorCat V I) (a : Action d S R)
    (k : I) (x : (I × I) × I) :
    AssociatorFlat.rightGenerator d R.toEnrichedFunctor S S k x ≫
        AssociatorRightFlattening.flatToNested d R.toEnrichedFunctor S S k ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
            (LaxMonoid.multiply d S L) k ≫
        component a k =
      (𝟙 ((x.1.1 ⊗ (x.1.2 ⊗ x.2)) ⟶[V] k) ⊗ₘ
        ((R.toEnrichedFunctor.obj x.1.1 ◁ L.mu x.1.2 x.2) ≫ sigma d S R a x.1.1 (x.1.2 ⊗ x.2))) ≫
        ActionFromTransformation.targetAction R.toEnrichedFunctor (x.1.1 ⊗ (x.1.2 ⊗ x.2)) k := by
  let n := x.1.1
  let j := x.1.2
  let b := x.2
  let A := R.toEnrichedFunctor.obj n
  let B := S.obj j
  let C := S.obj b
  let N := EnrichedDayKernel.obj d.tensorEnrichedFunctor S S (j ⊗ b)
  let H : V := (n ⊗ (j ⊗ b)) ⟶[V] k
  let P := AssociatorFlat.rightPoint d R.toEnrichedFunctor S S k
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor S S) k
  let E := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor S k
  let γ : H ⊗ (A ⊗ (B ⊗ C)) ⟶ P := AssociatorFlat.rightGenerator d R.toEnrichedFunctor S S k x
  let f : P ⟶ D := AssociatorRightFlattening.flatToNested d R.toEnrichedFunctor S S k
  let δ : H ⊗ (A ⊗ N) ⟶ D := gen d.tensorEnrichedFunctor R.toEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor S S) k (n, j ⊗ b)
  let t : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
      (LaxMonoid.multiply d S L) k
  let δ' : H ⊗ (A ⊗ S.obj (j ⊗ b)) ⟶ E :=
      gen d.tensorEnrichedFunctor R.toEnrichedFunctor S k (n, j ⊗ b)
  let m := component a k
  let u := AssociatorUnit.unitGenerator d.tensorEnrichedFunctor S S (j, b)
  let v := component (LaxMonoid.multiply d S L) (j ⊗ b)
  let q := L.mu j b
  let r := sigma d S R a n (j ⊗ b)
  let z := ActionFromTransformation.targetAction R.toEnrichedFunctor (n ⊗ (j ⊗ b)) k
  have hf : γ ≫ f = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ δ :=
      AssociatorRightFlattening.rightGenerator_flatToNested d R.toEnrichedFunctor S S k x
  have ht : δ ≫ t = (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ v)) ≫ δ' :=
    (Input.gen_mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
        (LaxMonoid.multiply d S L) k (n, j ⊗ b)).trans
      (congrArg (fun s => (𝟙 H ⊗ₘ (s ⊗ₘ v)) ≫ δ')
          (GradedNatTrans.unitId_component R.toEnrichedFunctor n))
  have hm : δ' ≫ m = (𝟙 H ⊗ₘ r) ≫ z := gen_action d S R a k n (j ⊗ b)
  have hu : u ≫ v = q := LaxMonoid.unitGenerator_multiply d S L (j, b)
  have hinner : (𝟙 A ⊗ₘ u) ≫ (𝟙 A ⊗ₘ v) = 𝟙 A ⊗ₘ q :=
    (tensorHom_comp_tensorHom (𝟙 A) u (𝟙 A) v).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Category.id_comp (𝟙 A)) hu)
  have houter : (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)) ≫ (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ v)) = 𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q) :=
    (tensorHom_comp_tensorHom (𝟙 H) (𝟙 A ⊗ₘ u) (𝟙 H) (𝟙 A ⊗ₘ v)).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Category.id_comp (𝟙 H)) hinner)
  have hfinal : (𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)) ≫ (𝟙 H ⊗ₘ r) = 𝟙 H ⊗ₘ ((A ◁ q) ≫ r) :=
    (tensorHom_comp_tensorHom (𝟙 H) (𝟙 A ⊗ₘ q) (𝟙 H) r).trans
      (congrArg₂ (fun s t => s ⊗ₘ t) (Category.id_comp (𝟙 H))
        (congrArg (fun s => s ≫ r) (id_tensorHom A q)))
  let c0 := 𝟙 H ⊗ₘ (𝟙 A ⊗ₘ u)
  let c1 := 𝟙 H ⊗ₘ (𝟙 A ⊗ₘ v)
  let c2 := 𝟙 H ⊗ₘ (𝟙 A ⊗ₘ q)
  let c3 := 𝟙 H ⊗ₘ r
  change γ ≫ f ≫ t ≫ m = (𝟙 H ⊗ₘ ((A ◁ q) ≫ r)) ≫ z
  exact (Category.assoc γ f (t ≫ m)).symm.trans
    ((congrArg (fun s => s ≫ (t ≫ m)) hf).trans
      ((Category.assoc c0 δ (t ≫ m)).trans
        ((congrArg (fun s => c0 ≫ s) (Category.assoc δ t m).symm).trans
          ((congrArg (fun s => c0 ≫ s ≫ m) ht).trans
            ((congrArg (fun s => c0 ≫ s) (Category.assoc c1 δ' m)).trans
              ((Category.assoc c0 c1 (δ' ≫ m)).symm.trans
                ((congrArg (fun s => s ≫ δ' ≫ m) houter).trans
                  ((congrArg (fun s => c2 ≫ s) hm).trans
                    ((Category.assoc c2 c3 z).symm.trans
                      (congrArg (fun s => s ≫ z) hfinal))))))))))

/-- The MMSS external unit law for the literal extracted action. -/
def UnitLaw (R : EnrichedFunctorCat V I) (a : Action d S R) : Prop :=
  ∀ n : I, (R.toEnrichedFunctor.obj n ◁ L.epsilon) ≫ sigma d S R a n (𝟙_ I) ≫
    R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom = (ρ_ (R.toEnrichedFunctor.obj n)).hom

/-- The MMSS external associativity law retains both ambient and index associators. -/
def AssocLaw (R : EnrichedFunctorCat V I) (a : Action d S R) : Prop :=
  ∀ n j b : I, (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).inv ≫
      (sigma d S R a n j ▷ S.obj b) ≫ sigma d S R a (n ⊗ j) b =
    (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫ sigma d S R a n (j ⊗ b) ≫
      R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv

/-- The actual Day inverse right unitor turns the whole unit equation into its source composite. -/
theorem one_unit_formula (R : EnrichedFunctorCat V I) (a : Action d S R) (k : I) :
    letI := ColimitMonoidal.monoidalCategory d
    component (((ρ_ R).inv ≫ (R ◁ LaxMonoid.unit d S L)) ≫ a) k =
      ((ρ_ (R.toEnrichedFunctor.obj k)).inv ≫ (R.toEnrichedFunctor.obj k ◁ L.epsilon)) ≫
        (sigma d S R a k (𝟙_ I) ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let q := (ρ_ R).inv
  let p := R ◁ LaxMonoid.unit d S L
  have hq : component q k = Unitors.rightInvComponent d R.toEnrichedFunctor k :=
    Unitors.rightUnitorInv_component d R.toEnrichedFunctor k
  have hp : component p k = Input.mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId R.toEnrichedFunctor) (LaxMonoid.unit d S L) k :=
    Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
        (LaxMonoid.unit d S L) k
  exact (component_comp (q ≫ p) a k).trans
    ((congrArg (fun s => s ≫ component a k) ((component_comp q p k).trans
      (congrArg₂ (fun s t => s ≫ t) hq hp))).trans (rightInv_unit_action d S L R a k))

/-- The source unit law and the stock whole Day unit equation are genuinely equivalent. -/
theorem unit_iff (R : EnrichedFunctorCat V I) (a : Action d S R) :
    UnitLaw d S L R a ↔
      (letI := ColimitMonoidal.monoidalCategory d
       (R ◁ LaxMonoid.unit d S L) ≫ a = (ρ_ R).hom) := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  constructor
  · intro h
    have hi : (((ρ_ R).inv ≫ (R ◁ LaxMonoid.unit d S L)) ≫ a) = 𝟙 R := by
      apply EnrichedFunctorCat.hom_ext
      intro k
      let A := R.toEnrichedFunctor.obj k
      let u := A ◁ L.epsilon
      let v := sigma d S R a k (𝟙_ I) ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom
      exact (one_unit_formula d S L R a k).trans
        ((Category.assoc (ρ_ A).inv u v).trans
          ((congrArg (fun s => (ρ_ A).inv ≫ s) (h k)).trans
            ((Iso.inv_hom_id (ρ_ A)).trans (component_id R k).symm)))
    apply (cancel_epi (ρ_ R).inv).1
    exact (Category.assoc _ _ _).symm.trans (hi.trans (Iso.inv_hom_id (ρ_ R)).symm)
  · intro h k
    have hi : (((ρ_ R).inv ≫ (R ◁ LaxMonoid.unit d S L)) ≫ a) = 𝟙 R :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun s => (ρ_ R).inv ≫ s) h).trans (Iso.inv_hom_id (ρ_ R)))
    let A := R.toEnrichedFunctor.obj k
    let u := A ◁ L.epsilon
    let v := sigma d S R a k (𝟙_ I) ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ k).hom
    have hc : ((ρ_ A).inv ≫ u) ≫ v = 𝟙 A :=
      (one_unit_formula d S L R a k).symm.trans
        ((congrArg (fun s => component s k) hi).trans (component_id R k))
    apply (cancel_epi (ρ_ A).inv).1
    exact (Category.assoc (ρ_ A).inv u v).symm.trans
      (hc.trans (Iso.inv_hom_id (ρ_ A)).symm)

/-- The full external unit law is derived from the original stock module's one-action axiom. -/
theorem stock_sigma_unit :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      UnitLaw d S L M.X M.action := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M
  apply (unit_iff d S L M.X M.action).2
  exact CommutativeModuleConversion.RightModule.one_action M

private theorem assoc_coefficient (R : EnrichedFunctorCat V I) (a : Action d S R)
    (h : AssocLaw d S L R a) (n j b : I) :
    ((sigma d S R a n j ▷ S.obj b) ≫ sigma d S R a (n ⊗ j) b) ≫
        R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).hom =
      (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).hom ≫
        ((R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫ sigma d S R a n (j ⊗ b)) := by
  let v := α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)
  let e := R.toEnrichedFunctor.toOrdinaryFunctor.mapIso (α_ n j b)
  let p := (sigma d S R a n j ▷ S.obj b) ≫ sigma d S R a (n ⊗ j) b
  let q := (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫ sigma d S R a n (j ⊗ b)
  have hp : v.inv ≫ p = q ≫ e.inv := (h n j b).trans (Category.assoc _ _ _).symm
  have hr : p = v.hom ≫ q ≫ e.inv :=
    (v.hom_inv_id_assoc p).symm.trans (congrArg (fun r => v.hom ≫ r) hp)
  exact (congrArg (fun r => r ≫ e.hom) hr).trans
    ((Category.assoc v.hom (q ≫ e.inv) e.hom).trans
      ((congrArg (fun r => v.hom ≫ r) (Category.assoc q e.inv e.hom)).trans
        ((congrArg (fun r => v.hom ≫ q ≫ r) e.inv_hom_id).trans
          (congrArg (fun r => v.hom ≫ r) (Category.comp_id q)))))

/-- The source associativity law descends on every whole left-flat triple coend generator. -/
theorem assoc_component (R : EnrichedFunctorCat V I) (a : Action d S R)
    (h : AssocLaw d S L R a) (k : I) :
    Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k ≫ component a k =
      (AssociatorConstruction.componentIso d R.toEnrichedFunctor S S k).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
            (LaxMonoid.multiply d S L) k ≫
        component a k := by
  apply (cancel_epi (AssociatorFlattening.iso d R.toEnrichedFunctor S S k).hom).1
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d k)
    (Associator.leftCoefficients R.toEnrichedFunctor S S)
  intro x
  let n := x.1.1
  let j := x.1.2
  let b := x.2
  let i : I := (n ⊗ j) ⊗ b
  let i' : I := n ⊗ (j ⊗ b)
  let Q : V := (R.toEnrichedFunctor.obj n ⊗ S.obj j) ⊗ S.obj b
  let Q' : V := R.toEnrichedFunctor.obj n ⊗ (S.obj j ⊗ S.obj b)
  let H : V := i ⟶[V] k
  let H' : V := i' ⟶[V] k
  let P := AssociatorFlat.leftPoint d R.toEnrichedFunctor S S k
  let P' := AssociatorFlat.rightPoint d R.toEnrichedFunctor S S k
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor R.toEnrichedFunctor S) S k
  let D' := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor S S) k
  let E := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor S k
  let γ : H ⊗ Q ⟶ P := AssociatorFlat.leftGenerator d R.toEnrichedFunctor S S k x
  let δ : H' ⊗ Q' ⟶ P' := AssociatorFlat.rightGenerator d R.toEnrichedFunctor S S k x
  let f : P ⟶ D := AssociatorFlattening.flatToNested d R.toEnrichedFunctor S S k
  let r : P' ⟶ D' := AssociatorRightFlattening.flatToNested d R.toEnrichedFunctor S S k
  let α : D ⟶ D' := (AssociatorConstruction.componentIso d R.toEnrichedFunctor S S k).hom
  let l : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k
  let m : D' ⟶ E := Input.mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId R.toEnrichedFunctor) (LaxMonoid.multiply d S L) k
  let z := component a k
  let p : Q ⟶ R.toEnrichedFunctor.obj i := (sigma d S R a n j ▷ S.obj b) ≫ sigma d S R a (n ⊗ j) b
  let q : Q' ⟶ R.toEnrichedFunctor.obj i' := (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫
      sigma d S R a n (j ⊗ b)
  let v : Q ⟶ Q' := (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).hom
  let w : H ⟶ H' := eHomWhiskerRight V (α_ n j b).inv k
  let g := R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).hom
  let act := ActionFromTransformation.targetAction R.toEnrichedFunctor i k
  let act' := ActionFromTransformation.targetAction R.toEnrichedFunctor i' k
  have hl : γ ≫ f ≫ l ≫ z = (𝟙 H ⊗ₘ p) ≫ act := leftFlat_action d S R a k x
  have hr : δ ≫ r ≫ m ≫ z = (𝟙 H' ⊗ₘ q) ≫ act' := rightFlat_action d S L R a k x
  have ha : γ ≫ f ≫ α = (w ⊗ₘ v) ≫ δ ≫ r :=
    AssociatorConstruction.tripleGenerator_hom d R.toEnrichedFunctor S S k x
  have hc : p ≫ g = v ≫ q := assoc_coefficient d S L R a h n j b
  have hs : (𝟙 H ⊗ₘ p) ≫ act = ((𝟙 H ≫ w) ⊗ₘ (p ≫ g)) ≫ act' :=
    LaxMonoid.targetAction_sourceIso R.toEnrichedFunctor (α_ n j b) k p (𝟙 H)
  have ht : (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) = w ⊗ₘ (v ≫ q) :=
    (tensorHom_comp_tensorHom w v (𝟙 H') q).trans
      (congrArg (fun r => r ⊗ₘ (v ≫ q)) (Category.comp_id w))
  have hcoef : (𝟙 H ⊗ₘ p) ≫ act = (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) ≫ act' :=
    hs.trans ((congrArg (fun r => (r ⊗ₘ (p ≫ g)) ≫ act') (Category.id_comp w)).trans
      ((congrArg (fun r => (w ⊗ₘ r) ≫ act') hc).trans
        ((congrArg (fun r => r ≫ act') ht.symm).trans (Category.assoc _ _ _))))
  have hright : γ ≫ f ≫ α ≫ m ≫ z = (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) ≫ act' := by
    calc
      _ = (w ⊗ₘ v) ≫ δ ≫ r ≫ m ≫ z := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ m ≫ z) ha
      _ = _ := congrArg (fun t => (w ⊗ₘ v) ≫ t) hr
  change γ ≫ f ≫ l ≫ z = γ ≫ f ≫ α ≫ m ≫ z
  exact hl.trans (hcoef.trans hright.symm)

/-- Exact source associativity gives the whole original stock Day associativity equation. -/
theorem source_assoc_to_day (R : EnrichedFunctorCat V I) (a : Action d S R)
    (h : AssocLaw d S L R a) :
    letI := ColimitMonoidal.monoidalCategory d
    (a ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ a =
      (α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom ≫ (R ◁ LaxMonoid.multiply d S L) ≫ a := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  apply EnrichedFunctorCat.hom_ext
  intro k
  have hl : component (a ▷ (⟨S⟩ : EnrichedFunctorCat V I)) k =
      Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k :=
    Input.natTrans_component d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) k
  have hr : component (R ◁ LaxMonoid.multiply d S L) k =
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
          (LaxMonoid.multiply d S L) k :=
    Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
        (LaxMonoid.multiply d S L) k
  have ha : component (α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom k =
      (AssociatorConstruction.componentIso d R.toEnrichedFunctor S S k).hom :=
    AssociatorConstruction.functorIso_hom_component d R.toEnrichedFunctor S S k
  exact (component_comp _ _ k).trans
    ((congrArg (fun t => t ≫ component a k) hl).trans
      ((assoc_component d S L R a h k).trans
        ((congrArg₂ (fun s t => s ≫ t) ha.symm
          ((congrArg (fun t => t ≫ component a k) hr.symm).trans (component_comp _ _ k).symm)).trans
            (component_comp _ _ k).symm)))

omit [MonoidalCategory I] [HasColimitsOfSize.{uI, uI} V] in
private theorem identityInsert_target (F : EnrichedFunctor V I V) (x : I) (Q : V)
    (c : Q ⟶ F.obj x) :
    (AssociatorUnit.identityInsert (V := V) x Q ≫ (𝟙 (x ⟶[V] x) ⊗ₘ c)) ≫
      ActionFromTransformation.targetAction F x x = c := by
  let z := ActionFromTransformation.targetAction F x x
  let u := AssociatorUnit.identityInsert (V := V) x Q
  let u' := AssociatorUnit.identityInsert (V := V) x (F.obj x)
  have hm : u ≫ (𝟙 (x ⟶[V] x) ⊗ₘ c) = c ≫ u' :=
    (congrArg (fun r => u ≫ r) (id_tensorHom (x ⟶[V] x) c)).trans
      (AssociatorUnit.identityInsert_naturality x c)
  have hz : u' ≫ z = 𝟙 (F.obj x) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => (λ_ (F.obj x)).inv ≫ (r ⊗ₘ 𝟙 (F.obj x)) ≫ z)
          (eHomEquiv_id V x)).symm.trans
        ((LaxMonoid.targetAction_point F (𝟙 x)).trans (F.toOrdinaryFunctor.map_id x)))
  exact (congrArg (fun r => r ≫ z) hm).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun r => c ≫ r) hz).trans (Category.comp_id c)))

omit [MonoidalCategory I] [HasColimitsOfSize.{uI, uI} V] in
private theorem identityInsert_source (F : EnrichedFunctor V I V) {x y : I}
    (f : y ⟶ x) (Q : V) (c : Q ⟶ F.obj y)
    (w : (x ⟶[V] x) ⟶ (y ⟶[V] x)) (hw : eId V x ≫ w = eHomEquiv V f) :
    (AssociatorUnit.identityInsert (V := V) x Q ≫ (w ⊗ₘ c)) ≫
      ActionFromTransformation.targetAction F y x = c ≫ F.toOrdinaryFunctor.map f := by
  let z := ActionFromTransformation.targetAction F y x
  have ht : (eId V x ⊗ₘ 𝟙 Q) ≫ (w ⊗ₘ c) = eHomEquiv V f ⊗ₘ c :=
    (tensorHom_comp_tensorHom (eId V x) (𝟙 Q) w c).trans
      (congrArg₂ (fun r s => r ⊗ₘ s) hw (Category.id_comp c))
  have hi : AssociatorUnit.identityInsert (V := V) x Q ≫ (w ⊗ₘ c) =
      (λ_ Q).inv ≫ (eHomEquiv V f ⊗ₘ c) :=
    (Category.assoc _ _ _).trans (congrArg (fun r => (λ_ Q).inv ≫ r) ht)
  have hu : (λ_ Q).inv ≫ (eHomEquiv V f ⊗ₘ c) =
      c ≫ (λ_ (F.obj y)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (F.obj y)) :=
    (leftUnitor_inv_comp_tensorHom (eHomEquiv V f) c).trans
      (congrArg (fun r => c ≫ (λ_ (F.obj y)).inv ≫ r) (tensorHom_id (eHomEquiv V f) (F.obj y)).symm)
  exact (congrArg (fun r => r ≫ z) hi).trans
    ((congrArg (fun r => r ≫ z) hu).trans
      ((Category.assoc c ((λ_ (F.obj y)).inv ≫ (eHomEquiv V f ⊗ₘ 𝟙 (F.obj y))) z).trans
        ((congrArg (fun r => c ≫ r) (Category.assoc (λ_ (F.obj y)).inv
          (eHomEquiv V f ⊗ₘ 𝟙 (F.obj y)) z)).trans
            (congrArg (fun r => c ≫ r) (LaxMonoid.targetAction_point F f)))))

/-- The stock whole Day associativity equation yields the exact MMSS source law. -/
theorem day_assoc_to_source (R : EnrichedFunctorCat V I) (a : Action d S R) :
    (letI := ColimitMonoidal.monoidalCategory d
     (a ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ a =
       (α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom ≫ (R ◁ LaxMonoid.multiply d S L) ≫ a) →
      AssocLaw d S L R a := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  intro h n j b
  let i : I := (n ⊗ j) ⊗ b
  let i' : I := n ⊗ (j ⊗ b)
  let Q : V := (R.toEnrichedFunctor.obj n ⊗ S.obj j) ⊗ S.obj b
  let Q' : V := R.toEnrichedFunctor.obj n ⊗ (S.obj j ⊗ S.obj b)
  let H : V := i ⟶[V] i
  let H' : V := i' ⟶[V] i
  let P := AssociatorFlat.leftPoint d R.toEnrichedFunctor S S i
  let P' := AssociatorFlat.rightPoint d R.toEnrichedFunctor S S i
  let D := EnrichedDayKernel.obj d.tensorEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor R.toEnrichedFunctor S) S i
  let D' := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor
      (Output.functor d.tensorEnrichedFunctor S S) i
  let E := EnrichedDayKernel.obj d.tensorEnrichedFunctor R.toEnrichedFunctor S i
  let γ : H ⊗ Q ⟶ P := AssociatorFlat.leftGenerator d R.toEnrichedFunctor S S i ((n, j), b)
  let δ : H' ⊗ Q' ⟶ P' := AssociatorFlat.rightGenerator d R.toEnrichedFunctor S S i ((n, j), b)
  let f : P ⟶ D := AssociatorFlattening.flatToNested d R.toEnrichedFunctor S S i
  let f' : P' ⟶ D' := AssociatorRightFlattening.flatToNested d R.toEnrichedFunctor S S i
  let α : D ⟶ D' := (AssociatorConstruction.componentIso d R.toEnrichedFunctor S S i).hom
  let l : D ⟶ E := Input.mapAt d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) i
  let r : D' ⟶ E := Input.mapAt d.tensorEnrichedFunctor
      (GradedNatTrans.unitId R.toEnrichedFunctor) (LaxMonoid.multiply d S L) i
  let m := component a i
  let p : Q ⟶ R.toEnrichedFunctor.obj i := (sigma d S R a n j ▷ S.obj b) ≫ sigma d S R a (n ⊗ j) b
  let q : Q' ⟶ R.toEnrichedFunctor.obj i' := (R.toEnrichedFunctor.obj n ◁ L.mu j b) ≫
      sigma d S R a n (j ⊗ b)
  let v : Q ⟶ Q' := (α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)).hom
  let w : H ⟶ H' := eHomWhiskerRight V (α_ n j b).inv i
  let z := ActionFromTransformation.targetAction R.toEnrichedFunctor i i
  let z' := ActionFromTransformation.targetAction R.toEnrichedFunctor i' i
  let u := AssociatorUnit.identityInsert (V := V) i Q
  have hl : γ ≫ f ≫ l ≫ m = (𝟙 H ⊗ₘ p) ≫ z := leftFlat_action d S R a i ((n, j), b)
  have hr : δ ≫ f' ≫ r ≫ m = (𝟙 H' ⊗ₘ q) ≫ z' := rightFlat_action d S L R a i ((n, j), b)
  have ht : γ ≫ f ≫ α = (w ⊗ₘ v) ≫ δ ≫ f' :=
    AssociatorConstruction.tripleGenerator_hom d R.toEnrichedFunctor S S i ((n, j), b)
  have hc : l ≫ m = α ≫ r ≫ m := by
    have hL : component (a ▷ (⟨S⟩ : EnrichedFunctorCat V I)) i = l :=
      Input.natTrans_component d.tensorEnrichedFunctor a (GradedNatTrans.unitId S) i
    have hR : component (R ◁ LaxMonoid.multiply d S L) i = r :=
      Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId R.toEnrichedFunctor)
          (LaxMonoid.multiply d S L) i
    have hA : component (α_ R (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩).hom i = α :=
      AssociatorConstruction.functorIso_hom_component d R.toEnrichedFunctor S S i
    exact ((congrArg (fun t => t ≫ m) hL).symm.trans (component_comp _ _ i).symm).trans
      ((congrArg (fun t => component t i) h).trans
        ((component_comp _ _ i).trans (congrArg₂ (fun s t => s ≫ t) hA
          ((component_comp _ _ i).trans (congrArg (fun t => t ≫ m) hR)))))
  have hEq : (𝟙 H ⊗ₘ p) ≫ z = (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) ≫ z' := by
    have h1 : γ ≫ f ≫ l ≫ m = γ ≫ f ≫ α ≫ r ≫ m :=
      congrArg (fun t => γ ≫ f ≫ t) hc
    have h2 : γ ≫ f ≫ α ≫ r ≫ m = (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) ≫ z' := by
      calc
        _ = (w ⊗ₘ v) ≫ δ ≫ f' ≫ r ≫ m := by
          simpa only [Category.assoc] using congrArg (fun t => t ≫ r ≫ m) ht
        _ = _ := congrArg (fun t => (w ⊗ₘ v) ≫ t) hr
    exact hl.symm.trans (h1.trans h2)
  have hTensor : (w ⊗ₘ v) ≫ (𝟙 H' ⊗ₘ q) = w ⊗ₘ (v ≫ q) :=
    (tensorHom_comp_tensorHom w v (𝟙 H') q).trans
      (congrArg (fun t => t ⊗ₘ (v ≫ q)) (Category.comp_id w))
  have hEq' : (𝟙 H ⊗ₘ p) ≫ z = (w ⊗ₘ (v ≫ q)) ≫ z' :=
    hEq.trans ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ z') hTensor))
  have hp : p = (v ≫ q) ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv :=
    (identityInsert_target R.toEnrichedFunctor i Q p).symm.trans
      (((Category.assoc u (𝟙 H ⊗ₘ p) z).trans (congrArg (fun t => u ≫ t) hEq')).trans
        ((Category.assoc u (w ⊗ₘ (v ≫ q)) z').symm.trans
          (identityInsert_source R.toEnrichedFunctor (α_ n j b).inv Q (v ≫ q) w
            (eId_comp_eHomWhiskerRight V I (α_ n j b).inv))))
  let eV := α_ (R.toEnrichedFunctor.obj n) (S.obj j) (S.obj b)
  exact (congrArg (fun t => eV.inv ≫ t) hp).trans
    ((congrArg (fun t => eV.inv ≫ t) (Category.assoc v q
      (R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv))).trans
        ((eV.inv_hom_id_assoc (q ≫ R.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n j b).inv)).trans
          (Category.assoc _ _ _)))

/-- The external associativity law is derived from the original stock mul-action axiom. -/
theorem stock_sigma_assoc :
    letI := ColimitMonoidal.monoidalCategory d
    letI := LaxMonoid.monObj d S L
    ∀ M : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I),
      AssocLaw d S L M.X M.action := by
  let : MonoidalCategory (EnrichedFunctorCat V I) := ColimitMonoidal.monoidalCategory d
  let : MonObj (⟨S⟩ : EnrichedFunctorCat V I) := LaxMonoid.monObj d S L
  intro M
  apply day_assoc_to_source d S L M.X M.action
  let α := α_ M.X (⟨S⟩ : EnrichedFunctorCat V I) ⟨S⟩
  have h := CommutativeModuleConversion.RightModule.mul_action M
  exact (α.hom_inv_id_assoc ((M.action ▷ (⟨S⟩ : EnrichedFunctorCat V I)) ≫ M.action)).symm.trans
    (congrArg (fun t => α.hom ≫ t) h.symm)

end CategoryTheory.EnrichedDayKernel.ExternalRightModule
