/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WeightedEndVariance

/-!
# Whole proof families for the fixed weighted-end construction

Every ambient category, monoidal, braided, closed and enriched datum
remains fixed. First identify the entire object-product and relation-product
proof families. The equalizer predicates then have the same dependent
types. The same chosen weighted-end algorithm retains its complete object,
projection, weight-map, diagram-map and Hom-function families.

This concerns Prop-valued existence proofs. Arbitrary separately chosen
product cones, equalizer cones or categorical dictionaries are not compared.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.WeightedEndProofFamilies

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

/-- The entire object-product existence family of the original end. -/
abbrev ObjectFamily : Prop :=
  ∀ W F : EnrichedFunctor V I V, HasProduct (weightedEnd.objects W F)

/-- The entire relation-product existence family of the original end. -/
abbrev RelationFamily : Prop :=
  ∀ W F : EnrichedFunctor V I V, HasProduct (weightedEnd.relations W F)

/-- The equalizer family retains both actual product proof families
in the types of the original two parallel naturality maps. -/
abbrev EqualizerFamily (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) : Prop :=
  ∀ W F : EnrichedFunctor V I V, HasEqualizer
    (@weightedEnd.leftMap V _ _ _ _ I _ W F (po W F) (pr W F))
    (@weightedEnd.rightMap V _ _ _ _ I _ W F (po W F) (pr W F))

omit [BraidedCategory V] in
/-- The entire original object-product proof family is unique. -/
theorem objectFamily_eq (po po' : ObjectFamily (V := V) (I := I)) : po = po' :=
  Subsingleton.elim _ _

omit [BraidedCategory V] in
/-- The entire original relation-product proof family is unique. -/
theorem relationFamily_eq (pr pr' : RelationFamily (V := V) (I := I)) : pr = pr' :=
  Subsingleton.elim _ _

/-- Only after both whole product proof families are fixed do the
dependent equalizer predicates have the same original type. -/
theorem equalizerFamily_eq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I)) :
    EqualizerFamily po pr = EqualizerFamily po' pr' := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  rfl

/-- Equalizer witness families are transported after their product
families, retaining the whole dependent proof family. -/
theorem equalizerFamily_heq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') : HEq pe pe' := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  exact heq_of_eq (Subsingleton.elim pe pe')

/-- The complete original end-object function has every proof argument explicit. -/
def objectFunction
    (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) (pe : EqualizerFamily po pr) :
    EnrichedFunctor V I V → EnrichedFunctor V I V → V :=
  fun W F => @weightedEnd V _ _ _ _ I _ W F (po W F) (pr W F) (pe W F)

/-- The complete original projection function uses the same products
and the same equalizer witness at every source, target and index. -/
def projectionFunction
    (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) (pe : EqualizerFamily po pr) :
    ∀ W F : EnrichedFunctor V I V, ∀ a : I,
      objectFunction po pr pe W F ⟶ (ihom (W.obj a)).obj (F.obj a) :=
  fun W F a => @weightedEnd.π V _ _ _ _ I _ W F (po W F) (pr W F) (pe W F) a

/-- The whole diagram-map function retains both original endpoints,
all actual transformations and both endpoint witness families. -/
def diagramMapFunction
    (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) (pe : EqualizerFamily po pr) :
    ∀ W F F' : EnrichedFunctor V I V,
      GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F' →
        (objectFunction po pr pe W F ⟶ objectFunction po pr pe W F') :=
  fun W F F' f => @weightedEnd.mapDiagram V _ _ _ _ I _
    W F (po W F) (pr W F) (pe W F) F' f (po W F') (pr W F') (pe W F')

/-- The whole weight-map function retains both original endpoints,
all actual transformations and both endpoint witness families. -/
def weightMapFunction
    (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) (pe : EqualizerFamily po pr) :
    ∀ W W' F : EnrichedFunctor V I V,
      GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W →
        (objectFunction po pr pe W F ⟶ objectFunction po pr pe W' F) :=
  fun W W' F f => @weightedEnd.mapWeight V _ _ _ _ I _
    W F (po W F) (pr W F) (pe W F) W' f (po W' F) (pr W' F) (pe W' F)

/-- The same selected algorithm has the same entire object function,
after the full product and dependent equalizer proof families agree. -/
theorem object_function_eq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    objectFunction po pr pe = objectFunction po' pr' pe' := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

/-- Every original end projection is retained as one complete dependent function. -/
theorem projection_function_heq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    HEq (projectionFunction po pr pe) (projectionFunction po' pr' pe') := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

/-- Every original diagram arrow is retained as one complete dependent function. -/
theorem diagram_map_function_heq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    HEq (diagramMapFunction po pr pe) (diagramMapFunction po' pr' pe') := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

/-- Every original weight arrow is retained as one complete dependent function. -/
theorem weight_map_function_heq
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    HEq (weightMapFunction po pr pe) (weightMapFunction po' pr' pe') := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

/-- Any fixed original forward Hom algorithm keeps its entire function
family when only the Prop-valued end witness families vary. -/
theorem forward_hom_algorithm_heq
    {H : EnrichedFunctor V I V → EnrichedFunctor V I V → V → Type*}
    (algorithm : ∀ po : ObjectFamily (V := V) (I := I),
      ∀ pr : RelationFamily (V := V) (I := I), ∀ pe : EqualizerFamily po pr,
      ∀ W F T, (T ⟶ objectFunction po pr pe W F) → H W F T)
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    HEq (algorithm po pr pe) (algorithm po' pr' pe') := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

/-- Any fixed original inverse Hom algorithm keeps its entire function
family under the same whole product/equalizer proof transport. -/
theorem inverse_hom_algorithm_heq
    {H : EnrichedFunctor V I V → EnrichedFunctor V I V → V → Type*}
    (algorithm : ∀ po : ObjectFamily (V := V) (I := I),
      ∀ pr : RelationFamily (V := V) (I := I), ∀ pe : EqualizerFamily po pr,
      ∀ W F T, H W F T → (T ⟶ objectFunction po pr pe W F))
    (po po' : ObjectFamily (V := V) (I := I))
    (pr pr' : RelationFamily (V := V) (I := I))
    (pe : EqualizerFamily po pr) (pe' : EqualizerFamily po' pr') :
    HEq (algorithm po pr pe) (algorithm po' pr' pe') := by
  cases objectFamily_eq po po'
  cases relationFamily_eq pr pr'
  cases Subsingleton.elim pe pe'
  rfl

section GlobalWitnesses

omit [BraidedCategory V] in
/-- A given global product witness supplies the actual whole object family. -/
theorem objectFamilyOfProducts (hp : HasProducts.{uI} V) : ObjectFamily (V := V) (I := I) := by
  let _ := hp
  exact fun _ _ => inferInstance

omit [BraidedCategory V] in
/-- The same given global witness supplies the actual whole relation family. -/
theorem relationFamilyOfProducts (hp : HasProducts.{uI} V) : RelationFamily (V := V) (I := I) := by
  let _ := hp
  exact fun _ _ => inferInstance

/-- A given global equalizer witness supplies the dependent original
equalizer family after the two complete product families are fixed. -/
theorem equalizerFamilyOfEqualizers (po : ObjectFamily (V := V) (I := I))
    (pr : RelationFamily (V := V) (I := I)) (he : HasEqualizers V) : EqualizerFamily po pr := by
  let _ := he
  intro W F
  let _ := po W F
  let _ := pr W F
  exact inferInstance

/-- The whole original weighted-end bifunctor is independent only
of global existence proofs with every categorical datum fixed. -/
theorem bifunctor_proof_eq (hp hp' : HasProducts.{uI} V) (he he' : HasEqualizers V) :
    @EnrichedFunctorCat.WeightedEndVariance.bifunctor V _ _ _ _ I _ hp he =
      @EnrichedFunctorCat.WeightedEndVariance.bifunctor V _ _ _ _ I _ hp' he' := by
  cases Subsingleton.elim hp hp'
  cases Subsingleton.elim he he'
  rfl

/-- The complete original source functor family agrees under those
global witness proofs, before any actual target object is selected. -/
theorem source_functor_function_eq (hp hp' : HasProducts.{uI} V) (he he' : HasEqualizers V) :
    (fun E : EnrichedFunctorCat V I =>
      (@EnrichedFunctorCat.WeightedEndVariance.bifunctor V _ _ _ _ I _ hp he).flip.obj E) =
      fun E : EnrichedFunctorCat V I =>
        (@EnrichedFunctorCat.WeightedEndVariance.bifunctor V _ _ _ _ I _ hp' he').flip.obj E := by
  rw [bifunctor_proof_eq hp hp' he he']

end GlobalWitnesses

end CategoryTheory.Enriched.WeightedEndProofFamilies
