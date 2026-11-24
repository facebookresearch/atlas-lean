/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.EnrichedCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# The actual two-object simplicial enrichment

For every simplicial set `X`, the enriched category `WalkingHom X` has two
objects, the original Hom object `X` in the forward direction, empty reverse
Hom, and only identity endomorphisms. This is the generic arrow `2[X]` of
Riehl–Verity, *Homotopy coherent adjunctions and the formal theory of monads*,
arXiv:1310.8279v4, Notation 2.1.3.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  HomotopicalAlgebra
open scoped Simplicial
open scoped SSet.modelCategoryQuillen

namespace SSet

/-- The two original objects of the enrichment with forward Hom `X`. -/
inductive WalkingHom (X : SSet.{u}) : Type
  | source
  | target
  deriving DecidableEq

namespace WalkingHom

variable (X : SSet.{u})

/-- The actual empty simplicial set, with no reverse arrows. -/
abbrev emptyHom : SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

/-- The entire four-entry Hom diagram of the two-object category. -/
def homObject : WalkingHom X → WalkingHom X → SSet.{u}
  | .source, .source => 𝟙_ SSet.{u}
  | .source, .target => X
  | .target, .source => emptyHom
  | .target, .target => 𝟙_ SSet.{u}

/-- Identity arrows are the identities of the original monoidal unit. -/
def identity (a : WalkingHom X) : 𝟙_ SSet.{u} ⟶ homObject X a a :=
  match a with
  | .source => 𝟙 _
  | .target => 𝟙 _

/-- Composition uses the original unitors; the two cycles have empty domain. -/
def composition (a b c : WalkingHom X) :
    homObject X a b ⊗ homObject X b c ⟶ homObject X a c :=
  match a, b, c with
  | .source, .source, .source => (λ_ _).hom
  | .source, .source, .target => (λ_ _).hom
  | .source, .target, .source => toUnit _
  | .source, .target, .target => (ρ_ _).hom
  | .target, .source, .source => (ρ_ _).hom
  | .target, .source, .target => toUnit _
  | .target, .target, .source => (λ_ _).hom
  | .target, .target, .target => (λ_ _).hom

/-- The two-object enrichment, with every identity and composition law proved. -/
instance enrichedCategory : EnrichedCategory SSet.{u} (WalkingHom X) where
  Hom := homObject X
  id := identity X
  comp := composition X
  id_comp a b := by
    cases a <;> cases b <;> dsimp only [homObject, identity, composition] <;> simp
  comp_id a b := by
    cases a <;> cases b <;> dsimp only [homObject, identity, composition]
    all_goals first
      | exact Subsingleton.elim _ _
      | simp
  assoc a b c d := by
    cases a <;> cases b <;> cases c <;> cases d
    all_goals dsimp only [homObject, composition]
    all_goals first
      | exact Subsingleton.elim _ _
      | ext Δ x
        try dsimp only [emptyHom, Functor.const_obj_obj] at x
        first
          | rfl
          | exact PEmpty.elim x.1
          | exact PEmpty.elim x.2.1

/-- The bundled category retains the same original two objects and enrichment. -/
def bundled : EnrichedCat SSet.{u} := EnrichedCat.of SSet.{u} (WalkingHom X)

@[simp] theorem hom_source_target :
    ((source : WalkingHom X) ⟶[SSet.{u}] target) = X := rfl

@[simp] theorem hom_target_source :
    ((target : WalkingHom X) ⟶[SSet.{u}] source) = emptyHom := rfl

@[simp] theorem hom_source_source :
    ((source : WalkingHom X) ⟶[SSet.{u}] source) = 𝟙_ SSet.{u} := rfl

@[simp] theorem hom_target_target :
    ((target : WalkingHom X) ⟶[SSet.{u}] target) = 𝟙_ SSet.{u} := rfl

variable {X} {C : Type v} [EnrichedCategory SSet.{u} C]

private lemma identity_comp (a b : C) :
    eId SSet.{u} a ▷ _ ≫ eComp SSet.{u} a a b = (λ_ (a ⟶[SSet.{u}] b)).hom := by
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    using congrArg (fun f => (λ_ (a ⟶[SSet.{u}] b)).hom ≫ f)
    (e_id_comp SSet.{u} a b)

private lemma comp_identity (a b : C) :
    _ ◁ eId SSet.{u} b ≫ eComp SSet.{u} a b b = (ρ_ (a ⟶[SSet.{u}] b)).hom := by
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    using congrArg (fun f => (ρ_ (a ⟶[SSet.{u}] b)).hom ≫ f)
    (e_comp_id SSet.{u} a b)

private lemma map_left (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    (λ_ X).hom ≫ f = (eId SSet.{u} a ⊗ₘ f) ≫ eComp SSet.{u} a a b := by
  rw [tensorHom_def', Category.assoc, identity_comp, leftUnitor_naturality]

private lemma map_right (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    (ρ_ X).hom ≫ f = (f ⊗ₘ eId SSet.{u} b) ≫ eComp SSet.{u} a b b := by
  rw [tensorHom_def, Category.assoc, comp_identity, rightUnitor_naturality]

/-- The original ordered object assignment, allowing the two images to coincide. -/
def objectMap (a b : C) : WalkingHom X → C
  | .source => a
  | .target => b

/-- The strict enriched functor determined by two objects and its original forward Hom map. -/
def ofMap (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    EnrichedFunctor SSet.{u} (WalkingHom X) C where
  obj := objectMap a b
  map i j := match i, j with
    | .source, .source => eId SSet.{u} a
    | .source, .target => f
    | .target, .source =>
      { app _ := ↾fun x => PEmpty.elim x
        naturality _ _ _ := by
          ext x
          exact PEmpty.elim x }
    | .target, .target => eId SSet.{u} b
  map_id i := by
    cases i <;> exact Category.id_comp _
  map_comp i j k := by
    cases i <;> cases j <;> cases k
    all_goals dsimp only [eComp, enrichedCategory, composition, objectMap]
    all_goals first
      | exact map_left _ _ _
      | exact map_right _ _ _
      | ext Δ x
        first
          | exact PEmpty.elim x.1
          | exact PEmpty.elim x.2

@[simp] theorem ofMap_obj_source (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    (ofMap a b f).obj source = a := rfl

@[simp] theorem ofMap_obj_target (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    (ofMap a b f).obj target = b := rfl

@[simp] theorem ofMap_map_source_target (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) :
    (ofMap a b f).map source target = f := rfl

/-- Reading the original objects and forward Hom map reconstructs the entire strict functor. -/
theorem ofMap_readback (F : EnrichedFunctor SSet.{u} (WalkingHom X) C) :
    ofMap (F.obj source) (F.obj target) (F.map source target) = F := by
  apply EnrichedFunctor.ext SSet.{u} (fun i => by cases i <;> rfl)
  intro i j
  cases i <;> cases j
  · change eId SSet.{u} (F.obj source) ≫ 𝟙 _ = F.map source source
    have h : 𝟙 _ ≫ F.map source source = eId SSet.{u} (F.obj source) := F.map_id source
    exact (Category.comp_id _).trans (h.symm.trans (Category.id_comp _))
  · rfl
  · ext Δ x
    exact PEmpty.elim x
  · change eId SSet.{u} (F.obj target) ≫ 𝟙 _ = F.map target target
    have h : 𝟙 _ ≫ F.map target target = eId SSet.{u} (F.obj target) := F.map_id target
    exact (Category.comp_id _).trans (h.symm.trans (Category.id_comp _))

/-- Strict enriched functors out of `2[X]` are exactly two objects and an original Hom map. -/
def functorEquiv :
    EnrichedFunctor SSet.{u} (WalkingHom X) C ≃ (Σ a : C, Σ b : C, X ⟶ a ⟶[SSet.{u}] b) where
  toFun F := ⟨F.obj source, F.obj target, F.map source target⟩
  invFun p := ofMap p.1 p.2.1 p.2.2
  left_inv := ofMap_readback
  right_inv p := by
    rcases p with ⟨a, b, f⟩
    rfl

/-- Strict functors whose two original object images are prescribed. -/
abbrev FixedObjects (a b : C) :=
  { F : EnrichedFunctor SSet.{u} (WalkingHom X) C // F.obj source = a ∧ F.obj target = b }

/-- The fixed-object representation transports only the two stated object equalities. -/
def fixedObjectEquiv (a b : C) : FixedObjects (X := X) a b ≃ (X ⟶ a ⟶[SSet.{u}] b) where
  toFun F := F.val.map source target ≫ eqToHom (by rw [F.property.1, F.property.2])
  invFun f := ⟨ofMap a b f, rfl, rfl⟩
  left_inv F := by
    rcases F with ⟨F, ha, hb⟩
    cases ha
    cases hb
    exact Subtype.ext (ofMap_readback F)
  right_inv f := by
    change f ≫ 𝟙 _ = f
    exact Category.comp_id f

/-- With both objects fixed, equality of the strict functors detects the original Hom map. -/
theorem ofMap_injective (a b : C) : Function.Injective (ofMap (X := X) a b) := by
  intro f g h
  have hfixed : (⟨ofMap a b f, rfl, rfl⟩ : FixedObjects (X := X) a b) =
      ⟨ofMap a b g, rfl, rfl⟩ := Subtype.ext h
  have hm := congrArg (fixedObjectEquiv a b) hfixed
  change f ≫ 𝟙 _ = g ≫ 𝟙 _ at hm
  exact (Category.comp_id f).symm.trans (hm.trans (Category.comp_id g))

/-- Composing the represented functor uses the literal original Hom map of the target functor. -/
theorem ofMap_comp {D : Type w} [EnrichedCategory SSet.{u} D]
    (a b : C) (f : X ⟶ a ⟶[SSet.{u}] b) (P : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor.comp SSet.{u} (ofMap a b f) P =
      ofMap (P.obj a) (P.obj b) (f ≫ P.map a b) :=
  (ofMap_readback (EnrichedFunctor.comp SSet.{u} (ofMap a b f) P)).symm

/-- The actual enriched map `2[i]` is the identity on the two object positions. -/
def map {A B : SSet.{u}} (i : A ⟶ B) : EnrichedFunctor SSet.{u} (WalkingHom A) (WalkingHom B) :=
  ofMap source target i

@[simp] theorem map_obj_source {A B : SSet.{u}} (i : A ⟶ B) :
    (map i).obj source = source := rfl

@[simp] theorem map_obj_target {A B : SSet.{u}} (i : A ⟶ B) :
    (map i).obj target = target := rfl

@[simp] theorem map_forward {A B : SSet.{u}} (i : A ⟶ B) :
    (map i).map source target = i := rfl

@[simp] theorem map_id (A : SSet.{u}) :
    map (𝟙 A) = EnrichedFunctor.id SSet.{u} (WalkingHom A) :=
  ofMap_readback (EnrichedFunctor.id SSet.{u} (WalkingHom A))

/-- The two-object maps compose on their literal original forward Hom maps. -/
theorem map_comp {A B E : SSet.{u}} (i : A ⟶ B) (j : B ⟶ E) :
    EnrichedFunctor.comp SSet.{u} (map i) (map j) = map (i ≫ j) :=
  ofMap_comp source target i (map j)

section Lifting

variable {D : Type w} [EnrichedCategory SSet.{u} D]
  (P : EnrichedFunctor SSet.{u} C D) (a b : C)

/-- An actual Hom filler extends the entire strict functor, fixing both object images
and both triangles. The hypothesis may come from a lifting property or a given filler. -/
theorem exists_fixedObject_lift {A B : SSet.{u}} (i : A ⟶ B)
    (f : A ⟶ a ⟶[SSet.{u}] b) (g : B ⟶ P.obj a ⟶[SSet.{u}] P.obj b)
    (sq : CommSq f i (P.map a b) g) [sq.HasLift] :
    ∃ L : FixedObjects (X := B) a b,
      EnrichedFunctor.comp SSet.{u} (map i) L.val = ofMap a b f ∧
      EnrichedFunctor.comp SSet.{u} L.val P = ofMap (P.obj a) (P.obj b) g := by
  refine ⟨⟨ofMap a b sq.lift, rfl, rfl⟩, ?_, ?_⟩
  · calc
      EnrichedFunctor.comp SSet.{u} (map i) (ofMap a b sq.lift) =
          ofMap a b (i ≫ sq.lift) := ofMap_comp source target i (ofMap a b sq.lift)
      _ = ofMap a b f := by rw [sq.fac_left]
  · calc
      EnrichedFunctor.comp SSet.{u} (ofMap a b sq.lift) P =
          ofMap (P.obj a) (P.obj b) (sq.lift ≫ P.map a b) := ofMap_comp a b sq.lift P
      _ = ofMap (P.obj a) (P.obj b) g := by rw [sq.fac_right]

/-- A local Kan fibration fills actual horns of fixed-object strict enriched functors. -/
theorem exists_horn_lift [Fibration (P.map a b)] (n : ℕ) (k : Fin (n + 2))
    (f : (Λ[n + 1, k] : SSet.{u}) ⟶ (a ⟶[SSet.{u}] b))
    (g : Δ[n + 1] ⟶ P.obj a ⟶[SSet.{u}] P.obj b)
    (sq : CommSq f Λ[n + 1, k].ι (P.map a b) g) :
    ∃ L : FixedObjects (X := Δ[n + 1]) a b,
      EnrichedFunctor.comp SSet.{u} (map Λ[n + 1, k].ι) L.val = ofMap a b f ∧
      EnrichedFunctor.comp SSet.{u} L.val P = ofMap (P.obj a) (P.obj b) g :=
  exists_fixedObject_lift P a b _ f g sq

/-- Right lifting against the original boundary family gives every prescribed boundary
extension. This uses the native trivial Kan fibration class `I.rlp`, not just Kan fibrancy. -/
theorem exists_boundary_lift (hp : modelCategoryQuillen.I.rlp (P.map a b)) (n : ℕ)
    (f : (∂Δ[n] : SSet.{u}) ⟶ (a ⟶[SSet.{u}] b))
    (g : Δ[n] ⟶ P.obj a ⟶[SSet.{u}] P.obj b)
    (sq : CommSq f ∂Δ[n].ι (P.map a b) g) :
    ∃ L : FixedObjects (X := Δ[n]) a b,
      EnrichedFunctor.comp SSet.{u} (map ∂Δ[n].ι) L.val = ofMap a b f ∧
      EnrichedFunctor.comp SSet.{u} L.val P = ofMap (P.obj a) (P.obj b) g := by
  have : HasLiftingProperty ∂Δ[n].ι (P.map a b) :=
    hp _ (modelCategoryQuillen.boundary_ι_mem_I n)
  exact exists_fixedObject_lift P a b _ f g sq

/-- The actual fixed-object Hom restriction square: its point records the boundary map
and the target simplex, and its comparison uses the original local Hom map of `P`. -/
noncomputable def restrictionSquare {A B : SSet.{u}} (i : A ⟶ B) :
    MonoidalClosed.internalHom.PullbackObjObj i (P.map a b) :=
  Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i (P.map a b)

/-- A local Kan fibration makes the fixed-object boundary comparison a Kan fibration.
It does not assert that every prescribed boundary has a simplex filler. -/
theorem boundaryRestriction_fibration [Fibration (P.map a b)] (n : ℕ) :
    Fibration (restrictionSquare P a b ∂Δ[n].ι).π :=
  SSet.fibration_pullbackObjObjπ _

end Lifting

end WalkingHom
end SSet
