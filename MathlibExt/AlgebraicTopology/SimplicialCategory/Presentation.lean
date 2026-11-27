/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeEvaluation

/-!
# Actual presentations of simplicial categories

The generating relations are closed under equivalence, composition,
and every simplex operator. Only Hom paths are identified: the supplied
individual object type is retained exactly. An interpretation descends
by proving the stated relations on its actual generating maps.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialQuiver

variable {O : Type u} (Q : Data O)

/-- A family of actual relations on whole generating paths in every scalar degree. -/
abbrev Relations := ∀ (n : SimplexCategoryᵒᵖ) (x y : O), Path Q n x y → Path Q n x y → Prop

/-- The smallest equivalence and composition congruence containing the given relations
and stable under all original scalar simplex operators. -/
inductive Closure (R : Relations Q) :
    ∀ {n : SimplexCategoryᵒᵖ} {x y : O}, Path Q n x y → Path Q n x y → Prop
  | relation {n x y} {p q : Path Q n x y} : R n x y p q → Closure R p q
  | refl {n x y} (p : Path Q n x y) : Closure R p p
  | symm {n x y} {p q : Path Q n x y} : Closure R p q → Closure R q p
  | trans {n x y} {p q r : Path Q n x y} : Closure R p q → Closure R q r → Closure R p r
  | comp {n x y z} {p p' : Path Q n x y} {q q' : Path Q n y z} :
      Closure R p p' → Closure R q q' →
      Closure R (@Quiver.Path.comp O (quiverAt Q n) x y z p q)
        (@Quiver.Path.comp O (quiverAt Q n) x y z p' q')
  | operator {n m x y} (f : n ⟶ m) {p q : Path Q n x y} :
      Closure R p q → Closure R (mapPath Q f p) (mapPath Q f q)

variable {Q}

/-- The actual generated Hom congruence in one scalar degree at the same two original vertices. -/
def congruence (R : Relations Q) (n : SimplexCategoryᵒᵖ) (x y : O) : Setoid (Path Q n x y) where
  r := Closure Q R
  iseqv := ⟨Closure.refl, Closure.symm, Closure.trans⟩

/-- The presented Hom simplicial set, retaining its specified original source and target. -/
def presentedHom (R : Relations Q) (x y : O) : SSet.{u} where
  obj n := _root_.Quotient (congruence R n x y)
  map f := ↾_root_.Quotient.map (mapPath Q f) (fun _ _ h => Closure.operator f h)
  map_id n := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | h p =>
        change _root_.Quotient.mk _ (mapPath Q (𝟙 n) p) = _root_.Quotient.mk _ p
        rw [mapPath_id]
  map_comp f g := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | h p =>
        change _root_.Quotient.mk _ (mapPath Q (f ≫ g) p) =
          _root_.Quotient.mk _ (mapPath Q g (mapPath Q f p))
        rw [mapPath_comp]

/-- The actual quotient of free paths is a simplicial map at the original vertices. -/
def quotientHom (R : Relations Q) (x y : O) : freeHom Q x y ⟶ presentedHom R x y where
  app n := ↾_root_.Quotient.mk (congruence R n x y)
  naturality n m f := by ext p; rfl

/-- The empty original path supplies the presented identity. -/
def presentedId (R : Relations Q) (x : O) : 𝟙_ SSet.{u} ⟶ presentedHom R x x where
  app n := ↾fun _ => _root_.Quotient.mk _ (@Quiver.Path.nil O (quiverAt Q n) x)
  naturality n m f := by ext p; rfl

/-- Presented composition is induced by concatenation of the actual original paths. -/
def presentedComp (R : Relations Q) (x y z : O) :
    presentedHom R x y ⊗ presentedHom R y z ⟶ presentedHom R x z where
  app n := ↾fun p => _root_.Quotient.map₂
    (@Quiver.Path.comp O (quiverAt Q n) x y z)
    (fun _ _ h _ _ k => Closure.comp h k) p.1 p.2
  naturality n m f := by
    ext p
    obtain ⟨a, b⟩ := p
    induction a using _root_.Quotient.inductionOn with
    | h a =>
        induction b using _root_.Quotient.inductionOn with
        | h b =>
            change _root_.Quotient.mk _ (@Quiver.Path.comp O (quiverAt Q m) x y z
              (mapPath Q f a) (mapPath Q f b)) =
                _root_.Quotient.mk _ (mapPath Q f (@Quiver.Path.comp O (quiverAt Q n) x y z a b))
            exact congrArg (fun p : Path Q m x z => _root_.Quotient.mk (congruence R m x z) p)
              (@Prefunctor.mapPath_comp O (quiverAt Q n) O (quiverAt Q m)
                (operator Q f) x y a z b).symm

/-- The genuine presented enriched category on the unchanged original vertex type. -/
@[instance_reducible]
def presentedEnrichment (R : Relations Q) : EnrichedCategory SSet.{u} O where
  Hom := presentedHom R
  id := presentedId R
  comp := presentedComp R
  id_comp x y := by
    ext n a
    induction a using _root_.Quotient.inductionOn with
    | h p =>
        exact congrArg (fun p : Path Q n x y => _root_.Quotient.mk (congruence R n x y) p)
          (@Quiver.Path.nil_comp O (quiverAt Q n) x y p)
  comp_id x y := by
    ext n a
    induction a using _root_.Quotient.inductionOn with
    | h p =>
        exact congrArg (fun p : Path Q n x y => _root_.Quotient.mk (congruence R n x y) p)
          (@Quiver.Path.comp_nil O (quiverAt Q n) x y p)
  assoc w x y z := by
    ext n a
    obtain ⟨a, b, c⟩ := a
    induction a using _root_.Quotient.inductionOn with
    | h a =>
        induction b using _root_.Quotient.inductionOn with
        | h b =>
            induction c using _root_.Quotient.inductionOn with
            | h c =>
                change _root_.Quotient.mk _ (@Quiver.Path.comp O (quiverAt Q n) w y z
                  (@Quiver.Path.comp O (quiverAt Q n) w x y a b) c) =
                    _root_.Quotient.mk _ (@Quiver.Path.comp O (quiverAt Q n) w x z a
                      (@Quiver.Path.comp O (quiverAt Q n) x y z b c))
                exact congrArg (fun p : Path Q n w z => _root_.Quotient.mk (congruence R n w z) p)
                  (@Quiver.Path.comp_assoc O (quiverAt Q n) w x y z a b c)

/-- Bundle the genuine presented simplicial category without identifying original objects. -/
def presented (R : Relations Q) : EnrichedCat SSet.{u} := by
  letI := presentedEnrichment R
  exact EnrichedCat.of SSet.{u} O

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Actual evaluation of the given generators kills every generated simplicial congruence
relation. -/
theorem Interpretation.evalPath_congruent (I : Interpretation Q C) (R : Relations Q)
    (hR : ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q)
    {n : SimplexCategoryᵒᵖ} {x y : O} {p q : Path Q n x y} (h : Closure Q R p q) :
    I.evalPath n p = I.evalPath n q := by
  induction h with
  | relation h => exact hR _ _ _ _ _ h
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih jk => exact ih.trans jk
  | comp h k ih jk => rw [I.evalPath_comp, I.evalPath_comp, ih, jk]
  | operator f h ih => rw [I.evalPath_naturality, I.evalPath_naturality, ih]

/-- The genuine presented Hom map obtained from an actual relation-respecting interpretation. -/
def Interpretation.descendHom (I : Interpretation Q C) (R : Relations Q)
    (hR : ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q) (x y : O) :
    presentedHom R x y ⟶ I.obj x ⟶[SSet.{u}] I.obj y where
  app n := ↾_root_.Quotient.lift (I.evalPath n) (fun _ _ h => I.evalPath_congruent R hR h)
  naturality n m f := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | h p => exact I.evalPath_naturality f p

/-- The complete enriched extension to the actual presentation, not a supplied comparison
functor. -/
def Interpretation.descend (I : Interpretation Q C) (R : Relations Q)
    (hR : ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q) :
    letI := presentedEnrichment R
    EnrichedFunctor SSet.{u} O C := by
  letI := presentedEnrichment R
  exact {
    obj := I.obj
    map := I.descendHom R hR
    map_id := fun x => by ext n p; exact I.evalPath_nil n x
    map_comp := fun x y z => by
      ext n a
      obtain ⟨a, b⟩ := a
      induction a using _root_.Quotient.inductionOn with
      | h a =>
          induction b using _root_.Quotient.inductionOn with
          | h b => exact I.evalPath_comp n a b }

/-- The descended map evaluates the same whole original path represented by its quotient class. -/
theorem Interpretation.quotient_descend (I : Interpretation Q C) (R : Relations Q)
    (hR : ∀ n x y p q, R n x y p q → I.evalPath n p = I.evalPath n q) (x y : O) :
    quotientHom R x y ≫ I.descendHom R hR x y = I.evalHom x y := by ext n p; rfl

end CategoryTheory.SimplicialQuiver
