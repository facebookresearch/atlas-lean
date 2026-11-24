/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeAdjunction
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Actual fixed-object free-path algebras are simplicial enrichments

The monad comes from the genuine canonical free/Hom adjunction. Its unit
retains the original generators and its multiplication evaluates whole
nested paths. The two algebra equations derive the actual enriched identity,
binary composition and associativity on the unchanged original Hom family.
No supplied enriched structure or comparison certificate is an input.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

variable {O : Type u}

/-- The actual whole free-path monad, induced by the canonical free/Hom adjunction. -/
def pathMonad (O : Type u) : Monad (Families O) := (adjunction.{u} (O := O)).toMonad

/-- Two actual original generators concatenate in the same canonical free enrichment. -/
def pairWord (Q : SimplicialQuiver.Data O) (x y z : O) :
    Q.Hom x y ⊗ Q.Hom y z ⟶ SimplicialQuiver.freeHom Q x z :=
  (SimplicialQuiver.generator Q x y ⊗ₘ SimplicialQuiver.generator Q y z) ≫
    SimplicialQuiver.freeComp Q x y z

/-- Evaluating the full two-letter word is the original target composition. -/
theorem pairWord_evaluate (C : FixedObjects O) (x y z : O) :
    pairWord (quiver ((underlyingFunctor.{u} (O := O)).obj C)) x y z ≫
      homMap (evaluate C) x z = compositionMap C x y z := by
  unfold pairWord
  erw [Category.assoc, compositionMap_homMap]
  erw [← Category.assoc, tensorHom_comp_tensorHom]
  erw [generator_evaluate, generator_evaluate]
  exact Category.id_comp (compositionMap C x y z)

/-- The same whole two-letter word retains the actual generator maps under every free functor. -/
theorem pairWord_map {Q R : SimplicialQuiver.Data O}
    (f : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y) (x y z : O) :
    pairWord Q x y z ≫ homMap (FreeQuiver.map f) x z =
      (f x y ⊗ₘ f y z) ≫ pairWord R x y z := by
  ext n a
  rfl

variable (A : (pathMonad O).Algebra)

/-- The actual algebra action on the concrete original whole finite-path Hom. -/
def action (x y : O) : SimplicialQuiver.freeHom (quiver A.A) x y ⟶ A.A (x, y) :=
  A.a (x, y)

/-- Algebra unit retains the identical original complete generating Hom. -/
theorem generator_action (x y : O) :
    SimplicialQuiver.generator (quiver A.A) x y ≫ action A x y = 𝟙 (A.A (x, y)) :=
  congrArg (fun f => f (x, y)) A.unit

/-- The actual empty path supplies the original enriched identity. -/
def algebraIdentity (x : O) : 𝟙_ SSet.{u} ⟶ A.A (x, x) :=
  SimplicialQuiver.freeId (quiver A.A) x ≫ action A x x

/-- The actual original two-letter path supplies binary enriched composition. -/
def algebraComposition (x y z : O) : A.A (x, y) ⊗ A.A (y, z) ⟶ A.A (x, z) :=
  pairWord (quiver A.A) x y z ≫ action A x z

/-- The algebra associativity equation evaluates arbitrary whole original path concatenations. -/
theorem action_composition (x y z : O) :
    SimplicialQuiver.freeComp (quiver A.A) x y z ≫ action A x z =
      (action A x y ⊗ₘ action A y z) ≫ algebraComposition A x y z := by
  let Q := quiver A.A
  let C : FixedObjects O := FreeQuiver.object Q
  let R := quiver ((underlyingFunctor.{u} (O := O)).obj C)
  have h : homMap (evaluate C) x z ≫ action A x z =
      homMap (FreeQuiver.map (Q := R) (R := Q) (fun a b => action A a b)) x z ≫ action A x z :=
    congrArg (fun f => f (x, z)) A.assoc
  have h' := congrArg (fun f => pairWord R x y z ≫ f) h
  erw [← Category.assoc, pairWord_evaluate] at h'
  erw [← Category.assoc, pairWord_map, Category.assoc] at h'
  exact h'

/-- Whole path concatenation is preserved in every original scalar degree. -/
theorem action_comp_apply (n : SimplexCategoryᵒᵖ) {x y z : O}
    (p : SimplicialQuiver.Path (quiver A.A) n x y)
    (q : SimplicialQuiver.Path (quiver A.A) n y z) :
    (action A x z).app n (@Quiver.Path.comp O (SimplicialQuiver.quiverAt (quiver A.A) n) x y
      z p q) =
      (algebraComposition A x y z).app n ((action A x y).app n p, (action A y z).app n q) :=
  congrArg (fun f => f.app n (p, q)) (action_composition A x y z)

/-- Every original generating scalar arrow is retained by the algebra action. -/
theorem action_generator_apply (n : SimplexCategoryᵒᵖ) {x y : O} (f : (A.A (x, y)).obj n) :
    (action A x y).app n ((SimplicialQuiver.generator (quiver A.A) x y).app n f) = f :=
  congrArg (fun k => k.app n f) (generator_action A x y)

/-- The two algebra equations construct the genuine simplicial enrichment on the original
objects. -/
@[instance_reducible]
def algebraEnrichment : EnrichedCategory SSet.{u} O where
  Hom x y := A.A (x, y)
  id := algebraIdentity A
  comp := algebraComposition A
  id_comp x y := by
    ext n f
    let p : SimplicialQuiver.Path (quiver A.A) n x y :=
      (SimplicialQuiver.generator (quiver A.A) x y).app n f
    have h := action_comp_apply A n (@Quiver.Path.nil O (SimplicialQuiver.quiverAt (quiver
      A.A) n) x)
      p
    have hn := @Quiver.Path.nil_comp O (SimplicialQuiver.quiverAt (quiver A.A) n) x y p
    have hg : (action A x y).app n p = f := action_generator_apply A n f
    rw [hn, hg] at h
    exact h.symm
  comp_id x y := by
    ext n f
    let p : SimplicialQuiver.Path (quiver A.A) n x y :=
      (SimplicialQuiver.generator (quiver A.A) x y).app n f
    have h := action_comp_apply A n p
      (@Quiver.Path.nil O (SimplicialQuiver.quiverAt (quiver A.A) n) y)
    have hn := @Quiver.Path.comp_nil O (SimplicialQuiver.quiverAt (quiver A.A) n) x y p
    have hg : (action A x y).app n p = f := action_generator_apply A n f
    rw [hn, hg] at h
    exact h.symm
  assoc w x y z := by
    ext n f
    rcases f with ⟨f, g, h⟩
    let : Quiver O := SimplicialQuiver.quiverAt (quiver A.A) n
    let p : SimplicialQuiver.Path (quiver A.A) n w x := (SimplicialQuiver.generator (quiver
      A.A) w x).app n f
    let q : SimplicialQuiver.Path (quiver A.A) n x y := (SimplicialQuiver.generator (quiver
      A.A) x y).app n g
    let r : SimplicialQuiver.Path (quiver A.A) n y z := (SimplicialQuiver.generator (quiver
      A.A) y z).app n h
    have hp : (action A w x).app n p = f := action_generator_apply A n f
    have hq : (action A x y).app n q = g := action_generator_apply A n g
    have hr : (action A y z).app n r = h := action_generator_apply A n h
    have hpq := action_comp_apply A n p q
    rw [hp, hq] at hpq
    have hqr := action_comp_apply A n q r
    rw [hq, hr] at hqr
    have hl := action_comp_apply A n (p.comp q) r
    rw [hpq, hr] at hl
    have hr' := action_comp_apply A n p (q.comp r)
    rw [hp, hqr] at hr'
    change (algebraComposition A w y z).app n
        ((algebraComposition A w x y).app n (f, g), h) =
      (algebraComposition A w x z).app n
        (f, (algebraComposition A x y z).app n (g, h))
    exact hl.symm.trans ((congrArg ((action A w z).app n)
      (@Quiver.Path.comp_assoc O (SimplicialQuiver.quiverAt (quiver A.A) n) w x y z p q
        r)).trans hr')

/-- Bundle the constructed enrichment without changing its original object or whole Hom family. -/
def ofAlgebra : FixedObjects O := by
  letI := algebraEnrichment A
  exact of O

/-- Every actual algebra action is the full enriched path-evaluation map into the
constructed enrichment. -/
def actionMap : FreeQuiver.object (quiver A.A) ⟶ ofAlgebra A :=
  ofHomMaps (fun x y => action A x y)
    (fun _x => rfl) (action_composition A)

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree
