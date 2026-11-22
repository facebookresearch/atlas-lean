/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftUnit

/-!
# Natural transformations from symmetric operator labels

Constructs an enriched natural transformation from component maps satisfying the
operator-generator relations. Proves naturality over the complete Hom copowers, retaining
coefficient labels and postcomposition maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricLabelTransformation

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

private theorem remove_braid {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] (A X Y T U : C) (q : X ⟶ Y) (t : T ⟶ U)
    (f : X ⊗ A ⟶ T) (g : Y ⊗ A ⟶ U)
    (h : (β_ A X).hom ≫ f ≫ t = (A ◁ q) ≫ (β_ A Y).hom ≫ g) :
    f ≫ t = (q ▷ A) ≫ g := by
  apply (cancel_epi (β_ A X).hom).1
  have hb := congrArg (fun z => z ≫ g) (braiding_naturality_right A q)
  exact h.trans (by simpa only [Category.assoc] using hb)

/-- The whole labelled coefficient square also gives its genuine closed transpose. -/
theorem curried_label_naturality (F G : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (q : ∀ n : Operad.SmallFinBijGroupoid,
      F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ⟶
      G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (a n k : Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k)
    (h : reconstructedArrowAction F a n k f ≫ q k =
      (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁ q n) ≫
        reconstructedArrowAction G a n k f) :
    reconstructedCurriedAction F a n k f ≫
        (ihom (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))).map (q k) =
      reconstructedCurriedAction G a n k f ≫
        (MonoidalClosed.pre (q n)).app
          (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k)) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_pre_app]
  exact remove_braid (S.{u, v}.functor.obj a)
    (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
    (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
    (q n) (q k) (MonoidalClosed.uncurry (reconstructedCurriedAction F a n k f))
    (MonoidalClosed.uncurry (reconstructedCurriedAction G a n k f)) h

/-- All original copower labels determine naturality on the entire native Hom object. -/
theorem full_curried_naturality (F G : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (q : ∀ n : Operad.SmallFinBijGroupoid,
      F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ⟶
      G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
    (h : ∀ a n k : Operad.SmallFinBijGroupoid, ∀ f : a ⊗ n ⟶ k,
      reconstructedArrowAction F a n k f ≫ q k =
        (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁ q n) ≫
          reconstructedArrowAction G a n k f)
    (n k : Operad.SmallFinBijGroupoid) :
    F.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
        (PointedCGWH.symmetricOperatorObj.{u, v} k) ≫
        (ihom (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))).map (q k) =
      G.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
        (PointedCGWH.symmetricOperatorObj.{u, v} k) ≫
        (MonoidalClosed.pre (q n)).app
          (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k)) := by
  let R := PointedCGWH.copowerRestriction.{u, v, 0} I
  let W := Enriched.SphereOperator.weight (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
    (R.obj n) (R.obj k)
  apply Enriched.weightedCoend.hom_ext W PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
  intro a
  let a₀ : I := a
  apply PointedCGWH.discreteSmash_hom_ext.{u, v, 0}
    (a₀ ⊗ n ⟶ k) (S.{u, v}.functor.obj a₀)
  intro f
  let K : V.{u, v} := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[V.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} k
  let Z : V.{u, v} :=
    (ihom (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))).obj
      (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
  let j := PointedCGWH.discreteSmashIncl.{u, v, 0}
    (a₀ ⊗ n ⟶ k) (S.{u, v}.functor.obj a₀) f
  let i := Enriched.weightedCoend.ι W PointedCGWH.sphereCopowerEnrichedFunctor.{u, v} a
  let fm := F.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (PointedCGWH.symmetricOperatorObj.{u, v} k)
  let gm := G.toEnrichedFunctor.map (PointedCGWH.symmetricOperatorObj.{u, v} n)
    (PointedCGWH.symmetricOperatorObj.{u, v} k)
  let t := (ihom (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))).map (q k)
  let p := (MonoidalClosed.pre (q n)).app
    (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} k))
  let u : K ⟶ Z := fm ≫ t
  let v : K ⟶ Z := gm ≫ p
  have hp := curried_label_naturality F G q a₀ n k f (h a₀ n k f)
  change ((j ≫ i) ≫ fm) ≫ t = ((j ≫ i) ≫ gm) ≫ p at hp
  have hp' : (j ≫ i) ≫ u = (j ≫ i) ≫ v :=
    (Category.assoc (j ≫ i) fm t).symm.trans (hp.trans (Category.assoc (j ≫ i) gm p))
  change j ≫ i ≫ u = j ≫ i ≫ v
  exact (Category.assoc j i u).symm.trans (hp'.trans (Category.assoc j i v))

private theorem index_surjective (x : J.{u, v}) :
    ∃ n : I, PointedCGWH.symmetricOperatorObj.{u, v} n = x := by
  rcases x with ⟨n⟩
  exact ⟨(show I from n), rfl⟩

/-- Complete label squares construct a genuine enriched transformation with those components. -/
def transformation (F G : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (q : ∀ x : PointedCGWH.SymmetricOperatorIndex.{u, v},
      F.toEnrichedFunctor.obj x ⟶ G.toEnrichedFunctor.obj x)
    (h : ∀ a n k : Operad.SmallFinBijGroupoid, ∀ f : a ⊗ n ⟶ k,
      reconstructedArrowAction F a n k f ≫ q (PointedCGWH.symmetricOperatorObj.{u, v} k) =
        (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁
          q (PointedCGWH.symmetricOperatorObj.{u, v} n)) ≫
          reconstructedArrowAction G a n k f) : F ⟶ G :=
  GradedNatTrans.unitOfComponents q (by
    intro x y
    obtain ⟨n, rfl⟩ := index_surjective x
    obtain ⟨k, rfl⟩ := index_surjective y
    rw [tensorHom_id]
    have hc := congrArg MonoidalClosed.uncurry
      (full_curried_naturality F G (fun n => q (PointedCGWH.symmetricOperatorObj.{u, v} n)) h n k)
    simpa only [MonoidalClosed.uncurry_natural_right,
      MonoidalClosed.uncurry_pre_app] using hc)

/-- The full enriched transformation retains exactly the original supplied components. -/
theorem transformation_component (F G : EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v})
    (q : ∀ x : PointedCGWH.SymmetricOperatorIndex.{u, v},
      F.toEnrichedFunctor.obj x ⟶ G.toEnrichedFunctor.obj x)
    (h : ∀ a n k : Operad.SmallFinBijGroupoid, ∀ f : a ⊗ n ⟶ k,
      reconstructedArrowAction F a n k f ≫ q (PointedCGWH.symmetricOperatorObj.{u, v} k) =
        (PointedCGWH.sphereSequence.{u, v}.functor.obj a ◁
          q (PointedCGWH.symmetricOperatorObj.{u, v} n)) ≫
          reconstructedArrowAction G a n k f)
    (x : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    component (transformation F G q h) x = q x := by
  unfold transformation component
  exact GradedNatTrans.unitOfComponents_component _ _ _

end NativeOmegaRecovery.NativeSymmetricLabelTransformation
