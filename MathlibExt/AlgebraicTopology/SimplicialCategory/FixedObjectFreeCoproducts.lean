/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeQuiver
import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedSums

/-!
# Actual indexed coproducts of fixed-object free simplicial categories

The generating quiver is the literal indexed scalar sum at every
original endpoint pair. The existing free universal property proves
the entire fixed-object coproduct and its map laws. Original labels,+loops and identity words remain
  unchanged, including empty families.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiver

variable {O I : Type u}

/-- Sum the supplied original generating quivers at every same original label pair. -/
abbrev sumQuiver (Q : I → SimplicialQuiver.Data O) : SimplicialQuiver.Data O where
  Hom x y := SSet.IndexedSums.object (fun i => (Q i).Hom x y)

/-- The actual original free category on the entire indexed generating quiver. -/
abbrev sumObject (Q : I → SimplicialQuiver.Data O) : FixedObjects O := object (sumQuiver Q)

/-- Include every original generating family by its same indexed simplex map. -/
def sumInclusion (Q : I → SimplicialQuiver.Data O) (i : I) : object (Q i) ⟶ sumObject Q :=
  map (fun x y => SSet.IndexedSums.inclusion (fun i => (Q i).Hom x y) i)

/-- Read back the literal scalar indexed inclusion on each original free generator. -/
theorem generator_sumInclusion (Q : I → SimplicialQuiver.Data O) (i : I) (x y : O) :
    generator (Q i) x y ≫ homMap (sumInclusion Q i) x y =
      SSet.IndexedSums.inclusion (fun i => (Q i).Hom x y) i ≫ generator (sumQuiver Q) x y :=
  generator_map _ x y

/-- Extend the supplied original free cocone maps on every literal indexed generating simplex. -/
def sumDesc (Q : I → SimplicialQuiver.Data O) {D : FixedObjects O}
    (f : ∀ i, object (Q i) ⟶ D) : sumObject Q ⟶ D :=
  extend (sumQuiver Q) D (fun x y => SSet.IndexedSums.desc (fun i => (Q i).Hom x y)
    (fun i => generator (Q i) x y ≫ homMap (f i) x y))

/-- The actual full free sum desc reads back each whole original cocone leg. -/
theorem sumInclusion_desc (Q : I → SimplicialQuiver.Data O) {D : FixedObjects O}
    (f : ∀ i, object (Q i) ⟶ D) (i : I) : sumInclusion Q i ≫ sumDesc Q f = f i := by
  apply generators_ext (Q i)
  intro x y
  rw [homMap_comp, ← Category.assoc, generator_sumInclusion, Category.assoc]
  change _ ≫ (generator (sumQuiver Q) x y ≫ homMap (extend (sumQuiver Q) D _) x y) = _
  rw [generator_extend]
  exact SSet.IndexedSums.inclusion_desc (fun i => (Q i).Hom x y) _ i

/-- The whole original free coproduct map is uniquely determined by its supplied original legs. -/
private theorem indexed_eval (Q : I → SimplicialQuiver.Data O) {D : FixedObjects O}
    (g : sumObject Q ⟶ D) (i : I) (x y : O) :
    SSet.IndexedSums.inclusion (fun i => (Q i).Hom x y) i ≫ generator (sumQuiver Q) x y ≫ homMap g x y =
      generator (Q i) x y ≫ homMap (sumInclusion Q i ≫ g) x y := by
  rw [homMap_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ homMap g x y) (generator_sumInclusion Q i x y)).symm.trans
      (Category.assoc _ _ _))

/-- The whole original free coproduct map is uniquely determined by its supplied original legs. -/
theorem sumDesc_unique (Q : I → SimplicialQuiver.Data O) {D : FixedObjects O}
    (f : ∀ i, object (Q i) ⟶ D) (g : sumObject Q ⟶ D)
    (h : ∀ i, sumInclusion Q i ≫ g = f i) : g = sumDesc Q f := by
  apply generators_ext (sumQuiver Q)
  intro x y
  apply SSet.IndexedSums.hom_ext (fun i => (Q i).Hom x y)
  intro i
  calc
    _ = generator (Q i) x y ≫ homMap (sumInclusion Q i ≫ g) x y := indexed_eval Q g i x y
    _ = generator (Q i) x y ≫ homMap (f i) x y := by rw [h i]
    _ = generator (Q i) x y ≫ homMap (sumInclusion Q i ≫ sumDesc Q f) x y := by rw [sumInclusion_desc]
    _ = _ := (indexed_eval Q (sumDesc Q f) i x y).symm

/-- The same whole indexed free inclusions form an original fixed-object coproduct cocone. -/
def sumCofan (Q : I → SimplicialQuiver.Data O) : Cofan (fun i => object (Q i)) :=
  Cofan.mk (sumObject Q) (sumInclusion Q)

/-- The actual entire free indexed generating sum has the full enriched coproduct universal property. -/
def sumIsColimit (Q : I → SimplicialQuiver.Data O) : IsColimit (sumCofan Q) :=
  Cofan.IsColimit.mk _ (fun s => sumDesc Q s.inj)
    (fun s i => sumInclusion_desc Q s.inj i)
    (fun s g h => sumDesc_unique Q s.inj g h)

/-- The same indexed family of generating maps acts on the entire original free sum. -/
def sumMap {Q R : I → SimplicialQuiver.Data O}
    (f : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y) : sumObject Q ⟶ sumObject R :=
  map (fun x y => SSet.IndexedSums.map (fun i => (Q i).Hom x y) (fun i => f i x y))

/-- The actual whole free sum map commutes with every same original indexed family map. -/
theorem sumInclusion_sumMap {Q R : I → SimplicialQuiver.Data O}
    (f : ∀ i x y, (Q i).Hom x y ⟶ (R i).Hom x y) (i : I) :
    sumInclusion Q i ≫ sumMap f = map (f i) ≫ sumInclusion R i := by
  apply generators_ext (Q i)
  intro x y
  calc
    _ = SSet.IndexedSums.inclusion (fun i => (Q i).Hom x y) i ≫
      generator (sumQuiver Q) x y ≫ homMap (sumMap f) x y := (indexed_eval Q (sumMap f) i x y).symm
    _ = SSet.IndexedSums.inclusion (fun i => (Q i).Hom x y) i ≫
      SSet.IndexedSums.map (fun i => (Q i).Hom x y) (fun i => f i x y) ≫ generator (sumQuiver R) x y := by
        change _ ≫ (generator (sumQuiver Q) x y ≫ homMap (map _) x y) = _
        rw [generator_map]
    _ = f i x y ≫ SSet.IndexedSums.inclusion (fun i => (R i).Hom x y) i ≫ generator (sumQuiver R) x y :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ generator (sumQuiver R) x y)
          (SSet.IndexedSums.inclusion_map (fun i => (Q i).Hom x y) (fun i => f i x y) i)).trans
          (Category.assoc _ _ _))
    _ = f i x y ≫ generator (R i) x y ≫ homMap (sumInclusion R i) x y :=
      congrArg (fun t => f i x y ≫ t) (generator_sumInclusion R i x y).symm
    _ = generator (Q i) x y ≫ homMap (map (f i)) x y ≫ homMap (sumInclusion R i) x y :=
      (congrArg (fun t => t ≫ homMap (sumInclusion R i) x y) (generator_map (f i) x y)).symm.trans
        (Category.assoc _ _ _)
    _ = _ := by rw [homMap_comp]

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiver
