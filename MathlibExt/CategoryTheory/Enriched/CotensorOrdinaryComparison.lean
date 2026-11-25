/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.ScalarCotensor
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Ordinary functors underlying enriched cotensor

For a monoidal closed coefficient category and an enriched ordinary index, identifies the
ordinary functor of an enriched cotensor with composition by internal Hom. Computes its map on
every ordinary index morphism.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor.CotensorOrdinaryComparison
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]

/-- The original enriched self-representable has the unchanged ordinary internal-Hom target map. -/
theorem representable_map (M : V) {X Y : V} (f : X ⟶ Y) :
    (EnrichedFunctor.covariantRepresentable V V M).toOrdinaryFunctor.map f =
      (ihom M).map f := by
  apply (eHomEquiv V).injective
  rw [EnrichedFunctor.toOrdinaryFunctor_map,
    MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv]
  change MonoidalClosed.curry' f ≫ MonoidalClosed.curry (eComp V M X Y) =
    MonoidalClosed.curry' ((ihom M).map f)
  rw [← MonoidalClosed.curry_natural_left]
  change MonoidalClosed.curry
      (((ihom M).obj X) ◁ MonoidalClosed.curry' f ≫ MonoidalClosed.comp M X Y) =
    MonoidalClosed.curry' ((ihom M).map f)
  rw [MonoidalClosed.whiskerLeft_curry'_comp]
  rfl

variable {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]

/-- Every original ordinary index arrow of the actual enriched cotensor is exactly the original
internal-Hom map of that same index arrow. -/
theorem map (M : V) (G : EnrichedFunctor V I V) {a b : I} (f : a ⟶ b) :
    (EnrichedFunctor.cotensor M G).toOrdinaryFunctor.map f =
      (ihom M).map (G.toOrdinaryFunctor.map f) := by
  let R := EnrichedFunctor.covariantRepresentable V V M
  let g : G.obj a ⟶ G.obj b := G.toOrdinaryFunctor.map f
  let u : (ihom M).obj (G.obj a) ⟶ (ihom M).obj (G.obj b) :=
    (EnrichedFunctor.cotensor M G).toOrdinaryFunctor.map f
  let v : (ihom M).obj (G.obj a) ⟶ (ihom M).obj (G.obj b) := (ihom M).map g
  have hu : eHomEquiv V u = eHomEquiv V f ≫ (G.map a b ≫ R.map (G.obj a) (G.obj b)) :=
    EnrichedFunctor.toOrdinaryFunctor_map (EnrichedFunctor.cotensor M G) f
  have hg : eHomEquiv V g = eHomEquiv V f ≫ G.map a b :=
    EnrichedFunctor.toOrdinaryFunctor_map G f
  have hv : eHomEquiv V v = eHomEquiv V g ≫ R.map (G.obj a) (G.obj b) := by
    have h := EnrichedFunctor.toOrdinaryFunctor_map R g
    have hm := representable_map M g
    exact (congrArg (fun w : (ihom M).obj (G.obj a) ⟶ (ihom M).obj (G.obj b) =>
      eHomEquiv V w) hm).symm.trans h
  change u = v
  apply (eHomEquiv V).injective
  exact hu.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun w => w ≫ R.map (G.obj a) (G.obj b)) hg.symm).trans hv.symm))

/-- The actual cotensor and ordinary internal Hom agree as whole ordinary functors, with every
original index map. -/
def comparison (M : V) (G : EnrichedFunctor V I V) :
    (EnrichedFunctor.cotensor M G).toOrdinaryFunctor ≅ G.toOrdinaryFunctor ⋙ ihom M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    let u : (ihom M).obj (G.obj a) ⟶ (ihom M).obj (G.obj b) :=
      (EnrichedFunctor.cotensor M G).toOrdinaryFunctor.map f
    let v : (ihom M).obj (G.obj a) ⟶ (ihom M).obj (G.obj b) :=
      (ihom M).map (G.toOrdinaryFunctor.map f)
    change u ≫
        𝟙 ((ihom M).obj (G.obj b)) =
      𝟙 ((ihom M).obj (G.obj a)) ≫ v
    rw [Category.comp_id, Category.id_comp]
    exact map M G f)

end CategoryTheory.EnrichedFunctor.CotensorOrdinaryComparison
