/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoid
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# The original finite-label copower coend of the generic sphere operator

The Hom object from `n` to `k` is the colimit of all coefficient objects
`T^a` labelled by complete finite bijections `a ⊗ n ⟶ k`. Its relations
are the original coefficient-index maps. This is a `V`-object construction;
no enriched-ordinary dictionary is imposed on the old finite-bijection category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

/-- The actual coefficient-first labelled index of the operator Hom coend. -/
abbrev Labels (n k : I) := CostructuredArrow (tensorRight n) k

/-- Every target-index map retains all coefficient objects and postcomposes their full labels. -/
abbrev targetLabels (n : I) {k l : I} (f : k ⟶ l) : Labels n k ⥤ Labels n l :=
  CostructuredArrow.map f

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]

/-- The complete original coefficient diagram, before taking its labelled coend. -/
abbrev diagram (T : V) (n k : I) : Labels n k ⥤ V :=
  CostructuredArrow.proj (tensorRight n) k ⋙ (genericSphereSequence T).functor

/-- The genuine value-category object of all original operator coefficients and label relations. -/
def Hom (T : V) (n k : I) : V := colimit (diagram T n k)

/-- The full original coefficient enters its Hom coend at the specified whole finite bijection. -/
def generator (T : V) (a n k : I) (f : a ⊗ n ⟶ k) :
    (genericSphereSequence T).functor.obj a ⟶ Hom T n k :=
  colimit.ι (diagram T n k) (CostructuredArrow.mk (Y := a) f)

/-- Every original coefficient-index map imposes its actual labelled coend relation. -/
theorem generator_relation (T : V) {a b n k : I} (r : a ⟶ b) (f : b ⊗ n ⟶ k) :
    (genericSphereSequence T).functor.map r ≫ generator T b n k f =
      generator T a n k ((r ▷ n) ≫ f) := by
  let q : Labels n k := CostructuredArrow.mk (Y := a) ((r ▷ n) ≫ f)
  let q' : Labels n k := CostructuredArrow.mk (Y := b) f
  let h : q ⟶ q' := CostructuredArrow.homMk r rfl
  exact colimit.w (diagram T n k) h

/-- Whole coefficient generators determine every map from the original Hom coend. -/
theorem hom_ext (T : V) (n k : I) {Z : V} (f g : Hom T n k ⟶ Z)
    (h : ∀ (a : I) (r : a ⊗ n ⟶ k), generator T a n k r ≫ f = generator T a n k r ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro q
  exact h q.left q.hom

/-- The complete target-index cocone postcomposes every original finite label. -/
def targetCocone (T : V) (n : I) {k l : I} (f : k ⟶ l) : Cocone (diagram T n k) where
  pt := Hom T n l
  ι :=
    { app q := generator T q.left n l (q.hom ≫ f)
      naturality := by
        intro q q' r
        simp only [Functor.const_obj_map]
        have h := generator_relation T r.left (q'.hom ≫ f)
        have hl : (r.left ▷ n) ≫ (q'.hom ≫ f) = q.hom ≫ f :=
          (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ f) r.w)
        exact h.trans ((congrArg (generator T q.left n l) hl).trans
          (Category.comp_id _).symm) }

/-- The actual target-index map on the whole operator Hom coend. -/
def targetMap (T : V) (n : I) {k l : I} (f : k ⟶ l) : Hom T n k ⟶ Hom T n l :=
  colimit.desc (diagram T n k) (targetCocone T n f)

/-- Every entire target-index map has its unchanged original generating label equation. -/
theorem generator_targetMap (T : V) (a n k l : I) (r : a ⊗ n ⟶ k) (f : k ⟶ l) :
    generator T a n k r ≫ targetMap T n f = generator T a n l (r ≫ f) := by
  unfold targetMap
  exact colimit.ι_desc (targetCocone T n f) (CostructuredArrow.mk (Y := a) r)

/-- All target-index identities act by the identity on the complete Hom coend. -/
theorem targetMap_id (T : V) (n k : I) : targetMap T n (𝟙 k) = 𝟙 (Hom T n k) := by
  apply hom_ext T n k
  intro a r
  exact (generator_targetMap T a n k k r (𝟙 k)).trans
    ((congrArg (generator T a n k) (Category.comp_id r)).trans
      (Category.comp_id _).symm)

/-- Every source-first target-index composite acts by the corresponding whole Hom-map composite. -/
theorem targetMap_comp (T : V) (n : I) {k l m : I} (f : k ⟶ l) (g : l ⟶ m) :
    targetMap T n (f ≫ g) = targetMap T n f ≫ targetMap T n g := by
  apply hom_ext T n k
  intro a r
  exact (generator_targetMap T a n k m r (f ≫ g)).trans
    ((congrArg (generator T a n m) (Category.assoc r f g).symm).trans
      ((generator_targetMap T a n l m (r ≫ f) g).symm.trans
        ((congrArg (fun t => t ≫ targetMap T n g) (generator_targetMap T a n k l r f).symm).trans
          (Category.assoc _ _ _))))

end CategoryTheory.Spectra.Symmetric.OperatorCoend
