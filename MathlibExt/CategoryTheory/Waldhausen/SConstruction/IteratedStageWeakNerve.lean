/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakNerve
public import MathlibExt.CategoryTheory.Waldhausen.WeakFunctor

/-!
# The original multisimplicial weak iterated S-construction

At every finite simplex tuple, objects are the original iterated S-stages
and morphisms are their original weak equivalences. The actual exact tuple
reindex functors preserve these maps. Their earned identity/composition
laws bundle the complete multisimplicial category and its original nerve.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original weak-equivalence category on the actual iterated S-stage carrier. -/
abbrev IteratedStageWeakAtTuple {r : ℕ} (a : StageSimplexTuple r) :=
  WideSubcategory (WaldhausenCategoryWithoutGluing.weakEquivalences (C := StageAtTuple C a))

/-- The actual original tuple reindex map restricts to its original weak morphisms. -/
def reindexIteratedStageWeak {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    IteratedStageWeakAtTuple C a ⥤ IteratedStageWeakAtTuple C b :=
  (reindexIteratedStage_isWaldhausenExact C α).mapWeakCategory

/-- Actual weak tuple maps retain their original identity objects and morphisms. -/
theorem reindexIteratedStageWeak_id (r : ℕ) (a : StageSimplexTuple r) :
    reindexIteratedStageWeak C (𝟙 a) = 𝟭 (IteratedStageWeakAtTuple C a) := by
  unfold reindexIteratedStageWeak
  exact (Functor.IsWaldhausenExact.mapWeakCategory_eq (reindexIteratedStage_isWaldhausenExact C
      (𝟙 a))
    (Functor.IsWaldhausenExact.id (C := StageAtTuple C a))
    (reindexIteratedStage_id C r a)).trans (by rfl)

/-- Actual weak tuple maps retain original componentwise simplex composition. -/
theorem reindexIteratedStageWeak_comp (r : ℕ) {a b c : StageSimplexTuple r}
    (α : a ⟶ b) (β : b ⟶ c) :
    reindexIteratedStageWeak C (α ≫ β) =
      reindexIteratedStageWeak C α ⋙ reindexIteratedStageWeak C β := by
  unfold reindexIteratedStageWeak
  exact (Functor.IsWaldhausenExact.mapWeakCategory_eq (reindexIteratedStage_isWaldhausenExact C (α
      ≫ β))
    ((reindexIteratedStage_isWaldhausenExact C α).comp
      (reindexIteratedStage_isWaldhausenExact C β))
    (reindexIteratedStage_comp C r α β)).trans (by rfl)

/-- The original weak iterated S-categories form a genuine multisimplicial category. -/
def iteratedStageWeakMultisimplicial (r : ℕ) : StageSimplexTuple r ⥤ Cat.{v, max u v} where
  obj a := Cat.of (IteratedStageWeakAtTuple C a)
  map α := (reindexIteratedStageWeak C α).toCatHom
  map_id a := by rw [reindexIteratedStageWeak_id]; rfl
  map_comp α β := by rw [reindexIteratedStageWeak_comp]; rfl

/-- The complete original nerve retains all original finite S-stage directions. -/
def iteratedStageWeakNerve (r : ℕ) : StageSimplexTuple r ⥤ SSet.{max u v} :=
  iteratedStageWeakMultisimplicial C r ⋙ CategoryTheory.nerveFunctor

/-- Every whole original nerve map is the nerve of the actual original weak tuple map. -/
theorem iteratedStageWeakNerve_map {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    (iteratedStageWeakNerve C r).map α = CategoryTheory.nerveMap (reindexIteratedStageWeak C α) :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
