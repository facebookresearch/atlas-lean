/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.ExactCategory.WeakEquivalenceChain

/-!
# Exact weak-equivalence chain tests

These tests pin the generic carrier, evaluation and constant-chain formulas,
the ordered zero-to-vertex comparison, the transported additive carrier
structures, and the local exactness characterization.
-/

noncomputable section

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C]

example (k : ℕ) : ExactWeakChain C k =
    MorphismPropertyChain (MorphismProperty.isomorphisms C) k :=
  rfl

example (k : ℕ) : ExactWeakChain C k ⥤ C :=
  exactWeakChainEvalZero C k

example (k : ℕ) (r : Fin (k + 1)) : ExactWeakChain C k ⥤ C :=
  exactWeakChainEval C k r

example (k : ℕ) : C ⥤ ExactWeakChain C k :=
  exactWeakChainConst C k

example (k : ℕ) : ExactWeakChain C k ≌ C :=
  exactWeakChainEvaluationEquivalence C k

example (k : ℕ) (X : ExactWeakChain C k) :
    (exactWeakChainEvalZero C k).obj X = X.obj.obj 0 :=
  exactWeakChainEvalZero_obj C k X

example (k : ℕ) {X Y : ExactWeakChain C k} (f : X ⟶ Y) :
    (exactWeakChainEvalZero C k).map f = f.hom.app 0 :=
  exactWeakChainEvalZero_map C k f

example (k : ℕ) (r : Fin (k + 1))
    {X Y : ExactWeakChain C k} (f : X ⟶ Y) :
    (exactWeakChainEval C k r).map f = f.hom.app r :=
  exactWeakChainEval_map C k r f

example (k : ℕ) (X : C) (i : Fin (k + 1)) :
    ((exactWeakChainConst C k).obj X).obj.obj i = X :=
  exactWeakChainConst_obj_obj C k X i

example (k : ℕ) {X Y : C} (f : X ⟶ Y) (i : Fin (k + 1)) :
    ((exactWeakChainConst C k).map f).hom.app i = f :=
  exactWeakChainConst_map_app C k f i

/-- In degree zero the comparison component is the identity transition. -/
example (X : ExactWeakChain C 0) :
    (exactWeakChainEvalZeroIso C 0 0).hom.app X = 𝟙 _ := by
  rw [exactWeakChainEvalZeroIso_hom_app]
  simp

/-- In degree one the comparison reaches the right-hand vertex. -/
example (X : ExactWeakChain C 1) :
    (exactWeakChainEvalZeroIso C 1 1).hom.app X =
      X.obj.map' 0 1 := by
  rw [exactWeakChainEvalZeroIso_hom_app]

/-- In degree two the terminal component is the composite zero-to-two
transition, not either individual successor edge. -/
example (X : ExactWeakChain C 2) :
    (exactWeakChainEvalZeroIso C 2 2).hom.app X =
      X.obj.map' 0 2 := by
  rw [exactWeakChainEvalZeroIso_hom_app]

section Additive

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

example (k : ℕ) (r : Fin (k + 1)) :
    (exactWeakChainEval C k r).Additive :=
  inferInstance

example (k : ℕ) (r : Fin (k + 1)) :
    (exactWeakChainEval C k r).IsEquivalence :=
  inferInstance

example (k : ℕ) (r : Fin (k + 1)) (X : ExactWeakChain C k) :
    IsZero X ↔ IsZero ((exactWeakChainEval C k r).obj X) :=
  exactWeakChain_isZero_iff_eval C k r X

example (k : ℕ) : HasZeroObject (ExactWeakChain C k) :=
  inferInstance

example (k : ℕ) : HasBinaryBiproducts (ExactWeakChain C k) :=
  inferInstance

section Exact

variable [CategoryTheory.ExactCategory C]

example (k : ℕ) : CategoryTheory.ExactCategory (ExactWeakChain C k) :=
  exactWeakChainExactCategory C k

example (k : ℕ) (S : ShortComplex (ExactWeakChain C k)) :
    letI : CategoryTheory.ExactCategory (ExactWeakChain C k) :=
      exactWeakChainExactCategory C k
    CategoryTheory.ExactCategory.IsAdmissibleExact S ↔
      CategoryTheory.ExactCategory.IsAdmissibleExact
        (S.map (exactWeakChainEvalZero C k)) :=
  exactWeakChain_isAdmissibleExact_iff C k S

end Exact

end Additive

end MathlibExtTest.CategoryTheory.ExactCategory

end
