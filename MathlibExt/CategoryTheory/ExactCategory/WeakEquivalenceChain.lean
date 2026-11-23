/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ExactCategory.Equivalence
public import MathlibExt.CategoryTheory.MorphismProperty.Chain

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exact weak-equivalence chains

An `ExactWeakChain C k` is a chain of `k` isomorphisms in `C`.  Evaluation at
the zero vertex is equivalent to `C`; an inverse sends an object to its
constant chain.  This equivalence supplies canonical zero objects and binary
biproducts on the chain carrier.

For an exact category, its exact structure may then be transported through
the evaluation equivalence.  This transported exact structure is a named
definition, not a global instance, since a preadditive category can support
more than one exact structure.

The transported exact structure uses the same evaluation equivalence and
its original object and morphism maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CategoryTheory

/-- Chains whose successive arrows are isomorphisms.  This carrier is
independent of any choice of Waldhausen structure. -/
abbrev ExactWeakChain (C : Type u) [Category.{v} C] (k : ℕ) :=
  MorphismPropertyChain (MorphismProperty.isomorphisms C) k

/-- Evaluation of an exact weak chain at an arbitrary vertex. -/
def exactWeakChainEval (C : Type u) [Category.{v} C] (k : ℕ)
    (r : Fin (k + 1)) : ExactWeakChain C k ⥤ C :=
  morphismPropertyChainEval (MorphismProperty.isomorphisms C) k r

@[simp]
theorem exactWeakChainEval_obj
    (C : Type u) [Category.{v} C] (k : ℕ) (r : Fin (k + 1))
    (X : ExactWeakChain C k) :
    (exactWeakChainEval C k r).obj X = X.obj.obj r :=
  rfl

@[simp]
theorem exactWeakChainEval_map
    (C : Type u) [Category.{v} C] (k : ℕ) (r : Fin (k + 1))
    {X Y : ExactWeakChain C k} (f : X ⟶ Y) :
    (exactWeakChainEval C k r).map f = f.hom.app r :=
  rfl

/-- Evaluation of an exact weak chain at its zero vertex. -/
abbrev exactWeakChainEvalZero (C : Type u) [Category.{v} C] (k : ℕ) :
    ExactWeakChain C k ⥤ C :=
  exactWeakChainEval C k 0

@[simp]
theorem exactWeakChainEvalZero_obj
    (C : Type u) [Category.{v} C] (k : ℕ) (X : ExactWeakChain C k) :
    (exactWeakChainEvalZero C k).obj X = X.obj.obj 0 :=
  rfl

@[simp]
theorem exactWeakChainEvalZero_map
    (C : Type u) [Category.{v} C] (k : ℕ)
    {X Y : ExactWeakChain C k} (f : X ⟶ Y) :
    (exactWeakChainEvalZero C k).map f = f.hom.app 0 :=
  rfl

/-- The constant exact weak chain. -/
def exactWeakChainConst (C : Type u) [Category.{v} C] (k : ℕ) :
    C ⥤ ExactWeakChain C k :=
  (morphismPropertyChainProperty
      (MorphismProperty.isomorphisms C) k).lift
    (Functor.const (Fin (k + 1)))
    (fun X i => by
      change IsIso (𝟙 X)
      infer_instance)

@[simp]
theorem exactWeakChainConst_obj_obj
    (C : Type u) [Category.{v} C] (k : ℕ) (X : C)
    (i : Fin (k + 1)) :
    ((exactWeakChainConst C k).obj X).obj.obj i = X :=
  rfl

@[simp]
theorem exactWeakChainConst_map_app
    (C : Type u) [Category.{v} C] (k : ℕ)
    {X Y : C} (f : X ⟶ Y) (i : Fin (k + 1)) :
    ((exactWeakChainConst C k).map f).hom.app i = f :=
  rfl

/-- The constant chain on the zero vertex of `X` is canonically isomorphic
to `X`.  Its component at `i` is the transition from zero to `i`. -/
noncomputable def exactWeakChainConstIso
    (C : Type u) [Category.{v} C] (k : ℕ)
    (X : ExactWeakChain C k) :
    (exactWeakChainConst C k).obj
        ((exactWeakChainEvalZero C k).obj X) ≅ X :=
  (morphismPropertyChainProperty
      (MorphismProperty.isomorphisms C) k).isoMk
    (NatIso.ofComponents
      (fun (i : Fin (k + 1)) => by
        let f : (0 : Fin (k + 1)) ⟶ i := homOfLE (Fin.zero_le i)
        exact @asIso C _ _ _ (X.obj.map f)
          (morphismPropertyChain_map_mem
            (MorphismProperty.isomorphisms C) k X f))
      (by
        intro i j f
        change 𝟙 _ ≫ X.obj.map (homOfLE (Fin.zero_le j)) =
          X.obj.map (homOfLE (Fin.zero_le i)) ≫ X.obj.map f
        rw [Category.id_comp, ← X.obj.map_comp]
        exact X.obj.congr_map (Subsingleton.elim _ _)))

@[simp]
theorem exactWeakChainConstIso_hom_app
    (C : Type u) [Category.{v} C] (k : ℕ)
    (X : ExactWeakChain C k) (i : Fin (k + 1)) :
    (exactWeakChainConstIso C k X).hom.hom.app i =
      X.obj.map (homOfLE (Fin.zero_le i) :
        (0 : Fin (k + 1)) ⟶ i) :=
  rfl

/-- Evaluation at zero is naturally isomorphic to evaluation at any vertex.
The component is the ordered transition from zero to that vertex. -/
noncomputable def exactWeakChainEvalZeroIso
    (C : Type u) [Category.{v} C] (k : ℕ) (r : Fin (k + 1)) :
    exactWeakChainEvalZero C k ≅ exactWeakChainEval C k r :=
  NatIso.ofComponents
    (fun (X : ExactWeakChain C k) => by
      let f : (0 : Fin (k + 1)) ⟶ r := homOfLE (Fin.zero_le r)
      exact @asIso C _ _ _ (X.obj.map f)
        (morphismPropertyChain_map_mem
          (MorphismProperty.isomorphisms C) k X f))
    (by
      intro X Y f
      change f.hom.app 0 ≫ Y.obj.map (homOfLE (Fin.zero_le r)) =
        X.obj.map (homOfLE (Fin.zero_le r)) ≫ f.hom.app r
      exact (f.hom.naturality (homOfLE (Fin.zero_le r))).symm)

@[simp]
theorem exactWeakChainEvalZeroIso_hom_app
    (C : Type u) [Category.{v} C] (k : ℕ) (r : Fin (k + 1))
    (X : ExactWeakChain C k) :
    (exactWeakChainEvalZeroIso C k r).hom.app X =
      X.obj.map (homOfLE (Fin.zero_le r) :
        (0 : Fin (k + 1)) ⟶ r) :=
  rfl

/-- The constant-chain comparison is natural in the exact weak chain. -/
noncomputable def exactWeakChainConstNatIso
    (C : Type u) [Category.{v} C] (k : ℕ) :
    exactWeakChainEvalZero C k ⋙ exactWeakChainConst C k ≅
      (𝟭 (ExactWeakChain C k) :
        ExactWeakChain C k ⥤ ExactWeakChain C k) :=
  NatIso.ofComponents (exactWeakChainConstIso C k)
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      ext i
      simp only [Functor.comp_map, exactWeakChainEvalZero_map,
        Functor.id_map]
      exact (f.hom.naturality (homOfLE (Fin.zero_le i))).symm)

/-- Evaluation at zero is an equivalence, with the constant-chain functor as
its literal inverse. -/
@[instance_reducible]
noncomputable def exactWeakChainEvaluationEquivalence
    (C : Type u) [Category.{v} C] (k : ℕ) :
    ExactWeakChain C k ≌ C where
  functor := exactWeakChainEvalZero C k
  inverse := exactWeakChainConst C k
  unitIso := (exactWeakChainConstNatIso C k).symm
  counitIso := NatIso.ofComponents (fun X => Iso.refl X)
  functor_unitIso_comp X := by
    change (exactWeakChainConstIso C k X).inv.hom.app 0 ≫
        𝟙 _ = 𝟙 _
    rw [Category.comp_id]
    apply (cancel_epi
      ((exactWeakChainConstIso C k X).hom.hom.app
        (0 : Fin (k + 1)))).mp
    have h := congrArg (fun f => f.hom.app (0 : Fin (k + 1)))
      (exactWeakChainConstIso C k X).hom_inv_id
    have hhomInv :
        (exactWeakChainConstIso C k X).hom.hom.app 0 ≫
          (exactWeakChainConstIso C k X).inv.hom.app 0 = 𝟙 _ := by
      simpa only [ObjectProperty.FullSubcategory.comp_hom,
        NatTrans.comp_app, ObjectProperty.FullSubcategory.id_hom,
        NatTrans.id_app] using h
    have hhom : (exactWeakChainConstIso C k X).hom.hom.app 0 = 𝟙 _ := by
      rw [exactWeakChainConstIso_hom_app]
      calc
        X.obj.map (homOfLE (Fin.zero_le 0)) = X.obj.map (𝟙 0) :=
          X.obj.congr_map (Subsingleton.elim _ _)
        _ = 𝟙 _ := X.obj.map_id _
    rw [hhomInv]
    exact hhom.symm.trans (Category.comp_id _).symm

@[simp]
theorem exactWeakChainEvaluationEquivalence_functor
    (C : Type u) [Category.{v} C] (k : ℕ) :
    (exactWeakChainEvaluationEquivalence C k).functor =
      exactWeakChainEvalZero C k :=
  rfl

@[simp]
theorem exactWeakChainEvaluationEquivalence_inverse
    (C : Type u) [Category.{v} C] (k : ℕ) :
    (exactWeakChainEvaluationEquivalence C k).inverse =
      exactWeakChainConst C k :=
  rfl

instance exactWeakChainEval_additive
    (C : Type u) [Category.{v} C] [Preadditive C] (k : ℕ)
    (r : Fin (k + 1)) : (exactWeakChainEval C k r).Additive := by
  dsimp [exactWeakChainEval, morphismPropertyChainEval]
  infer_instance

noncomputable instance exactWeakChainEval_isEquivalence
    (C : Type u) [Category.{v} C] (k : ℕ) (r : Fin (k + 1)) :
    (exactWeakChainEval C k r).IsEquivalence := by
  let _ : (exactWeakChainEvalZero C k).IsEquivalence := by
    change (exactWeakChainEvaluationEquivalence C k).functor.IsEquivalence
    infer_instance
  exact Functor.isEquivalence_of_iso (exactWeakChainEvalZeroIso C k r)

/-- The zero object transported through evaluation at zero. -/
noncomputable instance exactWeakChainHasInitial
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (k : ℕ) : HasInitial (ExactWeakChain C k) :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (exactWeakChainEvaluationEquivalence C k).functor

noncomputable instance exactWeakChainHasZeroObject
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (k : ℕ) : HasZeroObject (ExactWeakChain C k) :=
  hasZeroObject_of_hasInitial_object

/-- Binary products transported through evaluation at zero. -/
noncomputable instance exactWeakChainHasBinaryProducts
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (k : ℕ) :
    HasBinaryProducts (ExactWeakChain C k) :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (exactWeakChainEvaluationEquivalence C k).functor

noncomputable instance exactWeakChainHasBinaryBiproducts
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (k : ℕ) :
    HasBinaryBiproducts (ExactWeakChain C k) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- An exact weak chain is zero exactly when its value at any chosen vertex
is zero. -/
theorem exactWeakChain_isZero_iff_eval
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (k : ℕ) (r : Fin (k + 1)) (X : ExactWeakChain C k) :
    IsZero X ↔ IsZero ((exactWeakChainEval C k r).obj X) := by
  constructor
  · exact (exactWeakChainEval C k r).map_isZero
  · intro h
    let _ : (exactWeakChainEvaluationEquivalence C k).functor.Additive := by
      change (exactWeakChainEval C k 0).Additive
      infer_instance
    let _ : (exactWeakChainConst C k).Additive :=
      (exactWeakChainEvaluationEquivalence C k).inverse_additive
    have h0 : IsZero ((exactWeakChainEvalZero C k).obj X) :=
      ((exactWeakChainEvalZeroIso C k r).app X).isZero_iff.mpr h
    have hc : IsZero ((exactWeakChainConst C k).obj
        ((exactWeakChainEvalZero C k).obj X)) :=
      (exactWeakChainConst C k).map_isZero h0
    exact (exactWeakChainConstIso C k X).isZero_iff.mp hc

/-- The exact structure on isomorphism chains transported from evaluation at
zero.  This is intentionally not a global instance. -/
@[instance_reducible]
noncomputable def exactWeakChainExactCategory
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (k : ℕ) : ExactCategory (ExactWeakChain C k) :=
  let _ : (exactWeakChainEvaluationEquivalence C k).functor.Additive := by
    change (exactWeakChainEval C k 0).Additive
    infer_instance
  ExactCategory.ofEquivalence (exactWeakChainEvaluationEquivalence C k)

/-- Under the transported exact structure, admissible exactness is detected
at the zero vertex. -/
theorem exactWeakChain_isAdmissibleExact_iff
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (k : ℕ) (S : ShortComplex (ExactWeakChain C k)) :
    letI : ExactCategory (ExactWeakChain C k) :=
      exactWeakChainExactCategory C k
    ExactCategory.IsAdmissibleExact S ↔
      ExactCategory.IsAdmissibleExact
        (S.map (exactWeakChainEvalZero C k)) :=
  let _ : (exactWeakChainEvaluationEquivalence C k).functor.Additive := by
    change (exactWeakChainEval C k 0).Additive
    infer_instance
  ExactCategory.ofEquivalence_isAdmissibleExact_iff
    (exactWeakChainEvaluationEquivalence C k) S

end CategoryTheory

end
