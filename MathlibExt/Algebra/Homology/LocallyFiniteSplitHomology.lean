/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologyMapComponent
public import MathlibExt.CategoryTheory.Linear.LocallyFiniteSplitCoproduct
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Actual locally finite split-complex homology coproducts

Original split image inclusions/projections and their original finite
middle-degree projector sum give the actual homology coproduct inverse.
Native homology depends only on the original middle component, so no
global homology/coproduct preservation or AB5 certificate is needed. The
inverse is the genuine finite native sum of the original projection
homology maps followed by coproduct inclusions.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (F : ℕ → HomologicalComplex C c)
  (i : ∀ j : ℕ, F j ⟶ K) (p : ∀ j : ℕ, K ⟶ F j)
  (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
  (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
  (n : ι) (N : ℕ)
  (hsupport : ∀ j : ℕ, N < j → (p j).f n = 0)
  (hsum : (∑ j : Fin (N + 1), (p j).f n ≫ (i j).f n) = 𝟙 (K.X n))
  [HasCoproduct (fun j : ℕ => (F j).homology n)]

include hsum in
/-- The actual finite middle-component sum gives the actual identity homology projector sum. -/
theorem finiteSplitHomology_projector_sum :
    (∑ j : Fin (N + 1), homologyMap (p j.val) n ≫ homologyMap (i j.val) n) = 𝟙 (K.homology n) := by
  classical
  let s : K ⟶ K := ∑ j : Fin (N + 1), p j.val ≫ i j.val
  have hs : s.f n = 𝟙 (K.X n) :=
    ((HomologicalComplex.eval C c n).map_sum
      (fun j : Fin (N + 1) => p j.val ≫ i j.val) Finset.univ).trans
        ((Finset.sum_congr rfl (fun j _ => by
          exact HomologicalComplex.comp_f (p j.val) (i j.val) n)).trans hsum)
  have hhom := homologyMap_eq_id_of_component n s hs
  simp_rw [← homologyMap_comp]
  change (∑ j : Fin (N + 1), (homologyFunctor C c n).map (p j.val ≫ i j.val)) = _
  rw [← Functor.map_sum]
  exact hhom

include hsplit hcross hsupport hsum in
/-- The actual locally finite split-image homology inclusion descent has its genuine finite projection inverse. -/
def finiteSplitHomologyCoproductIso : (∐ (fun j : ℕ => (F j).homology n)) ≅ K.homology n :=
  finiteSplitCoproductIso (fun j : ℕ => (F j).homology n)
    (fun j => homologyMap (i j) n) (fun j => homologyMap (p j) n) N
    (by
      intro j
      rw [← homologyMap_comp, hsplit, homologyMap_id])
    (by
      intro j k hjk
      rw [← homologyMap_comp, hcross j k hjk, homologyMap_zero])
    (by
      intro j hj
      exact homologyMap_eq_zero_of_component n (p j) (hsupport j hj))
    (finiteSplitHomology_projector_sum K F i p n N hsum)

include hsplit hcross hsupport hsum in
/-- The actual forward map is the original native sum of the image homology inclusions. -/
theorem finiteSplitHomologyCoproductIso_hom :
    (finiteSplitHomologyCoproductIso K F i p hsplit hcross n N hsupport hsum).hom =
      Sigma.desc (fun j => homologyMap (i j) n) := rfl

end HomologicalComplex
