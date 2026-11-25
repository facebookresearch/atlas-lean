/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# Actual original weak coproduct maps at independent index universes

The SAME original coproduct is compared by canonical Sigma.reindex
with the full ULift-labelled family in the coefficient universe. Both
native inclusion equations retain each original label and map.
Genuine same-universe coproduct weakness transfers across those isos.
-/

@[expose] public section


noncomputable section
universe u v
open CategoryTheory Limits
namespace SSet

/-- An actual coproduct map is realization weak at independent original index and coefficient
levels. -/
theorem sigma_map_weak_universes {I : Type u} {X Y : I → SSet.{max u v}}
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, realizationWeakEquivalences (f i)) :
    realizationWeakEquivalences (Limits.Sigma.map f) := by
  let J := ULift.{v} I
  let X' : J → SSet.{max u v} := X ∘ Equiv.ulift
  let Y' : J → SSet.{max u v} := Y ∘ Equiv.ulift
  let f' : ∀ i : J, X' i ⟶ Y' i := fun i => f i.down
  have hbig : realizationWeakEquivalences (Limits.Sigma.map f') :=
    sigma_map_mem_realizationWeakEquivalences f' (fun i => hf i.down)
  let eX : (∐ X' : SSet.{max u v}) ≅ ∐ X := Sigma.reindex Equiv.ulift X
  let eY : (∐ Y' : SSet.{max u v}) ≅ ∐ Y := Sigma.reindex Equiv.ulift Y
  have hsq : (Limits.Sigma.map f') ≫ eY.hom = eX.hom ≫ Limits.Sigma.map f := by
    apply Sigma.hom_ext
    intro i
    have hleft : Sigma.ι X' i ≫ (Limits.Sigma.map f' ≫ eY.hom) = f' i ≫ Sigma.ι Y i.down := by
      have h₁ := Sigma.ι_map f' i
      have h₂ := Sigma.ι_reindex_hom Equiv.ulift Y i
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ eY.hom) h₁).trans
          ((Category.assoc _ _ _).trans (congrArg (fun h => f' i ≫ h) h₂)))
    have hright : Sigma.ι X' i ≫ (eX.hom ≫ Limits.Sigma.map f) = f' i ≫ Sigma.ι Y i.down := by
      have h₁ := Sigma.ι_reindex_hom Equiv.ulift X i
      have h₂ := Sigma.ι_map f i.down
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ Limits.Sigma.map f) h₁).trans h₂)
    exact hleft.trans hright.symm
  have h := realizationWeakEquivalences.comp_mem _ _ hbig
    (realizationWeakEquivalences.of_isIso eY.hom)
  rw [hsq] at h
  exact realizationWeakEquivalences.of_precomp eX.hom _
    (realizationWeakEquivalences.of_isIso eX.hom) h

end SSet
