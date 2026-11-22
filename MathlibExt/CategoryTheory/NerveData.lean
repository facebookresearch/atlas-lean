/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# Generic nerve simplicial data

The nerve of a small category as simplicial `Data` and its genuine comparison
with Mathlib's simplicial nerve. Objects are `ComposableArrows C n`; faces and
degeneracies are the nerve maps. This is the generic layer relocated from
`CategoryTheory.CategoryBar.NerveComparison`, following the flat
`CategoryTheory` precedent of `NerveHomotopy.lean`.

Nonclaims: no two-sided bar, unit-coefficient, comma/category-of-elements, or
Grothendieck comparison, and no opposite/reversal, weak-equivalence, or
realization claim.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Nerve simplicial data.

Objects are `ComposableArrows C n`; faces and degeneracies are the nerve maps.
Each identity is nerve functoriality (`map_comp`, `map_id`) plus the
corresponding `SimplexCategory` relation, folded across the opposite via
`op_comp`. -/
noncomputable def nerveData (C : Type u) [Category.{v} C] :
    SimplicialObject.Data (Type (max u v)) where
  obj := fun n => ComposableArrows C n
  δ := fun {n} i => (nerve C).map (SimplexCategory.δ i).op
  σ := fun {n} i => (nerve C).map (SimplexCategory.σ i).op
  δ_comp_δ := by
    intro n i j h
    have inner : (SimplexCategory.δ j.succ).op ≫ (SimplexCategory.δ i).op =
        (SimplexCategory.δ i.castSucc).op ≫ (SimplexCategory.δ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_δ h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  δ_comp_σ_of_le := by
    intro n i j h
    have inner : (SimplexCategory.σ j.succ).op ≫ (SimplexCategory.δ i.castSucc).op =
        (SimplexCategory.δ i).op ≫ (SimplexCategory.σ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_of_le h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  δ_comp_σ_self := by
    intro n i
    have inner : (SimplexCategory.σ i).op ≫ (SimplexCategory.δ i.castSucc).op =
        𝟙 (Opposite.op (SimplexCategory.mk n)) := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_self, op_id]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_id _ _)
  δ_comp_σ_succ := by
    intro n i
    have inner : (SimplexCategory.σ i).op ≫ (SimplexCategory.δ i.succ).op =
        𝟙 (Opposite.op (SimplexCategory.mk n)) := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_succ, op_id]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_id _ _)
  δ_comp_σ_of_gt := by
    intro n i j h
    have inner : (SimplexCategory.σ j.castSucc).op ≫ (SimplexCategory.δ i.succ).op =
        (SimplexCategory.δ i).op ≫ (SimplexCategory.σ j).op := by
      simp only [← op_comp, SimplexCategory.δ_comp_σ_of_gt h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)
  σ_comp_σ := by
    intro n i j h
    have inner : (SimplexCategory.σ j).op ≫ (SimplexCategory.σ i.castSucc).op =
        (SimplexCategory.σ i).op ≫ (SimplexCategory.σ j.succ).op := by
      simp only [← op_comp, SimplexCategory.σ_comp_σ h]
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ inner)).trans
      (Functor.map_comp _ _ _)

/-- Face maps of `nerveData` are the nerve maps. -/
@[simp]
theorem nerveData_δ {n : ℕ} (i : Fin (n + 2)) :
    (nerveData C).δ i = (nerve C).map (SimplexCategory.δ i).op :=
  rfl

/-- Degeneracy maps of `nerveData` are the nerve maps. -/
@[simp]
theorem nerveData_σ {n : ℕ} (i : Fin (n + 1)) :
    (nerveData C).σ i = (nerve C).map (SimplexCategory.σ i).op :=
  rfl

/-- Nerve data agrees with Mathlib's nerve on a face generator. -/
private theorem nerveDataGenRel_δ {n : ℕ} (i : Fin (n + 2)) :
    (nerveData C).toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op =
      (nerve C).map
        (SimplexCategoryGenRel.toSimplexCategory.map
          (SimplexCategoryGenRel.δ i)).op := by
  rw [SimplicialObject.Data.toGenRelFunctor_map_δ_op,
    SimplexCategoryGenRel.toSimplexCategory_map_δ]
  exact nerveData_δ i

/-- Nerve data agrees with Mathlib's nerve on a degeneracy generator. -/
private theorem nerveDataGenRel_σ {n : ℕ} (i : Fin (n + 1)) :
    (nerveData C).toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op =
      (nerve C).map
        (SimplexCategoryGenRel.toSimplexCategory.map
          (SimplexCategoryGenRel.σ i)).op := by
  rw [SimplicialObject.Data.toGenRelFunctor_map_σ_op,
    SimplexCategoryGenRel.toSimplexCategory_map_σ]
  exact nerveData_σ i

/-- Nerve data agrees with Mathlib's nerve on every generator morphism. -/
private theorem nerveDataGenRel_map {x y : SimplexCategoryGenRel} (g : x ⟶ y) :
    (nerveData C).toGenRelFunctor.map g.op =
      (nerve C).map
        (SimplexCategoryGenRel.toSimplexCategory.map g).op := by
  refine SimplexCategoryGenRel.hom_induction
    (fun {a' b'} (k : a' ⟶ b') =>
      (nerveData C).toGenRelFunctor.map k.op =
        (nerve C).map
          (SimplexCategoryGenRel.toSimplexCategory.map k).op)
    (fun {n} => ?_) (fun u i ih => ?_) (fun u i ih => ?_) g
  · have hId : (𝟙 (SimplexCategoryGenRel.mk n)).op =
        𝟙 (Opposite.op (SimplexCategoryGenRel.mk n)) := rfl
    have hIdS : (SimplexCategoryGenRel.toSimplexCategory.map
        (𝟙 (SimplexCategoryGenRel.mk n))).op =
        𝟙 (Opposite.op (SimplexCategoryGenRel.toSimplexCategory.obj
          (SimplexCategoryGenRel.mk n))) := by
      rw [SimplexCategoryGenRel.toSimplexCategory.map_id]
      rfl
    rw [hId, (nerveData C).toGenRelFunctor.map_id, hIdS,
      (nerve C).map_id]
    rfl
  · have hComp : (u ≫ SimplexCategoryGenRel.δ i).op =
        (SimplexCategoryGenRel.δ i).op ≫ u.op := rfl
    have hCompS : (SimplexCategoryGenRel.toSimplexCategory.map
        (u ≫ SimplexCategoryGenRel.δ i)).op =
        (SimplexCategoryGenRel.toSimplexCategory.map
          (SimplexCategoryGenRel.δ i)).op ≫
        (SimplexCategoryGenRel.toSimplexCategory.map u).op := by
      rw [SimplexCategoryGenRel.toSimplexCategory.map_comp]
      rfl
    rw [hComp, (nerveData C).toGenRelFunctor.map_comp, hCompS,
      (nerve C).map_comp, ih, nerveDataGenRel_δ]
    rfl
  · have hComp : (u ≫ SimplexCategoryGenRel.σ i).op =
        (SimplexCategoryGenRel.σ i).op ≫ u.op := rfl
    have hCompS : (SimplexCategoryGenRel.toSimplexCategory.map
        (u ≫ SimplexCategoryGenRel.σ i)).op =
        (SimplexCategoryGenRel.toSimplexCategory.map
          (SimplexCategoryGenRel.σ i)).op ≫
        (SimplexCategoryGenRel.toSimplexCategory.map u).op := by
      rw [SimplexCategoryGenRel.toSimplexCategory.map_comp]
      rfl
    rw [hComp, (nerveData C).toGenRelFunctor.map_comp, hCompS,
      (nerve C).map_comp, ih, nerveDataGenRel_σ]
    rfl

/-- Genuine nerve-data comparison with Mathlib's simplicial nerve.

Both sides act identically on every generator morphism, so every component
is the identity. -/
noncomputable def nerveDataSimplicialIso (C : Type u) [Category.{v} C] :
    (nerveData C).toSimplicialObject ≅ nerve C :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {Δ Δ'} f => by
    have hGen := nerveDataGenRel_map (C := C)
      (SimplexCategoryGenRel.fromSimplexCategory.map f.unop)
    have hLeft : (nerveData C).toSimplicialObject.map f =
        (nerveData C).toGenRelFunctor.map
          (SimplexCategoryGenRel.fromSimplexCategory.map f.unop).op := rfl
    have hPre : SimplexCategoryGenRel.toSimplexCategory.map
        (SimplexCategoryGenRel.fromSimplexCategory.map f.unop) = f.unop := by
      rw [SimplexCategoryGenRel.fromSimplexCategory_map_preimage]
    have hMid : (nerve C).map
        (SimplexCategoryGenRel.toSimplexCategory.map
          (SimplexCategoryGenRel.fromSimplexCategory.map f.unop)).op =
        (nerve C).map f := by
      rw [hPre]
      exact congrArg (nerve C).map (Quiver.Hom.op_unop f)
    have hFG : (nerveData C).toSimplicialObject.map f =
        (nerve C).map f := by
      rw [hLeft, hGen, hMid]
    change (nerveData C).toSimplicialObject.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (nerve C).map f
    rw [Category.comp_id, Category.id_comp]
    exact hFG

/-- Forward component of `nerveDataSimplicialIso` is the identity.

Both sides act identically on every generator morphism, so the chosen
component iso is `Iso.refl _`. Consumers should rewrite with this lemma
rather than unfolding the multi-component iso construction. -/
@[simp]
theorem nerveDataSimplicialIso_hom_app (n : ℕ) :
    (nerveDataSimplicialIso C).hom.app (Opposite.op (SimplexCategory.mk n)) =
      𝟙 _ :=
  rfl

/-- Backward component of `nerveDataSimplicialIso` is the identity.

Both sides act identically on every generator morphism, so the chosen
component iso is `Iso.refl _`. Consumers should rewrite with this lemma
rather than unfolding the multi-component iso construction. -/
@[simp]
theorem nerveDataSimplicialIso_inv_app (n : ℕ) :
    (nerveDataSimplicialIso C).inv.app (Opposite.op (SimplexCategory.mk n)) =
      𝟙 _ :=
  rfl

end CategoryTheory

end
