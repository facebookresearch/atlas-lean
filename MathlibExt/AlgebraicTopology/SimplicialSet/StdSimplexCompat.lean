/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/

module

-- BACKPORT: Remaining standard-simplex helpers from Mathlib PR #42435,
-- head `e09070f786c9fc0a688e6239d71230b618b045ff`,
-- `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`,
-- blob `01377b85904978d402c830501e4615606021df8c`.
-- Five face formulas are delegated upstream; see `BACKPORTS.md`.

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Standard-simplex coordinates and representable simplex images

Face and degeneracy coordinates agree with their finite-index maps, and Yoneda transposition
commutes with simplex operators. A simplex whose Yoneda map is monic generates a representable
subcomplex, with its identity coordinate and inclusion computed explicitly. The nine retained
helpers use the pinned standard-simplex API; the five edge and triangle face formulas already
come from that upstream import.

The compatibility scope against Mathlib 4.35.0 (`56a005855ea17e0b0958f73ec801ae140b0a1679`) and
its removal conditions are recorded in `BACKPORTS.md`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial Opposite
open scoped Simplicial

namespace SSet

namespace stdSimplex

@[simp]
lemma objEquiv_symm_δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((objEquiv.{u}).symm (SimplexCategory.δ i) : Δ[n + 1] _⦋n⦌) j =
      i.succAbove j := rfl

@[simp]
lemma objEquiv_symm_σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ((objEquiv.{u}).symm (SimplexCategory.σ i) : Δ[n] _⦋n + 1⦌) j =
      i.predAbove j := rfl

@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_hom
    {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    yonedaEquiv (isoOfRepresentableBy h).hom = h.homEquiv (𝟙 ⦋m⦌) := rfl

end stdSimplex

lemma yonedaEquiv_symm_map {X : SSet.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : X.obj (op m)) :
    yonedaEquiv.symm (X.map f.op x) =
      stdSimplex.map f ≫ yonedaEquiv.symm x :=
  uliftYonedaEquiv_symm_map ..

lemma σ_zero_eq_yonedaEquiv_const {X : SSet.{u}} (x : X _⦋0⦌) :
    X.σ 0 x = yonedaEquiv (const x) :=
  yonedaEquiv.symm.injective
    (by simp [← stdSimplex.σ_comp_yonedaEquiv_symm, yonedaEquiv_symm_zero])

namespace Subcomplex

variable {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)

variable [Mono (yonedaEquiv.symm x)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If a simplex `x : X _⦋n⦌` is such that `yonedaEquiv.symm x : Δ[n] ⟶ X` is a
monomorphism, then `Subcomplex.ofSimplex x` is representable by `⦋n⦌`. -/
noncomputable def ofSimplexRepresentableBy :
    (Subcomplex.ofSimplex x : SSet).RepresentableBy ⦋n⦌ :=
  letI := (isIso_toOfSimplex_iff x).2 inferInstance
  let e := asIso (toOfSimplex x)
  { homEquiv {m} :=
      ((stdSimplex.objEquiv).symm.trans yonedaEquiv.symm).trans
        ((Iso.homCongr (α := Iso.refl (stdSimplex.obj m)) (β := e)).trans yonedaEquiv)
    homEquiv_comp {m m'} f g := by
      dsimp
      rw [Category.id_comp, Category.id_comp]
      rw [yonedaEquiv_symm_comp]
      erw [Equiv.apply_symm_apply]
      rw [yonedaEquiv_symm_comp]
      conv_rhs => erw [Equiv.apply_symm_apply]
      erw [NatTrans.naturality_apply]
      rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma ofSimplexRepresentableBy_id :
    dsimp% (ofSimplexRepresentableBy x).homEquiv (𝟙 ⦋n⦌) = x := by
  dsimp [ofSimplexRepresentableBy]
  rw [Category.id_comp, yonedaEquiv_symm_comp]
  erw [Equiv.apply_symm_apply]
  have h_obj : stdSimplex.objEquiv.symm (𝟙 ⦋n⦌) =
      yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := by
    apply stdSimplex.objEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact stdSimplex.objEquiv_yonedaEquiv_id.{u} n
  rw [h_obj]
  have h_app : (toOfSimplex x).app (op ⦋n⦌)
      (yonedaEquiv (𝟙 (Δ[n] : SSet.{u}))) = yonedaEquiv (toOfSimplex x) := by
    have h1 := yonedaEquiv_symm_app_id (yonedaEquiv (toOfSimplex x))
    have h2 : yonedaEquiv.symm (yonedaEquiv (toOfSimplex x)) = toOfSimplex x :=
      Equiv.symm_apply_apply _ _
    rw [h2] at h1
    exact h1
  rw [h_app]
  simp [yonedaEquiv_toOfSimplex]

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    yonedaEquiv ((stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι) = x := by
  rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_isoOfRepresentableBy_hom,
    Subfunctor.ι_app, TypeCat.ofHom_apply]
  simp

lemma isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    (stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι = yonedaEquiv.symm x :=
  yonedaEquiv.injective (by simp)

end Subcomplex

end SSet
