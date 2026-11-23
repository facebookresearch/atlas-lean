/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

-- BACKPORT: Extracted from PR leanprover-community/mathlib4#42435 head
-- `e09070f786c9fc0a688e6239d71230b618b045ff`, file
-- `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`,
-- blob `01377b85904978d402c830501e4615606021df8c`. Copied surface:
-- `SSet.stdSimplex.objEquiv_symm_δ_apply`,
-- `SSet.stdSimplex.objEquiv_symm_σ_apply`,
-- `SSet.yonedaEquiv_symm_map` (upstream in `SSet`, listed in contract as
-- `stdSimplex.yonedaEquiv_symm_map`),
-- `SSet.stdSimplex.yonedaEquiv_isoOfRepresentableBy_hom`,
-- `SSet.σ_zero_eq_yonedaEquiv_const`,
-- `SSet.Subcomplex.ofSimplexRepresentableBy`,
-- `SSet.Subcomplex.ofSimplexRepresentableBy_id`,
-- `SSet.Subcomplex.yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom`,
-- `SSet.Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom`,
-- `SSet.Edge.δ_zero_yonedaEquiv_symm`,
-- `SSet.Edge.δ_one_yonedaEquiv_symm`,
-- `SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm`,
-- `SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm`,
-- `SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm`.
-- Adaptations for pinned Mathlib v4.33.0 (`db584cd`): minimal import
-- `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex` which already provides
-- `stdSimplex.objEquiv`, `yonedaEquiv`, `Subcomplex.toOfSimplex`,
-- `isIso_toOfSimplex_iff`, `isoOfRepresentableBy`, `Edge`, `CompStruct`,
-- `stdSimplex.δ_comp_yonedaEquiv_symm`; proof of
-- `ofSimplexRepresentableBy_id` uses pinned `toOfSimplex`,
-- `yonedaEquiv_toOfSimplex`, `objEquiv_yonedaEquiv_id`, and
-- `yonedaEquiv_symm_app_id` to replace missing
-- `toOfSimplex_app_objEquiv_symm`; lemma `σ_zero_eq_yonedaEquiv_const`
-- uses existing `σ_comp_yonedaEquiv_symm` and `yonedaEquiv_symm_zero`;
-- the five `Edge`/`CompStruct` face lemmas use the pinned
-- `δ_comp_yonedaEquiv_symm`; otherwise proofs preserved verbatim.
-- Removal rule: delete this file and switch any imports to
-- `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex` once pinned Mathlib
-- contains all fourteen declarations at canonical path; regenerate
-- `MathlibExt.lean` in separate Avocado task; remove corresponding
-- `BACKPORTS.md` row only in that separate task.

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Standard simplex compatibility backport for Lean 4.33

This file backports from PR #42435 head `e09070f786c9fc0a688e6239d71230b618b045ff`,
file `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`,
blob `01377b85904978d402c830501e4615606021df8c`, upstream author Joël Riou
(copyright header preserved from upstream source), the fourteen declarations
required by `ProdStdSimplexOneCompat` and the
`KanComplex/FundamentalGroupoid` leaf (narrow closure plus five-lemma
provider extension for horn-face discharge):

* `SSet.stdSimplex.objEquiv_symm_δ_apply`
* `SSet.stdSimplex.objEquiv_symm_σ_apply`
* `SSet.yonedaEquiv_symm_map` (upstream in `SSet`, contract lists as
  `stdSimplex.yonedaEquiv_symm_map`)
* `SSet.stdSimplex.yonedaEquiv_isoOfRepresentableBy_hom`
* `SSet.σ_zero_eq_yonedaEquiv_const`
* `SSet.Subcomplex.ofSimplexRepresentableBy`
* `SSet.Subcomplex.ofSimplexRepresentableBy_id`
* `SSet.Subcomplex.yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom`
* `SSet.Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom`
* `SSet.Edge.δ_zero_yonedaEquiv_symm`
* `SSet.Edge.δ_one_yonedaEquiv_symm`
* `SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm`
* `SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm`
* `SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm`

## Source

* PR: leanprover-community/mathlib4#42435
* PR head: `e09070f786c9fc0a688e6239d71230b618b045ff`
* File: `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`
* Blob: `01377b85904978d402c830501e4615606021df8c`
* Upstream author: Joël Riou

## Adaptations for 4.33 pin

* Minimal import `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex` for
  all pre-existing declarations (`objEquiv`, `yonedaEquiv`,
  `toOfSimplex`, `isIso_toOfSimplex_iff`, `isoOfRepresentableBy`,
  `Edge`, `CompStruct`, `δ_comp_yonedaEquiv_symm`, etc.).
* `yonedaEquiv_symm_map`: proof `uliftYonedaEquiv_symm_map ..` preserved; API
  exists on pin via `Mathlib.CategoryTheory.Yoneda`.
* `σ_zero_eq_yonedaEquiv_const`: proof preserved verbatim using existing
  `stdSimplex.σ_comp_yonedaEquiv_symm` and `yonedaEquiv_symm_zero` from
  pinned v4.33.0.
* `ofSimplexRepresentableBy_id`: original proof used
  `toOfSimplex_app_objEquiv_symm` which is absent from pinned v4.33.0
  `StdSimplex.lean`; replaced with robust proof using pinned
  `toOfSimplex`, `yonedaEquiv_toOfSimplex`, `objEquiv_yonedaEquiv_id`,
  and `yonedaEquiv_symm_app_id` to unfold `RepresentableBy.homEquiv`
  and identify `(toOfSimplex x).app _ (objEquiv.symm 𝟙)` with
  `yonedaEquiv (toOfSimplex x)` via Yoneda evaluation at
  `yonedaEquiv 𝟙 = objEquiv.symm 𝟙`.
* `Edge.δ_zero_yonedaEquiv_symm`, `Edge.δ_one_yonedaEquiv_symm`,
  `Edge.CompStruct.δ_zero_yonedaEquiv_symm`,
  `Edge.CompStruct.δ_one_yonedaEquiv_symm`,
  `Edge.CompStruct.δ_two_yonedaEquiv_symm`: proofs preserved verbatim
  as `by simp [stdSimplex.δ_comp_yonedaEquiv_symm]`; attribute
  `@[reassoc (attr := simp)]` preserved exactly as upstream.
* Preserves upstream namespaces (`SSet`, `SSet.stdSimplex`, `SSet.Subcomplex`,
  `SSet.Edge`, `SSet.Edge.CompStruct`),
  universes `u`, attributes (`@[simp]`, `@[reassoc (attr := simp)]` where
  upstream), and mathematical content verbatim where elaborated on 4.33 pin.

## Removal rule

Delete `MathlibExt/AlgebraicTopology/SimplicialSet/StdSimplexCompat.lean` and
replace any imports of it with `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex`
once pinned Mathlib provides the fourteen declarations listed above at canonical
path. Do not retain local copies colliding with upstream. Regenerate
`MathlibExt.lean` in separate Avocado task.
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
