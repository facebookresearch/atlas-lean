/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
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
# Standard-simplex coordinates and representable subcomplexes

For simplicial sets in universe `u`, the standard-simplex equivalence identifies cofaces and codegeneracies with the maps `succAbove` and `predAbove` on finite ordinals. Yoneda evaluation of a representing isomorphism at the identity gives its distinguished simplex. For an ordinal map `f : n ⟶ m` and `x : X.obj (op m)`,
`yonedaEquiv.symm (X.map f.op x) = stdSimplex.map f ≫ yonedaEquiv.symm x`.
The degeneracy of a vertex is the Yoneda image of its constant simplicial map.

If `x : X _⦋n⦌` defines a monomorphism `yonedaEquiv.symm x : Δ[n] ⟶ X`, the generated
subcomplex `Subcomplex.ofSimplex x` is representable by `⦋n⦌`. Its representing isomorphism is
induced by `Subcomplex.toOfSimplex x`; the identity represents `x`, and the isomorphism
followed by the subcomplex inclusion is `yonedaEquiv.symm x`.
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

/-- Let `X : SSet.{u}`, `n : ℕ`, and `x : X _⦋n⦌`. If the Yoneda map `yonedaEquiv.symm x : Δ[n] ⟶
X` is a monomorphism, then `Subcomplex.ofSimplex x` is represented by `⦋n⦌`. The
representation identifies its simplices naturally with ordinal maps into `⦋n⦌`, using the
isomorphism `Subcomplex.toOfSimplex x : Δ[n] ⟶ Subcomplex.ofSimplex x`. -/
noncomputable def ofSimplexRepresentableBy :
    (Subcomplex.ofSimplex x : SSet).RepresentableBy ⦋n⦌ :=
  letI := (isIso_toOfSimplex_iff x).2 inferInstance
  let e := asIso (toOfSimplex x)
  { homEquiv {m} :=
      ((stdSimplex.objEquiv).symm.trans yonedaEquiv.symm).trans
        ((Iso.homCongr (α := Iso.refl (stdSimplex.obj m)) (β := e)).trans yonedaEquiv)
    homEquiv_comp {m m'} f g := by
      have hcoord {a : SimplexCategory} (h : a ⟶ ⦋n⦌) :
          yonedaEquiv ((Iso.refl (stdSimplex.obj a)).homCongr e
            (yonedaEquiv.symm (stdSimplex.objEquiv.symm h))) =
              yonedaEquiv (stdSimplex.map h ≫ e.hom) := by
        have hz : yonedaEquiv.symm (stdSimplex.objEquiv.symm h) = stdSimplex.map h :=
          yonedaEquiv.injective ((Equiv.apply_symm_apply _ _).trans
            (yonedaEquiv_map h).symm)
        exact congrArg yonedaEquiv
          ((congrArg ((Iso.refl (stdSimplex.obj a)).homCongr e) hz).trans
            ((Iso.homCongr_apply (Iso.refl (stdSimplex.obj a)) e (stdSimplex.map h)).trans
              (Category.id_comp (stdSimplex.map h ≫ e.hom))))
      change yonedaEquiv ((Iso.refl (stdSimplex.obj m)).homCongr e
          (yonedaEquiv.symm (stdSimplex.objEquiv.symm (f ≫ g)))) =
        (ofSimplex x : SSet).map f.op
          (yonedaEquiv ((Iso.refl (stdSimplex.obj m')).homCongr e
            (yonedaEquiv.symm (stdSimplex.objEquiv.symm g))))
      calc
        _ = yonedaEquiv (stdSimplex.map (f ≫ g) ≫ e.hom) := hcoord (f ≫ g)
        _ = yonedaEquiv ((stdSimplex.map f ≫ stdSimplex.map g) ≫ e.hom) :=
          congrArg (fun h => yonedaEquiv (h ≫ e.hom)) (stdSimplex.map_comp f g)
        _ = yonedaEquiv (stdSimplex.map f ≫ (stdSimplex.map g ≫ e.hom)) :=
          congrArg yonedaEquiv (Category.assoc (stdSimplex.map f) (stdSimplex.map g) e.hom)
        _ = (ofSimplex x : SSet).map f.op
            (yonedaEquiv (stdSimplex.map g ≫ e.hom)) :=
          (yonedaEquiv_naturality f (stdSimplex.map g ≫ e.hom)).symm
        _ = _ := congrArg (fun z => (ofSimplex x : SSet).map f.op z) (hcoord g).symm }

@[simp]
lemma ofSimplexRepresentableBy_id :
    dsimp% (ofSimplexRepresentableBy x).homEquiv (𝟙 ⦋n⦌) = x := by
  letI : IsIso (toOfSimplex x) := (isIso_toOfSimplex_iff x).2 inferInstance
  let e : Δ[n] ≅ (ofSimplex x : SSet.{u}) := asIso (toOfSimplex x)
  have hunit : (Iso.refl (Δ[n] : SSet.{u})).homCongr e
      (yonedaEquiv.symm (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) = toOfSimplex x := by
    calc
      _ = (Iso.refl (Δ[n] : SSet.{u})).homCongr e (𝟙 Δ[n]) :=
        congrArg ((Iso.refl (Δ[n] : SSet.{u})).homCongr e)
          (yonedaEquiv_symm_stdSimplex_id.{u} ⦋n⦌)
      _ = (𝟙 Δ[n]) ≫ (𝟙 Δ[n]) ≫ e.hom :=
        Iso.homCongr_apply (Iso.refl (Δ[n] : SSet.{u})) e (𝟙 Δ[n])
      _ = e.hom := (Category.id_comp ((𝟙 Δ[n]) ≫ e.hom)).trans (Category.id_comp e.hom)
      _ = toOfSimplex x := rfl
  change ↑(yonedaEquiv ((Iso.refl (Δ[n] : SSet.{u})).homCongr e
    (yonedaEquiv.symm (stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))))) = x
  calc
    _ = ↑(yonedaEquiv (toOfSimplex x)) :=
      congrArg (fun h : Δ[n] ⟶ (ofSimplex x : SSet.{u}) => (yonedaEquiv h).val) hunit
    _ = x := congrArg Subtype.val (yonedaEquiv_toOfSimplex x)

@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    yonedaEquiv ((stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι) = x := by
  let h := ofSimplexRepresentableBy x
  calc
    _ = (ofSimplex x).ι.app (op ⦋n⦌)
        (yonedaEquiv (stdSimplex.isoOfRepresentableBy h).hom) :=
      yonedaEquiv_comp (stdSimplex.isoOfRepresentableBy h).hom (ofSimplex x).ι
    _ = (ofSimplex x).ι.app (op ⦋n⦌) (h.homEquiv (𝟙 ⦋n⦌)) :=
      congrArg (fun z => (ofSimplex x).ι.app (op ⦋n⦌) z)
        (stdSimplex.yonedaEquiv_isoOfRepresentableBy_hom h)
    _ = x := ofSimplexRepresentableBy_id x

lemma isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    (stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι = yonedaEquiv.symm x :=
  yonedaEquiv.injective ((yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom x).trans
    (Equiv.apply_symm_apply yonedaEquiv x).symm)

end Subcomplex

end SSet
