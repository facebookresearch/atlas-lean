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

-- BACKPORT: closely adapted from Mathlib PR #42435, head
-- e09070f786c9fc0a688e6239d71230b618b045ff, StdSimplex.lean blob
-- 01377b85904978d402c830501e4615606021df8c. See BACKPORTS.md for the ledger entry.
-- The current pin is Mathlib v4.36.0 at fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
-- Eight local declarations remain: the two objEquiv coface/codegeneracy coordinate laws,
-- representable-isomorphism Yoneda evaluation, the constant-vertex degeneracy law,
-- ofSimplexRepresentableBy and its three identity/inclusion laws.
-- The five Edge/CompStruct face equations are supplied by the pin. The redundant local
-- yonedaEquiv_symm_map is replaced by yonedaEquiv_symm_naturality_left.
-- Representability uses the native equivUliftYonedaIso applied to asIso (toOfSimplex x).
-- Remove this module only after the pin supplies these surviving interfaces, or all concrete
-- consumers have migrated to compatible native interfaces. No generated import root is used.

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Standard-simplex coordinates and representable subcomplexes

For simplicial sets in universe `u`, the standard-simplex equivalence identifies cofaces and
  codegeneracies with the maps `succAbove` and `predAbove` on finite ordinals. Yoneda evaluation
  of a representing isomorphism at the identity gives its distinguished simplex. For an ordinal
  map `f : n ⟶ m` and `x : X.obj (op m)`,
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

/-- The n-simplex representing coface i has coordinate j equal to i.succAbove j. -/
@[simp]
lemma objEquiv_symm_δ_apply {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((objEquiv.{u}).symm (SimplexCategory.δ i) : Δ[n + 1] _⦋n⦌) j =
      i.succAbove j := rfl

/-- The (n+1)-simplex representing codegeneracy i has coordinate j equal to i.predAbove j. -/
@[simp]
lemma objEquiv_symm_σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    ((objEquiv.{u}).symm (SimplexCategory.σ i) : Δ[n] _⦋n + 1⦌) j =
      i.predAbove j := rfl

/-- Yoneda evaluation of a representing isomorphism is the image of the identity under its
hom equivalence. -/
@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_hom
    {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    yonedaEquiv (isoOfRepresentableBy h).hom = h.homEquiv (𝟙 ⦋m⦌) := rfl

end stdSimplex

/-- The degeneracy of a vertex is the Yoneda image of its constant edge. -/
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
  (Functor.RepresentableBy.equivUliftYonedaIso (ofSimplex x : SSet) ⦋n⦌).symm
    (asIso (toOfSimplex x))

/-- The identity ordinal map represents the original simplex x in its generated subcomplex. -/
@[simp]
lemma ofSimplexRepresentableBy_id :
    dsimp% (ofSimplexRepresentableBy x).homEquiv (𝟙 ⦋n⦌) = x := by
  letI : IsIso (toOfSimplex x) := (isIso_toOfSimplex_iff x).2 inferInstance
  change (yonedaEquiv (toOfSimplex x)).val = x
  exact congrArg Subtype.val (yonedaEquiv_toOfSimplex x)

/-- The representing isomorphism followed by the subcomplex inclusion evaluates to x. -/
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

/-- The representing isomorphism followed by the subcomplex inclusion is the Yoneda map of x. -/
lemma isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    (stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι = yonedaEquiv.symm x :=
  yonedaEquiv.injective ((yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom x).trans
    (Equiv.apply_symm_apply yonedaEquiv x).symm)

end Subcomplex

end SSet
