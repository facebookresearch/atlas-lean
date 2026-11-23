/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupProduct
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! # Binary-product closure of `KanComplex.W`

From `W f` and `W g`, derive `W (CategoryTheory.Limits.prod.map f g)` by
decomposing `W.mk` into (1) Kan/product fibrancy, proved here by pulling
the second factor's terminal fibration back along `prod.fst` and composing
with the first factor's (all stated via `J.rlp`, per the local convention);
(2) equivalence of the mapped fundamental groupoid, via provider theorem
`SSet.isEquivalence_mapFundamentalGroupoid_prodMap`; and (3) bijectivity of
every pointed homotopy-group map.

Canonical product decompositions:
- groupoid comparison and its `prod.map` naturality iso live in
  `FundamentalGroupoidProduct` (consumed here only through
  `SSet.isEquivalence_mapFundamentalGroupoid_prodMap`);
- `SSet.KanComplex.piProdComparison n x`: the function
  `π n (X ⨯ A) x → π n X _ × π n A _` induced by `π.map prod.fst` /
  `π.map prod.snd` (imported from `HomotopyGroupProduct`, no seam).
Transport through the factor maps for the `π` side is
`SSet.KanComplex.piProdComparison_prodMap` (intertwining equality for the
`π` comparison, imported from `HomotopyGroupProduct`); product bijectivity
is proved formally here (`bijective_prodMap`).

Assumption inventory (no private axiom in this file, no transitive seam):
the groupoid step is `SSet.isEquivalence_mapFundamentalGroupoid_prodMap`
from `FundamentalGroupoidProduct`, whose former private
`ax_faithful_prodComparison` is deleted in the provider with no replacement.

The former pointed-`π` seam `ax_bijective_piProdComparison` is deleted: the
static comparison bijectivity is now `SSet.KanComplex.bijective_piProdComparison`
from `HomotopyGroupProduct`, consumed in `bijective_piMap_prodMap`.

Seam delta vs base `d62db6ce20c2e99eedaaf111c1e2b7e182b7f397`: this file no
longer declares any private axiom; the former local groupoid comparison,
its axiom, and its transport/equivalence proofs are deleted in favour of the
provider theorem above.

Explicit nonclaims: no `ModelCategory SSet` instance is used or constructed;
no public axiom is added.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial Limits MorphismProperty
open SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

/-- Product of Kan complexes is Kan: `prod.fst` is a `J.rlp` map as the
pullback of the second factor's terminal map, so the product's terminal map,
a composite of `J.rlp` maps, is again `J.rlp`. Stated via `J.rlp` explicitly,
following the local `Fiber.lean` convention, because `fibrations SSet` is not
syntactically a `rlp` for typeclass search. -/
private lemma kanComplex_prod {X A : SSet.{u}} (hX : KanComplex X)
    (hA : KanComplex A) : KanComplex (X ⨯ A) := by
  have hX' : J.rlp (terminal.from X) := (fibration_iff _).mp hX
  have hA' : J.rlp (terminal.from A) := (fibration_iff _).mp hA
  have hPull : IsPullback (Limits.prod.snd : X ⨯ A ⟶ A)
      (Limits.prod.fst : X ⨯ A ⟶ X) (terminal.from A) (terminal.from X) :=
    (IsPullback.of_isLimit_binaryFan_of_isTerminal (limit.isLimit (pair X A))
      terminalIsTerminal).flip
  have hfst : J.rlp (Limits.prod.fst : X ⨯ A ⟶ X) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := J.rlp) hPull hA'
  have heq : terminal.from (X ⨯ A) =
      (Limits.prod.fst : X ⨯ A ⟶ X) ≫ terminal.from X := Subsingleton.elim _ _
  have hcomp : J.rlp (terminal.from (X ⨯ A)) := by
    rw [heq]
    exact comp_mem J.rlp _ _ hfst hX'
  exact (fibration_iff _).mpr hcomp

/-- The existing native product Kan proof, available to maps over a
product projection as well as to product maps. No new global instance. -/
theorem prod_kanComplex (X A : SSet.{u}) [KanComplex X] [KanComplex A] :
    KanComplex (X ⨯ A) :=
  kanComplex_prod inferInstance inferInstance

/-- Vertex-level first projection of `prod.map`: formal consequence of
`prod.map_fst` (no unfolding of limits, no seam). -/
private theorem prodMap_fst_app {X Y A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (x : (X ⨯ A) _⦋0⦌) :
    (Limits.prod.fst : Y ⨯ B ⟶ Y).app _ ((Limits.prod.map f g).app _ x) =
      f.app _ ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x) :=
  congrArg (·.app _ x) (Limits.prod.map_fst f g)

/-- Vertex-level second projection of `prod.map`: formal consequence of
`prod.map_snd` (no unfolding of limits, no seam). -/
private theorem prodMap_snd_app {X Y A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (x : (X ⨯ A) _⦋0⦌) :
    (Limits.prod.snd : Y ⨯ B ⟶ B).app _ ((Limits.prod.map f g).app _ x) =
      g.app _ ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x) :=
  congrArg (·.app _ x) (Limits.prod.map_snd f g)

/-- Product of two bijective maps is bijective. Proved formally (no seam). -/
private theorem bijective_prodMap {α β γ δ : Type*}
    (f : α → β) (g : γ → δ)
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (Prod.map f g) := by
  constructor
  · intro a b hab
    obtain ⟨ha, hb⟩ := Prod.mk.inj hab
    exact Prod.ext (hf.1 ha) (hg.1 hb)
  · intro p
    obtain ⟨a, ha⟩ := hf.2 p.1
    obtain ⟨b, hb⟩ := hg.2 p.2
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- Transport of `π.map` bijectivity across a basepoint equality. Proved formally
by substitution plus proof irrelevance (no seam). -/
private theorem bijective_piMap_of_basepoint_eq {X Y : SSet.{u}} {f : X ⟶ Y}
    {x : X _⦋0⦌} {y1 y2 : Y _⦋0⦌} (e : y1 = y2)
    (h1 : f.app _ x = y1) (h2 : f.app _ x = y2) (n : ℕ)
    (h : Function.Bijective (KanComplex.π.map f h1 (n := n))) :
    Function.Bijective (KanComplex.π.map f h2 (n := n)) := by
  subst e
  exact h

/-- Former broad seam, now a proved theorem: the pointed homotopy-group map
of a product of weak-equivalence maps is bijective. Derived from the provider
static comparison (`SSet.KanComplex.bijective_piProdComparison`) plus formal
transport (no new seam). -/
private theorem bijective_piMap_prodMap
    {X Y A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (hBijF : ∀ (n : ℕ) (x : X _⦋0⦌),
      Function.Bijective (KanComplex.π.map f rfl (n := n) (x := x)))
    (hBijG : ∀ (n : ℕ) (a : A _⦋0⦌),
      Function.Bijective (KanComplex.π.map g rfl (n := n) (x := a)))
    (n : ℕ) (x : (X ⨯ A) _⦋0⦌) :
    Function.Bijective (KanComplex.π.map
      (CategoryTheory.Limits.prod.map f g) rfl (n := n) (x := x)) := by
  have hFst : Function.Bijective (KanComplex.π.map f
      ((prodMap_fst_app (f := f) (g := g) x).symm) (n := n)) :=
    bijective_piMap_of_basepoint_eq ((prodMap_fst_app (f := f) (g := g) x).symm)
      _ _ n (hBijF n ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x))
  have hSnd : Function.Bijective (KanComplex.π.map g
      ((prodMap_snd_app (f := f) (g := g) x).symm) (n := n)) :=
    bijective_piMap_of_basepoint_eq ((prodMap_snd_app (f := f) (g := g) x).symm)
      _ _ n (hBijG n ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x))
  have hP : Function.Bijective
      (Prod.map
        (KanComplex.π.map f ((prodMap_fst_app (f := f) (g := g) x).symm) (n := n))
        (KanComplex.π.map g ((prodMap_snd_app (f := f) (g := g) x).symm) (n := n))) :=
    bijective_prodMap _ _ hFst hSnd
  have hCX : Function.Bijective (piProdComparison (X := X) (A := A) n x) :=
    SSet.KanComplex.bijective_piProdComparison n x
  have hCY : Function.Bijective
      (piProdComparison n ((Limits.prod.map f g).app _ x)) :=
    SSet.KanComplex.bijective_piProdComparison n _
  have hFun : (piProdComparison n ((Limits.prod.map f g).app _ x) ∘
      KanComplex.π.map (Limits.prod.map f g) rfl (n := n)) =
      Prod.map
          (KanComplex.π.map f ((prodMap_fst_app (f := f) (g := g) x).symm) (n := n))
          (KanComplex.π.map g ((prodMap_snd_app (f := f) (g := g) x).symm) (n := n)) ∘
        piProdComparison (X := X) (A := A) n x :=
    funext (piProdComparison_prodMap (f := f) (g := g) n x)
  have hComp : Function.Bijective
      (piProdComparison n ((Limits.prod.map f g).app _ x) ∘
        KanComplex.π.map (Limits.prod.map f g) rfl (n := n)) := by
    rw [hFun]
    exact hP.comp hCX
  exact (Function.Bijective.of_comp_iff' hCY
    (KanComplex.π.map (Limits.prod.map f g) rfl (n := n))).mp hComp

/-- Binary-product closure of `KanComplex.W`: from `W f` and `W g`, the product
map `Limits.prod.map f g` lies in `W`.

Hypotheses: `hf : W f` and `hg : W g`, universe-polymorphic in `u`.
Conclusion: `W (Limits.prod.map f g)` via `W.mk`. The Kan-source/target
components are proved here; the groupoid-equivalence component is provider
`SSet.isEquivalence_mapFundamentalGroupoid_prodMap` (former transitive seam
`ax_faithful_prodComparison`, now deleted in the provider) and the pointed-`π`
bijectivity component from the provider comparison. Uses no `ModelCategory SSet`
instance. -/
theorem W.prodMap {X Y A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (hf : W f) (hg : W g) : W (CategoryTheory.Limits.prod.map f g) :=
  W.mk _ (kanComplex_prod hf.kanComplex_source hg.kanComplex_source)
    (kanComplex_prod hf.kanComplex_target hg.kanComplex_target)
    (SSet.isEquivalence_mapFundamentalGroupoid_prodMap
      hf.isEquivalence_mapFundamentalGroupoid
      hg.isEquivalence_mapFundamentalGroupoid)
    (fun n x => bijective_piMap_prodMap (fun n x => hf.bijective_piMap n x)
      (fun n a => hg.bijective_piMap n a) n x)

end KanComplex

end SSet
