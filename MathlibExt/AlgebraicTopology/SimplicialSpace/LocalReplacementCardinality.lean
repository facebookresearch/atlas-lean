/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.PresheafIterationCardinality
public import MathlibExt.CategoryTheory.NatTrans.TerminalArrow
public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerators
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Presheaf

/-!
# Cardinal bounds for local simplicial-space replacements

For an eligible regular κ with a chosen ordinal bottom, the canonical terminal factorization by
the full auxiliary localizing family preserves the bound 2^ξ when ξ bounds κ, the generator
index set and both endpoint point counts, with ℵ₀ ≤ ξ. The count ranges over both simplicial
directions and retains the same κ-factorization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace SimplicialSpace

/-- The raw uncurried and canonical presheaf presentations have the same
total-point cardinality. -/
theorem mk_totalPoints_toPresheaf (X : SimplicialSpace.{u}) :
    Cardinal.mk (Functor.uncurry.obj X.diagram).Elements =
      Cardinal.mk (toPresheaf.obj X).Elements :=
  (totalPointsEquivToPresheaf X).cardinal_eq

/-- The SAME canonical terminal factorization at the SAME κ has its total-point bound.
The fixed profile is counted on the original full auxiliary family, including full E. -/
theorem canonical_localReplacement_mk_elements_le
    (κ ξ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (hξ : ℵ₀ ≤ ξ) (hκ : κ ≤ ξ)
    (hI :
      letI : MorphismProperty.IsSmall.{u} LocalGenerators.J.{u} :=
        SmallObject.isSmall LocalGenerators.J.{u} κ
      Cardinal.mk (Shrink.{u} LocalGenerators.J.{u}.toSet) ≤ ξ)
    (hA : ∀ i : LocalGenerators.J.{u}.toSet,
      Cardinal.mk (Functor.uncurry.obj i.1.left.diagram).Elements ≤ ξ)
    (hB : ∀ i : LocalGenerators.J.{u}.toSet,
      Cardinal.mk (Functor.uncurry.obj i.1.right.diagram).Elements ≤ ξ)
    (X : SimplicialSpace.{u})
    (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ 2 ^ ξ) :
    let t := terminal.fromNatTrans SimplicialSpace.{u}
    let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
    let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
    Cardinal.mk (Functor.uncurry.obj (r.Z.obj X).diagram).Elements ≤ 2 ^ ξ := by
  dsimp only
  let F := SimplicialSpace.toPresheaf.{u}
  have hcount (Y : SimplicialSpace.{u}) :
      Cardinal.mk (Functor.uncurry.obj Y.diagram).Elements =
        Cardinal.mk (F.obj Y).Elements := mk_totalPoints_toPresheaf Y
  change Cardinal.mk (Functor.uncurry.obj
    (SmallObject.obj LocalGenerators.J.{u} κ (terminal.from X)).diagram).Elements ≤ 2 ^ ξ
  rw [hcount]
  exact SmallObject.obj_terminal_mk_elements_le_of_presheaf_equivalence
    LocalGenerators.J.{u} κ F ξ hξ hκ hI
    (fun i => by rw [← hcount i.1.left]; exact hA i)
    (fun i => by rw [← hcount i.1.right]; exact hB i)
    X (by rw [← hcount X]; exact hX)

end SimplicialSpace
