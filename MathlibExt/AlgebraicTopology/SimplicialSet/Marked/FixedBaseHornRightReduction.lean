/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCotensorLeibniz
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseHornCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverMonoRight
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.BoundaryCells

/-!
# Original fixed-base horn tests reduce to the full original mono family

The actual cotensor comparison transposes the supplied horn/source
squares. Right lifting against every original mono generator over every
whole base map is the genuine mono-right class in the same slice. Thus
the fixed-base small horn family tests every original marked mono, with
its original source, markings and complete base map unchanged.

This is a proved horn/mono reduction, not a uniform-rank theorem for all
weak marked monomorphisms.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The native mono generators retain exactly the original full mono-right class in the supplied maximally
  marked slice. -/
theorem fixedBaseMonoCells_rlp_iff {B : SSet.{u}} {E F : Over (max B)} (p : E ⟶ F) :
    (overCells monoCell.{u} (max B)).rlp p ↔ (monomorphisms (Over (max B))).rlp p :=
  (overCells_rlp_iff monoCell.{u} (max B) p).trans
    ((monoCells_rlp_iff p.left).trans (over_monomorphisms_rlp_iff p).symm)

/-- Every original mono lifts each fixed scalar horn corner when the supplied original marked right map
  passes the actual small horn family. -/
theorem fixedBaseHornRight_lifts_all_monos {B : SSet.{u}} {E F X X' : Over (max B)}
    (p : E ⟶ F)
    (hp : ∀ s : FixedBaseMonoIndex B × FixedBaseHornIndex, HasLiftingProperty (fixedBaseHornCell B s).hom p)
    (i : X ⟶ X') [Mono i] (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) k).ι i) p := by
  let q := overCotensorComparison (horn.{u} (n + 1) k).ι p
  have hq : (overCells monoCell.{u} (max B)).rlp q := by
    rintro A D f ⟨s⟩
    exact (overParameter_cotensor_lifting_iff _ (overCell monoCell.{u} (max B) s) p).mp (hp (s, ⟨n, k⟩))
  have hm : (monomorphisms (Over (max B))).rlp q := (fixedBaseMonoCells_rlp_iff q).mp hq
  exact (overParameter_cotensor_lifting_iff _ i p).mpr (hm i inferInstance)

/-- The whole original Cartesian fixed-base right class passes every actual marked mono/horn corner, not
  just the small chosen mono sources. -/
theorem cartesianFixedBaseRight_horn_lifting {B : SSet.{u}} {E F X X' : Over (max B)}
    (p : E ⟶ F) (hp : (cartesianFixedBaseCells B).rlp p) (i : X ⟶ X') [Mono i]
    (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) k).ι i) p := by
  apply fixedBaseHornRight_lifts_all_monos p ?_ i n k
  intro s
  exact hp _ (ofHoms.mk (f := fun t => (cartesianFixedBaseCell B t).hom) (Sum.inr s))

/-- The unchanged original dual small horn family has the same full mono/horn right reduction. -/
theorem cocartesianFixedBaseRight_horn_lifting {B : SSet.{u}} {E F X X' : Over (max B)}
    (p : E ⟶ F) (hp : (cocartesianFixedBaseCells B).rlp p) (i : X ⟶ X') [Mono i]
    (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) k).ι i) p := by
  apply fixedBaseHornRight_lifts_all_monos p ?_ i n k
  intro s
  exact hp _ (ofHoms.mk (f := fun t => (cocartesianFixedBaseCell B t).hom) (Sum.inr s))

end SSet.Marked
