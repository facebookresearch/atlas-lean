/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryIterationCountability
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectOriginalFibrantReplacement
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerCountableCodiscreteResolution

/-!
# Countable full Homs of the SAME original native horn replacement

The entire original horn attachment family and both whole top/bottom
map sets are countable. Their actual coproduct pushouts and countable
native iteration retain every original full Hom simplex. Consequently
the SAME original horn replacement into the literal unit-Hom target
preserves countability, without any weak-terminal-map premise.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject
open scoped Simplicial
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects
variable {O : Type u} [Countable O]

/-- The SAME actual original horn arrow subset, with every ordered pair and horn position, is countable. -/
instance hornFamily_countable : Countable (hornFamily O).toSet := by
  let φ (i : Σ n : ℕ, O × O × Fin (n + 2)) : (hornFamily O).toSet :=
    ⟨Arrow.mk ((FreeSingleHom.functor i.2.1 i.2.2.1).map (Λ[i.1 + 1, i.2.2.2]).ι), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨A, B, f⟩, hf⟩
    obtain ⟨i⟩ := hf
    exact ⟨i, rfl⟩
  exact hφ.countable

/-- Each SAME original free horn source retains countable entire original path Homs. -/
instance hornFamily_source_countable (i : (hornFamily O).toSet) : CountableHoms i.val.left := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨n, x, y, k⟩⟩ := hf
  exact inferInstanceAs (CountableHoms (FreeSingleHom.object x y (Λ[n + 1, k] : SSet.{u})))

/-- Each SAME original free horn target retains all countable full path Homs. -/
instance hornFamily_target_countable (i : (hornFamily O).toSet) : CountableHoms i.val.right := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨n, x, y, k⟩⟩ := hf
  exact inferInstanceAs (CountableHoms (FreeSingleHom.object x y (Δ[n + 1] : SSet.{u})))

/-- All whole original top maps from a native free horn source are countable. -/
instance hornFamily_top_maps_countable (C : FixedObjects O) [CountableHoms C]
    (i : (hornFamily O).toSet) : Countable (i.val.left ⟶ C) := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨n, x, y, k⟩⟩ := hf
  exact FreeSingleHom.countable_horn_maps x y C n k

/-- All whole original bottom maps from a native free simplex target are countable. -/
instance hornFamily_bottom_maps_countable (D : FixedObjects O) [CountableHoms D]
    (i : (hornFamily O).toSet) : Countable (i.val.right ⟶ D) := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨n, x, y, k⟩⟩ := hf
  exact FreeSingleHom.countable_simplex_maps x y D (n + 1)

/-- The SAME original full horn successor retains countable full Homs from its actual countable attachment squares. -/
instance hornSuccessor_countableHoms {C D : FixedObjects O} [CountableHoms C] [CountableHoms D]
    (p : C ⟶ D) : CountableHoms (functorObj (hornFamily O).homFamily p) := by
  infer_instance

private theorem countable_hornIterationIndex : Countable Cardinal.aleph0.{u}.ord.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  simp only [Cardinal.mk_toType, Cardinal.card_ord]
  exact le_rfl

/-- Every SAME actual original horn iteration stage retains countable full Homs on its original labels. -/
theorem hornIteration_countableHoms {C D : FixedObjects O} [CountableHoms C] [CountableHoms D]
    (p : C ⟶ D) (j : Cardinal.aleph0.{u}.ord.ToType) :
    CountableHoms ((FreeFactorization.hornCells p).F.obj j) := by
  let _ : Countable Cardinal.aleph0.{u}.ord.ToType := countable_hornIterationIndex
  have : CountableHoms (Arrow.mk p).right := inferInstanceAs (CountableHoms D)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact countableHoms_of_iso (FreeFactorization.hornCells p).isoBot
  | succ j _ hj =>
    have : CountableHoms (((iterationFunctor (hornFamily O) Cardinal.aleph0.{u}).obj j).obj
        (Arrow.mk p)).left := hj
    have : CountableHoms (((iterationFunctor (hornFamily O) Cardinal.aleph0.{u}).obj j).obj
        (Arrow.mk p)).right :=
      countableHoms_of_iso (iterationFunctorObjObjRightIso (hornFamily O)
        Cardinal.aleph0.{u} (Arrow.mk p) j)
    exact countableHoms_of_iso (relativeCellComplexιObjFObjSuccIso (hornFamily O)
      Cardinal.aleph0.{u} p j)
  | isSuccLimit j hj ih =>
    have (k : Set.Iio j) : CountableHoms
        (((Set.principalSegIio j).monotone.functor ⋙ (FreeFactorization.hornCells p).F).obj k) :=
      ih k.val k.property
    exact countableHoms_of_isColimit
      ((FreeFactorization.hornCells p).F.isColimitOfIsWellOrderContinuous j hj)

/-- The actual stored original full horn-factorization object retains countable entire Hom simplices. -/
instance hornFactorization_countableHoms {C D : FixedObjects O} [CountableHoms C] [CountableHoms D]
    (p : C ⟶ D) : CountableHoms (FreeFactorization.horn p).Z := by
  let _ : Countable Cardinal.aleph0.{u}.ord.ToType := countable_hornIterationIndex
  have (j : Cardinal.aleph0.{u}.ord.ToType) :
      CountableHoms ((FreeFactorization.hornCells p).F.obj j) := hornIteration_countableHoms p j
  exact countableHoms_of_isColimit (FreeFactorization.hornCells p).isColimit

/-- The SAME original full horn replacement into the literal unit-Hom target preserves countability. -/
instance originalFibrantReplacement_countableHoms (C : FixedObjects O) [CountableHoms C] :
    CountableHoms ((OriginalFibrantReplacement.functor O).obj C) :=
  hornFactorization_countableHoms (CodiscreteTerminal.toTerminal C)

end CategoryTheory.SimplicialEnrichment.FixedObjects
