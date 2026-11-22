/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalRowFibrations

/-!
# Relative row pullback-Homs for Segal spaces

A vertical Reedy fibration between Segal spaces has inner right row
pullback-Homs along every scalar monomorphism. The original source and
chosen pullback target are quasicategories. The proof keeps both original
pullback projections: actual unary left restrictions are trivial, their
relative pullback-Hom is a Kan fibration, and base change with two-out-of-three
makes it trivial. The exact box adjunction transposes its lifting squares.

Source: Joyal–Tierney, Proposition 3.10, arXiv math/0607820v2, p. 20.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace

private lemma trivialFibration_of_boundaryRLP {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.modelCategoryQuillen.I.rlp f) :
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    trivialFibrations SSet.{u} f := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hm : (monomorphisms SSet.{u}).rlp f := by
    rw [SSet.rlp_monomorphisms]
    exact hf
  change (cofibrations SSet.{u}).rlp f at hm
  rwa [cofibrations_rlp] at hm

private lemma relativeLeft_boundaryRLP
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hp : SimplicialSpace.ReedyModel.modelCategory.{u}.categoryWithFibrations.fibrations p)
    {A B : SSet.{u}} (a : A ⟶ B) [Mono a]
    (hX : SSet.modelCategoryQuillen.I.rlp
      ((SimplicialSpace.boxLeftDivisionFunctor.map a.op).app X))
    (hY : SSet.modelCategoryQuillen.I.rlp
      ((SimplicialSpace.boxLeftDivisionFunctor.map a.op).app Y)) :
    SSet.modelCategoryQuillen.I.rlp (SimplicialSpace.boxLeftPullbackHom a p) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let i := SimplicialSpace.discreteInnerMap a
  have hiMono : Mono i := by
    let _ : (SimplicialObject.const (Type u)).PreservesMonomorphisms := inferInstance
    let _ : Mono (SSet.simplicialSpaceDiscrete.map a) := by
      change Mono (((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) SSet.{u}).obj
        (SimplicialObject.const (Type u))).map a)
      infer_instance
    exact inferInstanceAs (Mono (SimplicialSpace.ofSimplicialObject.map
      (SSet.simplicialSpaceDiscrete.map a)))
  have hiCof : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((SimplicialSpace.ReedyModel.cofibration_iff i).2 hiMono)
  let q := SimplicialSpace.boxLeftPullbackHomSquare a p
  let sq : SimplicialSpace.innerHomFunctor.PullbackObjObj i p :=
    { pt := q.pt
      fst := q.fst
      snd := q.snd
      isPullback := q.isPullback
      π := q.π
      π_fst := q.π_fst
      π_snd := q.π_snd }
  have hqFib : fibrations SSet.{u} q.π :=
    SimplicialSpace.ReedyModel.inner_pullbackHom_fibration i p sq hiCof hp
  have hXTriv := trivialFibration_of_boundaryRLP _ hX
  have hYTriv := trivialFibration_of_boundaryRLP _ hY
  have hfstTriv : trivialFibrations SSet.{u} q.fst :=
    (trivialFibrations SSet.{u}).of_isPullback q.isPullback.flip hYTriv
  have hqWeak : weakEquivalences SSet.{u} q.π := by
    apply (weakEquivalences SSet.{u}).of_postcomp q.π q.fst hfstTriv.2
    rw [q.π_fst]
    exact hXTriv.2
  rw [← SSet.rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp q.π
  rw [cofibrations_rlp]
  exact ⟨hqFib, hqWeak⟩

section SegalInputs

variable {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
  (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    IsFibrant X)
  (hY : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
    IsFibrant Y)
  (hp : SimplicialSpace.ReedyModel.modelCategory.{u}.categoryWithFibrations.fibrations p)
  (hSpineX : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
    ((SimplicialSpace.boxLeftDivisionFunctor.map
      (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app X))
  (hSpineY : ∀ n : ℕ, 2 ≤ n → SSet.realizationWeakEquivalences
    ((SimplicialSpace.boxLeftDivisionFunctor.map
      (SSet.Rezk.spineSubcomplex.{u} n).ι.op).app Y))

include hX hY hp hSpineX hSpineY

/-- JT3.10's original source-left pullback-Hom is trivial for every inner-anodyne map. -/
theorem leftPullbackHom_boundaryRLP_of_innerAnodyne
    {A B : SSet.{u}} (a : A ⟶ B) (ha : SSet.innerAnodyneExtensions a) :
    SSet.modelCategoryQuillen.I.rlp (SimplicialSpace.boxLeftPullbackHom a p) := by
  have hle : SSet.anodyneExtensions.{u} ≤ monomorphisms SSet.{u} := by
    rw [SSet.anodyneExtensions_eq_llp_rlp, ← SSet.modelCategoryQuillen.llp_rlp_I,
      ← SSet.rlp_monomorphisms]
    exact antitone_llp (antitone_rlp SSet.modelCategoryQuillen.J_le_monomorphisms)
  let _ : Mono a := hle _ (SSet.innerAnodyneExtensions_le _ ha)
  exact relativeLeft_boundaryRLP p hp a
    (SimplicialSpace.leftRestriction_boundaryRLP_of_innerAnodyne X hX hSpineX a ha)
    (SimplicialSpace.leftRestriction_boundaryRLP_of_innerAnodyne Y hY hSpineY a ha)

/-- The original relative row arrow is inner; it retains the original right pullback. -/
theorem rowPullbackHom_inner {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.InnerFibration (SimplicialSpace.rowPullbackHom v p) := by
  constructor
  intro A B a ha
  have hinner : SSet.innerAnodyneExtensions a := le_llp_rlp _ _ ha
  have hI := leftPullbackHom_boundaryRLP_of_innerAnodyne
    p hX hY hp hSpineX hSpineY a hinner
  have hm : (monomorphisms SSet.{u}).rlp
      (SimplicialSpace.boxLeftPullbackHom a p) := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  exact (SimplicialSpace.box_hasLiftingProperty_iff a v p).2 (hm v inferInstance)

omit hp in
/-- The chosen relative row target is quasi because its first projection is a
base change of the actual target row restriction. -/
theorem rowPullbackHom_target_quasi {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.Quasicategory (SimplicialSpace.rowPullbackHomSquare v p).pt := by
  let q := SimplicialSpace.rowPullbackHomSquare v p
  let _ : SSet.InnerFibration (SimplicialSpace.rowRestriction v Y) :=
    SimplicialSpace.rowRestriction_inner_of_spines Y hY hSpineY v
  have hfst : SSet.innerFibrations q.fst :=
    SSet.innerFibrations.of_isPullback q.isPullback.flip SSet.InnerFibration.mem
  exact @SSet.quasicategory_of_innerFibration _ _ q.fst ⟨hfst⟩
    (SimplicialSpace.rowPower_quasi_of_spines X hX hSpineX S)

/-- Full native JT3.10 row packet, including source/target quasi and both
chosen pullback projection equations. -/
theorem rowPullbackHom_packet {S T : SSet.{u}} (v : S ⟶ T) [Mono v] :
    SSet.InnerFibration (SimplicialSpace.rowPullbackHom v p) ∧
    SSet.Quasicategory ((SimplicialSpace.rowPowerFunctor T).obj X) ∧
    SSet.Quasicategory (SimplicialSpace.rowPullbackHomSquare v p).pt ∧
    SimplicialSpace.rowPullbackHom v p ≫
        (SimplicialSpace.rowPullbackHomSquare v p).fst =
      SimplicialSpace.rowRestriction v X ∧
    SimplicialSpace.rowPullbackHom v p ≫
        (SimplicialSpace.rowPullbackHomSquare v p).snd =
      (SimplicialSpace.rowPowerFunctor T).map p :=
  ⟨rowPullbackHom_inner p hX hY hp hSpineX hSpineY v,
    SimplicialSpace.rowPower_quasi_of_spines X hX hSpineX T,
    rowPullbackHom_target_quasi p hX hY hSpineX hSpineY v,
    SimplicialSpace.rowPullbackHom_fst v p, SimplicialSpace.rowPullbackHom_snd v p⟩

end SegalInputs

end SimplicialSpace
