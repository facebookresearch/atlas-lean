/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementInvariantSuccessor
import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion

/-!
# Bounded invariant closure for the canonical local replacement

Starting with one bounded original subpresheaf of a simplicial space, iterate
the exact bounded successor construction along `μ.ord.ToType`. Every stage is
the literal union of the prescribed input with all strictly earlier successor
seeds. The final union is the same μ-filtered colimit, so accessibility of the
canonical replacement and cocontinuity of the inner one-simplex tensor let each
final cylinder point descend to one stage.

The stored successor factorizations then give range containment in the final
replacement inclusion. Factoring through that monomorphism produces a single
whole restricted deformation with the exact original inclusion equation.
-/

set_option autoImplicit false
noncomputable section
universe u
open Cardinal CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SimplicialSpace

variable {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]

variable (e : LocalReplacementCardinalEnvelope κ) (Y : SimplicialSpace.{u})
  (H : innerOneSimplexPrecylinder.I.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y) ⟶
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y)
  (U : Subfunctor (toPresheaf.obj Y))
  (hU : Cardinal.mk U.toFunctor.Elements ≤ e.γ)

/-- A bounded original subpresheaf closed under a supplied whole deformation on
its canonical local replacement. -/
structure LocalReplacementInvariantSubpresheaf where
  /-- The invariant original subpresheaf. -/
  V : Subfunctor (toPresheaf.obj Y)
  /-- The prescribed input subpresheaf is literally contained in `V`. -/
  le : U ≤ V
  /-- Native total points of `V` remain within the stable envelope. -/
  points_le : Cardinal.mk V.toFunctor.Elements ≤ e.γ
  /-- Raw original total points of the realized `V` remain bounded. -/
  raw_points_le : Cardinal.mk
    (Functor.uncurry.obj (originalSubpresheafObject V).diagram).Elements ≤ e.γ
  /-- The supplied whole deformation restricts to the replacement of `V`. -/
  restrictedHomotopy : innerOneSimplexPrecylinder.I.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
        (originalSubpresheafObject V)) ⟶
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
      (originalSubpresheafObject V)
  /-- Inclusion of the restriction into `Q(Y)` recovers the supplied map. -/
  fac : innerOneSimplexPrecylinder.I.map
        ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
          (originalSubpresheafInclusion V)) ≫ H =
      restrictedHomotopy ≫
        (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
          (originalSubpresheafInclusion V)

namespace LocalReplacementInvariantClosure

private abbrev J := e.μ.ord.ToType

/-- One recursive output retains both the bounded input stage and the exact
successor packet chosen for that stage. -/
private structure StepPacket where
  V : Subfunctor (toPresheaf.obj Y)
  V_points_le : Cardinal.mk V.toFunctor.Elements ≤ e.γ
  successor : LocalReplacementDeformationSuccessor e Y H V

include hU in
private noncomputable def packetStep (j : J e)
    (previous : ∀ k : J e, k < j → StepPacket e Y H) : StepPacket e Y H := by
  let V : Subfunctor (toPresheaf.obj Y) :=
    U ⊔ ⨆ k : Set.Iio j, (previous k.1 k.2).successor.W
  have hindex : Cardinal.mk (Set.Iio j) ≤ e.γ :=
    (Cardinal.mk_subtype_le (fun k : J e => k < j)).trans e.μ_ord_le_γ
  have hseeds : Cardinal.mk
      (⨆ k : Set.Iio j, (previous k.1 k.2).successor.W).toFunctor.Elements ≤ e.γ := by
    apply Subfunctor.mk_elements_iSup_le_of_le
      (fun k : Set.Iio j => (previous k.1 k.2).successor.W)
      e.aleph0_le_γ hindex
    intro k
    exact (previous k.1 k.2).successor.points_le
  have hV : Cardinal.mk V.toFunctor.Elements ≤ e.γ := by
    apply Subfunctor.mk_elements_sup_le_of_le U
      (⨆ k : Set.Iio j, (previous k.1 k.2).successor.W)
      e.aleph0_le_γ hU hseeds
  let D := Classical.choice (e.exists_deformationSuccessor Y H V hV)
  exact { V := V, V_points_le := hV, successor := D }

include hU in
private noncomputable def packet : J e → StepPacket e Y H :=
  wellFounded_lt.fix (packetStep (e := e) (Y := Y) (H := H) (U := U)
    (hU := hU))

private noncomputable def seed (j : J e) : Subfunctor (toPresheaf.obj Y) :=
  (packet (e := e) (Y := Y) (H := H) (U := U) hU j).successor.W

private noncomputable def stage (j : J e) : Subfunctor (toPresheaf.obj Y) :=
  Subfunctor.strictPrefixUnion U (seed (e := e) (Y := Y) (H := H) (U := U) hU) j

/-- The recursive packet is genuinely attached to the same literal strict-prefix stage. -/
private theorem packet_stage (j : J e) :
    (packet (e := e) (Y := Y) (H := H) (U := U) hU j).V =
      stage (e := e) (Y := Y) (H := H) (U := U) hU j := by
  rw [packet, WellFounded.fix_eq]
  rfl

/-- The exact successor data, transported only along the literal stage equality. -/
private noncomputable def stageSuccessor (j : J e) :
    LocalReplacementDeformationSuccessor e Y H
      (stage (e := e) (Y := Y) (H := H) (U := U) hU j) := by
  exact (packet_stage (e := e) (Y := Y) (H := H) (U := U) hU j) ▸
    (packet (e := e) (Y := Y) (H := H) (U := U) hU j).successor

private theorem transportedSuccessor_W
    {V W : Subfunctor (toPresheaf.obj Y)} (h : V = W)
    (D : LocalReplacementDeformationSuccessor e Y H V) :
    ((h ▸ D : LocalReplacementDeformationSuccessor e Y H W).W) = D.W := by
  cases h
  rfl

private theorem stage_points_le (j : J e) :
    Cardinal.mk
      (stage (e := e) (Y := Y) (H := H) (U := U) hU j).toFunctor.Elements ≤ e.γ := by
  rw [← packet_stage (e := e) (Y := Y) (H := H) (U := U) hU j]
  exact (packet (e := e) (Y := Y) (H := H) (U := U) hU j).V_points_le

private theorem seed_eq_successor_W (j : J e) :
    seed (e := e) (Y := Y) (H := H) (U := U) hU j =
      (stageSuccessor (e := e) (Y := Y) (H := H) (U := U) hU j).W := by
  unfold seed stageSuccessor
  exact (transportedSuccessor_W (e := e) (Y := Y) (H := H)
    (packet_stage (e := e) (Y := Y) (H := H) (U := U) hU j)
    (packet (e := e) (Y := Y) (H := H) (U := U) hU j).successor).symm

private theorem stage_mono : Monotone
    (stage (e := e) (Y := Y) (H := H) (U := U) hU) :=
  Subfunctor.strictPrefixUnion_mono U
    (seed (e := e) (Y := Y) (H := H) (U := U) hU)

private theorem stage_limit (j : J e) (hj : Order.IsSuccLimit j) :
    stage (e := e) (Y := Y) (H := H) (U := U) hU j =
      ⨆ k : Set.Iio j,
        stage (e := e) (Y := Y) (H := H) (U := U) hU k.1 :=
  by
    let _ : Fact e.μ.IsRegular := e.regular_μ
    let _ : Nonempty (J e) := by
      simpa using Cardinal.IsRegular.ne_zero (Fact.out : e.μ.IsRegular)
    let _ : OrderBot (J e) := WellFoundedLT.toOrderBot (J e)
    exact Subfunctor.strictPrefixUnion_limit U
      (seed (e := e) (Y := Y) (H := H) (U := U) hU) j hj

private noncomputable def closure : Subfunctor (toPresheaf.obj Y) :=
  ⨆ j : J e, stage (e := e) (Y := Y) (H := H) (U := U) hU j

private theorem le_closure :
    U ≤ closure (e := e) (Y := Y) (H := H) (U := U) hU := by
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let _ : Nonempty (J e) := by
    simpa using Cardinal.IsRegular.ne_zero (Fact.out : e.μ.IsRegular)
  let _ : OrderBot (J e) := WellFoundedLT.toOrderBot (J e)
  exact le_sup_left.trans (le_iSup
    (stage (e := e) (Y := Y) (H := H) (U := U) hU) (⊥ : J e))

private theorem closure_points_le : Cardinal.mk
    (closure (e := e) (Y := Y) (H := H) (U := U) hU).toFunctor.Elements ≤ e.γ := by
  apply Subfunctor.mk_elements_iSup_le_of_le
    (stage (e := e) (Y := Y) (H := H) (U := U) hU)
    e.aleph0_le_γ e.μ_ord_le_γ
  exact stage_points_le (e := e) (Y := Y) (H := H) (U := U) hU

private theorem successor_W_le_stage_succ (j : J e) :
    (stageSuccessor (e := e) (Y := Y) (H := H) (U := U) hU j).W ≤
      stage (e := e) (Y := Y) (H := H) (U := U) hU (Order.succ j) := by
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let _ : NoMaxOrder (J e) :=
    Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  rw [← seed_eq_successor_W (e := e) (Y := Y) (H := H) (U := U) hU j]
  exact Subfunctor.seed_le_strictPrefixUnion_succ U
    (seed (e := e) (Y := Y) (H := H) (U := U) hU) j (not_isMax j)

private theorem successor_W_le_closure (j : J e) :
    (stageSuccessor (e := e) (Y := Y) (H := H) (U := U) hU j).W ≤
      closure (e := e) (Y := Y) (H := H) (U := U) hU :=
  (successor_W_le_stage_succ (e := e) (Y := Y) (H := H) (U := U) hU j).trans
    (le_iSup (stage (e := e) (Y := Y) (H := H) (U := U) hU) (Order.succ j))

private noncomputable def stageToClosure (j : J e) :
    originalSubpresheafObject
        (stage (e := e) (Y := Y) (H := H) (U := U) hU j) ⟶
      originalSubpresheafObject
        (closure (e := e) (Y := Y) (H := H) (U := U) hU) :=
  originalSubpresheafMapOfLE
    (le_iSup (stage (e := e) (Y := Y) (H := H) (U := U) hU) j)

/-- The exact original stage chain remains colimiting after realization, Q,
the inner one-simplex tensor, the presheaf equivalence, and evaluation. -/
private noncomputable def mappedCylinderChain_isColimit
    (p : (SimplexCategory × SimplexCategory)ᵒᵖ) :
    let S := stage (e := e) (Y := Y) (H := H) (U := U) hU
    let c0 := Subfunctor.chainUnionCocone S
      (stage_mono (e := e) (Y := Y) (H := H) (U := U) hU)
    let c1 := equivalencePresheaf.inverse.mapCocone c0
    let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
    let c2 := Q.mapCocone c1
    let c3 := innerOneSimplexPrecylinder.I.mapCocone c2
    let c4 := toPresheaf.mapCocone c3
    let c5 := ((evaluation _ (Type u)).obj p).mapCocone c4
    IsColimit c5 := by
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let _ : IsCardinalFiltered (J e) e.μ := inferInstance
  let S := stage (e := e) (Y := Y) (H := H) (U := U) hU
  let hS := stage_mono (e := e) (Y := Y) (H := H) (U := U) hU
  let c0 := Subfunctor.chainUnionCocone S hS
  let hc0 := Subfunctor.isColimitChainUnionCocone S hS
  let c1 := equivalencePresheaf.inverse.mapCocone c0
  let hc1 : IsColimit c1 := isColimitOfPreserves equivalencePresheaf.inverse hc0
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let _ : Q.IsCardinalAccessible e.μ := e.q_isCardinalAccessible
  let _ : PreservesColimitsOfShape (J e) Q :=
    Q.preservesColimitsOfShape_of_isCardinalAccessible e.μ (J e)
  let c2 := Q.mapCocone c1
  let hc2 : IsColimit c2 := isColimitOfPreserves Q hc1
  let _ : innerOneSimplexPrecylinder.{u}.I.IsLeftAdjoint :=
    (innerTensorCotensorAdjunction (Δ[1] : SSet.{u})).isLeftAdjoint
  let c3 := innerOneSimplexPrecylinder.I.mapCocone c2
  let hc3 : IsColimit c3 :=
    isColimitOfPreserves innerOneSimplexPrecylinder.I hc2
  let c4 := toPresheaf.mapCocone c3
  let hc4 : IsColimit c4 := isColimitOfPreserves toPresheaf hc3
  let E := (evaluation ((SimplexCategory × SimplexCategory)ᵒᵖ) (Type u)).obj p
  exact isColimitOfPreserves E hc4

private theorem exists_stage_cylinder_preimage
    (p : (SimplexCategory × SimplexCategory)ᵒᵖ)
    (x : (toPresheaf.obj
      (innerOneSimplexPrecylinder.I.obj
        ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
          (originalSubpresheafObject
            (closure (e := e) (Y := Y) (H := H) (U := U) hU))))).obj p) :
    ∃ (j : J e)
      (y : (toPresheaf.obj
        (innerOneSimplexPrecylinder.I.obj
          ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
            (originalSubpresheafObject
              (stage (e := e) (Y := Y) (H := H) (U := U) hU j))))).obj p),
      (toPresheaf.map
        (innerOneSimplexPrecylinder.I.map
          ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
            (stageToClosure (e := e) (Y := Y) (H := H) (U := U) hU j)))).app p y = x := by
  let S := stage (e := e) (Y := Y) (H := H) (U := U) hU
  let hS := stage_mono (e := e) (Y := Y) (H := H) (U := U) hU
  let c0 := Subfunctor.chainUnionCocone S hS
  let c1 := equivalencePresheaf.inverse.mapCocone c0
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let c2 := Q.mapCocone c1
  let c3 := innerOneSimplexPrecylinder.I.mapCocone c2
  let c4 := toPresheaf.mapCocone c3
  let E := (evaluation ((SimplexCategory × SimplexCategory)ᵒᵖ) (Type u)).obj p
  let c5 := E.mapCocone c4
  let hc5 : IsColimit c5 :=
    mappedCylinderChain_isColimit (e := e) (Y := Y) (H := H) (U := U) hU p
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc5 x
  exact ⟨j, y, hy⟩

private theorem closure_range_le :
    let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
    let V := closure (e := e) (Y := Y) (H := H) (U := U) hU
    let f : innerOneSimplexPrecylinder.I.obj
        (Q.obj (originalSubpresheafObject V)) ⟶ Q.obj Y :=
      innerOneSimplexPrecylinder.I.map
          (Q.map (originalSubpresheafInclusion V)) ≫ H
    let m : Q.obj (originalSubpresheafObject V) ⟶ Q.obj Y :=
      Q.map (originalSubpresheafInclusion V)
    Subfunctor.range (toPresheaf.map f) ≤
      Subfunctor.range (toPresheaf.map m) := by
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let V := closure (e := e) (Y := Y) (H := H) (U := U) hU
  let f : innerOneSimplexPrecylinder.I.obj
      (Q.obj (originalSubpresheafObject V)) ⟶ Q.obj Y :=
    innerOneSimplexPrecylinder.I.map
        (Q.map (originalSubpresheafInclusion V)) ≫ H
  let m : Q.obj (originalSubpresheafObject V) ⟶ Q.obj Y :=
    Q.map (originalSubpresheafInclusion V)
  apply Subfunctor.range_le_range_of_app
  intro p x
  obtain ⟨j, y, hy⟩ := exists_stage_cylinder_preimage
    (e := e) (Y := Y) (H := H) (U := U) hU p x
  let D := stageSuccessor (e := e) (Y := Y) (H := H) (U := U) hU j
  let a : originalSubpresheafObject
        (stage (e := e) (Y := Y) (H := H) (U := U) hU j) ⟶
      originalSubpresheafObject V :=
    stageToClosure (e := e) (Y := Y) (H := H) (U := U) hU j
  let b : originalSubpresheafObject D.W ⟶ originalSubpresheafObject V :=
    originalSubpresheafMapOfLE
      (successor_W_le_closure (e := e) (Y := Y) (H := H) (U := U) hU j)
  let z := (toPresheaf.map (D.lift ≫ Q.map b)).app p y
  refine ⟨z, ?_⟩
  have ha : a ≫ originalSubpresheafInclusion V =
      originalSubpresheafInclusion
        (stage (e := e) (Y := Y) (H := H) (U := U) hU j) := by
    exact originalSubpresheafMapOfLE_inclusion _
  have hb : b ≫ originalSubpresheafInclusion V =
      originalSubpresheafInclusion D.W := by
    exact originalSubpresheafMapOfLE_inclusion _
  have hfac :
      innerOneSimplexPrecylinder.I.map (Q.map a) ≫ f =
        (D.lift ≫ Q.map b) ≫ m := by
    calc
      _ = (innerOneSimplexPrecylinder.I.map (Q.map a) ≫
            innerOneSimplexPrecylinder.I.map
              (Q.map (originalSubpresheafInclusion V))) ≫ H := by
          simp only [f, Category.assoc]
      _ = innerOneSimplexPrecylinder.I.map
            (Q.map (a ≫ originalSubpresheafInclusion V)) ≫ H := by
          rw [Q.map_comp, innerOneSimplexPrecylinder.I.map_comp]
      _ = innerOneSimplexPrecylinder.I.map
            (Q.map (originalSubpresheafInclusion
              (stage (e := e) (Y := Y) (H := H) (U := U) hU j))) ≫ H := by
          rw [ha]
      _ = D.lift ≫ Q.map (originalSubpresheafInclusion D.W) := D.fac
      _ = D.lift ≫ Q.map (b ≫ originalSubpresheafInclusion V) := by rw [hb]
      _ = (D.lift ≫ Q.map b) ≫ m := by
          simp only [m, Q.map_comp, Category.assoc]
  rw [← hy]
  simpa only [z, f, m, a, Functor.map_comp, NatTrans.comp_app,
    types_comp_apply] using
    congrArg (fun k => (toPresheaf.map k).app p y) hfac.symm

include hU in
theorem _root_.SimplicialSpace.LocalReplacementCardinalEnvelope.exists_invariantSubpresheaf :
    Nonempty (LocalReplacementInvariantSubpresheaf e Y H U) := by
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let V := closure (e := e) (Y := Y) (H := H) (U := U) hU
  let f : innerOneSimplexPrecylinder.I.obj
      (Q.obj (originalSubpresheafObject V)) ⟶ Q.obj Y :=
    innerOneSimplexPrecylinder.I.map
        (Q.map (originalSubpresheafInclusion V)) ≫ H
  let m : Q.obj (originalSubpresheafObject V) ⟶ Q.obj Y :=
    Q.map (originalSubpresheafInclusion V)
  let _ : Q.PreservesMonomorphisms :=
    canonical_terminalIteration_preservesMonomorphisms κ
  let _ : Mono m := inferInstance
  have hrange : Subfunctor.range (toPresheaf.map f) ≤
      Subfunctor.range (toPresheaf.map m) :=
    closure_range_le (e := e) (Y := Y) (H := H) (U := U) hU
  let lPresheaf := NatTrans.factorThruMono
    (toPresheaf.map f) (toPresheaf.map m) hrange
  let l := toPresheaf.preimage lPresheaf
  have hfac : l ≫ m = f := by
    apply toPresheaf.map_injective
    rw [Functor.map_comp]
    dsimp only [l]
    rw [Functor.map_preimage]
    exact NatTrans.factorThruMono_comp _ _ _
  exact ⟨{
    V := V
    le := le_closure (e := e) (Y := Y) (H := H) (U := U) hU
    points_le := closure_points_le (e := e) (Y := Y) (H := H) (U := U) hU
    raw_points_le := originalSubpresheaf_mk_elements_le V e.γ
      (closure_points_le (e := e) (Y := Y) (H := H) (U := U) hU)
    restrictedHomotopy := l
    fac := hfac.symm }⟩

end LocalReplacementInvariantClosure
end SimplicialSpace
