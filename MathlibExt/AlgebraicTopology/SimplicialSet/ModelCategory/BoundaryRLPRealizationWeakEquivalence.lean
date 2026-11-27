/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationDeltaGenerated
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWUnit
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Factorization
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.SimplexTriviality
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationDeltaGeneratedFiniteLimits
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexBoundaryRLPRecognition
public import MathlibExt.CategoryTheory.TrivialBundleWithFiber
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Boundary lifting and weak equivalences under realization

In every universe u, a map f:X→Y between Kan simplicial sets is a simplicial weak equivalence
exactly when its realized map |f|:|X|→|Y| is a weak homotopy equivalence of spaces. For a
simplicial fibration p:E→B, right lifting against all boundary inclusions ∂Δ[n]→Δ[n], n≥0, is
equivalent to weak homotopy equivalence of |p|.

The comparison uses the realization–singular adjunction and finite-limit preservation after
delta-generated coreflection.

Reference: Goerss and Jardine, Simplicial Homotopy Theory, Chapter I.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

noncomputable section
universe u

namespace SSet.KanComplex

/-- For Kan simplicial sets X,Y in universe u and a simplicial map f:X→Y, f is a simplicial weak
equivalence if and only if |f|:|X|→|Y| is a weak homotopy equivalence. The simplicial
weak-equivalence predicate includes connected-component bijectivity and isomorphisms on pointed
homotopy groups. -/
theorem W_iff_realizationWeakEquivalence
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) :
    KanComplex.W f ↔ SSet.realizationWeakEquivalences f := by
  have hX : W (sSetTopAdj.unit.app X) := W.sSetTopAdj_unit_app X
  have hY : W (sSetTopAdj.unit.app Y) := W.sSetTopAdj_unit_app Y
  have hNat : f ≫ sSetTopAdj.unit.app Y =
      sSetTopAdj.unit.app X ≫
        (SSet.toTop ⋙ TopCat.toSSet).map f := by
    simpa only [Functor.id_map] using sSetTopAdj.unit.naturality f
  change W f ↔ W ((SSet.toTop ⋙ TopCat.toSSet).map f)
  calc
    W f ↔ W (f ≫ sSetTopAdj.unit.app Y) :=
      (W.postcomp_iff hY).symm
    _ ↔ W (sSetTopAdj.unit.app X ≫
        (SSet.toTop ⋙ TopCat.toSSet).map f) := by rw [hNat]
    _ ↔ W ((SSet.toTop ⋙ TopCat.toSSet).map f) :=
      W.precomp_iff hX

end SSet.KanComplex

namespace SSet

private theorem realizationCounitIsIso (X : SSet.{u}) :
    IsIso (DeltaGenerated.coreflectorAdjunction.counit.app
      (SSet.toTop.obj X)) := by
  let e : ((TopCat.toDeltaGenerated ⋙
      DeltaGenerated.deltaGeneratedToTop).obj (SSet.toTop.obj X)) ≅
      SSet.toTop.obj X :=
    TopCat.isoOfHomeo (Topology.IsGeneratedBy.homeomorph
      (X := fun n : ℕ => Fin n → ℝ)
      (Y := ↥(SSet.toTop.obj X)))
  have hEq : DeltaGenerated.coreflectorAdjunction.counit.app
      (SSet.toTop.obj X) = e.hom := by
    apply TopCat.hom_ext
    rfl
  rw [hEq]
  exact e.isIso_hom

private noncomputable def realizationCoreflectionIso :
    (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) ⋙
        DeltaGenerated.deltaGeneratedToTop.{u} ≅
      SSet.toTop.{u} :=
  NatIso.ofComponents (fun X => by
    let _ : IsIso (DeltaGenerated.coreflectorAdjunction.counit.app
        (SSet.toTop.obj X)) := realizationCounitIsIso X
    exact asIso (DeltaGenerated.coreflectorAdjunction.counit.app
      (SSet.toTop.obj X)))

private noncomputable def deltaRealizationAdjunction :
    (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) ⊣
      (DeltaGenerated.deltaGeneratedToTop.{u} ⋙ TopCat.toSSet.{u}) :=
  sSetTopAdj.restrictFullyFaithful
    (Functor.FullyFaithful.id SSet.{u})
    DeltaGenerated.fullyFaithfulDeltaGeneratedToTop
    realizationCoreflectionIso.symm
    (Iso.refl _)

private noncomputable def realSingCoreflectionIso :
    ((SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) ⋙
        (DeltaGenerated.deltaGeneratedToTop.{u} ⋙ TopCat.toSSet.{u})) ≅
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}) :=
  Functor.isoWhiskerRight realizationCoreflectionIso TopCat.toSSet

private noncomputable def deltaRealSingArrowIso
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    Arrow.mk ((DeltaGenerated.deltaGeneratedToTop.{u} ⋙
      TopCat.toSSet.{u}).map
        ((SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}).map f)) ≅
      Arrow.mk ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map f) :=
  Arrow.isoMk (realSingCoreflectionIso.app X)
    (realSingCoreflectionIso.app Y)
    (realSingCoreflectionIso.hom.naturality f).symm

private theorem realizationWeakEquivalence_of_fibration_of_isPullback
    {E' E B' B : SSet.{u}}
    {t : E' ⟶ E} {l : E' ⟶ B'} {r : E ⟶ B} {b : B' ⟶ B}
    [Fibration r] (hr : realizationWeakEquivalences r)
    (sq : IsPullback t l r b) :
    realizationWeakEquivalences l := by
  let F := SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}
  let G := DeltaGenerated.deltaGeneratedToTop.{u} ⋙ TopCat.toSSet.{u}
  let _ : G.IsRightAdjoint := deltaRealizationAdjunction.isRightAdjoint
  have sqD : IsPullback (F.map t) (F.map l) (F.map r) (F.map b) :=
    sq.map F
  have sqS : IsPullback (G.map (F.map t)) (G.map (F.map l))
      (G.map (F.map r)) (G.map (F.map b)) :=
    sqD.map G
  have hrJ0 : SSet.modelCategoryQuillen.J.{u}.rlp
      ((SSet.toTop ⋙ TopCat.toSSet).map r) :=
    (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp
      (SSet.toTop_map_mem_realizedHornRLP r)
  have hrW0 : SSet.KanComplex.W.{u}
      ((SSet.toTop ⋙ TopCat.toSSet).map r) := hr
  have hrJ : SSet.modelCategoryQuillen.J.{u}.rlp (G.map (F.map r)) :=
    (SSet.modelCategoryQuillen.J.rlp.arrow_mk_iso_iff
      (deltaRealSingArrowIso r)).mpr hrJ0
  have hrW : SSet.KanComplex.W.{u} (G.map (F.map r)) :=
    (SSet.KanComplex.W.arrow_mk_iso_iff
      (deltaRealSingArrowIso r)).mpr hrW0
  have hrI : SSet.modelCategoryQuillen.I.{u}.rlp (G.map (F.map r)) :=
    SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp _ ⟨hrJ, hrW⟩
  have hlI : SSet.modelCategoryQuillen.I.{u}.rlp (G.map (F.map l)) :=
    MorphismProperty.of_isPullback sqS hrI
  let _ : SSet.KanComplex (G.obj (F.obj E')) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (G.obj (F.obj B')) :=
    TopCat.toSSet_obj_kanComplex _
  have hlW : SSet.KanComplex.W.{u} (G.map (F.map l)) :=
    SSet.KanComplex.I_rlp_to_W_kanRestricted hlI
  exact (SSet.KanComplex.W.arrow_mk_iso_iff
    (deltaRealSingArrowIso l)).mp hlW

private theorem minimal_I_rlp_of_realizationWeakEquivalence
    {E B : SSet.{u}} {p : E ⟶ B}
    (hpMin : SSet.MinimalFibration.IsMinimalFibration p)
    (hpW : SSet.realizationWeakEquivalences p) :
    SSet.modelCategoryQuillen.I.{u}.rlp p := by
  let _ : Fibration p := hpMin.1
  rintro _ _ _ ⟨n⟩
  constructor
  intro top bottom sq
  let P := pullback p bottom
  let e : P ⟶ E := pullback.fst p bottom
  let q : P ⟶ (Δ[n] : SSet.{u}) := pullback.snd p bottom
  have hqMin : SSet.MinimalFibration.IsMinimalFibration q :=
    SSet.MinimalFibration.isMinimalFibration_pullback_snd p bottom hpMin
  let _ : Fibration q := hqMin.1
  have hqW : SSet.realizationWeakEquivalences q :=
    realizationWeakEquivalence_of_fibration_of_isPullback hpW
      (IsPullback.of_hasPullback p bottom)
  let topP : (SSet.boundary n : SSet.{u}) ⟶ P :=
    pullback.lift top (SSet.boundary n).ι sq.w
  have topP_fst : topP ≫ e = top := by
    exact pullback.lift_fst top (SSet.boundary n).ι sq.w
  have topP_snd : topP ≫ q = (SSet.boundary n).ι := by
    exact pullback.lift_snd top (SSet.boundary n).ι sq.w
  let v₀ : (Δ[n] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))
  let b₀ : (Δ[0] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) :=
    SSet.const v₀
  let F₀ := pullback q b₀
  let a : F₀ ⟶ (Δ[0] : SSet.{u}) := pullback.snd q b₀
  let _ : Fibration a := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    apply MorphismProperty.of_isPullback (IsPullback.of_hasPullback q b₀)
    exact (SSet.modelCategoryQuillen.fibration_iff q).mp (by infer_instance)
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) := by
    exact (isFibrant_iff_of_isTerminal (𝟙 _)
      SSet.stdSimplex.isTerminalObj₀).2 (by infer_instance)
  let _ : SSet.KanComplex F₀ := isFibrant_of_fibration a
  have haW : SSet.realizationWeakEquivalences a :=
    realizationWeakEquivalence_of_fibration_of_isPullback hqW
      (IsPullback.of_hasPullback q b₀)
  have haKW : SSet.KanComplex.W a :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence a).mpr haW
  have haI : SSet.modelCategoryQuillen.I.{u}.rlp a :=
    (SSet.KanComplex.I_rlp_iff_W_of_fibration a).mpr haKW
  let hTriv : CategoryTheory.TrivialBundleWithFiber F₀ q := by
    simpa only [F₀, b₀, v₀] using
      SSet.MinimalFibration.trivialBundleWithFiber_stdSimplex q hqMin
  let topF : (SSet.boundary n : SSet.{u}) ⟶ F₀ := topP ≫ hTriv.r
  let sqF : CommSq topF (SSet.boundary n).ι a
      (SSet.stdSimplex.isTerminalObj₀.from _) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have hLP : HasLiftingProperty (SSet.boundary n).ι a :=
    haI _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)
  have hHas : sqF.HasLift := hLP.sq_hasLift sqF
  let lF : (Δ[n] : SSet.{u}) ⟶ F₀ := hHas.exists_lift.some.l
  let lQ : (Δ[n] : SSet.{u}) ⟶ P :=
    BinaryFan.IsLimit.lift hTriv.isLimit (𝟙 _) lF
  have hlQq : lQ ≫ q = 𝟙 _ :=
    BinaryFan.IsLimit.lift_fst hTriv.isLimit _ _
  have hlQr : lQ ≫ hTriv.r = lF :=
    BinaryFan.IsLimit.lift_snd hTriv.isLimit _ _
  have hleftQ : (SSet.boundary n).ι ≫ lQ = topP := by
    apply BinaryFan.IsLimit.hom_ext hTriv.isLimit
    · change ((SSet.boundary n).ι ≫ lQ) ≫ q = topP ≫ q
      rw [Category.assoc, hlQq, Category.comp_id, topP_snd]
    · change ((SSet.boundary n).ι ≫ lQ) ≫ hTriv.r =
        topP ≫ hTriv.r
      rw [Category.assoc, hlQr]
      exact hHas.exists_lift.some.fac_left
  exact CommSq.HasLift.mk' ⟨lQ ≫ e,
    by
      rw [← Category.assoc, hleftQ, topP_fst],
    by
      calc
        (lQ ≫ e) ≫ p = lQ ≫ (e ≫ p) := Category.assoc _ _ _
        _ = lQ ≫ (q ≫ bottom) := by rw [pullback.condition]
        _ = (lQ ≫ q) ≫ bottom := by rw [Category.assoc]
        _ = bottom := by rw [hlQq, Category.id_comp]⟩

namespace modelCategoryQuillen

/-- Let p:E→B be a simplicial fibration in universe u. Then p has the right lifting property against
every boundary inclusion ∂Δ[n]→Δ[n], n≥0, if and only if |p|:|E|→|B| is a weak homotopy
equivalence. This statement uses the fibration hypothesis on p. -/
theorem I_rlp_iff_realizationWeakEquivalence_of_fibration
    {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] :
    SSet.modelCategoryQuillen.I.{u}.rlp p ↔
      SSet.realizationWeakEquivalences p := by
  constructor
  · exact fun hp =>
      SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences p hp
  · intro hpW
    obtain ⟨E', r, p', hfac, hp'Min, hrI⟩ :=
      SSet.MinimalFibration.factorization p
    have hrW : SSet.realizationWeakEquivalences r :=
      SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences r hrI
    have hcompW : SSet.realizationWeakEquivalences (r ≫ p') := by
      simpa only [hfac] using hpW
    have hp'W : SSet.realizationWeakEquivalences p' :=
      MorphismProperty.of_precomp SSet.realizationWeakEquivalences
        r p' hrW hcompW
    have hp'I : SSet.modelCategoryQuillen.I.{u}.rlp p' :=
      minimal_I_rlp_of_realizationWeakEquivalence hp'Min hp'W
    have hcompI : SSet.modelCategoryQuillen.I.{u}.rlp (r ≫ p') :=
      MorphismProperty.comp_mem _ _ _ hrI hp'I
    simpa only [hfac] using hcompI

end modelCategoryQuillen
end SSet
