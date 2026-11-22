/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FiniteCompletenessCentralFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.InverseTriangleContractibility
import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ScalarFibreWeakDetection
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant

/-!
# The original finite completeness evaluation

The central edge evaluates into the original intrinsic equivalence component.
Its strict fibres retain the complete adjacent tetrahedron and the independent
left and right inverse triangles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.FiniteCompletenessMapping

open SegalHomotopy SSet.Rezk.FiniteCompleteness

private theorem centralInverseData (W : SimplicialSpace.{u})
    (z : (mapping W) _⦋0⦌) :
    HasInverseData W ((toCentral W).app (op ⦋0⦌) z) := by
  refine ⟨(toThree W).app (op ⦋0⦌) z, ?_⟩
  have h := congrArg (fun f => inverseTestHom W ≫ f)
    (pullback.condition (f := inverseRestriction W) (g := identityTriple W))
  have hc : toThree W ≫ inverseRestriction W = toCentral W ≫ identityTriple W := by
    simpa only [Category.assoc, inverseTestHom_three_assoc,
      inverseTestHom_central_assoc] using h
  exact congrArg (fun f => f.app (op ⦋0⦌) z) hc

private theorem centralRange (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.Subcomplex.range (toCentral W) ≤ equivalenceSubcomplex W hW := by
  intro n r hr
  obtain ⟨z, rfl⟩ := hr
  rw [mem_equivalenceSubcomplex, ← (toCentral W).naturality_apply]
  exact isEquivalenceEdge_of_hasInverseData W hW _ (centralInverseData W _)

/-- The original central12 evaluation factors through the same equivalence-arrow component. -/
def centralEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    mapping W ⟶ (equivalenceSubcomplex W hW : SSet.{u}) :=
  SSet.Subcomplex.lift (toCentral W) (centralRange W hW)

/-- The same canonical evaluation in the original selected-end presentation. -/
def decoratedEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    mapping W ⟶ (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) :=
  centralEvaluation W hW ≫ (EquivalenceMapping.yonedaIsoOne W hW).inv

/-- The canonical factor retains the whole original central restriction. -/
@[reassoc (attr := simp)]
theorem centralEvaluation_iota (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    centralEvaluation W hW ≫ (equivalenceSubcomplex W hW).ι = toCentral W :=
  SSet.Subcomplex.lift_ι _ _

/-- The selected-end factor retains its original inclusion and inverse Yoneda map. -/
@[reassoc]
theorem decoratedEvaluation_iota (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    decoratedEvaluation W hW ≫ (EquivalenceMapping.subcomplex W hW Δ[1]).ι =
      toCentral W ≫ (discreteYonedaIso W 1).inv := by
  rw [decoratedEvaluation, Category.assoc, EquivalenceMapping.yonedaIsoOne_inv_ι,
    ← Category.assoc, centralEvaluation_iota]

/-- The actual source and both canonical target presentations are Kan internally. -/
theorem mappingEndpoints_kanComplex (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex (mapping W) ∧
      SSet.KanComplex (equivalenceSubcomplex W hW : SSet.{u}) ∧
        SSet.KanComplex (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hK : SSet.KanComplex (mapping W) :=
    ReedyModel.innerHom_kanComplex (ofSimplicialObject.obj K) W
      (ReedyModel.isCofibrant _) hW.1
  let _ : SSet.KanComplex (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) :=
    EquivalenceMapping.subcomplex_kan W hW Δ[1]
  have hE : SSet.KanComplex (equivalenceSubcomplex W hW : SSet.{u}) :=
    isFibrant_of_fibration (EquivalenceMapping.yonedaIsoOne W hW).inv
  exact ⟨hK, hE, inferInstance⟩

private theorem rawCentralFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (toCentral W) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (inverseRestriction W) := inverseRestriction_fibration W hW
  have h : toCentral W = (inverseTestIso W).hom ≫
      pullback.snd (inverseRestriction W) (identityTriple W) :=
    (inverseTestHom_central W).symm
  rw [h]
  infer_instance

private theorem centralFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (centralEvaluation W hW) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  have hraw := (SSet.modelCategoryQuillen.fibration_iff (toCentral W)).mp
    (rawCentralFibration W hW)
  let _ : HasLiftingProperty i (toCentral W) := hraw i hi
  constructor
  intro top bottom sq
  let sqRaw : CommSq top i (toCentral W)
      (bottom ≫ (equivalenceSubcomplex W hW).ι) := by
    constructor
    have h := congrArg (fun f => f ≫ (equivalenceSubcomplex W hW).ι) sq.w
    simpa only [Category.assoc, centralEvaluation_iota] using h
  refine CommSq.HasLift.mk' ⟨sqRaw.lift, sqRaw.fac_left, ?_⟩
  apply (cancel_mono (equivalenceSubcomplex W hW).ι).mp
  rw [Category.assoc, centralEvaluation_iota]
  exact sqRaw.fac_right

/-- Both original evaluation presentations have genuine scalar Kan fibrations. -/
theorem evaluation_fibrations (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    Fibration (centralEvaluation W hW) ∧ Fibration (decoratedEvaluation W hW) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (centralEvaluation W hW) := centralFibration W hW
  have hp : Fibration (decoratedEvaluation W hW) := by
    unfold decoratedEvaluation
    infer_instance
  exact ⟨inferInstance, hp⟩

private theorem pairedPointTF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y x) _⦋0⦌)
    (hIso : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨x⟩) (SSet.π₀.mk a)) :
    trivialFibrations SSet.{u} (InverseTriangle.pairedToPoint W y x a) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let L := InverseTriangle.leftSpace W y x a
  let R := InverseTriangle.rightSpace W y x a
  have hl := InverseTriangle.leftToPoint_trivialFibration W hW y x a hIso
  have hr := InverseTriangle.rightToPoint_trivialFibration W hW y x a hIso
  have sq : IsPullback (prod.fst : L ⨯ R ⟶ L) (prod.snd : L ⨯ R ⟶ R)
      (InverseTriangle.leftToPoint W y x a) (InverseTriangle.rightToPoint W y x a) := by
    have hs := IsPullback.of_isLimit_binaryFan_of_isTerminal
      (prodIsProd L R) (SSet.stdSimplex.isTerminalObj₀.{u})
    have hL : SSet.stdSimplex.isTerminalObj₀.from L =
        InverseTriangle.leftToPoint W y x a := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have hR : SSet.stdSimplex.isTerminalObj₀.from R =
        InverseTriangle.rightToPoint W y x a := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    change IsPullback (prod.fst : L ⨯ R ⟶ L) (prod.snd : L ⨯ R ⟶ R)
      (SSet.stdSimplex.isTerminalObj₀.from L) (SSet.stdSimplex.isTerminalObj₀.from R) at hs
    rw [hL, hR] at hs
    exact hs
  have hp : trivialFibrations SSet.{u} (prod.snd : L ⨯ R ⟶ R) :=
    (trivialFibrations SSet.{u}).of_isPullback sq hl
  rw [← InverseTriangle.pairedToPoint_right]
  exact (trivialFibrations SSet.{u}).comp_mem _ _ hp hr

private theorem coherentPointTF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y x) _⦋0⦌)
    (hIso : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨x⟩) (SSet.π₀.mk a)) :
    trivialFibrations SSet.{u} (coherentPoint W x y a) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hp : trivialFibrations SSet.{u}
      (pullback.snd (AdjacentTriangle.comparison W x y x y) (pairedToAdjacent W x y a)) :=
    (trivialFibrations SSet.{u}).of_isPullback (IsPullback.of_hasPullback _ _)
      (AdjacentTriangle.comparison_trivialFibration W hW x y x y)
  exact (trivialFibrations SSet.{u}).comp_mem _ _ hp (pairedPointTF W hW x y a hIso)

private theorem centralPointTF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W y x) _⦋0⦌)
    (hIso : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨x⟩) (SSet.π₀.mk a)) :
    trivialFibrations SSet.{u} (centralPoint W x y a) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have h := (trivialFibrations SSet.{u}).comp_mem (centralIso W x y a).hom
    (coherentPoint W x y a) ((trivialFibrations SSet.{u}).of_isIso _)
      (coherentPointTF W hW x y a hIso)
  simpa only [centralIso, centralHom_point] using h

private def originalSource (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) : (W.diagram _⦋0⦌) _⦋0⦌ :=
  (W.diagram.δ (1 : Fin 2)).app (op ⦋0⦌) g

private def originalTarget (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) : (W.diagram _⦋0⦌) _⦋0⦌ :=
  (W.diagram.δ (0 : Fin 2)).app (op ⦋0⦌) g

private def originalPointMap (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) : (Δ[0] : SSet.{u}) ⟶
      mappingFibre W (originalSource W g) (originalTarget W g) :=
  pullback.lift (SSet.yonedaEquiv.symm g) (𝟙 _) (by
    apply prod.hom_ext
    · rw [Category.assoc, mappingEndpoint_fst, Category.id_comp, mappingPointPair_fst]
      exact SSet.yonedaEquiv_symm_comp g (W.diagram.δ (1 : Fin 2))
    · rw [Category.assoc, mappingEndpoint_snd, Category.id_comp, mappingPointPair_snd]
      exact SSet.yonedaEquiv_symm_comp g (W.diagram.δ (0 : Fin 2)))

private def originalPoint (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    (mappingFibre W (originalSource W g) (originalTarget W g)) _⦋0⦌ :=
  SSet.yonedaEquiv (originalPointMap W g)

private theorem originalPoint_projection (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    (mappingFibre.fst W (originalSource W g) (originalTarget W g)).app (op ⦋0⦌)
      (originalPoint W g) = g := by
  have h : originalPointMap W g ≫
      mappingFibre.fst W (originalSource W g) (originalTarget W g) =
      SSet.yonedaEquiv.symm g := pullback.lift_fst _ _ _
  have hc := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, originalPoint] using hc

private theorem originalPoint_map (W : SimplicialSpace.{u})
    (g : (W.diagram _⦋1⦌) _⦋0⦌) :
    SSet.yonedaEquiv.symm (originalPoint W g) ≫
      mappingFibre.fst W (originalSource W g) (originalTarget W g) =
        SSet.const (X := Δ[0]) g := by
  rw [SSet.yonedaEquiv_symm_comp, originalPoint_projection,
    SSet.yonedaEquiv_symm_zero]

private theorem selectedFibrePointTF (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (b : (equivalenceSubcomplex W hW : SSet.{u}) _⦋0⦌) :
    trivialFibrations SSet.{u}
      (SSet.stdSimplex.isTerminalObj₀.from
        (SSet.Subcomplex.fiber (centralEvaluation W hW) b : SSet.{u})) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let g := b.val
  let x := originalTarget W g
  let y := originalSource W g
  let a := originalPoint W g
  have hIso : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨x⟩) (SSet.π₀.mk a) :=
    (isEquivalenceEdge_iff_of_fibre W hW g a (originalPoint_projection W g)).mp
      ((mem_equivalenceSubcomplex_zero W hW g).mp b.property)
  have hraw : trivialFibrations SSet.{u}
      (pullback.snd (toCentral W) (SSet.const (X := Δ[0]) g)) := by
    have h := centralPointTF W hW x y a hIso
    change trivialFibrations SSet.{u} (pullback.snd (toCentral W)
      (SSet.yonedaEquiv.symm (originalPoint W g) ≫
        mappingFibre.fst W (originalSource W g) (originalTarget W g))) at h
    exact Eq.mp (congrArg (fun k : (Δ[0] : SSet.{u}) ⟶ W.diagram _⦋1⦌ =>
      trivialFibrations SSet.{u} (pullback.snd (toCentral W) k))
        (originalPoint_map W g)) h
  let F : SSet.{u} := SSet.Subcomplex.fiber (centralEvaluation W hW) b
  let t : F ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from F
  have oldSq : IsPullback (SSet.Subcomplex.fiber (centralEvaluation W hW) b).ι t
      (centralEvaluation W hW) (SSet.const (X := Δ[0]) b) :=
    SSet.Subcomplex.fiber_isPullback (centralEvaluation W hW) b
  have hι : (SSet.const (X := Δ[0]) b) ≫ (equivalenceSubcomplex W hW).ι =
      SSet.const (X := Δ[0]) g := by
    rw [SSet.const_comp]
    rfl
  have rawSq : IsPullback (SSet.Subcomplex.fiber (centralEvaluation W hW) b).ι t
      (toCentral W) (SSet.const (X := Δ[0]) g) := by
    apply IsPullback.mk'
    · have h := congrArg (fun f => f ≫ (equivalenceSubcomplex W hW).ι) oldSq.w
      simpa only [Category.assoc, centralEvaluation_iota, hι] using h
    · intro T φ ψ h₁ h₂
      exact oldSq.hom_ext h₁ h₂
    · intro T u v h
      have hq : u ≫ centralEvaluation W hW = v ≫ SSet.const (X := Δ[0]) b := by
        apply (cancel_mono (equivalenceSubcomplex W hW).ι).mp
        rw [Category.assoc, centralEvaluation_iota, Category.assoc, hι]
        exact h
      exact ⟨oldSq.lift u v hq, oldSq.lift_fst _ _ _, oldSq.lift_snd _ _ _⟩
  have hc := (trivialFibrations SSet.{u}).comp_mem rawSq.isoPullback.hom
    (pullback.snd (toCentral W) (SSet.const (X := Δ[0]) g))
      ((trivialFibrations SSet.{u}).of_isIso _) hraw
  simpa only [rawSq.isoPullback_hom_snd] using hc

private theorem centralWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (centralEvaluation W hW) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (centralEvaluation W hW) := centralFibration W hW
  apply (SSet.realizationWeakEquivalence_iff_fibrewise_of_fibrations
    (centralEvaluation W hW) (centralEvaluation W hW) (𝟙 _) (Category.comp_id _)).mpr
  intro b
  let η := SSet.Subcomplex.mapFiber (f := centralEvaluation W hW) (f' := 𝟙 _)
    (centralEvaluation W hW) (𝟙 _) ((Category.comp_id _).trans (Category.comp_id _).symm)
      (y := b) (y' := b) rfl
  let v := SSet.stdSimplex.isTerminalObj₀.from
    (SSet.Subcomplex.fiber (𝟙 (equivalenceSubcomplex W hW : SSet.{u})) b : SSet.{u})
  let _ : IsIso v :=
    (SSet.Subcomplex.fiber_isPullback (𝟙 (equivalenceSubcomplex W hW : SSet.{u}))
        b).isIso_snd_of_isIso
  have hv : SSet.realizationWeakEquivalences v := SSet.realizationWeakEquivalences.of_isIso v
  have hc : η ≫ v = SSet.stdSimplex.isTerminalObj₀.from
      (SSet.Subcomplex.fiber (centralEvaluation W hW) b : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hs : SSet.realizationWeakEquivalences (η ≫ v) := by
    rw [hc]
    exact (selectedFibrePointTF W hW b).2
  exact SSet.realizationWeakEquivalences.of_postcomp η v hv hs

/-- The original central evaluation is a genuine Kan-Quillen trivial fibration. -/
theorem centralEvaluation_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (centralEvaluation W hW) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (centralEvaluation W hW) := centralFibration W hW
  let _ : WeakEquivalence (centralEvaluation W hW) :=
    (weakEquivalence_iff _).mpr (centralWeak W hW)
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The same selected-end evaluation has the identical native trivial-fibration class. -/
theorem decoratedEvaluation_trivialFibration (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    trivialFibrations SSet.{u} (decoratedEvaluation W hW) :=
  (trivialFibrations SSet.{u}).comp_mem _ _ (centralEvaluation_trivialFibration W hW)
    ((trivialFibrations SSet.{u}).of_isIso _)

/-- Both original evaluation arrows are full realization weak equivalences. -/
theorem evaluation_realizationWeak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (centralEvaluation W hW) ∧
      SSet.realizationWeakEquivalences (decoratedEvaluation W hW) :=
  ⟨(centralEvaluation_trivialFibration W hW).2,
    (decoratedEvaluation_trivialFibration W hW).2⟩

/-- Native Kan weakness retains every pointed homotopy map for both presentations. -/
theorem evaluation_W (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.KanComplex.W (centralEvaluation W hW) ∧ SSet.KanComplex.W (decoratedEvaluation W hW) := by
  let _ : SSet.KanComplex (mapping W) := (mappingEndpoints_kanComplex W hW).1
  let _ : SSet.KanComplex (equivalenceSubcomplex W hW : SSet.{u}) :=
    (mappingEndpoints_kanComplex W hW).2.1
  let _ : SSet.KanComplex (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) :=
    (mappingEndpoints_kanComplex W hW).2.2
  exact ⟨(SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
      (evaluation_realizationWeak W hW).1,
    (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
      (evaluation_realizationWeak W hW).2⟩

/-- Both canonical evaluation maps retain every original inner simplex operator. -/
theorem evaluation_operator (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (mapping W).map θ ≫ (centralEvaluation W hW).app n =
        (centralEvaluation W hW).app m ≫
          (equivalenceSubcomplex W hW : SSet.{u}).map θ ∧
      (mapping W).map θ ≫ (decoratedEvaluation W hW).app n =
        (decoratedEvaluation W hW).app m ≫
          (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}).map θ :=
  ⟨(centralEvaluation W hW).naturality θ, (decoratedEvaluation W hW).naturality θ⟩

/-- Both presentations retain every actual target map between the original Segal spaces. -/
theorem evaluation_naturality_target {W V : SimplicialSpace.{u}} (t : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    mappingMap t ≫ centralEvaluation V hV =
        centralEvaluation W hW ≫ equivalenceMap t hW hV ∧
      mappingMap t ≫ decoratedEvaluation V hV =
        decoratedEvaluation W hW ≫ EquivalenceMapping.targetMap t hW hV Δ[1] := by
  have hq : mappingMap t ≫ centralEvaluation V hV =
      centralEvaluation W hW ≫ equivalenceMap t hW hV := by
    apply (cancel_mono (equivalenceSubcomplex V hV).ι).mp
    simp only [Category.assoc, centralEvaluation_iota, equivalenceMap_ι,
      centralEvaluation_iota_assoc]
    exact mappingMap_central t
  refine ⟨hq, ?_⟩
  change mappingMap t ≫ (centralEvaluation V hV ≫
      (EquivalenceMapping.yonedaIsoOne V hV).inv) =
    (centralEvaluation W hW ≫ (EquivalenceMapping.yonedaIsoOne W hW).inv) ≫ _
  rw [← Category.assoc, hq, Category.assoc,
    EquivalenceMapping.yonedaIsoOne_inv_naturality_target, ← Category.assoc]

/-- Every original boundary square against the central map has both exact lift factors. -/
theorem centralEvaluation_boundary_lift (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (n : ℕ) (top : (∂Δ[n] : SSet.{u}) ⟶ mapping W)
    (bottom : (Δ[n] : SSet.{u}) ⟶ (equivalenceSubcomplex W hW : SSet.{u}))
    (sq : CommSq top (SSet.boundary n).ι (centralEvaluation W hW) bottom) :
    ∃ l : (Δ[n] : SSet.{u}) ⟶ mapping W,
      (SSet.boundary n).ι ≫ l = top ∧ l ≫ centralEvaluation W hW = bottom := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (centralEvaluation W hW) := (evaluation_fibrations W hW).1
  have hI := (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration
    (centralEvaluation W hW)).mpr (evaluation_realizationWeak W hW).1
  let _ : HasLiftingProperty (SSet.boundary n).ι (centralEvaluation W hW) := hI _ (by constructor)
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Every boundary, including zero, lifts in the same selected-end presentation. -/
theorem decoratedEvaluation_boundary_lift (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (n : ℕ) (top : (∂Δ[n] : SSet.{u}) ⟶ mapping W)
    (bottom : (Δ[n] : SSet.{u}) ⟶ (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}))
    (sq : CommSq top (SSet.boundary n).ι (decoratedEvaluation W hW) bottom) :
    ∃ l : (Δ[n] : SSet.{u}) ⟶ mapping W,
      (SSet.boundary n).ι ≫ l = top ∧ l ≫ decoratedEvaluation W hW = bottom := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Fibration (decoratedEvaluation W hW) := (evaluation_fibrations W hW).2
  have hI := (SSet.modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration
    (decoratedEvaluation W hW)).mpr (evaluation_realizationWeak W hW).2
  let _ : HasLiftingProperty (SSet.boundary n).ι (decoratedEvaluation W hW) := hI _ (by constructor)
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

private def representableValue (A : SimplicialObject SSet.{u}) (n : ℕ)
    (γ : SSet.Rezk.representable n ⟶ A) : (A.obj (op ⦋n⦌)) _⦋0⦌ :=
  (discreteYonedaIso (ofSimplicialObject.obj A) n).hom.app (op ⦋0⦌)
    (innerHomEquiv (ofSimplicialObject.obj (SSet.Rezk.representable n))
      (ofSimplicialObject.obj A) (ofSimplicialObject.map γ))

private theorem representableValue_injective (A : SimplicialObject SSet.{u}) (n : ℕ) :
    Function.Injective (representableValue A n) := by
  intro γ δ h
  have hi : Function.Injective
      ((discreteYonedaIso (ofSimplicialObject.obj A) n).hom.app (op ⦋0⦌)) :=
    (mono_iff_injective _).mp inferInstance
  have he := (innerHomEquiv (ofSimplicialObject.obj (SSet.Rezk.representable n))
    (ofSimplicialObject.obj A)).injective (hi h)
  exact congrArg (fun f => f.hom) he

open MonoidalCategory MonoidalClosed in
private theorem evaluateCurriedPoint {X Y : SSet.{u}} (p : 𝟙_ SSet.{u} ⟶ X) (f : X ⟶ Y) :
    curry' f ≫ (λ_ ((ihom X).obj Y)).inv ≫ p ▷ ((ihom X).obj Y) ≫
      (ihom.ev X).app Y = p ≫ f := by
  calc
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫ p ▷ (𝟙_ SSet.{u}) ≫ uncurry (curry' f) := by
      rw [uncurry_eq, MonoidalCategory.leftUnitor_inv_naturality_assoc,
        MonoidalCategory.whisker_exchange_assoc]
    _ = (λ_ (𝟙_ SSet.{u})).inv ≫ p ▷ (𝟙_ SSet.{u}) ≫ (ρ_ X).hom ≫ f := by
      rw [curry', uncurry_curry]
    _ = p ≫ f := by
      rw [MonoidalCategory.rightUnitor_naturality_assoc, ← unitors_equal,
        Iso.inv_hom_id_assoc]

private theorem representableValue_formula (A : SimplicialObject SSet.{u}) (n : ℕ)
    (γ : SSet.Rezk.representable n ⟶ A) :
    representableValue A n γ =
      (γ.app (op ⦋n⦌)).app (op ⦋0⦌)
        ((SSet.Rezk.representableIdentityPoint n).app (op ⦋0⦌) PUnit.unit) := by
  let : EnrichedCategory SSet.{u} SSet.{u} := MonoidalClosed.enrichedCategorySelf SSet.{u}
  let : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
    MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}
  let : ∀ X Y : SimplicialObject SSet.{u}, Enriched.FunctorCategory.HasEnrichedHom SSet.{u} X Y :=
    inferInstance
  have hπ : Enriched.FunctorCategory.homEquiv SSet.{u} γ ≫
      SSet.simplicialSpacePointwiseHomπ (SSet.Rezk.representable.{u} n) A (op ⦋n⦌) =
        MonoidalClosed.curry' (γ.app (op ⦋n⦌)) := by
    change Enriched.FunctorCategory.homEquiv SSet.{u} γ ≫
      Enriched.FunctorCategory.enrichedHomπ SSet.{u} _ _ (op ⦋n⦌) =
        eHomEquiv SSet.{u} (γ.app (op ⦋n⦌))
    exact Enriched.FunctorCategory.homEquiv_apply_π SSet.{u} γ (op ⦋n⦌)
  have hπ₀ := congrArg (fun f => f.app (op ⦋0⦌) PUnit.unit) hπ
  change (SSet.simplicialSpacePointwiseHomπ (SSet.Rezk.representable n) A (op ⦋n⦌)).app
    (op ⦋0⦌) (innerHomEquiv (ofSimplicialObject.obj (SSet.Rezk.representable n))
      (ofSimplicialObject.obj A) (ofSimplicialObject.map γ)) =
    (MonoidalClosed.curry' (γ.app (op ⦋n⦌))).app (op ⦋0⦌) PUnit.unit at hπ₀
  unfold representableValue discreteYonedaIso
  rw [SSet.Rezk.pointwiseYonedaIso_hom_projection]
  change ((MonoidalCategoryStruct.leftUnitor _).inv ≫
      MonoidalCategoryStruct.whiskerRight (SSet.Rezk.representableIdentityPoint n) _ ≫
        (ihom.ev ((SSet.Rezk.representable n).obj (op ⦋n⦌))).app (A.obj (op ⦋n⦌))).app
    (op ⦋0⦌) ((SSet.simplicialSpacePointwiseHomπ (SSet.Rezk.representable n) A (op ⦋n⦌)).app
      (op ⦋0⦌) (innerHomEquiv (ofSimplicialObject.obj (SSet.Rezk.representable n))
        (ofSimplicialObject.obj A) (ofSimplicialObject.map γ))) = _
  rw [hπ₀]
  exact congrArg (fun f => f.app (op ⦋0⦌) PUnit.unit)
    (evaluateCurriedPoint (SSet.Rezk.representableIdentityPoint n) (γ.app (op ⦋n⦌)))

private def pointAt (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : originalSource W g = x) (ht : originalTarget W g = y) :
    (mappingFibre W x y) _⦋0⦌ := by
  subst x
  subst y
  exact originalPoint W g

private theorem pointAt_projection (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) (g : (W.diagram _⦋1⦌) _⦋0⦌)
    (hs : originalSource W g = x) (ht : originalTarget W g = y) :
    (mappingFibre.fst W x y).app (op ⦋0⦌) (pointAt W x y g hs ht) = g := by
  subst x
  subst y
  exact originalPoint_projection W g

private def vertexThree (W : SimplicialSpace.{u}) (i : Fin 4)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) : (W.diagram _⦋0⦌) _⦋0⦌ :=
  (W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op).app (op ⦋0⦌) t

private def intervalThree (W : SimplicialSpace.{u}) (i j : Fin 4) (h : i ≤ j) :
    W.diagram _⦋3⦌ ⟶ W.diagram _⦋1⦌ :=
  W.diagram.map (SimplexCategory.mkOfLe i j h).op

private theorem intervalEndpoints (W : SimplicialSpace.{u})
    (i j : Fin 4) (h : i ≤ j) (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    originalSource W ((intervalThree W i j h).app (op ⦋0⦌) t) = vertexThree W i t ∧
      originalTarget W ((intervalThree W i j h).app (op ⦋0⦌) t) = vertexThree W j t := by
  constructor
  · change ((W.diagram.map (SimplexCategory.mkOfLe i j h).op ≫
      W.diagram.map (SimplexCategory.δ (1 : Fin 2)).op).app (op ⦋0⦌)) t = _
    rw [← W.diagram.map_comp, ← op_comp]
    have he : SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.mkOfLe i j h =
        SimplexCategory.const ⦋0⦌ ⦋3⦌ i := by
      ext k
      fin_cases k
      rfl
    rw [he]
    rfl
  · change ((W.diagram.map (SimplexCategory.mkOfLe i j h).op ≫
      W.diagram.map (SimplexCategory.δ (0 : Fin 2)).op).app (op ⦋0⦌)) t = _
    rw [← W.diagram.map_comp, ← op_comp]
    have he : SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.mkOfLe i j h =
        SimplexCategory.const ⦋0⦌ ⦋3⦌ j := by
      ext k
      fin_cases k
      rfl
    rw [he]
    rfl

private theorem identityEndpoints (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    originalSource W ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) = x ∧
      originalTarget W ((W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x) = x := by
  exact ⟨congrArg (fun f => f.app (op ⦋0⦌) x) (W.diagram.δ_comp_σ_succ (i := (0 : Fin 1))),
    congrArg (fun f => f.app (op ⦋0⦌) x) (W.diagram.δ_comp_σ_self (i := (0 : Fin 1)))⟩

private theorem faceInterval (W : SimplicialSpace.{u}) (i : Fin 4) (j : Fin 3)
    (a b : Fin 4) (hab : a ≤ b)
    (h : SimplexCategory.δ j ≫ SimplexCategory.δ i = SimplexCategory.mkOfLe a b hab)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (W.diagram.δ j).app (op ⦋0⦌) ((W.diagram.δ i).app (op ⦋0⦌) t) =
      (intervalThree W a b hab).app (op ⦋0⦌) t := by
  change ((W.diagram.map (SimplexCategory.δ i).op ≫
    W.diagram.map (SimplexCategory.δ j).op).app (op ⦋0⦌)) t = _
  rw [← W.diagram.map_comp, ← op_comp, h]
  rfl

private theorem inverseOuterEdges (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) (x y : (W.diagram _⦋0⦌) _⦋0⦌)
    (h02 : (intervalThree W 0 2 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x)
    (h13 : (intervalThree W 1 3 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) y)
    (h12 : IsEquivalenceEdge W hW ((intervalThree W 1 2 (by decide)).app (op ⦋0⦌) t)) :
    IsEquivalenceEdge W hW ((intervalThree W 0 1 (by decide)).app (op ⦋0⦌) t) ∧
      IsEquivalenceEdge W hW ((intervalThree W 2 3 (by decide)).app (op ⦋0⦌) t) ∧
        IsEquivalenceEdge W hW ((intervalThree W 0 3 (by decide)).app (op ⦋0⦌) t) := by
  have hv0 : vertexThree W 0 t = x :=
    (intervalEndpoints W 0 2 (by decide) t).1.symm.trans
      ((congrArg (originalSource W) h02).trans (identityEndpoints W x).1)
  have hv2 : vertexThree W 2 t = x :=
    (intervalEndpoints W 0 2 (by decide) t).2.symm.trans
      ((congrArg (originalTarget W) h02).trans (identityEndpoints W x).2)
  have hv1 : vertexThree W 1 t = y :=
    (intervalEndpoints W 1 3 (by decide) t).1.symm.trans
      ((congrArg (originalSource W) h13).trans (identityEndpoints W y).1)
  have hv3 : vertexThree W 3 t = y :=
    (intervalEndpoints W 1 3 (by decide) t).2.symm.trans
      ((congrArg (originalTarget W) h13).trans (identityEndpoints W y).2)
  let g01 := (intervalThree W 0 1 (by decide)).app (op ⦋0⦌) t
  let g12 := (intervalThree W 1 2 (by decide)).app (op ⦋0⦌) t
  let g23 := (intervalThree W 2 3 (by decide)).app (op ⦋0⦌) t
  let g03 := (intervalThree W 0 3 (by decide)).app (op ⦋0⦌) t
  have hs01 : originalSource W g01 = x := (intervalEndpoints W 0 1 (by decide) t).1.trans hv0
  have ht01 : originalTarget W g01 = y := (intervalEndpoints W 0 1 (by decide) t).2.trans hv1
  have hs12 : originalSource W g12 = y := (intervalEndpoints W 1 2 (by decide) t).1.trans hv1
  have ht12 : originalTarget W g12 = x := (intervalEndpoints W 1 2 (by decide) t).2.trans hv2
  have hs23 : originalSource W g23 = x := (intervalEndpoints W 2 3 (by decide) t).1.trans hv2
  have ht23 : originalTarget W g23 = y := (intervalEndpoints W 2 3 (by decide) t).2.trans hv3
  have hs03 : originalSource W g03 = x := (intervalEndpoints W 0 3 (by decide) t).1.trans hv0
  have ht03 : originalTarget W g03 = y := (intervalEndpoints W 0 3 (by decide) t).2.trans hv3
  let b := pointAt W x y g01 hs01 ht01
  let a := pointAt W y x g12 hs12 ht12
  let c := pointAt W x y g23 hs23 ht23
  let r := pointAt W x y g03 hs03 ht03
  have hb : (mappingFibre.fst W x y).app (op ⦋0⦌) b = g01 := pointAt_projection _ _ _ _ _ _
  have ha : (mappingFibre.fst W y x).app (op ⦋0⦌) a = g12 := pointAt_projection _ _ _ _ _ _
  have hc : (mappingFibre.fst W x y).app (op ⦋0⦌) c = g23 := pointAt_projection _ _ _ _ _ _
  have hr : (mappingFibre.fst W x y).app (op ⦋0⦌) r = g03 := pointAt_projection _ _ _ _ _ _
  have hba := compose_of_original_triangle W hW ((W.diagram.δ (3 : Fin 4)).app (op ⦋0⦌) t)
    b a (identityVertex W x)
    (hb.trans (faceInterval W 3 2 0 1 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
    (ha.trans (faceInterval W 3 0 1 2 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
    ((identityVertex_fst W x).trans
      ((faceInterval W 3 1 0 2 (by decide) (by ext k; fin_cases k <;> rfl) t).trans h02).symm)
  have hac := compose_of_original_triangle W hW ((W.diagram.δ (0 : Fin 4)).app (op ⦋0⦌) t)
    a c (identityVertex W y)
    (ha.trans (faceInterval W 0 2 1 2 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
    (hc.trans (faceInterval W 0 0 2 3 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
    ((identityVertex_fst W y).trans
      ((faceInterval W 0 1 1 3 (by decide) (by ext k; fin_cases k <;> rfl) t).trans h13).symm)
  let : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨x⟩) (SSet.π₀.mk a) :=
    (isEquivalenceEdge_iff_of_fibre W hW g12 a ha).mp h12
  let : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨x⟩)
      (SSet.π₀.mk (identityVertex W x)) :=
    (isEquivalenceEdge_iff_of_fibre W hW _ (identityVertex W x) (identityVertex_fst W x)).mp
      (identity_isEquivalenceEdge W hW x)
  let : IsIso (C := Object W hW) (X := ⟨y⟩) (Y := ⟨y⟩)
      (SSet.π₀.mk (identityVertex W y)) :=
    (isEquivalenceEdge_iff_of_fibre W hW _ (identityVertex W y) (identityVertex_fst W y)).mp
      (identity_isEquivalenceEdge W hW y)
  have hbIso : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk b) :=
    IsIso.of_isIso_fac_right (C := Object W hW) hba
  have hcIso : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk c) :=
    IsIso.of_isIso_fac_left (C := Object W hW) hac
  let _ := hbIso
  have hbr := compose_of_original_triangle W hW ((W.diagram.δ (2 : Fin 4)).app (op ⦋0⦌) t)
    b (identityVertex W y) r
    (hb.trans (faceInterval W 2 2 0 1 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
    ((identityVertex_fst W y).trans
      ((faceInterval W 2 0 1 3 (by decide) (by ext k; fin_cases k <;> rfl) t).trans h13).symm)
    (hr.trans (faceInterval W 2 1 0 3 (by decide) (by ext k; fin_cases k <;> rfl) t).symm)
  have hrIso : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk r) := by
    have hh : compose W hW (SSet.π₀.mk b) (SSet.π₀.mk (identityVertex W y)) = SSet.π₀.mk b :=
      compose_identity_right W hW _
    have hre : SSet.π₀.mk r = SSet.π₀.mk b := hbr.symm.trans hh
    rw [hre]
    exact hbIso
  exact ⟨(isEquivalenceEdge_iff_of_fibre W hW g01 b hb).mpr hbIso,
    (isEquivalenceEdge_iff_of_fibre W hW g23 c hc).mpr hcIso,
    (isEquivalenceEdge_iff_of_fibre W hW g03 r hr).mpr hrIso⟩

private theorem diagonalInterval (W : SimplicialSpace.{u}) (i : Fin 4)
    (t : (W.diagram _⦋3⦌) _⦋0⦌) :
    (intervalThree W i i le_rfl).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) (vertexThree W i t) := by
  have h : SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ ⦋3⦌ i =
      SimplexCategory.mkOfLe i i le_rfl := by
    ext k
    fin_cases k <;> rfl
  have hm : intervalThree W i i le_rfl =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op ≫ W.diagram.σ (0 : Fin 1) := by
    change W.diagram.map (SimplexCategory.mkOfLe i i le_rfl).op =
      W.diagram.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ i).op ≫
        W.diagram.map (SimplexCategory.σ (0 : Fin 1)).op
    rw [← W.diagram.map_comp, ← op_comp, h]
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, vertexThree] using
    congrArg (fun f => f.app (op ⦋0⦌) t) hm

private theorem intervalEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (z : (mapping W) _⦋0⦌) (i j : Fin 4) (hij : i ≤ j) :
    IsEquivalenceEdge W hW
      ((intervalThree W i j hij).app (op ⦋0⦌) ((toThree W).app (op ⦋0⦌) z)) := by
  let t := (toThree W).app (op ⦋0⦌) z
  let x := (toFirst W).app (op ⦋0⦌) z
  let y := (toLast W).app (op ⦋0⦌) z
  have he02 : edge02 = SimplexCategory.mkOfLe (0 : Fin 4) 2 (by decide) := by
    ext k
    fin_cases k <;> rfl
  have he13 : edge13 = SimplexCategory.mkOfLe (1 : Fin 4) 3 (by decide) := by
    ext k
    fin_cases k <;> rfl
  have h02 : (intervalThree W 0 2 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) x := by
    have h := congrArg (fun f => f.app (op ⦋0⦌) z) (toThree_edge02 W)
    simpa only [he02, intervalThree, t, x, NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  have h13 : (intervalThree W 1 3 (by decide)).app (op ⦋0⦌) t =
      (W.diagram.σ (0 : Fin 1)).app (op ⦋0⦌) y := by
    have h := congrArg (fun f => f.app (op ⦋0⦌) z) (toThree_edge13 W)
    simpa only [he13, intervalThree, t, y, NatTrans.comp_app, ConcreteCategory.comp_apply] using h
  have h12 : IsEquivalenceEdge W hW ((intervalThree W 1 2 (by decide)).app (op ⦋0⦌) t) :=
    isEquivalenceEdge_of_hasInverseData W hW _ (centralInverseData W z)
  have hout := inverseOuterEdges W hW t x y h02 h13 h12
  have hd (k : Fin 4) : IsEquivalenceEdge W hW
      ((intervalThree W k k le_rfl).app (op ⦋0⦌) t) := by
    rw [diagonalInterval]
    exact identity_isEquivalenceEdge W hW _
  have h02e : IsEquivalenceEdge W hW ((intervalThree W 0 2 (by decide)).app (op ⦋0⦌) t) := by
    rw [h02]
    exact identity_isEquivalenceEdge W hW x
  have h13e : IsEquivalenceEdge W hW ((intervalThree W 1 3 (by decide)).app (op ⦋0⦌) t) := by
    rw [h13]
    exact identity_isEquivalenceEdge W hW y
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact hout.1
  · exact h02e
  · exact hout.2.2
  · exfalso; simp at hij
  · exact hd 1
  · exact h12
  · exact h13e
  · exfalso; simp at hij
  · exfalso; simp at hij
  · exact hd 2
  · exact hout.2.1
  · exfalso; simp at hij
  · exfalso; simp at hij
  · exfalso; simp at hij
  · exact hd 3

private theorem collapseEvaluation (W : SimplicialSpace.{u})
    (k : SSet.Rezk.representable 0 ⟶ K) :
    restriction W (representableCollapse 1 ≫ k) ≫ (representableMappingIso W 1).hom =
      (restriction W k ≫ (representableMappingIso W 0).hom) ≫ W.diagram.σ (0 : Fin 1) := by
  have he : SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) :=
    Subsingleton.elim _ _
  have hc : representableCollapse.{u} 1 =
      SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1))) := by
    unfold representableCollapse
    rw [he]
  rw [restriction_comp, hc, Category.assoc, representableMappingIso_naturality, Category.assoc]
  rfl

private theorem originalEdgeEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : SSet.Rezk.representable 1 ⟶ K) (z : (mapping W) _⦋0⦌) :
    IsEquivalenceEdge W hW
      ((restriction W γ ≫ (representableMappingIso W 1).hom).app (op ⦋0⦌) z) := by
  obtain ⟨p, hp⟩ | ⟨s, hs⟩ | ⟨p, hp⟩ :=
    original_points_covered (op ⦋1⦌) (op ⦋0⦌) (representableValue K 1 γ)
  · let γ₀ := representableCollapse.{u} 1 ≫ firstInclusion
    have hv : representableValue K 1 γ₀ = (firstInclusion.app (op ⦋1⦌)).app (op ⦋0⦌) p := by
      rw [representableValue_formula]
      change (firstInclusion.app (op ⦋1⦌)).app (op ⦋0⦌)
        (((representableCollapse 1).app (op ⦋1⦌)).app (op ⦋0⦌)
          ((SSet.Rezk.representableIdentityPoint 1).app (op ⦋0⦌) PUnit.unit)) = _
      congr 1
      apply SSet.stdSimplex.objEquiv.injective
      exact Subsingleton.elim _ _
    have hγ : γ = γ₀ := representableValue_injective K 1 (hp.symm.trans hv.symm)
    rw [hγ, collapseEvaluation]
    exact identity_isEquivalenceEdge W hW _
  · let θ : ⦋1⦌ ⟶ ⦋3⦌ := SSet.stdSimplex.objEquiv s
    let γ₃ := SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map θ) ≫ threeInclusion
    have hv : representableValue K 1 γ₃ = (threeInclusion.app (op ⦋1⦌)).app (op ⦋0⦌) s := by
      rw [representableValue_formula]
      change (threeInclusion.app (op ⦋1⦌)).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌ ≫ θ)) = _
      rw [Category.id_comp]
      exact congrArg (fun q => (threeInclusion.app (op ⦋1⦌)).app (op ⦋0⦌) q)
        (Equiv.symm_apply_apply SSet.stdSimplex.objEquiv s)
    have hγ : γ = γ₃ := representableValue_injective K 1 (hs.symm.trans hv.symm)
    rw [hγ, restriction_comp, Category.assoc, representableMappingIso_naturality,
      ← Category.assoc, ← toThree_restriction]
    have he : θ = SimplexCategory.mkOfLe (θ.toOrderHom 0) (θ.toOrderHom 1)
        (θ.toOrderHom.monotone (by decide)) := by
      ext k
      fin_cases k <;> rfl
    rw [he]
    exact intervalEquivalence W hW z _ _ _
  · let γ₀ := representableCollapse.{u} 1 ≫ lastInclusion
    have hv : representableValue K 1 γ₀ = (lastInclusion.app (op ⦋1⦌)).app (op ⦋0⦌) p := by
      rw [representableValue_formula]
      change (lastInclusion.app (op ⦋1⦌)).app (op ⦋0⦌)
        (((representableCollapse 1).app (op ⦋1⦌)).app (op ⦋0⦌)
          ((SSet.Rezk.representableIdentityPoint 1).app (op ⦋0⦌) PUnit.unit)) = _
      congr 1
      apply SSet.stdSimplex.objEquiv.injective
      exact Subsingleton.elim _ _
    have hγ : γ = γ₀ := representableValue_injective K 1 (hp.symm.trans hv.symm)
    rw [hγ, collapseEvaluation]
    exact identity_isEquivalenceEdge W hW _

/-- Every original K edge evaluation lands in the same intrinsic equivalence component. -/
theorem edgeEvaluation_range (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : SSet.Rezk.representable 1 ⟶ K) :
    SSet.Subcomplex.range (restriction W γ ≫ (representableMappingIso W 1).hom) ≤
      equivalenceSubcomplex W hW := by
  intro n r hr
  obtain ⟨z, rfl⟩ := hr
  rw [mem_equivalenceSubcomplex,
    ← (restriction W γ ≫ (representableMappingIso W 1).hom).naturality_apply]
  exact originalEdgeEquivalence W hW γ _

/-- The canonical original all-edge factor, including nonmonic constant edges. -/
def edgeEvaluationLift (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : SSet.Rezk.representable 1 ⟶ K) :
    mapping W ⟶ (equivalenceSubcomplex W hW : SSet.{u}) :=
  SSet.Subcomplex.lift (restriction W γ ≫ (representableMappingIso W 1).hom)
    (edgeEvaluation_range W hW γ)

/-- The all-edge factor retains the same original edge evaluation under inclusion. -/
@[reassoc]
theorem edgeEvaluationLift_iota (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : SSet.Rezk.representable 1 ⟶ K) :
    edgeEvaluationLift W hW γ ≫ (equivalenceSubcomplex W hW).ι =
      restriction W γ ≫ (representableMappingIso W 1).hom :=
  SSet.Subcomplex.lift_ι _ _

/-- The original all-edge factor is natural at every inner simplex operator. -/
theorem edgeEvaluationLift_operator (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (γ : SSet.Rezk.representable 1 ⟶ K) {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n) :
    (mapping W).map θ ≫ (edgeEvaluationLift W hW γ).app n =
      (edgeEvaluationLift W hW γ).app m ≫ (equivalenceSubcomplex W hW : SSet.{u}).map θ :=
  (edgeEvaluationLift W hW γ).naturality θ

/-- Every original target map retains the same all-edge factor and component inclusion. -/
theorem edgeEvaluationLift_naturality_target {W V : SimplicialSpace.{u}} (t : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (γ : SSet.Rezk.representable 1 ⟶ K) :
    mappingMap t ≫ edgeEvaluationLift V hV γ =
      edgeEvaluationLift W hW γ ≫ equivalenceMap t hW hV := by
  apply (cancel_mono (equivalenceSubcomplex V hV).ι).mp
  simp only [Category.assoc, edgeEvaluationLift_iota, equivalenceMap_ι,
    edgeEvaluationLift_iota_assoc]
  have h := congrArg (fun f => f ≫ (representableMappingIso V 1).hom)
    (restriction_naturality t γ)
  simpa only [Category.assoc, representableMappingIso_target] using h

end SimplicialSpace.FiniteCompletenessMapping
