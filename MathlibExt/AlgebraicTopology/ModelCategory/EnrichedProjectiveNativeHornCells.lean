/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorPushout
public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjective
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHWeakHomotopyTransfiniteClosed
public import MathlibExt.CategoryTheory.SmallObject.AdjointFamilyCells
public import MathlibExt.CategoryTheory.SmallObject.SelectiveMapping
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# The actual evaluated native free-J endpoint

Literal free-image labels are normalized without changing the original chain.
Evaluation retains the full enriched Hom coefficient. Actual costar horn
arrows are transported through complete Arrow equality, and both original
attaching cofans provide the actual weak-and-closed successor. Only the
continuous endpoint witness is forgotten to native CGWH, whose unconditional
closed-chain theorem gives the exact original evaluated endpoint.

The original cardinal and caller bottom are retained. No target model,
supplied hCells, coefficient cofibrancy, ordinary index or NoMaxOrder is
assumed. The public endpoint theorem supplies the native projective
construction with acyclicity of the original evaluated free-J cells.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v uA
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativeHornCells


/-- Fix the original family projection before binding a different caller bottom.
Only the property is extracted; the supplied chain still uses its caller bottom. -/
abbrev nativeJ : MorphismProperty PointedCGWH.{u, v} :=
  PointedCGWH.cofibrantGenerationData.{u, v}.J

variable {A : Type uA} [EnrichedCategory PointedCGWH.{u, v} A]
variable [OrderBot (realizedGeneratorCardinal.{v}).ord.ToType]


/-- A horn dimension, a missing face, and the pointed scalar used to tensor that horn. -/
abbrev HornLabel := Σ n : ℕ, Fin (n + 2) × PointedCGWH.{u, v}

/-- The horn inclusion tensored with its selected pointed scalar. -/
def hornTensorFamily (p : HornLabel.{u, v}) :
    (Under.costar CGWH.point).obj
        (SSet.toCGWHOfFinite (SSet.horn.{v} (p.1 + 1) p.2.1)) ⊗ p.2.2 ⟶
      (Under.costar CGWH.point).obj
        (SSet.toCGWHOfFinite (Δ[p.1 + 1] : SSet.{v})) ⊗ p.2.2 :=
  (Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} p.1 p.2.1) ⊗ₘ
    𝟙 p.2.2

omit [OrderBot (realizedGeneratorCardinal.{v}).ord.ToType] in
private theorem evaluatedFreeJArrow_exists (b : A) (q : A × nativeJ.{u, v}.toSet) :
    ∃ (n : ℕ) (i : Fin (n + 2)),
      Arrow.mk ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b).map
        ((EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom)) =
      Arrow.mk ((Under.costar CGWH.point).map
        (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 (q.1 ⟶[PointedCGWH.{u, v}] b)) := by
  have actual {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (hf : nativeJ.{u, v} f) :
      ∃ (n : ℕ) (i : Fin (n + 2)),
        Arrow.mk ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b).map
          ((EnrichedFunctorCat.Free.functor q.1).map f)) =
        Arrow.mk ((Under.costar CGWH.point).map
          (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 (q.1 ⟶[PointedCGWH.{u, v}] b)) := by
    change (CGWH.realizedHornInclusions.{u, v}.strictMap (Under.costar CGWH.point)) f at hf
    cases hf with
    | map h =>
        change (⨆ n : ℕ, MorphismProperty.ofHoms
          (fun i : Fin (n + 2) => CGWH.realizedHornInclusion.{v, u} n i)) _ at h
        obtain ⟨n, hn⟩ := (MorphismProperty.iSup_iff _ _).1 h
        obtain ⟨i⟩ := hn
        refine ⟨n, i, ?_⟩
        change Arrow.mk (EnrichedFunctorCat.component
          (EnrichedFunctorCat.Free.coefficientMap q.1 _) b) = _
        rw [EnrichedFunctorCat.Free.coefficientMap_component, tensorHom_id]
  exact actual q.2.1.hom q.2.2

/-- The horn label representing an evaluated native generating acyclic cofibration. -/
def evaluatedLabel (b : A) (q : A × (nativeJ.{u, v}).toSet) : HornLabel.{u, v} :=
  let h : ∃ (n : ℕ) (i : Fin (n + 2)),
      Arrow.mk ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b).map
        ((EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom)) =
      Arrow.mk ((Under.costar CGWH.point).map
        (CGWH.realizedHornInclusion.{v, u} n i) ⊗ₘ 𝟙 (q.1 ⟶[PointedCGWH.{u, v}] b)) := by
    exact evaluatedFreeJArrow_exists b q
  ⟨h.choose, h.choose_spec.choose, q.1 ⟶[PointedCGWH.{u, v}] b⟩

/-- The arrow isomorphism identifying an evaluated generator with its horn tensor. -/
def evaluatedArrowIso (b : A) (q : A × (nativeJ.{u, v}).toSet) :
    Arrow.mk ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b).map
      ((EnrichedFunctorCat.Free.functor q.1).map q.2.1.hom)) ≅
      Arrow.mk (hornTensorFamily (evaluatedLabel b q)) :=
  eqToIso (by exact (evaluatedFreeJArrow_exists b q).choose_spec.choose_spec)

/-- The actual evaluated free-J complex with only the literal horn labels changed. -/
def evaluatedComplex (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    RelativeCellComplex.{v} (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) =>
      hornTensorFamily)
      ((EnrichedFunctorCat.evaluation b).map f) := by
  let L : A → PointedCGWH.{u, v} ⥤ (EnrichedFunctorCat PointedCGWH.{u, v} A) := fun a =>
    EnrichedFunctorCat.Free.functor a
  let E := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b
  let cn := c.adjointFamilyCellTypes L (nativeJ.{u, v})
  let _ : PreservesWellOrderContinuousOfShape (realizedGeneratorCardinal.{v}).ord.ToType E :=
    ⟨fun _ _ => inferInstance⟩
  let cm := cn.map E
  exact
    { toTransfiniteCompositionOfShape := cm.toTransfiniteCompositionOfShape
      attachCells := fun t ht =>
        (cm.attachCells t ht).reindexCellTypes hornTensorFamily
          (evaluatedLabel b) (evaluatedArrowIso b) }

/-- The complete original diagram is retained under the actual evaluation. -/
theorem evaluatedComplex_F (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (evaluatedComplex b f c).F = c.F ⋙ EnrichedFunctorCat.evaluation b := rfl

/-- Every original diagram map is retained under the actual evaluation. -/
theorem evaluatedComplex_map (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f)
    {s t : (realizedGeneratorCardinal.{v}).ord.ToType} (φ : s ⟶ t) :
    (evaluatedComplex b f c).F.map φ =
      (EnrichedFunctorCat.evaluation b).map (c.F.map φ) := rfl

/-- The original supplied-bottom isomorphism is retained under evaluation. -/
theorem evaluatedComplex_isoBot (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X
  ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (evaluatedComplex b f c).isoBot = (EnrichedFunctorCat.evaluation b).mapIso c.isoBot := rfl

/-- The original endpoint inclusion is retained through the genuine const-comp map. -/
theorem evaluatedComplex_incl (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) (t : (realizedGeneratorCardinal.{v}).ord.ToType) :
    (evaluatedComplex b f c).incl.app t =
      (EnrichedFunctorCat.evaluation b).map (c.incl.app t) := by
  change (EnrichedFunctorCat.evaluation b).map (c.incl.app t) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The original evaluated endpoint equation is kept, not replaced by another colimit arrow. -/
theorem evaluatedComplex_fac (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (evaluatedComplex b f c).isoBot.inv ≫ (evaluatedComplex b f c).incl.app ⊥ =
      (EnrichedFunctorCat.evaluation b).map f :=
  (evaluatedComplex b f c).fac

private theorem evaluatedSuccessor (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f
  : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f)
    (t : (realizedGeneratorCardinal.{v}).ord.ToType) (ht : ¬ IsMax t) :
    CGWH.weakHomotopyEquivalences
        ((evaluatedComplex b f c).F.map (homOfLE (Order.le_succ t))).right ∧
      IsClosedEmbedding (ConcreteCategory.hom
        ((evaluatedComplex b f c).F.map (homOfLE (Order.le_succ t))).right) := by
  let a := (evaluatedComplex b f c).attachCells t ht
  let n : a.ι → ℕ := fun j => (a.π j).1
  let i : ∀ j, Fin (n j + 2) := fun j => (a.π j).2.1
  let K : a.ι → PointedCGWH.{u, v} := fun j => (a.π j).2.2
  have hm : ∀ j, a.cofan₁.inj j ≫ a.m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n j) (i j)) ⊗ₘ
        𝟙 (K j)) ≫ a.cofan₂.inj j := a.hm
  exact
    ⟨PointedCGWH.freePointHornTensorCofan_cobaseChange_mem_weakHomotopyEquivalences
      a.ι n i K a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂ a.m hm a.isPushout.flip,
    PointedCGWH.freePointHornTensorCofan_cobaseChange_isClosedEmbedding
      a.ι n i K a.cofan₁ a.cofan₂ a.isColimit₁ a.isColimit₂ a.m hm a.isPushout.flip⟩

/-- The original continuous evaluated endpoint after forgetting only the selected point. -/
def underlyingClosedComposition (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)} (f : X
  ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (CGWH.weakHomotopyEquivalences ⊓
      TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop).TransfiniteCompositionOfShape
        (realizedGeneratorCardinal.{v}).ord.ToType
        (PointedCGWH.pointedToCGWH.map ((EnrichedFunctorCat.evaluation b).map f)) := by
  let cm := evaluatedComplex b f c
  let U := PointedCGWH.pointedToCGWH.{u, v}
  let _ : IsFiltered (realizedGeneratorCardinal.{v}).ord.ToType := inferInstance
  let _ : PreservesColimit cm.F U := inferInstance
  let hLimit (m : (realizedGeneratorCardinal.{v}).ord.ToType) (hm : Order.IsSuccLimit m) :
      PreservesColimit ((Set.principalSegIio m).monotone.functor ⋙ cm.F) U := by
    let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let _ : OrderBot (Set.Iio m) :=
      { bot := ⟨⊥, hm.bot_lt⟩,
        bot_le := fun x => show (⊥ : (realizedGeneratorCardinal.{v}).ord.ToType) ≤ x.1 from bot_le }
    let _ : IsFiltered (Set.Iio m) := inferInstance
    infer_instance
  let original := cm.toTransfiniteCompositionOfShape.mapOfPreserves U hLimit
  exact
    { toTransfiniteCompositionOfShape := original
      map_mem := fun t ht => by exact evaluatedSuccessor b f c t ht }

/-- The whole original diagram and every mapped successor/limit map remain unchanged. -/
theorem underlyingClosedComposition_F (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)}
  (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (underlyingClosedComposition b f c).F =
      c.F ⋙ EnrichedFunctorCat.evaluation b ⋙ PointedCGWH.pointedToCGWH := rfl


/-- Every original diagram map is retained after evaluation and point forgetting. -/
theorem underlyingClosedComposition_map (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v}
  A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f)
    {s t : (realizedGeneratorCardinal.{v}).ord.ToType} (φ : s ⟶ t) :
    (underlyingClosedComposition b f c).F.map φ =
      PointedCGWH.pointedToCGWH.map
        ((EnrichedFunctorCat.evaluation b).map (c.F.map φ)) := rfl

/-- The mapped isomorphism at the SAME caller bottom is the original one. -/
theorem underlyingClosedComposition_isoBot (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v}
  A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (underlyingClosedComposition b f c).isoBot =
      PointedCGWH.pointedToCGWH.mapIso ((EnrichedFunctorCat.evaluation b).mapIso c.isoBot) :=
  rfl

/-- The original endpoint cocone leg is retained after both actual functors. -/
theorem underlyingClosedComposition_incl (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v}
  A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) (t : (realizedGeneratorCardinal.{v}).ord.ToType) :
    (underlyingClosedComposition b f c).incl.app t =
      PointedCGWH.pointedToCGWH.map
        ((EnrichedFunctorCat.evaluation b).map (c.incl.app t)) := by
  change PointedCGWH.pointedToCGWH.map ((evaluatedComplex b f c).incl.app t) ≫ 𝟙 _ = _
  rw [Category.comp_id, evaluatedComplex_incl]

/-- The mapped original endpoint equation factors precisely the original evaluated map. -/
theorem underlyingClosedComposition_fac (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v}
  A)} (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    (underlyingClosedComposition b f c).isoBot.inv ≫
        (underlyingClosedComposition b f c).incl.app ⊥ =
      PointedCGWH.pointedToCGWH.map ((EnrichedFunctorCat.evaluation b).map f) :=
  (underlyingClosedComposition b f c).fac

/-- The original endpoint after evaluation is weak, using native unconditional closed closure. -/
theorem endpoint_mem_weakEquivalences (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)}
  (f : X ⟶ Y)
    (c : RelativeCellComplex.{v}
      (fun (_ : (realizedGeneratorCardinal.{v}).ord.ToType) => (EnrichedProjective.generators (A
        := A) nativeJ.{u, v}).homFamily) f) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation b).map f) := by
  let E := EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v}) b
  have h : CGWH.weakHomotopyEquivalences (PointedCGWH.pointedToCGWH.map (E.map f)) :=
    CGWH.weakHomotopyEquivalences.of_transfiniteComposition_closed.{u, v, v}
      (underlyingClosedComposition b f c)
  apply (HomotopicalAlgebra.weakEquivalence_iff (E.map f)).1
  apply (PointedCGWH.weakEquivalence_iff (E.map f)).2
  exact (HomotopicalAlgebra.weakEquivalence_iff (E.map f).right).2 h

local instance : Fact (realizedGeneratorCardinal.{v}).IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal.{v}⟩

/-- The actual same-cardinal small-object inclusion is weak at every genuine evaluation. -/
theorem smallObject_ιObj_mem_weakEquivalences
    [(EnrichedProjective.generators (A := A) nativeJ.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v}] (b : A) {X Y : (EnrichedFunctorCat PointedCGWH.{u, v} A)}
      (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation b).map (SmallObject.ιObj
      (EnrichedProjective.generators (A := A) nativeJ.{u, v}) realizedGeneratorCardinal.{v} f)) :=
  endpoint_mem_weakEquivalences b (SmallObject.ιObj (EnrichedProjective.generators (A := A)
    nativeJ.{u, v}) realizedGeneratorCardinal.{v} f)
    (SmallObject.relativeCellComplexιObj (EnrichedProjective.generators (A := A) nativeJ.{u, v})
      realizedGeneratorCardinal.{v} f)

/-- The exact same-realizedGeneratorCardinal.{v} factorization data retains that original weak
  left arrow. -/
theorem originalFactorization_i_mem_weakEquivalences
    [(EnrichedProjective.generators (A := A) nativeJ.{u, v}).IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v}] (b : A) (f : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)) :
    weakEquivalences PointedCGWH.{u, v} ((EnrichedFunctorCat.evaluation b).map
      ((SmallObject.functorialFactorizationData (EnrichedProjective.generators (A := A)
        nativeJ.{u, v}) realizedGeneratorCardinal.{v}).i.app f)) :=
  smallObject_ιObj_mem_weakEquivalences b f.hom

end HomotopicalAlgebra.EnrichedProjective.NativeHornCells
