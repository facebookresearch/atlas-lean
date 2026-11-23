/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaOppositeComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaBousfieldKanSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenB
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenBComparison
public import MathlibExt.CategoryTheory.NerveOppositeNaturality
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-!
# The native left-comma Quillen-B comparison

The original left-comma realization is identified with the right comma for
`F.op` by the actual opposite functor and nerve realization reversal. The
full compact-open homotopy fiber is then transported along the original
opposite-realization square, repointed by the actual vertex equation.

The source objects have level `max u w`, the base objects level `u`, and both
Hom types level `max v w`. The original nerves have value level `max u v w`.
The old same-object/small-Hom case is the specialization `v=w=0`.
Every original comma arrow and its complete path are retained. Transition
weakness gives comparison weakness through the existing canonical right
Quillen-B theorem; no alternative comparison or category model is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial

universe u v w uOpp vOpp

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- Realized left-comma nerves identify with realized right-comma nerves for
`F.op`, by reversal followed by the opposite nerve comparison. -/
noncomputable def leftCommaRealizationIso (F : C ⥤ D) (d : Dᵒᵖ) :
    SSet.toTop.obj (nerve (StructuredArrow d.unop F)) ≅
      SSet.toTop.obj (nerve (CostructuredArrow F.op d)) :=
  (toTopReversalIso (nerve (StructuredArrow d.unop F))).symm ≪≫
    SSet.toTop.mapIso (leftCommaOppositeNerveIso.{max u w, max v w, u} F d)

/-- Realization of an opposite nerve identifies with realization of the nerve,
by the nerve–opposite comparison followed by reversal. -/
noncomputable def nerveRealizationOppositeIso (C : Type uOpp) [Category.{vOpp} C] :
    SSet.toTop.obj (nerve Cᵒᵖ) ≅ SSet.toTop.obj (nerve C) :=
  SSet.toTop.mapIso (nerveOppositeSimplicialIso C) ≪≫
    toTopReversalIso (nerve C)

/-- The actual opposite-realization isos intertwine both native common-Hom maps. -/
theorem leftCommaBaseSquare_comm (F : C ⥤ D) :
    SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op) ≫ (nerveRealizationOppositeIso D).hom =
      (nerveRealizationOppositeIso C).hom ≫ SSet.toTop.map (nerveMapCommonHom.{u, w, v} F) := by
  have hnat := nerveOppositeSimplicialIso_nerveMapCommonHom_naturality.{u, w, v} F
  have hrev := toTopReversalIso_naturality (nerveMapCommonHom.{u, w, v} F)
  simp only [nerveRealizationOppositeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← SSet.toTop.map_comp, ← hnat, SSet.toTop.map_comp,
    Category.assoc, hrev, ← Category.assoc]

/-- The base realization iso sends the opposite vertex to the vertex. -/
theorem leftCommaBaseVertex_eq {D : Type uOpp} [Category.{vOpp} D] (d : D) :
    (nerveRealizationOppositeIso D).hom
        (realizedVertex (ComposableArrows.mk₀ (op d) :
          (nerve Dᵒᵖ : SSet.{max uOpp vOpp}) _⦋0⦌)) =
      realizedVertex (ComposableArrows.mk₀ d :
        (nerve D : SSet.{max uOpp vOpp}) _⦋0⦌) := by
  have hmap : (nerveOppositeSimplicialIso D).hom.app (op ⦋0⦌)
      (ComposableArrows.mk₀ (op d)) =
      opVertex (ComposableArrows.mk₀ d) := by
    rw [nerveOppositeSimplicialIso_hom_app_mk]
    change ComposableArrows.unop (ComposableArrows.mk₀ (op d)) =
      ComposableArrows.mk₀ d
    exact ComposableArrows.ext₀ rfl
  calc (nerveRealizationOppositeIso D).hom
          (realizedVertex (ComposableArrows.mk₀ (op d) :
            (nerve Dᵒᵖ : SSet.{max uOpp vOpp}) _⦋0⦌))
        = (toTopReversalIso (nerve D)).hom
            (SSet.toTop.map (nerveOppositeSimplicialIso D).hom
              (realizedVertex (ComposableArrows.mk₀ (op d) :
                (nerve Dᵒᵖ : SSet.{max uOpp vOpp}) _⦋0⦌))) := by
          simp only [nerveRealizationOppositeIso, Iso.trans_hom,
            Functor.mapIso_hom, TopCat.comp_app]
      _ = (toTopReversalIso (nerve D)).hom
            (realizedVertex (opVertex
              (ComposableArrows.mk₀ d :
                (nerve D : SSet.{max uOpp vOpp}) _⦋0⦌))) := by
          have hnat := realizedVertex_naturality
            (nerveOppositeSimplicialIso D).hom
            (ComposableArrows.mk₀ (op d) : (nerve Dᵒᵖ : SSet.{max uOpp vOpp}) _⦋0⦌)
          rw [hmap] at hnat
          rw [← hnat]
      _ = realizedVertex (ComposableArrows.mk₀ d :
            (nerve D : SSet.{max uOpp vOpp}) _⦋0⦌) :=
          toTopReversalIso_realizedVertex (nerve D) _

/-- Left-comma transitions realize to weak equivalences exactly when the
corresponding `F.op` right-comma transitions do: the diagram iso intertwines
them up to reversal, and both sides are iso-invariant. -/
theorem leftCommaTransition_mem_weakHomotopyEquivalences_iff (F : C ⥤ D)
    {d d' : Dᵒᵖ} (g : d ⟶ d') :
    TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (StructuredArrow.map (S := d'.unop)
          (S' := d.unop) (T := F) g.unop))) ↔
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (CostructuredArrow.map (S := F.op) g))) := by
  have hnat := (leftCommaOppositeDiagramIso.{max u w, max v w, u} F).hom.naturality g
  rw [Functor.comp_map, leftCommaNerveDiagram_map, rightCommaNerveDiagram_map,
    ← Iso.app_hom, ← Iso.app_hom, leftCommaOppositeDiagramIso_app,
    leftCommaOppositeDiagramIso_app] at hnat
  have hsq : SSet.toTop.map (SimplicialObject.opFunctor.map (nerveMap
        (StructuredArrow.map (S := d'.unop) (S' := d.unop) (T := F) g.unop))) ≫
        SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d').hom =
      SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d).hom ≫
        SSet.toTop.map (nerveMap (CostructuredArrow.map (S := F.op) g)) := by
    rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
    exact congrArg SSet.toTop.map hnat
  have hR : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d').hom) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hL : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d).hom) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hrev := toTopReversal_mem_weakHomotopyEquivalences_iff
    (nerveMap (StructuredArrow.map (S := d'.unop) (S' := d.unop) (T := F) g.unop))
  constructor
  · intro h
    have hA := hrev.mpr h
    have hAR := TopCat.weakHomotopyEquivalences.comp_mem _ _ hA hR
    rw [hsq] at hAR
    exact TopCat.weakHomotopyEquivalences.of_precomp _ _ hL hAR
  · intro h
    have hLB := TopCat.weakHomotopyEquivalences.comp_mem _ _ hL h
    rw [← hsq] at hLB
    have hA := TopCat.weakHomotopyEquivalences.of_postcomp _ _ hR hLB
    exact hrev.mp hA

/-- Transport along the nerve–opposite square, repointed to the standard
vertex by `leftCommaBaseVertex_eq`. -/
noncomputable def leftCommaFiberTransport (F : C ⥤ D) (d : D) :
    TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op))
        (SSet.realizedVertex (ComposableArrows.mk₀ (op d) :
          (nerve Dᵒᵖ : SSet.{max u v w}) _⦋0⦌)) ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{max u v w}) _⦋0⦌)) :=
  (leftCommaBaseVertex_eq.{u, max v w} d) ▸
    (TopCat.homotopyFiberMapOfSquare (nerveRealizationOppositeIso C).hom
      (nerveRealizationOppositeIso D).hom (leftCommaBaseSquare_comm.{u, v, w} F)
      (SSet.realizedVertex (ComposableArrows.mk₀ (op d) :
        (nerve Dᵒᵖ : SSet.{max u v w}) _⦋0⦌)))

/-- The transported fiber map is a weak equivalence. -/
theorem leftCommaFiberTransport_mem_weakHomotopyEquivalences (F : C ⥤ D)
    (d : D) :
    TopCat.weakHomotopyEquivalences (leftCommaFiberTransport.{u, v, w} F d) := by
  unfold leftCommaFiberTransport
  exact TopCat.homotopyFiberMapOfSquare_mem_weakHomotopyEquivalences_of_basepoint_eq
    _ _ _ _ (leftCommaBaseVertex_eq.{u, max v w} d)
    (TopCat.weakHomotopyEquivalences.of_isIso _)
    (TopCat.weakHomotopyEquivalences.of_isIso _)

/-- The left-comma homotopy-fiber comparison, transported from the
`F.op` right-comma comparison along the realization iso and the fiber
transport. -/
noncomputable def leftCommaHomotopyFiberComparison (F : C ⥤ D) (d : D) :
    SSet.toTop.obj (nerve (StructuredArrow d F)) ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{max u v w}) _⦋0⦌)) :=
  (leftCommaRealizationIso.{u, v, w} F (op d)).hom ≫
    rightCommaHomotopyFiberComparison.{u, v, w} F.op (op d) ≫
      leftCommaFiberTransport.{u, v, w} F d

/-- The left-comma comparison is weak whenever every left-comma
transition realizes to a weak homotopy equivalence. -/
theorem leftCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences
    (F : C ⥤ D)
    (hF : ∀ (d d' : D) (g : d ⟶ d'),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (StructuredArrow.map (S := d) (S' := d')
          (T := F) g))))
    (d : D) :
    TopCat.weakHomotopyEquivalences (leftCommaHomotopyFiberComparison.{u, v, w} F d) := by
  have hRight : ∀ (e e' : Dᵒᵖ) (g : e ⟶ e'),
      TopCat.weakHomotopyEquivalences
        (SSet.toTop.map (nerveMap (CostructuredArrow.map (S := F.op) g))) := by
    intro e e' g
    exact (leftCommaTransition_mem_weakHomotopyEquivalences_iff.{u, v, w} F g).mp
      (hF e'.unop e.unop g.unop)
  have hRC := rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences.{
    u, v, w} F.op hRight (op d)
  have hIso : TopCat.weakHomotopyEquivalences
      (leftCommaRealizationIso.{u, v, w} F (op d)).hom :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hTr := leftCommaFiberTransport_mem_weakHomotopyEquivalences.{u, v, w} F d
  unfold leftCommaHomotopyFiberComparison
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hIso
    (TopCat.weakHomotopyEquivalences.comp_mem _ _ hRC hTr)


/-- The full left-comma path is the original opposite right-comma path transported to the base. -/
theorem leftCommaHomotopyFiberComparison_path (F : C ⥤ D) (d : D) :
    leftCommaHomotopyFiberComparison.{u, v, w} F d ≫
        TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (realizedVertex (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ d)) =
      (leftCommaRealizationIso.{u, v, w} F (op d)).hom ≫
        rightCommaHomotopyFiberComparison.{u, v, w} F.op (op d) ≫
          TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op))
            (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max u v w}))
              (ComposableArrows.mk₀ (op d))) ≫
            TopCat.pathObjectMap (nerveRealizationOppositeIso D).hom := by
  let p := SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)
  let pOp := SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op)
  let b : SSet.toTop.obj (nerve D : SSet.{max u v w}) :=
    realizedVertex (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ d)
  let bOp : SSet.toTop.obj (nerve Dᵒᵖ : SSet.{max u v w}) :=
    realizedVertex (X := (nerve Dᵒᵖ : SSet.{max u v w})) (ComposableArrows.mk₀ (op d))
  let rC := (nerveRealizationOppositeIso C).hom
  let rD := (nerveRealizationOppositeIso D).hom
  let a := (leftCommaRealizationIso.{u, v, w} F (op d)).hom
  let χ : SSet.toTop.obj (nerve (CostructuredArrow F.op (op d))) ⟶
      TopCat.homotopyFiber pOp bOp :=
    rightCommaHomotopyFiberComparison.{u, v, w} F.op (op d)
  let T : TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b :=
    leftCommaFiberTransport.{u, v, w} F d
  have hT : T ≫ TopCat.homotopyFiberPath p b =
      TopCat.homotopyFiberPath pOp bOp ≫ TopCat.pathObjectMap rD := by
    have key : ∀ {b' : SSet.toTop.obj (nerve D : SSet.{max u v w})}
        (e : rD bOp = b'),
        (e ▸ TopCat.homotopyFiberMapOfSquare rC rD
            (leftCommaBaseSquare_comm.{u, v, w} F) bOp :
          TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b') ≫
            TopCat.homotopyFiberPath p b' =
          TopCat.homotopyFiberPath pOp bOp ≫ TopCat.pathObjectMap rD := by
      intro b' e
      cases e
      exact TopCat.homotopyFiberMapOfSquare_path _ _ _ _
    exact key (leftCommaBaseVertex_eq.{u, max v w} d)
  change (a ≫ (χ ≫ T)) ≫ TopCat.homotopyFiberPath p b =
    a ≫ (χ ≫ (TopCat.homotopyFiberPath pOp bOp ≫ TopCat.pathObjectMap rD))
  calc
    (a ≫ (χ ≫ T)) ≫ TopCat.homotopyFiberPath p b =
        a ≫ ((χ ≫ T) ≫ TopCat.homotopyFiberPath p b) := Category.assoc _ _ _
    _ = a ≫ (χ ≫ (T ≫ TopCat.homotopyFiberPath p b)) :=
      congrArg (fun m : SSet.toTop.obj (nerve (CostructuredArrow F.op (op d))) ⟶
        TopCat.pathObject (SSet.toTop.obj (nerve D)) => a ≫ m)
        (Category.assoc χ T (TopCat.homotopyFiberPath p b))
    _ = a ≫ (χ ≫ (TopCat.homotopyFiberPath pOp bOp ≫ TopCat.pathObjectMap rD)) :=
      congrArg (fun m : TopCat.homotopyFiber pOp bOp ⟶
        TopCat.pathObject (SSet.toTop.obj (nerve D)) => a ≫ (χ ≫ m)) hT

/-- Every time of the carried opposite path is retained by the actual base-realization reversal. -/
theorem leftCommaHomotopyFiberComparison_path_apply (F : C ⥤ D) (d : D)
    (z : SSet.toTop.obj (nerve (StructuredArrow d F))) (t : TopCat.I.{max u v w}) :
    TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (realizedVertex (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ d))
        (leftCommaHomotopyFiberComparison.{u, v, w} F d z) t =
      (nerveRealizationOppositeIso D).hom
        (TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op))
          (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max u v w}))
            (ComposableArrows.mk₀ (op d)))
          (rightCommaHomotopyFiberComparison.{u, v, w} F.op (op d)
            ((leftCommaRealizationIso.{u, v, w} F (op d)).hom z)) t) := by
  have h := ConcreteCategory.congr_hom
    (leftCommaHomotopyFiberComparison_path.{u, v, w} F d) z
  exact congrArg (fun γ : TopCat.pathObject (SSet.toTop.obj (nerve D)) => γ t) h


/-- The native left comparison retains the original comma projection
as its exact total coordinate. -/
theorem leftCommaHomotopyFiberComparison_toTotal (F : C ⥤ D) (d : D) :
    leftCommaHomotopyFiberComparison.{u, v, w} F d ≫
        TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
          (realizedVertex (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ d)) =
      SSet.toTop.map
        (nerveMapCommonHom.{max u w, v, w} (StructuredArrow.proj d F)) := by
  let NL : SSet.{max u v w} := nerve (StructuredArrow d F)
  let NC : SSet.{max u v w} := nerve C
  let πLS : NL ⟶ NC := (leftCommaProjection.{max u w, max v w, u} F).app (op d)
  let πRS : (nerve (CostructuredArrow F.op (op d)) : SSet.{max u v w}) ⟶
      (nerve Cᵒᵖ : SSet.{max u v w}) :=
    nerveMapCommonHom.{max u w, v, w} (CostructuredArrow.proj F.op (op d))
  let O := leftCommaOppositeNerveIso.{max u w, max v w, u} F (op d)
  let cO := nerveOppositeSimplicialIso C
  let L := SSet.toTop.map πLS
  let R := SSet.toTop.map πRS
  let mO := SSet.toTop.map O.hom
  let mπOp := SSet.toTop.map (SimplicialObject.opFunctor.map πLS)
  let mCInv := SSet.toTop.map cO.inv
  let mCHom := SSet.toTop.map cO.hom
  let revL := toTopReversalIso NL
  let revC := toTopReversalIso NC
  let a := (leftCommaRealizationIso.{u, v, w} F (op d)).hom
  let rC := (nerveRealizationOppositeIso C).hom
  have hA : a = revL.inv ≫ mO := by
    simp only [a, leftCommaRealizationIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    rfl
  have hC : rC = mCHom ≫ revC.hom := by
    simp only [rC, nerveRealizationOppositeIso, Iso.trans_hom, Functor.mapIso_hom]
    rfl
  have hComp : mO ≫ R = mπOp ≫ mCInv := by
    change SSet.toTop.map O.hom ≫ SSet.toTop.map πRS =
      SSet.toTop.map (SimplicialObject.opFunctor.map πLS) ≫ SSet.toTop.map cO.inv
    have hS : O.hom ≫ πRS =
        SimplicialObject.opFunctor.map πLS ≫ cO.inv :=
      leftCommaProjectionOppositeCompatNative.{u, v, w} F (op d)
    calc
      SSet.toTop.map O.hom ≫ SSet.toTop.map πRS =
          SSet.toTop.map (O.hom ≫ πRS) := (SSet.toTop.map_comp O.hom πRS).symm
      _ = SSet.toTop.map (SimplicialObject.opFunctor.map πLS ≫ cO.inv) :=
        congrArg (fun m : SimplicialObject.opFunctor.obj NL ⟶
          (nerve Cᵒᵖ : SSet.{max u v w}) => SSet.toTop.map m) hS
      _ = SSet.toTop.map (SimplicialObject.opFunctor.map πLS) ≫
          SSet.toTop.map cO.inv :=
        SSet.toTop.map_comp (SimplicialObject.opFunctor.map πLS) cO.inv
  have hCancel : mCInv ≫ mCHom =
      𝟙 (SSet.toTop.obj (SimplicialObject.opFunctor.obj NC)) :=
    (SSet.toTop.mapIso cO).inv_hom_id
  have hRev : L ≫ revC.inv = revL.inv ≫ mπOp :=
    toTopReversalIso_inv_naturality πLS
  have hActual : a ≫ (R ≫ rC) = L := by
    calc
      a ≫ (R ≫ rC) = (a ≫ R) ≫ rC := (Category.assoc _ _ _).symm
      _ = ((revL.inv ≫ mO) ≫ R) ≫ rC := congrArg (fun m => (m ≫ R) ≫ rC) hA
      _ = (revL.inv ≫ (mO ≫ R)) ≫ rC :=
        congrArg (· ≫ rC) (Category.assoc revL.inv mO R)
      _ = (revL.inv ≫ (mπOp ≫ mCInv)) ≫ rC :=
        congrArg (fun m => (revL.inv ≫ m) ≫ rC) hComp
      _ = revL.inv ≫ ((mπOp ≫ mCInv) ≫ rC) := Category.assoc _ _ _
      _ = revL.inv ≫ ((mπOp ≫ mCInv) ≫ (mCHom ≫ revC.hom)) :=
        congrArg (fun m => revL.inv ≫ ((mπOp ≫ mCInv) ≫ m)) hC
      _ = revL.inv ≫ (mπOp ≫ (mCInv ≫ (mCHom ≫ revC.hom))) :=
        congrArg (revL.inv ≫ ·) (Category.assoc mπOp mCInv (mCHom ≫ revC.hom))
      _ = revL.inv ≫ (mπOp ≫ ((mCInv ≫ mCHom) ≫ revC.hom)) :=
        congrArg (fun m => revL.inv ≫ (mπOp ≫ m))
          (Category.assoc mCInv mCHom revC.hom).symm
      _ = revL.inv ≫ (mπOp ≫ ((𝟙 _) ≫ revC.hom)) :=
        congrArg (fun m => revL.inv ≫ (mπOp ≫ (m ≫ revC.hom))) hCancel
      _ = revL.inv ≫ (mπOp ≫ revC.hom) :=
        congrArg (fun m => revL.inv ≫ (mπOp ≫ m)) (Category.id_comp revC.hom)
      _ = (revL.inv ≫ mπOp) ≫ revC.hom := (Category.assoc _ _ _).symm
      _ = (L ≫ revC.inv) ≫ revC.hom := congrArg (· ≫ revC.hom) hRev.symm
      _ = L ≫ (revC.inv ≫ revC.hom) := Category.assoc _ _ _
      _ = L := by rw [Iso.inv_hom_id, Category.comp_id]
  let p := SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)
  let pOp := SSet.toTop.map (nerveMapCommonHom.{u, w, v} F.op)
  let b : SSet.toTop.obj (nerve D : SSet.{max u v w}) :=
    realizedVertex (X := (nerve D : SSet.{max u v w})) (ComposableArrows.mk₀ d)
  let bOp : SSet.toTop.obj (nerve Dᵒᵖ : SSet.{max u v w}) :=
    realizedVertex (X := (nerve Dᵒᵖ : SSet.{max u v w})) (ComposableArrows.mk₀ (op d))
  let rD := (nerveRealizationOppositeIso D).hom
  let χ : SSet.toTop.obj (nerve (CostructuredArrow F.op (op d))) ⟶
      TopCat.homotopyFiber pOp bOp :=
    rightCommaHomotopyFiberComparison.{u, v, w} F.op (op d)
  let T : TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b :=
    leftCommaFiberTransport.{u, v, w} F d
  have hT : T ≫ TopCat.homotopyFiberToTotal p b =
      TopCat.homotopyFiberToTotal pOp bOp ≫ rC := by
    have key : ∀ {b' : SSet.toTop.obj (nerve D : SSet.{max u v w})}
        (e : rD bOp = b'),
        (e ▸ TopCat.homotopyFiberMapOfSquare rC rD
            (leftCommaBaseSquare_comm.{u, v, w} F) bOp :
          TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b') ≫
            TopCat.homotopyFiberToTotal p b' =
          TopCat.homotopyFiberToTotal pOp bOp ≫ rC := by
      intro b' e
      cases e
      exact TopCat.homotopyFiberMapOfSquare_toTotal _ _ _ _
    exact key (leftCommaBaseVertex_eq.{u, max v w} d)
  have hχ : χ ≫ TopCat.homotopyFiberToTotal pOp bOp = R :=
    (rightCommaHomotopyFiberComparison_toTotal.{u, v, w} F.op (op d)).trans (by rfl)
  have hL : L = SSet.toTop.map
      (nerveMapCommonHom.{max u w, v, w} (StructuredArrow.proj d F)) := rfl
  change (a ≫ (χ ≫ T)) ≫ TopCat.homotopyFiberToTotal p b = _
  calc
    (a ≫ (χ ≫ T)) ≫ TopCat.homotopyFiberToTotal p b =
        a ≫ ((χ ≫ T) ≫ TopCat.homotopyFiberToTotal p b) := Category.assoc _ _ _
    _ = a ≫ (χ ≫ (T ≫ TopCat.homotopyFiberToTotal p b)) :=
      congrArg (a ≫ ·) (Category.assoc χ T (TopCat.homotopyFiberToTotal p b))
    _ = a ≫ (χ ≫ (TopCat.homotopyFiberToTotal pOp bOp ≫ rC)) :=
      congrArg (fun m => a ≫ (χ ≫ m)) hT
    _ = a ≫ ((χ ≫ TopCat.homotopyFiberToTotal pOp bOp) ≫ rC) :=
      congrArg (a ≫ ·) (Category.assoc χ (TopCat.homotopyFiberToTotal pOp bOp) rC).symm
    _ = a ≫ (R ≫ rC) := congrArg (fun m => a ≫ (m ≫ rC)) hχ
    _ = L := hActual
    _ = SSet.toTop.map
        (nerveMapCommonHom.{max u w, v, w} (StructuredArrow.proj d F)) := hL

end SSet

public section NativeEqualityComponentPath

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The actual opposite realization sends a comma vertex to its original opposite comma vertex. -/
theorem leftCommaRealizationIso_vertex (F : C ⥤ D) (d : D)
    (c : StructuredArrow d F) :
    (leftCommaRealizationIso.{u, v, w} F (op d)).hom
        (realizedVertex (ComposableArrows.mk₀ c :
          (nerve (StructuredArrow d F) : SSet.{max u v w}) _⦋0⦌)) =
      realizedVertex (ComposableArrows.mk₀
        ((StructuredArrow.toCostructuredArrow F d).obj (op c)) :
          (nerve (CostructuredArrow F.op (op d)) : SSet.{max u v w}) _⦋0⦌) := by
  let NL : SSet.{max u v w} := nerve (StructuredArrow d F)
  let cO : CostructuredArrow F.op (op d) :=
    (StructuredArrow.toCostructuredArrow F d).obj (op c)
  let eR := toTopReversalIso NL
  let eO : SimplicialObject.opFunctor.obj NL ≅
      (nerve (CostructuredArrow F.op (op d)) : SSet.{max u v w}) :=
    leftCommaOppositeNerveIso.{max u w, max v w, u} F (op d)
  have hrev : eR.inv (realizedVertex (ComposableArrows.mk₀ c : NL _⦋0⦌)) =
      realizedVertex (opVertex (ComposableArrows.mk₀ c : NL _⦋0⦌)) := by
    let y : SSet.toTop.obj (SimplicialObject.opFunctor.obj NL) :=
      realizedVertex (opVertex (ComposableArrows.mk₀ c : NL _⦋0⦌))
    have hr : eR.hom y = realizedVertex (ComposableArrows.mk₀ c : NL _⦋0⦌) :=
      toTopReversalIso_realizedVertex NL _
    have hinv := ConcreteCategory.congr_hom eR.hom_inv_id y
    change eR.inv (eR.hom y) = y at hinv
    exact (congrArg (fun z => eR.inv z) hr).symm.trans hinv
  have hmap : eO.hom.app (op ⦋0⦌)
      (opVertex (ComposableArrows.mk₀ c : NL _⦋0⦌)) =
      ComposableArrows.mk₀ cO := by
    change (leftCommaOppositeNerveIso.{max u w, max v w, u} F (op d)).hom.app
        (op ⦋0⦌) (ComposableArrows.mk₀ c) = ComposableArrows.mk₀ cO
    rw [leftCommaOppositeNerveIso_hom_app_mk]
    exact ComposableArrows.ext₀ rfl
  have hnat := (realizedVertex_naturality eO.hom
    (opVertex (ComposableArrows.mk₀ c : NL _⦋0⦌))).symm
  rw [hmap] at hnat
  change SSet.toTop.map eO.hom
      (eR.inv (realizedVertex (ComposableArrows.mk₀ c : NL _⦋0⦌))) =
    realizedVertex (ComposableArrows.mk₀ cO)
  rw [hrev]
  exact hnat

/-- An equality arrow carries the literal constant path through the original opposite transport. -/
theorem leftCommaHomotopyFiberComparison_vertex_path_const_of_hom_eqToHom
    (F : C ⥤ D) (d : D) (c : StructuredArrow d F)
    (h : d = F.obj c.right) (hc : c.hom = eqToHom h)
    (t : TopCat.I.{max u v w}) :
    TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (realizedVertex (ComposableArrows.mk₀ d :
          (nerve D : SSet.{max u v w}) _⦋0⦌))
        (leftCommaHomotopyFiberComparison.{u, v, w} F d
          (realizedVertex (ComposableArrows.mk₀ c :
            (nerve (StructuredArrow d F) : SSet.{max u v w}) _⦋0⦌))) t =
      realizedVertex (ComposableArrows.mk₀ d :
        (nerve D : SSet.{max u v w}) _⦋0⦌) := by
  let cO : CostructuredArrow F.op (op d) :=
    (StructuredArrow.toCostructuredArrow F d).obj (op c)
  have hO : F.op.obj cO.left = op d := congrArg op h.symm
  have hcO : cO.hom = eqToHom hO := by
    change c.hom.op = eqToHom (congrArg op h.symm)
    rw [hc]
    have hEq : ∀ {x y : D} (e : x = y),
        (eqToHom e).op = eqToHom (congrArg op e.symm) := by
      intro x y e
      cases e
      rfl
    exact hEq h
  have hr := rightCommaHomotopyFiberComparison_vertex_path_const_of_hom_eqToHom.{
    u, v, w} F.op (op d) cO hO hcO t
  have hl := leftCommaHomotopyFiberComparison_path_apply.{u, v, w} F d
    (realizedVertex (ComposableArrows.mk₀ c :
      (nerve (StructuredArrow d F) : SSet.{max u v w}) _⦋0⦌)) t
  rw [leftCommaRealizationIso_vertex] at hl
  exact hl.trans ((congrArg (fun z => (nerveRealizationOppositeIso D).hom z) hr).trans
    (leftCommaBaseVertex_eq.{u, max v w} d))

end SSet

end NativeEqualityComponentPath


noncomputable section

open CategoryTheory Opposite


namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

private theorem originalLeftCommaRealizationIsoHomValueComputed
    (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaRealizationIso.{u, v, w} F d).hom =
      (toTopReversalIso (nerve (StructuredArrow d.unop F))).inv ≫
        SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d).hom := rfl

/-- The whole hom is the SAME original reversal followed by the original opposite-comma nerve map.
-/
public theorem leftCommaRealizationIso_hom_value
    (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaRealizationIso.{u, v, w} F d).hom =
      (toTopReversalIso (nerve (StructuredArrow d.unop F))).inv ≫
        SSet.toTop.map (leftCommaOppositeNerveIso.{max u w, max v w, u} F d).hom :=
  originalLeftCommaRealizationIsoHomValueComputed F d

private theorem originalNerveRealizationOppositeIsoInvValueComputed
    (C : Type uOpp) [Category.{vOpp} C] :
    (nerveRealizationOppositeIso C).inv =
      (toTopReversalIso (nerve C)).inv ≫
        SSet.toTop.map (nerveOppositeSimplicialIso C).inv := rfl

/-- The whole inv is the SAME original reversal followed by the original inverse nerve-opposite map.
-/
public theorem nerveRealizationOppositeIso_inv_value
    (C : Type uOpp) [Category.{vOpp} C] :
    (nerveRealizationOppositeIso C).inv =
      (toTopReversalIso (nerve C)).inv ≫
        SSet.toTop.map (nerveOppositeSimplicialIso C).inv :=
  originalNerveRealizationOppositeIsoInvValueComputed C

end SSet

end

noncomputable section

open CategoryTheory Opposite Simplicial

universe uNative vNative wNative

namespace SSet

variable {C : Type (max uNative wNative)} {D : Type uNative}
  [Category.{max vNative wNative} C] [Category.{max vNative wNative} D]

private theorem leftCommaFiberTransportToTotalNativeComputed (F : C ⥤ D) (d : D) :
    leftCommaFiberTransport.{uNative, vNative, wNative} F d ≫
        TopCat.homotopyFiberToTotal
          (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F))
          (realizedVertex (X := (nerve D : SSet.{max uNative vNative wNative}))
            (ComposableArrows.mk₀ d)) =
      TopCat.homotopyFiberToTotal
        (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op))
        (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
          (ComposableArrows.mk₀ (op d))) ≫ (nerveRealizationOppositeIso C).hom := by
  let p := toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F)
  let pOp := toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op)
  let bOp := realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
    (ComposableArrows.mk₀ (op d))
  let rC := (nerveRealizationOppositeIso C).hom
  let rD := (nerveRealizationOppositeIso D).hom
  have key : ∀ {b' : toTop.obj (nerve D)} (e : rD bOp = b'),
      (e ▸ TopCat.homotopyFiberMapOfSquare rC rD
          (leftCommaBaseSquare_comm.{uNative, vNative, wNative} F) bOp :
        TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b') ≫
          TopCat.homotopyFiberToTotal p b' =
        TopCat.homotopyFiberToTotal pOp bOp ≫ rC := by
    intro b' e
    cases e
    exact TopCat.homotopyFiberMapOfSquare_toTotal _ _ _ _
  unfold leftCommaFiberTransport
  exact key (leftCommaBaseVertex_eq.{uNative, max vNative wNative} d)

/-- Every original total coordinate of the opposite fiber transport uses the same original iso. -/
public theorem leftCommaFiberTransportToTotalNative (F : C ⥤ D) (d : D) :
    leftCommaFiberTransport.{uNative, vNative, wNative} F d ≫
        TopCat.homotopyFiberToTotal
          (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F))
          (realizedVertex (X := (nerve D : SSet.{max uNative vNative wNative}))
            (ComposableArrows.mk₀ d)) =
      TopCat.homotopyFiberToTotal
        (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op))
        (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
          (ComposableArrows.mk₀ (op d))) ≫ (nerveRealizationOppositeIso C).hom :=
  leftCommaFiberTransportToTotalNativeComputed F d

private theorem leftCommaFiberTransportPathNativeComputed (F : C ⥤ D) (d : D) :
    leftCommaFiberTransport.{uNative, vNative, wNative} F d ≫
        TopCat.homotopyFiberPath
          (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F))
          (realizedVertex (X := (nerve D : SSet.{max uNative vNative wNative}))
            (ComposableArrows.mk₀ d)) =
      TopCat.homotopyFiberPath
        (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op))
        (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
          (ComposableArrows.mk₀ (op d))) ≫
        TopCat.pathObjectMap (nerveRealizationOppositeIso D).hom := by
  let p := toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F)
  let pOp := toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op)
  let bOp := realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
    (ComposableArrows.mk₀ (op d))
  let rC := (nerveRealizationOppositeIso C).hom
  let rD := (nerveRealizationOppositeIso D).hom
  have key : ∀ {b' : toTop.obj (nerve D)} (e : rD bOp = b'),
      (e ▸ TopCat.homotopyFiberMapOfSquare rC rD
          (leftCommaBaseSquare_comm.{uNative, vNative, wNative} F) bOp :
        TopCat.homotopyFiber pOp bOp ⟶ TopCat.homotopyFiber p b') ≫
          TopCat.homotopyFiberPath p b' =
        TopCat.homotopyFiberPath pOp bOp ≫ TopCat.pathObjectMap rD := by
    intro b' e
    cases e
    exact TopCat.homotopyFiberMapOfSquare_path _ _ _ _
  unfold leftCommaFiberTransport
  exact key (leftCommaBaseVertex_eq.{uNative, max vNative wNative} d)

/-- Every original carried curve of the opposite fiber transport uses the same original base iso. -/
public theorem leftCommaFiberTransportPathNative (F : C ⥤ D) (d : D) :
    leftCommaFiberTransport.{uNative, vNative, wNative} F d ≫
        TopCat.homotopyFiberPath
          (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F))
          (realizedVertex (X := (nerve D : SSet.{max uNative vNative wNative}))
            (ComposableArrows.mk₀ d)) =
      TopCat.homotopyFiberPath
        (toTop.map (nerveMapCommonHom.{uNative, wNative, vNative} F.op))
        (realizedVertex (X := (nerve Dᵒᵖ : SSet.{max uNative vNative wNative}))
          (ComposableArrows.mk₀ (op d))) ≫
        TopCat.pathObjectMap (nerveRealizationOppositeIso D).hom :=
  leftCommaFiberTransportPathNativeComputed F d

private theorem leftCommaHomotopyFiberComparisonFactoryValueNativeComputed
    (F : C ⥤ D) (d : D) :
    leftCommaHomotopyFiberComparison.{uNative, vNative, wNative} F d =
      (leftCommaRealizationIso.{uNative, vNative, wNative} F (op d)).hom ≫
        rightCommaHomotopyFiberComparison.{uNative, vNative, wNative} F.op (op d) ≫
          leftCommaFiberTransport.{uNative, vNative, wNative} F d := rfl

/-- The complete original left comparison is the same published opposite and reversal factory. -/
public theorem leftCommaHomotopyFiberComparisonFactoryValueNative (F : C ⥤ D) (d : D) :
    leftCommaHomotopyFiberComparison.{uNative, vNative, wNative} F d =
      (leftCommaRealizationIso.{uNative, vNative, wNative} F (op d)).hom ≫
        rightCommaHomotopyFiberComparison.{uNative, vNative, wNative} F.op (op d) ≫
          leftCommaFiberTransport.{uNative, vNative, wNative} F d :=
  leftCommaHomotopyFiberComparisonFactoryValueNativeComputed F d

end SSet

end
