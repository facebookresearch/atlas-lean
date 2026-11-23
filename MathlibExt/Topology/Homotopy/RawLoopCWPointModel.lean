/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.BasedPolyhedralReplacement
public import MathlibExt.Topology.CWComplex.UniverseLift
public import MathlibExt.Topology.Homotopy.BasedLoopCWType
import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricRealization
import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricLoopSingularCWPointModel

/-!
# Based CW point models of raw loop spaces

Standard point NDR data and a specified based Hausdorff classical CW model give
an actual classical CW model of the entire raw compact-open loop space. Its
point is an actual zero-cell. Both comparison maps and inverse homotopies
preserve the literal constant loop and the chosen model point.

The original space and its given CW model may live in independent universes.
The construction applies to all loop components. Standard neighborhood
deformation data at the constant loop is induced from the original point data.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped unitInterval Simplicial

universe u v w z

namespace RawLoopCWPointModelConstruction

private abbrev pointedAt (A : TopCat.{u}) (a : A) : PointedTopCat.{u} :=
  { left := Discrete.mk PUnit.unit
    right := A
    hom := TopCat.const (X := TopCat.of PUnit) a }

private def pointedMap {A B : PointedTopCat.{u}} (f : C(A.right, B.right))
    (hf : f (A.hom PUnit.unit) = B.hom PUnit.unit) : A ⟶ B :=
  Under.homMk (TopCat.ofHom f) (by
    apply TopCat.ext
    intro p
    cases p
    exact hf)

private def pairHomotopyOfPointRel {A B : PointedTopCat.{u}} {f g : A ⟶ B}
    (H : ContinuousMap.HomotopyRel f.right.hom g.right.hom {A.hom PUnit.unit}) :
    TopPair.Homotopy (PointedTopCat.pointedPair.map f)
      (PointedTopCat.pointedPair.map g) where
  fst := H.toHomotopy
  snd := TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit))
  w := by
    apply TopCat.ext
    intro ⟨p, t⟩
    change H (TopCat.I.homeomorph t, A.hom p) = B.hom p
    cases p
    exact (H.eq_fst (TopCat.I.homeomorph t) (Set.mem_singleton_iff.mpr rfl)).trans
      (PointedTopCat.map_basepoint f)

private def pointPairEquiv {A B : PointedTopCat.{u}}
    (f : C(A.right, B.right)) (g : C(B.right, A.right))
    (hf : f (A.hom PUnit.unit) = B.hom PUnit.unit)
    (hg : g (B.hom PUnit.unit) = A.hom PUnit.unit)
    (HA : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id A.right)
      {A.hom PUnit.unit})
    (HB : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id B.right)
      {B.hom PUnit.unit}) :
    TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B) := by
  let fp : A ⟶ B := pointedMap f hf
  let gp : B ⟶ A := pointedMap g hg
  let HA' : ContinuousMap.HomotopyRel (fp ≫ gp).right.hom
      (𝟙 A : A ⟶ A).right.hom {A.hom PUnit.unit} := by
    simpa only [Under.comp_right, Under.id_right, fp, gp, pointedMap,
      Under.homMk_right, TopCat.hom_comp, TopCat.hom_id, TopCat.hom_ofHom] using HA
  let HB' : ContinuousMap.HomotopyRel (gp ≫ fp).right.hom
      (𝟙 B : B ⟶ B).right.hom {B.hom PUnit.unit} := by
    simpa only [Under.comp_right, Under.id_right, fp, gp, pointedMap,
      Under.homMk_right, TopCat.hom_comp, TopCat.hom_id, TopCat.hom_ofHom] using HB
  have hIdA : PointedTopCat.pointedPair.map (𝟙 A) =
      𝟙 (PointedTopCat.pointedPair.obj A) := PointedTopCat.pointedPair.map_id A
  have hIdB : PointedTopCat.pointedPair.map (𝟙 B) =
      𝟙 (PointedTopCat.pointedPair.obj B) := PointedTopCat.pointedPair.map_id B
  refine
    { hom := PointedTopCat.pointedPair.map fp
      inv := PointedTopCat.pointedPair.map gp
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · simpa only [Functor.map_comp, hIdA] using
      (pairHomotopyOfPointRel HA')
  · simpa only [Functor.map_comp, hIdB] using
      (pairHomotopyOfPointRel HB')

private theorem pairMap_point {A B : PointedTopCat.{u}}
    (f : PointedTopCat.pointedPair.obj A ⟶ PointedTopCat.pointedPair.obj B) :
    (TopPair.Hom.fst f) (A.hom PUnit.unit) = B.hom PUnit.unit := by
  have h := TopPair.Hom.w_apply f PUnit.unit
  change B.hom ((TopPair.Hom.snd f) PUnit.unit) =
    (TopPair.Hom.fst f) (A.hom PUnit.unit) at h
  have hp : (TopPair.Hom.snd f) PUnit.unit = PUnit.unit :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  rw [hp] at h
  exact h.symm

private def pointRelOfPairHomotopy {A B : PointedTopCat.{u}}
    {f g : PointedTopCat.pointedPair.obj A ⟶ PointedTopCat.pointedPair.obj B}
    (H : TopPair.Homotopy f g) :
    ContinuousMap.HomotopyRel (TopPair.Hom.fst f).hom (TopPair.Hom.fst g).hom
      {A.hom PUnit.unit} where
  toHomotopy := H.fst
  prop' t a ha := by
    obtain rfl := Set.mem_singleton_iff.mp ha
    have h := H.w_apply' PUnit.unit t
    change H.fst (t, A.hom PUnit.unit) =
      B.hom (H.snd (t, PUnit.unit)) at h
    have hp : H.snd (t, PUnit.unit) = PUnit.unit :=
      Subsingleton.elim (α := PUnit.{u + 1}) _ _
    rw [hp] at h
    exact h.trans (pairMap_point f).symm

private def pairForward {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) : C(A.right, B.right) :=
  (TopPair.Hom.fst e.hom).hom

private def pairBackward {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) : C(B.right, A.right) :=
  (TopPair.Hom.fst e.inv).hom

private theorem pairForward_point {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) :
    pairForward e (A.hom PUnit.unit) = B.hom PUnit.unit := pairMap_point e.hom

private theorem pairBackward_point {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) :
    pairBackward e (B.hom PUnit.unit) = A.hom PUnit.unit := pairMap_point e.inv

private def pairLeftHomotopy {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) :
    ContinuousMap.HomotopyRel ((pairBackward e).comp (pairForward e))
      (ContinuousMap.id A.right) {A.hom PUnit.unit} := by
  let H := pointRelOfPairHomotopy e.homotopyHomInvId
  exact H.cast (by rfl) (by rfl)

private def pairRightHomotopy {A B : PointedTopCat.{u}}
    (e : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj A)
      (PointedTopCat.pointedPair.obj B)) :
    ContinuousMap.HomotopyRel ((pairForward e).comp (pairBackward e))
      (ContinuousMap.id B.right) {B.hom PUnit.unit} := by
  let H := pointRelOfPairHomotopy e.homotopyInvHomId
  exact H.cast (by rfl) (by rfl)

/-! ## Continuous lift and point-relative transport across universes -/

private def liftUp (A : Type u) [TopologicalSpace A] : C(A, ULift.{v} A) :=
  ⟨ULift.up, continuous_uliftUp⟩

private def liftDown (A : Type u) [TopologicalSpace A] : C(ULift.{v} A, A) :=
  ⟨ULift.down, continuous_uliftDown⟩

private def whiskerAtPoint {A : Type u} {B : Type v} {Z : Type w} {T : Type z}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace T]
    {f g : C(A, B)} (a : A) (H : ContinuousMap.HomotopyRel f g {a})
    (p : C(Z, A)) (q : C(B, T)) (z₀ : Z) (hp : p z₀ = a) :
    ContinuousMap.HomotopyRel (q.comp (f.comp p)) (q.comp (g.comp p)) {z₀} where
  toHomotopy := (ContinuousMap.Homotopy.refl q).comp
    (H.toHomotopy.compContinuousMap p)
  prop' t z' hz' := by
    have hz : z' = z₀ := Set.mem_singleton_iff.mp hz'
    subst z'
    change q (H (t, p z₀)) = q (f (p z₀))
    rw [hp]
    exact congrArg q (H.eq_fst t (Set.mem_singleton_iff.mpr rfl))

private def loopUp (A : Type u) [TopologicalSpace A] (a : A) :
    C(LoopSpace A a, LoopSpace (ULift.{v} A) (ULift.up a)) :=
  ContinuousMap.strictLoopMap (liftUp A) a

private def loopDown (A : Type u) [TopologicalSpace A] (a : A) :
    C(LoopSpace (ULift.{v} A) (ULift.up a), LoopSpace A a) :=
  ContinuousMap.strictLoopMap (liftDown A) (ULift.up a)

private theorem loopDown_up (A : Type u) [TopologicalSpace A] (a : A)
    (gamma : LoopSpace A a) : loopDown A a (loopUp A a gamma) = gamma := by
  apply Path.ext
  funext t
  rfl

private theorem loopUp_down (A : Type u) [TopologicalSpace A] (a : A)
    (gamma : LoopSpace (ULift.{v} A) (ULift.up a)) :
    loopUp A a (loopDown A a gamma) = gamma := by
  apply Path.ext
  funext t
  exact ULift.up_down (gamma t)

private theorem loopUp_refl (A : Type u) [TopologicalSpace A] (a : A) :
    loopUp A a (Path.refl a) = Path.refl (ULift.up a) :=
  ContinuousMap.strictLoopMap_refl (liftUp A) a

private theorem loopDown_refl (A : Type u) [TopologicalSpace A] (a : A) :
    loopDown A a (Path.refl (ULift.up a)) = Path.refl a :=
  ContinuousMap.strictLoopMap_refl (liftDown A) (ULift.up a)

end RawLoopCWPointModelConstruction

open RawLoopCWPointModelConstruction

namespace PointedTopCat

/-- A Hausdorff classical CW point model of all raw loops, with actual maps,
both chosen point-relative inverse families and constant-loop standard NDR data. -/
public structure RawLoopCWPointModelData (X : PointedTopCat.{u}) where
  /-- The constructed space modeling the entire raw compact-open loop space. -/
  model : TopCat.{v}
  /-- The selected classical CW structure on the model. -/
  cw : Topology.CWComplex (Set.univ : Set model)
  /-- Hausdorffness of the constructed CW model. -/
  hausdorff : T2Space model
  /-- The model point corresponding to the literal original constant loop. -/
  point : model
  /-- An actual zero-cell of the selected model CW structure. -/
  zeroCell : cw.cell 0
  /-- The zero-cell characteristic map is the model point in every coordinate. -/
  zeroCell_value : ∀ q : Fin 0 → ℝ, cw.map 0 zeroCell q = point
  /-- The actual continuous map from all original based loops to the CW model. -/
  toModel : C(LoopSpace X.right (X.hom PUnit.unit), model)
  /-- The actual continuous return map to the original raw based loop space. -/
  fromModel : C(model, LoopSpace X.right (X.hom PUnit.unit))
  /-- The forward map sends the literal constant loop to the model point. -/
  toModel_point : toModel (Path.refl (X.hom PUnit.unit)) = point
  /-- The return map sends the model point to the literal original constant loop. -/
  fromModel_point : fromModel point = Path.refl (X.hom PUnit.unit)
  /-- The original-side inverse family, fixed at the constant loop for all times. -/
  originalHomotopy : ContinuousMap.HomotopyRel (fromModel.comp toModel)
    (ContinuousMap.id (LoopSpace X.right (X.hom PUnit.unit)))
    {Path.refl (X.hom PUnit.unit)}
  /-- The model-side inverse family, fixed at the model point for all times. -/
  modelHomotopy : ContinuousMap.HomotopyRel (toModel.comp fromModel)
    (ContinuousMap.id model) {point}
  /-- Standard neighborhood deformation data at the original constant loop. -/
  constantLoopNDR : TopPair.StandardNDRData (PointedTopCat.loopPair X)

/-- Construct the based CW point model from a specified based CW equivalence.
The given model has its selected zero-cell; the original carrier needs only its
standard point NDR data. The two carrier universes remain independent. -/
public def rawLoopCWPointModel (X : PointedTopCat.{u})
    (dX : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj X))
    (C : TopCat.{v}) [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (c : C) (j : Topology.CWComplex.cell (Set.univ : Set C) 0)
    (hj : Topology.CWComplex.map (C := (Set.univ : Set C)) 0 j ![] = c)
    (r : C(X.right, C)) (s : C(C, X.right))
    (hr : r (X.hom PUnit.unit) = c) (hs : s c = X.hom PUnit.unit)
    (HX : ContinuousMap.HomotopyRel (s.comp r) (ContinuousMap.id X.right)
      {X.hom PUnit.unit})
    (HC : ContinuousMap.HomotopyRel (r.comp s) (ContinuousMap.id C) {c}) :
    RawLoopCWPointModelData.{u, max u v} X := by
  classical
  let x : X.right := X.hom PUnit.unit
  let BX : TopCat.{max u v} := TopCat.of (ULift.{v} X.right)
  let AC : TopCat.{max u v} := TopCat.of (ULift.{u} C)
  let upX : C(X.right, BX) := liftUp.{u, v} X.right
  let downX : C(BX, X.right) := liftDown.{u, v} X.right
  let upC : C(C, AC) := liftUp.{v, u} C
  let downC : C(AC, C) := liftDown.{v, u} C
  let xU : BX := upX x
  letI : Topology.CWComplex (Set.univ : Set AC) := Topology.CWComplex.uliftCWComplex.{v, u} C
  have zeroLift : ∃ jU : (Topology.CWComplex.uliftCWComplex.{v, u} C).cell 0,
      ∀ q : Fin 0 → ℝ, (Topology.CWComplex.uliftCWComplex.{v, u} C).map 0 jU q = upC c := by
    exact Topology.CWComplex.uliftCWComplex_zeroCell.{v, u} C c j hj
  let jU : Topology.CWComplex.cell (Set.univ : Set AC) 0 := Classical.choose zeroLift
  have hjU : ∀ q : Fin 0 → ℝ,
      Topology.CWComplex.map (C := (Set.univ : Set AC)) 0 jU q = upC c := by
    exact Classical.choose_spec zeroLift
  let aCW : AC := Topology.CWComplex.map (C := (Set.univ : Set AC)) 0 jU 0
  have haCW : aCW = upC c := hjU 0
  -- Transport the given based CW equivalence to the common universe.
  let F : C(BX, AC) := upC.comp (r.comp downX)
  let G : C(AC, BX) := upX.comp (s.comp downC)
  have hF : F xU = aCW := by
    change upC (r x) = aCW
    exact (congrArg upC hr).trans haCW.symm
  have hG : G aCW = xU := by
    rw [haCW]
    change upX (s c) = upX x
    exact congrArg upX hs
  let HXlift := whiskerAtPoint x HX downX upX xU (by rfl)
  let HXU : ContinuousMap.HomotopyRel (G.comp F) (ContinuousMap.id BX) {xU} :=
    HXlift.cast (by
      apply ContinuousMap.ext
      intro b
      rfl) (by
      apply ContinuousMap.ext
      intro b
      exact ULift.up_down b)
  let HClift := whiskerAtPoint c HC downC upC (upC c) (by rfl)
  let HCU₀ : ContinuousMap.HomotopyRel (F.comp G) (ContinuousMap.id AC) {upC c} :=
    HClift.cast (by
      apply ContinuousMap.ext
      intro a
      rfl) (by
      apply ContinuousMap.ext
      intro a
      exact ULift.up_down a)
  let HCU : ContinuousMap.HomotopyRel (F.comp G) (ContinuousMap.id AC) {aCW} := by
    simpa only [haCW] using HCU₀
  let PBX : PointedTopCat.{max u v} := pointedAt BX xU
  let PAC : PointedTopCat.{max u v} := pointedAt AC aCW
  let E₀ : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj PBX)
      (PointedTopCat.pointedPair.obj PAC) :=
    pointPairEquiv F G hF hG HXU HCU
  -- Construct the weak polyhedron and its separate metric model.
  let D := Topology.CWComplex.basedPolyhedralReplacement AC jU
  let P : PreAbstractSimplicialComplex D.vertices := D.polyhedron
  let vP : D.vertices := D.vertex
  have hvP : {vP} ∈ P := D.vertex_mem
  let p : P.Realization := Realization.vertex P vP hvP
  let PW : PointedTopCat.{max u v} := pointedAt (TopCat.of P.Realization) p
  let E₁ : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj PAC)
      (PointedTopCat.pointedPair.obj PW) :=
    pointPairEquiv D.toPolyhedron D.fromPolyhedron D.toPolyhedron_point
      D.fromPolyhedron_point D.originalHomotopy D.polyhedralHomotopy
  let a : MetricRealization P := Realization.toMetric P p
  let PM : PointedTopCat.{max u v} := pointedAt (TopCat.of (MetricRealization P)) a
  let E₂ : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj PW)
      (PointedTopCat.pointedPair.obj PM) :=
    pointPairEquiv (Realization.toMetric P) (MetricRealization.toWeak P)
      (by rfl) (MetricRealization.toWeak_vertex P vP hvP)
      (weakMetricLeftHomotopy P vP hvP) (weakMetricRightHomotopy P vP hvP)
  let Ebase : TopPair.HomotopyEquiv (PointedTopCat.pointedPair.obj PBX)
      (PointedTopCat.pointedPair.obj PM) := (E₀.trans E₁).trans E₂
  let Eloops : TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace PBX))
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace PM)) :=
    Ebase.loopSpace (X := PBX) (Y := PM)
  -- Construct the singular CW model of the metric loops and return to the raw loops.
  let M := Path a a
  let e : M := Path.refl a
  let S : SSet.{max u v} := TopCat.toSSet.obj (TopCat.of M)
  let C₀ : TopCat.{max u v} := SSet.toTop.obj S
  let c₀ : C₀ := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm e)
  let cw₀ : Topology.CWComplex (Set.univ : Set C₀) := SSet.realizationClassicalCWComplex S
  letI : Topology.CWComplex (Set.univ : Set C₀) := cw₀
  let epsilon : C(C₀, M) := (sSetTopAdj.counit.app (TopCat.of M)).hom
  have metricData : T2Space C₀ ∧
      (∃ j₀ : Topology.CWComplex.cell (Set.univ : Set C₀) 0,
        ∀ q : Fin 0 → ℝ, Topology.CWComplex.map (C := (Set.univ : Set C₀)) 0 j₀ q = c₀) ∧
      ∃ R : C(M, C₀),
        R e = c₀ ∧ epsilon c₀ = e ∧
        ∃ HL : ContinuousMap.HomotopyRel (R.comp epsilon)
            (ContinuousMap.id C₀) {c₀},
          ∃ HR : ContinuousMap.HomotopyRel (epsilon.comp R)
              (ContinuousMap.id M) {e},
            (∀ t : unitInterval, HL (t, c₀) = c₀) ∧
            (∀ t : unitInterval, HR (t, e) = e) ∧
            ∃ E : ContinuousMap.HomotopyEquiv C₀ M,
              E.toFun = epsilon ∧ E.invFun = R := by
    exact metricLoopSingularCWPointModel P vP hvP
  let j₀ : Topology.CWComplex.cell (Set.univ : Set C₀) 0 := Classical.choose metricData.2.1
  have hj₀ : ∀ q : Fin 0 → ℝ,
      Topology.CWComplex.map (C := (Set.univ : Set C₀)) 0 j₀ q = c₀ :=
    Classical.choose_spec metricData.2.1
  let R : C(M, C₀) := Classical.choose metricData.2.2
  have hRdata := Classical.choose_spec metricData.2.2
  have hR : R e = c₀ := hRdata.1
  have hepsilon : epsilon c₀ = e := hRdata.2.1
  let HL : ContinuousMap.HomotopyRel (R.comp epsilon) (ContinuousMap.id C₀) {c₀} :=
    Classical.choose hRdata.2.2
  have hHRdata := Classical.choose_spec hRdata.2.2
  let HR : ContinuousMap.HomotopyRel (epsilon.comp R) (ContinuousMap.id M) {e} :=
    Classical.choose hHRdata
  let PC₀ : PointedTopCat.{max u v} := pointedAt C₀ c₀
  let Esingular : TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace PM))
      (PointedTopCat.pointedPair.obj PC₀) :=
    pointPairEquiv R epsilon hR hepsilon HR HL
  let Ecomplete : TopPair.HomotopyEquiv
      (PointedTopCat.pointedPair.obj (PointedTopCat.loopSpace PBX))
      (PointedTopCat.pointedPair.obj PC₀) := Eloops.trans Esingular
  let Fbig : C(LoopSpace BX xU, C₀) := pairForward Ecomplete
  let Gbig : C(C₀, LoopSpace BX xU) := pairBackward Ecomplete
  have hFbig : Fbig (Path.refl xU) = c₀ := pairForward_point Ecomplete
  have hGbig : Gbig c₀ = Path.refl xU := pairBackward_point Ecomplete
  let U : C(LoopSpace X.right x, LoopSpace BX xU) := loopUp.{u, v} X.right x
  let V : C(LoopSpace BX xU, LoopSpace X.right x) := loopDown.{u, v} X.right x
  have hU : U (Path.refl x) = Path.refl xU := loopUp_refl X.right x
  have hV : V (Path.refl xU) = Path.refl x := loopDown_refl X.right x
  let toFinal : C(LoopSpace X.right x, C₀) := Fbig.comp U
  let fromFinal : C(C₀, LoopSpace X.right x) := V.comp Gbig
  have hTo : toFinal (Path.refl x) = c₀ := (congrArg Fbig hU).trans hFbig
  have hFrom : fromFinal c₀ = Path.refl x := (congrArg V hGbig).trans hV
  let Hbig : ContinuousMap.HomotopyRel (Gbig.comp Fbig)
      (ContinuousMap.id (LoopSpace BX xU)) {Path.refl xU} := pairLeftHomotopy Ecomplete
  let Horiginal₀ := whiskerAtPoint (Path.refl xU) Hbig U V (Path.refl x) hU
  let Horiginal : ContinuousMap.HomotopyRel (fromFinal.comp toFinal)
      (ContinuousMap.id (LoopSpace X.right x)) {Path.refl x} :=
    Horiginal₀.cast (by
      apply ContinuousMap.ext
      intro gamma
      rfl) (by
      apply ContinuousMap.ext
      intro gamma
      exact loopDown_up.{u, v} X.right x gamma)
  let Hmodel₀ : ContinuousMap.HomotopyRel (Fbig.comp Gbig)
      (ContinuousMap.id C₀) {c₀} := pairRightHomotopy Ecomplete
  have hModelStart : Fbig.comp Gbig = toFinal.comp fromFinal := by
    apply ContinuousMap.ext
    intro z₀
    change Fbig (Gbig z₀) = Fbig (U (V (Gbig z₀)))
    exact (congrArg Fbig (loopUp_down X.right x (Gbig z₀))).symm
  let Hmodel : ContinuousMap.HomotopyRel (toFinal.comp fromFinal)
      (ContinuousMap.id C₀) {c₀} := Hmodel₀.cast hModelStart rfl
  exact
    { model := C₀
      cw := cw₀
      hausdorff := metricData.1
      point := c₀
      zeroCell := j₀
      zeroCell_value := hj₀
      toModel := toFinal
      fromModel := fromFinal
      toModel_point := hTo
      fromModel_point := hFrom
      originalHomotopy := Horiginal
      modelHomotopy := Hmodel
      constantLoopNDR := dX.loop }

/-- The complete raw loop space admits a compatible based Hausdorff CW point model. -/
public theorem hasRawLoopCWPointModel (X : PointedTopCat.{u})
    (dX : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj X))
    (C : TopCat.{v}) [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (c : C) (j : Topology.CWComplex.cell (Set.univ : Set C) 0)
    (hj : Topology.CWComplex.map (C := (Set.univ : Set C)) 0 j ![] = c)
    (r : C(X.right, C)) (s : C(C, X.right))
    (hr : r (X.hom PUnit.unit) = c) (hs : s c = X.hom PUnit.unit)
    (HX : ContinuousMap.HomotopyRel (s.comp r) (ContinuousMap.id X.right)
      {X.hom PUnit.unit})
    (HC : ContinuousMap.HomotopyRel (r.comp s) (ContinuousMap.id C) {c}) :
    Nonempty (RawLoopCWPointModelData.{u, max u v} X) :=
  ⟨rawLoopCWPointModel X dX C c j hj r s hr hs HX HC⟩

/-- The constructed constant-loop NDR data is exactly induced from the original point data. -/
public theorem rawLoopCWPointModel_constantLoopNDR (X : PointedTopCat.{u})
    (dX : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj X))
    (C : TopCat.{v}) [T2Space C] [Topology.CWComplex (Set.univ : Set C)]
    (c : C) (j : Topology.CWComplex.cell (Set.univ : Set C) 0)
    (hj : Topology.CWComplex.map (C := (Set.univ : Set C)) 0 j ![] = c)
    (r : C(X.right, C)) (s : C(C, X.right))
    (hr : r (X.hom PUnit.unit) = c) (hs : s c = X.hom PUnit.unit)
    (HX : ContinuousMap.HomotopyRel (s.comp r) (ContinuousMap.id X.right)
      {X.hom PUnit.unit})
    (HC : ContinuousMap.HomotopyRel (r.comp s) (ContinuousMap.id C) {c}) :
    (rawLoopCWPointModel X dX C c j hj r s hr hs HX HC).constantLoopNDR = dX.loop := by
  rfl

end PointedTopCat

end
