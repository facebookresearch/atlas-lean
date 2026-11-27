/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Exact.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ConnectingExactness

/-!
# Fibration sequences

Bundled pointed Kan fibration sequence `FibrationSequence` over `p : E ⟶ B`
with strict fiber `F`. Covers functorial maps / naturality via
`FibrationSequenceHom` / `fiberMap` and `connectingMap_naturality` of
connecting morphisms `connectingMap`, and exactness at base/fiber/total
space (`exactness_at_B` / `mulExact_at_B`, `exactness_at_fiber` /
`mulExact_at_fiber`, `exactness_at_E` / `mulExact_at_E`), packaged as
`ExactSegment`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra Opposite
open scoped Simplicial
open SSet.modelCategoryQuillen

namespace SSet

/-- Bundled strict Kan-fibration sequence over `p : E ⟶ B` with
chosen `e : E _⦋0⦌`, its image `b`, and strict fiber
`F = fiber p b`. Fields are ordered for a future derived-fiber
wrapper that may extend this strict core. -/
structure FibrationSequence where
  E : SSet.{u}
  B : SSet.{u}
  p : E ⟶ B
  fibration_p : Fibration p
  fibrant_B : IsFibrant B
  e : E _⦋0⦌
  b : B _⦋0⦌
  hb : p.app (op ⦋0⦌) e = b

namespace FibrationSequence

/-- Strict fiber as a simplicial set. -/
abbrev fiber (S : FibrationSequence) : SSet.{u} :=
  Subcomplex.fiber S.p S.b

/-- Inclusion of the strict fiber into the total space. -/
abbrev fiberIncl (S : FibrationSequence) : S.fiber ⟶ S.E :=
  (Subcomplex.fiber S.p S.b).ι

/-- Basepoint of the fiber determined by `e` and `hb`. -/
abbrev fiberPoint (S : FibrationSequence) : S.fiber _⦋0⦌ :=
  Subcomplex.fiber.basePoint S.e S.hb

/-- Canonical identification of the fiber as a pullback. -/
theorem fiber_isPullback (S : FibrationSequence) :
    IsPullback S.fiberIncl
      (IsTerminal.from stdSimplex.isTerminalObj₀ S.fiber) S.p
      (SSet.const (X := Δ[0]) S.b) :=
  Subcomplex.fiber_isPullback S.p S.b

instance isFibrant_base (S : FibrationSequence) : IsFibrant S.B :=
  S.fibrant_B

instance isFibrant_total (S : FibrationSequence) : IsFibrant S.E := by
  have : Fibration S.p := S.fibration_p
  have : IsFibrant S.B := S.fibrant_B
  exact isFibrant_of_fibration S.p

/-- The strict fiber is fibrant when `p` is a Kan fibration. -/
instance isFibrant_fiber (S : FibrationSequence) : IsFibrant S.fiber := by
  have : Fibration S.p := S.fibration_p
  infer_instance

@[simp]
theorem fiberIncl_comp (S : FibrationSequence) :
    S.fiberIncl ≫ S.p = SSet.const S.b :=
  Subcomplex.fiber_ι_comp S.p S.b

/-- Bundled wrapper around `ConnectingMap.connectingMap`, with the fibration
instance and pointed data supplied by `S`. -/
noncomputable def connectingMap (S : FibrationSequence) (n : ℕ) :
    KanComplex.π (n + 1) S.B S.b →
      KanComplex.π n S.fiber S.fiberPoint :=
  have : Fibration S.p := S.fibration_p
  ConnectingMap.connectingMap S.p S.e S.hb

@[simp]
theorem connectingMap_mk (S : FibrationSequence) {n : ℕ}
    (σ : S.B.PtSimplex (n + 1) S.b) :
    S.connectingMap (n := n) (KanComplex.π.mk σ) =
      KanComplex.π.mk
        (@ConnectingMap.connectingPtSimplexRep _ _ n S.p S.e S.b
          S.hb S.fibration_p σ) := by
  have : Fibration S.p := S.fibration_p
  simp only [connectingMap]
  exact ConnectingMap.connectingMap_mk S.p S.e S.hb σ

end FibrationSequence

/-- Morphism of strict fibration sequences given by a commutative
square preserving the chosen basepoints. -/
structure FibrationSequenceHom (S T : FibrationSequence.{u}) where
  totalMap : S.E ⟶ T.E
  baseMap : S.B ⟶ T.B
  comm : totalMap ≫ T.p = S.p ≫ baseMap
  total_pt : totalMap.app (op ⦋0⦌) S.e = T.e
  base_pt : baseMap.app (op ⦋0⦌) S.b = T.b

namespace FibrationSequenceHom

variable {S T U : FibrationSequence.{u}}

/-- Induced map on strict fibers. -/
def fiberMap (f : FibrationSequenceHom S T) :
    S.fiber ⟶ T.fiber :=
  Subcomplex.mapFiber f.totalMap f.baseMap f.comm f.base_pt

@[simp, reassoc]
theorem fiberMap_ι (f : FibrationSequenceHom S T) :
    f.fiberMap ≫ T.fiberIncl = S.fiberIncl ≫ f.totalMap :=
  Subcomplex.mapFiber_ι _ _ _ _

@[simp]
theorem fiberMap_id (S : FibrationSequence) :
    (FibrationSequenceHom.mk (𝟙 S.E) (𝟙 S.B) (by simp) rfl rfl).fiberMap =
      𝟙 S.fiber := by
  simp only [fiberMap, Subcomplex.mapFiber_id]

theorem fiberMap_comp (f : FibrationSequenceHom S T)
    (g : FibrationSequenceHom T U) :
    (FibrationSequenceHom.mk (f.totalMap ≫ g.totalMap)
        (f.baseMap ≫ g.baseMap)
        (by
          calc (f.totalMap ≫ g.totalMap) ≫ U.p =
              f.totalMap ≫ (g.totalMap ≫ U.p) := by rw [Category.assoc]
            _ = f.totalMap ≫ (T.p ≫ g.baseMap) := by rw [g.comm]
            _ = (f.totalMap ≫ T.p) ≫ g.baseMap := by rw [← Category.assoc]
            _ = (S.p ≫ f.baseMap) ≫ g.baseMap := by rw [f.comm]
            _ = S.p ≫ (f.baseMap ≫ g.baseMap) := by rw [Category.assoc])
        (by simp [f.total_pt, g.total_pt])
        (by simp [f.base_pt, g.base_pt])).fiberMap =
      f.fiberMap ≫ g.fiberMap := by
  simp only [fiberMap, Subcomplex.mapFiber_comp]

/-- Identity morphism. -/
def id (S : FibrationSequence.{u}) : FibrationSequenceHom S S where
  totalMap := 𝟙 S.E
  baseMap := 𝟙 S.B
  comm := by simp
  total_pt := rfl
  base_pt := rfl

/-- Composition of morphisms. -/
def comp (f : FibrationSequenceHom S T) (g : FibrationSequenceHom T U) :
    FibrationSequenceHom S U where
  totalMap := f.totalMap ≫ g.totalMap
  baseMap := f.baseMap ≫ g.baseMap
  comm := by
    calc (f.totalMap ≫ g.totalMap) ≫ U.p =
        f.totalMap ≫ (g.totalMap ≫ U.p) := by rw [Category.assoc]
      _ = f.totalMap ≫ (T.p ≫ g.baseMap) := by rw [g.comm]
      _ = (f.totalMap ≫ T.p) ≫ g.baseMap := by rw [← Category.assoc]
      _ = (S.p ≫ f.baseMap) ≫ g.baseMap := by rw [f.comm]
      _ = S.p ≫ (f.baseMap ≫ g.baseMap) := by rw [Category.assoc]
  total_pt := by simp [f.total_pt, g.total_pt]
  base_pt := by simp [f.base_pt, g.base_pt]

@[simp]
theorem id_fiberMap (S : FibrationSequence) :
    (id S).fiberMap = 𝟙 S.fiber := by
  simp only [id, fiberMap, Subcomplex.mapFiber_id]

@[simp]
theorem comp_fiberMap (f : FibrationSequenceHom S T)
    (g : FibrationSequenceHom T U) :
    (comp f g).fiberMap = f.fiberMap ≫ g.fiberMap := by
  simp only [comp, fiberMap, Subcomplex.mapFiber_comp]

@[simp]
theorem fiberMap_app_basePoint (f : FibrationSequenceHom S T) :
    f.fiberMap.app (op ⦋0⦌) S.fiberPoint = T.fiberPoint := by
  apply Subtype.ext
  exact f.total_pt

end FibrationSequenceHom

namespace FibrationSequence

variable {S T : FibrationSequence.{u}}
  (f : FibrationSequenceHom S T)

/-- Connecting-map naturality: the connecting map commutes with the maps
induced by a morphism of strict fibration sequences, descending from
pointed-simplex representative naturality. -/
theorem connectingMap_naturality {n : ℕ}
    (q : KanComplex.π (n + 1) S.B S.b) :
    KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n
        (S.connectingMap (n := n) q) =
      T.connectingMap (n := n)
        (KanComplex.π.map f.baseMap f.base_pt (n + 1) q) := by
  induction q using KanComplex.π.rec with
  | mk σ =>
    have : Fibration S.p := S.fibration_p
    have : Fibration T.p := T.fibration_p
    simp only [connectingMap, ConnectingMap.connectingMap_mk,
      KanComplex.π.map_mk]
    rw [KanComplex.π.mk_eq_mk_iff]
    exact ConnectingMap.connectingPtSimplexRep_naturality_rel
      f.totalMap f.baseMap f.comm
      f.total_pt f.base_pt σ

/-- Kernel-to-image at `π (n + 1) B`: if `S.connectingMap` sends a class
to `1`, that class comes from `π.map S.p` in degree `n + 1`. -/
theorem exactness_at_B {n : ℕ}
    (q : KanComplex.π (n + 1) S.B S.b) :
    S.connectingMap (n := n) q = 1 →
      ∃ r : KanComplex.π (n + 1) S.E S.e,
        KanComplex.π.map S.p S.hb (n + 1) r = q := by
  have : Fibration S.p := S.fibration_p
  intro hq
  have hq' : ConnectingMap.connectingMap S.p S.e S.hb (n := n) q = 1 := by
    simpa [connectingMap] using hq
  exact ConnectingMap.connecting_exactness_at_B S.p S.e S.hb q hq'

/-- Kernel-to-image at `π n F`: a fiber class killed by `S.fiberIncl`
comes from `S.connectingMap`. -/
theorem exactness_at_fiber {n : ℕ}
    (q : KanComplex.π n S.fiber S.fiberPoint) :
    KanComplex.π.map S.fiberIncl
        ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n q = 1 →
      ∃ r : KanComplex.π (n + 1) S.B S.b,
        S.connectingMap (n := n) r = q := by
  have : Fibration S.p := S.fibration_p
  intro hq
  have hq' : KanComplex.π.map
        (Subcomplex.fiber S.p S.b).ι
        ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n q = 1 := hq
  obtain ⟨r, hr⟩ :=
    ConnectingMap.connecting_exactness_at_fiber S.p S.e S.hb (n := n) q hq'
  exact ⟨r, by simpa [connectingMap] using hr⟩

/-- Kernel-to-image at `π n E`: a total-space class killed by `S.p`
comes from `S.fiberIncl`. -/
theorem exactness_at_E {n : ℕ}
    (q : KanComplex.π n S.E S.e) :
    KanComplex.π.map S.p S.hb n q = 1 →
      ∃ r : KanComplex.π n S.fiber S.fiberPoint,
        KanComplex.π.map S.fiberIncl
          ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n r = q := by
  have : Fibration S.p := S.fibration_p
  exact ConnectingMap.connecting_exactness_at_E S.p S.hb q

/-- The fiber inclusion followed by `p` is trivial on homotopy groups. -/
theorem map_p_comp_fiberIncl_eq_one {n : ℕ}
    (q : KanComplex.π n S.fiber S.fiberPoint) :
    KanComplex.π.map S.p S.hb n
        (KanComplex.π.map S.fiberIncl
            ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n q) =
      1 := by
  induction q using KanComplex.π.rec with
  | mk t =>
    have h_base : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e := by rfl
    have h_pt : (S.fiberIncl ≫ S.p).app (op ⦋0⦌) S.fiberPoint = S.b := by
      calc (S.fiberIncl ≫ S.p).app (op ⦋0⦌) S.fiberPoint
          = S.p.app (op ⦋0⦌) (S.fiberIncl.app (op ⦋0⦌) S.fiberPoint) := rfl
        _ = S.p.app (op ⦋0⦌) S.e := by rw [h_base]
        _ = S.b := S.hb
    calc KanComplex.π.map S.p S.hb n
            (KanComplex.π.map S.fiberIncl h_base n
              (KanComplex.π.mk t))
        = KanComplex.π.map (S.fiberIncl ≫ S.p) h_pt n
            (KanComplex.π.mk t) := by
          rw [← KanComplex.π.map_comp_apply S.fiberIncl S.p
            h_base S.hb h_pt]
      _ = KanComplex.π.mk
            (SSet.PtSimplex.map (S.fiberIncl ≫ S.p) h_pt t) := rfl
      _ = KanComplex.π.mk
            (RelativeMorphism.const : S.B.PtSimplex n S.b) := by
          congr 1
          apply RelativeMorphism.ext
          calc RelativeMorphism.map
                  (SSet.PtSimplex.map (S.fiberIncl ≫ S.p) h_pt t)
              = RelativeMorphism.map t ≫ (S.fiberIncl ≫ S.p) := rfl
            _ = RelativeMorphism.map t ≫
                  SSet.const (X := S.fiber) S.b := by
                rw [S.fiberIncl_comp]
            _ = SSet.const (X := Δ[n]) S.b := by
                simp [SSet.comp_const]
            _ = RelativeMorphism.map
                  (RelativeMorphism.const : S.B.PtSimplex n S.b) := rfl
      _ = 1 := rfl

private def idFibrationSeq (S : FibrationSequence.{u}) : FibrationSequence where
  E := S.E
  B := S.E
  p := 𝟙 S.E
  fibration_p := inferInstance
  fibrant_B := S.isFibrant_total
  e := S.e
  b := S.e
  hb := rfl

private def idHom (S : FibrationSequence.{u}) :
    FibrationSequenceHom (idFibrationSeq S) S where
  totalMap := 𝟙 S.E
  baseMap := S.p
  comm := by
    unfold idFibrationSeq
    rfl
  total_pt := rfl
  base_pt := S.hb

private theorem fiberId_ι_eq_const (S : FibrationSequence.{u}) :
    (Subcomplex.fiber (𝟙 S.E) S.e).ι =
      SSet.const (X := (Subcomplex.fiber (𝟙 S.E) S.e : SSet)) S.e := by
  have h := Subcomplex.fiber_ι_comp (𝟙 S.E) S.e
  calc (Subcomplex.fiber (𝟙 S.E) S.e).ι
      = (Subcomplex.fiber (𝟙 S.E) S.e).ι ≫ 𝟙 S.E := by simp
    _ = SSet.const S.e := h

private theorem fiberId_ptSimplex_map_eq_const
    (S : FibrationSequence.{u}) {n : ℕ}
    (t : ((Subcomplex.fiber (𝟙 S.E) S.e : SSet).PtSimplex n
      (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl))) :
    RelativeMorphism.map t =
      SSet.const
        (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl) := by
  have hTerm : IsTerminal
      (Subcomplex.fiber (𝟙 S.E) S.e : SSet) := by
    have hEq : Subcomplex.fiber (𝟙 S.E) S.e =
        Subcomplex.ofSimplex S.e :=
      Subcomplex.preimage_id _
    rw [hEq]
    exact Subcomplex.isTerminalOfSimplex S.e
  exact IsTerminal.hom_ext hTerm _ _

private theorem fiberId_ptSimplex_eq_const
    (S : FibrationSequence.{u}) {n : ℕ}
    (t : ((Subcomplex.fiber (𝟙 S.E) S.e : SSet).PtSimplex n
      (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl))) :
    t = (RelativeMorphism.const :
      ((Subcomplex.fiber (𝟙 S.E) S.e : SSet).PtSimplex n
        (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl))) := by
  apply RelativeMorphism.ext
  exact fiberId_ptSimplex_map_eq_const S t

private theorem fiberId_pi_eq_one (S : FibrationSequence.{u}) {n : ℕ}
    (q : KanComplex.π n (Subcomplex.fiber (𝟙 S.E) S.e : SSet)
      (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl)) :
    q = 1 := by
  induction q using KanComplex.π.rec with
  | mk t =>
    have ht : t = (RelativeMorphism.const :
      ((Subcomplex.fiber (𝟙 S.E) S.e : SSet).PtSimplex n
        (Subcomplex.fiber.basePoint (f := 𝟙 S.E) S.e rfl))) :=
      fiberId_ptSimplex_eq_const S t
    calc KanComplex.π.mk t =
          KanComplex.π.mk (RelativeMorphism.const :
            ((Subcomplex.fiber (𝟙 S.E) S.e : SSet).PtSimplex n
              (Subcomplex.fiber.basePoint
                (f := 𝟙 S.E) S.e rfl))) := by
          rw [ht]
      _ = 1 := rfl

private theorem pi_map_one_eq_one {X Y : SSet.{u}} {x : X _⦋0⦌}
    {y : Y _⦋0⦌} (f : X ⟶ Y) (hf : f.app _ x = y) (n : ℕ) :
    KanComplex.π.map f hf n (1 : KanComplex.π n X x) = 1 := by
  have h1 : (1 : KanComplex.π n X x) =
      KanComplex.π.mk (RelativeMorphism.const : X.PtSimplex n x) := rfl
  rw [h1, KanComplex.π.map_mk]
  have hmap : SSet.PtSimplex.map f hf
      (RelativeMorphism.const : X.PtSimplex n x) =
      (RelativeMorphism.const : Y.PtSimplex n y) := by
    apply RelativeMorphism.ext
    calc RelativeMorphism.map
            (SSet.PtSimplex.map f hf
              (RelativeMorphism.const : X.PtSimplex n x))
        = RelativeMorphism.map
            (RelativeMorphism.const : X.PtSimplex n x) ≫ f := rfl
      _ = SSet.const (X := Δ[n]) x ≫ f := rfl
      _ = SSet.const (X := Δ[n]) y := by rw [SSet.const_comp, hf]
      _ = RelativeMorphism.map
            (RelativeMorphism.const : Y.PtSimplex n y) := rfl
  rw [hmap]
  rfl

private theorem idFibrationSeq_connectingMap_eq_one
    (S : FibrationSequence.{u}) {n : ℕ}
    (q : KanComplex.π (n + 1) (idFibrationSeq S).B
      (idFibrationSeq S).b) :
    (idFibrationSeq S).connectingMap (n := n) q = 1 :=
  fiberId_pi_eq_one S _

/-- Connecting map kills the image of `π.map p`. -/
theorem connectingMap_map_eq_one {n : ℕ}
    (q : KanComplex.π (n + 1) S.E S.e) :
    S.connectingMap (n := n) (KanComplex.π.map S.p S.hb (n + 1) q) = 1 := by
  have hNat := connectingMap_naturality (S := idFibrationSeq S) (T := S)
    (f := idHom S) (n := n) (q := q)
  have hSrc : (idFibrationSeq S).connectingMap (n := n) q = 1 :=
    idFibrationSeq_connectingMap_eq_one S q
  have hFiber : KanComplex.π.map (idHom S).fiberMap
      (FibrationSequenceHom.fiberMap_app_basePoint (idHom S)) n 1 = 1 :=
    pi_map_one_eq_one (idHom S).fiberMap
      (FibrationSequenceHom.fiberMap_app_basePoint (idHom S)) n
  calc S.connectingMap (n := n) (KanComplex.π.map S.p S.hb (n + 1) q)
      = S.connectingMap (n := n)
          (KanComplex.π.map (idHom S).baseMap (idHom S).base_pt (n + 1) q) :=
        rfl
    _ = KanComplex.π.map (idHom S).fiberMap
          (FibrationSequenceHom.fiberMap_app_basePoint (idHom S)) n
          ((idFibrationSeq S).connectingMap (n := n) q) := by
        rw [hNat]
    _ = KanComplex.π.map (idHom S).fiberMap
          (FibrationSequenceHom.fiberMap_app_basePoint (idHom S)) n 1 := by
        rw [hSrc]
    _ = 1 := hFiber

private noncomputable def constToChosenLiftRelStruct
    (S : FibrationSequence.{u}) {n : ℕ}
    [Fibration S.p] (σ : S.B.PtSimplex (n + 1) S.b) :
    SSet.PtSimplex.RelStruct
      (RelativeMorphism.const : S.E.PtSimplex n S.e)
      (ConnectingMap.chosenLiftPt (e := S.e) (b := S.b) S.p S.hb σ)
      (Fin.last n) := by
  refine
    { map :=
        SSet.yonedaEquiv.symm
          (ConnectingMap.chosenLift (e := S.e) (b := S.b) S.p S.hb σ)
      δ_castSucc_map := by
        have h_ne : (Fin.last n).castSucc ≠ Fin.last (n + 1) :=
          ne_of_lt (by simp)
        exact ConnectingMap.chosenLift_face_eq_const
          (e := S.e) (b := S.b) S.p S.hb σ _ h_ne
      δ_succ_map := by
        have h_eq : (Fin.last n).succ = Fin.last (n + 1) := rfl
        rw [h_eq]
        exact (ConnectingMap.chosenLift_face_eq
          (e := S.e) (b := S.b) S.p S.hb σ).symm
      δ_map_of_lt := by
        intro j hj
        have h_ne : j ≠ Fin.last (n + 1) :=
          ne_of_lt (lt_trans hj (by simp))
        exact ConnectingMap.chosenLift_face_eq_const
          (e := S.e) (b := S.b) S.p S.hb σ j h_ne
      δ_map_of_gt := by
        intro j hj
        have h_le : j ≤ Fin.last (n + 1) := Fin.le_last j
        have h_eq : (Fin.last n).succ = Fin.last (n + 1) := rfl
        rw [h_eq] at hj
        exact absurd hj (not_lt.mpr h_le) }

/-- Fiber inclusion kills the image of the connecting map. -/
theorem fiberIncl_map_connectingMap_eq_one {n : ℕ}
    (q : KanComplex.π (n + 1) S.B S.b) :
    KanComplex.π.map S.fiberIncl
        ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n
        (S.connectingMap (n := n) q) = 1 := by
  induction q using KanComplex.π.rec with
  | mk σ =>
    have : Fibration S.p := S.fibration_p
    have h_base : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e := by rfl
    rw [S.connectingMap_mk, KanComplex.π.map_mk,
      KanComplex.π.mk_eq_one_iff]
    have hEq : SSet.PtSimplex.map S.fiberIncl h_base
            (ConnectingMap.connectingPtSimplexRep
              (p := S.p) (e := S.e) S.hb σ) =
        ConnectingMap.chosenLiftPt (e := S.e) (b := S.b) S.p S.hb σ := by
      apply RelativeMorphism.ext
      calc RelativeMorphism.map
              (SSet.PtSimplex.map S.fiberIncl h_base
                (ConnectingMap.connectingPtSimplexRep
                  (p := S.p) (e := S.e) S.hb σ))
          = RelativeMorphism.map
              (ConnectingMap.connectingPtSimplexRep
                (p := S.p) (e := S.e) S.hb σ) ≫ S.fiberIncl := rfl
        _ = RelativeMorphism.map
              (ConnectingMap.chosenLiftPt (e := S.e) (b := S.b) S.p S.hb σ) :=
            ConnectingMap.connectingPtSimplexRep_ι
              (p := S.p) (e := S.e) S.hb σ
    have hRel : Nonempty
        (SSet.PtSimplex.RelStruct₀
          (ConnectingMap.chosenLiftPt (e := S.e) (b := S.b) S.p S.hb σ)
          (RelativeMorphism.const : S.E.PtSimplex n S.e)) := by
      have hLast : SSet.PtSimplex.RelStruct
          (RelativeMorphism.const : S.E.PtSimplex n S.e)
          (ConnectingMap.chosenLiftPt (e := S.e) (b := S.b) S.p S.hb σ)
          (Fin.last n) :=
        constToChosenLiftRelStruct S σ
      exact ⟨(hLast.symm).relStruct₀⟩
    obtain ⟨h⟩ := hRel
    exact ⟨h.copy hEq.symm rfl⟩

theorem mulExact_at_B {n : ℕ} :
    Function.MulExact
      (KanComplex.π.map S.p S.hb (n + 1))
      (S.connectingMap (n := n)) := by
  intro q
  constructor
  · intro hq
    obtain ⟨r, hr⟩ := S.exactness_at_B q hq
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact S.connectingMap_map_eq_one r

theorem mulExact_at_fiber {n : ℕ} :
    Function.MulExact
      (S.connectingMap (n := n))
      (KanComplex.π.map S.fiberIncl
        ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n) := by
  intro q
  constructor
  · intro hq
    obtain ⟨r, hr⟩ := S.exactness_at_fiber q hq
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact S.fiberIncl_map_connectingMap_eq_one r

theorem mulExact_at_E {n : ℕ} :
    Function.MulExact
      (KanComplex.π.map S.fiberIncl
        ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n)
      (KanComplex.π.map S.p S.hb n) := by
  intro q
  constructor
  · intro hq
    obtain ⟨r, hr⟩ := S.exactness_at_E q hq
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact S.map_p_comp_fiberIncl_eq_one r

structure ExactSegment (S : FibrationSequence) (n : ℕ) : Prop where
  atBase : Function.MulExact
    (KanComplex.π.map S.p S.hb (n + 1))
    (S.connectingMap (n := n))
  atFiber : Function.MulExact
    (S.connectingMap (n := n))
    (KanComplex.π.map S.fiberIncl
      ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n)
  atTotal : Function.MulExact
    (KanComplex.π.map S.fiberIncl
      ((by rfl) : S.fiberIncl.app (op ⦋0⦌) S.fiberPoint = S.e) n)
    (KanComplex.π.map S.p S.hb n)

theorem exactSegment (S : FibrationSequence) (n : ℕ) :
    S.ExactSegment n where
  atBase := S.mulExact_at_B (n := n)
  atFiber := S.mulExact_at_fiber (n := n)
  atTotal := S.mulExact_at_E (n := n)

end FibrationSequence

end SSet
