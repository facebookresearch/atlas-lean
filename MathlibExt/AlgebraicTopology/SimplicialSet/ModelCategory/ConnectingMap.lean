/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

public section

universe u

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra
open Opposite MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen

namespace SSet

namespace ConnectingMap

variable {E B : SSet.{u}} {e : E _⦋0⦌} {b : B _⦋0⦌}

/-!
# Representative connecting map for a Kan fibration

For a Kan fibration `p : E ⟶ B` with basepoints `e : E _⦋0⦌` and
`b = p.app _ e`, this file constructs the representative connecting map:
the pointed `n`-simplex in the strict fiber `fiber p b`, its quotient
descent to homotopy groups, its naturality under commutative squares, and
the three exactness results at `π (n + 1) B`, `π n (fiber p b)` and `π n E`.
-/

-- =========================================================================
-- Layer 1: private horn / boundary lift choice data
-- =========================================================================

private structure ChosenLiftData {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) where
  lift : E _⦋n + 1⦌
  pt : E.PtSimplex n e
  lift_projects :
    SSet.yonedaEquiv.symm lift ≫ p = RelativeMorphism.map σ
  face_eq :
    RelativeMorphism.map pt =
      stdSimplex.δ (Fin.last _) ≫ SSet.yonedaEquiv.symm lift

private noncomputable def chosenLiftData {n : ℕ} (p : E ⟶ B)
    (hb : p.app _ e = b) [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    ChosenLiftData (e := e) (b := b) p hb σ := by
  let bMap : Δ[n + 1] ⟶ B := RelativeMorphism.map σ
  let lastIdx : Fin (n + 2) := Fin.last _
  let f : ∀ (j : Fin (n + 2)) (_ : j ≠ lastIdx), Δ[n] ⟶ E :=
    fun _ _ => SSet.const (X := Δ[n]) e
  have hf : horn.IsCompatible f := by
    cases n with
    | zero => trivial
    | succ m =>
      intro j k hj hk hjk
      simp [f, SSet.comp_const]
  have hcomm : ∀ (j : Fin (n + 2)) (hj : j ≠ lastIdx),
      f j hj ≫ p = stdSimplex.δ j ≫ bMap := by
    intro j hj
    have h1 : f j hj ≫ p = SSet.const (X := Δ[n]) b := by
      simp [f, SSet.const_comp, hb]
    have h2 : stdSimplex.δ j ≫ bMap = SSet.const (X := Δ[n]) b := by
      simp [bMap, SSet.PtSimplex.δ_map]
    exact h1.trans h2.symm
  let φ : Δ[n + 1] ⟶ E := hf.lift p bMap hcomm
  have hφ_comp : φ ≫ p = bMap := hf.lift_comp (p := p) (b := bMap) hcomm
  have hφ_face : ∀ (j : Fin (n + 2)) (hj : j ≠ lastIdx),
      stdSimplex.δ j ≫ φ = f j hj := fun j hj =>
    hf.δ_lift (p := p) (b := bMap) hcomm j hj
  let liftVal : E _⦋n + 1⦌ := SSet.yonedaEquiv φ
  have hLiftSymm : SSet.yonedaEquiv.symm liftVal = φ := by
    simp [liftVal]
  let ptMap : Δ[n] ⟶ E := stdSimplex.δ lastIdx ≫ φ
  have hBoundary : (SSet.boundary n).ι ≫ ptMap = SSet.const (X := SSet.boundary n) e := by
    cases n with
    | zero =>
      have : SSet.boundary (0 : ℕ) = ⊥ := SSet.boundary_zero
      rw [this]
      exact Subsingleton.elim _ _
    | succ m =>
      apply SSet.boundary.hom_ext
      intro k
      have h_le : (k : Fin (m + 2)) ≤ Fin.last (m + 1) := Fin.le_last _
      have h_eq :
          stdSimplex.δ (k : Fin (m + 2)) ≫ stdSimplex.δ lastIdx =
            stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
              stdSimplex.δ (Fin.castSucc (k : Fin (m + 2)) : Fin (m + 3)) := by
        have h_last : lastIdx = (Fin.last (m + 1) : Fin (m + 2)).succ := rfl
        calc stdSimplex.δ (k : Fin (m + 2)) ≫ stdSimplex.δ lastIdx
            = stdSimplex.δ (k : Fin (m + 2)) ≫
                stdSimplex.δ ((Fin.last (m + 1) : Fin (m + 2)).succ) := by
              rw [← h_last]
          _ = stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
                stdSimplex.δ (Fin.castSucc (k : Fin (m + 2)) : Fin (m + 3)) := by
              exact SSet.stdSimplex.δ_comp_δ (n := m) h_le
      have h_δ_pt : stdSimplex.δ (k : Fin (m + 2)) ≫ ptMap =
          SSet.const (X := Δ[m]) e := by
        calc stdSimplex.δ (k : Fin (m + 2)) ≫ ptMap
            = (stdSimplex.δ (k : Fin (m + 2)) ≫ stdSimplex.δ lastIdx) ≫ φ := by
              simp [ptMap, Category.assoc]
          _ = (stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
                stdSimplex.δ (Fin.castSucc (k : Fin (m + 2)) : Fin (m + 3))) ≫ φ := by
              rw [h_eq]
          _ = stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
                (stdSimplex.δ (Fin.castSucc (k : Fin (m + 2)) : Fin (m + 3)) ≫ φ) := by
              rw [Category.assoc]
          _ = stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
                SSet.const (X := Δ[m + 1]) e := by
              rw [hφ_face (Fin.castSucc (k : Fin (m + 2)))
                (by simp [lastIdx, Fin.castSucc_ne_last])]
          _ = SSet.const (X := Δ[m]) e := by
              simp only [SSet.comp_const]
      calc SSet.boundary.ι (k : Fin (m + 2)) ≫ (SSet.boundary (m + 1)).ι ≫ ptMap
          = stdSimplex.δ (k : Fin (m + 2)) ≫ ptMap := by
            rw [← Category.assoc, SSet.boundary.ι_ι]
        _ = SSet.const (X := Δ[m]) e := h_δ_pt
        _ = SSet.boundary.ι (k : Fin (m + 2)) ≫ SSet.const (X := SSet.boundary (m + 1)) e := by
            simp only [SSet.comp_const]
  let pt : E.PtSimplex n e :=
    { map := ptMap
      comm := by
        have h0 : (SSet.boundary n).ι ≫ ptMap =
            SSet.const (X := SSet.boundary n) e := hBoundary
        have h1 :
            SSet.const
                (X := SSet.boundary n)
                (⟨e, Subcomplex.mem_ofSimplex_obj (X := E) e⟩ :
                  (Subcomplex.ofSimplex (X := E) e : SSet) _⦋0⦌) ≫
              (Subcomplex.ofSimplex (X := E) e).ι =
            SSet.const (X := SSet.boundary n) e := by
          simp [Subcomplex.ofSimplex_ι, SSet.comp_const]
        rw [← h1] at h0
        exact h0 }
  refine
    { lift := liftVal
      pt := pt
      lift_projects := by
        have : SSet.yonedaEquiv.symm liftVal ≫ p = φ ≫ p := by
          rw [hLiftSymm]
        rw [this, hφ_comp]
      face_eq := by
        simp [pt, ptMap, lastIdx, hLiftSymm] }

noncomputable def chosenLift {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) : E _⦋n + 1⦌ :=
  (chosenLiftData (e := e) (b := b) p hb σ).lift

noncomputable def chosenLiftPt {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) : E.PtSimplex n e :=
  (chosenLiftData (e := e) (b := b) p hb σ).pt

lemma chosenLift_projects {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) ≫ p =
      RelativeMorphism.map σ :=
  (chosenLiftData (e := e) (b := b) p hb σ).lift_projects

lemma chosenLift_face_eq {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ) =
      stdSimplex.δ (Fin.last _) ≫
        SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) :=
  (chosenLiftData (e := e) (b := b) p hb σ).face_eq

-- =========================================================================
-- Layer 2: representative pointed simplex in the fiber
-- =========================================================================

lemma pt_map_comp_const {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ) ≫ p =
      SSet.const (X := Δ[n]) b := by
  calc RelativeMorphism.map (chosenLiftPt (e := e) p hb σ) ≫ p
      = (stdSimplex.δ (Fin.last _) ≫ SSet.yonedaEquiv.symm
            (chosenLift (e := e) p hb σ)) ≫ p := by
        rw [chosenLift_face_eq]
    _ = stdSimplex.δ (Fin.last _) ≫
          (SSet.yonedaEquiv.symm (chosenLift (e := e) p hb σ) ≫ p) := by
        rw [Category.assoc]
    _ = stdSimplex.δ (Fin.last _) ≫ RelativeMorphism.map σ := by
        rw [chosenLift_projects]
    _ = SSet.const (X := Δ[n]) b := by
        exact SSet.PtSimplex.δ_map σ (Fin.last _)

lemma pt_range_le_fiber {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    Subcomplex.range
        (RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ)) ≤
      Subcomplex.fiber p b := by
  rw [Subcomplex.range_le_fiber_iff]
  exact pt_map_comp_const p hb σ

noncomputable def connectingPtSimplexRep {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p]
    (σ : B.PtSimplex (n + 1) b) :
    (Subcomplex.fiber p b : SSet.{u}).PtSimplex n
      (Subcomplex.fiber.basePoint (f := p) e hb) where
  map :=
    Subcomplex.lift
      (RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ))
      (pt_range_le_fiber (e := e) p hb σ)
  comm := by
    have h_range := pt_range_le_fiber (e := e) p hb σ
    let pt := chosenLiftPt (e := e) (b := b) p hb σ
    have h_pt_comm :
        (SSet.boundary n).ι ≫ RelativeMorphism.map pt = SSet.const e := by
      calc (SSet.boundary n).ι ≫ RelativeMorphism.map pt
          = SSet.const
              (⟨e, Subcomplex.mem_ofSimplex_obj (X := E) e⟩ :
                (Subcomplex.ofSimplex (X := E) e : SSet) _⦋0⦌) ≫
              (Subcomplex.ofSimplex (X := E) e).ι := pt.comm
        _ = SSet.const (X := SSet.boundary n) e := by
            simp [Subcomplex.ofSimplex_ι]
    have h_lift :
        Subcomplex.lift (RelativeMorphism.map pt) h_range ≫
            (Subcomplex.fiber p b).ι =
          RelativeMorphism.map pt := Subcomplex.lift_ι _ _
    have h_boundary_lift :
        (SSet.boundary n).ι ≫
            Subcomplex.lift (RelativeMorphism.map pt) h_range ≫
              (Subcomplex.fiber p b).ι = SSet.const e := by
      calc (SSet.boundary n).ι ≫
            Subcomplex.lift (RelativeMorphism.map pt) h_range ≫
              (Subcomplex.fiber p b).ι
          = (SSet.boundary n).ι ≫
              (Subcomplex.lift (RelativeMorphism.map pt) h_range ≫
                (Subcomplex.fiber p b).ι) := rfl
        _ = (SSet.boundary n).ι ≫ RelativeMorphism.map pt := by
            rw [h_lift]
        _ = SSet.const e := h_pt_comm
    have h_const_fiber :
        SSet.const (X := SSet.boundary n)
            (Subcomplex.fiber.basePoint (f := p) e hb) ≫
          (Subcomplex.fiber p b).ι = SSet.const e := by
      calc SSet.const (X := SSet.boundary n)
              (Subcomplex.fiber.basePoint (f := p) e hb) ≫
              (Subcomplex.fiber p b).ι
          = SSet.const
              (X := SSet.boundary n)
              ((Subcomplex.fiber p b).ι.app _
                (Subcomplex.fiber.basePoint (f := p) e hb)) := by
            rw [SSet.const_comp]
        _ = SSet.const (X := SSet.boundary n) e := by
            have hpoint : (Subcomplex.fiber p b).ι.app _
                (Subcomplex.fiber.basePoint (f := p) e hb) = e := by
              change (Subcomplex.fiber.basePoint (f := p) e hb).val = e
              exact Subcomplex.fiber.basePoint_val
            rw [hpoint]
    have h_eq :
        (SSet.boundary n).ι ≫
            Subcomplex.lift (RelativeMorphism.map pt) h_range =
          SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) := by
      apply (cancel_mono (Subcomplex.fiber p b).ι).mp
      calc (SSet.boundary n).ι ≫
            Subcomplex.lift (RelativeMorphism.map pt) h_range ≫
              (Subcomplex.fiber p b).ι
          = SSet.const e := h_boundary_lift
        _ = SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) ≫
              (Subcomplex.fiber p b).ι := h_const_fiber.symm
    -- Convert to RelativeMorphism comm form
    have h_ofSimplex :
        SSet.const (X := SSet.boundary n)
            (Subcomplex.fiber.basePoint (f := p) e hb) =
          SSet.const
              (X := SSet.boundary n)
              (Y := (Subcomplex.ofSimplex
                  (Subcomplex.fiber.basePoint (f := p) e hb) : SSet))
              (⟨Subcomplex.fiber.basePoint (f := p) e hb,
                Subcomplex.mem_ofSimplex_obj _⟩ :
                (Subcomplex.ofSimplex
                    (Subcomplex.fiber.basePoint (f := p) e hb) : SSet).obj
                  (op ⦋0⦌)) ≫
            (Subcomplex.ofSimplex
                (Subcomplex.fiber.basePoint (f := p) e hb)).ι := by
      rw [Subcomplex.ofSimplex_ι]
      rfl
    calc (SSet.boundary n).ι ≫
          Subcomplex.lift (RelativeMorphism.map pt) h_range
        = SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) := h_eq
      _ = SSet.const
            (⟨Subcomplex.fiber.basePoint (f := p) e hb,
              Subcomplex.mem_ofSimplex_obj _⟩ :
              (Subcomplex.ofSimplex
                  (Subcomplex.fiber.basePoint (f := p) e hb) : SSet).obj
                (op ⦋0⦌)) ≫
            (Subcomplex.ofSimplex
                (Subcomplex.fiber.basePoint (f := p) e hb)).ι := by
          rw [h_ofSimplex]

lemma connectingPtSimplexRep_ι {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p]
    (σ : B.PtSimplex (n + 1) b) :
    RelativeMorphism.map
        (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
        (Subcomplex.fiber p b).ι =
      RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ) := by
  simp [connectingPtSimplexRep, Subcomplex.lift_ι]

lemma connectingPtSimplexRep_face {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p]
    (σ : B.PtSimplex (n + 1) b) :
    Subcomplex.range
        (RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ)) ≤
      Subcomplex.fiber p b :=
  pt_range_le_fiber (e := e) p hb σ

lemma connectingPtSimplexRep_pointed {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p]
    (σ : B.PtSimplex (n + 1) b) :
    RelativeMorphism.map
        (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
        (Subcomplex.fiber p b).ι =
      RelativeMorphism.map (chosenLiftPt (e := e) (b := b) p hb σ) := by
  simp [connectingPtSimplexRep, Subcomplex.lift_ι]

-- =========================================================================
-- Layer 3: representative naturality under a commutative square
-- =========================================================================

private lemma chosenLift_horn {n : ℕ} (p : E ⟶ B)
    (hb : p.app _ e = b) [Fibration p] (σ : B.PtSimplex (n + 1) b) :
    (Λ[n + 1, Fin.last (n + 1)] : (Δ[n + 1] : SSet).Subcomplex).ι ≫
      SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) =
        SSet.const (X := (Λ[n + 1, Fin.last (n + 1)] :
          (Δ[n + 1] : SSet).Subcomplex).toSSet) e := by
  let lastIdx : Fin (n + 2) := Fin.last _
  let hornSub := Λ[n + 1, lastIdx]
  let φ : Δ[n + 1] ⟶ E :=
    SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)
  change hornSub.ι ≫ φ = SSet.const (X := hornSub.toSSet) e
  apply horn.hom_ext'
  intro j hj
  have hδ : stdSimplex.δ j ≫ φ = SSet.const (X := Δ[n]) e := by
    have h1 : stdSimplex.δ j ≫
        SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) =
      stdSimplex.δ j ≫ SSet.yonedaEquiv.symm
        ((chosenLiftData (e := e) (b := b) p hb σ).lift) := rfl
    rw [h1]
    let f : ∀ (k : Fin (n + 2)) (_ : k ≠ lastIdx), Δ[n] ⟶ E :=
      fun _ _ => SSet.const (X := Δ[n]) e
    have hf : horn.IsCompatible f := by
      cases n with
      | zero => trivial
      | succ m =>
        intro j k hj hk hjk
        simp [f, SSet.comp_const]
    have hcomm : ∀ (k : Fin (n + 2)) (hk : k ≠ lastIdx),
        f k hk ≫ p = stdSimplex.δ k ≫ RelativeMorphism.map σ := by
      intro k hk
      simp [f, SSet.const_comp, hb, SSet.PtSimplex.δ_map]
    have h2 : SSet.yonedaEquiv.symm
        ((chosenLiftData (e := e) (b := b) p hb σ).lift) =
      hf.lift p (RelativeMorphism.map σ) hcomm := by
      simp only [chosenLiftData, SSet.yonedaEquiv.symm_apply_apply]
    rw [h2]
    exact hf.δ_lift p (RelativeMorphism.map σ) hcomm j hj
  calc
    horn.ι lastIdx j hj ≫ (hornSub.ι ≫ φ) =
        stdSimplex.δ j ≫ φ := by rw [← Category.assoc, horn.ι_ι]
    _ = SSet.const (X := Δ[n]) e := hδ
    _ = horn.ι lastIdx j hj ≫
        SSet.const (X := hornSub.toSSet) e := by
      simp [SSet.comp_const]

/-- Every face `j ≠ Fin.last (n + 1)` of `yonedaEquiv.symm (chosenLift p hb σ)` is the
constant simplex at `e`. -/
lemma chosenLift_face_eq_const {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] (σ : B.PtSimplex (n + 1) b) (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)) :
    stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) =
      SSet.const (X := Δ[n]) e := by
  have hHorn := chosenLift_horn (p := p) (hb := hb) (σ := σ)
  calc stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)
      = (horn.ι (Fin.last (n + 1)) j hj ≫
          (Λ[n + 1, Fin.last (n + 1)] : (Δ[n + 1] : SSet).Subcomplex).ι) ≫
          SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) := by
        rw [horn.ι_ι]
      _ = horn.ι (Fin.last (n + 1)) j hj ≫
          ((Λ[n + 1, Fin.last (n + 1)] : (Δ[n + 1] : SSet).Subcomplex).ι ≫
            SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)) := by
        rw [Category.assoc]
      _ = horn.ι (Fin.last (n + 1)) j hj ≫
          SSet.const (X := (Λ[n + 1, Fin.last (n + 1)] :
            (Δ[n + 1] : SSet).Subcomplex).toSSet) e := by
        rw [hHorn]
      _ = SSet.const (X := Δ[n]) e := by
        simp [SSet.comp_const]

section Naturality

variable {E' B' : SSet.{u}} {e' : E' _⦋0⦌} {b' : B' _⦋0⦌}

lemma connectingPtSimplexRep_naturality_mapFiber_basePoint
    {p : E ⟶ B} {p' : E' ⟶ B'} (g : E ⟶ E') (h : B ⟶ B')
    (hc : g ≫ p' = p ≫ h)
    {hb : p.app _ e = b} {hb' : p'.app _ e' = b'}
    (hg : g.app _ e = e') (hh : h.app _ b = b')
    [Fibration p] [Fibration p'] :
    (Subcomplex.mapFiber (f := p) (f' := p') g h hc hh).app _
        (Subcomplex.fiber.basePoint (f := p) e hb) =
      Subcomplex.fiber.basePoint (f := p') e' hb' := by
  have h_base :=
    Subcomplex.mapFiber_app_basePoint (f := p) (f' := p') g h hc hh e hb
  calc (Subcomplex.mapFiber g h hc hh).app _
          (Subcomplex.fiber.basePoint (f := p) e hb)
      = Subcomplex.fiber.basePoint (f := p') (g.app _ e)
          (by
            have h1 : (g ≫ p').app _ e = (p ≫ h).app _ e :=
              congrArg (fun k : E ⟶ B' => k.app _ e) hc
            simp only [NatTrans.comp_app, comp_apply] at h1
            rw [hb, hh] at h1
            exact h1) := h_base
    _ = Subcomplex.fiber.basePoint (f := p') e' hb' := by
        apply Subtype.ext
        exact hg

private lemma lastFace_prism_const {Z : SSet.{u}} (q : ℕ)
    (z : Z _⦋0⦌)
    (prism : Δ[q + 1] ⊗ Δ[1] ⟶ Z)
    (hHorn : (Λ[q + 1, Fin.last (q + 1)].ι ▷ Δ[1]) ≫ prism =
      SSet.const z) :
    ((boundary q).ι ▷ Δ[1]) ≫
        (SSet.stdSimplex.δ (Fin.last (q + 1)) ▷ Δ[1]) ≫ prism =
      SSet.const z := by
  cases q with
  | zero =>
    ext _ ⟨⟨_, h⟩, _⟩
    simp at h
  | succ m =>
    have tensorRight_ext :
        ∀ (a b : (∂Δ[m + 1] : SSet) ⊗ Δ[1] ⟶ Z),
          (∀ (k : Fin (m + 2)),
            (SSet.boundary.ι k ▷ Δ[1]) ≫ a =
              (SSet.boundary.ι k ▷ Δ[1]) ≫ b) →
            a = b := by
      intro a b hb
      rw [← CategoryTheory.cancel_epi
        (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom]
      apply MonoidalClosed.curry_injective
      apply SSet.boundary.hom_ext (n := m)
      intro k
      simp only [← MonoidalClosed.curry_natural_left]
      apply congrArg MonoidalClosed.curry
      have hNat :
          (Δ[1] ◁ SSet.boundary.ι k) ≫
            (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom =
          (β_ Δ[1] (Δ[m] : SSet.{u})).hom ≫
            (SSet.boundary.ι k ▷ Δ[1]) :=
        BraidedCategory.braiding_naturality_right
          Δ[1] (SSet.boundary.ι k)
      calc (Δ[1] ◁ SSet.boundary.ι k) ≫
              (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom ≫ a
          = ((Δ[1] ◁ SSet.boundary.ι k) ≫
              (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom) ≫ a := by
            rw [Category.assoc]
        _ = ((β_ Δ[1] (Δ[m] : SSet.{u})).hom ≫
              (SSet.boundary.ι k ▷ Δ[1])) ≫ a := by
            rw [hNat]
        _ = (β_ Δ[1] (Δ[m] : SSet.{u})).hom ≫
              ((SSet.boundary.ι k ▷ Δ[1]) ≫ a) := by
            rw [← Category.assoc]
        _ = (β_ Δ[1] (Δ[m] : SSet.{u})).hom ≫
              ((SSet.boundary.ι k ▷ Δ[1]) ≫ b) := by
            rw [hb k]
        _ = ((β_ Δ[1] (Δ[m] : SSet.{u})).hom ≫
              (SSet.boundary.ι k ▷ Δ[1])) ≫ b := by
            rw [Category.assoc]
        _ = ((Δ[1] ◁ SSet.boundary.ι k) ≫
              (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom) ≫ b := by
            rw [← hNat]
        _ = (Δ[1] ◁ SSet.boundary.ι k) ≫
              (β_ Δ[1] (∂Δ[m + 1] : SSet.{u})).hom ≫ b := by
            rw [← Category.assoc]
    apply tensorRight_ext
    intro k
    have hι :
        SSet.boundary.ι k ≫ (SSet.boundary (m + 1)).ι =
          SSet.stdSimplex.δ (k : Fin (m + 2)) :=
      SSet.boundary.ι_ι k
    have hLast :
        (Fin.last (m + 2) : Fin (m + 3)) =
          (Fin.last (m + 1) : Fin (m + 2)).succ := rfl
    have hδ :
        SSet.stdSimplex.δ (k : Fin (m + 2)) ≫
          SSet.stdSimplex.δ (Fin.last (m + 2)) =
        SSet.stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
          SSet.stdSimplex.δ (Fin.castSucc k : Fin (m + 3)) := by
      calc SSet.stdSimplex.δ (k : Fin (m + 2)) ≫
              SSet.stdSimplex.δ (Fin.last (m + 2))
          = SSet.stdSimplex.δ (k : Fin (m + 2)) ≫
              SSet.stdSimplex.δ
                ((Fin.last (m + 1) : Fin (m + 2)).succ) := by
            rw [← hLast]
        _ = _ :=
            SSet.stdSimplex.δ_comp_δ (n := m) (Fin.le_last _)
    have hComp :
        SSet.boundary.ι k ≫ (SSet.boundary (m + 1)).ι ≫
          SSet.stdSimplex.δ (Fin.last (m + 2)) =
        SSet.stdSimplex.δ (Fin.last (m + 1) : Fin (m + 2)) ≫
          SSet.stdSimplex.δ (Fin.castSucc k : Fin (m + 3)) := by
      calc SSet.boundary.ι k ≫ (SSet.boundary (m + 1)).ι ≫
              SSet.stdSimplex.δ (Fin.last (m + 2))
          = (SSet.boundary.ι k ≫ (SSet.boundary (m + 1)).ι) ≫
              SSet.stdSimplex.δ (Fin.last (m + 2)) := by
            rw [Category.assoc]
        _ = SSet.stdSimplex.δ (k : Fin (m + 2)) ≫
              SSet.stdSimplex.δ (Fin.last (m + 2)) := by
            rw [hι]
        _ = _ := hδ
    have hHornWhisker :
        (SSet.stdSimplex.δ (Fin.castSucc k) ▷ Δ[1]) =
          (SSet.horn.ι (Fin.last (m + 2)) (Fin.castSucc k)
              (by simp [Fin.castSucc_ne_last]) ▷ Δ[1]) ≫
            ((Λ[m + 2, Fin.last (m + 2)]).ι ▷ Δ[1]) := by
      rw [← MonoidalCategory.comp_whiskerRight, SSet.horn.ι_ι]
    have hLeft :
        (SSet.boundary.ι k ▷ Δ[1]) ≫
            (SSet.boundary (m + 1)).ι ▷ Δ[1] ≫
              (SSet.stdSimplex.δ (Fin.last (m + 2)) ▷ Δ[1]) ≫ prism =
          SSet.const (X := Δ[m] ⊗ Δ[1]) z := by
      calc (SSet.boundary.ι k ▷ Δ[1]) ≫
              (SSet.boundary (m + 1)).ι ▷ Δ[1] ≫
                (SSet.stdSimplex.δ (Fin.last (m + 2)) ▷ Δ[1]) ≫ prism
          = ((SSet.boundary.ι k ≫ (SSet.boundary (m + 1)).ι ≫
                SSet.stdSimplex.δ (Fin.last (m + 2))) ▷ Δ[1]) ≫ prism := by
            simp only [MonoidalCategory.comp_whiskerRight,
              Category.assoc]
        _ = ((SSet.stdSimplex.δ (Fin.last (m + 1)) ≫
                SSet.stdSimplex.δ (Fin.castSucc k)) ▷ Δ[1]) ≫ prism := by
            rw [hComp]
        _ = (SSet.stdSimplex.δ (Fin.last (m + 1)) ▷ Δ[1]) ≫
              (SSet.stdSimplex.δ (Fin.castSucc k) ▷ Δ[1]) ≫ prism := by
            rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
        _ = (SSet.stdSimplex.δ (Fin.last (m + 1)) ▷ Δ[1]) ≫
              (SSet.horn.ι (Fin.last (m + 2)) (Fin.castSucc k) _ ▷ Δ[1]) ≫
                ((Λ[m + 2, Fin.last (m + 2)]).ι ▷ Δ[1]) ≫ prism := by
            rw [hHornWhisker, Category.assoc]
        _ = (SSet.stdSimplex.δ (Fin.last (m + 1)) ▷ Δ[1]) ≫
              (SSet.horn.ι (Fin.last (m + 2)) (Fin.castSucc k) _ ▷ Δ[1]) ≫
                SSet.const
                  (X := (Λ[m + 2, Fin.last (m + 2)] : SSet) ⊗ Δ[1]) z := by
            rw [hHorn]
        _ = SSet.const _ := by
            simp [SSet.comp_const]
    have hRight :
        (SSet.boundary.ι k ▷ Δ[1]) ≫
            SSet.const (X := (∂Δ[m + 1] : SSet) ⊗ Δ[1]) z =
          SSet.const (X := Δ[m] ⊗ Δ[1]) z := by
      simp [SSet.comp_const]
    rw [hLeft, hRight]

lemma connectingPtSimplexRep_naturality_rel {n : ℕ}
    {p : E ⟶ B} {p' : E' ⟶ B'} (g : E ⟶ E') (h : B ⟶ B')
    (hc : g ≫ p' = p ≫ h)
    {hb : p.app _ e = b} {hb' : p'.app _ e' = b'}
    (hg : g.app _ e = e') (hh : h.app _ b = b')
    [Fibration p] [Fibration p']
    (σ : B.PtSimplex (n + 1) b) :
    Nonempty
        ((SSet.PtSimplex.map
            (Subcomplex.mapFiber (f := p) (f' := p') g h hc hh)
            (connectingPtSimplexRep_naturality_mapFiber_basePoint
              g h hc hg hh)
            (connectingPtSimplexRep (p := p) (e := e) hb σ)).RelStruct₀
          (connectingPtSimplexRep (p := p') (e := e') hb'
            (SSet.PtSimplex.map h hh σ))) := by
  -- Prism base: Δ[n+1] ⊗ Δ[1] → B' via fst ≫ mapped simplex
  let σ' : B'.PtSimplex (n + 1) b' := SSet.PtSimplex.map h hh σ
  let prismBase := fst (Δ[n + 1]) (Δ[1]) ≫ RelativeMorphism.map σ'
  -- Last horn and boundary of interval
  let lastIdx : Fin (n + 2) := Fin.last _
  let hornSub := Λ[n + 1, lastIdx]
  let T := ∂Δ[1]
  -- Chosen fillers
  let φ : Δ[n + 1] ⟶ E := SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)
  let φ' : Δ[n + 1] ⟶ E' :=
    SSet.yonedaEquiv.symm (chosenLift (e := e') (b := b') p' hb' σ')
  let φg : Δ[n + 1] ⟶ E' := φ ≫ g
  have hφg_proj : φg ≫ p' = RelativeMorphism.map σ' := by
    have h1 : φ ≫ p = RelativeMorphism.map σ := chosenLift_projects (p := p) (hb := hb) σ
    calc φg ≫ p' = φ ≫ (g ≫ p') := by rw [Category.assoc]
      _ = φ ≫ (p ≫ h) := by rw [hc]
      _ = (φ ≫ p) ≫ h := by rw [Category.assoc]
      _ = RelativeMorphism.map σ ≫ h := by rw [h1]
      _ = RelativeMorphism.map σ' := rfl
  have hφ'_proj : φ' ≫ p' = RelativeMorphism.map σ' :=
    chosenLift_projects (p := p') (hb := hb') σ'
  -- Endpoint isomorphisms and right unitor
  let iso0 : Δ[0] ≅ (SSet.stdSimplex.face {0} : SSet) :=
    SSet.stdSimplex.faceSingletonIso (0 : Fin 2)
  let iso1 : Δ[0] ≅ (SSet.stdSimplex.face {1} : SSet) :=
    SSet.stdSimplex.faceSingletonIso (1 : Fin 2)
  -- Maps on X ⊗ face {0} and X ⊗ face {1}
  let map0 : Δ[n + 1] ⊗ (SSet.stdSimplex.face {0} : SSet) ⟶ E' :=
    (Δ[n + 1] ◁ iso0.inv) ≫ (SSet.stdSimplex.rightUnitor (Δ[n + 1])).hom ≫ φg
  let map1 : Δ[n + 1] ⊗ (SSet.stdSimplex.face {1} : SSet) ⟶ E' :=
    (Δ[n + 1] ◁ iso1.inv) ≫ (SSet.stdSimplex.rightUnitor (Δ[n + 1])).hom ≫ φ'
  -- Bicartesian square for T
  have hT_bicart : SSet.Subcomplex.BicartSq (⊥ : SSet.Subcomplex (Δ[1]))
      (SSet.stdSimplex.face {0}) (SSet.stdSimplex.face {1}) T := by
    constructor
    · -- sup_eq: face {0} ⊔ face {1} = ∂Δ[1]
      have h0 : (({0} : Finset (Fin 2)) = ({1}ᶜ : Finset (Fin 2))) := by decide
      have h1 : (({1} : Finset (Fin 2)) = ({0}ᶜ : Finset (Fin 2))) := by decide
      calc SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊔
            SSet.stdSimplex.face ({1} : Finset (Fin 2))
          = SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) ⊔
            SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) := by
            rw [← h0, ← h1]
        _ = SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) ⊔
            SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) := by
            rw [sup_comm]
        _ = ⨆ (i : Fin 2), SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2))) := by
            apply le_antisymm
            · apply sup_le
              · exact le_iSup
                    (f := fun i : Fin 2 =>
                      SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 0
              · exact le_iSup
                    (f := fun i : Fin 2 =>
                      SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 1
            · apply iSup_le
              intro i
              fin_cases i
              · exact le_sup_left
              · exact le_sup_right
        _ = SSet.boundary 1 := (SSet.boundary_eq_iSup (n := 1)).symm
        _ = T := rfl
    · -- inf_eq: face {0} ⊓ face {1} = ⊥
      have h_eq :
          SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊓
            SSet.stdSimplex.face ({1} : Finset (Fin 2)) =
          SSet.stdSimplex.face (({0} : Finset (Fin 2)) ⊓ {1}) := by
        rw [SSet.stdSimplex.face_inter_face]
      rw [h_eq]
      have h_empty : (({0} : Finset (Fin 2)) ⊓ {1} : Finset (Fin 2)) = ∅ := by decide
      rw [h_empty]
      exact SSet.stdSimplex.face_empty 1
  have hT_isPushout := SSet.Subcomplex.BicartSq.isPushout hT_bicart
  -- Lift to product X ⊗ T via prodIso/topIso
  -- Construct endpoint map on X ⊗ T
  -- For brevity, use prod subcomplexes
  let X : SSet := Δ[n + 1]
  let Y : SSet := Δ[1]
  let P0 : SSet.Subcomplex (X ⊗ Y) :=
    (⊤ : SSet.Subcomplex X).prod
      (SSet.stdSimplex.face ({0} : Finset (Fin 2)) :
        SSet.Subcomplex (Δ[1]))
  let P1 : SSet.Subcomplex (X ⊗ Y) :=
    (⊤ : SSet.Subcomplex X).prod
      (SSet.stdSimplex.face ({1} : Finset (Fin 2)) :
        SSet.Subcomplex (Δ[1]))
  let PT : SSet.Subcomplex (X ⊗ Y) := (⊤ : SSet.Subcomplex X).prod T
  have hProdBicart : SSet.Subcomplex.BicartSq
      (⊥ : SSet.Subcomplex (X ⊗ Y)) P0 P1 PT := by
    constructor
    · ext m ⟨x, y⟩
      change
        ((x ∈ (Set.univ : Set (X.obj m)) ∧
            y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∨
          (x ∈ (Set.univ : Set (X.obj m)) ∧
            y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔
        (x ∈ (Set.univ : Set (X.obj m)) ∧ y ∈ T.obj m)
      simp only [Set.mem_univ, true_and]
      have hm := congrArg (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.sup_eq
      simpa only [Subfunctor.max_obj, Set.mem_union] using Set.ext_iff.mp hm y
    · ext m ⟨x, y⟩
      change
        ((x ∈ (Set.univ : Set (X.obj m)) ∧
            y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∧
          (x ∈ (Set.univ : Set (X.obj m)) ∧
            y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔ False
      simp only [Set.mem_univ, true_and]
      have hm := congrArg (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.inf_eq
      have hy := Set.ext_iff.mp hm y
      simpa only [Subfunctor.min_obj, Set.mem_inter_iff,
        Subfunctor.bot_obj, Set.bot_eq_empty, Set.mem_empty_iff_false] using hy
  have hProdPushout := SSet.Subcomplex.BicartSq.isPushout hProdBicart
  -- Isomorphisms all the way to X ⊗ endpoint / T using prodIso + whiskerRightIso of topIso
  let isoP0 : P0.toSSet ≅ X ⊗ (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
        (SSet.stdSimplex.face ({0} : Finset (Fin 2)) :
          SSet.Subcomplex (Δ[1])) ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X)
        (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet)
  let isoP1 : P1.toSSet ≅ X ⊗ (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
        (SSet.stdSimplex.face ({1} : Finset (Fin 2)) :
          SSet.Subcomplex (Δ[1])) ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X)
        (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet)
  let isoPT : PT.toSSet ≅ X ⊗ (T : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X) T ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X) (T : SSet)
  -- Component maps P0 → E' and P1 → E' via hom sides followed by map0/map1
  let compMap0 : P0.toSSet ⟶ E' := isoP0.hom ≫ map0
  let compMap1 : P1.toSSet ⟶ E' := isoP1.hom ≫ map1
  have hAgreeProd :
      SSet.Subcomplex.homOfLE
          (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P0 from bot_le) ≫ compMap0 =
        SSet.Subcomplex.homOfLE
          (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P1 from bot_le) ≫ compMap1 := by
    apply Subsingleton.elim
  let endpointMapPT : PT.toSSet ⟶ E' := hProdPushout.desc compMap0 compMap1 hAgreeProd
  let endpointMap : X ⊗ (T : SSet) ⟶ E' := isoPT.inv ≫ endpointMapPT
  -- Horn constant map
  have hHornConst :
      hornSub.ι ≫ φg = SSet.const (X := hornSub.toSSet) e' ∧
        hornSub.ι ≫ φ' = SSet.const (X := hornSub.toSSet) e' := by
    have hφ_horn : hornSub.ι ≫ φ = SSet.const (X := hornSub.toSSet) e := by
      apply horn.hom_ext'
      intro j hj
      have hδ : stdSimplex.δ j ≫ φ = SSet.const (X := Δ[n]) e := by
        -- φ = yonedaEquiv.symm (chosenLift ...) and chosenLift's underlying
        -- filler has δ j = const e for j ≠ last by horn.IsCompatible.δ_lift.
        -- We make this explicit via simp with chosenLift and yoneda.
        have h1 :
            stdSimplex.δ j ≫
              SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) =
            stdSimplex.δ j ≫
              SSet.yonedaEquiv.symm
                ((chosenLiftData (e := e) (b := b) p hb σ).lift) := rfl
        rw [h1]
        -- Now use the fact that (chosenLiftData ...).lift = yonedaEquiv (hf.lift)
        -- for f = const e; its δ is const e.
        -- We re-derive f/hf/hcomm and show the chosen lift coincides via simp.
        let f : ∀ (k : Fin (n + 2)) (_ : k ≠ lastIdx), Δ[n] ⟶ E :=
          fun _ _ => SSet.const (X := Δ[n]) e
        have hf : horn.IsCompatible f := by
          cases n with
          | zero => trivial
          | succ m =>
            intro j k hj hk hjk
            simp [f, SSet.comp_const]
        have hcomm : ∀ (k : Fin (n + 2)) (hk : k ≠ lastIdx),
            f k hk ≫ p = stdSimplex.δ k ≫ RelativeMorphism.map σ := by
          intro k hk
          simp [f, SSet.const_comp, hb, SSet.PtSimplex.δ_map]
        have h2 : SSet.yonedaEquiv.symm ((chosenLiftData (e := e) (b := b) p hb σ).lift)
            = hf.lift p (RelativeMorphism.map σ) hcomm := by
          simp only [chosenLiftData, SSet.yonedaEquiv.symm_apply_apply]
        rw [h2]
        exact hf.δ_lift p (RelativeMorphism.map σ) hcomm j hj
      calc horn.ι lastIdx j hj ≫ (hornSub.ι ≫ φ)
          = stdSimplex.δ j ≫ φ := by rw [← Category.assoc, horn.ι_ι]
        _ = SSet.const (X := Δ[n]) e := hδ
        _ = horn.ι lastIdx j hj ≫ SSet.const (X := hornSub.toSSet) e := by
            simp [SSet.comp_const]
    have hφ'_horn : hornSub.ι ≫ φ' = SSet.const (X := hornSub.toSSet) e' := by
      apply horn.hom_ext'
      intro j hj
      have hδ : stdSimplex.δ j ≫ φ' = SSet.const (X := Δ[n]) e' := by
        have h1 :
            stdSimplex.δ j ≫
              SSet.yonedaEquiv.symm (chosenLift (e := e') (b := b') p' hb' σ') =
            stdSimplex.δ j ≫
              SSet.yonedaEquiv.symm
                ((chosenLiftData (e := e') (b := b') p' hb' σ').lift) := rfl
        rw [h1]
        let f' : ∀ (k : Fin (n + 2)) (_ : k ≠ lastIdx), Δ[n] ⟶ E' :=
          fun _ _ => SSet.const (X := Δ[n]) e'
        have hf' : horn.IsCompatible f' := by
          cases n with
          | zero => trivial
          | succ m =>
            intro j k hj hk hjk
            simp [f', SSet.comp_const]
        have hcomm' : ∀ (k : Fin (n + 2)) (hk : k ≠ lastIdx),
            f' k hk ≫ p' = stdSimplex.δ k ≫ RelativeMorphism.map σ' := by
          intro k hk
          simp [f', SSet.const_comp, hb', SSet.PtSimplex.δ_map]
        have h2 : SSet.yonedaEquiv.symm ((chosenLiftData (e := e') (b := b') p' hb' σ').lift)
            = hf'.lift p' (RelativeMorphism.map σ') hcomm' := by
          simp only [chosenLiftData, SSet.yonedaEquiv.symm_apply_apply]
        rw [h2]
        exact hf'.δ_lift p' (RelativeMorphism.map σ') hcomm' j hj
      calc horn.ι lastIdx j hj ≫ (hornSub.ι ≫ φ')
          = stdSimplex.δ j ≫ φ' := by rw [← Category.assoc, horn.ι_ι]
        _ = SSet.const (X := Δ[n]) e' := hδ
        _ = horn.ι lastIdx j hj ≫ SSet.const (X := hornSub.toSSet) e' := by
            simp [SSet.comp_const]
    constructor
    · calc hornSub.ι ≫ φg = hornSub.ι ≫ (φ ≫ g) := rfl
        _ = (hornSub.ι ≫ φ) ≫ g := by rw [Category.assoc]
        _ = SSet.const (X := hornSub.toSSet) e ≫ g := by rw [hφ_horn]
        _ = SSet.const (X := hornSub.toSSet) (g.app _ e) := by
            simp [SSet.const_comp]
        _ = SSet.const (X := hornSub.toSSet) e' := by rw [hg]
    · exact hφ'_horn
  -- Glue via unionProd.isPushout
  have hIso0 : isoP0.hom ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) =
      SSet.Subcomplex.homOfLE hProdBicart.le₂₄ ≫ isoPT.hom := by
    ext m z
    · rfl
    · rfl
  have hIso1 : isoP1.hom ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) =
      SSet.Subcomplex.homOfLE hProdBicart.le₃₄ ≫ isoPT.hom := by
    ext m z
    · rfl
    · rfl
  have hEndpoint0 :
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ endpointMap = map0 := by
    apply (cancel_epi isoP0.hom).mp
    rw [← Category.assoc, hIso0]
    simp [endpointMap, endpointMapPT, compMap0]
  have hEndpoint1 :
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ endpointMap = map1 := by
    apply (cancel_epi isoP1.hom).mp
    rw [← Category.assoc, hIso1]
    simp [endpointMap, endpointMapPT, compMap1]
  have hHornMap0 :
      (hornSub.ι ▷ (SSet.stdSimplex.face {0} : SSet)) ≫ map0 =
        SSet.const (X := (hornSub : SSet) ⊗
          (SSet.stdSimplex.face {0} : SSet)) e' := by
    dsimp [map0]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
    rw [hHornConst.1]
    simp
  have hHornMap1 :
      (hornSub.ι ▷ (SSet.stdSimplex.face {1} : SSet)) ≫ map1 =
        SSet.const (X := (hornSub : SSet) ⊗
          (SSet.stdSimplex.face {1} : SSet)) e' := by
    dsimp [map1]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
    rw [hHornConst.2]
    simp
  have hHornTPushout :=
    (tensorLeft (hornSub : SSet)).map_isPushout hT_isPushout
  have hEndpointHorn : (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
      SSet.const (X := (hornSub : SSet) ⊗ (T : SSet)) e' := by
    apply hHornTPushout.hom_ext
    · rw [SSet.comp_const]
      change (((hornSub : SSet) ◁
          SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
        (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
      calc
        _ = (hornSub.ι ▷
            (SSet.stdSimplex.face {0} : SSet)) ≫
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
                endpointMap) := by
          rw [MonoidalCategory.whisker_exchange, Category.assoc]
        _ = (hornSub.ι ▷
            (SSet.stdSimplex.face {0} : SSet)) ≫ map0 := by
          rw [hEndpoint0]
        _ = _ := hHornMap0
    · rw [SSet.comp_const]
      change (((hornSub : SSet) ◁
          SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
        (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
      calc
        _ = (hornSub.ι ▷
            (SSet.stdSimplex.face {1} : SSet)) ≫
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
                endpointMap) := by
          rw [MonoidalCategory.whisker_exchange, Category.assoc]
        _ = (hornSub.ι ▷
            (SSet.stdSimplex.face {1} : SSet)) ≫ map1 := by
          rw [hEndpoint1]
        _ = _ := hHornMap1
  have hCompatGlue :
      (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
        ((hornSub : SSet) ◁ T.ι) ≫
          SSet.const (X := (hornSub : SSet) ⊗ Y) e' := by
    rw [hEndpointHorn]
    simp
  let hGlue : (hornSub.unionProd T).toSSet ⟶ E' :=
    (SSet.Subcomplex.unionProd.isPushout hornSub T).desc endpointMap
      (SSet.const (X := (hornSub : SSet) ⊗ Y) e') hCompatGlue
  -- Anodyne lifting
  have hMap0Proj : map0 ≫ p' =
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
        (X ◁ T.ι) ≫ prismBase := by
    dsimp [map0, prismBase]
    rw [Category.assoc, Category.assoc, hφg_proj]
    ext m z
    rfl
  have hMap1Proj : map1 ≫ p' =
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
        (X ◁ T.ι) ≫ prismBase := by
    dsimp [map1, prismBase]
    rw [Category.assoc, Category.assoc, hφ'_proj]
    ext m z
    rfl
  have hXTPushout := (tensorLeft X).map_isPushout hT_isPushout
  have hEndpointProj : endpointMap ≫ p' = (X ◁ T.ι) ≫ prismBase := by
    apply hXTPushout.hom_ext
    · change ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ endpointMap) ≫ p' = _
      rw [hEndpoint0]
      exact hMap0Proj
    · change ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ endpointMap) ≫ p' = _
      rw [hEndpoint1]
      exact hMap1Proj
  have hSigmaHorn : hornSub.ι ≫ RelativeMorphism.map σ' =
      SSet.const (X := hornSub.toSSet) b' := by
    calc
      hornSub.ι ≫ RelativeMorphism.map σ' =
          (hornSub.ι ≫ φg) ≫ p' := by rw [Category.assoc, hφg_proj]
      _ = SSet.const (X := hornSub.toSSet) e' ≫ p' := by rw [hHornConst.1]
      _ = SSet.const (X := hornSub.toSSet) b' := by
        simp [SSet.const_comp, hb']
  have hHornBase : (hornSub.ι ▷ Y) ≫ prismBase =
      SSet.const (X := (hornSub : SSet) ⊗ Y) b' := by
    dsimp [prismBase]
    rw [CartesianMonoidalCategory.whiskerRight_fst_assoc, hSigmaHorn]
    simp
  have hHornProj :
      SSet.const (X := (hornSub : SSet) ⊗ Y) e' ≫ p' =
        (hornSub.ι ▷ Y) ≫ prismBase := by
    rw [hHornBase]
    simp [SSet.const_comp, hb']
  have hGlueLeft : SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue = endpointMap := by
    dsimp [hGlue]
    simp
  have hGlueRight : SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue =
      SSet.const (X := (hornSub : SSet) ⊗ Y) e' := by
    dsimp [hGlue]
    simp
  have hGlueProj : hGlue ≫ p' = (hornSub.unionProd T).ι ≫ prismBase := by
    apply (SSet.Subcomplex.unionProd.isPushout hornSub T).hom_ext
    · rw [← Category.assoc, hGlueLeft, hEndpointProj]
      rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
    · rw [← Category.assoc, hGlueRight, hHornProj]
      rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
  let sq : CommSq hGlue (hornSub.unionProd T).ι p' prismBase :=
    CommSq.mk hGlueProj
  have hAnodyne : SSet.anodyneExtensions (hornSub.unionProd T).ι := by
    simpa [hornSub, T, lastIdx] using
      SSet.prodStdSimplex.anodyneExtensions_unionProd_ι lastIdx 1
  have : HasLiftingProperty (hornSub.unionProd T).ι p' :=
    hAnodyne p' (by rwa [← HomotopicalAlgebra.fibration_iff])
  have hLift : ∃ (prism : X ⊗ Y ⟶ E'), prism ≫ p' = prismBase ∧
      (hornSub.unionProd T).ι ≫ prism = hGlue :=
    ⟨sq.lift, sq.fac_right, sq.fac_left⟩
  -- Restrict last face and convert to RelStruct₀
  have hPrismT : (X ◁ T.ι) ≫ hLift.choose = endpointMap := by
    calc
      (X ◁ T.ι) ≫ hLift.choose =
          SSet.Subcomplex.unionProd.ι₁ hornSub T ≫
            (hornSub.unionProd T).ι ≫ hLift.choose := by
              rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
      _ = SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue := by
            rw [hLift.choose_spec.2]
      _ = endpointMap := hGlueLeft
  have hPrismZero : SSet.ι₀ ≫ hLift.choose = φg := by
    rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_one_assoc]
    rw [← SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₂₄]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [hPrismT, hEndpoint0]
    simp [map0, iso0]
  have hPrismOne : SSet.ι₁ ≫ hLift.choose = φ' := by
    rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
    rw [← SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₃₄]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [hPrismT, hEndpoint1]
    simp [map1, iso1]
  have hPrismHorn : (hornSub.ι ▷ Y) ≫ hLift.choose =
      SSet.const (X := (hornSub : SSet) ⊗ Y) e' := by
    calc
      (hornSub.ι ▷ Y) ≫ hLift.choose =
          SSet.Subcomplex.unionProd.ι₂ hornSub T ≫
            (hornSub.unionProd T).ι ≫ hLift.choose := by
              rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
      _ = SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue := by
            rw [hLift.choose_spec.2]
      _ = _ := hGlueRight
  have hFaceRelE :
      ((SSet.boundary n).ι ▷ Δ[1]) ≫
        (SSet.stdSimplex.δ lastIdx ▷ Δ[1]) ≫ hLift.choose =
        SSet.const (X := (SSet.boundary n : SSet) ⊗ Δ[1]) e' := by
    simpa [hornSub, lastIdx, X, Y] using
      lastFace_prism_const n e' hLift.choose
        (by simpa [hornSub, lastIdx, X, Y] using hPrismHorn)
  let facePrism : Δ[n] ⊗ Δ[1] ⟶ E' :=
    (SSet.stdSimplex.δ lastIdx ▷ Δ[1]) ≫ hLift.choose
  have hface : facePrism ≫ p' =
      SSet.const (X := Δ[n] ⊗ Δ[1]) b' := by
    dsimp [facePrism]
    rw [Category.assoc, hLift.choose_spec.1]
    dsimp [prismBase]
    rw [CartesianMonoidalCategory.whiskerRight_fst_assoc]
    dsimp [σ', lastIdx]
    rw [SSet.PtSimplex.δ_map]
    simp [SSet.comp_const]
  have hrange : SSet.Subcomplex.range facePrism ≤
      SSet.Subcomplex.fiber p' b' := by
    rw [SSet.Subcomplex.range_le_fiber_iff]
    exact hface
  let fiberPrism : Δ[n] ⊗ Δ[1] ⟶
      (SSet.Subcomplex.fiber p' b' : SSet) :=
    SSet.Subcomplex.lift facePrism hrange
  have hFiberι : fiberPrism ≫ (SSet.Subcomplex.fiber p' b').ι =
      facePrism := SSet.Subcomplex.lift_ι _ _
  let src : (SSet.Subcomplex.fiber p' b' : SSet).PtSimplex n
      (SSet.Subcomplex.fiber.basePoint (f := p') e' hb') :=
    SSet.PtSimplex.map
      (SSet.Subcomplex.mapFiber (f := p) (f' := p') g h hc hh)
      (connectingPtSimplexRep_naturality_mapFiber_basePoint g h hc hg hh)
      (connectingPtSimplexRep (p := p) (e := e) hb σ)
  let tgt : (SSet.Subcomplex.fiber p' b' : SSet).PtSimplex n
      (SSet.Subcomplex.fiber.basePoint (f := p') e' hb') :=
    connectingPtSimplexRep (p := p') (e := e') hb'
      (SSet.PtSimplex.map h hh σ)
  have hSourceι : RelativeMorphism.map src ≫
      (SSet.Subcomplex.fiber p' b').ι =
        SSet.stdSimplex.δ lastIdx ≫ φg := by
    change
      (RelativeMorphism.map
          (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
        SSet.Subcomplex.mapFiber (f := p) (f' := p') g h hc hh) ≫
        (SSet.Subcomplex.fiber p' b').ι = _
    calc
      (RelativeMorphism.map
          (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
        SSet.Subcomplex.mapFiber (f := p) (f' := p') g h hc hh) ≫
          (SSet.Subcomplex.fiber p' b').ι =
        RelativeMorphism.map
          (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
            ((SSet.Subcomplex.fiber p b).ι ≫ g) := by
              rw [Category.assoc, SSet.Subcomplex.mapFiber_ι]
      _ = (RelativeMorphism.map
          (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
            (SSet.Subcomplex.fiber p b).ι) ≫ g := by
              rw [Category.assoc]
      _ = RelativeMorphism.map
          (chosenLiftPt (e := e) (b := b) p hb σ) ≫ g := by
              rw [connectingPtSimplexRep_ι]
      _ = (SSet.stdSimplex.δ lastIdx ≫ φ) ≫ g := by
              rw [chosenLift_face_eq]
      _ = SSet.stdSimplex.δ lastIdx ≫ φg := by
              simp [φg, Category.assoc]
  have hTargetι : RelativeMorphism.map tgt ≫
      (SSet.Subcomplex.fiber p' b').ι =
        SSet.stdSimplex.δ lastIdx ≫ φ' := by
    dsimp [tgt]
    rw [connectingPtSimplexRep_ι, chosenLift_face_eq]
  let H : src.Homotopy tgt :=
    { h := fiberPrism
      h₀ := by
        apply (cancel_mono (SSet.Subcomplex.fiber p' b').ι).mp
        rw [Category.assoc, hFiberι]
        rw [SSet.ι₀_comp_assoc, hPrismZero, hSourceι]
      h₁ := by
        apply (cancel_mono (SSet.Subcomplex.fiber p' b').ι).mp
        rw [Category.assoc, hFiberι]
        rw [SSet.ι₁_comp_assoc, hPrismOne, hTargetι]
      rel := by
        apply (cancel_mono (SSet.Subcomplex.fiber p' b').ι).mp
        rw [Category.assoc, hFiberι]
        rw [hFaceRelE]
        ext m z
        rfl }
  have hRestrict : Nonempty
      ((SSet.PtSimplex.map
        (Subcomplex.mapFiber (f := p) (f' := p') g h hc hh)
        (connectingPtSimplexRep_naturality_mapFiber_basePoint g h hc hg hh)
        (connectingPtSimplexRep (p := p) (e := e) hb σ)).RelStruct₀
      (connectingPtSimplexRep (p := p') (e := e') hb'
        (SSet.PtSimplex.map h hh σ))) :=
    ⟨SSet.PtSimplex.Homotopy.relStruct₀ H⟩
  exact hRestrict

end Naturality

-- =========================================================================
-- Layer 4: quotient descent and exactness for the connecting map
--         Well-definedness and exactness at the base and fiber terms.
-- =========================================================================

section QuotientDescent

lemma connectingPtSimplexRep_prism_rel {n : ℕ}
    (p : E ⟶ B) (e : E _⦋0⦌) {b : B _⦋0⦌}
    (hb : p.app _ e = b) [Fibration p]
    (σ τ : B.PtSimplex (n + 1) b)
    (K : Δ[n + 1] ⊗ Δ[1] ⟶ B)
    (hK₀ : SSet.ι₀ ≫ K = RelativeMorphism.map σ)
    (hK₁ : SSet.ι₁ ≫ K = RelativeMorphism.map τ)
    (hKrel : ((SSet.boundary (n + 1)).ι ▷ Δ[1]) ≫ K =
      SSet.const (X := (SSet.boundary (n + 1) : SSet) ⊗ Δ[1]) b) :
    Nonempty
      ((connectingPtSimplexRep (p := p) (e := e) hb σ).RelStruct₀
        (connectingPtSimplexRep (p := p) (e := e) hb τ)) := by
  let lastIdx : Fin (n + 2) := Fin.last _
  let hornSub := Λ[n + 1, lastIdx]
  let T := ∂Δ[1]
  let φ0 : Δ[n + 1] ⟶ E :=
    SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)
  let φ1 : Δ[n + 1] ⟶ E :=
    SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb τ)
  have hφ0_proj : φ0 ≫ p = RelativeMorphism.map σ :=
    chosenLift_projects (p := p) (hb := hb) σ
  have hφ1_proj : φ1 ≫ p = RelativeMorphism.map τ :=
    chosenLift_projects (p := p) (hb := hb) τ
  let iso0 : Δ[0] ≅ (SSet.stdSimplex.face {0} : SSet) :=
    SSet.stdSimplex.faceSingletonIso (0 : Fin 2)
  let iso1 : Δ[0] ≅ (SSet.stdSimplex.face {1} : SSet) :=
    SSet.stdSimplex.faceSingletonIso (1 : Fin 2)
  let map0 : Δ[n + 1] ⊗ (SSet.stdSimplex.face {0} : SSet) ⟶ E :=
    (Δ[n + 1] ◁ iso0.inv) ≫ (SSet.stdSimplex.rightUnitor (Δ[n + 1])).hom ≫ φ0
  let map1 : Δ[n + 1] ⊗ (SSet.stdSimplex.face {1} : SSet) ⟶ E :=
    (Δ[n + 1] ◁ iso1.inv) ≫ (SSet.stdSimplex.rightUnitor (Δ[n + 1])).hom ≫ φ1
  have hT_bicart : SSet.Subcomplex.BicartSq
      (⊥ : SSet.Subcomplex (Δ[1]))
      (SSet.stdSimplex.face {0}) (SSet.stdSimplex.face {1}) T := by
    constructor
    · have h0 : (({0} : Finset (Fin 2)) = ({1}ᶜ : Finset (Fin 2))) := by decide
      have h1 : (({1} : Finset (Fin 2)) = ({0}ᶜ : Finset (Fin 2))) := by decide
      calc
        SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊔
            SSet.stdSimplex.face ({1} : Finset (Fin 2)) =
          SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) ⊔
            SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) := by
          rw [← h0, ← h1]
        _ = SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) ⊔
            SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) := by
          rw [sup_comm]
        _ = ⨆ (i : Fin 2), SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2))) := by
            apply le_antisymm
            · apply sup_le
              · exact le_iSup
                    (f := fun i : Fin 2 =>
                      SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 0
              · exact le_iSup
                    (f := fun i : Fin 2 =>
                      SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 1
            · apply iSup_le
              intro i
              fin_cases i
              · exact le_sup_left
              · exact le_sup_right
        _ = SSet.boundary 1 := (SSet.boundary_eq_iSup (n := 1)).symm
        _ = T := rfl
    · have h_eq : SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊓
          SSet.stdSimplex.face ({1} : Finset (Fin 2)) =
          SSet.stdSimplex.face (({0} : Finset (Fin 2)) ⊓ {1}) := by
          rw [SSet.stdSimplex.face_inter_face]
      rw [h_eq]
      have h_empty : (({0} : Finset (Fin 2)) ⊓ {1} : Finset (Fin 2)) = ∅ := by decide
      rw [h_empty]
      exact SSet.stdSimplex.face_empty 1
  have hT_isPushout := SSet.Subcomplex.BicartSq.isPushout hT_bicart
  let X : SSet := Δ[n + 1]
  let Y : SSet := Δ[1]
  let P0 : SSet.Subcomplex (X ⊗ Y) := (⊤ : SSet.Subcomplex X).prod
    (SSet.stdSimplex.face {0} : SSet.Subcomplex (Δ[1]))
  let P1 : SSet.Subcomplex (X ⊗ Y) := (⊤ : SSet.Subcomplex X).prod
    (SSet.stdSimplex.face {1} : SSet.Subcomplex (Δ[1]))
  let PT : SSet.Subcomplex (X ⊗ Y) := (⊤ : SSet.Subcomplex X).prod T
  have hProdBicart : SSet.Subcomplex.BicartSq
      (⊥ : SSet.Subcomplex (X ⊗ Y)) P0 P1 PT := by
    constructor
    · ext m ⟨x, y⟩
      change
          (((x ∈ (Set.univ : Set (X.obj m)) ∧
              y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∨
            (x ∈ (Set.univ : Set (X.obj m)) ∧
              y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔
          (x ∈ (Set.univ : Set (X.obj m)) ∧ y ∈ T.obj m))
      simp only [Set.mem_univ, true_and]
      have hm := congrArg (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.sup_eq
      simpa only [Subfunctor.max_obj, Set.mem_union] using Set.ext_iff.mp hm y
    · ext m ⟨x, y⟩
      change
          (((x ∈ (Set.univ : Set (X.obj m)) ∧
              y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∧
            (x ∈ (Set.univ : Set (X.obj m)) ∧
              y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔
          False)
      simp only [Set.mem_univ, true_and]
      have hm := congrArg (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.inf_eq
      have hy := Set.ext_iff.mp hm y
      simpa only [Subfunctor.min_obj, Set.mem_inter_iff, Subfunctor.bot_obj,
        Set.bot_eq_empty, Set.mem_empty_iff_false] using hy
  have hProdPushout := SSet.Subcomplex.BicartSq.isPushout hProdBicart
  let isoP0 : P0.toSSet ≅ X ⊗ (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
        (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet.Subcomplex (Δ[1])) ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X)
        (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet)
  let isoP1 : P1.toSSet ≅ X ⊗ (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
        (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet.Subcomplex (Δ[1])) ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X)
        (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet)
  let isoPT : PT.toSSet ≅ X ⊗ (T : SSet) :=
    SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X) T ≪≫
      whiskerRightIso (SSet.Subcomplex.topIso X) (T : SSet)
  let compMap0 : P0.toSSet ⟶ E := isoP0.hom ≫ map0
  let compMap1 : P1.toSSet ⟶ E := isoP1.hom ≫ map1
  have hAgreeProd :
      SSet.Subcomplex.homOfLE
          (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P0 from bot_le) ≫ compMap0 =
        SSet.Subcomplex.homOfLE
          (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P1 from bot_le) ≫ compMap1 := by
    apply Subsingleton.elim
  let endpointMapPT : PT.toSSet ⟶ E := hProdPushout.desc compMap0 compMap1 hAgreeProd
  let endpointMap : X ⊗ (T : SSet) ⟶ E := isoPT.inv ≫ endpointMapPT
  have hHornConst :
      hornSub.ι ≫ φ0 = SSet.const (X := hornSub.toSSet) e ∧
        hornSub.ι ≫ φ1 = SSet.const (X := hornSub.toSSet) e := by
    constructor
    · simpa [hornSub, lastIdx, φ0] using chosenLift_horn (e := e) (b := b) p hb σ
    · simpa [hornSub, lastIdx, φ1] using chosenLift_horn (e := e) (b := b) p hb τ
  have hIso0 : isoP0.hom ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) =
      SSet.Subcomplex.homOfLE hProdBicart.le₂₄ ≫ isoPT.hom := by
    ext m z
    · rfl
    · rfl
  have hIso1 : isoP1.hom ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) =
      SSet.Subcomplex.homOfLE hProdBicart.le₃₄ ≫ isoPT.hom := by
    ext m z
    · rfl
    · rfl
  have hEndpoint0 : (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
      endpointMap = map0 := by
    apply (cancel_epi isoP0.hom).mp
    rw [← Category.assoc, hIso0]
    simp [endpointMap, endpointMapPT, compMap0]
  have hEndpoint1 : (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
      endpointMap = map1 := by
    apply (cancel_epi isoP1.hom).mp
    rw [← Category.assoc, hIso1]
    simp [endpointMap, endpointMapPT, compMap1]
  have hHornMap0 :
      (hornSub.ι ▷ (SSet.stdSimplex.face {0} : SSet)) ≫ map0 =
        SSet.const (X := (hornSub : SSet) ⊗
          (SSet.stdSimplex.face {0} : SSet)) e := by
    dsimp [map0]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
    rw [hHornConst.1]
    simp
  have hHornMap1 :
      (hornSub.ι ▷ (SSet.stdSimplex.face {1} : SSet)) ≫ map1 =
        SSet.const (X := (hornSub : SSet) ⊗
          (SSet.stdSimplex.face {1} : SSet)) e := by
    dsimp [map1]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
    rw [hHornConst.2]
    simp
  have hHornTPushout := (tensorLeft (hornSub : SSet)).map_isPushout hT_isPushout
  have hEndpointHorn : (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
      SSet.const (X := (hornSub : SSet) ⊗ (T : SSet)) e := by
    apply hHornTPushout.hom_ext
    · rw [SSet.comp_const]
      change (((hornSub : SSet) ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
        (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
      calc
        _ = (hornSub.ι ▷ (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet)) ≫
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ endpointMap) := by
                rw [MonoidalCategory.whisker_exchange, Category.assoc]
        _ = (hornSub.ι ▷ (SSet.stdSimplex.face ({0} : Finset (Fin 2)) : SSet)) ≫ map0 := by
              rw [hEndpoint0]
        _ = _ := hHornMap0
    · rw [SSet.comp_const]
      change (((hornSub : SSet) ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
        (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
      calc
        _ = (hornSub.ι ▷ (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet)) ≫
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ endpointMap) := by
                rw [MonoidalCategory.whisker_exchange, Category.assoc]
        _ = (hornSub.ι ▷ (SSet.stdSimplex.face ({1} : Finset (Fin 2)) : SSet)) ≫ map1 := by
              rw [hEndpoint1]
        _ = _ := hHornMap1
  have hCompatGlue : (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
      ((hornSub : SSet) ◁ T.ι) ≫ SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
    rw [hEndpointHorn]
    simp
  let hGlue : (hornSub.unionProd T).toSSet ⟶ E :=
    (SSet.Subcomplex.unionProd.isPushout hornSub T).desc endpointMap
      (SSet.const (X := (hornSub : SSet) ⊗ Y) e) hCompatGlue
  have hMap0Proj : map0 ≫ p =
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ (X ◁ T.ι) ≫ K := by
    apply (cancel_epi (X ◁ iso0.hom)).mp
    calc
      (X ◁ iso0.hom) ≫ map0 ≫ p =
          (SSet.stdSimplex.rightUnitor X).hom ≫ φ0 ≫ p := by simp [map0, iso0, X]
      _ = (SSet.stdSimplex.rightUnitor X).hom ≫ RelativeMorphism.map σ := by rw [hφ0_proj]
      _ = (SSet.stdSimplex.rightUnitor X).hom ≫ SSet.ι₀ ≫ K := by rw [hK₀]
      _ = (X ◁ SSet.stdSimplex.δ 1) ≫ K := by rw [SSet.stdSimplex.rightUnitor_hom_ι₀_assoc]
      _ = (X ◁ (iso0.hom ≫ (SSet.stdSimplex.face {0}).ι)) ≫ K := by
            rw [SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
      _ = (X ◁ iso0.hom) ≫ (X ◁ (SSet.stdSimplex.face {0}).ι) ≫ K := by
            rw [MonoidalCategory.whiskerLeft_comp_assoc]
      _ = (X ◁ iso0.hom) ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
            (X ◁ T.ι) ≫ K := by
            rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₂₄]
            rw [MonoidalCategory.whiskerLeft_comp_assoc]
  have hMap1Proj : map1 ≫ p =
      (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ (X ◁ T.ι) ≫ K := by
    apply (cancel_epi (X ◁ iso1.hom)).mp
    calc
      (X ◁ iso1.hom) ≫ map1 ≫ p =
          (SSet.stdSimplex.rightUnitor X).hom ≫ φ1 ≫ p := by simp [map1, iso1, X]
      _ = (SSet.stdSimplex.rightUnitor X).hom ≫ RelativeMorphism.map τ := by rw [hφ1_proj]
      _ = (SSet.stdSimplex.rightUnitor X).hom ≫ SSet.ι₁ ≫ K := by rw [hK₁]
      _ = (X ◁ SSet.stdSimplex.δ 0) ≫ K := by rw [SSet.stdSimplex.rightUnitor_hom_ι₁_assoc]
      _ = (X ◁ (iso1.hom ≫ (SSet.stdSimplex.face {1}).ι)) ≫ K := by
            rw [SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
      _ = (X ◁ iso1.hom) ≫ (X ◁ (SSet.stdSimplex.face {1}).ι) ≫ K := by
            rw [MonoidalCategory.whiskerLeft_comp_assoc]
      _ = (X ◁ iso1.hom) ≫ (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
            (X ◁ T.ι) ≫ K := by
            rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₃₄]
            rw [MonoidalCategory.whiskerLeft_comp_assoc]
  have hXTPushout := (tensorLeft X).map_isPushout hT_isPushout
  have hEndpointProj : endpointMap ≫ p = (X ◁ T.ι) ≫ K := by
    apply hXTPushout.hom_ext
    · change ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ endpointMap) ≫ p = _
      rw [hEndpoint0]
      exact hMap0Proj
    · change ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ endpointMap) ≫ p = _
      rw [hEndpoint1]
      exact hMap1Proj
  have hHornLe : hornSub ≤ SSet.boundary (n + 1) := by
    dsimp [hornSub]
    rw [SSet.horn_eq_iSup]
    exact iSup_le (fun j => SSet.face_singleton_compl_le_boundary j.1)
  have hHornBase : (hornSub.ι ▷ Y) ≫ K =
      SSet.const (X := (hornSub : SSet) ⊗ Y) b := by
    rw [← SSet.Subcomplex.homOfLE_ι hHornLe]
    rw [MonoidalCategory.comp_whiskerRight_assoc]
    rw [hKrel]
    simp
  have hHornProj : SSet.const (X := (hornSub : SSet) ⊗ Y) e ≫ p =
      (hornSub.ι ▷ Y) ≫ K := by
    rw [hHornBase]
    simp [SSet.const_comp, hb]
  have hGlueLeft : SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue = endpointMap := by
    dsimp [hGlue]; simp
  have hGlueRight : SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue =
      SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
    dsimp [hGlue]; simp
  have hGlueProj : hGlue ≫ p = (hornSub.unionProd T).ι ≫ K := by
    apply (SSet.Subcomplex.unionProd.isPushout hornSub T).hom_ext
    · rw [← Category.assoc, hGlueLeft, hEndpointProj]
      rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
    · rw [← Category.assoc, hGlueRight, hHornProj]
      rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
  let sq : CommSq hGlue (hornSub.unionProd T).ι p K := CommSq.mk hGlueProj
  have hAnodyne : SSet.anodyneExtensions (hornSub.unionProd T).ι := by
    simpa [hornSub, T, lastIdx] using
      SSet.prodStdSimplex.anodyneExtensions_unionProd_ι lastIdx 1
  have : HasLiftingProperty (hornSub.unionProd T).ι p :=
    hAnodyne p (by rwa [← HomotopicalAlgebra.fibration_iff])
  have hLift : ∃ (prism : X ⊗ Y ⟶ E), prism ≫ p = K ∧
      (hornSub.unionProd T).ι ≫ prism = hGlue :=
    ⟨sq.lift, sq.fac_right, sq.fac_left⟩
  have hPrismT : (X ◁ T.ι) ≫ hLift.choose = endpointMap := by
    calc
      (X ◁ T.ι) ≫ hLift.choose = SSet.Subcomplex.unionProd.ι₁ hornSub T ≫
          (hornSub.unionProd T).ι ≫ hLift.choose := by
        rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
      _ = SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue := by
        rw [hLift.choose_spec.2]
      _ = endpointMap := hGlueLeft
  have hPrismZero : SSet.ι₀ ≫ hLift.choose = φ0 := by
    rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_one_assoc]
    rw [← SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₂₄]
    rw [MonoidalCategory.whiskerLeft_comp_assoc, hPrismT, hEndpoint0]
    simp [map0, iso0]
  have hPrismOne : SSet.ι₁ ≫ hLift.choose = φ1 := by
    rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
    rw [← SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₃₄]
    rw [MonoidalCategory.whiskerLeft_comp_assoc, hPrismT, hEndpoint1]
    simp [map1, iso1]
  have hPrismHorn : (hornSub.ι ▷ Y) ≫ hLift.choose =
      SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
    calc
      (hornSub.ι ▷ Y) ≫ hLift.choose = SSet.Subcomplex.unionProd.ι₂ hornSub T ≫
          (hornSub.unionProd T).ι ≫ hLift.choose := by rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
      _ = SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue := by rw [hLift.choose_spec.2]
      _ = _ := hGlueRight
  have hFaceRelE : ((SSet.boundary n).ι ▷ Δ[1]) ≫
      (SSet.stdSimplex.δ lastIdx ▷ Δ[1]) ≫ hLift.choose =
      SSet.const (X := (SSet.boundary n : SSet) ⊗ Δ[1]) e := by
    simpa [hornSub, lastIdx, X, Y] using lastFace_prism_const n e hLift.choose
      (by simpa [hornSub, lastIdx, X, Y] using hPrismHorn)
  let facePrism : Δ[n] ⊗ Δ[1] ⟶ E :=
    (SSet.stdSimplex.δ lastIdx ▷ Δ[1]) ≫ hLift.choose
  have hδboundary : SSet.stdSimplex.δ lastIdx =
      (SSet.stdSimplex.faceSingletonComplIso lastIdx).hom ≫
        SSet.boundary.faceι lastIdx ≫ (SSet.boundary (n + 1)).ι := by
    rw [SSet.boundary.faceι_ι, SSet.stdSimplex.faceSingletonComplIso_hom_ι]
  have hface : facePrism ≫ p = SSet.const (X := Δ[n] ⊗ Δ[1]) b := by
    dsimp [facePrism]
    rw [Category.assoc, hLift.choose_spec.1]
    rw [hδboundary]
    rw [MonoidalCategory.comp_whiskerRight_assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc]
    rw [hKrel]
    simp
  have hrange : SSet.Subcomplex.range facePrism ≤ SSet.Subcomplex.fiber p b := by
    rw [SSet.Subcomplex.range_le_fiber_iff]; exact hface
  let fiberPrism : Δ[n] ⊗ Δ[1] ⟶ (SSet.Subcomplex.fiber p b : SSet) :=
    SSet.Subcomplex.lift facePrism hrange
  have hFiberι : fiberPrism ≫ (SSet.Subcomplex.fiber p b).ι = facePrism :=
    SSet.Subcomplex.lift_ι _ _
  let src := connectingPtSimplexRep (p := p) (e := e) hb σ
  let tgt := connectingPtSimplexRep (p := p) (e := e) hb τ
  have hSourceι : RelativeMorphism.map src ≫ (SSet.Subcomplex.fiber p b).ι =
      SSet.stdSimplex.δ lastIdx ≫ φ0 := by
    dsimp [src]; rw [connectingPtSimplexRep_ι, chosenLift_face_eq]
  have hTargetι : RelativeMorphism.map tgt ≫ (SSet.Subcomplex.fiber p b).ι =
      SSet.stdSimplex.δ lastIdx ≫ φ1 := by
    dsimp [tgt]; rw [connectingPtSimplexRep_ι, chosenLift_face_eq]
  let H : src.Homotopy tgt :=
    { h := fiberPrism
      h₀ := by
        apply (cancel_mono (SSet.Subcomplex.fiber p b).ι).mp
        rw [Category.assoc, hFiberι, SSet.ι₀_comp_assoc, hPrismZero, hSourceι]
      h₁ := by
        apply (cancel_mono (SSet.Subcomplex.fiber p b).ι).mp
        rw [Category.assoc, hFiberι, SSet.ι₁_comp_assoc, hPrismOne, hTargetι]
      rel := by
        apply (cancel_mono (SSet.Subcomplex.fiber p b).ι).mp
        rw [Category.assoc, hFiberι, hFaceRelE]
        ext m z
        rfl }
  exact ⟨SSet.PtSimplex.Homotopy.relStruct₀ H⟩

lemma connectingPtSimplexRep_homotopy_rel {n : ℕ}
    (p : E ⟶ B) (e : E _⦋0⦌) {b : B _⦋0⦌}
    (hb : p.app _ e = b) [Fibration p]
    {σ τ : B.PtSimplex (n + 1) b}
    (H : Nonempty (σ.Homotopy τ)) :
    Nonempty
      ((connectingPtSimplexRep (p := p) (e := e) hb σ).RelStruct₀
        (connectingPtSimplexRep (p := p) (e := e) hb τ)) := by
  obtain ⟨H⟩ := H
  apply connectingPtSimplexRep_prism_rel p e hb σ τ H.h H.h₀ H.h₁
  rw [H.rel]
  simp [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]

noncomputable def connectingMap {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p] :
    SSet.KanComplex.π (n + 1) B b → SSet.KanComplex.π n
      (Subcomplex.fiber p b : SSet.{u})
      (Subcomplex.fiber.basePoint (f := p) e hb) :=
  Quot.lift
    (fun σ => SSet.KanComplex.π.mk
      (connectingPtSimplexRep (p := p) (e := e) hb σ))
    (by
      intro σ τ H
      rw [SSet.KanComplex.π.mk_eq_mk_iff]
      exact connectingPtSimplexRep_homotopy_rel p e hb H)

lemma connectingMap_mk {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p]
    (σ : B.PtSimplex (n + 1) b) :
    connectingMap (n := n) (p := p) (e := e) hb
        (SSet.KanComplex.π.mk σ) =
      SSet.KanComplex.π.mk (connectingPtSimplexRep (p := p) (e := e) hb σ) := by
  rw [connectingMap]
  rfl

private def mapRelStruct {X Y : SSet.{u}} {n : ℕ}
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (f : X ⟶ Y) (hf : f.app _ x = y)
    {a b : X.PtSimplex n x} {i : Fin (n + 1)} (r : a.RelStruct b i) :
    (SSet.PtSimplex.map f hf a).RelStruct (SSet.PtSimplex.map f hf b) i where
  map := r.map ≫ f
  δ_castSucc_map := by
    rw [← Category.assoc, r.δ_castSucc_map]
    rfl
  δ_succ_map := by
    rw [← Category.assoc, r.δ_succ_map]
    rfl
  δ_map_of_lt j hj := by
    rw [← Category.assoc, r.δ_map_of_lt j hj, SSet.const_comp, hf]
  δ_map_of_gt j hj := by
    rw [← Category.assoc, r.δ_map_of_gt j hj, SSet.const_comp, hf]

private lemma exists_totalPtSimplex_of_connecting_rel_const {n : ℕ}
    (p : E ⟶ B) (e : E _⦋0⦌) {b : B _⦋0⦌}
    (hb : p.app _ e = b) [Fibration p] [KanComplex B]
    (σ : B.PtSimplex (n + 1) b)
    (hrel : Nonempty
      ((connectingPtSimplexRep (p := p) (e := e) hb σ).RelStruct₀ .const)) :
    ∃ r : E.PtSimplex (n + 1) e,
      Nonempty ((SSet.PtSimplex.map p hb r).RelStruct₀ σ) := by
  let d := chosenLiftData (e := e) (b := b) p hb σ
  obtain ⟨h⟩ := hrel
  have hf : (Subcomplex.fiber p b).ι.app _ (Subcomplex.fiber.basePoint (f := p) e hb) = e := by
    change (Subcomplex.fiber.basePoint (f := p) e hb).val = e
    exact Subcomplex.fiber.basePoint_val
  have hE0 : (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf
      (connectingPtSimplexRep (p := p) (e := e) hb σ)).RelStruct
      (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf .const) 0 :=
    mapRelStruct (Subcomplex.fiber p b).ι hf h
  have hEq1 : SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf
      (connectingPtSimplexRep (p := p) (e := e) hb σ) = d.pt := by
    apply RelativeMorphism.ext
    change RelativeMorphism.map
        (connectingPtSimplexRep (p := p) (e := e) hb σ) ≫
      (Subcomplex.fiber p b).ι = RelativeMorphism.map d.pt
    simpa [d, chosenLiftPt] using connectingPtSimplexRep_ι p e hb σ
  have hEq2 : SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf
      (RelativeMorphism.const : (Subcomplex.fiber p b : SSet).PtSimplex n _) =
      (RelativeMorphism.const : E.PtSimplex n e) := by
    apply RelativeMorphism.ext
    change SSet.const (X := Δ[n]) (Subcomplex.fiber.basePoint (f := p) e hb) ≫
        (Subcomplex.fiber p b).ι = SSet.const (X := Δ[n]) e
    rw [SSet.const_comp, hf]
  have : KanComplex E := isFibrant_of_fibration p
  have hFLast : (connectingPtSimplexRep (p := p) (e := e) hb σ).RelStruct
      (RelativeMorphism.const : (Subcomplex.fiber p b : SSet).PtSimplex n _)
      (Fin.last n) :=
    h.relStruct (Fin.last n)
  let hEpre : (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf
      (connectingPtSimplexRep (p := p) (e := e) hb σ)).RelStruct
      (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hf .const) (Fin.last n) :=
    mapRelStruct (Subcomplex.fiber p b).ι hf hFLast
  let hElast : d.pt.RelStruct
      (RelativeMorphism.const : E.PtSimplex n e) (Fin.last n) :=
    hEpre.copy hEq1 hEq2
  have hElastProj : hElast.map ≫ p = SSet.const (X := Δ[n + 1]) b := by
    -- `copy` preserves the underlying map, and `mapRelStruct` is
    -- `r.map ≫ f`, so `hElast.map = hFLast.map ≫ fiber.ι` by `rfl`.
    have h1 : hEpre.map = hFLast.map ≫ (SSet.Subcomplex.fiber p b).ι :=
      rfl
    have h2 : hElast.map = hEpre.map := rfl
    calc hElast.map ≫ p
        = (hFLast.map ≫ (SSet.Subcomplex.fiber p b).ι) ≫ p := by
          rw [h2, h1]
      _ = hFLast.map ≫ ((SSet.Subcomplex.fiber p b).ι ≫ p) := by
          rw [Category.assoc]
      _ = hFLast.map ≫ SSet.const
            (X := (SSet.Subcomplex.fiber p b : SSet)) b := by
          rw [SSet.Subcomplex.fiber_ι_comp]
      _ = SSet.const (X := Δ[n + 1]) b := by
          simp [SSet.comp_const]
  let i : Fin (n + 1) := Fin.last n
  let missing : Fin (n + 3) := i.castSucc.succ
  let phi : Δ[n + 1] ⟶ E := SSet.yonedaEquiv.symm d.lift
  have hPhiProj : phi ≫ p = RelativeMorphism.map σ := d.lift_projects
  have hPhiFace : RelativeMorphism.map d.pt = stdSimplex.δ (Fin.last (n + 1)) ≫ phi := d.face_eq
  have hPhiHornWhole : (Λ[n + 1, Fin.last (n + 1)]).ι ≫ phi =
      SSet.const (X := (Λ[n + 1, Fin.last (n + 1)]).toSSet) e := by
    have hhorn := chosenLift_horn (p := p) (hb := hb) (σ := σ)
    have hphi_eq : phi = SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ) := by
      simp [phi, chosenLift, d]
    rw [hphi_eq]
    exact hhorn
  have hPhiHorn : ∀ (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)),
      stdSimplex.δ j ≫ phi = SSet.const (X := Δ[n]) e := by
    intro j hj
    calc stdSimplex.δ j ≫ phi
        = SSet.horn.ι (Fin.last (n + 1)) j hj ≫
            ((Λ[n + 1, Fin.last (n + 1)]).ι ≫ phi) := by
          rw [← Category.assoc, SSet.horn.ι_ι]
      _ = SSet.horn.ι (Fin.last (n + 1)) j hj ≫
          SSet.const (X := (Λ[n + 1, Fin.last (n + 1)]).toSSet) e := by
          rw [hPhiHornWhole]
      _ = SSet.const (X := Δ[n]) e := by
          rw [SSet.comp_const]
  let α (j : Fin (n + 3)) (_ : j ≠ missing) : Δ[n + 1] ⟶ E :=
    if j = i.castSucc.castSucc then phi else
      if j = i.succ.succ then hElast.map else SSet.const (X := Δ[n + 1]) e
  have hAne : i.castSucc.castSucc ≠ missing := Fin.castSucc_lt_succ.ne
  have hCne : i.succ.succ ≠ missing := by
    intro heq
    have hv := congrArg Fin.val heq
    simp [missing] at hv
  have hAlpha : horn.IsCompatible α := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    by_cases hja : j = i.castSucc.castSucc
    · subst j
      have hkc : k = i.succ.succ := by
        dsimp [i, missing] at hj hk hjk ⊢
        grind
      subst k
      have hp : (i.succ.succ).pred (Fin.ne_zero_of_lt hjk) = i.succ := by
        apply Fin.ext
        rfl
      have hc : i.castSucc.castSucc.castPred (Fin.ne_last_of_lt hjk) = i.castSucc := by
        apply Fin.ext
        rfl
      have hne : i.succ.succ ≠ i.castSucc.castSucc := by
        dsimp [i]
        grind
      rw [hp, hc, show α i.castSucc.castSucc hj = phi by simp [α],
        show α i.succ.succ hk = hElast.map by simp [α, hne]]
      change stdSimplex.δ (Fin.last (n + 1)) ≫ phi =
        stdSimplex.δ (Fin.last n).castSucc ≫ hElast.map
      rw [← hPhiFace]
      exact hElast.δ_castSucc_map.symm
    · have hjc : j ≠ i.succ.succ := by
        dsimp [i] at hjk ⊢
        grind
      rw [show α j hj = SSet.const (X := Δ[n + 1]) e by simp [α, hja, hjc]]
      rw [SSet.comp_const]
      by_cases hka : k = i.castSucc.castSucc
      · subst k
        rw [show α i.castSucc.castSucc hk = phi by simp [α]]
        exact (hPhiHorn _ (by
          intro heq
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simpa [i, missing] using hv)).symm
      · by_cases hkc : k = i.succ.succ
        · subst k
          have hne : i.succ.succ ≠ i.castSucc.castSucc := by
            dsimp [i]
            grind
          rw [show α i.succ.succ hk = hElast.map by simp [α, hne]]
          exact (hElast.δ_map_of_lt _ (by
            change j.val < i.val
            dsimp [i, missing] at hj hja hjc hjk ⊢
            grind)).symm
        · rw [show α k hk = SSet.const (X := Δ[n + 1]) e by simp [α, hka, hkc]]
          simp
  let filler : Δ[n + 2] ⟶ E := hAlpha.liftOfKanComplex
  let r : E.PtSimplex (n + 1) e :=
    RelativeMorphism.mk (SSet.stdSimplex.δ missing ≫ filler) (by
      apply SSet.boundary.hom_ext (n := n)
      intro j
      have hι : SSet.boundary.ι (j : Fin (n + 2)) ≫
          (SSet.boundary (n + 1)).ι =
          SSet.stdSimplex.δ (j : Fin (n + 2)) :=
        SSet.boundary.ι_ι j
      have hι_comp : SSet.boundary.ι (j : Fin (n + 2)) ≫
          (SSet.boundary (n + 1)).ι ≫
          SSet.stdSimplex.δ missing ≫ filler =
          (SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
            SSet.stdSimplex.δ missing) ≫ filler := by
        calc
          SSet.boundary.ι (j : Fin (n + 2)) ≫
              (SSet.boundary (n + 1)).ι ≫
              SSet.stdSimplex.δ missing ≫ filler
              = (SSet.boundary.ι (j : Fin (n + 2)) ≫
                (SSet.boundary (n + 1)).ι) ≫
                SSet.stdSimplex.δ missing ≫ filler := by
            rw [← Category.assoc]
          _ = SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
              SSet.stdSimplex.δ missing ≫ filler := by rw [hι]
          _ = (SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
              SSet.stdSimplex.δ missing) ≫ filler := by
            rw [Category.assoc]
      rw [hι_comp]
      simp only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
      by_cases hj : (j : Fin (n + 2)) ≤ i.castSucc
      · have hδ : SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
            SSet.stdSimplex.δ missing =
            SSet.stdSimplex.δ (i.castSucc : Fin (n + 2)) ≫
              SSet.stdSimplex.δ (j.castSucc : Fin (n + 3)) := by
          have hMissing : missing = i.castSucc.succ := rfl
          calc SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
                SSet.stdSimplex.δ missing
              = SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
                SSet.stdSimplex.δ i.castSucc.succ := by
                rw [hMissing]
            _ = SSet.stdSimplex.δ (i.castSucc : Fin (n + 2)) ≫
                SSet.stdSimplex.δ (j.castSucc : Fin (n + 3)) := by
              exact SSet.stdSimplex.δ_comp_δ (n := n) hj
        have hAssoc : (SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
            SSet.stdSimplex.δ missing) ≫ filler =
            SSet.stdSimplex.δ (i.castSucc : Fin (n + 2)) ≫
              (SSet.stdSimplex.δ (j.castSucc : Fin (n + 3)) ≫
                filler) := by
          calc
            (SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
              SSet.stdSimplex.δ missing) ≫ filler
              = SSet.stdSimplex.δ (j : Fin (n + 2)) ≫
                (SSet.stdSimplex.δ missing ≫ filler) := by
              rw [Category.assoc]
            _ = SSet.stdSimplex.δ (i.castSucc : Fin (n + 2)) ≫
                (SSet.stdSimplex.δ (j.castSucc : Fin (n + 3)) ≫
                  filler) := by
              rw [← Category.assoc, hδ, Category.assoc]
        rw [hAssoc,
          hAlpha.δ_liftOfKanComplex (j.castSucc : Fin (n + 3))
            (by dsimp [missing, i] at hj ⊢; grind)]
        by_cases hji : (j : Fin (n + 2)) = i.castSucc
        · subst j
          rw [show α i.castSucc.castSucc hAne = phi by simp [α]]
          exact hPhiHorn _ (by dsimp [i]; grind)
        · have hjA : (j.castSucc : Fin (n + 3)) ≠
              i.castSucc.castSucc := by
            intro hcast
            apply hji
            apply Fin.ext
            simpa using congrArg Fin.val hcast
          have hjC : (j.castSucc : Fin (n + 3)) ≠ i.succ.succ := by
            dsimp [i] at hj ⊢; grind
          have hjm : (j.castSucc : Fin (n + 3)) ≠ missing := by
            dsimp [missing, i] at hj ⊢; grind
          rw [show α j.castSucc hjm =
              SSet.const (X := Δ[n + 1]) e by simp [α, hjA, hjC]]
          simp
      · have hj_gt : i.castSucc < (j : Fin (n + 2)) := by
          dsimp [i] at hj ⊢; grind
        have hji : (j : Fin (n + 2)) = i.succ := by
          dsimp [i] at hj hj_gt ⊢; grind
        subst j
        have hSelf : SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
            SSet.stdSimplex.δ missing =
            SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
              SSet.stdSimplex.δ
                (i.succ.succ : Fin (n + 3)) := by
          have hEq : missing =
              (i.succ : Fin (n + 2)).castSucc := rfl
          calc SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
                SSet.stdSimplex.δ missing
              = SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
                SSet.stdSimplex.δ
                  ((i.succ : Fin (n + 2)).castSucc : Fin (n + 3)) := by
                rw [hEq]
            _ = SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
                SSet.stdSimplex.δ (i.succ.succ : Fin (n + 3)) := by
              exact SSet.stdSimplex.δ_comp_δ_self
                (i := (i.succ : Fin (n + 2)))
        have hAssoc2 : (SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
            SSet.stdSimplex.δ missing) ≫ filler =
            SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
              (SSet.stdSimplex.δ (i.succ.succ : Fin (n + 3)) ≫
                filler) := by
          calc
            (SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
              SSet.stdSimplex.δ missing) ≫ filler
              = (SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
                SSet.stdSimplex.δ (i.succ.succ : Fin (n + 3))) ≫
                filler := by
              rw [hSelf]
            _ = SSet.stdSimplex.δ (i.succ : Fin (n + 2)) ≫
                (SSet.stdSimplex.δ (i.succ.succ : Fin (n + 3)) ≫
                  filler) := by
              rw [Category.assoc]
        rw [hAssoc2,
          hAlpha.δ_liftOfKanComplex (i.succ.succ : Fin (n + 3))
            (by dsimp [missing, i]; grind)]
        have hne : i.succ.succ ≠ i.castSucc.castSucc := by
          dsimp [i]; grind
        rw [show α i.succ.succ hCne = hElast.map by simp [α, hne],
          hElast.δ_succ_map]
        simp only [RelativeMorphism.const_map])
  let relBefore : σ.RelStruct (SSet.PtSimplex.map p hb r) i.castSucc :=
    { map := filler ≫ p
      δ_castSucc_map := by
        dsimp [filler]
        rw [← Category.assoc,
          hAlpha.δ_liftOfKanComplex i.castSucc.castSucc hAne]
        rw [show α i.castSucc.castSucc hAne = phi by simp [α], hPhiProj]
      δ_succ_map := by
        change stdSimplex.δ missing ≫ (filler ≫ p) =
          (stdSimplex.δ missing ≫ filler) ≫ p
        rw [Category.assoc]
      δ_map_of_lt := by
        intro j hj
        have hjm : j ≠ missing := by
          dsimp [missing, i] at hj ⊢
          grind
        dsimp [filler]
        rw [← Category.assoc, hAlpha.δ_liftOfKanComplex j hjm]
        have hja : j ≠ i.castSucc.castSucc := by grind
        have hjc : j ≠ i.succ.succ := by grind
        rw [show α j hjm = SSet.const (X := Δ[n + 1]) e by simp [α, hja, hjc]]
        simp [SSet.const_comp, hb]
      δ_map_of_gt := by
        intro j hj
        have hjc : j = i.succ.succ := by
          dsimp [i] at hj ⊢
          grind
        subst j
        dsimp [filler]
        rw [← Category.assoc, hAlpha.δ_liftOfKanComplex i.succ.succ hCne]
        have hne : i.succ.succ ≠ i.castSucc.castSucc := by
          dsimp [i]
          grind
        rw [show α i.succ.succ hCne = hElast.map by simp [α, hne], hElastProj] }
  exact ⟨r, ⟨relBefore.symm.relStruct₀⟩⟩

lemma connecting_exactness_at_B {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p] [KanComplex B] :
    ∀ (q : SSet.KanComplex.π (n + 1) B b),
      connectingMap (n := n) (p := p) (e := e) hb q = 1 →
        ∃ _r : SSet.KanComplex.π (n + 1) E e,
          SSet.KanComplex.π.map (f := p) hb (n := n + 1) _r = q := by
  have : KanComplex E := isFibrant_of_fibration p
  intro q
  induction q using SSet.KanComplex.π.rec with
  | mk σ =>
      intro hq
      rw [connectingMap_mk, SSet.KanComplex.π.mk_eq_one_iff] at hq
      obtain ⟨r, hr⟩ := exists_totalPtSimplex_of_connecting_rel_const p e hb σ hq
      refine ⟨SSet.KanComplex.π.mk r, ?_⟩
      rw [SSet.KanComplex.π.map_mk, SSet.KanComplex.π.mk_eq_mk_iff]
      exact hr

lemma connecting_exactness_at_fiber {n : ℕ} (p : E ⟶ B) (e : E _⦋0⦌)
    {b : B _⦋0⦌} (hb : p.app _ e = b) [Fibration p] [KanComplex B] :
    ∀ (q : SSet.KanComplex.π n
        (Subcomplex.fiber p b : SSet.{u})
        (Subcomplex.fiber.basePoint (f := p) e hb)),
      SSet.KanComplex.π.map (Subcomplex.fiber p b).ι rfl n q = 1 →
        ∃ _r : SSet.KanComplex.π (n + 1) B b,
          connectingMap (n := n) (p := p) (e := e) hb _r = q := by
  intro q hq
  have : IsFibrant E := isFibrant_of_fibration p
  induction q using SSet.KanComplex.π.rec with
  | mk τ =>
    have hFiberPoint : (Subcomplex.fiber p b).ι.app _
        (Subcomplex.fiber.basePoint (f := p) e hb) = e := by
      change (Subcomplex.fiber.basePoint (f := p) e hb).val = e
      rfl
    have hq' : SSet.KanComplex.π.mk
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ) = 1 := by
      have hEq : SSet.PtSimplex.map (Subcomplex.fiber p b).ι
          (rfl : (Subcomplex.fiber p b).ι.app _
            (Subcomplex.fiber.basePoint (f := p) e hb) = e) τ =
          SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ :=
        rfl
      have h1 : SSet.KanComplex.π.mk
          (SSet.PtSimplex.map (Subcomplex.fiber p b).ι
            (rfl : (Subcomplex.fiber p b).ι.app _
              (Subcomplex.fiber.basePoint (f := p) e hb) = e) τ) = 1 := by
        simpa [SSet.KanComplex.π.map_mk] using hq
      rw [hEq] at h1
      exact h1
    have hRel₀ : Nonempty
        ((SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ).RelStruct₀
          .const) := by
      rwa [SSet.KanComplex.π.mk_eq_one_iff] at hq'
    let c : E.PtSimplex n e :=
      { map := SSet.const (X := Δ[n]) e
        comm := by
          have h0 : (SSet.boundary n).ι ≫ SSet.const (X := Δ[n]) e =
              SSet.const (X := SSet.boundary n) e := by
            simp
          have h1 : SSet.const (X := SSet.boundary n)
                (⟨e, Subcomplex.mem_ofSimplex_obj (X := E) e⟩ :
                  (Subcomplex.ofSimplex (X := E) e : SSet) _⦋0⦌) ≫
                (Subcomplex.ofSimplex (X := E) e).ι =
              SSet.const (X := SSet.boundary n) e := by
            -- `SSet.const ⟨e, _⟩ ≫ ι = SSet.const e` by `SSet.const_comp`
            have : SSet.const
                (X := SSet.boundary n)
                (⟨e, Subcomplex.mem_ofSimplex_obj (X := E) e⟩ :
                  (Subcomplex.ofSimplex (X := E) e : SSet) _⦋0⦌) ≫
                (Subcomplex.ofSimplex (X := E) e).ι =
              SSet.const (X := SSet.boundary n) e := by
              ext m x
              rfl
            exact this
          rw [h0, ← h1] }
    have hSymm : Nonempty (c.RelStruct₀
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ)) :=
      ⟨hRel₀.some.symm⟩
    let hE : SSet.PtSimplex.RelStruct (X := E) c
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ)
        (Fin.last n) :=
      hSymm.some.relStruct (Fin.last n)
    let bMap : Δ[n + 1] ⟶ B := hE.map ≫ p
    have hMapComp : SSet.RelativeMorphism.map
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ) ≫ p =
        SSet.const (X := Δ[n]) b := by
      calc SSet.RelativeMorphism.map
            (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ) ≫ p
          = SSet.RelativeMorphism.map τ ≫
              (Subcomplex.fiber p b).ι ≫ p := rfl
        _ = SSet.RelativeMorphism.map τ ≫
              SSet.const (X := (Subcomplex.fiber p b : SSet)) b := by
            rw [Subcomplex.fiber_ι_comp]
        _ = SSet.const (X := Δ[n]) b := by
            simp [SSet.comp_const]
    have hBdry : (SSet.boundary (n + 1)).ι ≫ bMap =
        SSet.const (X := SSet.boundary (n + 1)) b := by
      cases n with
      | zero =>
        apply SSet.boundary.hom_ext
        intro j
        fin_cases j
        · have hj : stdSimplex.δ (0 : Fin 2) ≫ bMap =
              SSet.const (X := Δ[0]) b := by
            calc stdSimplex.δ (0 : Fin 2) ≫ bMap
                = (stdSimplex.δ (0 : Fin 2) ≫ hE.map) ≫ p := by
                  simp [bMap, Category.assoc]
              _ = SSet.const (X := Δ[0]) b := by
                  have h1 : stdSimplex.δ (0 : Fin 2) ≫ hE.map =
                      SSet.RelativeMorphism.map c :=
                    hE.δ_castSucc_map
                  rw [h1]
                  -- `map c = SSet.const e` by definition of `c`
                  have h2 : SSet.RelativeMorphism.map c =
                      SSet.const (X := Δ[0]) e := rfl
                  rw [h2, SSet.const_comp, hb]
          calc SSet.boundary.ι (0 : Fin 2) ≫ (SSet.boundary 1).ι ≫ bMap
              = stdSimplex.δ (0 : Fin 2) ≫ bMap := by
                rw [← Category.assoc, SSet.boundary.ι_ι]
            _ = SSet.const (X := Δ[0]) b := hj
            _ = SSet.boundary.ι (0 : Fin 2) ≫
                  SSet.const (X := SSet.boundary 1) b := by
                simp [SSet.comp_const]
        · have hj : stdSimplex.δ (1 : Fin 2) ≫ bMap =
              SSet.const (X := Δ[0]) b := by
            calc stdSimplex.δ (1 : Fin 2) ≫ bMap
                = (stdSimplex.δ (1 : Fin 2) ≫ hE.map) ≫ p := by
                  simp [bMap, Category.assoc]
              _ = SSet.const (X := Δ[0]) b := by
                  have h1 : stdSimplex.δ (1 : Fin 2) ≫ hE.map =
                      SSet.RelativeMorphism.map
                        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι
                          hFiberPoint τ) :=
                    hE.δ_succ_map
                  rw [h1, hMapComp]
          calc SSet.boundary.ι (1 : Fin 2) ≫ (SSet.boundary 1).ι ≫ bMap
              = stdSimplex.δ (1 : Fin 2) ≫ bMap := by
                rw [← Category.assoc, SSet.boundary.ι_ι]
            _ = SSet.const (X := Δ[0]) b := hj
            _ = SSet.boundary.ι (1 : Fin 2) ≫
                  SSet.const (X := SSet.boundary 1) b := by
                simp [SSet.comp_const]
      | succ m =>
        apply SSet.boundary.hom_ext
        intro j
        have hj : stdSimplex.δ j ≫ bMap = SSet.const (X := Δ[m + 1]) b := by
          calc stdSimplex.δ j ≫ bMap
              = (stdSimplex.δ j ≫ hE.map) ≫ p := by
                simp [bMap, Category.assoc]
            _ = SSet.const (X := Δ[m + 1]) b := by
                by_cases hjLast : j = Fin.last (m + 2)
                · rw [hjLast]
                  have h1 : stdSimplex.δ (Fin.last (m + 2)) ≫ hE.map =
                      SSet.RelativeMorphism.map
                        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι
                          hFiberPoint τ) := by
                    have hEq : (Fin.last (m + 2) : Fin (m + 3)) =
                        (Fin.last (m + 1) : Fin (m + 2)).succ := by
                      ext; simp
                    rw [hEq, hE.δ_succ_map]
                  rw [h1, hMapComp]
                · by_cases hjCast : j = Fin.castSucc (Fin.last (m + 1))
                  · rw [hjCast, hE.δ_castSucc_map]
                    have h2 : SSet.RelativeMorphism.map c =
                        SSet.const (X := Δ[m + 1]) e := rfl
                    rw [h2, SSet.const_comp, hb]
                  · have hjLt : j < Fin.castSucc (Fin.last (m + 1)) := by
                      have hjValNeLast : (j : Fin (m + 3)).val ≠ m + 2 := by
                        intro h
                        have : j = Fin.last (m + 2) := Fin.ext h
                        contradiction
                      have hjValNeCast : (j : Fin (m + 3)).val ≠ m + 1 := by
                        intro h
                        have : j = Fin.castSucc (Fin.last (m + 1)) :=
                          Fin.ext (by simpa using h)
                        contradiction
                      have hjValLt : (j : Fin (m + 3)).val < m + 1 := by
                        omega
                      exact Fin.lt_def.mpr hjValLt
                    rw [hE.δ_map_of_lt j hjLt]
                    rw [SSet.const_comp, hb]
        calc SSet.boundary.ι j ≫ (SSet.boundary (m + 2)).ι ≫ bMap
            = stdSimplex.δ j ≫ bMap := by
              rw [← Category.assoc, SSet.boundary.ι_ι]
          _ = SSet.const (X := Δ[m + 1]) b := hj
          _ = SSet.boundary.ι j ≫
                SSet.const (X := SSet.boundary (m + 2)) b := by
              simp [SSet.comp_const]
    let σ : B.PtSimplex (n + 1) b :=
      { map := bMap
        comm := by
          have h0 : (SSet.boundary (n + 1)).ι ≫ bMap =
              SSet.const (X := SSet.boundary (n + 1)) b := hBdry
          have h1 :
              SSet.const
                  (X := SSet.boundary (n + 1))
                  (⟨b, Subcomplex.mem_ofSimplex_obj (X := B) b⟩ :
                    (Subcomplex.ofSimplex (X := B) b : SSet) _⦋0⦌) ≫
                (Subcomplex.ofSimplex (X := B) b).ι =
              SSet.const (X := SSet.boundary (n + 1)) b := by
            simp [Subcomplex.ofSimplex_ι, SSet.comp_const]
          rw [← h1] at h0
          exact h0 }
    have hσ_map : RelativeMorphism.map σ = bMap := rfl
    let myLift : E _⦋n + 1⦌ := SSet.yonedaEquiv hE.map
    have hMyLiftSymm : SSet.yonedaEquiv.symm myLift = hE.map := by
      change SSet.yonedaEquiv.symm (SSet.yonedaEquiv hE.map) = hE.map
      simp
    let myData : ChosenLiftData (e := e) (b := b) p hb σ :=
      { lift := myLift
        pt := SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ
        lift_projects := by
          rw [hMyLiftSymm, hσ_map]
        face_eq := by
          rw [hMyLiftSymm]
          exact hE.δ_succ_map.symm }
    -- The fiber point of myData is τ (by canceling mono)
    have hMyToFiber : Subcomplex.lift
          (SSet.RelativeMorphism.map
            (SSet.PtSimplex.map (Subcomplex.fiber p b).ι hFiberPoint τ))
          (by rw [Subcomplex.range_le_fiber_iff]; exact hMapComp) =
        SSet.RelativeMorphism.map τ :=
      rfl
    -- The canonical rep is homotopic to τ via prism between the two lifts
    have hFiberHomotopy : Nonempty
        ((connectingPtSimplexRep (p := p) (e := e) hb σ).RelStruct₀ τ) := by
      let lastIdx : Fin (n + 2) := Fin.last _
      let hornSub := Λ[n + 1, lastIdx]
      let T := ∂Δ[1]
      let X : SSet := Δ[n + 1]
      let Y : SSet := Δ[1]
      let φ0 : X ⟶ E :=
        SSet.yonedaEquiv.symm (chosenLift (e := e) (b := b) p hb σ)
      let φ1 : X ⟶ E := hE.map
      have hφ0_proj : φ0 ≫ p = RelativeMorphism.map σ :=
        chosenLift_projects (p := p) (hb := hb) σ
      have hφ1_proj : φ1 ≫ p = RelativeMorphism.map σ := by
        calc φ1 ≫ p = hE.map ≫ p := rfl
          _ = bMap := rfl
          _ = RelativeMorphism.map σ := hσ_map.symm
      have hHorn0 : hornSub.ι ≫ φ0 =
          SSet.const (X := hornSub.toSSet) e := by
        simpa [φ0] using chosenLift_horn (e := e) (b := b) p hb σ
      have hHorn1 : hornSub.ι ≫ φ1 =
          SSet.const (X := hornSub.toSSet) e := by
        apply horn.hom_ext'
        intro j hj
        have hδ : stdSimplex.δ j ≫ φ1 =
            SSet.const (X := Δ[n]) e := by
          cases n with
          | zero =>
            fin_cases j
            · simpa [φ1] using hE.δ_castSucc_map
            · exact absurd rfl hj
          | succ m =>
            by_cases h_eq : j = Fin.castSucc (Fin.last (m + 1))
            · rw [h_eq, hE.δ_castSucc_map]
            · have hlt : j < Fin.castSucc (Fin.last (m + 1)) := by
                have hj_ne_last : j ≠ Fin.last (m + 2) := hj
                have h_ne_cast : j ≠ Fin.castSucc (Fin.last (m + 1)) :=
                  h_eq
                have h_val_ne_cast : (j : Fin (m + 3)).val ≠ m + 1 := by
                  intro h
                  apply h_ne_cast
                  exact Fin.ext h
                have h_val_ne_last : (j : Fin (m + 3)).val ≠ m + 2 := by
                  intro h
                  apply hj_ne_last
                  exact Fin.ext h
                have h_le : (j : Fin (m + 3)).val ≤ m + 2 := by
                  have := j.isLt
                  omega
                have h_lt_val : (j : Fin (m + 3)).val < m + 1 := by
                  omega
                exact Fin.lt_def.mpr h_lt_val
              rw [hE.δ_map_of_lt _ hlt]
        calc horn.ι lastIdx j hj ≫ (hornSub.ι ≫ φ1)
              = stdSimplex.δ j ≫ φ1 := by
              rw [← Category.assoc, horn.ι_ι]
          _ = SSet.const (X := Δ[n]) e := hδ
          _ = horn.ι lastIdx j hj ≫
              SSet.const (X := hornSub.toSSet) e := by simp
      let K : X ⊗ Y ⟶ B := fst X Y ≫ RelativeMorphism.map σ
      have hK₀ : SSet.ι₀ ≫ K = RelativeMorphism.map σ := by
        calc SSet.ι₀ ≫ K
            = (SSet.ι₀ ≫ fst X Y) ≫ RelativeMorphism.map σ := by
              simp [K]
          _ = 𝟙 X ≫ RelativeMorphism.map σ := by rw [SSet.ι₀_fst]
          _ = RelativeMorphism.map σ := by simp
      have hK₁ : SSet.ι₁ ≫ K = RelativeMorphism.map σ := by
        calc SSet.ι₁ ≫ K
            = (SSet.ι₁ ≫ fst X Y) ≫ RelativeMorphism.map σ := by
              simp [K]
          _ = 𝟙 X ≫ RelativeMorphism.map σ := by rw [SSet.ι₁_fst]
          _ = RelativeMorphism.map σ := by simp
      have hKrel : ((SSet.boundary (n + 1)).ι ▷ Y) ≫ K =
          SSet.const (X := (SSet.boundary (n + 1) : SSet) ⊗ Y) (Y := B) b := by
        have hB : (SSet.boundary (n + 1)).ι ≫ RelativeMorphism.map σ =
            SSet.const (X := (SSet.boundary (n + 1) : SSet)) (Y := B) b := by
          simpa [hσ_map] using hBdry
        have hFstNat : ((SSet.boundary (n + 1)).ι ▷ Y) ≫ fst X Y =
            fst (SSet.boundary (n + 1) : SSet) Y ≫
              (SSet.boundary (n + 1)).ι := by
          ext Δ x
          rcases x with ⟨x, y⟩
          rfl
        calc ((SSet.boundary (n + 1)).ι ▷ Y) ≫ K
            = ((SSet.boundary (n + 1)).ι ▷ Y) ≫ fst X Y ≫
                RelativeMorphism.map σ := rfl
          _ = fst (SSet.boundary (n+1) : SSet) Y ≫
                (SSet.boundary (n+1)).ι ≫ RelativeMorphism.map σ := by
              rw [← Category.assoc, hFstNat, Category.assoc]
          _ = fst _ _ ≫ SSet.const (X := (SSet.boundary (n+1) : SSet))
                  (Y := B) b := by rw [hB]
          _ = SSet.const (X := (SSet.boundary (n+1) : SSet) ⊗ Y)
                  (Y := B) b := by
              ext Δ x
              rcases x with ⟨x, y⟩
              simp
      let iso0 : Δ[0] ≅ (SSet.stdSimplex.face {0} : SSet) :=
        SSet.stdSimplex.faceSingletonIso (0 : Fin 2)
      let iso1 : Δ[0] ≅ (SSet.stdSimplex.face {1} : SSet) :=
        SSet.stdSimplex.faceSingletonIso (1 : Fin 2)
      let map0 : X ⊗ (SSet.stdSimplex.face {0} : SSet) ⟶ E :=
        (X ◁ iso0.inv) ≫ (SSet.stdSimplex.rightUnitor X).hom ≫ φ0
      let map1 : X ⊗ (SSet.stdSimplex.face {1} : SSet) ⟶ E :=
        (X ◁ iso1.inv) ≫ (SSet.stdSimplex.rightUnitor X).hom ≫ φ1
      have hT_bicart : SSet.Subcomplex.BicartSq
          (⊥ : SSet.Subcomplex (Δ[1]))
          (SSet.stdSimplex.face {0}) (SSet.stdSimplex.face {1}) T := by
        constructor
        · have h0 : (({0} : Finset (Fin 2)) = ({1}ᶜ : Finset (Fin 2))) := by
            decide
          have h1 : (({1} : Finset (Fin 2)) = ({0}ᶜ : Finset (Fin 2))) := by
            decide
          calc SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊔
                SSet.stdSimplex.face ({1} : Finset (Fin 2))
              = SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) ⊔
                  SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) := by
                rw [← h0, ← h1]
            _ = SSet.stdSimplex.face (({0}ᶜ : Finset (Fin 2))) ⊔
                  SSet.stdSimplex.face (({1}ᶜ : Finset (Fin 2))) := by
                rw [sup_comm]
            _ = ⨆ (i : Fin 2),
                  SSet.stdSimplex.face (({i}ᶜ : Finset (Fin 2))) := by
                apply le_antisymm
                · apply sup_le
                  · exact le_iSup
                      (f := fun i : Fin 2 =>
                        SSet.stdSimplex.face
                          (({i}ᶜ : Finset (Fin 2)))) 0
                  · exact le_iSup
                      (f := fun i : Fin 2 =>
                        SSet.stdSimplex.face
                          (({i}ᶜ : Finset (Fin 2)))) 1
                · apply iSup_le
                  intro i
                  fin_cases i
                  · exact le_sup_left
                  · exact le_sup_right
            _ = SSet.boundary 1 :=
                (SSet.boundary_eq_iSup (n := 1)).symm
            _ = T := rfl
        · have h_eq : SSet.stdSimplex.face ({0} : Finset (Fin 2)) ⊓
              SSet.stdSimplex.face ({1} : Finset (Fin 2)) =
              SSet.stdSimplex.face
                (({0} : Finset (Fin 2)) ⊓ {1}) := by
            rw [SSet.stdSimplex.face_inter_face]
          rw [h_eq]
          have h_empty : (({0} : Finset (Fin 2)) ⊓ {1} :
              Finset (Fin 2)) = ∅ := by decide
          rw [h_empty]
          exact SSet.stdSimplex.face_empty 1
      have hT_isPushout :=
        SSet.Subcomplex.BicartSq.isPushout hT_bicart
      let P0 : SSet.Subcomplex (X ⊗ Y) :=
        (⊤ : SSet.Subcomplex X).prod
          (SSet.stdSimplex.face {0} : SSet.Subcomplex (Δ[1]))
      let P1 : SSet.Subcomplex (X ⊗ Y) :=
        (⊤ : SSet.Subcomplex X).prod
          (SSet.stdSimplex.face {1} : SSet.Subcomplex (Δ[1]))
      let PT : SSet.Subcomplex (X ⊗ Y) := (⊤ : SSet.Subcomplex X).prod T
      have hProdBicart : SSet.Subcomplex.BicartSq
          (⊥ : SSet.Subcomplex (X ⊗ Y)) P0 P1 PT := by
        constructor
        · ext m ⟨x, y⟩
          change
              (((x ∈ (Set.univ : Set (X.obj m)) ∧
                y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∨
              (x ∈ (Set.univ : Set (X.obj m)) ∧
                y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔
            (x ∈ (Set.univ : Set (X.obj m)) ∧ y ∈ T.obj m))
          simp only [Set.mem_univ, true_and]
          have hm := congrArg
              (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.sup_eq
          simpa only [Subfunctor.max_obj, Set.mem_union] using
            Set.ext_iff.mp hm y
        · ext m ⟨x, y⟩
          change
              (((x ∈ (Set.univ : Set (X.obj m)) ∧
                y ∈ (SSet.stdSimplex.face ({0} : Finset (Fin 2))).obj m) ∧
              (x ∈ (Set.univ : Set (X.obj m)) ∧
                y ∈ (SSet.stdSimplex.face ({1} : Finset (Fin 2))).obj m)) ↔
            False)
          simp only [Set.mem_univ, true_and]
          have hm := congrArg
              (fun U : SSet.Subcomplex Y => U.obj m) hT_bicart.inf_eq
          have hy := Set.ext_iff.mp hm y
          simpa only [Subfunctor.min_obj, Set.mem_inter_iff,
            Subfunctor.bot_obj, Set.bot_eq_empty, Set.mem_empty_iff_false] using hy
      have hProdPushout := SSet.Subcomplex.BicartSq.isPushout hProdBicart
      let isoP0 : P0.toSSet ≅ X ⊗ (SSet.stdSimplex.face {0} : SSet) :=
        SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
            (SSet.stdSimplex.face {0} : SSet.Subcomplex (Δ[1])) ≪≫
          whiskerRightIso (SSet.Subcomplex.topIso X)
            (SSet.stdSimplex.face {0} : SSet)
      let isoP1 : P1.toSSet ≅ X ⊗ (SSet.stdSimplex.face {1} : SSet) :=
        SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X)
            (SSet.stdSimplex.face {1} : SSet.Subcomplex (Δ[1])) ≪≫
          whiskerRightIso (SSet.Subcomplex.topIso X)
            (SSet.stdSimplex.face {1} : SSet)
      let isoPT : PT.toSSet ≅ X ⊗ (T : SSet) :=
        SSet.Subcomplex.prodIso (⊤ : SSet.Subcomplex X) T ≪≫
          whiskerRightIso (SSet.Subcomplex.topIso X) (T : SSet)
      let compMap0 : P0.toSSet ⟶ E := isoP0.hom ≫ map0
      let compMap1 : P1.toSSet ⟶ E := isoP1.hom ≫ map1
      have hAgreeProd :
          SSet.Subcomplex.homOfLE
              (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P0 from bot_le) ≫
                compMap0 =
            SSet.Subcomplex.homOfLE
                (show (⊥ : SSet.Subcomplex (X ⊗ Y)) ≤ P1 from bot_le) ≫
                  compMap1 := by
        apply Subsingleton.elim
      let endpointMapPT : PT.toSSet ⟶ E :=
        hProdPushout.desc compMap0 compMap1 hAgreeProd
      let endpointMap : X ⊗ (T : SSet) ⟶ E := isoPT.inv ≫ endpointMapPT
      have hIso0 : isoP0.hom ≫
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) =
          SSet.Subcomplex.homOfLE hProdBicart.le₂₄ ≫ isoPT.hom := by
        ext m z
        · rfl
        · rfl
      have hIso1 : isoP1.hom ≫
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) =
          SSet.Subcomplex.homOfLE hProdBicart.le₃₄ ≫ isoPT.hom := by
        ext m z
        · rfl
        · rfl
      have hEndpoint0 :
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫ endpointMap =
            map0 := by
        apply (cancel_epi isoP0.hom).mp
        rw [← Category.assoc, hIso0]
        simp [endpointMap, endpointMapPT, compMap0]
      have hEndpoint1 :
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫ endpointMap =
            map1 := by
        apply (cancel_epi isoP1.hom).mp
        rw [← Category.assoc, hIso1]
        simp [endpointMap, endpointMapPT, compMap1]
      have hHornMap0 :
          (hornSub.ι ▷ (SSet.stdSimplex.face {0} : SSet)) ≫ map0 =
            SSet.const (X := (hornSub : SSet) ⊗
              (SSet.stdSimplex.face {0} : SSet)) e := by
        dsimp [map0]
        rw [← MonoidalCategory.whisker_exchange_assoc]
        rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
        rw [hHorn0]
        simp
      have hHornMap1 :
          (hornSub.ι ▷ (SSet.stdSimplex.face {1} : SSet)) ≫ map1 =
            SSet.const (X := (hornSub : SSet) ⊗
              (SSet.stdSimplex.face {1} : SSet)) e := by
        dsimp [map1]
        rw [← MonoidalCategory.whisker_exchange_assoc]
        rw [SSet.stdSimplex.rightUnitor_hom_naturality_assoc]
        rw [hHorn1]
        simp
      have hHornTPushout :=
        (tensorLeft (hornSub : SSet)).map_isPushout hT_isPushout
      have hEndpointHorn : (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
          SSet.const (X := (hornSub : SSet) ⊗ (T : SSet)) e := by
        apply hHornTPushout.hom_ext
        · rw [SSet.comp_const]
          change
              (((hornSub : SSet) ◁
                  SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
              (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
          calc _ = (hornSub.ι ▷
                  (SSet.stdSimplex.face {0} : SSet)) ≫
                  ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
                    endpointMap) := by
                    rw [MonoidalCategory.whisker_exchange, Category.assoc]
            _ = (hornSub.ι ▷
                  (SSet.stdSimplex.face {0} : SSet)) ≫
                  map0 := by rw [hEndpoint0]
            _ = _ := hHornMap0
        · rw [SSet.comp_const]
          change
              (((hornSub : SSet) ◁
                  SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
              (hornSub.ι ▷ (T : SSet))) ≫ endpointMap = _
          calc _ = (hornSub.ι ▷
                  (SSet.stdSimplex.face {1} : SSet)) ≫
                  ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
                    endpointMap) := by
                    rw [MonoidalCategory.whisker_exchange, Category.assoc]
            _ = (hornSub.ι ▷
                  (SSet.stdSimplex.face {1} : SSet)) ≫
                  map1 := by rw [hEndpoint1]
            _ = _ := hHornMap1
      have hCompatGlue : (hornSub.ι ▷ (T : SSet)) ≫ endpointMap =
          ((hornSub : SSet) ◁ T.ι) ≫
            SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
        rw [hEndpointHorn]
        simp
      let hGlue : (hornSub.unionProd T).toSSet ⟶ E :=
        (SSet.Subcomplex.unionProd.isPushout hornSub T).desc endpointMap
          (SSet.const (X := (hornSub : SSet) ⊗ Y) e) hCompatGlue
      have hMap0Proj : map0 ≫ p =
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
            (X ◁ T.ι) ≫ K := by
        apply (cancel_epi (X ◁ iso0.hom)).mp
        calc (X ◁ iso0.hom) ≫ map0 ≫ p =
              (SSet.stdSimplex.rightUnitor X).hom ≫ φ0 ≫ p := by
              simp [map0, iso0, X]
          _ = (SSet.stdSimplex.rightUnitor X).hom ≫
                RelativeMorphism.map σ := by rw [hφ0_proj]
          _ = (SSet.stdSimplex.rightUnitor X).hom ≫ SSet.ι₀ ≫ K := by
              rw [hK₀]
          _ = (X ◁ SSet.stdSimplex.δ 1) ≫ K := by
              rw [SSet.stdSimplex.rightUnitor_hom_ι₀_assoc]
          _ = (X ◁ (iso0.hom ≫ (SSet.stdSimplex.face {0}).ι)) ≫ K := by
              rw [SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
          _ = (X ◁ iso0.hom) ≫ (X ◁ (SSet.stdSimplex.face {0}).ι) ≫ K := by
              rw [MonoidalCategory.whiskerLeft_comp_assoc]
          _ = (X ◁ iso0.hom) ≫
                (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
                  (X ◁ T.ι) ≫ K := by
              rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₂₄]
              rw [MonoidalCategory.whiskerLeft_comp_assoc]
      have hMap1Proj : map1 ≫ p =
          (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
            (X ◁ T.ι) ≫ K := by
        apply (cancel_epi (X ◁ iso1.hom)).mp
        calc (X ◁ iso1.hom) ≫ map1 ≫ p =
              (SSet.stdSimplex.rightUnitor X).hom ≫ φ1 ≫ p := by
              simp [map1, iso1, X]
          _ = (SSet.stdSimplex.rightUnitor X).hom ≫
                RelativeMorphism.map σ := by rw [hφ1_proj]
          _ = (SSet.stdSimplex.rightUnitor X).hom ≫ SSet.ι₁ ≫ K := by
              rw [hK₁]
          _ = (X ◁ SSet.stdSimplex.δ 0) ≫ K := by
              rw [SSet.stdSimplex.rightUnitor_hom_ι₁_assoc]
          _ = (X ◁ (iso1.hom ≫ (SSet.stdSimplex.face {1}).ι)) ≫ K := by
              rw [SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
          _ = (X ◁ iso1.hom) ≫ (X ◁ (SSet.stdSimplex.face {1}).ι) ≫ K := by
              rw [MonoidalCategory.whiskerLeft_comp_assoc]
          _ = (X ◁ iso1.hom) ≫
                (X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
                  (X ◁ T.ι) ≫ K := by
              rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₃₄]
              rw [MonoidalCategory.whiskerLeft_comp_assoc]
      have hXTPushout := (tensorLeft X).map_isPushout hT_isPushout
      have hEndpointProj : endpointMap ≫ p = (X ◁ T.ι) ≫ K := by
        apply hXTPushout.hom_ext
        · change
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₂₄) ≫
              endpointMap) ≫ p = _
          rw [hEndpoint0]
          exact hMap0Proj
        · change
              ((X ◁ SSet.Subcomplex.homOfLE hT_bicart.le₃₄) ≫
              endpointMap) ≫ p = _
          rw [hEndpoint1]
          exact hMap1Proj
      have hHornBase : (hornSub.ι ▷ Y) ≫ K =
          SSet.const (X := (hornSub : SSet) ⊗ Y) b := by
        dsimp [K]
        rw [CartesianMonoidalCategory.whiskerRight_fst_assoc]
        have hHornMap : hornSub.ι ≫ RelativeMorphism.map σ =
            SSet.const (X := hornSub.toSSet) b := by
          calc hornSub.ι ≫ RelativeMorphism.map σ =
                (hornSub.ι ≫ φ0) ≫ p := by
                rw [Category.assoc, hφ0_proj]
            _ = SSet.const (X := hornSub.toSSet) e ≫ p := by
                rw [hHorn0]
            _ = SSet.const (X := hornSub.toSSet) b := by
                simp [SSet.const_comp, hb]
        rw [hHornMap]
        simp
      have hHornProj : SSet.const (X := (hornSub : SSet) ⊗ Y) e ≫ p =
          (hornSub.ι ▷ Y) ≫ K := by
        rw [hHornBase]
        simp [SSet.const_comp, hb]
      have hGlueLeft : SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue =
          endpointMap := by dsimp [hGlue]; simp
      have hGlueRight : SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue =
          SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
        dsimp [hGlue]; simp
      have hGlueProj : hGlue ≫ p = (hornSub.unionProd T).ι ≫ K := by
        apply (SSet.Subcomplex.unionProd.isPushout hornSub T).hom_ext
        · rw [← Category.assoc, hGlueLeft, hEndpointProj]
          rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
        · rw [← Category.assoc, hGlueRight, hHornProj]
          rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
      let sq : CommSq hGlue (hornSub.unionProd T).ι p K :=
        CommSq.mk hGlueProj
      have hAnodyne :
          SSet.anodyneExtensions (hornSub.unionProd T).ι := by
        simpa [hornSub, T, lastIdx] using
          SSet.prodStdSimplex.anodyneExtensions_unionProd_ι lastIdx 1
      have : HasLiftingProperty (hornSub.unionProd T).ι p :=
        hAnodyne p (by rwa [← HomotopicalAlgebra.fibration_iff])
      have hLift : ∃ (prism : X ⊗ Y ⟶ E), prism ≫ p = K ∧
          (hornSub.unionProd T).ι ≫ prism = hGlue :=
        ⟨sq.lift, sq.fac_right, sq.fac_left⟩
      have hPrismT : (X ◁ T.ι) ≫ hLift.choose = endpointMap := by
        calc (X ◁ T.ι) ≫ hLift.choose =
              SSet.Subcomplex.unionProd.ι₁ hornSub T ≫
                (hornSub.unionProd T).ι ≫ hLift.choose := by
              rw [SSet.Subcomplex.unionProd.ι₁_ι_assoc]
          _ = SSet.Subcomplex.unionProd.ι₁ hornSub T ≫ hGlue := by
              rw [hLift.choose_spec.2]
          _ = endpointMap := hGlueLeft
      have hPrismZero : SSet.ι₀ ≫ hLift.choose = φ0 := by
        rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_one_assoc]
        rw [← SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]
        rw [MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₂₄]
        rw [MonoidalCategory.whiskerLeft_comp_assoc]
        rw [hPrismT, hEndpoint0]
        simp [map0, iso0]
      have hPrismOne : SSet.ι₁ ≫ hLift.choose = φ1 := by
        rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_zero_assoc]
        rw [← SSet.stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
        rw [MonoidalCategory.whiskerLeft_comp_assoc]
        rw [← SSet.Subcomplex.homOfLE_ι hT_bicart.le₃₄]
        rw [MonoidalCategory.whiskerLeft_comp_assoc]
        rw [hPrismT, hEndpoint1]
        simp [map1, iso1]
      have hPrismHorn : (hornSub.ι ▷ Y) ≫ hLift.choose =
          SSet.const (X := (hornSub : SSet) ⊗ Y) e := by
        calc (hornSub.ι ▷ Y) ≫ hLift.choose =
              SSet.Subcomplex.unionProd.ι₂ hornSub T ≫
                (hornSub.unionProd T).ι ≫ hLift.choose := by
              rw [SSet.Subcomplex.unionProd.ι₂_ι_assoc]
          _ = SSet.Subcomplex.unionProd.ι₂ hornSub T ≫ hGlue := by
              rw [hLift.choose_spec.2]
          _ = _ := hGlueRight
      have hFaceRelE : ((SSet.boundary n).ι ▷ Y) ≫
            (SSet.stdSimplex.δ lastIdx ▷ Y) ≫ hLift.choose =
          SSet.const (X := (SSet.boundary n : SSet) ⊗ Y) e := by
        simpa [hornSub, lastIdx, X, Y] using
          lastFace_prism_const n e hLift.choose
            (by simpa [hornSub, lastIdx, X, Y] using hPrismHorn)
      let facePrism : Δ[n] ⊗ Y ⟶ E :=
        (SSet.stdSimplex.δ lastIdx ▷ Y) ≫ hLift.choose
      have hδboundary : SSet.stdSimplex.δ lastIdx =
          (SSet.stdSimplex.faceSingletonComplIso lastIdx).hom ≫
            SSet.boundary.faceι lastIdx ≫
              (SSet.boundary (n + 1)).ι := by
        rw [SSet.boundary.faceι_ι,
          SSet.stdSimplex.faceSingletonComplIso_hom_ι]
      have hface : facePrism ≫ p =
          SSet.const (X := Δ[n] ⊗ Y) b := by
        dsimp [facePrism]
        rw [Category.assoc, hLift.choose_spec.1]
        rw [hδboundary]
        rw [MonoidalCategory.comp_whiskerRight_assoc]
        rw [MonoidalCategory.comp_whiskerRight_assoc]
        rw [hKrel]
        simp
      have hrange : SSet.Subcomplex.range facePrism ≤
          SSet.Subcomplex.fiber p b := by
        rw [SSet.Subcomplex.range_le_fiber_iff]
        exact hface
      let fiberPrism : Δ[n] ⊗ Y ⟶ (SSet.Subcomplex.fiber p b : SSet) :=
        SSet.Subcomplex.lift facePrism hrange
      have hFiberι : fiberPrism ≫ (SSet.Subcomplex.fiber p b).ι =
          facePrism := SSet.Subcomplex.lift_ι _ _
      let src := connectingPtSimplexRep (p := p) (e := e) hb σ
      have hSourceι : RelativeMorphism.map src ≫
          (Subcomplex.fiber p b).ι =
          SSet.stdSimplex.δ lastIdx ≫ φ0 := by
        dsimp [src]
        rw [connectingPtSimplexRep_ι, chosenLift_face_eq]
      have hTargetι : RelativeMorphism.map τ ≫
          (Subcomplex.fiber p b).ι =
          SSet.stdSimplex.δ lastIdx ≫ φ1 := by
        calc RelativeMorphism.map τ ≫ (Subcomplex.fiber p b).ι
            = RelativeMorphism.map
                (SSet.PtSimplex.map (Subcomplex.fiber p b).ι
                  hFiberPoint τ) := rfl
          _ = RelativeMorphism.map myData.pt := rfl
          _ = SSet.stdSimplex.δ lastIdx ≫ φ1 := by
              rw [myData.face_eq, hMyLiftSymm]
      let H : src.Homotopy τ :=
        { h := fiberPrism
          h₀ := by
            apply (cancel_mono (Subcomplex.fiber p b).ι).mp
            rw [Category.assoc, hFiberι]
            rw [SSet.ι₀_comp_assoc, hPrismZero, hSourceι]
          h₁ := by
            apply (cancel_mono (Subcomplex.fiber p b).ι).mp
            rw [Category.assoc, hFiberι]
            rw [SSet.ι₁_comp_assoc, hPrismOne, hTargetι]
          rel := by
            apply (cancel_mono (Subcomplex.fiber p b).ι).mp
            rw [Category.assoc, hFiberι]
            rw [hFaceRelE]
            ext m z
            rfl }
      exact ⟨SSet.PtSimplex.Homotopy.relStruct₀ H⟩
    exact ⟨SSet.KanComplex.π.mk σ, by
      rw [connectingMap_mk]
      rw [SSet.KanComplex.π.mk_eq_mk_iff]
      exact hFiberHomotopy⟩

end QuotientDescent

end ConnectingMap

end SSet
