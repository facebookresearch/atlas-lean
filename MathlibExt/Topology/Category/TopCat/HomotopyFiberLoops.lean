/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberConullTotal
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Selected based loops and the actual compact-open homotopy fiber

The homotopy fiber of the constant map from a point is the original compact-open based
loop space. A specified total point induces the map carrying that point and the entire
original loop into the homotopy fiber of a given map. Total terminal weakness makes this
map weak. The construction keeps the constant loop at the independently defined selected
point and constant path, without assuming a path-lifting or based-contraction theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy

universe u

namespace TopCat

/-- The original loop is viewed on the canonical interval of the compact-open path object. -/
def loopPathObjectMap (B : TopCat.{u}) (b : B) :
    TopCat.of (LoopSpace B b) ⟶ pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z => z.1 ((TopCat.I.homeomorph.{u}) z.2)
      continuous_toFun := by
        have h : Continuous (fun z : LoopSpace B b × unitInterval => z.1 z.2) :=
          Path.continuous_uncurry_iff.mpr continuous_id
        exact h.comp (continuous_fst.prodMk
          ((TopCat.I.homeomorph.{u}).continuous.comp continuous_snd)) }

/-- Both endpoints retain the specified base point of the original loop. -/
theorem loopPathObjectMap_evalZero (B : TopCat.{u}) (b : B) :
    loopPathObjectMap B b ≫ pathEvalZero B = TopCat.const b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  change gamma ((TopCat.I.homeomorph.{u}) (0 : TopCat.I.{u})) = b
  rw [TopCat.I.homeomorph_zero.{u}]
  exact gamma.source

/-- The endpoint at one is the same actual loop base point. -/
theorem loopPathObjectMap_evalOne (B : TopCat.{u}) (b : B) :
    loopPathObjectMap B b ≫ pathEvalOne B = TopCat.const b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  change gamma ((TopCat.I.homeomorph.{u}) (1 : TopCat.I.{u})) = b
  rw [TopCat.I.homeomorph_one.{u}]
  exact gamma.target

/-- Put the actual loop, with its full path, into the homotopy fiber of the constant point map. -/
def loopConstantHomotopyFiber (B : TopCat.{u}) (b : B) :
    TopCat.of (LoopSpace B b) ⟶
      homotopyFiber (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) b := by
  let L : TopCat.{u} := TopCat.of (LoopSpace B b)
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let q : P ⟶ B := TopCat.const b
  let c : L ⟶ P := TopCat.const PUnit.unit
  have hc : c ≫ q = (TopCat.const b : L ⟶ B) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro gamma
    rfl
  refine pullback.lift (Limits.prod.lift c c) (loopPathObjectMap B b) ?_
  apply Limits.prod.hom_ext
  · calc
      (Limits.prod.lift c c ≫ Limits.prod.map q q) ≫ Limits.prod.fst =
          Limits.prod.lift c c ≫ (Limits.prod.map q q ≫ Limits.prod.fst) :=
        Category.assoc _ _ _
      _ = Limits.prod.lift c c ≫ (Limits.prod.fst ≫ q) :=
        congrArg (fun k => Limits.prod.lift c c ≫ k) (Limits.prod.map_fst q q)
      _ = (Limits.prod.lift c c ≫ Limits.prod.fst) ≫ q := (Category.assoc _ _ _).symm
      _ = c ≫ q := congrArg (fun k => k ≫ q) (Limits.prod.lift_fst c c)
      _ = TopCat.const b := hc
      _ = loopPathObjectMap B b ≫ pathEvalZero B := (loopPathObjectMap_evalZero B b).symm
      _ = (loopPathObjectMap B b ≫ pathEndpoints B) ≫ Limits.prod.fst := by
        rw [Category.assoc, pathEndpoints, Limits.prod.lift_fst]
  · calc
      (Limits.prod.lift c c ≫ Limits.prod.map q q) ≫ Limits.prod.snd =
          Limits.prod.lift c c ≫ (Limits.prod.map q q ≫ Limits.prod.snd) :=
        Category.assoc _ _ _
      _ = Limits.prod.lift c c ≫ (Limits.prod.snd ≫ q) :=
        congrArg (fun k => Limits.prod.lift c c ≫ k) (Limits.prod.map_snd q q)
      _ = (Limits.prod.lift c c ≫ Limits.prod.snd) ≫ q := (Category.assoc _ _ _).symm
      _ = c ≫ q := congrArg (fun k => k ≫ q) (Limits.prod.lift_snd c c)
      _ = TopCat.const b := hc
      _ = loopPathObjectMap B b ≫ pathEvalOne B := (loopPathObjectMap_evalOne B b).symm
      _ = (loopPathObjectMap B b ≫ pathEndpoints B) ≫ Limits.prod.snd := by
        rw [Category.assoc, pathEndpoints, Limits.prod.lift_snd]

/-- The constant-source homotopy fiber carries exactly the given entire loop. -/
theorem loopConstantHomotopyFiber_path (B : TopCat.{u}) (b : B) :
    loopConstantHomotopyFiber B b ≫
        homotopyFiberPath (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) b =
      loopPathObjectMap B b := by
  unfold loopConstantHomotopyFiber
  exact pullback.lift_snd _ _ _

/-- Its total point is the unique original point source. -/
theorem loopConstantHomotopyFiber_toTotal (B : TopCat.{u}) (b : B) :
    loopConstantHomotopyFiber B b ≫
        homotopyFiberToTotal (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) b =
      (TopCat.const PUnit.unit : TopCat.of (LoopSpace B b) ⟶ TopCat.of PUnit.{u + 1}) :=
  TopCat.isTerminalPUnit.hom_ext _ _

/-- The actual compact-open constant-source homotopy fiber is the original based loop space. -/
def loopHomotopyFiberConstIso (B : TopCat.{u}) (b : B) :
    TopCat.of (LoopSpace B b) ≅
      homotopyFiber (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) b := by
  let q : TopCat.of PUnit.{u + 1} ⟶ B := TopCat.const b
  let fromFiber : homotopyFiber q b ⟶ TopCat.of (LoopSpace B b) :=
    TopCat.ofHom
      { toFun := fun z =>
          { toContinuousMap :=
              (homotopyFiberPath q b z).comp
                ⟨(TopCat.I.homeomorph.{u}).symm, (TopCat.I.homeomorph.{u}).symm.continuous⟩
            source' := by
              have h := ConcreteCategory.congr_hom (homotopyPullbackPath_evalZero q q) z
              have hzero : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) =
                  (0 : TopCat.I.{u}) := by
                apply (TopCat.I.homeomorph.{u}).injective
                simp
              change homotopyFiberPath q b z ((TopCat.I.homeomorph.{u}).symm 0) = b
              rw [hzero]
              exact h
            target' := by
              have h := ConcreteCategory.congr_hom (homotopyPullbackPath_evalOne q q) z
              have hone : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) =
                  (1 : TopCat.I.{u}) := by
                apply (TopCat.I.homeomorph.{u}).injective
                simp
              change homotopyFiberPath q b z ((TopCat.I.homeomorph.{u}).symm 1) = b
              rw [hone]
              exact h }
        continuous_toFun := by
          apply Path.continuous_uncurry_iff.mp
          exact continuous_eval.comp
            (((homotopyFiberPath q b).hom.continuous.comp continuous_fst).prodMk
              ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_snd)) }
  refine
    { hom := loopConstantHomotopyFiber B b
      inv := fromFiber
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro gamma
    apply Path.ext
    funext t
    have h := ConcreteCategory.congr_hom (loopConstantHomotopyFiber_path B b) gamma
    have heval := congrArg
      (fun k : pathObject B => k ((TopCat.I.homeomorph.{u}).symm t)) h
    change homotopyFiberPath q b (loopConstantHomotopyFiber B b gamma)
      ((TopCat.I.homeomorph.{u}).symm t) = gamma t
    exact heval.trans (by
      change gamma ((TopCat.I.homeomorph.{u}) ((TopCat.I.homeomorph.{u}).symm t)) = gamma t
      exact congrArg (fun s : unitInterval => gamma s)
        ((TopCat.I.homeomorph.{u}).apply_symm_apply t))
  · apply homotopyPullback_hom_ext
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · exact TopCat.isTerminalPUnit.hom_ext _ _
    · rw [Category.assoc, loopConstantHomotopyFiber_path, Category.id_comp]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      apply ContinuousMap.ext
      intro t
      change homotopyFiberPath q b z
          ((TopCat.I.homeomorph.{u}).symm ((TopCat.I.homeomorph.{u}) t)) =
        homotopyFiberPath q b z t
      rw [(TopCat.I.homeomorph.{u}).symm_apply_apply]

/-- The selected total point and the original whole loop give a canonical homotopy-fiber map. -/
def loopToHomotopyFiber {E B : TopCat.{u}} (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    TopCat.of (LoopSpace B b) ⟶ homotopyFiber p b := by
  let q : TopCat.of PUnit.{u + 1} ⟶ B := TopCat.const b
  let i : TopCat.of PUnit.{u + 1} ⟶ E := TopCat.const e0
  have square : q ≫ 𝟙 B = i ≫ p := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact fun _ => he.symm
  exact (loopHomotopyFiberConstIso B b).hom ≫
    homotopyFiberMapOfSquare (p := q) (q := p) i (𝟙 B) square b

/-- The map retains the specified total point at every loop. -/
theorem loopToHomotopyFiber_toTotal {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    loopToHomotopyFiber p e0 b he ≫ homotopyFiberToTotal p b = TopCat.const e0 := by
  apply TopCat.ext
  intro gamma
  let q : TopCat.of PUnit.{u + 1} ⟶ B := TopCat.const b
  let i : TopCat.of PUnit.{u + 1} ⟶ E := TopCat.const e0
  have square : q ≫ 𝟙 B = i ≫ p := by
    apply TopCat.ext
    exact fun _ => he.symm
  have h := ConcreteCategory.congr_hom
    (homotopyFiberMapOfSquare_toTotal (p := q) (q := p) i (𝟙 B) square b)
    ((loopHomotopyFiberConstIso B b).hom gamma)
  change homotopyFiberToTotal p b (loopToHomotopyFiber p e0 b he gamma) = e0
  change homotopyFiberToTotal p b
      (homotopyFiberMapOfSquare (p := q) (q := p) i (𝟙 B) square b
        ((loopHomotopyFiberConstIso B b).hom gamma)) = e0 at h
  exact h

/-- Every full compact-open loop is carried unchanged into the homotopy fiber. -/
theorem loopToHomotopyFiber_path {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    loopToHomotopyFiber p e0 b he ≫ homotopyFiberPath p b = loopPathObjectMap B b := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro gamma
  let q : TopCat.of PUnit.{u + 1} ⟶ B := TopCat.const b
  let i : TopCat.of PUnit.{u + 1} ⟶ E := TopCat.const e0
  have square : q ≫ 𝟙 B = i ≫ p := by
    apply TopCat.ext
    exact fun _ => he.symm
  have h := ConcreteCategory.congr_hom
    (homotopyFiberMapOfSquare_path (p := q) (q := p) i (𝟙 B) square b)
    ((loopHomotopyFiberConstIso B b).hom gamma)
  change homotopyFiberPath p b
      (homotopyFiberMapOfSquare (p := q) (q := p) i (𝟙 B) square b
        ((loopHomotopyFiberConstIso B b).hom gamma)) =
    pathObjectMap (𝟙 B)
      (homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma)) at h
  change homotopyFiberPath p b (loopToHomotopyFiber p e0 b he gamma) =
    loopPathObjectMap B b gamma
  calc
    _ = pathObjectMap (𝟙 B)
        (homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma)) := h
    _ = homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma) := by
      have hid := ConcreteCategory.congr_hom (pathObjectMap_id B)
        (homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma))
      change pathObjectMap (𝟙 B)
          (homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma)) =
        homotopyFiberPath q b ((loopHomotopyFiberConstIso B b).hom gamma) at hid
      exact hid
    _ = loopPathObjectMap B b gamma :=
      ConcreteCategory.congr_hom (loopConstantHomotopyFiber_path B b) gamma

/-- Terminal weakness of the actual total space makes the selected loop map weak. -/
theorem loopToHomotopyFiber_mem_of_total_conull {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b)
    (hE : weakHomotopyEquivalences (terminal.from E)) :
    weakHomotopyEquivalences (loopToHomotopyFiber p e0 b he) := by
  have hFiber := homotopyFiberPointMap_mem_of_total_conull p e0 b he hE
  exact weakHomotopyEquivalences.comp_mem (loopHomotopyFiberConstIso B b).hom _
    (weakHomotopyEquivalences.of_isIso _) hFiber

/-- The selected homotopy-fiber point has the given total point and independently constant path. -/
def homotopyFiberSelectedPointMap {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    TopCat.of PUnit.{u + 1} ⟶ homotopyFiber p b :=
  pullback.lift
    (TopCat.const e0 : TopCat.of PUnit.{u + 1} ⟶ E)
    (𝟙 (TopCat.of PUnit.{u + 1}))
    (by
      apply TopCat.ext
      exact fun _ => he) ≫ strictFiberToHomotopyFiber p b

/-- The independently constructed selected point retains its specified total coordinate. -/
theorem homotopyFiberSelectedPointMap_toTotal {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    homotopyFiberSelectedPointMap p e0 b he ≫ homotopyFiberToTotal p b =
      TopCat.const e0 := by
  unfold homotopyFiberSelectedPointMap
  rw [Category.assoc, strictFiberToHomotopyFiber_toTotal]
  exact pullback.lift_fst _ _ _

/-- Its whole path coordinate is the independently specified constant path at b. -/
theorem homotopyFiberSelectedPointMap_path {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    homotopyFiberSelectedPointMap p e0 b he ≫ homotopyFiberPath p b =
      TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{u + 1})
        (ContinuousMap.const TopCat.I.{u} b)) := by
  unfold homotopyFiberSelectedPointMap
  rw [Category.assoc, strictFiberToHomotopyFiber_path]
  simp only [← Category.assoc, pullback.lift_snd, Category.id_comp]
  rfl

/-- The actual constant based loop is sent to that independently constructed selected point. -/
theorem loopToHomotopyFiber_constant_point {E B : TopCat.{u}}
    (p : E ⟶ B) (e0 : E) (b : B) (he : p e0 = b) :
    (TopCat.const (Path.refl b) : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (LoopSpace B b)) ≫
        loopToHomotopyFiber p e0 b he = homotopyFiberSelectedPointMap p e0 b he := by
  apply homotopyPullback_hom_ext
  · rw [Category.assoc, loopToHomotopyFiber_toTotal, homotopyFiberSelectedPointMap_toTotal]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  · exact TopCat.isTerminalPUnit.hom_ext _ _
  · rw [Category.assoc, loopToHomotopyFiber_path, homotopyFiberSelectedPointMap_path]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    rfl

end TopCat

end
