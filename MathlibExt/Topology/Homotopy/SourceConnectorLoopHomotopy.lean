/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Joint source-connector loop homotopy and actual unit rectangle

Every time slice is rooted by the same actual source connector mapped
through the whole relative homotopy, followed by the same actual target
path. The entire loop family has an actual moving unit. One fixed interval
backtrack template contracts that unit jointly over both time parameters.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.HomotopyRel

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} {x₀ x₁ : X} {y₁ y₀ : Y}

private def mappedSourceConnector (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (hf : f x₁ = y₁) (t : I) : Path (H (t, x₀)) y₁ where
  toFun s := H (t, r s)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk r.continuous)
  source' := congrArg (fun x => H (t, x)) r.source
  target' := (congrArg (fun x => H (t, x)) r.target).trans
    ((H.eq_fst t (Set.mem_singleton x₁)).trans hf)

private def sourceRootAt (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (t : I) :
    Path (H (t, x₀)) y₀ :=
  (mappedSourceConnector H r hf t).trans q

private theorem sourceRootAt_continuous (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) :
    Continuous (fun ts : I × I => sourceRootAt H r q hf ts.1 ts.2) := by
  have hR : Continuous (fun ts : I × I => mappedSourceConnector H r hf ts.1 ts.2) :=
    H.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  have hQ : Continuous (fun ts : I × I => q ts.2) := q.continuous.comp continuous_snd
  exact Path.trans_continuous_family (fun t => mappedSourceConnector H r hf t) hR
    (fun _ => q) hQ

private def sourceMappedLoopAt (H : HomotopyRel f g {x₁})
    (γ : LoopSpace X x₀) (t : I) : Path (H (t, x₀)) (H (t, x₀)) where
  toFun s := H (t, γ s)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk γ.continuous)
  source' := congrArg (fun x => H (t, x)) γ.source
  target' := congrArg (fun x => H (t, x)) γ.target

private def sourceConnectorLoopFamily (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) :
    C(I × LoopSpace X x₀, LoopSpace Y y₀) where
  toFun tγ := (sourceRootAt H r q hf tγ.1).symm.trans
    ((sourceMappedLoopAt H tγ.2 tγ.1).trans (sourceRootAt H r q hf tγ.1))
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    let A := I × LoopSpace X x₀
    let T : ∀ a : A, Path (H (a.1, x₀)) y₀ := fun a => sourceRootAt H r q hf a.1
    let M : ∀ a : A, Path (H (a.1, x₀)) (H (a.1, x₀)) :=
      fun a => sourceMappedLoopAt H a.2 a.1
    have hT : Continuous ↿T := (sourceRootAt_continuous H r q hf).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    have hM : Continuous ↿M := H.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_eval.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    have hTS := Path.symm_continuous_family T hT
    have hMT := Path.trans_continuous_family M hM T hT
    exact Path.trans_continuous_family (fun a => (T a).symm) hTS
      (fun a => (M a).trans (T a)) hMT

private theorem sourceRootAt_zero (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) :
    (sourceRootAt H r q hf 0).cast (H.apply_zero x₀).symm rfl =
      ((r.map f.continuous).cast rfl hf.symm).trans q := by
  apply Path.ext
  funext s
  change (mappedSourceConnector H r hf 0).trans q s =
    ((r.map f.continuous).cast rfl hf.symm).trans q s
  simp only [Path.trans_apply]
  split_ifs
  · exact H.apply_zero _
  · rfl

private theorem sourceRootAt_one (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (hg : g x₁ = y₁) :
    (sourceRootAt H r q hf 1).cast (H.apply_one x₀).symm rfl =
      ((r.map g.continuous).cast rfl hg.symm).trans q := by
  apply Path.ext
  funext s
  change (mappedSourceConnector H r hf 1).trans q s =
    ((r.map g.continuous).cast rfl hg.symm).trans q s
  simp only [Path.trans_apply]
  split_ifs
  · exact H.apply_one _
  · rfl

private theorem sourceMappedLoopAt_zero (H : HomotopyRel f g {x₁})
    (γ : LoopSpace X x₀) :
    (sourceMappedLoopAt H γ 0).cast (H.apply_zero x₀).symm (H.apply_zero x₀).symm =
      γ.map f.continuous := by
  apply Path.ext
  funext s
  exact H.apply_zero _

private theorem sourceMappedLoopAt_one (H : HomotopyRel f g {x₁})
    (γ : LoopSpace X x₀) :
    (sourceMappedLoopAt H γ 1).cast (H.apply_one x₀).symm (H.apply_one x₀).symm =
      γ.map g.continuous := by
  apply Path.ext
  funext s
  exact H.apply_one _

private theorem sourceConjugation_cast {a a' b : Y} (p : Path a b)
    (γ : Path a a) (h : a' = a) :
    (p.cast h rfl).symm.trans ((γ.cast h h).trans (p.cast h rfl)) =
      p.symm.trans (γ.trans p) := by
  cases h
  rfl

/-- The actual complete source-rooted loop family has the original two
loop maps, with the SAME source connector and SAME target root path. -/
def sourceConnectorLoopHomotopy (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (hg : g x₁ = y₁) :
    Homotopy
      (⟨f, ((r.map f.continuous).cast rfl hf.symm).trans q⟩ :
        WeaklyPointed x₀ y₀).loopMap
      (⟨g, ((r.map g.continuous).cast rfl hg.symm).trans q⟩ :
        WeaklyPointed x₀ y₀).loopMap where
  toContinuousMap := sourceConnectorLoopFamily H r q hf
  map_zero_left γ := by
    change (sourceRootAt H r q hf 0).symm.trans
      ((sourceMappedLoopAt H γ 0).trans (sourceRootAt H r q hf 0)) = _
    rw [← sourceConjugation_cast (sourceRootAt H r q hf 0) (sourceMappedLoopAt H γ 0)
      (H.apply_zero x₀).symm, sourceRootAt_zero, sourceMappedLoopAt_zero]
    rfl
  map_one_left γ := by
    change (sourceRootAt H r q hf 1).symm.trans
      ((sourceMappedLoopAt H γ 1).trans (sourceRootAt H r q hf 1)) = _
    rw [← sourceConjugation_cast (sourceRootAt H r q hf 1) (sourceMappedLoopAt H γ 1)
      (H.apply_one x₀).symm, sourceRootAt_one H r q hf hg, sourceMappedLoopAt_one]
    rfl

private def sourceUnitTemplate : LoopSpace I (1 : I) :=
  (Path.id : Path (0 : I) (1 : I)).symm.trans
    ((Path.refl (0 : I)).trans (Path.id : Path (0 : I) (1 : I)))

private def sourceUnitTemplateContraction :
    sourceUnitTemplate.Homotopy (Path.refl (1 : I)) where
  toFun us := Set.Icc.convexComb (sourceUnitTemplate us.2) 1 us.1
  continuous_toFun := by fun_prop
  map_zero_left s := by
    change Set.Icc.convexComb (sourceUnitTemplate s) 1 0 = sourceUnitTemplate s
    rw [Set.Icc.convexComb_zero]
  map_one_left s := by
    change Set.Icc.convexComb (sourceUnitTemplate s) 1 1 = 1
    rw [Set.Icc.convexComb_one]
  prop' := by
    intro u s hs
    rcases hs with hs | hs
    · subst s
      change Set.Icc.convexComb (sourceUnitTemplate 0) 1 u = sourceUnitTemplate 0
      rw [sourceUnitTemplate.source, Set.Icc.convexComb_eq]
    · have hs' : s = 1 := Set.mem_singleton_iff.mp hs
      subst s
      change Set.Icc.convexComb (sourceUnitTemplate 1) 1 u = sourceUnitTemplate 1
      rw [sourceUnitTemplate.target, Set.Icc.convexComb_eq]

private theorem sourceConnectorLoopFamily_refl_template
    (H : HomotopyRel f g {x₁}) (r : Path x₀ x₁) (q : Path y₁ y₀)
    (hf : f x₁ = y₁) (t s : I) :
    sourceConnectorLoopFamily H r q hf (t, Path.refl x₀) s =
      sourceRootAt H r q hf t (sourceUnitTemplate s) := by
  change (sourceRootAt H r q hf t).symm.trans
      ((sourceMappedLoopAt H (Path.refl x₀) t).trans (sourceRootAt H r q hf t)) s =
    sourceRootAt H r q hf t (sourceUnitTemplate s)
  have hM : sourceMappedLoopAt H (Path.refl x₀) t = Path.refl (H (t, x₀)) := by
    apply Path.ext
    rfl
  rw [hM]
  unfold sourceUnitTemplate
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · rfl
  · change H (t, x₀) = (sourceRootAt H r q hf t) 0
    exact (sourceRootAt H r q hf t).source.symm
  · rfl

private def sourceConnectorLoopUnitFamily (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) :
    C(I × I, LoopSpace Y y₀) where
  toFun tu :=
    { toFun := fun s => sourceRootAt H r q hf tu.1 (sourceUnitTemplateContraction (tu.2, s))
      continuous_toFun := (sourceRootAt H r q hf tu.1).continuous.comp
        (sourceUnitTemplateContraction.continuous.comp (continuous_const.prodMk continuous_id))
      source' := by
        rw [sourceUnitTemplateContraction.eq_snd tu.2 (by simp)]
        exact (sourceRootAt H r q hf tu.1).target
      target' := by
        rw [sourceUnitTemplateContraction.eq_snd tu.2 (by simp)]
        exact (sourceRootAt H r q hf tu.1).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (sourceRootAt_continuous H r q hf).comp
      ((continuous_fst.comp continuous_fst).prodMk
        (sourceUnitTemplateContraction.continuous.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

/-- One jointly continuous TWO-parameter unit rectangle for the complete
original source-connector loop homotopy. -/
def sourceConnectorLoopUnitRectangle (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) :
    C(I × I, LoopSpace Y y₀) := sourceConnectorLoopUnitFamily H r q hf

/-- At contraction-zero the rectangle is the ACTUAL original moving unit
trace of the ENTIRE loop homotopy, for every original homotopy time. -/
theorem sourceConnectorLoopUnitRectangle_zero (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (hg : g x₁ = y₁) (t : I) :
    sourceConnectorLoopUnitRectangle H r q hf (t, 0) =
      sourceConnectorLoopHomotopy H r q hf hg (t, Path.refl x₀) := by
  apply Path.ext
  funext s
  change sourceRootAt H r q hf t (sourceUnitTemplateContraction (0, s)) =
    sourceConnectorLoopFamily H r q hf (t, Path.refl x₀) s
  rw [sourceUnitTemplateContraction.apply_zero]
  exact (sourceConnectorLoopFamily_refl_template H r q hf t s).symm

/-- At contraction-one the rectangle is the ORIGINAL canonical constant
loop for every original homotopy time, from the actual interval-template contraction. -/
theorem sourceConnectorLoopUnitRectangle_one (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (t : I) :
    sourceConnectorLoopUnitRectangle H r q hf (t, 1) = Path.refl y₀ := by
  apply Path.ext
  funext s
  change sourceRootAt H r q hf t (sourceUnitTemplateContraction (1, s)) = y₀
  rw [sourceUnitTemplateContraction.apply_one]
  exact (sourceRootAt H r q hf t).target

/-- The ACTUAL source-connector root at every original homotopy time. -/
def sourceConnectorRootAt (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (t : I) :
    Path (H (t, x₀)) y₀ := sourceRootAt H r q hf t

/-- The ORIGINAL interval backtrack of a conjugated constant loop. -/
def sourceLoopUnitTemplate : LoopSpace I (1 : I) := sourceUnitTemplate

/-- The ACTUAL convex contraction of the ORIGINAL interval backtrack. -/
def sourceLoopUnitTemplateContraction :
    sourceLoopUnitTemplate.Homotopy (Path.refl (1 : I)) := sourceUnitTemplateContraction

/-- BOTH time parameters and every loop coordinate of the actual unit
rectangle retain the SAME original root and SAME interval template contraction. -/
theorem sourceConnectorLoopUnitRectangle_value (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (t u s : I) :
    sourceConnectorLoopUnitRectangle H r q hf (t, u) s =
      sourceConnectorRootAt H r q hf t (sourceLoopUnitTemplateContraction (u, s)) := by
  unfold sourceConnectorLoopUnitRectangle sourceConnectorLoopUnitFamily
    sourceConnectorRootAt sourceLoopUnitTemplateContraction
  rfl

end ContinuousMap.HomotopyRel

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

private theorem originalLoopUnitTemplate_value (F : WeaklyPointed x y) (s : I) :
    F.loopMap (Path.refl x) s = F.rootPath (HomotopyRel.sourceLoopUnitTemplate s) := by
  change F.rootPath.symm.trans
    (((Path.refl x).map F.hom.continuous).trans F.rootPath) s = _
  have hMap : (Path.refl x).map F.hom.continuous = Path.refl (F.hom x) := by
    apply Path.ext
    rfl
  rw [hMap]
  unfold HomotopyRel.sourceLoopUnitTemplate HomotopyRel.sourceUnitTemplate
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · rfl
  · change F.hom x = F.rootPath 0
    exact F.rootPath.source.symm
  · rfl

private def originalLoopUnitFamily (F : WeaklyPointed x y) : C(I, LoopSpace Y y) where
  toFun u :=
    { toFun := fun s => F.rootPath (HomotopyRel.sourceLoopUnitTemplateContraction (u, s))
      continuous_toFun := F.rootPath.continuous.comp
        (HomotopyRel.sourceLoopUnitTemplateContraction.continuous.comp
          (continuous_const.prodMk continuous_id))
      source' := by
        rw [HomotopyRel.sourceLoopUnitTemplateContraction.eq_snd u (by simp)]
        exact F.rootPath.target
      target' := by
        rw [HomotopyRel.sourceLoopUnitTemplateContraction.eq_snd u (by simp)]
        exact F.rootPath.target }
  continuous_toFun := Path.continuous_uncurry_iff.mp
    (F.rootPath.continuous.comp HomotopyRel.sourceLoopUnitTemplateContraction.continuous)

/-- The ACTUAL canonical unit path of an ORIGINAL weakly pointed loop map:
contract its original padded unit through its original root path and interval template. -/
def loopUnitRootPath (F : WeaklyPointed x y) :
    Path (F.loopMap (Path.refl x)) (Path.refl y) where
  toContinuousMap := originalLoopUnitFamily F
  source' := by
    apply Path.ext
    funext s
    change F.rootPath (HomotopyRel.sourceLoopUnitTemplateContraction (0, s)) =
      F.loopMap (Path.refl x) s
    rw [HomotopyRel.sourceLoopUnitTemplateContraction.apply_zero]
    exact (originalLoopUnitTemplate_value F s).symm
  target' := by
    apply Path.ext
    funext s
    change F.rootPath (HomotopyRel.sourceLoopUnitTemplateContraction (1, s)) = y
    rw [HomotopyRel.sourceLoopUnitTemplateContraction.apply_one]
    exact F.rootPath.target

/-- EVERY contraction time and EVERY loop coordinate retain the ACTUAL
original root path evaluated on the ORIGINAL unit-template contraction. -/
theorem loopUnitRootPath_value (F : WeaklyPointed x y) (u s : I) :
    loopUnitRootPath F u s =
      F.rootPath (HomotopyRel.sourceLoopUnitTemplateContraction (u, s)) := by
  unfold loopUnitRootPath originalLoopUnitFamily
  rfl

end ContinuousMap.WeaklyPointed

namespace ContinuousMap.HomotopyRel

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} {x₀ x₁ : X} {y₁ y₀ : Y}

/-- The two ORIGINAL canonical unit paths are compatible with the ACTUAL
unit trace of the WHOLE source-connector loop homotopy. The uniform unit
rectangle earns this path homotopy, with no supplied coherence outcome. -/
theorem sourceConnectorLoopUnitRootHomotopic (H : HomotopyRel f g {x₁})
    (r : Path x₀ x₁) (q : Path y₁ y₀) (hf : f x₁ = y₁) (hg : g x₁ = y₁) :
    (WeaklyPointed.loopUnitRootPath
      (⟨f, ((r.map f.continuous).cast rfl hf.symm).trans q⟩ : WeaklyPointed x₀ y₀)).Homotopic
      (((sourceConnectorLoopHomotopy H r q hf hg).evalAt (Path.refl x₀)).trans
        (WeaklyPointed.loopUnitRootPath
          (⟨g, ((r.map g.continuous).cast rfl hg.symm).trans q⟩ : WeaklyPointed x₀ y₀))) := by
  let F : WeaklyPointed x₀ y₀ := ⟨f, ((r.map f.continuous).cast rfl hf.symm).trans q⟩
  let G : WeaklyPointed x₀ y₀ := ⟨g, ((r.map g.continuous).cast rfl hg.symm).trans q⟩
  let K := sourceConnectorLoopHomotopy H r q hf hg
  let U := sourceConnectorLoopUnitRectangle H r q hf
  let UF : C(I, LoopSpace Y y₀) := U.comp
    ⟨fun u => ((0 : I), u), continuous_const.prodMk continuous_id⟩
  let UG : C(I, LoopSpace Y y₀) := U.comp
    ⟨fun u => ((1 : I), u), continuous_const.prodMk continuous_id⟩
  let HU : Homotopy UF UG :=
    { toContinuousMap := U
      map_zero_left _ := rfl
      map_one_left _ := rfl }
  have h00 : UF 0 = F.loopMap (Path.refl x₀) :=
    (sourceConnectorLoopUnitRectangle_zero H r q hf hg 0).trans (K.apply_zero _)
  have h10 : UG 0 = G.loopMap (Path.refl x₀) :=
    (sourceConnectorLoopUnitRectangle_zero H r q hf hg 1).trans (K.apply_one _)
  have h01 : UF 1 = Path.refl y₀ := sourceConnectorLoopUnitRectangle_one H r q hf 0
  have h11 : UG 1 = Path.refl y₀ := sourceConnectorLoopUnitRectangle_one H r q hf 1
  let PF := ((Path.id : Path (0 : I) (1 : I)).map UF.continuous).cast h00.symm h01.symm
  let PG := ((Path.id : Path (0 : I) (1 : I)).map UG.continuous).cast h10.symm h11.symm
  let PT := (HU.evalAt 1).cast h01.symm h11.symm
  let PB := (HU.evalAt 0).cast h00.symm h10.symm
  have hPF : PF = WeaklyPointed.loopUnitRootPath F := by
    apply Path.ext
    funext u
    apply Path.ext
    funext s
    change U (0, u) s = WeaklyPointed.loopUnitRootPath F u s
    rw [sourceConnectorLoopUnitRectangle_value, WeaklyPointed.loopUnitRootPath_value]
    exact congrArg (fun p : Path (f x₀) y₀ => p (sourceLoopUnitTemplateContraction (u, s)))
      (sourceRootAt_zero H r q hf)
  have hPG : PG = WeaklyPointed.loopUnitRootPath G := by
    apply Path.ext
    funext u
    apply Path.ext
    funext s
    change U (1, u) s = WeaklyPointed.loopUnitRootPath G u s
    rw [sourceConnectorLoopUnitRectangle_value, WeaklyPointed.loopUnitRootPath_value]
    exact congrArg (fun p : Path (g x₀) y₀ => p (sourceLoopUnitTemplateContraction (u, s)))
      (sourceRootAt_one H r q hf hg)
  have hPT : PT = Path.refl (Path.refl y₀) := by
    apply Path.ext
    funext t
    exact sourceConnectorLoopUnitRectangle_one H r q hf t
  have hPB : PB = K.evalAt (Path.refl x₀) := by
    apply Path.ext
    funext t
    exact sourceConnectorLoopUnitRectangle_zero H r q hf hg t
  have hSquare := (Path.Homotopic.map_trans_evalAt HU
    (Path.id : Path (0 : I) (1 : I))).pathCast h00.symm h11.symm
  have hLeft :
      ((((Path.id : Path (0 : I) (1 : I)).map UF.continuous).trans (HU.evalAt 1)).cast
        h00.symm h11.symm) = PF.trans PT := by
    apply Path.ext
    rfl
  have hRight :
      (((HU.evalAt 0).trans ((Path.id : Path (0 : I) (1 : I)).map UG.continuous)).cast
        h00.symm h11.symm) = PB.trans PG := by
    apply Path.ext
    rfl
  have hComp : (PF.trans PT).Homotopic (PB.trans PG) :=
    Nonempty.map (fun L => Path.Homotopy.cast L hLeft hRight) hSquare
  rw [hPF, hPG, hPT, hPB] at hComp
  exact (Path.Homotopic.trans_refl (WeaklyPointed.loopUnitRootPath F)).symm.trans hComp

end ContinuousMap.HomotopyRel

end


noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe uOriginalRootValue vOriginalRootValue

namespace ContinuousMap.HomotopyRel

variable {X : Type uOriginalRootValue} {Y : Type vOriginalRootValue}
  [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} {x₀ x₁ : X} {y₁ y₀ : Y}

private theorem originalSourceConnectorRootValueComputed
    (H : HomotopyRel f g {x₁}) (r : Path x₀ x₁) (q : Path y₁ y₀)
    (hf : f x₁ = y₁) (t s : I) :
    sourceConnectorRootAt H r q hf t s =
      if hs : (s : ℝ) ≤ 1 / 2 then
        H.toHomotopy.toContinuousMap.toFun
          (t, r (⟨2 * (s : ℝ),
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ : I))
      else
        q (⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ : I) := by
  change (mappedSourceConnector H r hf t).trans q s = _
  rw [Path.trans_apply]
  split_ifs <;> rfl

/-- Every original homotopy and root-path time retains the actual original
H-image of SAME r followed by SAME q, with the original canonical half clock. -/
public theorem sourceConnectorRootAt_apply
    (H : HomotopyRel f g {x₁}) (r : Path x₀ x₁) (q : Path y₁ y₀)
    (hf : f x₁ = y₁) (t s : I) :
    sourceConnectorRootAt H r q hf t s =
      if hs : (s : ℝ) ≤ 1 / 2 then
        H.toHomotopy.toContinuousMap.toFun
          (t, r (⟨2 * (s : ℝ),
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ : I))
      else
        q (⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ : I) :=
  originalSourceConnectorRootValueComputed H r q hf t s

end ContinuousMap.HomotopyRel

end


noncomputable section

open unitInterval
open scoped Topology ContinuousMap

namespace ContinuousMap.HomotopyRel

private theorem originalSourceLoopUnitTemplateContractionValueComputed (u s : I) :
    sourceLoopUnitTemplateContraction (u, s) =
      Set.Icc.convexComb
        (((Path.id : Path (0 : I) (1 : I)).symm.trans
          ((Path.refl (0 : I)).trans (Path.id : Path (0 : I) (1 : I)))) s) 1 u := rfl

/-- Both original contraction and loop times read the ACTUAL original
three-piece interval word under its SAME affine contraction to the target. -/
public theorem sourceLoopUnitTemplateContraction_apply (u s : I) :
    sourceLoopUnitTemplateContraction (u, s) =
      Set.Icc.convexComb
        (((Path.id : Path (0 : I) (1 : I)).symm.trans
          ((Path.refl (0 : I)).trans (Path.id : Path (0 : I) (1 : I)))) s) 1 u :=
  originalSourceLoopUnitTemplateContractionValueComputed u s

end ContinuousMap.HomotopyRel

end
