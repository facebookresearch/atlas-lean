/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import MathlibExt.Topology.Category.TopCat.EndpointFixedCorrection

/-!
# Whole endpoint-fixed pasting families

The original interval clocks give association and backtrack contraction
for an entire continuous homotopy family. Pasting preserves the complete
time-endpoint faces. Every source point and both interval parameters occur
in the actual continuous maps; no pointwise choice of a path homotopy is used.
-/

noncomputable section

open scoped ContinuousMap unitInterval

universe uSpace vSpace

namespace ContinuousMap.Homotopy

variable {X : Type uSpace} {Y : Type vSpace}
  [TopologicalSpace X] [TopologicalSpace Y]


private theorem evalAt_trans_value {f₀ f₁ f₂ : C(X, Y)}
    (H : Homotopy f₀ f₁) (K : Homotopy f₁ f₂) (x : X) :
    (H.trans K).evalAt x = (H.evalAt x).trans (K.evalAt x) := by
  apply _root_.Path.ext
  funext t
  change (H.trans K) (t, x) = ((H.evalAt x).trans (K.evalAt x)) t
  rw [ContinuousMap.Homotopy.trans_apply, _root_.Path.trans_apply]
  split_ifs <;> rfl

private theorem evalAt_symm_value {f₀ f₁ : C(X, Y)}
    (H : Homotopy f₀ f₁) (x : X) :
    H.symm.evalAt x = (H.evalAt x).symm := by
  apply _root_.Path.ext
  funext t
  rfl

private theorem pathReparamClockCongr
    {Z : Type vSpace} [TopologicalSpace Z] {z₀ z₁ : Z}
    (p : _root_.Path z₀ z₁) (r : C(unitInterval, unitInterval))
    (q : unitInterval → unitInterval)
    (r₀ : r 0 = 0) (r₁ : r 1 = 1)
    (hq : Continuous q) (q₀ : q 0 = 0) (q₁ : q 1 = 1)
    (hClock : ∀ t, r t = q t) :
    p.reparam r r.continuous r₀ r₁ = p.reparam q hq q₀ q₁ := by
  apply _root_.Path.ext
  funext t
  change p (r t) = p (q t)
  exact congrArg p (hClock t)

/-- Change only the original inner interval clock, retaining both actual
endpoint maps and the complete original continuous family. -/
public def reparam {f₀ f₁ : C(X, Y)} (H : Homotopy f₀ f₁)
    (r : C(unitInterval, unitInterval)) (r₀ : r 0 = 0) (r₁ : r 1 = 1) :
    Homotopy f₀ f₁ where
  toFun z := H (r z.1, z.2)
  continuous_toFun := H.continuous.comp
    ((r.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := by rw [r₀]; exact H.map_zero_left x
  map_one_left x := by rw [r₁]; exact H.map_one_left x

/-- The actual convex interpolation of inner clocks gives a WHOLE
two-parameter family relative to BOTH complete endpoint faces. -/
public def reparamToOriginal {f₀ f₁ : C(X, Y)} (H : Homotopy f₀ f₁)
    (r : C(unitInterval, unitInterval)) (r₀ : r 0 = 0) (r₁ : r 1 = 1) :
    ContinuousMap.HomotopyRel (H.reparam r r₀ r₁).toContinuousMap
      H.toContinuousMap {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} where
  toFun z := H (Set.Icc.convexComb (r z.2.1) z.2.1 z.1, z.2.2)
  continuous_toFun := H.continuous.comp
    ((Set.Icc.continuous_convexComb_prod.comp
      ((r.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_fst.comp continuous_snd).prodMk continuous_fst))).prodMk
          (continuous_snd.comp continuous_snd))
  map_zero_left z := by
    change H (Set.Icc.convexComb (r z.1) z.1 0, z.2) = H (r z.1, z.2)
    rw [Set.Icc.convexComb_zero]
  map_one_left z := by
    change H (Set.Icc.convexComb (r z.1) z.1 1, z.2) = H (z.1, z.2)
    rw [Set.Icc.convexComb_one]
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with ht | ht
    · subst t
      change H (Set.Icc.convexComb (r 0) 0 s, x) = H (r 0, x)
      rw [r₀, Set.Icc.convexComb_eq]
    · subst t
      change H (Set.Icc.convexComb (r 1) 1 s, x) = H (r 1, x)
      rw [r₁, Set.Icc.convexComb_eq]

/-- The original public path-association clock gives association of
ENTIRE homotopy families, jointly continuous in the source point and
both parameters, with BOTH complete endpoint faces fixed. -/
public def assocFamily {f₀ f₁ f₂ f₃ : C(X, Y)}
    (H : Homotopy f₀ f₁) (K : Homotopy f₁ f₂) (L : Homotopy f₂ f₃) :
    ContinuousMap.HomotopyRel ((H.trans K).trans L).toContinuousMap
      (H.trans (K.trans L)).toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} := by
  let r : C(unitInterval, unitInterval) :=
    { toFun := fun t => ⟨_root_.Path.Homotopy.transAssocReparamAux t,
        _root_.Path.Homotopy.transAssocReparamAux_mem_I t⟩
      continuous_toFun :=
        _root_.Path.Homotopy.continuous_transAssocReparamAux.subtype_mk
          _root_.Path.Homotopy.transAssocReparamAux_mem_I }
  have r₀ : r 0 = 0 :=
    Subtype.ext _root_.Path.Homotopy.transAssocReparamAux_zero
  have r₁ : r 1 = 1 :=
    Subtype.ext _root_.Path.Homotopy.transAssocReparamAux_one
  let W := H.trans (K.trans L)
  have hMap : ((H.trans K).trans L).toContinuousMap =
      (W.reparam r r₀ r₁).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    have hPath :
        ((H.trans K).trans L).evalAt z.2 =
          (W.evalAt z.2).reparam r r.continuous r₀ r₁ := by
      let clock : unitInterval → unitInterval := fun t =>
        ⟨_root_.Path.Homotopy.transAssocReparamAux t,
          _root_.Path.Homotopy.transAssocReparamAux_mem_I t⟩
      have hClockContinuous : Continuous clock :=
        _root_.Path.Homotopy.continuous_transAssocReparamAux.subtype_mk
          _root_.Path.Homotopy.transAssocReparamAux_mem_I
      have clock₀ : clock 0 = 0 :=
        Subtype.ext _root_.Path.Homotopy.transAssocReparamAux_zero
      have clock₁ : clock 1 = 1 :=
        Subtype.ext _root_.Path.Homotopy.transAssocReparamAux_one
      have hClock : ∀ t, r t = clock t := by
        intro t
        rfl
      have hCanonical :
          ((H.trans K).trans L).evalAt z.2 =
            (W.evalAt z.2).reparam clock hClockContinuous clock₀ clock₁ := by
        simpa only [evalAt_trans_value, W, clock] using
          (_root_.Path.Homotopy.trans_assoc_reparam
            (H.evalAt z.2) (K.evalAt z.2) (L.evalAt z.2))
      exact hCanonical.trans
        (pathReparamClockCongr (W.evalAt z.2) r clock r₀ r₁
          hClockContinuous clock₀ clock₁ hClock).symm
    exact congrArg (fun p : _root_.Path (f₀ z.2) (f₃ z.2) => p z.1) hPath
  exact (W.reparamToOriginal r r₀ r₁).cast hMap.symm rfl

/-- The SAME original public backtrack clock contracts the ENTIRE
original family followed by its reverse, relative to both complete faces. -/
public def backtrackFamily {f₀ f₁ : C(X, Y)} (H : Homotopy f₀ f₁) :
    ContinuousMap.HomotopyRel (H.trans H.symm).toContinuousMap
      (Homotopy.refl f₀).toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} where
  toFun z := (_root_.Path.Homotopy.reflTransSymm (H.evalAt z.2.2)).symm
    (z.1, z.2.1)
  continuous_toFun := by
    change Continuous (fun z : unitInterval × (unitInterval × X) =>
      H (⟨_root_.Path.Homotopy.reflTransSymmAux (σ z.1, z.2.1),
        _root_.Path.Homotopy.reflTransSymmAux_mem_I (σ z.1, z.2.1)⟩, z.2.2))
    have hClock : Continuous (fun z : unitInterval × (unitInterval × X) =>
        (⟨_root_.Path.Homotopy.reflTransSymmAux (σ z.1, z.2.1),
          _root_.Path.Homotopy.reflTransSymmAux_mem_I (σ z.1, z.2.1)⟩ : unitInterval)) :=
      (_root_.Path.Homotopy.continuous_reflTransSymmAux.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk
          (continuous_fst.comp continuous_snd))).subtype_mk
            (fun z => _root_.Path.Homotopy.reflTransSymmAux_mem_I (σ z.1, z.2.1))
    exact H.continuous.comp
      (hClock.prodMk (continuous_snd.comp continuous_snd))
  map_zero_left z := by
    have h := (_root_.Path.Homotopy.reflTransSymm (H.evalAt z.2)).symm.map_zero_left z.1
    have hp : (H.trans H.symm).evalAt z.2 =
        (H.evalAt z.2).trans (H.evalAt z.2).symm := by
      simpa only [evalAt_symm_value] using evalAt_trans_value H H.symm z.2
    exact h.trans (congrArg
      (fun p : _root_.Path (f₀ z.2) (f₀ z.2) => p z.1) hp).symm
  map_one_left z := by
    exact (_root_.Path.Homotopy.reflTransSymm (H.evalAt z.2)).symm.map_one_left z.1
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with ht | ht
    · subst t
      exact ((_root_.Path.Homotopy.reflTransSymm (H.evalAt x)).symm.source s).trans
        ((H.trans H.symm).map_zero_left x).symm
    · subst t
      exact ((_root_.Path.Homotopy.reflTransSymm (H.evalAt x)).symm.target s).trans
        ((H.trans H.symm).map_one_left x).symm

/-- Delete the original constant prefix by its EXISTING original tail
clock; the full comparison keeps both complete time-endpoint faces fixed. -/
public def reflTransFamily {f₀ f₁ : C(X, Y)} (H : Homotopy f₀ f₁) :
    ContinuousMap.HomotopyRel ((Homotopy.refl f₀).trans H).toContinuousMap
      H.toContinuousMap {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} := by
  let r := TopCat.homotopyReflTransReparam
  have hMap : ((Homotopy.refl f₀).trans H).toContinuousMap =
      (H.reparam r TopCat.homotopyReflTransReparam_zero
        TopCat.homotopyReflTransReparam_one).toContinuousMap := by
    apply ContinuousMap.ext
    intro z
    change ((Homotopy.refl f₀).trans H) (z.1, z.2) = H (r z.1, z.2)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · rw [TopCat.homotopyReflTransReparam_eq_zero_of_le z.1 ht]
      exact (H.map_zero_left z.2).symm
    · rw [TopCat.homotopyReflTransReparam_eq_of_not_le z.1 ht]
  exact (H.reparamToOriginal r TopCat.homotopyReflTransReparam_zero
    TopCat.homotopyReflTransReparam_one).cast hMap.symm rfl

private def parameterFamily {f₀ f₁ : C(X, Y)} {H H' : Homotopy f₀ f₁}
    (L : ContinuousMap.HomotopyRel H.toContinuousMap H'.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1}) :
    Homotopy
      (f₀.comp (ContinuousMap.snd : C(unitInterval × X, X)))
      (f₁.comp (ContinuousMap.snd : C(unitInterval × X, X))) where
  toFun z := L (z.2.1, (z.1, z.2.2))
  continuous_toFun := L.continuous.comp
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := (L.eq_fst z.1 (Or.inl rfl)).trans (H.map_zero_left z.2)
  map_one_left z := (L.eq_fst z.1 (Or.inr rfl)).trans (H.map_one_left z.2)

/-- Append the SAME original homotopy to a WHOLE relative family.
The actual pasting is continuous in all source and parameter coordinates. -/
public def appendFamily {f₀ f₁ f₂ : C(X, Y)}
    (H H' : Homotopy f₀ f₁) (K : Homotopy f₁ f₂)
    (L : ContinuousMap.HomotopyRel H.toContinuousMap H'.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1}) :
    ContinuousMap.HomotopyRel (H.trans K).toContinuousMap
      (H'.trans K).toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} := by
  let C := (parameterFamily L).trans
    (K.compContinuousMap (ContinuousMap.snd : C(unitInterval × X, X)))
  refine
    { toFun := fun z => C (z.2.1, (z.1, z.2.2))
      continuous_toFun := C.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro z
    change C (z.1, (0, z.2)) = (H.trans K) (z.1, z.2)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact L.map_zero_left _
    · rfl
  · intro z
    change C (z.1, (1, z.2)) = (H'.trans K) (z.1, z.2)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · exact L.map_one_left _
    · rfl
  · intro s z hz
    rcases z with ⟨t, x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with ht | ht
    · subst t
      exact (C.map_zero_left (s, x)).trans ((H.trans K).map_zero_left x).symm
    · subst t
      exact (C.map_one_left (s, x)).trans ((H.trans K).map_one_left x).symm

/-- Prepend the SAME original homotopy to a WHOLE relative family,
retaining BOTH complete endpoint faces and all active source points. -/
public def prependFamily {f₀ f₁ f₂ : C(X, Y)}
    (K : Homotopy f₀ f₁) (H H' : Homotopy f₁ f₂)
    (L : ContinuousMap.HomotopyRel H.toContinuousMap H'.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1}) :
    ContinuousMap.HomotopyRel (K.trans H).toContinuousMap
      (K.trans H').toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} := by
  let C := (K.compContinuousMap (ContinuousMap.snd : C(unitInterval × X, X))).trans
    (parameterFamily L)
  refine
    { toFun := fun z => C (z.2.1, (z.1, z.2.2))
      continuous_toFun := C.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro z
    change C (z.1, (0, z.2)) = (K.trans H) (z.1, z.2)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · rfl
    · exact L.map_zero_left _
  · intro z
    change C (z.1, (1, z.2)) = (K.trans H') (z.1, z.2)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · rfl
    · exact L.map_one_left _
  · intro s z hz
    rcases z with ⟨t, x⟩
    change t = 0 ∨ t = 1 at hz
    rcases hz with ht | ht
    · subst t
      exact (C.map_zero_left (s, x)).trans ((K.trans H).map_zero_left x).symm
    · subst t
      exact (C.map_one_left (s, x)).trans ((K.trans H).map_one_left x).symm

end ContinuousMap.Homotopy

end
