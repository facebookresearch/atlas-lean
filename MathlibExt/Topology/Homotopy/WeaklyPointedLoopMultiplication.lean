/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopies
public import Mathlib.Topology.Homotopy.HSpaces

/-!
# Original weakly pointed loop maps and multiplication

The actual chosen root path is retained in a jointly continuous family
showing that the original weakly pointed loop map preserves the original
loop H-space concatenation. The original root-pair contractions also give
its genuine unit path, with both original time coordinates recorded.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

private def originalConjugationMultiplicationComputed {x y : X} (p : Path x y) :
    Homotopy
      ((loopBasepointChange p).comp
        (HSpace.hmul : C(LoopSpace X x × LoopSpace X x, LoopSpace X x)))
      ((HSpace.hmul : C(LoopSpace X y × LoopSpace X y, LoopSpace X y)).comp
        ((loopBasepointChange p).prodMap (loopBasepointChange p))) := by
  let B := LoopSpace X x × LoopSpace X x
  let mx : C(B, LoopSpace X x) := HSpace.hmul
  let my : C(LoopSpace X y × LoopSpace X y, LoopSpace X y) := HSpace.hmul
  let F := loopBasepointChange p
  let tail : C(B, Path x y) := ⟨fun z => z.2.trans p, by fun_prop⟩
  let loopPrefix : C(Path x y, LoopSpace X y) := ⟨fun r => p.symm.trans r, by fun_prop⟩
  let context : C(LoopSpace X x × Path x y, LoopSpace X y) :=
    ⟨fun z => p.symm.trans (z.1.trans z.2), by fun_prop⟩
  let A₀ : C(B, LoopSpace X y) := my.comp (F.prodMap F)
  let A₁ : C(B, LoopSpace X y) :=
    ⟨fun z => p.symm.trans
      ((z.1.trans p).trans (p.symm.trans (z.2.trans p))), by fun_prop⟩
  let A₂ : C(B, LoopSpace X y) :=
    ⟨fun z => p.symm.trans
      (z.1.trans (p.trans (p.symm.trans (z.2.trans p)))), by fun_prop⟩
  let A₃ : C(B, LoopSpace X y) :=
    ⟨fun z => p.symm.trans
      (z.1.trans ((p.trans p.symm).trans (z.2.trans p))), by fun_prop⟩
  let A₄ : C(B, LoopSpace X y) :=
    ⟨fun z => p.symm.trans
      (z.1.trans ((Path.refl x).trans (z.2.trans p))), by fun_prop⟩
  let A₅ : C(B, LoopSpace X y) :=
    ⟨fun z => p.symm.trans (z.1.trans (z.2.trans p)), by fun_prop⟩
  let c₁ : C(B, (Path y x × Path x y) × Path y y) :=
    ⟨fun z => ((p.symm, z.1.trans p), p.symm.trans (z.2.trans p)), by fun_prop⟩
  let c₂ : C(B, (Path x x × Path x y) × Path y y) :=
    ⟨fun z => ((z.1, p), p.symm.trans (z.2.trans p)), by fun_prop⟩
  let c₃ : C(B, (Path x y × Path y x) × Path x y) :=
    ⟨fun z => ((p, p.symm), z.2.trans p), by fun_prop⟩
  let c₆ : C(B, (Path x x × Path x x) × Path x y) :=
    ⟨fun z => ((z.1, z.2), p), by fun_prop⟩
  let H₁ : Homotopy A₀ A₁ :=
    ((pathTripleAssocHomotopy y x y y).compContinuousMap c₁).cast rfl rfl
  let H₂ : Homotopy A₁ A₂ :=
    ((Homotopy.refl loopPrefix).comp
      ((pathTripleAssocHomotopy x x y y).compContinuousMap c₂)).cast rfl rfl
  let K₃ := (pathTripleAssocHomotopy x y x y).symm.compContinuousMap c₃
  let H₃ : Homotopy A₂ A₃ :=
    ((Homotopy.refl context).comp
      ((Homotopy.refl (ContinuousMap.fst : C(B, LoopSpace X x))).prodMk K₃)).cast rfl rfl
  let K := (Path.Homotopy.reflTransSymm p).symm
  let E : C(I, Path x x) :=
    ⟨K.eval, Path.continuous_uncurry_iff.mp K.continuous_toFun⟩
  let K₄ : Homotopy
      (⟨fun z : B => (p.trans p.symm).trans (z.2.trans p), by fun_prop⟩ : C(B, Path x y))
      ((pathPrependRefl x y).comp tail) :=
    { toFun := fun z => (K.eval z.1).trans (tail z.2)
      continuous_toFun := Continuous.path_trans
        (E.continuous.comp continuous_fst) (tail.continuous.comp continuous_snd)
      map_zero_left := fun z => by rw [Path.Homotopy.eval_zero]; rfl
      map_one_left := fun z => by rw [Path.Homotopy.eval_one]; rfl }
  let H₄ : Homotopy A₃ A₄ :=
    ((Homotopy.refl context).comp
      ((Homotopy.refl (ContinuousMap.fst : C(B, LoopSpace X x))).prodMk K₄)).cast rfl rfl
  let K₅ := (pathPrependReflHomotopy x y).compContinuousMap tail
  let H₅ : Homotopy A₄ A₅ :=
    ((Homotopy.refl context).comp
      ((Homotopy.refl (ContinuousMap.fst : C(B, LoopSpace X x))).prodMk K₅)).cast rfl rfl
  let H₆ : Homotopy A₅ (F.comp mx) :=
    ((Homotopy.refl loopPrefix).comp
      ((pathTripleAssocHomotopy x x x y).symm.compContinuousMap c₆)).cast rfl rfl
  exact (H₁.trans (H₂.trans (H₃.trans (H₄.trans (H₅.trans H₆))))).symm

/-- The original root conjugation preserves original loop multiplication
by ONE jointly continuous homotopy on every original loop pair. -/
def loopBasepointChangeMultiplicationHomotopy {x y : X} (p : Path x y) :
    Homotopy
      ((loopBasepointChange p).comp
        (HSpace.hmul : C(LoopSpace X x × LoopSpace X x, LoopSpace X x)))
      ((HSpace.hmul : C(LoopSpace X y × LoopSpace X y, LoopSpace X y)).comp
        ((loopBasepointChange p).prodMap (loopBasepointChange p))) :=
  originalConjugationMultiplicationComputed p

namespace WeaklyPointed

variable {Y : Type v} [TopologicalSpace Y] {x : X} {y : Y}

/-- The ENTIRE original weakly pointed loop map preserves the ORIGINAL
loop H-space operation up to one joint homotopy, with its actual root. -/
def loopMapMultiplicationHomotopy (f : WeaklyPointed x y) :
    Homotopy
      (f.loopMap.comp
        (HSpace.hmul : C(LoopSpace X x × LoopSpace X x, LoopSpace X x)))
      ((HSpace.hmul : C(LoopSpace Y y × LoopSpace Y y, LoopSpace Y y)).comp
        (f.loopMap.prodMap f.loopMap)) := by
  let M := strictLoopMap f.hom x
  let D := M.prodMap M
  let K := (loopBasepointChangeMultiplicationHomotopy f.rootPath).compContinuousMap D
  have hSource : ((loopBasepointChange f.rootPath).comp
      (HSpace.hmul : C(LoopSpace Y (f.hom x) × LoopSpace Y (f.hom x),
        LoopSpace Y (f.hom x)))).comp D =
      f.loopMap.comp (HSpace.hmul : C(LoopSpace X x × LoopSpace X x, LoopSpace X x)) := by
    apply ContinuousMap.ext
    intro z
    change f.rootPath.symm.trans
      (((z.1.map f.hom.continuous).trans (z.2.map f.hom.continuous)).trans f.rootPath) =
      f.rootPath.symm.trans (((z.1.trans z.2).map f.hom.continuous).trans f.rootPath)
    rw [Path.map_trans]
  have hTarget : ((HSpace.hmul : C(LoopSpace Y y × LoopSpace Y y, LoopSpace Y y)).comp
      ((loopBasepointChange f.rootPath).prodMap (loopBasepointChange f.rootPath))).comp D =
      (HSpace.hmul : C(LoopSpace Y y × LoopSpace Y y, LoopSpace Y y)).comp
        (f.loopMap.prodMap f.loopMap) := by
    apply ContinuousMap.ext
    intro z
    rfl
  exact K.cast hSource hTarget

/-- Contract the ACTUAL root-conjugated image of the original constant
loop, using the actual original reflexive segment and original root pair. -/
def loopMapUnitHomotopy (f : WeaklyPointed x y) :
    Path.Homotopy (f.loopMap (Path.refl x)) (Path.refl y) := by
  let K := (Path.Homotopy.refl f.rootPath.symm).hcomp
    (Path.Homotopy.reflTrans f.rootPath)
  have hSource : f.rootPath.symm.trans ((Path.refl (f.hom x)).trans f.rootPath) =
      f.loopMap (Path.refl x) := by
    apply Path.ext
    funext s
    rfl
  exact (K.cast hSource rfl).trans (Path.Homotopy.reflSymmTrans f.rootPath).symm

/-- The actual unit Path lies in the ORIGINAL loop carrier. -/
def loopMapUnitPath (f : WeaklyPointed x y) :
    Path (f.loopMap (Path.refl x)) (Path.refl y) where
  toFun t := (loopMapUnitHomotopy f).eval t
  continuous_toFun := Path.continuous_uncurry_iff.mp (loopMapUnitHomotopy f).continuous_toFun
  source' := Path.Homotopy.eval_zero (loopMapUnitHomotopy f)
  target' := Path.Homotopy.eval_one (loopMapUnitHomotopy f)

private theorem originalLoopMapUnitPathValueComputed
    (f : WeaklyPointed x y) (t s : I) :
    ((loopMapUnitPath f).toContinuousMap.toFun t : I → Y) s =
      loopMapUnitHomotopy f (t, s) := rfl

private theorem originalLoopMapMultiplicationUnitValueComputed
    (f : WeaklyPointed x y) (t s : I) :
    (loopMapMultiplicationHomotopy f (t, (Path.refl x, Path.refl x)) : I → Y) s =
      (loopMapMultiplicationHomotopy f).evalAt (Path.refl x, Path.refl x) t s := rfl

/-- BOTH original time coordinates of the actual root-unit Path are retained. -/
theorem loopMapUnitPath_apply (f : WeaklyPointed x y) (t s : I) :
    ((loopMapUnitPath f).toContinuousMap.toFun t : I → Y) s =
      loopMapUnitHomotopy f (t, s) :=
  originalLoopMapUnitPathValueComputed f t s

/-- BOTH time coordinates of the actual multiplication family at the
ORIGINAL source unit pair, with the original root-conjugated endpoints. -/
theorem loopMapMultiplicationHomotopy_unit_apply (f : WeaklyPointed x y) (t s : I) :
    (loopMapMultiplicationHomotopy f (t, (Path.refl x, Path.refl x)) : I → Y) s =
      (loopMapMultiplicationHomotopy f).evalAt (Path.refl x, Path.refl x) t s :=
  originalLoopMapMultiplicationUnitValueComputed f t s

end WeaklyPointed

end ContinuousMap

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

private theorem originalLoopMapUnitHomotopyTemplateComputed
    (f : WeaklyPointed x y) (t : I) :
    (loopMapUnitHomotopy f).eval t =
      (((loopMapUnitHomotopy
        (⟨ContinuousMap.id I, (Path.id : Path (0 : I) (1 : I))⟩ :
          WeaklyPointed (0 : I) (1 : I))).eval t).map f.rootPath.continuous).cast
            f.rootPath.target.symm f.rootPath.target.symm := by
  let p := f.rootPath
  let q : Path (0 : I) (1 : I) := Path.id
  let A := (Path.Homotopy.refl p.symm).hcomp (Path.Homotopy.reflTrans p)
  let B := (Path.Homotopy.reflSymmTrans p).symm
  let AI := (Path.Homotopy.refl q.symm).hcomp (Path.Homotopy.reflTrans q)
  let BI := (Path.Homotopy.reflSymmTrans q).symm
  have hIf (c : Prop) (dc : Decidable c)
      (a : c → Y) (b : ¬c → Y) (ai : c → I) (bi : ¬c → I)
      (ha : ∀ h, a h = p (ai h)) (hb : ∀ h, b h = p (bi h)) :
      @dite Y c dc a b = p (@dite I c dc ai bi) := by
    cases dc with
    | isTrue hc => exact ha hc
    | isFalse hc => exact hb hc
  have hA (r s : I) : A (r, s) = p (AI (r, s)) := by
    change ((Path.Homotopy.refl p.symm).hcomp (Path.Homotopy.reflTrans p)) (r, s) =
      p (((Path.Homotopy.refl q.symm).hcomp (Path.Homotopy.reflTrans q)) (r, s))
    rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
    apply hIf _ (inferInstance) _ _ _ _
    · intro hs
      rfl
    · intro hs
      rfl
  have hB (r s : I) : B (r, s) = p (BI (r, s)) := rfl
  apply Path.ext
  funext s
  change (A.trans B) (t, s) = p ((AI.trans BI) (t, s))
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  apply hIf _ (inferInstance) _ _ _ _
  · intro ht
    exact hA _ s
  · intro ht
    exact hB _ s

/-- EVERY original unit-homotopy time is the SAME actual universal
interval unit homotopy, mapped along the ACTUAL original chosen root.
The original reflexive segment, root-pair contraction and endpoint casts remain. -/
public theorem loopMapUnitHomotopy_template (f : WeaklyPointed x y) (t : I) :
    (loopMapUnitHomotopy f).eval t =
      (((loopMapUnitHomotopy
        (⟨ContinuousMap.id I, (Path.id : Path (0 : I) (1 : I))⟩ :
          WeaklyPointed (0 : I) (1 : I))).eval t).map f.rootPath.continuous).cast
            f.rootPath.target.symm f.rootPath.target.symm :=
  originalLoopMapUnitHomotopyTemplateComputed f t

end ContinuousMap.WeaklyPointed

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X] {x y : X}

private theorem originalConjugationMultiplicationUnitTemplateComputed
    (p : Path x y) (t : I) :
    loopBasepointChangeMultiplicationHomotopy p (t, (Path.refl x, Path.refl x)) =
      ((loopBasepointChangeMultiplicationHomotopy
        (Path.id : Path (0 : I) (1 : I))
          (t, (Path.refl (0 : I), Path.refl (0 : I)))).map p.continuous).cast
            p.target.symm p.target.symm := by
  let q : Path (0 : I) (1 : I) := Path.id
  let eX : LoopSpace X x := Path.refl x
  let eI : LoopSpace I (0 : I) := Path.refl 0
  let BX := LoopSpace X x × LoopSpace X x
  let BI := LoopSpace I (0 : I) × LoopSpace I (0 : I)
  let W : LoopSpace I (1 : I) → LoopSpace X y := fun gamma =>
    (gamma.map p.continuous).cast p.target.symm p.target.symm
  have hIfPoint (c : Prop) (dc : Decidable c)
      (a : c → X) (b : ¬c → X) (ai : c → I) (bi : ¬c → I)
      (ha : ∀ h, a h = p (ai h)) (hb : ∀ h, b h = p (bi h)) :
      @dite X c dc a b = p (@dite I c dc ai bi) := by
    cases dc with
    | isTrue hc => exact ha hc
    | isFalse hc => exact hb hc
  have hIfLoop (c : Prop) (dc : Decidable c)
      (a : c → LoopSpace X y) (b : ¬c → LoopSpace X y)
      (ai : c → LoopSpace I (1 : I)) (bi : ¬c → LoopSpace I (1 : I))
      (ha : ∀ h, a h = W (ai h)) (hb : ∀ h, b h = W (bi h)) :
      @dite (LoopSpace X y) c dc a b = W (@dite (LoopSpace I (1 : I)) c dc ai bi) := by
    cases dc with
    | isTrue hc => exact ha hc
    | isFalse hc => exact hb hc
  have hTrans {a b c : I} {a' b' c' : X}
      (l : Path a' b') (m : Path b' c') (li : Path a b) (mi : Path b c)
      (hl : ∀ s, l s = p (li s)) (hm : ∀ s, m s = p (mi s)) (s : I) :
      (l.trans m) s = p ((li.trans mi) s) := by
    rw [Path.trans_apply, Path.trans_apply]
    apply hIfPoint _ (inferInstance) _ _ _ _
    · intro hs
      exact hl _
    · intro hs
      exact hm _
  have hAssoc {a b c d : I} {a' b' c' d' : X}
      (l : Path a' b') (m : Path b' c') (n : Path c' d')
      (li : Path a b) (mi : Path b c) (ni : Path c d)
      (hl : ∀ s, l s = p (li s)) (hm : ∀ s, m s = p (mi s))
      (hn : ∀ s, n s = p (ni s)) (r s : I) :
      pathTripleAssocHomotopy a' b' c' d' (r, ((l, m), n)) s =
        p (pathTripleAssocHomotopy a b c d (r, ((li, mi), ni)) s) := by
    rw [pathTripleAssocHomotopy_apply, pathTripleAssocHomotopy_apply]
    exact hTrans l (m.trans n) li (mi.trans ni) hl
      (fun s => hTrans m n mi ni hm hn s) _
  have hP (s : I) : p s = p (q s) := rfl
  have hSymm (s : I) : p.symm s = p (q.symm s) := rfl
  have hUnit (s : I) : eX s = p (eI s) := p.source.symm
  have hTail (s : I) : (eX.trans p) s = p ((eI.trans q) s) :=
    hTrans eX p eI q hUnit hP s
  have hSymmTail (s : I) : (p.symm.trans (eX.trans p)) s =
      p ((q.symm.trans (eI.trans q)) s) :=
    hTrans p.symm (eX.trans p) q.symm (eI.trans q) hSymm hTail s
  have hPrependCast {a b a' b' : X} (r : Path a b)
      (ha : a' = a) (hb : b' = b) (v : I) :
      pathPrependReflHomotopy a' b' (v, r.cast ha hb) =
        (pathPrependReflHomotopy a b (v, r)).cast ha hb := by
    cases ha
    cases hb
    rfl
  have hPrepend (r s : I) :
      pathPrependReflHomotopy x y (r, eX.trans p) s =
        p (pathPrependReflHomotopy (0 : I) (1 : I) (r, eI.trans q) s) := by
    have hTailEq : ((eI.trans q).map p.continuous).cast
        p.source.symm p.target.symm = eX.trans p := by
      apply Path.ext
      funext s
      exact (hTail s).symm
    have hInput := congrArg (fun gamma : Path x y =>
      pathPrependReflHomotopy x y (r, gamma)) hTailEq
    have hCast := hPrependCast ((eI.trans q).map p.continuous)
      p.source.symm p.target.symm r
    have hMap := pathPrependReflHomotopy_map p.toContinuousMap (eI.trans q) r
    have hValue : pathPrependReflHomotopy x y (r, eX.trans p) =
        ((pathPrependReflHomotopy (0 : I) (1 : I) (r, eI.trans q)).map
          p.continuous).cast p.source.symm p.target.symm :=
      hInput.symm.trans (hCast.trans
        (congrArg (fun gamma : Path (p (0 : I)) (p (1 : I)) =>
          gamma.cast p.source.symm p.target.symm) hMap).symm)
    exact congrArg (fun gamma : Path x y => gamma s) hValue
  have hTransValue
      {f₀ f₁ f₂ : C(BX, LoopSpace X y)}
      {g₀ g₁ g₂ : C(BI, LoopSpace I (1 : I))}
      (H : Homotopy f₀ f₁) (K : Homotopy f₁ f₂)
      (HI : Homotopy g₀ g₁) (KI : Homotopy g₁ g₂)
      (hH : ∀ r, H (r, (eX, eX)) = W (HI (r, (eI, eI))))
      (hK : ∀ r, K (r, (eX, eX)) = W (KI (r, (eI, eI)))) (r : I) :
      (H.trans K) (r, (eX, eX)) = W ((HI.trans KI) (r, (eI, eI))) := by
    rw [Homotopy.trans_apply, Homotopy.trans_apply]
    apply hIfLoop _ (inferInstance) _ _ _ _
    · intro hr
      exact hH _
    · intro hr
      exact hK _
  change loopBasepointChangeMultiplicationHomotopy p (t, (eX, eX)) =
    W (loopBasepointChangeMultiplicationHomotopy q (t, (eI, eI)))
  unfold loopBasepointChangeMultiplicationHomotopy originalConjugationMultiplicationComputed
  rw [Homotopy.symm_apply, Homotopy.symm_apply]
  refine hTransValue _ _ _ _ ?_ ?_ _
  · intro r
    apply Path.ext
    funext s
    change pathTripleAssocHomotopy y x y y
      (r, ((p.symm, eX.trans p), p.symm.trans (eX.trans p))) s =
        p (pathTripleAssocHomotopy (1 : I) (0 : I) (1 : I) (1 : I)
          (r, ((q.symm, eI.trans q), q.symm.trans (eI.trans q))) s)
    exact hAssoc p.symm (eX.trans p) (p.symm.trans (eX.trans p))
      q.symm (eI.trans q) (q.symm.trans (eI.trans q)) hSymm hTail hSymmTail r s
  · intro r
    refine hTransValue _ _ _ _ ?_ ?_ r
    · intro r
      apply Path.ext
      funext s
      change (p.symm.trans (pathTripleAssocHomotopy x x y y
        (r, ((eX, p), p.symm.trans (eX.trans p))))) s =
          p ((q.symm.trans (pathTripleAssocHomotopy (0 : I) (0 : I) (1 : I) (1 : I)
            (r, ((eI, q), q.symm.trans (eI.trans q))))) s)
      exact hTrans p.symm _ q.symm _ hSymm
        (fun s => hAssoc eX p (p.symm.trans (eX.trans p))
          eI q (q.symm.trans (eI.trans q)) hUnit hP hSymmTail r s) s
    · intro r
      refine hTransValue _ _ _ _ ?_ ?_ r
      · intro r
        apply Path.ext
        funext s
        change (p.symm.trans (eX.trans (pathTripleAssocHomotopy x y x y
          (unitInterval.symm r, ((p, p.symm), eX.trans p))))) s =
            p ((q.symm.trans (eI.trans (pathTripleAssocHomotopy
              (0 : I) (1 : I) (0 : I) (1 : I)
                (unitInterval.symm r, ((q, q.symm), eI.trans q))))) s)
        exact hTrans p.symm _ q.symm _ hSymm
          (fun s => hTrans eX _ eI _ hUnit
            (fun s => hAssoc p p.symm (eX.trans p) q q.symm (eI.trans q)
              hP hSymm hTail (unitInterval.symm r) s) s) s
      · intro r
        refine hTransValue _ _ _ _ ?_ ?_ r
        · intro r
          apply Path.ext
          funext s
          change (p.symm.trans (eX.trans
            (((Path.Homotopy.reflTransSymm p).symm.eval r).trans (eX.trans p)))) s =
              p ((q.symm.trans (eI.trans
                (((Path.Homotopy.reflTransSymm q).symm.eval r).trans (eI.trans q)))) s)
          exact hTrans p.symm _ q.symm _ hSymm
            (fun s => hTrans eX _ eI _ hUnit
              (fun s => hTrans ((Path.Homotopy.reflTransSymm p).symm.eval r)
                (eX.trans p) ((Path.Homotopy.reflTransSymm q).symm.eval r)
                  (eI.trans q) (fun s => rfl) hTail s) s) s
        · intro r
          refine hTransValue _ _ _ _ ?_ ?_ r
          · intro r
            apply Path.ext
            funext s
            change (p.symm.trans (eX.trans
              (pathPrependReflHomotopy x y (r, eX.trans p)))) s =
                p ((q.symm.trans (eI.trans
                  (pathPrependReflHomotopy (0 : I) (1 : I) (r, eI.trans q)))) s)
            exact hTrans p.symm _ q.symm _ hSymm
              (fun s => hTrans eX _ eI _ hUnit (hPrepend r) s) s
          · intro r
            apply Path.ext
            funext s
            change (p.symm.trans (pathTripleAssocHomotopy x x x y
              (unitInterval.symm r, ((eX, eX), p)))) s =
                p ((q.symm.trans (pathTripleAssocHomotopy
                  (0 : I) (0 : I) (0 : I) (1 : I)
                    (unitInterval.symm r, ((eI, eI), q)))) s)
            exact hTrans p.symm _ q.symm _ hSymm
              (fun s => hAssoc eX eX p eI eI q hUnit hUnit hP
                (unitInterval.symm r) s) s

/-- ALL original multiplication times at the original unit pair use the
SAME six-stage universal interval family, mapped along the SAME chosen root.
Every association, reversed clock, root-pair contraction and target cast remains. -/
public theorem loopBasepointChangeMultiplicationHomotopy_unit_template
    (p : Path x y) (t : I) :
    loopBasepointChangeMultiplicationHomotopy p (t, (Path.refl x, Path.refl x)) =
      ((loopBasepointChangeMultiplicationHomotopy
        (Path.id : Path (0 : I) (1 : I))
          (t, (Path.refl (0 : I), Path.refl (0 : I)))).map p.continuous).cast
            p.target.symm p.target.symm :=
  originalConjugationMultiplicationUnitTemplateComputed p t

end ContinuousMap

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

private theorem originalWeakLoopMultiplicationUnitValueComputed
    (f : WeaklyPointed x y) (t : I) :
    loopMapMultiplicationHomotopy f (t, (Path.refl x, Path.refl x)) =
      loopBasepointChangeMultiplicationHomotopy f.rootPath
        (t, (Path.refl (f.hom x), Path.refl (f.hom x))) := by
  let M := strictLoopMap f.hom x
  let K := (loopBasepointChangeMultiplicationHomotopy f.rootPath).compContinuousMap
    (M.prodMap M)
  have hValue : loopMapMultiplicationHomotopy f (t, (Path.refl x, Path.refl x)) =
      K (t, (Path.refl x, Path.refl x)) := rfl
  have hUnit : M (Path.refl x) = Path.refl (f.hom x) := strictLoopMap_refl f.hom x
  exact hValue.trans (congrArg (fun pair : LoopSpace Y (f.hom x) × LoopSpace Y (f.hom x) =>
    loopBasepointChangeMultiplicationHomotopy f.rootPath (t, pair)) (Prod.ext hUnit hUnit))

/-- The ACTUAL whole multiplication family at the original source unit pair
is SAME original root-conjugation multiplication family at the strict mapped unit.
Its original root, mapped source and every original clock are retained. -/
public theorem loopMapMultiplicationHomotopy_unit_value (f : WeaklyPointed x y) (t : I) :
    loopMapMultiplicationHomotopy f (t, (Path.refl x, Path.refl x)) =
      loopBasepointChangeMultiplicationHomotopy f.rootPath
        (t, (Path.refl (f.hom x), Path.refl (f.hom x))) :=
  originalWeakLoopMultiplicationUnitValueComputed f t

end ContinuousMap.WeaklyPointed

end
