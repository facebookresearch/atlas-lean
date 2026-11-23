/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorAllKiMap
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorOriginalCompositionUnitTrace
public import MathlibExt.Topology.Homotopy.MixedBasepointChangeNaturality

/-!
# Actual positive Ki composition and natural-isomorphism transport

The original whole composition and isomorphism homotopies have their
designated-unit compatibilities. Their positive group maps therefore obey
the actual functor laws with the same original roots and unit clocks.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Topology

universe uC vC uD vD uE vE uX uY uZ

namespace AlgebraicKTheory

private theorem originalUnitPairSourceCast
    {X : Type uX} [TopologicalSpace X] {a b c d e : X}
    (p : Path a c) (q : Path b c) (ha : d = a) (hb : e = b) :
    (p.cast ha rfl).trans (q.cast hb rfl).symm = (p.trans q.symm).cast ha hb := by
  cases ha
  cases hb
  apply Path.ext
  funext t
  rfl

private theorem originalRootedGroupValue
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (p : Path (f x) y) (q : Path (g x) y)
    (hRoot : ((H.evalAt x).trans q).Homotopic p)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p (HomotopyGroup.map f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q (HomotopyGroup.map g a) :=
  DFunLike.congr_fun (TopCat.homotopyGroup_rooted_map_homotopy_mixed n H p q hRoot) a

private theorem originalRootedCompositionValue
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (n : ℕ) (f : C(X, Y)) (g : C(Y, Z))
    (p : Path (f x) y) (q : Path (g y) z)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z)
        ((p.map g.continuous).trans q) (HomotopyGroup.map (g.comp f) a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) q
        (HomotopyGroup.map g
          (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p (HomotopyGroup.map f a)))
              := by
  have hTrans := DFunLike.congr_fun
    (TopCat.homotopyGroupBasepointChangeMulEquiv_trans n (TopCat.of Z) (p.map g.continuous) q)
    (HomotopyGroup.map (g.comp f) a)
  have hComp := HomotopyGroup.map_comp f g a
  have hNatural := TopCat.homotopyGroupBasepointChangeMulEquiv_naturality_mixed n g p
    (HomotopyGroup.map f a)
  exact hTrans.trans
    ((congrArg (fun b => TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) q
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) (p.map g.continuous) b))
          hComp).trans
        (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Z) q) hNatural.symm))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Every actual current positive Ki function preserves functor composition with original designated
  units. -/
theorem NQKSpaceFunctorKiMap_original_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap (F ⋙ G) (n + 1) a =
      NQKSpaceFunctorKiMap G (n + 1) (NQKSpaceFunctorKiMap F (n + 1) a) := by
  let f := NQKSpaceFunctorMap F
  let g := NQKSpaceFunctorMap G
  let p := NQKSpaceFunctorKiUnitRootPath F
  let q := NQKSpaceFunctorKiUnitRootPath G
  let s := (p.map g.continuous).trans q
  have hWhole := originalRootedGroupValue n (NQKSpaceFunctorOriginalCompHomotopy F G)
    (NQKSpaceFunctorKiUnitRootPath (F ⋙ G)) s
    (NQKSpaceFunctorOriginalCompHomotopy_rooted_units F G) a
  have hComposition := originalRootedCompositionValue n f g p q a
  have hF := NQKSpaceFunctorKiMap_succ_apply F n a
  have hG := NQKSpaceFunctorKiMap_succ_apply G n (NQKSpaceFunctorKiMap F (n + 1) a)
  have hFG := NQKSpaceFunctorKiMap_succ_apply (F ⋙ G) n a
  have hInner := congrArg (fun b : HomotopyGroup.Pi (n + 1) (NQKSpace D)
      (Path.refl (NQReal.basepoint D)) =>
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (NQKSpace E)) q (HomotopyGroup.map g
        b)) hF.symm
  exact hFG.trans (hWhole.trans (hComposition.trans (hInner.trans hG.symm)))

/-- The complete original current positive homomorphism preserves actual functor composition. -/
theorem NQKSpaceFunctorPositiveKiMap_original_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (n : ℕ) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C));
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D));
    letI := NQKSpaceOriginalPositiveGroup E n (Path.refl (NQReal.basepoint E));
    NQKSpaceFunctorPositiveKiMap (F ⋙ G) n =
      (NQKSpaceFunctorPositiveKiMap G n).comp (NQKSpaceFunctorPositiveKiMap F n) := by
  letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
  letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
  letI := NQKSpaceOriginalPositiveGroup E n (Path.refl (NQReal.basepoint E))
  apply MonoidHom.ext
  intro a
  have hF := NQKSpaceFunctorKiMap_succ_eq_positive F n a
  have hG := NQKSpaceFunctorKiMap_succ_eq_positive G n (NQKSpaceFunctorPositiveKiMap F n a)
  have hFG := NQKSpaceFunctorKiMap_succ_eq_positive (F ⋙ G) n a
  exact hFG.symm.trans
    ((NQKSpaceFunctorKiMap_original_comp F G n a).trans
      ((congrArg (NQKSpaceFunctorKiMap G (n + 1)) hF).trans hG))

private theorem originalNatIsoRootedUnits (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (((NQKSpaceFunctorNatIsoHomotopy F G e).evalAt (Path.refl (NQReal.basepoint C))).trans
      (NQKSpaceFunctorKiUnitRootPath G)).Homotopic (NQKSpaceFunctorKiUnitRootPath F) := by
  let U := NQKSpaceFunctorKiUnitRootPath F
  let V := NQKSpaceFunctorKiUnitRootPath G
  have hPair : U.trans V.symm =
      ((((ContinuousMap.rootUnitContraction
        (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
          (NQReal.basepoint D) => p) continuous_eval).evalAt
            (NQRealFunctorWeaklyPointed F).rootPath).trans
              ((ContinuousMap.rootUnitContraction
                (fun p : Path ((NQRealFunctorWeaklyPointed G).hom (NQReal.basepoint C))
                  (NQReal.basepoint D) => p) continuous_eval).evalAt
                    (NQRealFunctorWeaklyPointed G).rootPath).symm).cast
                      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F)
                      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily G)) := by
    let PF := (ContinuousMap.rootUnitContraction
      (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
        (NQReal.basepoint D) => p) continuous_eval).evalAt
          (NQRealFunctorWeaklyPointed F).rootPath
    let PG := (ContinuousMap.rootUnitContraction
      (fun p : Path ((NQRealFunctorWeaklyPointed G).hom (NQReal.basepoint C))
        (NQReal.basepoint D) => p) continuous_eval).evalAt
          (NQRealFunctorWeaklyPointed G).rootPath
    let hF := NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F
    let hG := NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily G
    have hU : U = PF.cast hF rfl :=
      NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction F
    have hV : V = PG.cast hG rfl :=
      NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction G
    have hPairValue := congrArg₂
      (fun (p : Path (X := NQKSpace D)
          ((NQKSpaceFunctorMap F) (Path.refl (NQReal.basepoint C)))
          (Path.refl (NQReal.basepoint D)))
        (q : Path (X := NQKSpace D)
          ((NQKSpaceFunctorMap G) (Path.refl (NQReal.basepoint C)))
          (Path.refl (NQReal.basepoint D))) => p.trans q.symm) hU hV
    exact hPairValue.trans (originalUnitPairSourceCast PF PG hF hG)
  have hTrace : (NQKSpaceFunctorNatIsoUnitPath F G e).Homotopic (U.trans V.symm) := by
    obtain ⟨H⟩ := NQKSpaceFunctorNatIsoUnitPath_homotopic_rootUnits F G e
    exact ⟨H.cast rfl hPair.symm⟩
  have hRoot := (hTrace.hcomp (Path.Homotopic.refl V)).trans
    ((Path.Homotopic.trans_assoc U V.symm V).trans
      (((Path.Homotopic.refl U).hcomp (Path.Homotopic.symm_trans V)).trans
        (Path.Homotopic.trans_refl U)))
  have hActual : NQKSpaceFunctorNatIsoUnitPath F G e =
      (NQKSpaceFunctorNatIsoHomotopy F G e).evalAt (Path.refl (NQReal.basepoint C)) := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact NQKSpaceFunctorNatIsoUnitPath_apply F G e t s
  obtain ⟨H⟩ := hRoot
  exact ⟨H.cast (congrArg (fun p => p.trans V) hActual) rfl⟩

/-- Actual current positive Ki maps agree along an actual natural isomorphism. -/
theorem NQKSpaceFunctorKiMap_original_natIso (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F (n + 1) a = NQKSpaceFunctorKiMap G (n + 1) a := by
  have hActual := originalRootedGroupValue n (NQKSpaceFunctorNatIsoHomotopy F G e)
    (NQKSpaceFunctorKiUnitRootPath F) (NQKSpaceFunctorKiUnitRootPath G)
    (originalNatIsoRootedUnits F G e) a
  exact (NQKSpaceFunctorKiMap_succ_apply F n a).trans
    (hActual.trans (NQKSpaceFunctorKiMap_succ_apply G n a).symm)

/-- The entire current positive homomorphism is transported by the actual original NatIso family. -/
theorem NQKSpaceFunctorPositiveKiMap_original_natIso (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) (n : ℕ) :
    letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C));
    letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D));
    NQKSpaceFunctorPositiveKiMap F n = NQKSpaceFunctorPositiveKiMap G n := by
  letI := NQKSpaceOriginalPositiveGroup C n (Path.refl (NQReal.basepoint C))
  letI := NQKSpaceOriginalPositiveGroup D n (Path.refl (NQReal.basepoint D))
  apply MonoidHom.ext
  intro a
  exact (NQKSpaceFunctorKiMap_succ_eq_positive F n a).symm.trans
    ((NQKSpaceFunctorKiMap_original_natIso F G e n a).trans
      (NQKSpaceFunctorKiMap_succ_eq_positive G n a))

end AlgebraicKTheory

end
