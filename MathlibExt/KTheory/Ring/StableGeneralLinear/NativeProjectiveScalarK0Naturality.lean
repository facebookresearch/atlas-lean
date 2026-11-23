/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension
public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeProjectiveZeroScalarMap
public import MathlibExt.KTheory.Exact.Extension.CompletedCoreK0Naturality
public import MathlibExt.KTheory.Exact.K0.Functor
public import MathlibExt.KTheory.Ring.K0.ProjectiveUniverseEquivalence

/-!
# The original scalar functor and K0 on every projective component

The same intrinsic projective functor is compared with the actual
ringScalarExtension through the original target universe counit.
The source and target rings and module universes remain independent.
The actual completed-Core map and canonical component dictionary are used
on every component and every pair, with their original positive-first sign.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal CategoryTheory.MonoidalCategory

attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.StableGL

private def originalProjectiveScalarK0FunctorIsoComputed.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uMS} S).functor ≅
      (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor ⋙
        FGProjectiveCat.ringScalarExtension.{uR, uS} f := by
  let U := (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor
  let A := FGProjectiveCat.scalarExtension.{uR, uS, uR} f
  let B := (FGProjectiveCat.universeEquivalence.{uS, uR} S).functor
  let E := FGProjectiveCat.universeEquivalence.{uS, uMS} S
  exact Functor.associator U (A ⋙ (B ⋙ E.inverse)) E.functor ≪≫
    Functor.isoWhiskerLeft U (Functor.associator A (B ⋙ E.inverse) E.functor) ≪≫
      Functor.isoWhiskerLeft U
        (Functor.isoWhiskerLeft A (Functor.associator B E.inverse E.functor)) ≪≫
          Functor.isoWhiskerLeft U
            (Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft B E.counitIso)) ≪≫
              Functor.isoWhiskerLeft U (Functor.isoWhiskerLeft A (Functor.rightUnitor B))

/-- The SAME original intrinsic functor followed by target shrinking is naturally
    isomorphic to source shrinking followed by the actual ring scalar functor. -/
public def nativeProjectiveScalarOriginalK0FunctorIso.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uMS} S).functor ≅
      (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor ⋙
        FGProjectiveCat.ringScalarExtension.{uR, uS} f :=
  originalProjectiveScalarK0FunctorIsoComputed.{uR, uS, uMR, uMS} f

private theorem originalRingScalarK0MapValue.{uR, uS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    K0.map (FGProjectiveCat.ringScalarExtension.{uR, uS} f) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f := by
  apply K0.hom_ext
  intro M
  exact (K0.map_mk (FGProjectiveCat.ringScalarExtension.{uR, uS} f) M).trans
    (FGProjectiveCat.scalarExtensionK0_mk.{uR, uS} f M).symm

private theorem originalProjectiveUniverseK0MapValue.{uRing, uModule}
    (R : Type uRing) [Ring R] :
    (RingK0.projectiveUniverseEquiv.{uRing, uModule} R).toAddMonoidHom =
      K0.map (FGProjectiveCat.universeEquivalence.{uRing, uModule} R).functor := by
  rfl

/-- The actual K0 map equality uses the two independently sized intermediate
    categories, with no caller-provided natural Iso or equality premise. -/
public theorem nativeProjectiveScalarOriginalK0MapComposition.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (K0.map (FGProjectiveCat.universeEquivalence.{uS, uMS} S).functor).comp
        (K0.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) =
      (FGProjectiveCat.scalarExtensionK0.{uR, uS} f).comp
        (K0.map (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor) := by
  have h := K0.map_comp_eq_comp_of_iso
    (F₁ := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
    (G₁ := (FGProjectiveCat.universeEquivalence.{uS, uMS} S).functor)
    (F₂ := (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor)
    (G₂ := FGProjectiveCat.ringScalarExtension.{uR, uS} f)
    (nativeProjectiveScalarOriginalK0FunctorIso.{uR, uS, uMR, uMS} f)
  exact h.trans (congrArg (fun k : RingK0 R →+ RingK0 S =>
    k.comp (K0.map (FGProjectiveCat.universeEquivalence.{uR, uMR} R).functor))
      (originalRingScalarK0MapValue.{uR, uS} f))

/-- The existing fixed RingK0 dictionaries commute with the SAME intrinsic
    functor on the entire exact K0 group, in all four independent universes. -/
public theorem nativeProjectiveScalarOriginalK0MapChart.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (RingK0.projectiveUniverseEquiv.{uS, uMS} S).toAddMonoidHom.comp
        (K0.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)) =
      (FGProjectiveCat.scalarExtensionK0.{uR, uS} f).comp
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R).toAddMonoidHom := by
  have hTarget := congrArg
    (fun k : K0 (FGProjectiveCat.{max uS uMS} S) →+ RingK0 S =>
      k.comp (K0.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)))
    (originalProjectiveUniverseK0MapValue.{uS, uMS} S)
  have hSource := congrArg
    (fun k : K0 (FGProjectiveCat.{max uR uMR} R) →+ RingK0 R =>
      (FGProjectiveCat.scalarExtensionK0.{uR, uS} f).comp k)
    (originalProjectiveUniverseK0MapValue.{uR, uMR} R).symm
  exact hTarget.trans
    ((nativeProjectiveScalarOriginalK0MapComposition.{uR, uS, uMR, uMS} f).trans hSource)

/-- Every original finite projective object retains its actual coefficient
    class; no free-rank, IBN, nonzero-ring or zero-component restriction is used. -/
public theorem nativeProjectiveScalarOriginalK0Generator.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (M : FGProjectiveCat.{max uR uMR} R) :
    RingK0.projectiveUniverseEquiv.{uS, uMS} S
        (K0.mk ((nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f).obj M)) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R (K0.mk M)) := by
  have h := congrArg
    (fun k : K0 (FGProjectiveCat.{max uR uMR} R) →+ RingK0 S => k (K0.mk M))
    (nativeProjectiveScalarOriginalK0MapChart.{uR, uS, uMR, uMS} f)
  exact (congrArg (RingK0.projectiveUniverseEquiv.{uS, uMS} S)
    (K0.map_mk (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) M)).symm.trans h

private theorem originalProjectivePairK0DictionaryValue.{uRing, uModule}
    (R : Type uRing) [Ring R] (X : SInverseS.Pair (FGProjectiveCat.{max uRing uModule} R)) :
    RingK0.sInverseSComponentsUniverseEquiv.{uRing, uModule} R
        (CategoryTheory.ConnectedComponents.mk X) =
      RingK0.projectiveUniverseEquiv.{uRing, uModule} R (K0.mk X.fst - K0.mk X.snd) := by
  rw [RingK0.sInverseSComponentsUniverseEquiv_mk, map_sub,
    RingK0.projectiveUniverseEquiv_mk, RingK0.projectiveUniverseEquiv_mk]

/-- EVERY original categorical Pair class is mapped by the actual Pair functor
    and the existing positive-first fixed RingK0 component dictionary. -/
public theorem nativeProjectiveScalarOriginalPairK0Naturality.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (X : SInverseS.Pair (FGProjectiveCat.{max uR uMR} R)) :
    RingK0.sInverseSComponentsUniverseEquiv.{uS, uMS} S
        (CategoryTheory.ConnectedComponents.mk
          ((SInverseS.pairFunctor (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)).obj
            X)) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.sInverseSComponentsUniverseEquiv.{uR, uMR} R
          (CategoryTheory.ConnectedComponents.mk X)) := by
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let Y := (SInverseS.pairFunctor F).obj X
  have hObject : Y = (⟨F.obj X.fst, F.obj X.snd⟩ :
      SInverseS.Pair (FGProjectiveCat.{max uS uMS} S)) :=
    (SInverseS.pairFunctor_characteristic F F (Iso.refl F)
      (𝟭 (FGProjectiveCat.{max uS uMS} S))).1 X
  have hFirst : Y.fst = F.obj X.fst := congrArg SInverseS.Pair.fst hObject
  have hSecond : Y.snd = F.obj X.snd := congrArg SInverseS.Pair.snd hObject
  have hMapped : K0.map F (K0.mk X.fst - K0.mk X.snd) =
      K0.mk (F.obj X.fst) - K0.mk (F.obj X.snd) := by
    rw [map_sub, K0.map_mk, K0.map_mk]
  have hCoordinates : K0.mk Y.fst - K0.mk Y.snd =
      K0.map F (K0.mk X.fst - K0.mk X.snd) :=
    (congrArg₂ (fun M N : FGProjectiveCat.{max uS uMS} S => K0.mk M - K0.mk N)
      hFirst hSecond).trans hMapped.symm
  have hChart := congrArg
    (fun k : K0 (FGProjectiveCat.{max uR uMR} R) →+ RingK0 S =>
      k (K0.mk X.fst - K0.mk X.snd))
    (nativeProjectiveScalarOriginalK0MapChart.{uR, uS, uMR, uMS} f)
  exact (originalProjectivePairK0DictionaryValue.{uS, uMS} S Y).trans
    ((congrArg (RingK0.projectiveUniverseEquiv.{uS, uMS} S) hCoordinates).trans
      (hChart.trans (congrArg (FGProjectiveCat.scalarExtensionK0.{uR, uS} f)
        (originalProjectivePairK0DictionaryValue.{uR, uMR} R X).symm)))

/-- The SAME actual completed-Core component map commutes with the canonical
    fixed RingK0 dictionary on EVERY completed component. -/
public theorem nativeProjectiveScalarOriginalCompletedCoreK0Naturality.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace
      (C := FGProjectiveCat.{max uR uMR} R))) :
    RingK0.projectiveUniverseEquiv.{uS, uMS} S
        (OriginalQK0Comparison.canonicalCoreComponentsK0
          (C := FGProjectiveCat.{max uS uMS} S)
          (OriginalQK0Comparison.completedCoreComponentsMap
            (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) c)) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R
          (OriginalQK0Comparison.canonicalCoreComponentsK0
            (C := FGProjectiveCat.{max uR uMR} R) c)) := by
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  have h := OriginalQK0Comparison.canonicalCoreComponentsK0_naturality F c
  have hChart := congrArg
    (fun k : K0 (FGProjectiveCat.{max uR uMR} R) →+ RingK0 S =>
      k (OriginalQK0Comparison.canonicalCoreComponentsK0
        (C := FGProjectiveCat.{max uR uMR} R) c))
    (nativeProjectiveScalarOriginalK0MapChart.{uR, uS, uMR, uMS} f)
  exact (congrArg (RingK0.projectiveUniverseEquiv.{uS, uMS} S) h).trans hChart

/-- EVERY completed pair retains its original numerator-minus-denominator
    value after the SAME actual completed-Core scalar map. -/
public theorem nativeProjectiveScalarOriginalCompletedPairK0Naturality.{uR, uS, uMR, uMS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (a : SInverse (Core (FGProjectiveCat.{max uR uMR} R))
      (Core (FGProjectiveCat.{max uR uMR} R))) :
    RingK0.projectiveUniverseEquiv.{uS, uMS} S
        (OriginalQK0Comparison.canonicalCoreComponentsK0
          (C := FGProjectiveCat.{max uS uMS} S)
          (OriginalQK0Comparison.completedCoreComponentsMap
            (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
            (ZerothHomotopy.mk (SSet.realizedVertex
              (X := (nerve (SInverse (Core (FGProjectiveCat.{max uR uMR} R))
                (Core (FGProjectiveCat.{max uR uMR} R))) : SSet.{(max uR uMR) + 1}))
              (ComposableArrows.mk₀ a))))) =
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R
          (K0.mk a.of.1.of - K0.mk a.of.2.of)) := by
  have h := nativeProjectiveScalarOriginalCompletedCoreK0Naturality.{uR, uS, uMR, uMS} f
    (ZerothHomotopy.mk (SSet.realizedVertex
      (X := (nerve (SInverse (Core (FGProjectiveCat.{max uR uMR} R))
        (Core (FGProjectiveCat.{max uR uMR} R))) : SSet.{(max uR uMR) + 1}))
      (ComposableArrows.mk₀ a)))
  exact h.trans (congrArg
    (fun k : K0 (FGProjectiveCat.{max uR uMR} R) =>
      FGProjectiveCat.scalarExtensionK0.{uR, uS} f
        (RingK0.projectiveUniverseEquiv.{uR, uMR} R k))
    (OriginalQK0Comparison.canonicalCoreComponentsK0_mk
      (C := FGProjectiveCat.{max uR uMR} R) a))

end AlgebraicKTheory.StableGL

end
