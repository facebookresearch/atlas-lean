/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalQK0ComparisonCompatibility
public import MathlibExt.KTheory.Exact.K0.Equivalence
public import MathlibExt.Algebra.Category.FGProjectiveCat.CategoryUniverseLift
public import MathlibExt.KTheory.Ring.K0.ProjectiveUniverseEquivalence
public import MathlibExt.KTheory.Exact.Quillen.UniverseLift

/-!
# The original Q evaluator across category universes

The component evaluator remains the existing original Q/S evaluator. Its
actual fundamental-group homomorphism is an equivalence because the original
Q/S component map and exact/Waldhausen dictionary are equivalences. This
allows compatibility of an actual cross-universe Q map to be proved on the
original zero-mono/zero-epi generator loops, using exact K0 functoriality.
No final Q=plus homotopy equivalence enters the evaluator.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicKTheory.OriginalQK0Comparison

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility

attribute [local instance] ExactCategory.waldhausenCategory

private def loopComponentsCastEquiv {X : Type*} [TopologicalSpace X]
    {x y : X} (h : x = y) :
    ZerothHomotopy (LoopSpace X x) ≃ ZerothHomotopy (LoopSpace X y) := by
  cases h
  exact Equiv.refl _

private theorem loopComponentsCastEquivMk {X : Type*} [TopologicalSpace X]
    {x y : X} (h : x = y) (p : LoopSpace X x) :
    loopComponentsCastEquiv h (ZerothHomotopy.mk p) =
      ZerothHomotopy.mk (p.cast h.symm h.symm) := by
  cases h
  rfl

section OriginalEvaluator

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The existing canonical evaluator, with only the specified zero-point
equality promoted to an equivalence of loop components. -/
def originalComponentsEquivK0 (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C)) ≃ K0 C :=
  (loopComponentsCastEquiv
      ((NQReal.basepoint_eq_realizedVertex C).symm)).trans
    ((NQKSpacePiZeroEquivK0 C).trans
      (WaldhausenKTheory.K0.exactIso C).addCommGroupIsoToAddEquiv.toEquiv)

/-- This equivalence has exactly the original evaluator's value on every
component, including components represented by non-generator loops. -/
theorem originalComponentsEquivK0_apply
    (c : ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C))) :
    originalComponentsEquivK0 C c = canonicalLoopComponentsK0 (C := C) c := by
  induction c using ZerothHomotopy.rec with
  | mk p =>
      let p0 : LoopSpace (NQReal C) (SSet.realizedVertex (NQ.zeroVertex C)) := p
      let h : SSet.realizedVertex (NQ.zeroVertex C) = NQReal.basepoint C :=
        (NQReal.basepoint_eq_realizedVertex C).symm
      have hCast : loopComponentsCastEquiv h (ZerothHomotopy.mk p0) =
          ZerothHomotopy.mk (p0.cast h.symm h.symm) :=
        loopComponentsCastEquivMk h p0
      have hValue :
          WaldhausenKTheory.K0.toExact C
            (NQKSpacePiZeroEquivK0 C (loopComponentsCastEquiv h (ZerothHomotopy.mk p0))) =
        WaldhausenKTheory.K0.toExact C
          (NQKSpacePiZeroEquivK0 C (ZerothHomotopy.mk (p0.cast h.symm h.symm))) :=
        congrArg (fun z : ZerothHomotopy (NQKSpace C) =>
          WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C z)) hCast
      have hOriginal : originalComponentsEquivK0 C (ZerothHomotopy.mk p) =
          WaldhausenKTheory.K0.toExact C
            (NQKSpacePiZeroEquivK0 C
              (loopComponentsCastEquiv h (ZerothHomotopy.mk p0))) := rfl
      have hCanonical : canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p) =
          WaldhausenKTheory.K0.toExact C
            (NQKSpacePiZeroEquivK0 C
              (ZerothHomotopy.mk (p0.cast h.symm h.symm))) :=
        canonicalLoopComponentsK0_mk (C := C) p
      exact hOriginal.trans (hValue.trans hCanonical.symm)

/-- All exact K0 classes occur under the original Q/S component evaluator. -/
theorem canonicalLoopComponentsK0_bijective :
    Function.Bijective (canonicalLoopComponentsK0 (C := C)) := by
  have h : (originalComponentsEquivK0 C :
      ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C)) → K0 C) =
      canonicalLoopComponentsK0 (C := C) :=
    funext (originalComponentsEquivK0_apply (C := C))
  rw [← h]
  exact (originalComponentsEquivK0 C).bijective

private abbrev originalFundamentalGroup (C : Type uC) [Category.{vC} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :=
  FundamentalGroup (SSet.toTop.obj (NQ C))
    (OriginalQZeroComparison.zeroQVertex (C := C))

private def originalFundamentalValue (g : originalFundamentalGroup C) :
    Multiplicative (K0 C) :=
  Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C)
    ((loopComponentsEquivFundamentalGroup (SSet.toTop.obj (NQ C))
      (OriginalQZeroComparison.zeroQVertex (C := C))).symm g))

private theorem originalFundamentalValueMk
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    originalFundamentalValue (C := C)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p)) := by
  change Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C)
    ((loopComponentsEquivFundamentalGroup (SSet.toTop.obj (NQ C))
      (OriginalQZeroComparison.zeroQVertex (C := C))).symm
        ((loopComponentsEquivFundamentalGroup (SSet.toTop.obj (NQ C))
          (OriginalQZeroComparison.zeroQVertex (C := C))) (ZerothHomotopy.mk p)))) = _
  rw [Equiv.symm_apply_apply]

private def originalFundamentalHom :
    originalFundamentalGroup C →* Multiplicative (K0 C) where
  toFun := originalFundamentalValue (C := C)
  map_one' := by
    change originalFundamentalValue (C := C)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (Path.refl (OriginalQZeroComparison.zeroQVertex (C := C))))) = 1
    rw [originalFundamentalValueMk, canonicalLoopComponentsK0_refl]
    rfl
  map_mul' g h := by
    rcases g with ⟨g⟩
    rcases h with ⟨h⟩
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    have hm : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.trans p)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) := by
      apply CategoryTheory.End.ext
      exact Path.Homotopic.Quotient.mk_trans q p
    rw [← hm, originalFundamentalValueMk, originalFundamentalValueMk,
      originalFundamentalValueMk, canonicalLoopComponentsK0_trans]
    change Multiplicative.ofAdd
        (canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk q) +
          canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p)) =
      Multiplicative.ofAdd
        (canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p) +
          canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk q))
    exact congrArg Multiplicative.ofAdd (add_comm _ _)

private def originalFundamentalEquiv :
    originalFundamentalGroup C ≃* Multiplicative (K0 C) :=
  MulEquiv.ofBijective (originalFundamentalHom (C := C)) (by
    have hTag : Function.Bijective (Multiplicative.ofAdd : K0 C → Multiplicative (K0 C)) :=
      ⟨fun _ _ h => congrArg Multiplicative.toAdd h,
        fun x => ⟨x.toAdd, rfl⟩⟩
    exact hTag.comp ((canonicalLoopComponentsK0_bijective (C := C)).comp
      (loopComponentsEquivFundamentalGroup (SSet.toTop.obj (NQ C))
        (OriginalQZeroComparison.zeroQVertex (C := C))).symm.bijective))

private theorem originalFundamentalEquivMk
    (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    originalFundamentalEquiv (C := C)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C) (ZerothHomotopy.mk p)) :=
  originalFundamentalValueMk (C := C) p

private theorem originalFundamentalEquivGenerator (A : C) :
    originalFundamentalEquiv (C := C)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (generatorLoop (C := C) A))) =
      Multiplicative.ofAdd (K0.mk A) :=
  (originalFundamentalEquivMk (C := C) (generatorLoop (C := C) A)).trans
    (congrArg Multiplicative.ofAdd (generatorLoop_canonical (C := C) A))

end OriginalEvaluator

section GeneratorNaturality

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

private def transportedK0Hom
    (f : ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := D))) : K0 C →+ K0 D where
  toFun x := Multiplicative.toAdd
    (originalFundamentalEquiv (C := D)
      (basedFundamentalGroupMap f.hom f.rootPath
        ((originalFundamentalEquiv (C := C)).symm (Multiplicative.ofAdd x))))
  map_zero' := by
    change Multiplicative.toAdd
      (originalFundamentalEquiv (C := D)
        (basedFundamentalGroupMap f.hom f.rootPath
          ((originalFundamentalEquiv (C := C)).symm 1))) = 0
    rw [map_one, map_one, map_one]
    rfl
  map_add' x y := by
    change Multiplicative.toAdd
      (originalFundamentalEquiv (C := D)
        (basedFundamentalGroupMap f.hom f.rootPath
          ((originalFundamentalEquiv (C := C)).symm
            (Multiplicative.ofAdd x * Multiplicative.ofAdd y)))) = _
    rw [(originalFundamentalEquiv (C := C)).symm.map_mul,
      (basedFundamentalGroupMap f.hom f.rootPath).map_mul,
      (originalFundamentalEquiv (C := D)).map_mul]
    rfl

private theorem transportedK0HomGenerator
    (F : C ⥤ D)
    (f : ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := D)))
    (hGenerators : ∀ A : C,
      (f.loopMap (generatorLoop (C := C) A)).Homotopic
        (generatorLoop (C := D) (F.obj A))) (A : C) :
    transportedK0Hom f (K0.mk A) = K0.mk (F.obj A) := by
  change Multiplicative.toAdd
    (originalFundamentalEquiv (C := D)
      (basedFundamentalGroupMap f.hom f.rootPath
        ((originalFundamentalEquiv (C := C)).symm
          (Multiplicative.ofAdd (K0.mk A))))) = _
  rw [← originalFundamentalEquivGenerator (C := C) A,
    (originalFundamentalEquiv (C := C)).symm_apply_apply]
  have hMap : basedFundamentalGroupMap f.hom f.rootPath
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (generatorLoop (C := C) A))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (generatorLoop (C := D) (F.obj A))) :=
    (basedFundamentalGroupMap_mk f.hom f.rootPath (generatorLoop (C := C) A)).trans
      (congrArg FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.eq.mpr (hGenerators A)))
  rw [hMap, originalFundamentalEquivGenerator]
  rfl

private theorem transportedK0HomApply
    (f : ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := D)))
    (c : ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C))) :
    transportedK0Hom f (canonicalLoopComponentsK0 (C := C) c) =
      canonicalLoopComponentsK0 (C := D) (f.loopComponentsMap c) := by
  let eC := loopComponentsEquivFundamentalGroup (SSet.toTop.obj (NQ C))
    (OriginalQZeroComparison.zeroQVertex (C := C))
  have hValue : originalFundamentalEquiv (C := C) (eC c) =
      Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C) c) := by
    change Multiplicative.ofAdd
      (canonicalLoopComponentsK0 (C := C) (eC.symm (eC c))) = _
    rw [eC.symm_apply_apply]
  change Multiplicative.toAdd
    (originalFundamentalEquiv (C := D)
      (basedFundamentalGroupMap f.hom f.rootPath
        ((originalFundamentalEquiv (C := C)).symm
          (Multiplicative.ofAdd (canonicalLoopComponentsK0 (C := C) c))))) = _
  rw [← hValue, (originalFundamentalEquiv (C := C)).symm_apply_apply]
  rfl

private theorem evaluatorNaturalityOfActualGeneratorLoops
    (F : C ⥤ D) [F.Additive] [F.IsExact]
    (f : ContinuousMap.WeaklyPointed
      (OriginalQZeroComparison.zeroQVertex (C := C))
      (OriginalQZeroComparison.zeroQVertex (C := D)))
    (hGenerators : ∀ A : C,
      (f.loopMap (generatorLoop (C := C) A)).Homotopic
        (generatorLoop (C := D) (F.obj A)))
    (c : ZerothHomotopy (BasedSplitExactQLoop.originalQLoops (C := C))) :
    canonicalLoopComponentsK0 (C := D) (f.loopComponentsMap c) =
      K0.map F (canonicalLoopComponentsK0 (C := C) c) := by
  have h : transportedK0Hom f = K0.map F := by
    apply K0.hom_ext
    intro A
    exact (transportedK0HomGenerator F f hGenerators A).trans
      (K0.map_mk F A).symm
  exact (transportedK0HomApply f c).symm.trans
    (congrArg (fun k : K0 C →+ K0 D => k (canonicalLoopComponentsK0 (C := C) c)) h)

end GeneratorNaturality


universe uRing uModule uObject uMorphism

local instance categoryUniverseSymmFunctorAdditive (R : Type uRing) [Ring R] :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uRing, uModule, uObject, uMorphism}
      R).symm.functor.Additive :=
  FGProjectiveCat.CategoryUniverseLift.downFunctorAdditive.{uRing, uModule, uObject, uMorphism}
    R

local instance categoryUniverseSymmInverseAdditive (R : Type uRing) [Ring R] :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uRing, uModule, uObject, uMorphism}
      R).symm.inverse.Additive :=
  FGProjectiveCat.CategoryUniverseLift.upFunctorAdditive.{uRing, uModule, uObject, uMorphism}
    R

local instance categoryUniverseSymmFunctorIsExact (R : Type uRing) [Ring R] :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uRing, uModule, uObject, uMorphism}
      R).symm.functor.IsExact :=
  FGProjectiveCat.CategoryUniverseLift.downFunctorIsExact.{uRing, uModule, uObject, uMorphism}
    R

local instance categoryUniverseSymmInverseIsExact (R : Type uRing) [Ring R] :
    (FGProjectiveCat.CategoryUniverseLift.equivalence.{uRing, uModule, uObject, uMorphism}
      R).symm.inverse.IsExact :=
  FGProjectiveCat.CategoryUniverseLift.upFunctorIsExact.{uRing, uModule, uObject, uMorphism}
    R


section ProjectiveClassDictionary

universe uR uM uObj uHom

/-- Actual category descent after lifting preserves every original exact K₀ class. -/
theorem categoryDownUpK0 (R : Type uR) [Ring R]
    (k : K0 (FGProjectiveCat.CategoryUniverseLift.originalCategory.{uR, uM} R)) :
    K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
      (K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) k) = k := by
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let D := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R
  have hu : U ⋙ D ≅ 𝟭 (FGProjectiveCat.CategoryUniverseLift.originalCategory.{uR, uM} R) :=
    E.unitIso.symm
  have hm : (K0.map D).comp (K0.map U) =
      AddMonoidHom.id (K0 (FGProjectiveCat.CategoryUniverseLift.originalCategory.{uR, uM} R)) :=
    (K0.map_comp U D).symm.trans ((K0.map_eq_of_iso hu).trans K0.map_id)
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
    DFunLike.congr_fun hm k

/-- Actual category lifting after descent preserves every lifted exact K₀ class. -/
theorem categoryUpDownK0 (R : Type uR) [Ring R]
    (k : K0 (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) :
    K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R)
      (K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) k) = k := by
  let U := FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R
  let D := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R
  have hc : D ⋙ U ≅ 𝟭 (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R) :=
    E.counitIso
  have hm : (K0.map U).comp (K0.map D) =
      AddMonoidHom.id (K0 (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) :=
    (K0.map_comp D U).symm.trans ((K0.map_eq_of_iso hc).trans K0.map_id)
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
    DFunLike.congr_fun hm k


variable (R : Type uR) [Ring R]

/-- The unchanged original evaluator in the selected module universe,
followed by the existing fixed RingK0 dictionary. -/
def originalLoopFixedK0
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :
    RingK0 R :=
  RingK0.projectiveUniverseEquiv.{uR, uM} R
    (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R) (ZerothHomotopy.mk p))

/-- The original module-category chosen-zero constant loop has fixed class zero. -/
theorem originalLoopFixedK0_constant :
    originalLoopFixedK0.{uR, uM} R
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max uR uM} R)) = 0 := by
  unfold originalLoopFixedK0
  rw [canonicalLoopComponentsK0_refl, map_zero]

/-- The original generator loop retains the fixed class of the same projective. -/
theorem originalLoopFixedK0_generator (X : FGProjectiveCat.{max uR uM} R) :
    originalLoopFixedK0.{uR, uM} R (generatorLoop X) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R (K0.mk X) := by
  unfold originalLoopFixedK0
  rw [generatorLoop_canonical]

/-- The actual exact-equivalence K0 descent followed by the unchanged fixed
RingK0 dictionary. Its inverse is constructed from the actual category lift. -/
def categoryK0Equiv :
    K0 (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R) ≃+
      RingK0 R :=
  (K0.equivOfEquivalence
      (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm).trans
    (RingK0.projectiveUniverseEquiv.{uR, uM} R)

/-- Every lifted category class is evaluated by the actual exact descent
functor, before applying the original module-universe dictionary. -/
theorem categoryK0Equiv_apply
    (k : K0 (FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) :
    categoryK0Equiv.{uR, uM, uObj, uHom} R k =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.map (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R)
          k) := by
  let E := (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
  let D := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  have hFunctor : E.functor = D := rfl
  have hMap : (K0.equivOfEquivalence E).toAddMonoidHom = K0.map D := by
    apply K0.hom_ext
    intro X
    change K0.equivOfEquivalence E (K0.mk X) = K0.map D (K0.mk X)
    exact (K0.equivOfEquivalence_mk E X).trans
      ((congrArg
        (fun Y : FGProjectiveCat.CategoryUniverseLift.originalCategory.{uR, uM} R =>
          K0.mk Y) (Functor.congr_obj hFunctor X)).trans (K0.map_mk D X).symm)
  have hValue : K0.equivOfEquivalence E k = K0.map D k :=
    DFunLike.congr_fun hMap k
  unfold categoryK0Equiv
  exact (AddEquiv.trans_apply (K0.equivOfEquivalence E)
    (RingK0.projectiveUniverseEquiv.{uR, uM} R) k).trans
      (congrArg (RingK0.projectiveUniverseEquiv.{uR, uM} R) hValue)

/-- An original class keeps its fixed RingK0 value after the actual category
lift and descent. This is the proved unit law of exact K0 equivalence. -/
theorem categoryK0Equiv_up
    (k : K0 (FGProjectiveCat.CategoryUniverseLift.originalCategory.{uR, uM} R)) :
    categoryK0Equiv.{uR, uM, uObj, uHom} R
        (K0.map (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) k) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R k := by
  rw [categoryK0Equiv_apply]
  exact congrArg (RingK0.projectiveUniverseEquiv.{uR, uM} R)
    (categoryDownUpK0.{uR, uM, uObj, uHom} R k)

/-- The generator formula uses the actual descended finite projective. -/
theorem categoryK0Equiv_mk
    (X : FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R) :
    categoryK0Equiv.{uR, uM, uObj, uHom} R (K0.mk X) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.mk ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj
          X)) := by
  rw [categoryK0Equiv_apply, K0.map_mk]

/-- The actual original Q-loop evaluator for the independently sized
category, using exact K0 descent. It does not refer to a chosen Q=plus HE. -/
def liftedCategoryLoopFixedK0
    (p : BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) :
    RingK0 R :=
  categoryK0Equiv.{uR, uM, uObj, uHom} R
    (canonicalLoopComponentsK0
      (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
      (ZerothHomotopy.mk p))

/-- The literal chosen-zero constant loop retains the original zero class. -/
theorem liftedCategoryLoopFixedK0_constant :
    liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R
        (BasedSplitExactQLoop.constantQLoop
          (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) = 0 := by
  unfold liftedCategoryLoopFixedK0
  rw [canonicalLoopComponentsK0_refl, map_zero]

/-- The original mono-forward/epi-reversed generator has the class of the
actual decoded original projective, with no class chosen from a comparison. -/
theorem liftedCategoryLoopFixedK0_generator
    (X : FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R) :
    liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R (generatorLoop X) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.mk ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj
          X)) := by
  unfold liftedCategoryLoopFixedK0
  rw [generatorLoop_canonical]
  exact categoryK0Equiv_mk.{uR, uM, uObj, uHom} R X

/-- Every fixed RingK0 class occurs on an actual original loop of the lifted
category. The original complete Q/S evaluator supplies this range. -/
theorem liftedCategoryLoopFixedK0_surjective :
    Function.Surjective (liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R) := by
  intro k
  obtain ⟨c, hc⟩ :=
    (canonicalLoopComponentsK0_bijective
      (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)).surjective
      ((categoryK0Equiv.{uR, uM, uObj, uHom} R).symm k)
  obtain ⟨p, rfl⟩ := ZerothHomotopy.mk_surjective c
  refine ⟨p, ?_⟩
  unfold liftedCategoryLoopFixedK0
  rw [hc]
  exact (categoryK0Equiv.{uR, uM, uObj, uHom} R).apply_symm_apply k

end ProjectiveClassDictionary

section NativeEvaluator

universe uR uM uObj uHom uNative

variable (R : Type uR) [Ring R]

/-- The fixed class of an actual native Q loop is computed from its literal
carrier descent, original CL evaluator and exact categorical K0 descent. -/
def nativeLoopFixedK0
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    RingK0 R :=
  liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R
    (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)

private theorem nativeLoopFixedK0FormulaLiteral
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.equivOfEquivalence
          (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
          (canonicalLoopComponentsK0
            (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
            (ZerothHomotopy.mk
              (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))) := by
  unfold nativeLoopFixedK0 liftedCategoryLoopFixedK0 categoryK0Equiv
  exact AddEquiv.trans_apply
    (K0.equivOfEquivalence
      (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm)
    (RingK0.projectiveUniverseEquiv.{uR, uM} R)
    (canonicalLoopComponentsK0
      (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
      (ZerothHomotopy.mk
        (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))

/-- The independent original evaluator formula keeps every actual CL
component and the unchanged fixed RingK0 target. -/
theorem nativeLoopFixedK0_formula
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.equivOfEquivalence
          (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
          (canonicalLoopComponentsK0
            (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
            (ZerothHomotopy.mk
              (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))) :=
  nativeLoopFixedK0FormulaLiteral.{uR, uM, uObj, uHom, uNative} R p

/-- The literal native constant loop retains the fixed zero class. -/
theorem nativeLoopFixedK0_constant :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) = 0 := by
  unfold nativeLoopFixedK0
  rw [QuillenUniverseLift.rawNativeCarrierDown_constant]
  exact liftedCategoryLoopFixedK0_constant.{uR, uM, uObj, uHom} R

/-- Including an actual original CL loop in its native carrier preserves
the original evaluator on the entire loop, without reference to a Q=plus map. -/
theorem nativeLoopFixedK0_carrierUp
    (p : BasedSplitExactQLoop.originalQLoops
      (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R p) =
      liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R p := by
  unfold nativeLoopFixedK0
  exact congrArg (liftedCategoryLoopFixedK0.{uR, uM, uObj, uHom} R)
    (congrArg (fun f => f p)
      (QuillenUniverseLift.rawNativeCarrierDown_comp_up.{uR, uM, uObj, uHom, uNative} R))

/-- Every fixed RingK0 class is represented by an actual native Q loop.
The range is supplied by the original evaluator and literal carrier inclusion. -/
theorem nativeLoopFixedK0_surjective :
    Function.Surjective (nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R) := by
  intro k
  obtain ⟨p, hp⟩ := liftedCategoryLoopFixedK0_surjective.{uR, uM, uObj, uHom} R k
  exact ⟨QuillenUniverseLift.rawNativeCarrierUp.{uR, uM, uObj, uHom, uNative} R p,
    (nativeLoopFixedK0_carrierUp.{uR, uM, uObj, uHom, uNative} R p).trans hp⟩

private theorem nativeDownFixedK0OfActualGenerators
    (hGenerators : ∀ X :
      FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R,
      ((QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
        (generatorLoop X)).Homotopic
          (generatorLoop
            ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj
              X)))
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    originalLoopFixedK0.{uR, uM} R
        (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p) =
      nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p := by
  let F := FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R
  let f := QuillenUniverseLift.qDownWeaklyPointed.{uR, uM, uObj, uHom} R
  let c := QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p
  have h := evaluatorNaturalityOfActualGeneratorLoops F f hGenerators (ZerothHomotopy.mk c)
  rw [ContinuousMap.WeaklyPointed.loopComponentsMap_mk] at h
  have hComponent := QuillenUniverseLift.Qdown_components.{uR, uM, uObj, uHom, uNative} R p
  have hValue : canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R)
      (ZerothHomotopy.mk
        (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p)) =
      K0.map F
        (canonicalLoopComponentsK0
          (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
          (ZerothHomotopy.mk c)) :=
    (congrArg (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R))
      hComponent).trans h
  unfold originalLoopFixedK0 nativeLoopFixedK0 liftedCategoryLoopFixedK0
  rw [categoryK0Equiv_apply]
  exact congrArg (RingK0.projectiveUniverseEquiv.{uR, uM} R) hValue

private theorem nativeUpFixedK0OfActualDown
    (hDown : ∀ p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R,
      originalLoopFixedK0.{uR, uM} R
          (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p) =
        nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p)
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p) =
      originalLoopFixedK0.{uR, uM} R p := by
  let H := (QuillenUniverseLift.QrightHomotopyRel.{uR, uM, uObj, uHom, uNative} R).toHomotopy
  let P : Path
      (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p)) p :=
    { toFun := fun t => H (t, p)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := H.map_zero_left p
      target' := H.map_one_left p }
  exact (hDown (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p)).symm.trans
    (congrArg (fun c => RingK0.projectiveUniverseEquiv.{uR, uM} R
      (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R) c))
        (ZerothHomotopy.sound P))

/-- The actual original Q descent preserves the independent canonical CL
evaluator in the fixed RingK0 group, on every native loop component. -/
theorem Qdown_fixedK0
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    originalLoopFixedK0.{uR, uM} R
        (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p) =
      nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R p :=
  nativeDownFixedK0OfActualGenerators.{uR, uM, uObj, uHom, uNative} R
    (QuillenUniverseLift.qDownWeaklyPointed_generator.{uR, uM, uObj, uHom} R) p

/-- The actual based inverse has the same original fixed class. This uses
the proved Q descent square and actual inverse family, rather than defining
the native class by an inverse homotopy equivalence. -/
theorem Qup_fixedK0
    (p : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max uR uM} R)) :
    nativeLoopFixedK0.{uR, uM, uObj, uHom, uNative} R
        (QuillenUniverseLift.Qup.{uR, uM, uObj, uHom, uNative} R p) =
      originalLoopFixedK0.{uR, uM} R p :=
  nativeUpFixedK0OfActualDown.{uR, uM, uObj, uHom, uNative} R
    (Qdown_fixedK0.{uR, uM, uObj, uHom, uNative} R) p

/-- The full original Q/S class formula for the actual cross-universe Q
descent, keeping the exact-equivalence dictionary and every original class. -/
theorem Qdown_canonicalEvaluator
    (p : QuillenUniverseLift.nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    RingK0.projectiveUniverseEquiv.{uR, uM} R
        (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R)
          (ZerothHomotopy.mk
            (QuillenUniverseLift.Qdown.{uR, uM, uObj, uHom, uNative} R p))) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (K0.equivOfEquivalence
          (FGProjectiveCat.CategoryUniverseLift.equivalence.{uR, uM, uObj, uHom} R).symm
          (canonicalLoopComponentsK0
            (C := FGProjectiveCat.CategoryUniverseLift.category.{uR, uM, uObj, uHom} R)
            (ZerothHomotopy.mk
              (QuillenUniverseLift.rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R p)))) :=
  (Qdown_fixedK0.{uR, uM, uObj, uHom, uNative} R p).trans
    (nativeLoopFixedK0_formula.{uR, uM, uObj, uHom, uNative} R p)

end NativeEvaluator

end AlgebraicKTheory.OriginalQK0UniverseLiftCompatibility

end
