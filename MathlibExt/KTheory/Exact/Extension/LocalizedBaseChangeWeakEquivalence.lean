/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ZeroSpanBaseChange
public import MathlibExt.KTheory.Exact.Extension.LocalizedZeroFiberNerveEquivalence
public import MathlibExt.KTheory.Exact.Extension.LocalizedMiddleWeakEquivalence

/-!
# Weakness of every original localized Q-span pullback

The actual kernel and middle comparisons give weak pullbacks for the two distinct zero
spans. Their natural pure-arrow triangles then give weak pure mono and epi pullbacks.
The epi-then-mono factorization of the original admissible span, followed by quotient
induction, proves weakness for every original Q arrow. All functors use the chosen
Cartesian pullbacks on the complete original fibers. Each zero-span helper uses only
its original base at the target, and each pure-arrow helper uses only its two endpoint
bases. The arbitrary-span and ring results retain the original base family.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory.FixedTargetExtension.IteratedAction.Collapse
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The original base at X, kernel comparison and zero-fiber equivalence make its pullback weak. -/
theorem zeroMonoBaseChangeNerveMap_mem_of_originalBases_conull
    (X : C)
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences (nerveMap (zeroMonoBaseChange X)) := by
  let theta : SInverse (Core C) (Core C) ⥤ FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
    FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
      FixedTargetExtension.localizedFiberFunctor (0 : C)
  have hKappa : SSet.realizationWeakEquivalences
      (nerveMapCommonHom.{u, max u v, 0} (FixedTargetExtension.localizedKernelFunctor X)) :=
    (collapse_and_kernelNerveMaps_mem_of_originalBase_conull
      (C := C) (X := X) hBaseX).2
  have hTheta : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} theta) :=
    FixedTargetExtension.completedCoreToZeroFiberNerveMap_mem_realizationWeakEquivalences
      (C := C)
  have hModelComp : SSet.realizationWeakEquivalences
      (nerveMapCommonHom.{u, max u v, 0} (FixedTargetExtension.localizedKernelFunctor X) ≫
        nerveMapCommonHomUp.{u, max u v, 0} theta) :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hKappa hTheta
  have hModel : SSet.realizationWeakEquivalences (nerveMap (kernelFiberFunctor X)) := by
    rw [nerveMapCommonHom_comp_up] at hModelComp
    exact hModelComp
  let V : SSet.{max u v} := nerve (FixedTargetExtension.localizedRows (C := C) X)
  let F0 : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) (0 : C))
  let l : V ⟶ F0 := nerveMap (FixedTargetExtension.localizedFiberFunctor X ⋙ zeroMonoBaseChange X)
  let r : V ⟶ F0 := nerveMap (kernelFiberFunctor X)
  have hNatural : SSet.Homotopy l r := NatTrans.nerveHomotopy (zeroMonoKernelNatIso X).hom
  let H := SSet.realizeHomotopy V F0 l r hNatural
  have hComposite : SSet.realizationWeakEquivalences l := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map l)
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).2 hModel
  have hI : SSet.realizationWeakEquivalences
      (nerveMap (FixedTargetExtension.localizedFiberFunctor X)) := by
    let e := FixedTargetExtension.localizedFiberEquivalence X
    exact nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hMaps : SSet.realizationWeakEquivalences
      (nerveMap (FixedTargetExtension.localizedFiberFunctor X) ≫
        nerveMap (zeroMonoBaseChange X)) := by
    rw [nerveMap_comp]
    exact hComposite
  exact SSet.realizationWeakEquivalences.of_precomp
    (nerveMap (FixedTargetExtension.localizedFiberFunctor X))
    (nerveMap (zeroMonoBaseChange X)) hI hMaps

/-- The original base at X and middle comparison give its given-object epi-zero pullback weakly. -/
theorem zeroEpiBaseChangeNerveMap_mem_of_originalBases_conull
    (X : C)
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    SSet.realizationWeakEquivalences (nerveMap (zeroEpiBaseChange X)) := by
  let theta : SInverse (Core C) (Core C) ⥤ FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
    FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
      FixedTargetExtension.localizedFiberFunctor (0 : C)
  have hBeta : SSet.realizationWeakEquivalences
      (nerveMapCommonHom.{u, max u v, 0} (FixedTargetExtension.localizedMiddleFunctor X)) :=
    FixedTargetExtension.SplitInclusion.localizedMiddleNerveMap_mem_of_originalBase_conull
      (C := C) (X := X) hBaseX
  have hTheta : SSet.realizationWeakEquivalences
      (nerveMapCommonHomUp.{u, max u v, 0} theta) :=
    FixedTargetExtension.completedCoreToZeroFiberNerveMap_mem_realizationWeakEquivalences
      (C := C)
  have hModelComp : SSet.realizationWeakEquivalences
      (nerveMapCommonHom.{u, max u v, 0} (FixedTargetExtension.localizedMiddleFunctor X) ≫
        nerveMapCommonHomUp.{u, max u v, 0} theta) :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hBeta hTheta
  have hModel : SSet.realizationWeakEquivalences (nerveMap (middleFiberFunctor X)) := by
    rw [nerveMapCommonHom_comp_up] at hModelComp
    exact hModelComp
  let V : SSet.{max u v} := nerve (FixedTargetExtension.localizedRows (C := C) X)
  let F0 : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) (0 : C))
  let l : V ⟶ F0 := nerveMap (FixedTargetExtension.localizedFiberFunctor X ⋙ zeroEpiBaseChange X)
  let r : V ⟶ F0 := nerveMap (middleFiberFunctor X)
  have hNatural : SSet.Homotopy l r := NatTrans.nerveHomotopy (zeroEpiMiddleNatIso X).hom
  let H := SSet.realizeHomotopy V F0 l r hNatural
  have hComposite : SSet.realizationWeakEquivalences l := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map l)
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).2 hModel
  have hI : SSet.realizationWeakEquivalences
      (nerveMap (FixedTargetExtension.localizedFiberFunctor X)) := by
    let e := FixedTargetExtension.localizedFiberEquivalence X
    exact nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hMaps : SSet.realizationWeakEquivalences
      (nerveMap (FixedTargetExtension.localizedFiberFunctor X) ≫
        nerveMap (zeroEpiBaseChange X)) := by
    rw [nerveMap_comp]
    exact hComposite
  exact SSet.realizationWeakEquivalences.of_precomp
    (nerveMap (FixedTargetExtension.localizedFiberFunctor X))
    (nerveMap (zeroEpiBaseChange X)) hI hMaps

/-- The two endpoint bases and mono-zero triangle give weakness on all original components. -/
theorem pureMonoBaseChangeNerveMap_mem_of_originalBases_conull
    {M X : C}
    (hBaseM : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C M)) :
          SSet.{max u v}))))
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v}))))
    (mu : M ⟶ X) (hmu : IsAdmissibleMono mu) :
    SSet.realizationWeakEquivalences
      (nerveMap (baseChangeFunctor (QuillenQ.pureMonoHom mu hmu))) := by
  let F := baseChangeFunctor (QuillenQ.pureMonoHom mu hmu)
  let G := zeroMonoBaseChange M
  let S := zeroMonoBaseChange X
  have hS : SSet.realizationWeakEquivalences (nerveMap S) :=
    zeroMonoBaseChangeNerveMap_mem_of_originalBases_conull X hBaseX
  have hG : SSet.realizationWeakEquivalences (nerveMap G) :=
    zeroMonoBaseChangeNerveMap_mem_of_originalBases_conull M hBaseM
  let A : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) X)
  let Z : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) (0 : C))
  let H := SSet.realizeHomotopy A Z (nerveMap S) (nerveMap (F ⋙ G))
    (NatTrans.nerveHomotopy (zeroMonoPureMonoTriangleNatIso mu hmu).hom)
  have hFunctorComp : SSet.realizationWeakEquivalences (nerveMap (F ⋙ G)) := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMap (F ⋙ G)))
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).1 hS
  have hMaps : SSet.realizationWeakEquivalences (nerveMap F ≫ nerveMap G) := by
    rw [nerveMap_comp]
    exact hFunctorComp
  exact SSet.realizationWeakEquivalences.of_postcomp (nerveMap F) (nerveMap G) hG hMaps

/-- The two endpoint bases and epi-zero triangle retain the original reverse pullback order. -/
theorem pureEpiBaseChangeNerveMap_mem_of_originalBases_conull
    {M X : C}
    (hBaseM : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C M)) :
          SSet.{max u v}))))
    (hBaseX : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v}))))
    (lambda : M ⟶ X)
    (hlambda : IsAdmissibleEpi lambda) :
    SSet.realizationWeakEquivalences
      (nerveMap (baseChangeFunctor (QuillenQ.pureEpiHom lambda hlambda))) := by
  let F := baseChangeFunctor (QuillenQ.pureEpiHom lambda hlambda)
  let G := zeroEpiBaseChange X
  let S := zeroEpiBaseChange M
  have hS : SSet.realizationWeakEquivalences (nerveMap S) :=
    zeroEpiBaseChangeNerveMap_mem_of_originalBases_conull M hBaseM
  have hG : SSet.realizationWeakEquivalences (nerveMap G) :=
    zeroEpiBaseChangeNerveMap_mem_of_originalBases_conull X hBaseX
  let A : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) M)
  let Z : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) (0 : C))
  let H := SSet.realizeHomotopy A Z (nerveMap S) (nerveMap (F ⋙ G))
    (NatTrans.nerveHomotopy (zeroEpiPureEpiTriangleNatIso lambda hlambda).hom)
  have hFunctorComp : SSet.realizationWeakEquivalences (nerveMap (F ⋙ G)) := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMap (F ⋙ G)))
    exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).1 hS
  have hMaps : SSet.realizationWeakEquivalences (nerveMap F ≫ nerveMap G) := by
    rw [nerveMap_comp]
    exact hFunctorComp
  exact SSet.realizationWeakEquivalences.of_postcomp (nerveMap F) (nerveMap G) hG hMaps

/-- Every original Q arrow has a weak pullback via its exact span factorization.
Quotient induction retains every original representative. -/
theorem baseChangeNerveMap_mem_of_originalBases_conull
    (hBase : ∀ X : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) {R S : QuillenQ C} (phi : R ⟶ S) :
    SSet.realizationWeakEquivalences (nerveMap (baseChangeFunctor phi)) := by
  rcases R with ⟨X⟩
  rcases S with ⟨Y⟩
  refine Quotient.inductionOn phi ?_
  intro sigma
  let ep : (⟨X⟩ : QuillenQ C) ⟶ (⟨sigma.apex⟩ : QuillenQ C) :=
    QuillenQ.pureEpiHom sigma.l sigma.wl
  let mon : (⟨sigma.apex⟩ : QuillenQ C) ⟶ (⟨Y⟩ : QuillenQ C) :=
    QuillenQ.pureMonoHom sigma.r sigma.wr
  let F := baseChangeFunctor mon
  let G := baseChangeFunctor ep
  have hF : SSet.realizationWeakEquivalences (nerveMap F) :=
    pureMonoBaseChangeNerveMap_mem_of_originalBases_conull
        (hBase sigma.apex) (hBase Y) sigma.r sigma.wr
  have hG : SSet.realizationWeakEquivalences (nerveMap G) :=
    pureEpiBaseChangeNerveMap_mem_of_originalBases_conull
        (hBase sigma.apex) (hBase X) sigma.l sigma.wl
  have hMaps : SSet.realizationWeakEquivalences (nerveMap F ≫ nerveMap G) :=
    SSet.realizationWeakEquivalences.comp_mem _ _ hF hG
  have hFunctorComp : SSet.realizationWeakEquivalences (nerveMap (F ⋙ G)) := by
    rw [nerveMap_comp] at hMaps
    exact hMaps
  have hArrow : ep ≫ mon = QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma :=
    QuillenQ.pureEpiHom_pureMonoHom sigma
  let i : baseChangeFunctor (ep ≫ mon) ≅
      baseChangeFunctor (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma) :=
    eqToIso (congrArg (fun q : (⟨X⟩ : QuillenQ C) ⟶ (⟨Y⟩ : QuillenQ C) =>
      baseChangeFunctor q) hArrow)
  let e : baseChangeFunctor (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma) ≅ F ⋙ G :=
    i.symm ≪≫ baseChangeCompositionNatIso ep mon
  let A : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) Y)
  let Z : SSet.{max u v} := nerve (FixedTargetExtension.localizedFiber (C := C) X)
  let H := SSet.realizeHomotopy A Z
    (nerveMap (baseChangeFunctor (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma)))
    (nerveMap (F ⋙ G)) (NatTrans.nerveHomotopy e.hom)
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map (nerveMap (baseChangeFunctor
      (QuillenQ.mkHom (X := ⟨X⟩) (Y := ⟨Y⟩) sigma))))
  exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy H).2 hFunctorComp

/-- Every original projective Q span over an associative unital ring has a weak pullback. -/
theorem projectiveBaseChangeNerveMap_mem_realizationWeakEquivalences
    {R : Type uRing} [Ring R]
    {A B : QuillenQ (FGProjectiveCat.{vModule} R)} (phi : A ⟶ B) :
    SSet.realizationWeakEquivalences
      (nerveMap (baseChangeFunctor (C := FGProjectiveCat.{vModule} R) phi)) := by
  have hBase : ∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
          (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
            SSet.{max uRing (vModule + 1)}))) := by
    intro X
    exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X
  exact baseChangeNerveMap_mem_of_originalBases_conull
    (C := FGProjectiveCat.{vModule} R) hBase phi

end AlgebraicKTheory.LocalizedBaseChange

end
