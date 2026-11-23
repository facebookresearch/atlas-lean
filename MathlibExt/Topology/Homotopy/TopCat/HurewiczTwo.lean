/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.HomologyUniverse
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateEmbedding
import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedHomologyComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.ConnectedDegreeTwoHurewicz
import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.RealizationSingular
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.AlgebraicTopology.SingularHomology.IntegerExactness
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Spherical representatives in integral degree two

The mathematical source is the degree-two Hurewicz theorem for a
path-connected space with trivial based fundamental group. Weibel,
*The K-book*, Exercise IV.1.4 (printed p. 273), separately asks for actual
sphere maps representing the added two-cell classes. Applying the existing
Hurewicz theorem to a constructed cover is the project’s proof route for
that application. The native simplicial Hurewicz theorem is already proved
and is reused here.

The continuous classical-sphere map, its calibration to the unchanged
boundary of the original relative three-disk generator, and the complete
integral coefficient formulas are project-derived comparison refinements.
This generic result does not assume or prove that the original two-cell
attachment is simply connected, and does not complete its proper-subgroup
spherical or local-coefficient plus construction.

The four oriented faces of the realized boundary of Delta3 give an actual
normalized cycle. The coefficient of its first face is a retraction, and the
existing realization homology comparison and sphere calculation prove that
it generates integral H2.

A pointed singular two-simplex extends over this boundary with the other
three faces constant. The original realization--singular adjunction identifies
its homology image with the native Hurewicz class. The computed coefficient
automorphism between this cycle and the boundary of the original relative
3-disk generator retains that fixed generator and its sign.

The resulting continuous representatives apply to ordinary path-connected
spaces with trivial actual fundamental group. No separation, CW, finite,
countable, spherical-map, homology-inverse, or model premise is supplied.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology
open scoped Simplicial

universe u

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private abbrev integralCoefficient : AddCommGrpCat.{u} :=
  singularIntegralCoefficients

private theorem integralHom_ext {A : AddCommGrpCat.{u}}
    (f g : integralCoefficient.{u} ⟶ A)
    (h : f (ULift.up (1 : ℤ)) = g (ULift.up (1 : ℤ))) : f = g := by
  apply AddCommGrpCat.ext
  intro a
  have ha : a = a.down • (ULift.up (1 : ℤ) : integralCoefficient.{u}) := by
    apply ULift.down_injective
    simp
  change f.hom a = g.hom a
  rw [ha, map_zsmul, map_zsmul]
  exact congrArg (fun z : A => a.down • z) h

private theorem integralEnd_comp_comm
    (f g : integralCoefficient.{u} ⟶ integralCoefficient.{u}) :
    f ≫ g = g ≫ f := by
  apply integralHom_ext
  let oneR : integralCoefficient.{u} := ULift.up (1 : ℤ)
  let a := (f.hom oneR).down
  let b := (g.hom oneR).down
  have hf : f.hom oneR = a • oneR := by
    apply ULift.down_injective
    simp [a, oneR]
  have hg : g.hom oneR = b • oneR := by
    apply ULift.down_injective
    simp [b, oneR]
  have hfg : g.hom (f.hom oneR) = (a * b) • oneR := by
    have h₁ : g.hom (f.hom oneR) = a • g.hom oneR :=
      (congrArg g.hom hf).trans (by rw [map_zsmul])
    have h₂ : a • g.hom oneR = a • (b • oneR) :=
      congrArg (fun z : integralCoefficient.{u} => a • z) hg
    exact h₁.trans (h₂.trans (smul_smul a b oneR))
  have hgf : f.hom (g.hom oneR) = (b * a) • oneR := by
    have h₁ : f.hom (g.hom oneR) = b • f.hom oneR :=
      (congrArg f.hom hg).trans (by rw [map_zsmul])
    have h₂ : b • f.hom oneR = b • (a • oneR) :=
      congrArg (fun z : integralCoefficient.{u} => b • z) hf
    exact h₁.trans (h₂.trans (smul_smul b a oneR))
  change g.hom (f.hom oneR) = f.hom (g.hom oneR)
  exact hfg.trans ((congrArg (fun k : ℤ => k • oneR) (mul_comm a b)).trans hgf.symm)

private theorem integralGenerator_isIso_of_retraction
    {A : AddCommGrpCat.{u}} (e : A ≅ integralCoefficient.{u})
    (f : integralCoefficient.{u} ⟶ A) (g : A ⟶ integralCoefficient.{u})
    (h : f ≫ g = 𝟙 integralCoefficient.{u}) : IsIso f := by
  have hfg : (f ≫ e.hom) ≫ (e.inv ≫ g) = 𝟙 integralCoefficient.{u} := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  have hgf : (e.inv ≫ g) ≫ (f ≫ e.hom) = 𝟙 integralCoefficient.{u} :=
    (integralEnd_comp_comm (e.inv ≫ g) (f ≫ e.hom)).trans hfg
  have hA : g ≫ f = 𝟙 A := by
    apply (cancel_mono e.hom).mp
    apply (cancel_epi e.inv).mp
    simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id] using hgf
  let ef : integralCoefficient.{u} ≅ A :=
    { hom := f
      inv := g
      hom_inv_id := h
      inv_hom_id := hA }
  exact ef.isIso_hom

end ClassicalSphereCalibration

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private abbrev boundaryThree : SSet.{u} :=
  (SSet.boundary.{u} 3 : SSet.{u})

private def boundaryFaceTwo (i : Fin 4) : boundaryThree.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (SSet.boundary.ι i)

private theorem boundaryFaceTwo_nonDegenerate (i : Fin 4) :
    boundaryFaceTwo.{u} i ∈ boundaryThree.{u}.nonDegenerate 2 := by
  let t : (Δ[2] : SSet.{u}).nonDegenerate 2 :=
    ⟨SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌),
      SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 2⟩
  let s := SSet.nonDegenerateEmbeddingOfMono (SSet.boundary.ι i) 2 t
  have ht : t.val = SSet.yonedaEquiv (𝟙 (Δ[2] : SSet.{u})) := by
    apply SSet.stdSimplex.objEquiv.injective
    simp [t]
  have hs : s.val = boundaryFaceTwo i := by
    dsimp only [s]
    rw [SSet.nonDegenerateEmbeddingOfMono_apply, ht]
    simpa only [Category.id_comp, boundaryFaceTwo] using
      (SSet.yonedaEquiv_comp (𝟙 (Δ[2] : SSet.{u})) (SSet.boundary.ι i)).symm
  simpa only [hs] using s.property

private theorem boundaryFaceTwo_zero_ne_succ (i : Fin 3) :
    boundaryFaceTwo.{u} 0 ≠ boundaryFaceTwo.{u} i.succ := by
  intro h
  have he := congrArg
    (fun z : boundaryThree.{u} _⦋2⦌ =>
      ((SSet.boundary.{u} 3).ι.app _ z) (0 : Fin 3)) h
  fin_cases i
  all_goals
    change (1 : Fin 4) = 0 at he
    exact (by decide : (1 : Fin 4) ≠ 0) he

private theorem boundaryFaceTwo_ridge
    (i j : Fin 4) (hij : i < j) :
    boundaryThree.{u}.δ (j.pred (Fin.ne_zero_of_lt hij)) (boundaryFaceTwo i) =
      boundaryThree.{u}.δ (i.castPred (Fin.ne_last_of_lt hij)) (boundaryFaceTwo j) := by
  have h := (SSet.boundary.isCompatible_succ_iff _).mp
    (SSet.boundary.ι_isCompatible 2) i j hij
  simpa only [boundaryFaceTwo, SSet.stdSimplex.yonedaEquiv_δ_comp] using
    congrArg SSet.yonedaEquiv h

private abbrev boundaryNormalizedComplex : ChainComplex AddCommGrpCat.{u} ℕ :=
  boundaryThree.{u}.normalizedChainComplex
    (singularIntegralCoefficients : AddCommGrpCat.{u})

private def normalizedBoundaryTwoChain :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      boundaryNormalizedComplex.{u}.X 2 :=
  boundaryThree.ιNormalizedChainComplex (boundaryFaceTwo 0) -
    boundaryThree.ιNormalizedChainComplex (boundaryFaceTwo 1) +
      boundaryThree.ιNormalizedChainComplex (boundaryFaceTwo 2) -
        boundaryThree.ιNormalizedChainComplex (boundaryFaceTwo 3)

private theorem normalizedBoundaryTwoChain_cycle :
    normalizedBoundaryTwoChain.{u} ≫ boundaryNormalizedComplex.{u}.d 2 1 = 0 := by
  have h01 : boundaryThree.{u}.δ 0 (boundaryFaceTwo 0) =
      boundaryThree.{u}.δ 0 (boundaryFaceTwo 1) := by
    simpa using boundaryFaceTwo_ridge.{u} 0 1 (by decide)
  have h02 : boundaryThree.{u}.δ 1 (boundaryFaceTwo 0) =
      boundaryThree.{u}.δ 0 (boundaryFaceTwo 2) := by
    simpa using boundaryFaceTwo_ridge.{u} 0 2 (by decide)
  have h03 : boundaryThree.{u}.δ 2 (boundaryFaceTwo 0) =
      boundaryThree.{u}.δ 0 (boundaryFaceTwo 3) := by
    simpa using boundaryFaceTwo_ridge.{u} 0 3 (by decide)
  have h12 : boundaryThree.{u}.δ 1 (boundaryFaceTwo 1) =
      boundaryThree.{u}.δ 1 (boundaryFaceTwo 2) := by
    simpa using boundaryFaceTwo_ridge.{u} 1 2 (by decide)
  have h13 : boundaryThree.{u}.δ 2 (boundaryFaceTwo 1) =
      boundaryThree.{u}.δ 1 (boundaryFaceTwo 3) := by
    simpa using boundaryFaceTwo_ridge.{u} 1 3 (by decide)
  have h23 : boundaryThree.{u}.δ 2 (boundaryFaceTwo 2) =
      boundaryThree.{u}.δ 2 (boundaryFaceTwo 3) := by
    have h := boundaryFaceTwo_ridge.{u} 2 3 (by decide)
    have hp : (3 : Fin 4).pred (Fin.ne_zero_of_lt (by decide : (2 : Fin 4) < 3)) =
        (2 : Fin 3) := by
      apply Fin.ext
      rfl
    have hc : (2 : Fin 4).castPred (Fin.ne_last_of_lt (by decide : (2 : Fin 4) < 3)) =
        (2 : Fin 3) := by
      apply Fin.ext
      rfl
    rw [hp, hc] at h
    exact h
  dsimp only [normalizedBoundaryTwoChain]
  simp only [Preadditive.sub_comp, Preadditive.add_comp,
    SSet.ιNormalizedChainComplex_d, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
    Fin.sum_univ_zero, pow_zero, pow_succ, mul_neg, mul_one,
    one_smul, neg_smul, add_zero]
  have hs₁ : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have hs₂ : (0 : Fin 1).succ.succ = (2 : Fin 3) := rfl
  rw [hs₁, hs₂, h01, h02, h03, h12, h13, h23]
  abel

private def normalizedBoundaryTwoCycle :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      boundaryNormalizedComplex.{u}.cycles 2 :=
  boundaryNormalizedComplex.liftCycles normalizedBoundaryTwoChain 1 (by simp)
    normalizedBoundaryTwoChain_cycle

private def normalizedBoundaryTwoClass :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      boundaryNormalizedComplex.{u}.homology 2 :=
  normalizedBoundaryTwoCycle ≫ boundaryNormalizedComplex.homologyπ 2

private def boundaryFaceZeroCoefficient :
    boundaryNormalizedComplex.{u}.X 2 ⟶
      (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  classical
  let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
  exact (boundaryThree.isColimitCofanNormalizedChainComplex (C := AddCommGrpCat.{u}) R 2).desc
    (Cofan.mk R (fun a : boundaryThree.{u}.nonDegenerate 2 =>
      if a.val = boundaryFaceTwo.{u} 0 then (𝟙 R) else (0 : R ⟶ R)))

private theorem boundaryFaceZeroCoefficient_face (i : Fin 4) :
    boundaryThree.{u}.ιNormalizedChainComplex (boundaryFaceTwo i) ≫
        boundaryFaceZeroCoefficient =
      if i = 0 then 𝟙 (singularIntegralCoefficients : AddCommGrpCat.{u}) else 0 := by
  classical
  let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
  let a : boundaryThree.{u}.nonDegenerate 2 :=
    ⟨boundaryFaceTwo.{u} i, boundaryFaceTwo_nonDegenerate.{u} i⟩
  have h :=
      (boundaryThree.{u}.isColimitCofanNormalizedChainComplex (C := AddCommGrpCat.{u}) R 2).fac
    (Cofan.mk R (fun b : boundaryThree.{u}.nonDegenerate 2 =>
      if b.val = boundaryFaceTwo.{u} 0 then (𝟙 R) else (0 : R ⟶ R))) (Discrete.mk a)
  change boundaryThree.{u}.ιNormalizedChainComplex (C := AddCommGrpCat.{u}) (R := R)
      (boundaryFaceTwo.{u} i) ≫ boundaryFaceZeroCoefficient.{u} =
        if boundaryFaceTwo.{u} i = boundaryFaceTwo.{u} 0
          then (𝟙 R) else (0 : R ⟶ R) at h
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · simpa using h
  · have hn : boundaryFaceTwo j.succ ≠ boundaryFaceTwo 0 :=
      (boundaryFaceTwo_zero_ne_succ.{u} j).symm
    have hIf : (if boundaryFaceTwo.{u} j.succ = boundaryFaceTwo.{u} 0
        then (𝟙 R) else (0 : R ⟶ R)) = 0 := ite_eq_right hn
    have hSucc : (if j.succ = (0 : Fin 4) then (𝟙 R) else (0 : R ⟶ R)) = 0 :=
      ite_eq_right (Fin.succ_ne_zero j)
    exact (h.trans hIf).trans hSucc.symm

private theorem normalizedBoundaryTwoChain_coefficient :
    normalizedBoundaryTwoChain.{u} ≫ boundaryFaceZeroCoefficient =
      𝟙 (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  simp only [normalizedBoundaryTwoChain, Preadditive.sub_comp, Preadditive.add_comp,
    boundaryFaceZeroCoefficient_face]
  simp

private theorem boundaryNormalized_d_three_eq_zero :
    boundaryNormalizedComplex.{u}.d 3 2 = 0 := by
  exact (boundaryThree.isZero_normalizedChainComplex_X_of_hasDimensionLT
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3 3).eq_of_src _ _

private def boundaryHomologyProjectionIso :
    boundaryNormalizedComplex.{u}.cycles 2 ≅ boundaryNormalizedComplex.{u}.homology 2 :=
  boundaryNormalizedComplex.isoHomologyπ 3 2 (by simp) boundaryNormalized_d_three_eq_zero

private def boundaryHomologyCoefficient :
    boundaryNormalizedComplex.{u}.homology 2 ⟶
      (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  boundaryHomologyProjectionIso.inv ≫ boundaryNormalizedComplex.iCycles 2 ≫
    boundaryFaceZeroCoefficient

private theorem normalizedBoundaryTwoClass_coefficient :
    normalizedBoundaryTwoClass.{u} ≫ boundaryHomologyCoefficient =
      𝟙 (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  have hπ : boundaryHomologyProjectionIso.{u}.hom =
      boundaryNormalizedComplex.{u}.homologyπ 2 := rfl
  dsimp only [normalizedBoundaryTwoClass, boundaryHomologyCoefficient]
  rw [← hπ, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, normalizedBoundaryTwoCycle, HomologicalComplex.liftCycles_i]
  exact normalizedBoundaryTwoChain_coefficient

end ClassicalSphereCalibration

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private theorem exists_pointedTwoRepresentative
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (x : K _⦋0⦌) [Subsingleton (SSet.KanComplex.π 1 K x)]
    (z : K.homology (C := AddCommGrpCat.{u}) (singularIntegralCoefficients : AddCommGrpCat.{u}) 2) :
    ∃ p : K.PtSimplex 2 x,
      (SSet.pointedTwoHomologyClass p ≫
        (K.normalizedHomologyIso (C := AddCommGrpCat.{u})
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom)
        (ULift.up (1 : ℤ)) = z := by
  let e := K.normalizedHomologyIso (C := AddCommGrpCat.{u})
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2
  let zN := e.inv z
  let a := (SSet.connectedDegreeTwoHurewiczEquiv x).symm
    (Multiplicative.ofAdd zN)
  obtain ⟨p, hp⟩ := SSet.KanComplex.π.mk_surjective a
  have h := SSet.connectedDegreeTwoHurewiczEquiv_mk x p
  rw [hp] at h
  change SSet.connectedDegreeTwoHurewiczEquiv x
      ((SSet.connectedDegreeTwoHurewiczEquiv x).symm
        (Multiplicative.ofAdd zN)) =
    Multiplicative.ofAdd
      (SSet.pointedTwoHomologyClass p (ULift.up (1 : ℤ))) at h
  rw [MulEquiv.apply_symm_apply] at h
  have hpClass : SSet.pointedTwoHomologyClass p (ULift.up (1 : ℤ)) = zN :=
    (congrArg Multiplicative.toAdd h).symm
  refine ⟨p, ?_⟩
  change e.hom (SSet.pointedTwoHomologyClass p (ULift.up (1 : ℤ))) = z
  rw [hpClass]
  have hInverse := ConcreteCategory.congr_hom e.inv_hom_id z
  change e.hom (e.inv z) = z at hInverse
  exact hInverse

private def pointedTwoRepresentative
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (x : K _⦋0⦌) [Subsingleton (SSet.KanComplex.π 1 K x)]
    (z : K.homology (C := AddCommGrpCat.{u}) (singularIntegralCoefficients : AddCommGrpCat.{u}) 2) :
    K.PtSimplex 2 x :=
  (exists_pointedTwoRepresentative K x z).choose

private theorem pointedTwoRepresentative_class
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected]
    (x : K _⦋0⦌) [Subsingleton (SSet.KanComplex.π 1 K x)]
    (z : K.homology (C := AddCommGrpCat.{u}) (singularIntegralCoefficients : AddCommGrpCat.{u}) 2) :
    (SSet.pointedTwoHomologyClass (pointedTwoRepresentative K x z) ≫
      (K.normalizedHomologyIso (C := AddCommGrpCat.{u})
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom)
      (ULift.up (1 : ℤ)) = z :=
  (exists_pointedTwoRepresentative K x z).choose_spec

end ClassicalSphereCalibration

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private def oneFaceFamily {K : SSet.{u}} {x : K _⦋0⦌}
    (p : K.PtSimplex 2 x) (i : Fin 4) :
    (Δ[2] : SSet.{u}) ⟶ K :=
  if i = 0 then SSet.RelativeMorphism.map p else SSet.const x

private theorem oneFaceFamily_isCompatible
    {K : SSet.{u}} {x : K _⦋0⦌} (p : K.PtSimplex 2 x) :
    SSet.boundary.IsCompatible (oneFaceFamily p) := by
  rw [SSet.boundary.isCompatible_succ_iff]
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j ≠ 0 := Fin.ne_zero_of_lt hij
    simp only [oneFaceFamily, ite_eq_right hj, SSet.comp_const]
    exact SSet.PtSimplex.δ_map p _
  · have hj : j ≠ 0 := Fin.ne_zero_of_lt hij
    simp only [oneFaceFamily, ite_eq_right hi, ite_eq_right hj, SSet.comp_const]

private def oneFaceBoundaryMap {K : SSet.{u}} {x : K _⦋0⦌}
    (p : K.PtSimplex 2 x) : boundaryThree.{u} ⟶ K :=
  (oneFaceFamily_isCompatible p).desc

private theorem oneFaceBoundaryMap_face {K : SSet.{u}} {x : K _⦋0⦌}
    (p : K.PtSimplex 2 x) (i : Fin 4) :
    SSet.boundary.ι i ≫ oneFaceBoundaryMap p = oneFaceFamily p i :=
  SSet.boundary.IsCompatible.ι_desc (oneFaceFamily_isCompatible p) i

private theorem oneFaceBoundaryMap_face_apply
    {K : SSet.{u}} {x : K _⦋0⦌} (p : K.PtSimplex 2 x) (i : Fin 4) :
    (oneFaceBoundaryMap p).app _ (boundaryFaceTwo i) =
      SSet.yonedaEquiv (oneFaceFamily p i) := by
  rw [boundaryFaceTwo, ← SSet.yonedaEquiv_comp, oneFaceBoundaryMap_face]

private theorem normalizedBoundaryTwoChain_map
    {K : SSet.{u}} {x : K _⦋0⦌} (p : K.PtSimplex 2 x) :
    normalizedBoundaryTwoChain.{u} ≫
      (SSet.normalizedChainComplexMap (oneFaceBoundaryMap p)
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).f 2 =
      SSet.pointedTwoGenerator p := by
  dsimp only [normalizedBoundaryTwoChain]
  simp only [Preadditive.sub_comp, Preadditive.add_comp,
    SSet.ι_normalizedChainComplexMap_f, oneFaceBoundaryMap_face_apply]
  simp [oneFaceFamily, SSet.pointedTwoGenerator,
    SSet.ιNormalizedChainComplex_yonedaEquiv_const_eq_zero]

private theorem normalizedBoundaryTwoClass_map
    {K : SSet.{u}} {x : K _⦋0⦌} (p : K.PtSimplex 2 x) :
    normalizedBoundaryTwoClass.{u} ≫
      HomologicalComplex.homologyMap
        (SSet.normalizedChainComplexMap (oneFaceBoundaryMap p)
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2 =
      SSet.pointedTwoHomologyClass p := by
  rw [normalizedBoundaryTwoClass, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  rw [SSet.pointedTwoHomologyClass]
  congr 1
  apply (cancel_mono ((K.normalizedChainComplex
    (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})).iCycles 2)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    normalizedBoundaryTwoCycle, HomologicalComplex.liftCycles_i,
    normalizedBoundaryTwoChain_map, SSet.pointedTwoCycle_i]

private theorem normalizedHomologyIso_naturality
    {K L : SSet.{u}} (f : K ⟶ L) :
    HomologicalComplex.homologyMap
        (SSet.normalizedChainComplexMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2 ≫
      (L.normalizedHomologyIso (C := AddCommGrpCat.{u})
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom =
    (K.normalizedHomologyIso (C := AddCommGrpCat.{u})
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
        SSet.homologyMap f
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2 := by
  let R := (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
  have h := (SSet.homologyNatIso_fromNormalizedChainComplex
    (C := AddCommGrpCat.{u}) R 2).hom.naturality f
  change HomologicalComplex.homologyMap (SSet.normalizedChainComplexMap f R) 2 ≫
      HomologicalComplex.homologyMap (L.fromNormalizedChainComplex R) 2 =
    HomologicalComplex.homologyMap (K.fromNormalizedChainComplex R) 2 ≫
      SSet.homologyMap f R 2 at h
  simpa only [SSet.normalizedHomologyIso_hom] using h

private theorem rawBoundaryTwoClass_map
    {K : SSet.{u}} {x : K _⦋0⦌} (p : K.PtSimplex 2 x) :
    normalizedBoundaryTwoClass.{u} ≫
        (boundaryThree.normalizedHomologyIso (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
      SSet.homologyMap (oneFaceBoundaryMap p)
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2 =
    SSet.pointedTwoHomologyClass p ≫
      (K.normalizedHomologyIso (C := AddCommGrpCat.{u})
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom := by
  rw [← normalizedHomologyIso_naturality (oneFaceBoundaryMap p),
    ← Category.assoc, normalizedBoundaryTwoClass_map]

end ClassicalSphereCalibration

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private abbrev homologyTwoFunctor : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
  (singularHomologyFunctor AddCommGrpCat.{u} 2).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u})

private def boundaryThreeSphereIso :
    SSet.toTop.obj boundaryThree.{u} ≅ TopCat.sphere.{u} 2 :=
  SSet.boundary.toTopDiskBoundaryIso 3

private def boundaryThreeClassicalIso :
    SSet.toTop.obj boundaryThree.{u} ≅
      (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd :=
  boundaryThreeSphereIso ≪≫
    TopCat.isoOfHomeo (Topology.CWComplex.classicalCellBoundarySphereHomeomorph.{u} 2).symm

private def boundaryNormalizedHomologyCoordinate :
    boundaryNormalizedComplex.{u}.homology 2 ≅
      (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  boundaryThree.normalizedHomologyIso (C := AddCommGrpCat.{u})
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2 ≪≫
    SSet.realizationSingularHomologyIso
      (singularIntegralCoefficients : AddCommGrpCat.{u}) boundaryThree 2 ≪≫
    homologyTwoFunctor.mapIso boundaryThreeSphereIso ≪≫
    ((reducedSingularHomologyFunctorIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2 (by decide)).app
        (TopCat.sphere.{u} 2)).symm ≪≫
    reducedSphereHomologyIsoOfUnivLE.{u, u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2

private theorem normalizedBoundaryTwoClass_isIso :
    IsIso normalizedBoundaryTwoClass.{u} :=
  integralGenerator_isIso_of_retraction boundaryNormalizedHomologyCoordinate
    normalizedBoundaryTwoClass boundaryHomologyCoefficient
    normalizedBoundaryTwoClass_coefficient

private def boundarySingularTwoClass :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      homologyTwoFunctor.obj (SSet.toTop.obj boundaryThree.{u}) :=
  normalizedBoundaryTwoClass ≫
    (boundaryThree.normalizedHomologyIso (C := AddCommGrpCat.{u})
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
        (SSet.realizationSingularHomologyIso
          (singularIntegralCoefficients : AddCommGrpCat.{u}) boundaryThree 2).hom

private theorem boundarySingularTwoClass_isIso :
    IsIso boundarySingularTwoClass.{u} := by
  have : IsIso normalizedBoundaryTwoClass.{u} := normalizedBoundaryTwoClass_isIso.{u}
  dsimp only [boundarySingularTwoClass]
  infer_instance

private def classicalBoundaryTwoCycleClass :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      homologyTwoFunctor.obj (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd :=
  boundarySingularTwoClass ≫ homologyTwoFunctor.map boundaryThreeClassicalIso.hom

private theorem classicalBoundaryTwoCycleClass_isIso :
    IsIso classicalBoundaryTwoCycleClass.{u} := by
  have : IsIso boundarySingularTwoClass.{u} := boundarySingularTwoClass_isIso.{u}
  dsimp only [classicalBoundaryTwoCycleClass]
  infer_instance

end ClassicalSphereCalibration

namespace Topology.CWComplex

/-- The original integral relative 3-disk generator, followed by the actual
pair boundary and the canonical return to natural grading. -/
def classicalCellBoundaryHomologyTwoGenerator :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
          (classicalCellDiskPair.{u} 3).snd) :=
  (classicalCellDiskPairRelativeHomologyIntIso.{u, u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).hom ≫
    (singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3
        (classicalCellDiskPair.{u} 3) ≫
    ((singularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
        (classicalCellDiskPair.{u} 3).snd).hom

/-- This generator uses the unchanged natural-graded relative disk coordinate. -/
theorem classicalCellBoundaryHomologyTwoGenerator_eq_original_boundary :
    classicalCellBoundaryHomologyTwoGenerator.{u} =
      (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).hom ≫
      ((relativeSingularHomologyNatToIntIso AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 3).app
          (classicalCellDiskPair.{u} 3)).inv ≫
      (singularHomologyIntData AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3
          (classicalCellDiskPair.{u} 3) ≫
      ((singularHomologyNatToIntIso AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).app
          (classicalCellDiskPair.{u} 3).snd).hom := by
  rfl

private theorem classicalThreeDisk_absoluteInt_isZero
    (k : ℕ) (hk : k ≠ 0) :
    IsZero ((singularHomologyIntFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) (k : ℤ)).obj
        (classicalCellDiskPair.{u} 3).fst) := by
  let : ContractibleSpace (classicalCellDiskPair.{u} 3).fst :=
    contractibleSpace_classicalCellDiskPair_fst 3
  have hNat : IsZero
      (((singularHomologyFunctor AddCommGrpCat.{u} k).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
          (classicalCellDiskPair.{u} 3).fst) :=
    isZero_singularHomology_of_contractible AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) k hk
        (classicalCellDiskPair.{u} 3).fst
  exact hNat.of_iso
    ((singularHomologyNatToIntIso AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) k).app
        (classicalCellDiskPair.{u} 3).fst)

private theorem classicalThreeDisk_boundary_isIso :
    IsIso ((singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3
        (classicalCellDiskPair.{u} 3)) := by
  let E := singularHomologyIntData AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u})
  let P := classicalCellDiskPair.{u} 3
  have hz3 : IsZero ((E.H 3).obj P.fst) :=
    classicalThreeDisk_absoluteInt_isZero 3 (by decide)
  have hz2 : IsZero ((E.H 2).obj P.fst) :=
    classicalThreeDisk_absoluteInt_isZero 2 (by decide)
  have hTo : E.toRelative 3 P = 0 := hz3.eq_of_src _ _
  have hSub : E.subspaceMap 2 P = 0 := hz2.eq_of_tgt _ _
  have : Mono (E.boundary 3 P) :=
      (TopPair.HomologyTheoryData.IsExact.exact_toRelative_boundary E 3 P).mono_g hTo
  have : Epi (E.boundary 3 P) :=
      (TopPair.HomologyTheoryData.IsExact.exact_boundary_subspaceMap E 3 P).epi_f hSub
  exact isIso_of_mono_of_epi (E.boundary 3 P)

/-- The actual boundary of the fixed relative 3-disk generator is a generator
of integral H2 of the literal classical sphere. -/
theorem classicalCellBoundaryHomologyTwoGenerator_isIso :
    IsIso classicalCellBoundaryHomologyTwoGenerator.{u} := by
  have : IsIso ((singularHomologyIntData AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 3
        (classicalCellDiskPair.{u} 3)) := classicalThreeDisk_boundary_isIso.{u}
  dsimp only [classicalCellBoundaryHomologyTwoGenerator]
  infer_instance

end Topology.CWComplex

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private def realizedOneFaceMap (Y : TopCat.{u})
    {x : (TopCat.toSSet.obj Y) _⦋0⦌}
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 x) :
    SSet.toTop.obj boundaryThree.{u} ⟶ Y :=
  SSet.toTop.map (oneFaceBoundaryMap p) ≫ sSetTopAdj.counit.app Y

private theorem realizedOneFaceMap_unit (Y : TopCat.{u})
    {x : (TopCat.toSSet.obj Y) _⦋0⦌}
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 x) :
    sSetTopAdj.unit.app boundaryThree.{u} ≫
      TopCat.toSSet.map (realizedOneFaceMap Y p) = oneFaceBoundaryMap p := by
  have h := sSetTopAdj.unit.naturality (oneFaceBoundaryMap p)
  change oneFaceBoundaryMap p ≫ sSetTopAdj.unit.app (TopCat.toSSet.obj Y) =
    sSetTopAdj.unit.app boundaryThree ≫
      TopCat.toSSet.map (SSet.toTop.map (oneFaceBoundaryMap p)) at h
  dsimp only [realizedOneFaceMap]
  rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc,
    sSetTopAdj.right_triangle_components, Category.comp_id]

private theorem boundarySingularTwoClass_map (Y : TopCat.{u})
    {x : (TopCat.toSSet.obj Y) _⦋0⦌}
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 x) :
    boundarySingularTwoClass.{u} ≫ homologyTwoFunctor.map (realizedOneFaceMap Y p) =
      SSet.pointedTwoHomologyClass p ≫
        ((TopCat.toSSet.obj Y).normalizedHomologyIso (C := AddCommGrpCat.{u})
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom := by
  let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := homologyTwoFunctor
  let e := boundaryThree.normalizedHomologyIso (C := AddCommGrpCat.{u}) R 2
  let F := realizedOneFaceMap Y p
  have hH : SSet.homologyMap (sSetTopAdj.unit.app boundaryThree.{u}) R 2 ≫ H.map F =
      SSet.homologyMap (oneFaceBoundaryMap p) R 2 := by
    change SSet.homologyMap (sSetTopAdj.unit.app boundaryThree) R 2 ≫
        SSet.homologyMap (TopCat.toSSet.map F) R 2 =
      SSet.homologyMap (oneFaceBoundaryMap p) R 2
    rw [← SSet.homologyMap_comp, realizedOneFaceMap_unit]
  have h₀ : boundarySingularTwoClass.{u} ≫ H.map F =
      (normalizedBoundaryTwoClass.{u} ≫ e.hom) ≫
        (SSet.homologyMap (sSetTopAdj.unit.app boundaryThree.{u}) R 2 ≫ H.map F) := by
    let f := normalizedBoundaryTwoClass.{u}
    let a := (boundaryThree.normalizedHomologyIso (C := AddCommGrpCat.{u}) R 2).hom
    let b := SSet.homologyMap (sSetTopAdj.unit.app boundaryThree.{u}) R 2
    let g := H.map F
    have hDefinition : boundarySingularTwoClass.{u} = f ≫ (a ≫ b) := by
      dsimp only [f, a, b, R]
      simp only [boundarySingularTwoClass, SSet.realizationSingularHomologyIso_hom]
      rfl
    have hLeft : boundarySingularTwoClass.{u} ≫ g = (f ≫ (a ≫ b)) ≫ g :=
      congrArg (fun k => k ≫ g) hDefinition
    have hAssoc : (f ≫ (a ≫ b)) ≫ g = (f ≫ a) ≫ (b ≫ g) :=
      ((Category.assoc f (a ≫ b) g).trans
        (congrArg (fun k => f ≫ k) (Category.assoc a b g))).trans
          (Category.assoc f a (b ≫ g)).symm
    exact hLeft.trans hAssoc
  have h₁ : (normalizedBoundaryTwoClass.{u} ≫ e.hom) ≫
        (SSet.homologyMap (sSetTopAdj.unit.app boundaryThree.{u}) R 2 ≫ H.map F) =
      (normalizedBoundaryTwoClass.{u} ≫ e.hom) ≫
        SSet.homologyMap (oneFaceBoundaryMap p) R 2 :=
    congrArg (fun k => (normalizedBoundaryTwoClass.{u} ≫ e.hom) ≫ k) hH
  have h₂ : (normalizedBoundaryTwoClass.{u} ≫ e.hom) ≫
        SSet.homologyMap (oneFaceBoundaryMap p) R 2 =
      SSet.pointedTwoHomologyClass p ≫
        ((TopCat.toSSet.obj Y).normalizedHomologyIso (C := AddCommGrpCat.{u}) R 2).hom :=
    (Category.assoc normalizedBoundaryTwoClass e.hom
      (SSet.homologyMap (oneFaceBoundaryMap p) R 2)).trans (rawBoundaryTwoClass_map p)
  exact h₀.trans (h₁.trans h₂)

private def classicalOneFaceMap (Y : TopCat.{u})
    {x : (TopCat.toSSet.obj Y) _⦋0⦌}
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 x) :
    (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd ⟶ Y :=
  boundaryThreeClassicalIso.inv ≫ realizedOneFaceMap Y p

private theorem classicalBoundaryTwoCycleClass_map (Y : TopCat.{u})
    {x : (TopCat.toSSet.obj Y) _⦋0⦌}
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 x) :
    classicalBoundaryTwoCycleClass.{u} ≫ homologyTwoFunctor.map (classicalOneFaceMap Y p) =
      SSet.pointedTwoHomologyClass p ≫
        ((TopCat.toSSet.obj Y).normalizedHomologyIso (C := AddCommGrpCat.{u})
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := homologyTwoFunctor
  let e : SSet.toTop.obj boundaryThree.{u} ≅
      (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd := boundaryThreeClassicalIso
  let F := realizedOneFaceMap Y p
  have hInv : H.map e.hom ≫ H.map e.inv = 𝟙 (H.obj (SSet.toTop.obj boundaryThree.{u})) := by
    rw [← H.map_comp, e.hom_inv_id, H.map_id]
  have h₀ : classicalBoundaryTwoCycleClass.{u} ≫ H.map (classicalOneFaceMap Y p) =
      (boundarySingularTwoClass.{u} ≫ (H.map e.hom ≫ H.map e.inv)) ≫ H.map F := by
    dsimp only [H, e, F]
    simp only [classicalBoundaryTwoCycleClass, classicalOneFaceMap,
      homologyTwoFunctor.map_comp, Category.assoc]
  have h₁ : (boundarySingularTwoClass.{u} ≫ (H.map e.hom ≫ H.map e.inv)) ≫ H.map F =
      boundarySingularTwoClass.{u} ≫ H.map F := by
    rw [hInv, Category.comp_id]
  have h₂ : boundarySingularTwoClass.{u} ≫ H.map F =
      SSet.pointedTwoHomologyClass p ≫
        ((TopCat.toSSet.obj Y).normalizedHomologyIso (C := AddCommGrpCat.{u})
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom :=
    boundarySingularTwoClass_map Y p
  exact h₀.trans (h₁.trans h₂)

private def singularPiOneEquiv (Y : TopCat.{u}) (y : Y) :
    SSet.KanComplex.π 1 (TopCat.toSSet.obj Y) (TopCat.toSSetObj₀Equiv.symm y) ≃*
      FundamentalGroup Y y :=
  (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
    (TopCat.toSSetObj₀Equiv.symm y)).trans
      (TopCat.singularFundamentalGroupoidEndMulEquiv Y y)

private theorem singularPiOne_subsingleton (Y : TopCat.{u}) (y : Y)
    [Subsingleton (FundamentalGroup Y y)] :
    Subsingleton (SSet.KanComplex.π 1 (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y)) := by
  constructor
  intro a b
  apply (singularPiOneEquiv Y y).injective
  exact Subsingleton.elim _ _

private def classicalSphereMapForCycle (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (h : (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶ homologyTwoFunctor.obj Y) :
    (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd ⟶ Y := by
  letI : Subsingleton (SSet.KanComplex.π 1 (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := singularPiOne_subsingleton Y y
  exact classicalOneFaceMap Y
    (pointedTwoRepresentative (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y) (h (ULift.up (1 : ℤ))))

private theorem classicalSphereMapForCycle_class (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (h : (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶ homologyTwoFunctor.obj Y) :
    classicalBoundaryTwoCycleClass.{u} ≫
      homologyTwoFunctor.map (classicalSphereMapForCycle Y y h) = h := by
  let : Subsingleton (SSet.KanComplex.π 1 (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)) := singularPiOne_subsingleton Y y
  let p := pointedTwoRepresentative (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y) (h (ULift.up (1 : ℤ)))
  apply integralHom_ext
  have hMap := ConcreteCategory.congr_hom (classicalBoundaryTwoCycleClass_map Y p)
    (ULift.up (1 : ℤ))
  have hClass := pointedTwoRepresentative_class (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y) (h (ULift.up (1 : ℤ)))
  change (classicalBoundaryTwoCycleClass ≫
    homologyTwoFunctor.map (classicalOneFaceMap Y p)) (ULift.up (1 : ℤ)) =
      h (ULift.up (1 : ℤ))
  exact hMap.trans hClass

end ClassicalSphereCalibration

namespace ClassicalSphereCalibration

attribute [local instance] TopCat.toSSet_obj_kanComplex

private def integralClassHom (A : AddCommGrpCat.{u}) (z : A) :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun a => a.down • z
      map_zero' := by simp
      map_add' := by
        intro a b
        change (a.down + b.down) • z = a.down • z + b.down • z
        exact add_zsmul z a.down b.down }

private def fixedGeneratorCoefficientIso :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ≅
      (singularIntegralCoefficients : AddCommGrpCat.{u}) := by
  haveI : IsIso Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{u} :=
    Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator_isIso
  haveI : IsIso classicalBoundaryTwoCycleClass.{u} := classicalBoundaryTwoCycleClass_isIso
  exact asIso Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≪≫
    (asIso classicalBoundaryTwoCycleClass).symm

private theorem fixedGeneratorCoefficientIso_cycle :
    fixedGeneratorCoefficientIso.{u}.hom ≫ classicalBoundaryTwoCycleClass =
      Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator := by
  have : IsIso classicalBoundaryTwoCycleClass.{u} := classicalBoundaryTwoCycleClass_isIso
  change (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫
    (asIso classicalBoundaryTwoCycleClass).inv) ≫ classicalBoundaryTwoCycleClass = _
  have hInv : (asIso classicalBoundaryTwoCycleClass).inv ≫
      classicalBoundaryTwoCycleClass =
        𝟙 (homologyTwoFunctor.obj (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd) :=
    (asIso classicalBoundaryTwoCycleClass).inv_hom_id
  rw [Category.assoc, hInv, Category.comp_id]

private def fixedSphereMap (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : homologyTwoFunctor.obj Y) :
    (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd ⟶ Y :=
  classicalSphereMapForCycle Y y
    (fixedGeneratorCoefficientIso.inv ≫ integralClassHom _ z)

private theorem fixedSphereMap_map (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : homologyTwoFunctor.obj Y) :
    Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      homologyTwoFunctor.map (fixedSphereMap Y y z) = integralClassHom _ z := by
  let d := fixedGeneratorCoefficientIso.{u}
  have hd : d.hom ≫ classicalBoundaryTwoCycleClass =
      Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator :=
    fixedGeneratorCoefficientIso_cycle
  change Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫
      homologyTwoFunctor.map
        (classicalSphereMapForCycle Y y (d.inv ≫ integralClassHom _ z)) = _
  rw [← hd, Category.assoc, classicalSphereMapForCycle_class]
  exact d.hom_inv_id_assoc _

end ClassicalSphereCalibration

namespace TopCat

/-- A continuous spherical representative of any integral H2 class on an
ordinary path-connected space with trivial based fundamental group. The
source is the literal boundary of the original classical 3-disk. -/
def classicalSphereHomologyTwoRepresentative (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj Y)) :
    (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd ⟶ Y := by
  exact ClassicalSphereCalibration.fixedSphereMap Y y z

/-- Every integral multiple of the fixed disk-boundary generator is sent
to the same multiple of the prescribed class by the actual representative. -/
theorem classicalSphereHomologyTwoRepresentative_homology
    (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj Y))
    (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map
          (classicalSphereHomologyTwoRepresentative Y y z))) a = a.down • z := by
  change (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator ≫
    ClassicalSphereCalibration.homologyTwoFunctor.map
      (ClassicalSphereCalibration.fixedSphereMap Y y z)) a = a.down • z
  exact ConcreteCategory.congr_hom (ClassicalSphereCalibration.fixedSphereMap_map Y y z) a

/-- The unchanged relative 3-disk boundary generator represents the
prescribed class under the constructed actual sphere map. -/
theorem classicalSphereHomologyTwoRepresentative_value
    (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj Y)) :
    (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map
          (classicalSphereHomologyTwoRepresentative Y y z))) (ULift.up (1 : ℤ)) = z := by
  simpa only [ULift.down_up, one_zsmul] using
    classicalSphereHomologyTwoRepresentative_homology Y y z (ULift.up (1 : ℤ))

/-- Integral degree2 Hurewicz surjectivity as actual continuous maps from
the fixed classical sphere, with no supplied spherical representative. -/
theorem exists_classicalSphereHomologyTwo_representative
    (Y : TopCat.{u}) (y : Y)
    [PathConnectedSpace Y] [Subsingleton (FundamentalGroup Y y)]
    (z : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj Y)) :
    ∃ f : (Topology.CWComplex.classicalCellDiskPair.{u} 3).snd ⟶ Y,
      (Topology.CWComplex.classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map f))
            (ULift.up (1 : ℤ)) = z := by
  exact ⟨classicalSphereHomologyTwoRepresentative Y y z,
    classicalSphereHomologyTwoRepresentative_value Y y z⟩

end TopCat

end
