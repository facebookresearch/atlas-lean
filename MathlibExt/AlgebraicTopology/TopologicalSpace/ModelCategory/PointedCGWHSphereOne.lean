/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoop
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CGWHRealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMap
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHFunctorialFactorizations
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
public import MathlibExt.Topology.Category.PointedCGWH.SuspensionLoop
public import MathlibExt.Topology.Category.PointedCGWH.Zero

/-!
# The one-sphere coordinate in the pointed CGWH model category

The native one-sphere is cofibrant, so fixed-left smash by it is a left
Quillen functor with based internal Hom as right adjoint.  The ordinary disk
cofiber supplies a forward weak cospan from the chosen derived suspension of
the smash unit to the one-sphere, and hence an isomorphism after formal
localization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory Simplicial ZeroObject

namespace PointedCGWH.modelCategory

set_option linter.flexible false in
private noncomputable def diskBoundaryRealizationData :
    {e : SSet.toCGWH.{u, v}.obj (SSet.boundary.{v} 1) ≅
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v} //
      e.inv ≫ SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι =
        PointedCGWH.diskBoundary.{u, v}.right} := by
  let eS : (SSet.boundary.{v} 1 : SSet.{v}) ≅
      ((Δ[0] : SSet.{v}) ⨿ (Δ[0] : SSet.{v})) :=
    { hom := SSet.boundaryOneMap
        (SSet.yonedaEquiv (coprod.inr :
          (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0]))
        (SSet.yonedaEquiv (coprod.inl :
          (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0]))
      inv := coprod.desc (SSet.boundary.ι (0 : Fin 2))
        (SSet.boundary.ι (1 : Fin 2))
      hom_inv_id := by
        apply SSet.boundary.hom_ext
        intro i
        fin_cases i
        · change (SSet.boundary.ι (0 : Fin 2) ≫
              SSet.boundaryOneMap _ _) ≫ _ =
            SSet.boundary.ι (0 : Fin 2) ≫ 𝟙 _
          rw [SSet.boundary_ι_zero_boundaryOneMap]
          have h : SSet.const (SSet.yonedaEquiv (coprod.inl :
              (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0])) =
              (coprod.inl : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) := by
            rw [← SSet.yonedaEquiv_symm_zero]
            exact Equiv.symm_apply_apply _ _
          rw [h, Limits.coprod.inl_desc, Category.comp_id]
        · change (SSet.boundary.ι (1 : Fin 2) ≫
              SSet.boundaryOneMap _ _) ≫ _ =
            SSet.boundary.ι (1 : Fin 2) ≫ 𝟙 _
          rw [SSet.boundary_ι_one_boundaryOneMap]
          have h : SSet.const (SSet.yonedaEquiv (coprod.inr :
              (Δ[0] : SSet.{v}) ⟶ (Δ[0] : SSet.{v}) ⨿ Δ[0])) =
              (coprod.inr : (Δ[0] : SSet.{v}) ⟶ Δ[0] ⨿ Δ[0]) := by
            rw [← SSet.yonedaEquiv_symm_zero]
            exact Equiv.symm_apply_apply _ _
          rw [h, Limits.coprod.inr_desc, Category.comp_id]
      inv_hom_id := by
        apply Limits.coprod.hom_ext
        · rw [← Category.assoc, Limits.coprod.inl_desc,
            SSet.boundary_ι_zero_boundaryOneMap]
          rw [← SSet.yonedaEquiv_symm_zero]
          rw [Equiv.symm_apply_apply, Category.comp_id]
        · rw [← Category.assoc, Limits.coprod.inr_desc,
            SSet.boundary_ι_one_boundaryOneMap]
          rw [← SSet.yonedaEquiv_symm_zero]
          rw [Equiv.symm_apply_apply, Category.comp_id] }
  let _ : PreservesColimits SSet.toCGWH.{u, v} :=
    SSet.sSetCGWHAdj.leftAdjoint_preservesColimits
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  let e := SSet.toCGWH.mapIso eS ≪≫
      preservesColimitIso SSet.toCGWH.{u, v}
        (pair (Δ[0] : SSet.{v}) Δ[0]) ≪≫
      HasColimit.isoOfNatIso
        (pairComp (Δ[0] : SSet.{v}) Δ[0] SSet.toCGWH.{u, v}) ≪≫
      coprod.mapIso e₀ e₀
  have h₀ : (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
        e₀.inv ≫ SSet.toCGWH.{u, v}.map
          (SSet.boundary.ι (0 : Fin 2)) := by
    change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2))
    simp [e, eS, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (0 : Fin 2)) = _
    rw [Category.id_comp]
  have h₁ : (coprod.inr : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv =
        e₀.inv ≫ SSet.toCGWH.{u, v}.map
          (SSet.boundary.ι (1 : Fin 2)) := by
    change _ = e₀.inv ≫
      SSet.toCGWH.{u, v}.map (SSet.boundary.ι (1 : Fin 2))
    simp [e, eS, e₀]
    change 𝟙 _ ≫ SSet.toCGWH.{u, v}.map
      (SSet.boundary.ι (1 : Fin 2)) = _
    rw [Category.id_comp]
  refine ⟨e, ?_⟩
  apply Limits.coprod.hom_ext
  · calc
      _ = ((coprod.inl : CGWH.point.{u, v} ⟶
            CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv) ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι :=
        (Category.assoc _ _ _).symm
      _ = (e₀.inv ≫ SSet.toCGWH.{u, v}.map
            (SSet.boundary.ι (0 : Fin 2))) ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι := by
        rw [h₀]
      _ = e₀.inv ≫ SSet.toCGWH.{u, v}.map
          (SSet.stdSimplex.δ (0 : Fin 2)) := by
        rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
      _ = _ := (Limits.coprod.inl_desc _ _).symm
  · calc
      _ = ((coprod.inr : CGWH.point.{u, v} ⟶
            CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) ≫ e.inv) ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι :=
        (Category.assoc _ _ _).symm
      _ = (e₀.inv ≫ SSet.toCGWH.{u, v}.map
            (SSet.boundary.ι (1 : Fin 2))) ≫
          SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι := by
        rw [h₁]
      _ = e₀.inv ≫ SSet.toCGWH.{u, v}.map
          (SSet.stdSimplex.δ (1 : Fin 2)) := by
        rw [Category.assoc, ← Functor.map_comp, SSet.boundary.ι_ι]
      _ = _ := (Limits.coprod.inr_desc _ _).symm

/-- The ordered boundary inclusion of the native one-disk is a pointed
cofibration. -/
theorem diskBoundary_cofibration :
    Cofibration PointedCGWH.diskBoundary.{u, v} := by
  let d := diskBoundaryRealizationData.{u, v}
  have hi := CGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp _
    (CGWH.boundary_mem_realizedBoundaryInclusions 1)
  change CGWH.cofibrantGenerationData.{u, v}.I.rlp.llp
    (CGWH.realizedBoundaryInclusion.{v, u} 1) at hi
  rw [CGWH.cofibrantGenerationData.I_rlp,
    trivialFibrations_llp] at hi
  have hcomp : cofibrations CGWH.{u, v}
      (d.1.inv ≫ SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι) :=
    (cofibrations CGWH.{u, v}).comp_mem _ _
      (mem_cofibrations d.1.inv) hi
  apply (PointedCGWH.cofibration_iff _).mpr
  apply (HomotopicalAlgebra.cofibration_iff _).mpr
  rw [← d.2]
  exact hcomp

private theorem simplexOneAugmentation_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{v})) := by
  let eT : (⊤_ SSet.{v}) ≅ (Δ[0] : SSet.{v}) :=
    terminalIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  let e : (Δ[1] : SSet.{v}) ≅ (Δ[1] : SSet.{v}) ⨯ Δ[0] :=
    (prod.rightUnitor (Δ[1] : SSet.{v})).symm ≪≫
      prod.mapIso (Iso.refl _) eT
  have hproj :=
    SSet.stdSimplexProdSnd_mem_weakHomotopyEquivalences 1
      (Δ[0] : SSet.{v})
  have h := RespectsIso.precomp TopCat.weakHomotopyEquivalences
    (SSet.toTop.map e.hom)
    (SSet.toTop.map
      (prod.snd : (Δ[1] : SSet.{v}) ⨯ Δ[0] ⟶ Δ[0])) hproj
  change TopCat.weakHomotopyEquivalences
    (SSet.toTop.map
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{v})))
  have he : e.hom ≫
      (prod.snd : (Δ[1] : SSet.{v}) ⨯ Δ[0] ⟶ Δ[0]) =
        SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{v}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simpa only [← SSet.toTop.map_comp, he] using h

private theorem realizedSimplexOneAugmentation_mem_weakHomotopyEquivalences :
    CGWH.weakHomotopyEquivalences
      (SSet.toCGWH.{u, v}.map
        (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{v}))) :=
  SSet.realizationWeakEquivalences_toCGWH
    simplexOneAugmentation_mem_realizationWeakEquivalences

private noncomputable def diskAugmentationComparisonData :
    {e : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
        (⊤_ PointedCGWH.{u, v}).right //
      SSet.toCGWH.{u, v}.map
          (SSet.stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{v})) ≫
        e.hom = PointedCGWH.diskAugmentation.{u, v}.right} := by
  let e₀ : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) ≅
      CGWH.point.{u, v} := by
    change (SSet.toCGWHOfFinite (Δ[0] : SSet.{v}) : CGWH.{u, v}) ≅
      CGWH.point.{u, v}
    exact SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}
  let hT : IsTerminal ((⊤_ PointedCGWH.{u, v}).right) :=
    terminalIsTerminal.isTerminalObj (Under.forget CGWH.point.{u, v})
  let eT : (⊤_ PointedCGWH.{u, v}).right ≅ CGWH.point.{u, v} :=
    hT.uniqueUpToIso CGWH.point_isTerminal
  let e := e₀ ≪≫ eT.symm
  exact ⟨e, hT.hom_ext _ _⟩

private theorem diskAugmentation_right_mem_weakHomotopyEquivalences :
    CGWH.weakHomotopyEquivalences
      PointedCGWH.diskAugmentation.{u, v}.right := by
  let a : (Δ[1] : SSet.{v}) ⟶ Δ[0] :=
    SSet.stdSimplex.isTerminalObj₀.from _
  have hReal : CGWH.weakHomotopyEquivalences
      (SSet.toCGWH.{u, v}.map a) :=
    realizedSimplexOneAugmentation_mem_weakHomotopyEquivalences
  let d := diskAugmentationComparisonData.{u, v}
  have hReal' : weakEquivalences CGWH.{u, v}
      (SSet.toCGWH.{u, v}.map a) := hReal
  have hcomp : weakEquivalences CGWH.{u, v}
      (SSet.toCGWH.{u, v}.map a ≫ d.1.hom) :=
    (weakEquivalences CGWH.{u, v}).comp_mem _ _ hReal'
      (mem_weakEquivalences d.1.hom)
  rw [d.2] at hcomp
  exact hcomp

/-- Collapsing the native one-disk to the pointed zero object is a weak
equivalence. -/
theorem diskAugmentation_weakEquivalence :
    WeakEquivalence PointedCGWH.diskAugmentation.{u, v} := by
  apply (PointedCGWH.weakEquivalence_iff _).mpr
  apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
  exact diskAugmentation_right_mem_weakHomotopyEquivalences

/-- The native pointed CGWH one-sphere is cofibrant. -/
theorem sphereOne_isCofibrant :
    IsCofibrant PointedCGWH.sphereOne.{u, v} := by
  rw [PointedCGWH.isCofibrant_iff]
  have hi := CGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp _
    (CGWH.boundary_mem_realizedBoundaryInclusions 1)
  change CGWH.cofibrantGenerationData.{u, v}.I.rlp.llp
    (CGWH.realizedBoundaryInclusion.{v, u} 1) at hi
  rw [CGWH.cofibrantGenerationData.I_rlp,
    trivialFibrations_llp] at hi
  change cofibrations CGWH.{u, v}
    (pushout.inr (SSet.toCGWH.{u, v}.map (SSet.boundary.{v} 1).ι)
      (CGWH.point_isTerminal.from _))
  exact (cofibrations CGWH.{u, v}).pushout_inr _ _ hi

end PointedCGWH.modelCategory

namespace CGWH.modelCategory

/-- In the selected pointed CGWH model, strict suspension and loops form a
Quillen adjunction. -/
noncomputable scoped instance
    instPointedCGWHSuspensionLoopIsQuillenAdjunction :
    PointedCGWH.suspensionLoopAdjunction.{u, v}.IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact
    HomotopicalAlgebra.ihomAdjunction_isQuillenAdjunction_of_isCofibrant
      PointedCGWH.sphereOne.{u, v}

end CGWH.modelCategory

namespace PointedCGWH.modelCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original disk cofiber maps weakly to both the actual derived suspension and one-sphere. -/
private noncomputable def derivedSuspensionSphereZeroCospan :
    {p :
        ((homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          (derivedSuspension (C := PointedCGWH.{u, v})).obj
            PointedCGWH.sphereZero) ×
        ((homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          PointedCGWH.sphereOne) //
      WeakEquivalence p.1 ∧ WeakEquivalence p.2} := by
  let S0 : PointedCGWH.{u, v} :=
    Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
  let eS0 : PointedCGWH.sphereZero.{u, v} ≅ S0 :=
    Under.isoMk (Iso.refl _) (by
      dsimp [S0, PointedCGWH.sphereZero,
        CategoryTheory.Pointed.smashUnit]
      simp)
  let zT := HasZeroObject.zeroIsoTerminal (C := PointedCGWH.{u, v})
  let sq : CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v} ⟶
      CategoryTheory.Arrow.mk (HasZeroObject.zeroIsTerminal.from
        PointedCGWH.sphereZero.{u, v}) :=
    Arrow.homMk
      (f := CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v})
      (g := CategoryTheory.Arrow.mk (HasZeroObject.zeroIsTerminal.from
        PointedCGWH.sphereZero.{u, v}))
      eS0.inv
      (PointedCGWH.diskAugmentation ≫ zT.inv) (by
        apply HasZeroObject.zeroIsTerminal.hom_ext)
  let hD :
      (homotopyCofiber (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
        (derivedSuspension (C := PointedCGWH.{u, v})).obj
          PointedCGWH.sphereZero :=
    (homotopyCofiber (C := PointedCGWH.{u, v})).map sq
  have hDWeak : WeakEquivalence hD := by
    apply homotopyCofiber_map_weakEquivalence sq
    · change WeakEquivalence eS0.inv
      rw [HomotopicalAlgebra.weakEquivalence_iff]
      exact mem_weakEquivalences eS0.inv
    · change WeakEquivalence
        (PointedCGWH.diskAugmentation.{u, v} ≫ zT.inv)
      rw [HomotopicalAlgebra.weakEquivalence_iff]
      exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
        diskAugmentation_weakEquivalence.mem
        (mem_weakEquivalences zT.inv)
  let hS :
      (homotopyCofiber (C := PointedCGWH.{u, v})).obj
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
        PointedCGWH.sphereOne :=
    (homotopyCofiberComparison (C := PointedCGWH.{u, v})).app
        (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ≫
      PointedCGWH.diskCofiberIsoSphereOne.hom
  let _ : IsCofibrant PointedCGWH.sphereZero.{u, v} :=
    PointedCGWH.modelCategory.smashUnit_isCofibrant
  have hS0 : IsCofibrant S0 := by
    rw [isCofibrant_iff_of_isInitial
      (initial.to PointedCGWH.sphereZero.{u, v} ≫ eS0.hom)
      initialIsInitial]
    infer_instance
  let _ : IsCofibrant
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left := by
    change IsCofibrant S0
    exact hS0
  let _ : Cofibration
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).hom := by
    change Cofibration PointedCGWH.diskBoundary.{u, v}
    exact diskBoundary_cofibration
  have hComparison : WeakEquivalence
      ((homotopyCofiberComparison (C := PointedCGWH.{u, v})).app
        (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)) :=
    weakEquivalence_homotopyCofiberComparison_of_pointedCofibration
      (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)
  have hSWeak : WeakEquivalence hS := by
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
      hComparison.mem
      (mem_weakEquivalences
        PointedCGWH.diskCofiberIsoSphereOne.{u, v}.hom)
  exact ⟨(hD, hS), hDWeak, hSWeak⟩

/-- In the formal localization, the chosen derived suspension of the smash
unit is canonically isomorphic to the native one-sphere. -/
noncomputable def derivedSuspensionSphereZeroIso :
    (weakEquivalences PointedCGWH.{u, v}).Q.obj
        ((derivedSuspension (C := PointedCGWH.{u, v})).obj
          PointedCGWH.sphereZero) ≅
      (weakEquivalences PointedCGWH.{u, v}).Q.obj
        PointedCGWH.sphereOne := by
  let d :
    {p :
        ((homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          (derivedSuspension (C := PointedCGWH.{u, v})).obj
            PointedCGWH.sphereZero) ×
        ((homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          PointedCGWH.sphereOne) //
      WeakEquivalence p.1 ∧ WeakEquivalence p.2} := by
    let S0 : PointedCGWH.{u, v} :=
      Under.mk (coprod.inl : CGWH.point.{u, v} ⟶
        CGWH.point.{u, v} ⨿ CGWH.point.{u, v})
    let eS0 : PointedCGWH.sphereZero.{u, v} ≅ S0 :=
      Under.isoMk (Iso.refl _) (by
        exact (CategoryTheory.Under.w
          (𝟙 ((Under.costar CGWH.point.{u, v}).obj CGWH.point.{u, v}))).trans
          ((CategoryTheory.Under.costar_obj_hom CGWH.point.{u, v}
            CGWH.point.{u, v}).trans (coprod.inl_desc _ _)))
    let zT := HasZeroObject.zeroIsoTerminal (C := PointedCGWH.{u, v})
    let sq : CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v} ⟶
        CategoryTheory.Arrow.mk (HasZeroObject.zeroIsTerminal.from
          PointedCGWH.sphereZero.{u, v}) :=
      Arrow.homMk
        (f := CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v})
        (g := CategoryTheory.Arrow.mk (HasZeroObject.zeroIsTerminal.from
          PointedCGWH.sphereZero.{u, v}))
        eS0.inv
        (PointedCGWH.diskAugmentation ≫ zT.inv) (by
          apply HasZeroObject.zeroIsTerminal.hom_ext)
    let hD :
        (homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          (derivedSuspension (C := PointedCGWH.{u, v})).obj
            PointedCGWH.sphereZero :=
      (homotopyCofiber (C := PointedCGWH.{u, v})).map sq
    have hDWeak : WeakEquivalence hD := by
      apply homotopyCofiber_map_weakEquivalence sq
      · change WeakEquivalence eS0.inv
        rw [HomotopicalAlgebra.weakEquivalence_iff]
        exact mem_weakEquivalences eS0.inv
      · change WeakEquivalence
          (PointedCGWH.diskAugmentation.{u, v} ≫ zT.inv)
        rw [HomotopicalAlgebra.weakEquivalence_iff]
        exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
          diskAugmentation_weakEquivalence.mem
          (mem_weakEquivalences zT.inv)
    let hS :
        (homotopyCofiber (C := PointedCGWH.{u, v})).obj
            (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ⟶
          PointedCGWH.sphereOne :=
      (homotopyCofiberComparison (C := PointedCGWH.{u, v})).app
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary) ≫
        PointedCGWH.diskCofiberIsoSphereOne.hom
    let _ : IsCofibrant PointedCGWH.sphereZero.{u, v} :=
      PointedCGWH.modelCategory.smashUnit_isCofibrant
    have hS0 : IsCofibrant S0 := by
      rw [isCofibrant_iff_of_isInitial
        (initial.to PointedCGWH.sphereZero.{u, v} ≫ eS0.hom)
        initialIsInitial]
      infer_instance
    let _ : IsCofibrant
        (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).left := by
      change IsCofibrant S0
      exact hS0
    let _ : Cofibration
        (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary.{u, v}).hom := by
      change Cofibration PointedCGWH.diskBoundary.{u, v}
      exact diskBoundary_cofibration
    have hComparison : WeakEquivalence
        ((homotopyCofiberComparison (C := PointedCGWH.{u, v})).app
          (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)) :=
      weakEquivalence_homotopyCofiberComparison_of_pointedCofibration
        (CategoryTheory.Arrow.mk PointedCGWH.diskBoundary)
    have hSWeak : WeakEquivalence hS := by
      rw [HomotopicalAlgebra.weakEquivalence_iff]
      exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _
        hComparison.mem
        (mem_weakEquivalences
          PointedCGWH.diskCofiberIsoSphereOne.{u, v}.hom)
    exact ⟨(hD, hS), hDWeak, hSWeak⟩
  let Q := (weakEquivalences PointedCGWH.{u, v}).Q
  let _ : IsIso (Q.map d.1.1) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map d.1.1).mp d.2.1.mem
  let _ : IsIso (Q.map d.1.2) :=
    (weakEquivalence_iff_isIso_toHomotopyCategory_map d.1.2).mp d.2.2.mem
  exact (asIso (Q.map d.1.1)).symm ≪≫ asIso (Q.map d.1.2)

end PointedCGWH.modelCategory
