/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.RealizedMonoCofibration
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Continuous Whitehead for realized simplicial sets

Cofibrancy, TopCat fibrancy and the good realized cylinder are derived from
the actual constructions. Model left homotopies are interpreted as continuous
homotopies through that cylinder. The resulting homotopy equivalence keeps
the literal realization of the given weak equivalence as its forward map.
-/

@[expose] public section

universe k

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen TopCat.modelCategory

namespace SSet.RealizationCWUpgrade

/-- Cofibrancy is derived from the actual realized initial monomorphism. -/
theorem realization_isCofibrant (K : SSet.{k}) : IsCofibrant (SSet.toTop.obj K) := by
  have hi : Cofibration (SSet.toTop.map (initial.to K)) := by
    rw [cofibration_iff]
    exact SSet.toTop_map_mem_realizedBoundaryLLP (initial.to K)
  have hInitial : IsInitial (SSet.toTop.obj (⊥_ SSet.{k})) :=
    initialIsInitial.isInitialObj (G := SSet.toTop)
  exact (isCofibrant_iff_of_isInitial (SSet.toTop.map (initial.to K)) hInitial).mpr hi

/-- Realize the actual canonical simplicial cylinder, including its already proved weak leg. -/
def realizedStandardCylinder (K : SSet.{k}) : Cylinder (SSet.toTop.obj K) where
  __ := (SSet.modelCategoryQuillen.standardCylinder K).toPrecylinder.map SSet.toTop
  weakEquivalence_π := by
    let Q := SSet.modelCategoryQuillen.standardCylinder K
    have hp : SSet.realizationWeakEquivalences Q.π :=
      (weakEquivalence_iff (f := Q.π)).mp Q.weakEquivalence_π
    apply (weakEquivalence_iff (f := SSet.toTop.map Q.π)).mpr
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map Q.π)
    exact hp

/-- Its endpoint coproduct is the realized simplicial endpoint mono under the actual Iso. -/
theorem realizedStandardCylinder_isGood (K : SSet.{k}) :
    (realizedStandardCylinder K).IsGood := by
  let Q : Cylinder K := SSet.modelCategoryQuillen.standardCylinder K
  let P : Cylinder (SSet.toTop.obj K) := realizedStandardCylinder K
  let R : TopCat.{k} := SSet.toTop.obj Q.I
  have hP₀ : (SSet.toTop.map Q.i₀ : SSet.toTop.obj K ⟶ R) =
      (P.i₀ : SSet.toTop.obj K ⟶ R) := rfl
  have hP₁ : (SSet.toTop.map Q.i₁ : SSet.toTop.obj K ⟶ R) =
      (P.i₁ : SSet.toTop.obj K ⟶ R) := rfl
  have hP_inl : (SSet.toTop.map Q.i₀ : SSet.toTop.obj K ⟶ R) =
      (coprod.inl : SSet.toTop.obj K ⟶ SSet.toTop.obj K ⨿ SSet.toTop.obj K) ≫
        (P.i : SSet.toTop.obj K ⨿ SSet.toTop.obj K ⟶ R) :=
    hP₀.trans P.toPrecylinder.inl_i.symm
  have hP_inr : (SSet.toTop.map Q.i₁ : SSet.toTop.obj K ⟶ R) =
      (coprod.inr : SSet.toTop.obj K ⟶ SSet.toTop.obj K ⨿ SSet.toTop.obj K) ≫
        (P.i : SSet.toTop.obj K ⨿ SSet.toTop.obj K ⟶ R) :=
    hP₁.trans P.toPrecylinder.inr_i.symm
  let e : SSet.toTop.obj K ⨿ SSet.toTop.obj K ≅ SSet.toTop.obj (K ⨿ K) :=
    PreservesColimitPair.iso SSet.toTop K K
  have he₀ : (coprod.inl : SSet.toTop.obj K ⟶ SSet.toTop.obj K ⨿ SSet.toTop.obj K) ≫
      e.hom = SSet.toTop.map (coprod.inl : K ⟶ K ⨿ K) := by
    simp only [e, PreservesColimitPair.iso_hom, coprodComparison, coprod.inl_desc]
  have he₁ : (coprod.inr : SSet.toTop.obj K ⟶ SSet.toTop.obj K ⨿ SSet.toTop.obj K) ≫
      e.hom = SSet.toTop.map (coprod.inr : K ⟶ K ⨿ K) := by
    simp only [e, PreservesColimitPair.iso_hom, coprodComparison, coprod.inr_desc]
  have hEndpoints :
      (e.hom ≫ SSet.toTop.map Q.i :
        SSet.toTop.obj K ⨿ SSet.toTop.obj K ⟶ R) =
      (P.i : SSet.toTop.obj K ⨿ SSet.toTop.obj K ⟶ R) := by
    apply coprod.hom_ext
    · rw [← Category.assoc, he₀, ← SSet.toTop.map_comp,
        Q.toPrecylinder.inl_i]
      exact hP_inl
    · rw [← Category.assoc, he₁, ← SSet.toTop.map_comp,
        Q.toPrecylinder.inr_i]
      exact hP_inr
  have hm : Mono Q.i :=
    (SSet.modelCategoryQuillen.cofibration_iff Q.i).mp
      (SSet.modelCategoryQuillen.standardCylinder_isGood K).cofibration_i
  have hMapped : Cofibration (SSet.toTop.map Q.i) := by
    rw [cofibration_iff]
    exact @SSet.toTop_map_mem_realizedBoundaryLLP _ _ Q.i hm
  have hIso : Cofibration e.hom := inferInstance
  constructor
  rw [cofibration_iff, ← hEndpoints]
  exact (cofibrations TopCat.{k}).comp_mem e.hom (SSet.toTop.map Q.i)
    ((cofibration_iff e.hom).mp hIso)
    ((cofibration_iff (SSet.toTop.map Q.i)).mp hMapped)

/-- The identity cylinder map is the actual universal endpoint homotopy. -/
def universalCylinderHomotopy (K : SSet.{k}) :
    SSet.Homotopy (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{k})) SSet.ι₁ :=
  SSet.Homotopy.mkOfH (𝟙 (K ⊗ (Δ[1] : SSet.{k})))
    (Category.comp_id _) (Category.comp_id _)

/-- A map out of the actual realized cylinder gives a continuous homotopy of its ends. -/
def continuousHomotopyOfCylinderMap {K : SSet.{k}} {Y : TopCat.{k}}
    {f g : SSet.toTop.obj K ⟶ Y}
    (h : SSet.toTop.obj (K ⊗ (Δ[1] : SSet.{k})) ⟶ Y)
    (h₀ : SSet.toTop.map (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{k})) ≫ h = f)
    (h₁ : SSet.toTop.map (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{k})) ≫ h = g) :
    TopCat.Homotopy f g := by
  let U := SSet.realizeHomotopy K (K ⊗ (Δ[1] : SSet.{k}))
    SSet.ι₀ SSet.ι₁ (universalCylinderHomotopy K)
  let H := (ContinuousMap.Homotopy.refl h.hom).comp U
  have hStart : h.hom.comp
      (SSet.toTop.map (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{k}))).hom = f.hom :=
    congrArg (fun q : SSet.toTop.obj K ⟶ Y => q.hom) h₀
  have hEnd : h.hom.comp
      (SSet.toTop.map (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{k}))).hom = g.hom :=
    congrArg (fun q : SSet.toTop.obj K ⟶ Y => q.hom) h₁
  exact H.cast hStart hEnd

/-- Interpret the model relation using the proved good cylinder, not an assumed path model. -/
def continuousHomotopyOfLeftHomotopy {K : SSet.{k}} {Y : TopCat.{k}} [IsFibrant Y]
    {f g : SSet.toTop.obj K ⟶ Y} (h : LeftHomotopyRel f g) : TopCat.Homotopy f g := by
  letI : IsCofibrant (SSet.toTop.obj K) := realization_isCofibrant K
  letI : (realizedStandardCylinder K).IsGood := realizedStandardCylinder_isGood K
  let H := h.leftHomotopy (realizedStandardCylinder K)
  let rawH : SSet.toTop.obj (K ⊗ (Δ[1] : SSet.{k})) ⟶ Y := H.h
  have h₀ : SSet.toTop.map (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{k})) ≫ rawH = f := H.h₀
  have h₁ : SSet.toTop.map (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{k})) ≫ rawH = g := H.h₁
  exact continuousHomotopyOfCylinderMap rawH h₀ h₁

/-- Every original TopCat object is fibrant, by its actual singular Kan complex. -/
theorem allTopCatObjectsFibrant (X : TopCat.{k}) : IsFibrant X := by
  have hKan : IsFibrant (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  have hTerminal : IsTerminal (TopCat.toSSet.obj (⊤_ TopCat.{k})) :=
    terminalIsTerminal.isTerminalObj TopCat.toSSet (⊤_ TopCat.{k})
  have hSingular : Fibration (TopCat.toSSet.map (terminal.from X)) :=
    (isFibrant_iff_of_isTerminal _ hTerminal).mp hKan
  apply (isFibrant_iff X).mpr
  apply (fibration_iff (terminal.from X)).mpr
  change TopCat.realizedHornInclusions.rlp (terminal.from X)
  apply (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mpr
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp hSingular

/-- Whitehead yields an HE with exactly the given realized forward map. -/
def realizationHomotopyEquiv {K L : SSet.{k}} (f : K ⟶ L)
    (hf : SSet.realizationWeakEquivalences f) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (SSet.toTop.obj L) := by
  let X := SSet.toTop.obj K
  let Y := SSet.toTop.obj L
  let F : X ⟶ Y := SSet.toTop.map f
  letI : IsCofibrant X := realization_isCofibrant K
  letI : IsCofibrant Y := realization_isCofibrant L
  letI : IsFibrant X := allTopCatObjectsFibrant X
  letI : IsFibrant Y := allTopCatObjectsFibrant Y
  letI : WeakEquivalence F := by
    apply (weakEquivalence_iff (f := F)).mpr
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
    exact hf
  let w : ∃ G : Y ⟶ X,
      LeftHomotopyRel (F ≫ G) (𝟙 X) ∧ LeftHomotopyRel (G ≫ F) (𝟙 Y) :=
    LeftHomotopyClass.whitehead F
  let G := Classical.choose w
  have hLeft : LeftHomotopyRel (F ≫ G) (𝟙 X) := (Classical.choose_spec w).1
  have hRight : LeftHomotopyRel (G ≫ F) (𝟙 Y) := (Classical.choose_spec w).2
  exact
    { toFun := F.hom
      invFun := G.hom
      left_inv := by
        exact ⟨(continuousHomotopyOfLeftHomotopy hLeft).cast rfl rfl⟩
      right_inv := by
        exact ⟨(continuousHomotopyOfLeftHomotopy hRight).cast rfl rfl⟩ }

/-- The forward map stays the literal realization of the original simplicial map. -/
theorem realizationHomotopyEquiv_toFun {K L : SSet.{k}} (f : K ⟶ L)
    (hf : SSet.realizationWeakEquivalences f) :
    (realizationHomotopyEquiv f hf).toFun = (SSet.toTop.map f).hom := rfl

/-- The actual realized terminal is contractible through its delta-zero Iso. -/
theorem realizedTerminal_contractible : ContractibleSpace (SSet.toTop.obj (⊤_ SSet.{k})) := by
  let e : (Δ[0] : SSet.{k}) ≅ (⊤_ SSet.{k}) :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  have hAffine : ContractibleSpace (Convexity.StdSimplex ℝ (Fin 1)) := inferInstance
  have hZero : ContractibleSpace (SSet.toTop.obj (Δ[0] : SSet.{k})) :=
    @Homeomorph.contractibleSpace _ _ _ _ hAffine (SimplexCategory.toTopHomeo ⦋0⦌)
  exact @Homeomorph.contractibleSpace _ _ _ _ hZero
    (TopCat.homeoOfIso (SSet.toTop.mapIso e).symm)

/-- Generic realization conull-WE upgrade, with all topology and inverse data derived above. -/
theorem contractible_of_conull_weakEquivalence (K : SSet.{k})
    (hK : SSet.realizationWeakEquivalences (terminal.from K)) :
    ContractibleSpace (SSet.toTop.obj K) :=
  @ContinuousMap.HomotopyEquiv.contractibleSpace _ _ _ _ realizedTerminal_contractible
    (realizationHomotopyEquiv (terminal.from K) hK)

private theorem conullSimplexZero_subsingleton :
    Subsingleton (SSet.toTop.obj (Δ[0] : SSet.{k})) := by
  constructor
  intro a b
  apply (SimplexCategory.toTopHomeo ⦋0⦌).injective
  exact Subsingleton.elim _ _

private def conullPointEquiv (K : SSet.{k})
    [ContractibleSpace (SSet.toTop.obj K)] :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj K)
      (SSet.toTop.obj (Δ[0] : SSet.{k})) := by
  have hNull : (ContinuousMap.id (SSet.toTop.obj K)).Nullhomotopic :=
    id_nullhomotopic (SSet.toTop.obj K)
  let p : SSet.toTop.obj K := Classical.choose hNull
  let hp : ContinuousMap.Homotopy (ContinuousMap.id (SSet.toTop.obj K))
      (ContinuousMap.const (SSet.toTop.obj K) p) :=
    Classical.choice (Classical.choose_spec hNull)
  let q : K ⟶ (Δ[0] : SSet.{k}) := SSet.stdSimplex.isTerminalObj₀.from K
  refine
    { toFun := (SSet.toTop.map q).hom
      invFun := ContinuousMap.const _ p
      left_inv := ?_
      right_inv := ?_ }
  · have he : (ContinuousMap.const (SSet.toTop.obj (Δ[0] : SSet.{k})) p).comp
        (SSet.toTop.map q).hom = ContinuousMap.const (SSet.toTop.obj K) p := rfl
    exact ⟨ContinuousMap.Homotopy.cast hp.symm he.symm rfl⟩
  · have he : (SSet.toTop.map q).hom.comp
        (ContinuousMap.const (SSet.toTop.obj (Δ[0] : SSet.{k})) p) =
        ContinuousMap.id (SSet.toTop.obj (Δ[0] : SSet.{k})) := by
      ext x
      exact conullSimplexZero_subsingleton.elim _ _
    rewrite [he]
    exact ContinuousMap.Homotopic.refl _

/-- Contractibility of the original realization makes its literal terminal map weak. -/
theorem conull_mem_of_contractible (K : SSet.{k})
    [ContractibleSpace (SSet.toTop.obj K)] :
    SSet.realizationWeakEquivalences (terminal.from K) := by
  let q : K ⟶ (Δ[0] : SSet.{k}) := SSet.stdSimplex.isTerminalObj₀.from K
  have hq : SSet.realizationWeakEquivalences q := by
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map q)
    exact TopCat.mem_of_eq_toFun (conullPointEquiv K) rfl
  let e : (Δ[0] : SSet.{k}) ≅ (⊤_ SSet.{k}) :=
    SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso terminalIsTerminal
  have he : q ≫ e.hom = terminal.from K := terminal.hom_ext _ _
  have ht := CategoryTheory.MorphismProperty.RespectsIso.postcomp
    SSet.realizationWeakEquivalences e.hom q hq
  rw [he] at ht
  exact ht

end SSet.RealizationCWUpgrade
end
