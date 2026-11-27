/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosNormalization
public import MathlibExt.AlgebraicTopology.CosimplicialObject.NormalizationKernel
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Nondegenerate coordinates for normalized Roos cochains

Normalized Roos cochains have product coordinates indexed by the nondegenerate
simplices of the nerve. The inverse coordinate map extends by zero on
degenerate chains and applies the normalization projection. These coordinates
apply to general index categories; their interpretation as strictly ordered
vertex chains requires a poset.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open CategoryTheory.CategoryHomology
open scoped BigOperators

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]

/-- The typed composable-arrow presentation of an nerve simplex. -/
def roosNerveChain (n : ℕ)
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    ComposableArrows Iᵒᵖ n := F

/-- The typed nerve-simplex presentation of a composable-arrow chain. -/
def roosNerveSimplex (n : ℕ) (F : ComposableArrows Iᵒᵖ n) :
    (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)) := F

variable {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{max u₁ v₁} A]

attribute [local instance] Classical.propDecidable

/-- The alternating-coface degree carrier of the Roos object. -/
abbrev fullRoosDegree (M : I ⥤ A) (n : ℕ) : A :=
  ((alternatingCofaceMapComplex A).obj (roosCosimplicial M)).X n

/-- The normalized-coface degree carrier of the Roos object. -/
abbrev normalizedRoosDegree (M : I ⥤ A) (n : ℕ) : A :=
  ((normalizedCofaceMapComplex A).obj (roosCosimplicial M)).X n

/-- The normalized inclusion at the displayed degree carriers. -/
abbrev roosInclusionAt (M : I ⥤ A) (n : ℕ) :
    normalizedRoosDegree M n ⟶ fullRoosDegree M n :=
  ((inclusionOfNormalizedCofaceMapComplex A).app (roosCosimplicial M)).f n

/-- The normalization projection at the displayed degree carriers. -/
abbrev roosProjectionAt (M : I ⥤ A) (n : ℕ) :
    fullRoosDegree M n ⟶ normalizedRoosDegree M n :=
  ((normalizedCofaceMapProjection A).app (roosCosimplicial M)).f n

/-- The weak-chain projection with its alternating degree source. -/
abbrev roosChainProjection (M : I ⥤ A) {n : ℕ} (F : ComposableArrows Iᵒᵖ n) :
    fullRoosDegree M n ⟶ M.obj F.left.unop :=
  roosπ M F

/-- The codegeneracy with alternating degree endpoints. -/
abbrev roosCodegeneracyAt (M : I ⥤ A) (n : ℕ) (i : Fin (n + 1)) :
    fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n :=
  (roosCosimplicial M).σ i

private theorem fullRoosDegree_hom_ext (M : I ⥤ A) {n : ℕ} {Z : A}
    {f g : Z ⟶ fullRoosDegree M n}
    (h : ∀ F : ComposableArrows Iᵒᵖ n,
      f ≫ roosChainProjection M F = g ≫ roosChainProjection M F) : f = g := by
  let e : fullRoosDegree M n ≅ ∏ᶜ (roosFamily M n) := roosObjIso M n
  apply (cancel_mono e.hom).1
  apply Pi.hom_ext
  intro F
  let p : (∏ᶜ (roosFamily M n)) ⟶ M.obj F.left.unop := Pi.π (roosFamily M n) F
  have he : e.hom ≫ p = roosChainProjection M F := roosObjIso_hom_π M F
  exact ((Category.assoc f e.hom p).trans (congrArg (fun k => f ≫ k) he)).trans
    ((h F).trans ((Category.assoc g e.hom p).trans
      (congrArg (fun k => g ≫ k) he)).symm)

/-- The coefficient family on nondegenerate nerve chains. -/
def nondegenerateRoosFamily (M : I ⥤ A) (n : ℕ) :
    (nerve Iᵒᵖ).nonDegenerate n → A :=
  fun F ↦ M.obj (roosNerveChain n F.val).left.unop

/-- Normalized coordinates are the inclusion followed by weak-chain projections. -/
def normalizedRoosProductMap (M : I ⥤ A) (n : ℕ) :
    ((normalizedRoosComplexFunctor (I := I) (A := A)).obj M).X n ⟶
      ∏ᶜ (nondegenerateRoosFamily M n) :=
  Pi.lift (fun F ↦ roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n F.val))

/-- The nondegenerate projection, or zero, at a displayed weak-chain coordinate. -/
def roosNondegenerateCoordinate (M : I ⥤ A) (n : ℕ)
    (F : ComposableArrows Iᵒᵖ n) :
    (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ roosFamily M n F := by
  let FN : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)) := roosNerveSimplex n F
  exact if h : FN ∈ (nerve Iᵒᵖ).nonDegenerate n then (by
    let FND : (nerve Iᵒᵖ).nonDegenerate n := ⟨FN, h⟩
    have hObj : nondegenerateRoosFamily M n FND = roosFamily M n F := rfl
    exact Eq.mp (congrArg (fun B : A => (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ B) hObj)
      (Pi.π (nondegenerateRoosFamily M n) FND)) else 0

/-- Native nerve input gives the nondegenerate projection formula. -/
theorem roosNondegenerateCoordinate_native (M : I ⥤ A) (n : ℕ)
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    roosNondegenerateCoordinate M n (roosNerveChain n F) =
      if h : F ∈ (nerve Iᵒᵖ).nonDegenerate n then
        Pi.π (nondegenerateRoosFamily M n) (⟨F, h⟩ : (nerve Iᵒᵖ).nonDegenerate n) else 0 := rfl

/-- The zero-extension matrix between the nondegenerate and weak-chain products. -/
def roosNondegenerateExtensionLift (M : I ⥤ A) (n : ℕ) :
    (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ ∏ᶜ (roosFamily M n) :=
  Pi.lift (roosNondegenerateCoordinate M n)

/-- Nondegenerate coordinates extend by zero to the full Roos object. -/
def roosNondegenerateExtension (M : I ⥤ A) (n : ℕ) :
    ∏ᶜ (nondegenerateRoosFamily M n) ⟶ (roosComplex M).X n :=
  roosNondegenerateExtensionLift M n ≫ (roosObjIso M n).inv

/-- The extension has the prescribed coordinates, including zero on degeneracies. -/
theorem roosNondegenerateExtension_π (M : I ⥤ A) (n : ℕ)
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n))) :
    roosNondegenerateExtension M n ≫ roosπ M (roosNerveChain n F) =
      if h : F ∈ (nerve Iᵒᵖ).nonDegenerate n then
        Pi.π (nondegenerateRoosFamily M n) ⟨F, h⟩ else 0 := by
  let FC : ComposableArrows Iᵒᵖ n := roosNerveChain n F
  let E : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ fullRoosDegree M n :=
    roosNondegenerateExtension M n
  let e : fullRoosDegree M n ≅ ∏ᶜ (roosFamily M n) := roosObjIso M n
  let p : (∏ᶜ (roosFamily M n)) ⟶ M.obj FC.left.unop := Pi.π (roosFamily M n) FC
  let π : fullRoosDegree M n ⟶ M.obj FC.left.unop := roosChainProjection M FC
  let q : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ ∏ᶜ (roosFamily M n) :=
    roosNondegenerateExtensionLift M n
  let c : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ M.obj FC.left.unop :=
    if h : F ∈ (nerve Iᵒᵖ).nonDegenerate n then
      Pi.π (nondegenerateRoosFamily M n) ⟨F, h⟩ else 0
  have hE : E = q ≫ e.inv := rfl
  have he : e.hom ≫ p = π := roosObjIso_hom_π M FC
  have hq : q ≫ p = c :=
    (Pi.lift_comp_π (roosNondegenerateCoordinate M n) FC).trans
      (roosNondegenerateCoordinate_native M n F)
  change E ≫ π = c
  calc
    E ≫ π = (q ≫ e.inv) ≫ π := congrArg (fun k => k ≫ π) hE
    _ = q ≫ e.inv ≫ π := Category.assoc q e.inv π
    _ = q ≫ e.inv ≫ (e.hom ≫ p) := congrArg (fun k => q ≫ e.inv ≫ k) he.symm
    _ = q ≫ (e.inv ≫ e.hom) ≫ p := by simp only [Category.assoc]
    _ = q ≫ p := (congrArg (fun k => q ≫ k ≫ p) e.inv_hom_id).trans
      (congrArg (fun k => q ≫ k) (Category.id_comp p))
    _ = c := hq

/-- The normalized inclusion has zero projection at every degenerate chain. -/
theorem inclusionOfNormalizedRoosComplex_f_π_degenerate (M : I ⥤ A) (n : ℕ)
    (F : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)))
    (hF : F ∈ (nerve Iᵒᵖ).degenerate n) :
    ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M).f n ≫
      roosπ M (roosNerveChain n F) = 0 := by
  change roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n F) = 0
  cases n with
  | zero =>
      simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hF
  | succ n =>
      rw [SSet.degenerate_eq_iUnion_range_σ, Set.mem_iUnion] at hF
      obtain ⟨i, hF⟩ := hF
      change ∃ G : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)),
        (nerve Iᵒᵖ).σ i G = F at hF
      obtain ⟨G, rfl⟩ := hF
      let GC : ComposableArrows Iᵒᵖ n := roosNerveChain n G
      let FG : ComposableArrows Iᵒᵖ (n + 1) :=
        roosNerveChain (n + 1) ((nerve Iᵒᵖ).σ i G)
      let t : (0 : Fin (n + 1)) ⟶ i.predAbove (0 : Fin (n + 2)) :=
        homOfLE (Fin.zero_le _)
      have : IsIso t := homOfLE_isIso_of_eq _
        (Fin.predAbove_right_zero (i := i)).symm
      have : IsIso (degeneracyLeftHom i GC) := by
        change IsIso (GC.map t)
        infer_instance
      let η : M.obj FG.left.unop ⟶ M.obj GC.left.unop :=
        M.map ((degeneracyLeftHom i GC).unop)
      have : IsIso η := by
        change IsIso (M.map ((degeneracyLeftHom i GC).unop))
        exact (M.mapIso ((asIso (degeneracyLeftHom i GC)).unop)).isIso_hom
      let I' : normalizedRoosDegree M (n + 1) ⟶ fullRoosDegree M (n + 1) :=
        roosInclusionAt M (n + 1)
      let σ : fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n :=
        roosCodegeneracyAt M n i
      let πG : fullRoosDegree M n ⟶ M.obj GC.left.unop := roosChainProjection M GC
      let πFG : fullRoosDegree M (n + 1) ⟶ M.obj FG.left.unop :=
        roosChainProjection M FG
      have hσ : σ ≫ πG = πFG ≫ η := roos_codegeneracy_π M i GC
      have hDegree :
          (alternatingCofaceObjIso (roosCosimplicial M) (n + 1)).hom ≫
            (roosCosimplicial M).σ i = σ :=
        (congrArg (fun k => k ≫ (roosCosimplicial M).σ i)
          (alternatingCofaceObjIso_hom (roosCosimplicial M) (n + 1))).trans
            (Category.id_comp _)
      have hIσ : I' ≫ σ = 0 :=
        (congrArg (fun k : fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n => I' ≫ k)
          hDegree).symm.trans
            (inclusionOfNormalizedCofaceMapComplex_f_comp_σ (roosCosimplicial M) n i)
      change I' ≫ πFG = 0
      apply (cancel_mono η).1
      calc
        (I' ≫ πFG) ≫ η = I' ≫ (πFG ≫ η) := Category.assoc I' πFG η
        _ = I' ≫ (σ ≫ πG) := congrArg (fun k => I' ≫ k) hσ.symm
        _ = (I' ≫ σ) ≫ πG := (Category.assoc I' σ πG).symm
        _ = 0 ≫ πG := congrArg (fun k => k ≫ πG) hIσ
        _ = 0 := zero_comp
        _ = 0 ≫ η := zero_comp.symm

/-- Zero extension annihilates each Roos codegeneracy. -/
theorem roosNondegenerateExtension_comp_σ (M : I ⥤ A) (n : ℕ) (i : Fin (n + 1)) :
    roosNondegenerateExtension M (n + 1) ≫ (roosCosimplicial M).σ i = 0 := by
  let E : (∏ᶜ (nondegenerateRoosFamily M (n + 1))) ⟶ fullRoosDegree M (n + 1) :=
    roosNondegenerateExtension M (n + 1)
  let σ : fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n := roosCodegeneracyAt M n i
  change E ≫ σ = 0
  apply fullRoosDegree_hom_ext M
  intro F
  let FN : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)) := roosNerveSimplex n F
  let FG : ComposableArrows Iᵒᵖ (n + 1) :=
    roosNerveChain (n + 1) ((nerve Iᵒᵖ).σ i FN)
  let π : fullRoosDegree M n ⟶ M.obj F.left.unop := roosChainProjection M F
  let πFG : fullRoosDegree M (n + 1) ⟶ M.obj FG.left.unop := roosChainProjection M FG
  let η : M.obj FG.left.unop ⟶ M.obj F.left.unop := M.map ((degeneracyLeftHom i F).unop)
  have hσ : σ ≫ π = πFG ≫ η := roos_codegeneracy_π M i F
  have hdeg : (nerve Iᵒᵖ).σ i FN ∉ (nerve Iᵒᵖ).nonDegenerate (n + 1) :=
    (SSet.mem_degenerate_iff_notMem_nonDegenerate (nerve Iᵒᵖ)
      ((nerve Iᵒᵖ).σ i FN)).mp (SSet.σ_mem_degenerate (nerve Iᵒᵖ) i FN)
  have hE : E ≫ πFG = 0 :=
    (roosNondegenerateExtension_π M (n + 1) ((nerve Iᵒᵖ).σ i FN)).trans (dite_eq_right hdeg)
  calc
    (E ≫ σ) ≫ π = E ≫ (σ ≫ π) := Category.assoc E σ π
    _ = E ≫ (πFG ≫ η) := congrArg (fun k => E ≫ k) hσ
    _ = (E ≫ πFG) ≫ η := (Category.assoc E πFG η).symm
    _ = 0 ≫ η := congrArg (fun k => k ≫ η) hE
    _ = 0 := zero_comp
    _ = 0 ≫ π := zero_comp.symm

/-- The normalization fixes the zero extension, in every degree including zero. -/
theorem roosNondegenerateExtension_comp_projection_comp_inclusion
    (M : I ⥤ A) (n : ℕ) :
    roosNondegenerateExtension M n ≫
        ((roosNormalizationProjection (I := I) (A := A)).app M).f n ≫
        ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M).f n =
      roosNondegenerateExtension M n := by
  cases n with
  | zero =>
      let E : (∏ᶜ (nondegenerateRoosFamily M 0)) ⟶ fullRoosDegree M 0 :=
        roosNondegenerateExtension M 0
      change E ≫ roosProjectionAt M 0 ≫ roosInclusionAt M 0 = E
      let S := (cosimplicialSimplicialEquiv A).functor.obj (op (roosCosimplicial M))
      have hP₀ : ((DoldKan.PInfty (X := S)).f 0).unop = 𝟙 (fullRoosDegree M 0) :=
        (congrArg Quiver.Hom.unop (DoldKan.PInfty_f_0 (X := S))).trans unop_id
      have h : roosProjectionAt M 0 ≫ roosInclusionAt M 0 = 𝟙 (fullRoosDegree M 0) :=
        (normalizedCofaceMapProjection_f_comp_inclusion (roosCosimplicial M) 0).trans hP₀
      exact (congrArg (fun k : fullRoosDegree M 0 ⟶ fullRoosDegree M 0 => E ≫ k) h).trans
        (Category.comp_id E)
  | succ n =>
      let E : (∏ᶜ (nondegenerateRoosFamily M (n + 1))) ⟶ fullRoosDegree M (n + 1) :=
        roosNondegenerateExtension M (n + 1)
      change E ≫ roosProjectionAt M (n + 1) ≫ roosInclusionAt M (n + 1) = E
      apply comp_normalizedCofaceMapProjection_f_comp_inclusion (roosCosimplicial M) n E
      intro i
      let σ : fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n := roosCodegeneracyAt M n i
      have hDegree :
          (alternatingCofaceObjIso (roosCosimplicial M) (n + 1)).hom ≫
            (roosCosimplicial M).σ i = σ :=
        (congrArg (fun k => k ≫ (roosCosimplicial M).σ i)
          (alternatingCofaceObjIso_hom (roosCosimplicial M) (n + 1))).trans
            (Category.id_comp _)
      exact (congrArg (fun k : fullRoosDegree M (n + 1) ⟶ fullRoosDegree M n => E ≫ k)
        hDegree).trans (roosNondegenerateExtension_comp_σ M n i)

/-- The inclusion is recovered from its nondegenerate product coordinates. -/
theorem normalizedRoosProductMap_comp_extension (M : I ⥤ A) (n : ℕ) :
    normalizedRoosProductMap M n ≫ roosNondegenerateExtension M n =
      ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M).f n := by
  let U : normalizedRoosDegree M n ⟶ ∏ᶜ (nondegenerateRoosFamily M n) :=
    normalizedRoosProductMap M n
  let E : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ fullRoosDegree M n :=
    roosNondegenerateExtension M n
  let I' : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
  change U ≫ E = I'
  apply fullRoosDegree_hom_ext M
  intro F
  let FN : (nerve Iᵒᵖ).obj (op (SimplexCategory.mk n)) := roosNerveSimplex n F
  let π : fullRoosDegree M n ⟶ M.obj F.left.unop := roosChainProjection M F
  let c : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ M.obj F.left.unop :=
    if h : FN ∈ (nerve Iᵒᵖ).nonDegenerate n then
      Pi.π (nondegenerateRoosFamily M n) ⟨FN, h⟩ else 0
  have hE : E ≫ π = c := roosNondegenerateExtension_π M n FN
  calc
    (U ≫ E) ≫ π = U ≫ (E ≫ π) := Category.assoc U E π
    _ = U ≫ c := congrArg (fun k => U ≫ k) hE
    _ = I' ≫ π := by
      by_cases hF : FN ∈ (nerve Iᵒᵖ).nonDegenerate n
      · let FND : (nerve Iᵒᵖ).nonDegenerate n := ⟨FN, hF⟩
        have hc : c = Pi.π (nondegenerateRoosFamily M n) FND := dite_eq_left hF
        have hU : U ≫ Pi.π (nondegenerateRoosFamily M n) FND = I' ≫ π :=
          Pi.lift_comp_π
            (fun G : (nerve Iᵒᵖ).nonDegenerate n =>
              roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n G.val)) FND
        exact (congrArg (fun k => U ≫ k) hc).trans hU
      · have hc : c = 0 := dite_eq_right hF
        have hI : I' ≫ π = 0 := inclusionOfNormalizedRoosComplex_f_π_degenerate M n FN
          ((SSet.mem_degenerate_iff_notMem_nonDegenerate (nerve Iᵒᵖ) FN).mpr hF)
        exact (congrArg (fun k => U ≫ k) hc).trans ((comp_zero).trans hI.symm)

/-- Normalized Roos degree n is the product over nondegenerate nerve n-simplices. -/
def normalizedRoosProductIso (M : I ⥤ A) (n : ℕ) :
    ((normalizedRoosComplexFunctor (I := I) (A := A)).obj M).X n ≅
      ∏ᶜ (nondegenerateRoosFamily M n) where
  hom := normalizedRoosProductMap M n
  inv := roosNondegenerateExtension M n ≫ roosProjectionAt M n
  hom_inv_id := by
    let U : normalizedRoosDegree M n ⟶ ∏ᶜ (nondegenerateRoosFamily M n) :=
      normalizedRoosProductMap M n
    let E : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ fullRoosDegree M n :=
      roosNondegenerateExtension M n
    let P : fullRoosDegree M n ⟶ normalizedRoosDegree M n := roosProjectionAt M n
    let I' : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
    have hU : U ≫ E = I' := normalizedRoosProductMap_comp_extension M n
    have hSplit : I' ≫ P = 𝟙 (normalizedRoosDegree M n) :=
      inclusionOfNormalizedCofaceMapComplex_f_comp_projection (roosCosimplicial M) n
    exact (Category.assoc U E P).symm.trans
      ((congrArg (fun k => k ≫ P) hU).trans hSplit)
  inv_hom_id := by
    let T := ∏ᶜ (nondegenerateRoosFamily M n)
    let U : normalizedRoosDegree M n ⟶ T := normalizedRoosProductMap M n
    let E : T ⟶ fullRoosDegree M n := roosNondegenerateExtension M n
    let P : fullRoosDegree M n ⟶ normalizedRoosDegree M n := roosProjectionAt M n
    let I' : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
    change (E ≫ P) ≫ U = 𝟙 T
    apply Pi.hom_ext
    intro F
    let FC : ComposableArrows Iᵒᵖ n := roosNerveChain n F.val
    let p : T ⟶ M.obj FC.left.unop := Pi.π (nondegenerateRoosFamily M n) F
    let π : fullRoosDegree M n ⟶ M.obj FC.left.unop := roosChainProjection M FC
    have hU : U ≫ p = I' ≫ π :=
      Pi.lift_comp_π
        (fun G : (nerve Iᵒᵖ).nonDegenerate n =>
          roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n G.val)) F
    have hFix : E ≫ P ≫ I' = E :=
      roosNondegenerateExtension_comp_projection_comp_inclusion M n
    have hE : E ≫ π = p :=
      (roosNondegenerateExtension_π M n F.val).trans (dite_eq_left F.property)
    calc
      ((E ≫ P) ≫ U) ≫ p = (E ≫ P) ≫ (U ≫ p) := Category.assoc (E ≫ P) U p
      _ = (E ≫ P) ≫ (I' ≫ π) := congrArg (fun k => (E ≫ P) ≫ k) hU
      _ = (E ≫ P ≫ I') ≫ π := by simp only [Category.assoc]
      _ = E ≫ π := congrArg (fun k => k ≫ π) hFix
      _ = p := hE
      _ = (𝟙 T) ≫ p := (Category.id_comp p).symm

/-- The product comparison's forward map is its constructed coordinate map. -/
@[simp]
theorem normalizedRoosProductIso_hom (M : I ⥤ A) (n : ℕ) :
    (normalizedRoosProductIso M n).hom = normalizedRoosProductMap M n := rfl

/-- The product comparison's inverse is zero extension followed by normalization. -/
@[simp]
theorem normalizedRoosProductIso_inv (M : I ⥤ A) (n : ℕ) :
    (normalizedRoosProductIso M n).inv =
      roosNondegenerateExtension M n ≫ roosProjectionAt M n := rfl

/-- The forward product comparison retains each nondegenerate projection. -/
theorem normalizedRoosProductIso_hom_π (M : I ⥤ A) (n : ℕ)
    (F : (nerve Iᵒᵖ).nonDegenerate n) :
    (normalizedRoosProductIso M n).hom ≫ Pi.π (nondegenerateRoosFamily M n) F =
      ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M).f n ≫
        roosπ M (roosNerveChain n F.val) := by
  change normalizedRoosProductMap M n ≫ Pi.π (nondegenerateRoosFamily M n) F =
    roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n F.val)
  exact Pi.lift_comp_π
    (fun G : (nerve Iᵒᵖ).nonDegenerate n =>
      roosInclusionAt M n ≫ roosChainProjection M (roosNerveChain n G.val)) F

/-- The inverse comparison really extends by zero into the full Roos object. -/
theorem normalizedRoosProductIso_inv_comp_inclusion (M : I ⥤ A) (n : ℕ) :
    (normalizedRoosProductIso M n).inv ≫
      ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M).f n =
        roosNondegenerateExtension M n := by
  change (roosNondegenerateExtension M n ≫ roosProjectionAt M n) ≫ roosInclusionAt M n =
    roosNondegenerateExtension M n
  exact (Category.assoc (roosNondegenerateExtension M n) (roosProjectionAt M n)
    (roosInclusionAt M n)).trans
      (roosNondegenerateExtension_comp_projection_comp_inclusion M n)

/-- The normalized differential uses the signed face formula and zero-extension. -/
theorem normalizedRoosProductIso_d_π (M : I ⥤ A) (n : ℕ)
    (F : (nerve Iᵒᵖ).nonDegenerate (n + 1)) :
    (normalizedRoosProductIso M n).inv ≫
        ((normalizedRoosComplexFunctor (I := I) (A := A)).obj M).d n (n + 1) ≫
        (normalizedRoosProductIso M (n + 1)).hom ≫
        Pi.π (nondegenerateRoosFamily M (n + 1)) F =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ((roosNondegenerateExtension M n ≫
          roosπ M (roosNerveChain n ((nerve Iᵒᵖ).δ i F.val))) ≫
            M.map ((faceLeftHom i (roosNerveChain (n + 1) F.val)).unop)) := by
  let FC : ComposableArrows Iᵒᵖ (n + 1) := roosNerveChain (n + 1) F.val
  let V : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ normalizedRoosDegree M n :=
    (normalizedRoosProductIso M n).inv
  let H : normalizedRoosDegree M (n + 1) ⟶ ∏ᶜ (nondegenerateRoosFamily M (n + 1)) :=
    (normalizedRoosProductIso M (n + 1)).hom
  let p : (∏ᶜ (nondegenerateRoosFamily M (n + 1))) ⟶ M.obj FC.left.unop :=
    Pi.π (nondegenerateRoosFamily M (n + 1)) F
  let π : fullRoosDegree M (n + 1) ⟶ M.obj FC.left.unop := roosChainProjection M FC
  let D : normalizedRoosDegree M n ⟶ normalizedRoosDegree M (n + 1) :=
    ((normalizedCofaceMapComplex A).obj (roosCosimplicial M)).d n (n + 1)
  let d : fullRoosDegree M n ⟶ fullRoosDegree M (n + 1) :=
    ((alternatingCofaceMapComplex A).obj (roosCosimplicial M)).d n (n + 1)
  let E : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ fullRoosDegree M n :=
    roosNondegenerateExtension M n
  let I₀ : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
  let I₁ : normalizedRoosDegree M (n + 1) ⟶ fullRoosDegree M (n + 1) :=
    roosInclusionAt M (n + 1)
  let face (i : Fin (n + 2)) : ComposableArrows Iᵒᵖ n :=
    roosNerveChain n ((nerve Iᵒᵖ).δ i F.val)
  let πface (i : Fin (n + 2)) : fullRoosDegree M n ⟶ M.obj (face i).left.unop :=
    roosChainProjection M (face i)
  let η (i : Fin (n + 2)) : M.obj (face i).left.unop ⟶ M.obj FC.left.unop :=
    M.map ((faceLeftHom i FC).unop)
  have hH : H ≫ p = I₁ ≫ π := normalizedRoosProductIso_hom_π M (n + 1) F
  have hComm : I₀ ≫ d = D ≫ I₁ :=
    ((inclusionOfNormalizedCofaceMapComplex A).app (roosCosimplicial M)).comm n (n + 1)
  have hV : V ≫ I₀ = E := normalizedRoosProductIso_inv_comp_inclusion M n
  have hd : d ≫ π = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (πface i ≫ η i) :=
    roosComplex_d_π M FC
  change V ≫ D ≫ H ≫ p =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • ((E ≫ πface i) ≫ η i)
  calc
    V ≫ D ≫ H ≫ p = V ≫ D ≫ (H ≫ p) := rfl
    _ = V ≫ D ≫ (I₁ ≫ π) := congrArg (fun k => V ≫ D ≫ k) hH
    _ = V ≫ (D ≫ I₁) ≫ π := by simp only [Category.assoc]
    _ = V ≫ (I₀ ≫ d) ≫ π := congrArg (fun k => V ≫ k ≫ π) hComm.symm
    _ = (V ≫ I₀) ≫ d ≫ π := by simp only [Category.assoc]
    _ = E ≫ d ≫ π := congrArg (fun k => k ≫ d ≫ π) hV
    _ = E ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (πface i ≫ η i)) :=
      congrArg (fun k => E ≫ k) hd
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • ((E ≫ πface i) ≫ η i) := by
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Category.assoc]

end CategoryTheory.CategoryCohomology

end
