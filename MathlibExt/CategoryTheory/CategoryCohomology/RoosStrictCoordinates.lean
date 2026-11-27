/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import MathlibExt.CategoryTheory.CategoryCohomology.RoosNormalizedCoordinates

/-!
# Strict-poset coordinates of normalized Roos cochains

For a poset, the nondegenerate coordinates of the normalized Roos complex are
indexed by strictly decreasing chains. The coefficient lies at the first,
largest displayed vertex, which is terminal in the original poset's arrow
direction. The differential is the signed deletion formula in these
coordinates. The normalization maps compare this complex with the full
weak-chain Roos complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open CategoryTheory.CategoryHomology
open scoped BigOperators

universe u₁ u₂ v₂

namespace CategoryTheory.CategoryCohomology

variable {P : Type u₁} [PartialOrder P]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{u₁} A]

/-- The nondegenerate-chain indices identify with strict given-poset vertices. -/
def strictRoosChainEquiv (P : Type u₁) [PartialOrder P] (n : ℕ) :
    (nerve Pᵒᵖ).nonDegenerate n ≃
      {F : ComposableArrows Pᵒᵖ n // StrictAnti (fun i ↦ (F.obj i).unop)} where
  toFun F := ⟨F.val, (PartialOrder.nerve_op_nonDegenerate_iff_strictAnti F.val).mp F.property⟩
  invFun F := ⟨F.val, (PartialOrder.nerve_op_nonDegenerate_iff_strictAnti F.val).mpr F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient family at the first, largest vertex of each strict descending
chain, terminal in the original poset's arrow direction. -/
abbrev strictRoosFamily (M : P ⥤ A) (n : ℕ) :
    {F : ComposableArrows Pᵒᵖ n // StrictAnti (fun i ↦ (F.obj i).unop)} → A :=
  fun F ↦ M.obj F.val.left.unop

/-- The index equivalence preserves the coefficient at the first, largest vertex
of each descending chain. -/
def strictRoosFactorIso (M : P ⥤ A) (n : ℕ)
    (F : (nerve Pᵒᵖ).nonDegenerate n) :
    strictRoosFamily M n (strictRoosChainEquiv P n F) ≅ nondegenerateRoosFamily M n F := by
  let FC : ComposableArrows Pᵒᵖ n := roosNerveChain n F.val
  change M.obj FC.left.unop ≅ M.obj FC.left.unop
  exact Iso.refl _

/-- The product reindexing through the strict/nondegenerate nerve equivalence. -/
def strictRoosProductComparison (M : P ⥤ A) (n : ℕ) :
    (∏ᶜ (nondegenerateRoosFamily M n)) ≅ ∏ᶜ (strictRoosFamily M n) :=
  Pi.whiskerEquiv (f := nondegenerateRoosFamily M n) (g := strictRoosFamily M n)
    (strictRoosChainEquiv P n) (strictRoosFactorIso M n)

/-- The normalized degree object is the product over strict descending chains. -/
def normalizedRoosStrictProductIso (M : P ⥤ A) (n : ℕ) :
    ((normalizedRoosComplexFunctor (I := P) (A := A)).obj M).X n ≅
      ∏ᶜ (fun F : {F : ComposableArrows Pᵒᵖ n //
          StrictAnti (fun i ↦ (F.obj i).unop)} ↦ M.obj F.val.left.unop) :=
  normalizedRoosProductIso M n ≪≫ strictRoosProductComparison M n

/-- The strict coordinate is the normalized inclusion and terminal-coefficient projection. -/
theorem normalizedRoosStrictProductIso_hom_π (M : P ⥤ A) (n : ℕ)
    (F : {F : ComposableArrows Pᵒᵖ n // StrictAnti (fun i ↦ (F.obj i).unop)}) :
    (normalizedRoosStrictProductIso M n).hom ≫
        Pi.π (fun F : {F : ComposableArrows Pᵒᵖ n //
          StrictAnti (fun i ↦ (F.obj i).unop)} ↦ M.obj F.val.left.unop) F =
      ((inclusionOfNormalizedRoosComplex (I := P) (A := A)).app M).f n ≫
        roosπ M F.val := by
  let e := strictRoosChainEquiv P n
  let F₀ : (nerve Pᵒᵖ).nonDegenerate n := e.symm F
  let W : (∏ᶜ (nondegenerateRoosFamily M n)) ≅ ∏ᶜ (strictRoosFamily M n) :=
    strictRoosProductComparison M n
  let p : (∏ᶜ (strictRoosFamily M n)) ⟶ M.obj F.val.left.unop :=
    Pi.π (strictRoosFamily M n) F
  let p₀ : (∏ᶜ (nondegenerateRoosFamily M n)) ⟶ M.obj F.val.left.unop :=
    Pi.π (nondegenerateRoosFamily M n) F₀
  have hW₀ : W.inv ≫ p₀ = p ≫ 𝟙 (M.obj F.val.left.unop) :=
    Pi.map'_comp_π (f := strictRoosFamily M n) (g := nondegenerateRoosFamily M n)
      e (fun G : (nerve Pᵒᵖ).nonDegenerate n => (strictRoosFactorIso M n G).hom) F₀
  have hW : W.inv ≫ p₀ = p := hW₀.trans (Category.comp_id p)
  have hW' : W.hom ≫ p = p₀ := by
    apply (cancel_epi W.inv).1
    exact (Category.assoc W.inv W.hom p).symm.trans
      ((congrArg (fun k => k ≫ p) W.inv_hom_id).trans
        ((Category.id_comp p).trans hW.symm))
  let U : normalizedRoosDegree M n ⟶ ∏ᶜ (nondegenerateRoosFamily M n) :=
    (normalizedRoosProductIso M n).hom
  let I' : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
  let π : fullRoosDegree M n ⟶ M.obj F.val.left.unop := roosChainProjection M F.val
  have hU : U ≫ p₀ = I' ≫ π := normalizedRoosProductIso_hom_π M n F₀
  change (U ≫ W.hom) ≫ p = I' ≫ π
  exact (Category.assoc U W.hom p).trans
    ((congrArg (fun k => U ≫ k) hW').trans hU)

/-- Deleting a vertex of a strict descending chain produces another strict descending chain. -/
def strictRoosFace {n : ℕ} (i : Fin (n + 2))
    (F : {F : ComposableArrows Pᵒᵖ (n + 1) //
      StrictAnti (fun j ↦ (F.obj j).unop)}) :
    {G : ComposableArrows Pᵒᵖ n // StrictAnti (fun j ↦ (G.obj j).unop)} :=
  ⟨(nerve Pᵒᵖ).δ i F.val, by
    intro a b hab
    simpa only [nerve.δ_obj] using F.property (Fin.strictMono_succAbove i hab)⟩

/-- The normalized differential is the signed strict-chain deletion formula. -/
theorem normalizedRoosStrictProductIso_d_π (M : P ⥤ A) (n : ℕ)
    (F : {F : ComposableArrows Pᵒᵖ (n + 1) //
      StrictAnti (fun i ↦ (F.obj i).unop)}) :
    ((normalizedRoosComplexFunctor (I := P) (A := A)).obj M).d n (n + 1) ≫
        (normalizedRoosStrictProductIso M (n + 1)).hom ≫
        Pi.π (fun F : {F : ComposableArrows Pᵒᵖ (n + 1) //
          StrictAnti (fun i ↦ (F.obj i).unop)} ↦ M.obj F.val.left.unop) F =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ((normalizedRoosStrictProductIso M n).hom ≫
          Pi.π (fun G : {G : ComposableArrows Pᵒᵖ n //
            StrictAnti (fun j ↦ (G.obj j).unop)} ↦ M.obj G.val.left.unop)
              (strictRoosFace i F) ≫
          M.map ((faceLeftHom i F.val).unop)) := by
  let D : normalizedRoosDegree M n ⟶ normalizedRoosDegree M (n + 1) :=
    ((normalizedCofaceMapComplex A).obj (roosCosimplicial M)).d n (n + 1)
  let d : fullRoosDegree M n ⟶ fullRoosDegree M (n + 1) :=
    ((alternatingCofaceMapComplex A).obj (roosCosimplicial M)).d n (n + 1)
  let U₀ : normalizedRoosDegree M n ⟶ ∏ᶜ (strictRoosFamily M n) :=
    (normalizedRoosStrictProductIso M n).hom
  let U₁ : normalizedRoosDegree M (n + 1) ⟶ ∏ᶜ (strictRoosFamily M (n + 1)) :=
    (normalizedRoosStrictProductIso M (n + 1)).hom
  let p : (∏ᶜ (strictRoosFamily M (n + 1))) ⟶ M.obj F.val.left.unop :=
    Pi.π (strictRoosFamily M (n + 1)) F
  let I₀ : normalizedRoosDegree M n ⟶ fullRoosDegree M n := roosInclusionAt M n
  let I₁ : normalizedRoosDegree M (n + 1) ⟶ fullRoosDegree M (n + 1) :=
    roosInclusionAt M (n + 1)
  let π : fullRoosDegree M (n + 1) ⟶ M.obj F.val.left.unop := roosChainProjection M F.val
  let πface (i : Fin (n + 2)) :
      fullRoosDegree M n ⟶ M.obj (strictRoosFace i F).val.left.unop :=
    roosChainProjection M (strictRoosFace i F).val
  let pface (i : Fin (n + 2)) :
      (∏ᶜ (strictRoosFamily M n)) ⟶ M.obj (strictRoosFace i F).val.left.unop :=
    Pi.π (strictRoosFamily M n) (strictRoosFace i F)
  let η (i : Fin (n + 2)) :
      M.obj (strictRoosFace i F).val.left.unop ⟶ M.obj F.val.left.unop :=
    M.map ((faceLeftHom i F.val).unop)
  have hU₁ : U₁ ≫ p = I₁ ≫ π := normalizedRoosStrictProductIso_hom_π M (n + 1) F
  have hComm : I₀ ≫ d = D ≫ I₁ :=
    ((inclusionOfNormalizedCofaceMapComplex A).app (roosCosimplicial M)).comm n (n + 1)
  have hd : d ≫ π = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (πface i ≫ η i) :=
    roosComplex_d_π M F.val
  have hU₀ (i : Fin (n + 2)) : U₀ ≫ pface i = I₀ ≫ πface i :=
    normalizedRoosStrictProductIso_hom_π M n (strictRoosFace i F)
  change D ≫ U₁ ≫ p =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (U₀ ≫ pface i ≫ η i)
  calc
    D ≫ U₁ ≫ p = D ≫ (I₁ ≫ π) := congrArg (fun k => D ≫ k) hU₁
    _ = (D ≫ I₁) ≫ π := (Category.assoc D I₁ π).symm
    _ = (I₀ ≫ d) ≫ π := congrArg (fun k => k ≫ π) hComm.symm
    _ = I₀ ≫ (d ≫ π) := Category.assoc I₀ d π
    _ = I₀ ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (πface i ≫ η i)) :=
      congrArg (fun k => I₀ ≫ k) hd
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (I₀ ≫ πface i ≫ η i) := by
      simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (U₀ ≫ pface i ≫ η i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun k : normalizedRoosDegree M n ⟶ M.obj F.val.left.unop =>
        (-1 : ℤ) ^ i.val • k)
          ((Category.assoc I₀ (πface i) (η i)).symm.trans
            ((congrArg (fun k => k ≫ η i) (hU₀ i).symm).trans
              (Category.assoc U₀ (pface i) (η i))))

end CategoryTheory.CategoryCohomology

end
