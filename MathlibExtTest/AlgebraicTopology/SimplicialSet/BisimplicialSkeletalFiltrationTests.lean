/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration

/-!
# Bisimplicial skeletal-filtration tests

The tests pin the latching factor order, the nontrivial `n = 1` overlap,
coefficient-first diagonal cells, both pushout families, exhaustion of the
diagonal, and functoriality of every successor-attachment leg.  They make no
properness, realization, or weak-equivalence claim.
-/

open CategoryTheory Limits MonoidalCategory Opposite

open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltrationTests

variable (X : SimplicialObject SSet.{u})

example : SSet.outerLatching X 0 = ⊥ :=
  SSet.outerLatching_zero X

example (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n⦌)).obj a) :
    x ∈ (SSet.outerLatching X n).obj a ↔
      ∃ (m : ℕ) (_ : m < n) (q : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi q)
        (y : (X.obj (op ⦋m⦌)).obj a),
        x = (X.map q.op).app a y :=
  SSet.mem_outerLatching_iff X n a x

/-- In outer degree two, the second attachment overlaps the first precisely
where the same simplex lies in the images of `σ₀` and `σ₁`. -/
example (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋2⦌)).obj a) :
    x ∈ (SSet.outerLatchingStageOverlap X 1 (1 : Fin 2)).obj a ↔
      (∃ y : (X.obj (op ⦋1⦌)).obj a, (X.σ (0 : Fin 2)).app a y = x) ∧
      ∃ y : (X.obj (op ⦋1⦌)).obj a, (X.σ (1 : Fin 2)).app a y = x := by
  rw [SSet.mem_outerLatchingStageOverlap_iff]
  constructor
  · rintro ⟨⟨i, hi, y, hy⟩, hr⟩
    have hi0 : i = (0 : Fin 2) := by fin_cases i <;> simp_all
    subst i
    exact ⟨⟨y, hy⟩, hr⟩
  · rintro ⟨⟨y, hy⟩, hr⟩
    exact ⟨⟨0, by decide, y, hy⟩, hr⟩

noncomputable example (n : ℕ) :
    X.obj (op ⦋n⦌) ≅ (SSet.outerLatchingStage X n 0 : SSet.{u}) :=
  SSet.outerLatchingStage_zero_iso X n

example (n : ℕ) :
    SSet.outerLatchingStage X n (Fin.last n) =
      SSet.outerLatching X (n + 1) :=
  SSet.outerLatchingStage_last X n

example (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋1⦌)).obj a) :
    x ∈ (SSet.outerLatchingStageSourceOverlap X 1 (1 : Fin 2)).obj a ↔
      ∃ y : (X.obj (op ⦋1⦌)).obj a,
        (X.σ (0 : Fin 2)).app a y = (X.σ (1 : Fin 2)).app a x := by
  rw [SSet.mem_outerLatchingStageSourceOverlap_iff]
  constructor
  · rintro ⟨i, hi, y, hy⟩
    have hi0 : i = (0 : Fin 2) := by fin_cases i <;> simp_all
    subst i
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨0, by decide, y, hy⟩

example :
    SSet.outerLatchingStageSourceOverlap X 1 (1 : Fin 2) =
      SSet.outerLatchingStage X 0 (0 : Fin 1) :=
  SSet.outerLatchingStageSourceOverlap_succ X 0 (0 : Fin 1)

example (n : ℕ) (r : Fin (n + 1)) :
    IsPushout
      ((SSet.outerLatchingStageBefore X n r).fromPreimage (X.σ r))
      (SSet.outerLatchingStageSourceOverlap X n r).ι
      (SSet.Subcomplex.homOfLE (by
        rw [SSet.outerLatchingStage_eq_before_sup_range]
        exact le_sup_left))
      (SSet.outerDegeneracyToLatchingStage X n r) :=
  SSet.outerLatchingStageSource_isPushout X n r

section Diagonal

example (n : ℕ) (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n⦌)).obj a) (θ : (Δ[n] : SSet.{u}).obj a) :
    (SSet.diagonalCellMap X n).app a ⟨x, θ⟩ =
      (X.map (SSet.stdSimplex.objEquiv θ).op).app a x :=
  SSet.diagonalCellMap_app_apply X n a x θ

example (n : ℕ) (x : (X.obj (op ⦋n⦌)).obj (op ⦋n⦌)) :
    (SSet.diagonalCellMap X n).app (op ⦋n⦌)
        ⟨x, SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)⟩ = x :=
  SSet.diagonalCellMap_identity X n x

noncomputable example :
    ⨆ (n : ℕ), SSet.diagonalFiltration X n = ⊤ :=
  SSet.iSup_diagonalFiltration_eq_top X

noncomputable example :
    X.obj (op ⦋0⦌) ⊗ Δ[0] ≅
      (SSet.diagonalFiltration X 0 : SSet.{u}) :=
  SSet.diagonalFiltration_zero_iso X

example (n : ℕ) :
    SSet.diagonalAttachmentDomain X n =
      (SSet.diagonalFiltration X n).preimage
        (SSet.diagonalCellMap X (n + 1)) :=
  SSet.diagonalAttachmentDomain_eq_preimage X n

example (n : ℕ) :
    IsPushout (SSet.diagonalAttachmentTopMap X n)
      (SSet.diagonalAttachmentDomain X n).ι
      (SSet.diagonalFiltrationMap X (Nat.le_succ n))
      (SSet.diagonalCellToFiltrationSucc X n) :=
  SSet.diagonalFiltrationSucc_isPushout X n

end Diagonal

section Naturality

variable {X Y Z : SimplicialObject SSet.{u}}
variable (η : X ⟶ Y) (θ : Y ⟶ Z)

example (n : ℕ) :
    SSet.outerLatchingMap (η ≫ θ) n =
      SSet.outerLatchingMap η n ≫ SSet.outerLatchingMap θ n :=
  SSet.outerLatchingMap_comp η θ n

example (n : ℕ) (r : Fin (n + 1)) :
    SSet.outerLatchingStageSourceOverlapMap η n r ≫
        (SSet.outerLatchingStageBefore Y n r).fromPreimage (Y.σ r) =
      (SSet.outerLatchingStageBefore X n r).fromPreimage (X.σ r) ≫
        SSet.outerLatchingStageBeforeMap η n r :=
  SSet.outerLatchingStageSource_top_naturality η n r

example (n : ℕ) (r : Fin (n + 1)) :
    SSet.outerLatchingStageSourceOverlapMap η n r ≫
        (SSet.outerLatchingStageSourceOverlap Y n r).ι =
      (SSet.outerLatchingStageSourceOverlap X n r).ι ≫
        η.app (op ⦋n⦌) :=
  SSet.outerLatchingStageSource_left_naturality η n r

example (n : ℕ) (r : Fin (n + 1)) :
    SSet.outerLatchingStageBeforeMap η n r ≫
        (SSet.Subcomplex.homOfLE (by
          rw [SSet.outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (SSet.outerLatchingStageBefore Y n r : SSet.{u}) ⟶
            SSet.outerLatchingStage Y n r) =
      (SSet.Subcomplex.homOfLE (by
          rw [SSet.outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (SSet.outerLatchingStageBefore X n r : SSet.{u}) ⟶
            SSet.outerLatchingStage X n r) ≫
        SSet.outerLatchingStageMap η n r :=
  SSet.outerLatchingStageSource_right_naturality η n r

example (n : ℕ) (r : Fin (n + 1)) :
    η.app (op ⦋n⦌) ≫ SSet.outerDegeneracyToLatchingStage Y n r =
      SSet.outerDegeneracyToLatchingStage X n r ≫
        SSet.outerLatchingStageMap η n r :=
  SSet.outerLatchingStageSource_bottom_naturality η n r

example (n : ℕ) :
    (η.app (op ⦋n⦌) ⊗ₘ 𝟙 Δ[n]) ≫ SSet.diagonalCellMap Y n =
      SSet.diagonalCellMap X n ≫
        SSet.simplicialDiagonalFunctor.map η :=
  SSet.diagonalCellMap_naturality η n

example (n : ℕ) :
    SSet.diagonalFiltrationNatMap (η ≫ θ) n =
      SSet.diagonalFiltrationNatMap η n ≫
        SSet.diagonalFiltrationNatMap θ n :=
  SSet.diagonalFiltrationNatMap_comp η θ n

example (n : ℕ) :
    SSet.diagonalAttachmentDomainMap η n ≫
        SSet.diagonalAttachmentTopMap Y n =
      SSet.diagonalAttachmentTopMap X n ≫
        SSet.diagonalFiltrationNatMap η n :=
  SSet.diagonalAttachmentTopMap_naturality η n

example (n : ℕ) :
    (η.app (op ⦋n + 1⦌) ⊗ₘ 𝟙 Δ[n + 1]) ≫
        SSet.diagonalCellToFiltrationSucc Y n =
      SSet.diagonalCellToFiltrationSucc X n ≫
        SSet.diagonalFiltrationNatMap η (n + 1) :=
  SSet.diagonalCellToFiltrationSucc_naturality η n

end Naturality

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltrationTests
