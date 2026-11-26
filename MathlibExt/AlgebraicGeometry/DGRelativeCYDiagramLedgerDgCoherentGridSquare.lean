/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGRelativeCYCospanGluing

/-!
# DG coherent grid squares

Proves `dg_coherent_grid_square`: the square's degree -1 cell is the signed
difference of its two native chain cells, with boundary the difference of the
two composed arrows.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, Theorems 6.1 and 6.2,
Definition 4.11 and diagrams 6.5--6.7. The ground ring is a field; this
composition theorem has no characteristic-zero restriction.
-/

namespace WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.CategoryTheory.DGRelativeCYCospanGluing
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels

universe u

private theorem chain_prefix_eq (a b c : GridIndex) (hab : a < b) (hbc : b < c) :
    (chainGenerator a b c hab hbc).prefix (0 : Fin 1) = directGenerator a b hab := by
  have hvert : ((chainGenerator a b c hab hbc).prefix (0 : Fin 1)).vertices =
      (directGenerator a b hab).vertices := by
    funext j
    fin_cases j <;> rfl
  cases h1 : (chainGenerator a b c hab hbc).prefix (0 : Fin 1)
  cases h2 : directGenerator a b hab
  simp_all
  rfl

private theorem chain_suffix_eq (a b c : GridIndex) (hab : a < b) (hbc : b < c) :
    (chainGenerator a b c hab hbc).suffix (0 : Fin 1) = directGenerator b c hbc := by
  have hvert : ((chainGenerator a b c hab hbc).suffix (0 : Fin 1)).vertices =
      (directGenerator b c hbc).vertices := by
    funext j
    fin_cases j <;> rfl
  cases h1 : (chainGenerator a b c hab hbc).suffix (0 : Fin 1)
  cases h2 : directGenerator b c hbc
  simp_all
  rfl

private theorem chain_face_eq (a b c : GridIndex) (hab : a < b) (hbc : b < c)
    (hac : a < c) :
    (chainGenerator a b c hab hbc).face (0 : Fin 1) = directGenerator a c hac := by
  have hvert : ((chainGenerator a b c hab hbc).face (0 : Fin 1)).vertices =
      (directGenerator a c hac).vertices := by
    funext j
    fin_cases j <;> rfl
  cases h1 : (chainGenerator a b c hab hbc).face (0 : Fin 1)
  cases h2 : directGenerator a c hac
  simp_all

private theorem chain_cell_eq {k : Type u} [Field k] (R : CoherentIndexModel k GridIndex)
    (a b c : GridIndex) (hab : a < b) (hbc : b < c) (hac : a < c) :
    dgDifferential k (-((1 : ℕ) : ℤ)) (R.cell (chainGenerator a b c hab hbc)) =
      degreeCast (dgHomComplex k (R.objects.symm a) (R.objects.symm c)) (by omega)
        (R.cell (directGenerator a c hac)) -
      dgComp k (p := 0) (q := 0) (n := 0)
        (R.cell (directGenerator a b hab)) (R.cell (directGenerator b c hbc)) (zero_add 0) := by
  have hcell : dgDifferential k (-((1 : ℕ) : ℤ)) (R.cell (chainGenerator a b c hab hbc)) =
      degreeCast (dgHomComplex k (R.objects.symm a) (R.objects.symm c)) (by omega)
        (R.cell ((chainGenerator a b c hab hbc).face (0 : Fin 1))) -
      dgComp k (R.cell ((chainGenerator a b c hab hbc).prefix (0 : Fin 1)))
        (R.cell ((chainGenerator a b c hab hbc).suffix (0 : Fin 1))) (by omega) := by
    have h := R.cell_boundary (chainGenerator a b c hab hbc)
    simpa using h
  rw [hcell]
  have hpre : R.cell ((chainGenerator a b c hab hbc).prefix (0 : Fin 1)) =
      R.cell (directGenerator a b hab) := by
    rw [chain_prefix_eq]
    rfl
  have hsuf : R.cell ((chainGenerator a b c hab hbc).suffix (0 : Fin 1)) =
      R.cell (directGenerator b c hbc) := by
    rw [chain_suffix_eq]
    rfl
  have hface : R.cell ((chainGenerator a b c hab hbc).face (0 : Fin 1)) =
      R.cell (directGenerator a c hac) := by
    rw [chain_face_eq _ _ _ _ _ hac]
  rw [hface, hpre, hsuf]
  rfl

private theorem cochain_chain_eq {k : Type u} [Field k] (R : CoherentIndexModel k GridIndex)
    (C : DGCat k) (Q : CoherentDiagram R C) (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (a b c : GridIndex) (hab : a < b) (hbc : b < c) (hac : a < c) :
    dgDifferential k (-1) (cochainAtNodes Q nodes eq (chainGenerator a b c hab hbc)) =
      moduleCycle (arrowAtNodes Q nodes eq a c hac) -
        moduleCycle (arrowAtNodes Q nodes eq a b hab ≫ arrowAtNodes Q nodes eq b c hbc) := by
  have hcomp : ∀ {M N P : RightModule k C} (f : M ⟶ N) (g : N ⟶ P),
      moduleCycle (f ≫ g) =
        dgComp k (p := 0) (q := 0) (n := 0) (moduleCycle f) (moduleCycle g) (zero_add 0) := by
    intro M N P f g
    have h := DGFunctor.homEquivDGCycles_comp (R := k) (α := f) (β := g)
    simp [moduleCycle, dgCompZero_def] at h ⊢
  have hsymm : ∀ {M N : RightModule k C} (x : DGHom k 0 M N) (hx : x ∈ dgCycles k M N),
      moduleCycle ((DGFunctor.homEquivDGCycles k M N).symm ⟨x, hx⟩) = x := by
    intro M N x hx
    simp [moduleCycle]
  have harrow : ∀ (x y : GridIndex) (hxy : x < y),
      moduleCycle (arrowAtNodes Q nodes eq x y hxy) =
        dgComp k (p := 0) (q := 0) (n := 0) (moduleCycle (eqToHom (eq x).symm))
          (dgComp k (p := 0) (q := 0) (n := 0)
            (Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator x y hxy)))
            (moduleCycle (eqToHom (eq y))) (zero_add 0)) (zero_add 0) := by
    intro x y hxy
    unfold arrowAtNodes
    rw [hcomp, hcomp, hsymm]
  have hid : ∀ (M : RightModule k C),
      moduleCycle (𝟙 M) = dgId k M := by
    intro M
    have h := DGFunctor.homEquivDGCycles_id (R := k) (F := M)
    simp [moduleCycle] at h ⊢
  have hmiddle : ∀ (q : GridIndex),
      dgComp k (p := 0) (q := 0) (n := 0)
        (moduleCycle (eqToHom (eq q))) (moduleCycle (eqToHom (eq q).symm)) (zero_add 0) =
        dgId k (Q.toEnrichedFunctor.obj (R.objects.symm q)) := by
    intro q
    have hcancel : eqToHom (eq q) ≫ eqToHom (eq q).symm = 𝟙 _ := by simp
    calc dgComp k (moduleCycle (eqToHom (eq q))) (moduleCycle (eqToHom (eq q).symm)) (zero_add 0)
        = moduleCycle (eqToHom (eq q) ≫ eqToHom (eq q).symm) := (hcomp _ _).symm
      _ = moduleCycle (𝟙 _) := by rw [hcancel]
      _ = dgId k _ := hid _
  have harrow_comp : ∀ (x y z : GridIndex) (hxy : x < y) (hyz : y < z),
      moduleCycle (arrowAtNodes Q nodes eq x y hxy ≫ arrowAtNodes Q nodes eq y z hyz) =
        dgComp k (p := 0) (q := 0) (n := 0) (moduleCycle (eqToHom (eq x).symm))
          (dgComp k (p := 0) (q := 0) (n := 0)
            (dgComp k (p := 0) (q := 0) (n := 0)
              (Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator x y hxy)))
              (Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator y z hyz))) (zero_add 0))
            (moduleCycle (eqToHom (eq z))) (zero_add 0)) (zero_add 0) := by
    intro x y z hxy hyz
    rw [hcomp, harrow, harrow]
    set La := moduleCycle (eqToHom (eq x).symm) with hLa
    set Mab := Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator x y hxy)) with hMab
    set Rb := moduleCycle (eqToHom (eq y)) with hRb
    set Lb := moduleCycle (eqToHom (eq y).symm) with hLb
    set Mbc := Q.toEnrichedFunctor.dgMap 0 (R.cell (directGenerator y z hyz)) with hMbc
    set Rc := moduleCycle (eqToHom (eq z)) with hRc
    set X := dgComp k (p := 0) (q := 0) (n := 0) Mab Rb (zero_add 0) with hX
    set Z := dgComp k (p := 0) (q := 0) (n := 0) Mbc Rc (zero_add 0) with hZ
    set Y := dgComp k (p := 0) (q := 0) (n := 0) Lb Z (zero_add 0) with hY
    have step1 : dgComp k (p := 0) (q := 0) (n := 0)
          (dgComp k (p := 0) (q := 0) (n := 0) La X (zero_add 0)) Y (zero_add 0) =
        dgComp k (p := 0) (q := 0) (n := 0) La
          (dgComp k (p := 0) (q := 0) (n := 0) X Y (zero_add 0)) (zero_add 0) :=
      dgComp_assoc k _ _ _ (zero_add 0) (zero_add 0) (by omega)
    rw [step1]
    have step2 : dgComp k (p := 0) (q := 0) (n := 0) X Y (zero_add 0) =
        dgComp k (p := 0) (q := 0) (n := 0) Mab
          (dgComp k (p := 0) (q := 0) (n := 0) Rb Y (zero_add 0)) (zero_add 0) := by
      rw [hX]
      exact dgComp_assoc k _ _ _ (zero_add 0) (zero_add 0) (by omega)
    rw [step2]
    have step3 : dgComp k (p := 0) (q := 0) (n := 0) Rb Y (zero_add 0) =
        dgComp k (p := 0) (q := 0) (n := 0)
          (dgComp k (p := 0) (q := 0) (n := 0) Rb Lb (zero_add 0)) Z (zero_add 0) := by
      rw [hY]
      exact (dgComp_assoc k _ _ _ (zero_add 0) (zero_add 0) (by omega)).symm
    rw [step3]
    have hmid : dgComp k (p := 0) (q := 0) (n := 0) Rb Lb (zero_add 0) =
        dgId k (Q.toEnrichedFunctor.obj (R.objects.symm y)) := hmiddle y
    rw [hmid]
    have step5 : dgComp k (p := 0) (q := 0) (n := 0)
          (dgId k (Q.toEnrichedFunctor.obj (R.objects.symm y))) Z (zero_add 0) = Z :=
      dgId_dgComp k Z
    rw [step5]
    have step6 : dgComp k (p := 0) (q := 0) (n := 0) Mab Z (zero_add 0) =
        dgComp k (p := 0) (q := 0) (n := 0)
          (dgComp k (p := 0) (q := 0) (n := 0) Mab Mbc (zero_add 0)) Rc (zero_add 0) := by
      rw [hZ]
      exact (dgComp_assoc k _ _ _ (zero_add 0) (zero_add 0) (by omega)).symm
    rw [step6]
  have hcochain : dgDifferential k (-1) (cochainAtNodes Q nodes eq (chainGenerator a b c hab hbc)) =
      dgComp k (p := 0) (q := 0) (n := 0) (moduleCycle (eqToHom (eq a).symm))
        (dgComp k (p := 0) (q := 0) (n := 0)
          (Q.toEnrichedFunctor.dgMap 0
            (dgDifferential k (-((1 : ℕ) : ℤ)) (R.cell (chainGenerator a b c hab hbc))))
          (moduleCycle (eqToHom (eq c))) (zero_add 0)) (zero_add 0) := by
    unfold cochainAtNodes
    have hL : dgDifferential k 0 (moduleCycle (eqToHom (eq a).symm)) = 0 := by
      exact (mem_dgCycles k).mp (DGFunctor.homEquivDGCycles k _ _ _).property
    have hR : dgDifferential k 0 (moduleCycle (eqToHom (eq c))) = 0 := by
      exact (mem_dgCycles k).mp (DGFunctor.homEquivDGCycles k _ _ _).property
    rw [dgDifferential_dgComp]
    simp only [hL, zero_dgComp, zero_add]
    simp only [Int.negOnePow_zero, one_smul]
    congr 1
    rw [dgDifferential_dgComp]
    simp only [hR, dgComp_zero, smul_zero, add_zero]
    congr 1
    have hdg := Q.toEnrichedFunctor.dgMap_dgDifferential
      (R.cell (chainGenerator a b c hab hbc))
    simpa only [Int.cast_ofNat_Int, Int.reduceNeg, Int.reduceAdd] using hdg.symm
  rw [hcochain, chain_cell_eq R a b c hab hbc hac]
  have hdeg : ∀ (x : DGHom k 0 (R.objects.symm a) (R.objects.symm c)),
      Q.toEnrichedFunctor.dgMap 0
        (degreeCast (dgHomComplex k (R.objects.symm a) (R.objects.symm c)) (by omega) x) =
        Q.toEnrichedFunctor.dgMap 0 x := by
    intro x
    simp [degreeCast]
  rw [map_sub]
  simp only [EnrichedFunctor.dgMap_dgComp]
  rw [hdeg]
  simp only [sub_eq_add_neg, dgComp_add, dgComp_neg, add_dgComp, neg_dgComp]
  rw [← harrow a c hac, ← harrow_comp a b c hab hbc]

/-- The square's degree -1 cell is the signed difference of its two native chain cells. -/
public theorem dg_coherent_grid_square (k : Type u) [Field k]
    (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) : CoherentSquareModel Q nodes eq s := by
  refine ⟨?_⟩
  unfold squareCell
  rw [map_sub]
  have hac : s.topLeft < s.bottomRight := lt_trans s.left_lt s.bottom_lt
  rw [cochain_chain_eq R C Q nodes eq s.topLeft s.bottomLeft s.bottomRight
    s.left_lt s.bottom_lt hac]
  rw [cochain_chain_eq R C Q nodes eq s.topLeft s.topRight s.bottomRight
    s.top_lt s.right_lt hac]
  abel

end WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted
