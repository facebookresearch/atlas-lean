/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import MathlibExt.CategoryTheory.DGSourceMore.HomologyEmbeddingTruncLE

/-!
# Actual isotropic closing-data paths and the normalized residue class

Isotropy is a path in the genuine global weighted NC space. Given paths
h:0→a, u:a→b and k:0→b, the normalized loop is the literal simplicial
module element h+u-k-s₀(a). Both faces vanish. The native alternating
chain projection, Dold--Kan counit, good truncation and shift identify
its class with H^(n-3)(NC^w(X)(2)), namely a closed two-form class of
degree n-1. No freely selected loop/degree-shift isomorphism appears.

Obtaining u from the actual derived-intersection universal homotopy,
and proving Lagrangian/nondegeneracy, are separate construction/proof
requirements. The path and residue definitions do not assume them.

Reference: PTVV arXiv:1111.3209v4, Definitions 2.7--2.8 and
Theorem 2.9, pp.38--40. Native normalized-chain and homology maps are
completed Mathlib operations; the good-truncation bridge retains its
Tau Ceti Apache source notices in DGSourceMore.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicTopology
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
variable {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
variable {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {X : Prestack k}

/-- The actual simplicial coefficient module of the closed two-form space. -/
def closedModules (G : GlobalNCModel D 2 NC X) (n : ℤ) :
    SimplicialObject (ModuleCat.{u + 1} k) :=
  Idempotents.DoldKan.Γ.obj (((ncComplex G)⟦n - (2 : ℤ)⟧).truncLE'
    ComplexShape.embeddingDownNat)

/-- Actual isotropic data, retaining the entire one-simplex of NC closing coefficients. -/
abbrev IsotropicPath (G : GlobalNCModel D 2 NC X) (n : ℤ) (ω : ClosedForm G n) :=
  SSet.Edge (X := closedSpace G n) (zeroForm G n) ω

/-- The three source paths of the derived-intersection residue loop. -/
structure ResiduePaths (G : GlobalNCModel D 2 NC X) (n : ℤ) where
  left : ClosedForm G n
  right : ClosedForm G n
  first : IsotropicPath G n left
  comparison : SSet.Edge (X := closedSpace G n) left right
  second : IsotropicPath G n right

/-- The actual normalized edge sum representing h⋅u⋅k⁻¹ in the simplicial module. -/
def residueTerm {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    (closedModules G n) _⦋1⦌ :=
  (show (closedModules G n) _⦋1⦌ from P.first.edge) +
    (show (closedModules G n) _⦋1⦌ from P.comparison.edge) -
      (show (closedModules G n) _⦋1⦌ from P.second.edge) -
        (closedModules G n).σ 0 (show (closedModules G n) _⦋0⦌ from P.left)

/-- The normalized residue edge has zero source. -/
theorem residueTerm_source {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    ((closedModules G n).δ 1).hom (residueTerm P) = 0 := by
  have hs := congrArg (fun f : (closedModules G n) _⦋0⦌ ⟶ _ => f P.left)
    ((closedModules G n).δ_comp_σ_succ (i := (0 : Fin 1)))
  change ((closedModules G n).δ 1).hom ((closedModules G n).σ 0 P.left) = P.left at hs
  have h₁ : ((closedModules G n).δ 1).hom P.first.edge = 0 := P.first.src_eq
  have h₂ : ((closedModules G n).δ 1).hom P.comparison.edge = P.left := P.comparison.src_eq
  have h₃ : ((closedModules G n).δ 1).hom P.second.edge = 0 := P.second.src_eq
  simp only [residueTerm, map_sub, map_add, h₁, h₂, h₃, hs]
  change (0 : (closedModules G n) _⦋0⦌) +
    (show (closedModules G n) _⦋0⦌ from P.left) - 0 -
      (show (closedModules G n) _⦋0⦌ from P.left) = 0
  abel

/-- The same edge has zero target, so it is a genuine based loop cycle. -/
theorem residueTerm_target {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    ((closedModules G n).δ 0).hom (residueTerm P) = 0 := by
  have hs := congrArg (fun f : (closedModules G n) _⦋0⦌ ⟶ _ => f P.left)
    ((closedModules G n).δ_comp_σ_self (i := (0 : Fin 1)))
  change ((closedModules G n).δ 0).hom ((closedModules G n).σ 0 P.left) = P.left at hs
  have h₁ : ((closedModules G n).δ 0).hom P.first.edge = P.left := P.first.tgt_eq
  have h₂ : ((closedModules G n).δ 0).hom P.comparison.edge = P.right := P.comparison.tgt_eq
  have h₃ : ((closedModules G n).δ 0).hom P.second.edge = P.right := P.second.tgt_eq
  simp only [residueTerm, map_sub, map_add, h₁, h₂, h₃, hs]
  change (show (closedModules G n) _⦋0⦌ from P.left) +
    (show (closedModules G n) _⦋0⦌ from P.right) -
      (show (closedModules G n) _⦋0⦌ from P.right) -
        (show (closedModules G n) _⦋0⦌ from P.left) = 0
  abel

/-- The actual alternating-chain representative is a cycle. -/
theorem residueTerm_cycle {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    ((AlternatingFaceMapComplex.obj (closedModules G n)).d 1 0).hom (residueTerm P) = 0 := by
  change (AlternatingFaceMapComplex.objD (closedModules G n) 0).hom (residueTerm P) = 0
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (closedModules G n).δ i).hom (residueTerm P) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one,
    pow_one, neg_smul, one_smul, ModuleCat.hom_add, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.neg_apply, residueTerm_source, residueTerm_target,
    neg_zero, add_zero]

/-- The native alternating-chain homology class of the displayed loop. -/
def alternatingResidueClass {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    (AlternatingFaceMapComplex.obj (closedModules G n)).homology 1 :=
  let f : ModuleCat.of k (ULift.{u + 1} k) ⟶
      (AlternatingFaceMapComplex.obj (closedModules G n)).X 1 :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton k _ (residueTerm P)).comp
      (ULift.moduleEquiv : ULift.{u + 1} k ≃ₗ[k] k).toLinearMap)
  ((AlternatingFaceMapComplex.obj (closedModules G n)).liftCycles f 0
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 by decide)) (by
    ext r
    change ((AlternatingFaceMapComplex.obj (closedModules G n)).d 1 0).hom
      (r.down • residueTerm P) = 0
    rw [map_smul, residueTerm_cycle, smul_zero]) ≫
      (AlternatingFaceMapComplex.obj (closedModules G n)).homologyπ 1) (ULift.up (1 : k))

/-- The source-fixed degree shift is native normalization, DK counit, truncation and shift. -/
def loopShiftHomologyIso (G : GlobalNCModel D 2 NC X) (n : ℤ) :
    ((normalizedMooreComplex (ModuleCat.{u + 1} k)).obj (closedModules G n)).homology 1 ≅
      (ncComplex G).homology (n - 3) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} k) (.down ℕ) 1).mapIso
    ((CategoryTheory.Abelian.DoldKan.equivalence (A := ModuleCat.{u + 1} k)).counitIso.app
      (((ncComplex G)⟦n - (2 : ℤ)⟧).truncLE' ComplexShape.embeddingDownNat)) ≪≫
  ((ncComplex G)⟦n - (2 : ℤ)⟧).truncLE'HomologyIso ComplexShape.embeddingDownNat 1 ≪≫
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} k) (.up ℤ) 0).shiftIso
    (n - (2 : ℤ)) (-1 : ℤ) (n - 3) (by omega)).app (ncComplex G)

/-- The actual canonical residue closed-form class, in degree n-1 for p=2. -/
def residueClass {G : GlobalNCModel D 2 NC X} {n : ℤ} (P : ResiduePaths G n) :
    (ncComplex G).homology (n - 3) :=
  (loopShiftHomologyIso G n).hom
    ((HomologicalComplex.homologyMap
      (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (closedModules G n)) 1)
        (alternatingResidueClass P))

end MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
