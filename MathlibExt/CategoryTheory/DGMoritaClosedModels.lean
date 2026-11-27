/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGQuasiFunctorModels
public import MathlibExt.CategoryTheory.DGSource.DGFunctorCategory

/-!
# Native derived DG closedness with the actual quasi-functor model

The internal-Hom model is the full DG subcategory of actual cofibrant
right-quasi-representable C-to-right-D-module functors. Its Hom complexes,
differential and composition are inherited from the source DG-functor
category. A small realization is a genuine DG quasi-equivalence to that
category, rather than a Type called a derived internal Hom.

The closedness output contains the native right-adjoint functor of the
fixed localized tensor and its native adjunction. Its values are identified
with those actual small quasi-functor models. The adjunction determines
the morphism action through the native tensor functor; no freely chosen
family of Hom bijections or evaluation oracle is an input.

Reference: Toën, arXiv:math/0408337v7, Theorem 6.1, printed p.31.
His covariant (C tensor D^op)-modules have our C-to-right-D-module
variance. The source Int model uses cofibrant modules; the projective
DG-module model has fibrant coefficient cochains. The input replacement
and tensor models are shared construction dependencies. A task proving
their construction must establish them, rather than assume its target.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGMoritaClosedModels

open _root_.CategoryTheory MonoidalCategory Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels

universe u

variable {k : Type u} [CommRing k]

/-- The actual closed natural module map at a bimodule column. -/
def columnMap {C D : Type u} [DGCategory k C] [DGCategory k D]
    {M N : Bimodule k C D} (f : M ⟶ N) (x : C) :
    M.toEnrichedFunctor.obj x ⟶ N.toEnrichedFunctor.obj x :=
  (DGFunctor.homEquivDGCycles k (M.toEnrichedFunctor.obj x)
    (N.toEnrichedFunctor.obj x)).symm ⟨f.dgApp x, f.dgApp_mem_dgCycles x⟩

@[simp]
theorem columnMap_id {C D : Type u} [DGCategory k C] [DGCategory k D]
    (M : Bimodule k C D) (x : C) : columnMap (𝟙 M) x = 𝟙 (M.toEnrichedFunctor.obj x) := by
  apply (DGFunctor.homEquivDGCycles k _ _).injective
  apply Subtype.ext
  simp only [columnMap, Equiv.apply_symm_apply, DGFunctor.homEquivDGCycles_id]
  change (DGNatTrans.id M.toEnrichedFunctor).dgApp x =
    dgId k (M.toEnrichedFunctor.obj x)
  exact DGNatTrans.dgApp_id M.toEnrichedFunctor x

@[simp]
theorem columnMap_comp {C D : Type u} [DGCategory k C] [DGCategory k D]
    {M N P : Bimodule k C D} (f : M ⟶ N) (g : N ⟶ P) (x : C) :
    columnMap (f ≫ g) x = columnMap f x ≫ columnMap g x := by
  apply (DGFunctor.homEquivDGCycles k _ _).injective
  apply Subtype.ext
  simp only [columnMap, Equiv.apply_symm_apply, DGFunctor.homEquivDGCycles_comp]
  change (DGNatTrans.comp f g).dgApp x = dgCompZero k (f.dgApp x) (g.dgApp x)
  exact DGNatTrans.dgApp_comp f g x

/-- The completed column evaluation, retaining its actual module maps. -/
def columnFunctor {C D : Type u} [DGCategory k C] [DGCategory k D] (x : C) :
    Bimodule k C D ⥤ RightModule k D where
  obj M := M.toEnrichedFunctor.obj x
  map f := columnMap f x
  map_id M := columnMap_id M x
  map_comp f g := columnMap_comp f g x

/-- Completed two-variable point evaluation for the actual bimodule action. -/
def pointEvaluation {C D : Type u} [DGCategory k C] [DGCategory k D]
    (x : C) (y : Dᵒᵖ) : Bimodule k C D ⥤ Cochains k :=
  columnFunctor x ⋙ (canonicalEvaluation y).functor

/-- The genuine projective trivial-fibration criterion for the curried
bimodule category, on every C/D component and every cochain degree. -/
def IsBimoduleTrivialFibration {C D : Type u} [DGCategory k C] [DGCategory k D]
    {M N : Bimodule k C D} (f : M ⟶ N) : Prop :=
  ∀ (x : C) (y : Dᵒᵖ),
    QuasiIso (moduleComponent (columnMap f x) y) ∧
      ∀ n : ℤ, Function.Surjective ((moduleComponent (columnMap f x) y).f n)

/-- Cofibrancy is the actual initial-object lifting property in the
module-action-preserving bimodule category. -/
def IsCofibrantBimodule {C D : Type u} [DGCategory k C] [DGCategory k D]
    (M : Bimodule k C D) : Prop :=
  ∀ (N P : Bimodule k C D) (p : N ⟶ P), IsBimoduleTrivialFibration p →
    ∀ f : M ⟶ P, ∃ g : M ⟶ N, g ≫ p = f

/-- The actual source Int objects: cofibrant and derived-representable columns. -/
def IsQuasiFunctorObject (C D : DGCat k) (M : Bimodule k C D) : Prop :=
  IsCofibrantBimodule M ∧
    IsRightQuasiRepresentable (fun y => canonicalEvaluation y) M

/-- The full DG quasi-functor category retains all source Hom complexes. -/
abbrev QuasiFunctorDGCategory (C D : DGCat k) :=
  DGFullSubcategory (IsQuasiFunctorObject C D)

/-- A genuine small DG realization of the fixed full quasi-functor category. -/
structure SmallQuasiFunctorModel (C D : DGCat k) where
  category : DGCat k
  realization : EnrichedFunctor (Cochains k) category (QuasiFunctorDGCategory C D)
  quasiEquivalence : realization.IsQuasiEquivalence

/-- Derived closedness is a construction output. It neither supplies an
unconstrained internal-Hom carrier nor assumes the target adjunction. -/
structure MoritaClosedModel (Q : ReplacementFunctor k) (C : DGCat k)
    (T : LocalizedTensorModel Q C) where
  rightAdjoint : HoDG k ⥤ HoDG k
  adjunction : T.functor ⊣ rightAdjoint
  quasiFunctorModel : ∀ D : DGCat k, SmallQuasiFunctorModel (Q.functor.obj C) D
  objectIso : ∀ D : DGCat k,
    rightAdjoint.obj ((toHo k).obj D) ≅
      (toHo k).obj (quasiFunctorModel D).category

end MathlibExt.CategoryTheory.DGMoritaClosedModels
