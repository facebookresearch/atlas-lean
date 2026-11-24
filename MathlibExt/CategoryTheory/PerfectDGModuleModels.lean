/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGSourceMore.DGOneSided
public import MathlibExt.CategoryTheory.DGSourceMore.DGKaroubi
public import MathlibExt.CategoryTheory.DGSourceMore.DGSimplicial
public import MathlibExt.CategoryTheory.DGScalarNerveMaps
public import MathlibExt.CategoryTheory.DGQuasiFunctorModels
public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Actual finite-cell modules and enhanced perfect DG objects

Finite cells are the native one-sided twisted complexes of finite sums
of shifts. Their right modules are the actual enriched representables
in that finite-cell category, restricted along the original embedding.
Their terms, differential and module action are inherited from the
source shift/matrix/twisted Hom complexes.

A perfect module is a retract of one of these literal finite-cell
modules in the actual quasi-isomorphism localization of right modules.
The enhanced perfect category is the full DG category of cofibrant
such modules. Only the membership test uses a localization; every
enhanced Hom complex retains the original DG-module enrichment.

Small realizations and coherent-nerve quasicategory laws are separate
construction outputs. The closed-idempotent Karoubi source does not
silently replace general homotopy retracts by strict idempotents.

References: Keller, Deriving DG categories, §§2--3; Toën--Vaquié,
arXiv:math/0503269v5, §2.2; BGT, arXiv:1001.2282v4, §§3--4.
Complete finite-cell and DG primitive source ports retain their pinned
Apache attribution in DGSource and DGSourceMore.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.PerfectDGModuleModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels

universe u v

variable {k : Type u} [CommRing k]

/-- The actual shifted finite sums with a Maurer--Cartan differential. -/
abbrev TwistedCells (C : DGCat k) :=
  DGTwistedObject k (DGAdditiveClosure (DGShiftClosure C))

/-- The actual finite-cell DG category retains all twisted Hom complexes. -/
abbrev FiniteCellDG (C : DGCat k) :=
  DGFullSubcategory (fun P : TwistedCells C => P.IsOneSided)

/-- The native embedding into shifted sums and zero twists. -/
def rawCellEmbedding (C : DGCat k) :
    EnrichedFunctor (Cochains k) C (TwistedCells C) :=
  ((DGShiftClosure.ι k).comp (Cochains k) (DGAdditiveClosure.embedding k)).comp
    (Cochains k) (DGTwistedObject.embedding k)

/-- The same embedding lands in the actual one-sided full subcategory. -/
def cellEmbedding (C : DGCat k) : EnrichedFunctor (Cochains k) C (FiniteCellDG C) where
  obj x := ⟨(rawCellEmbedding C).obj x, by
    exact DGTwistedObject.isOneSided_ofObj
      ((DGAdditiveClosure.embedding k).obj ((DGShiftClosure.ι k).obj x))⟩
  map x y := (rawCellEmbedding C).map x y
  map_id x := (rawCellEmbedding C).map_id x
  map_comp x y z := (rawCellEmbedding C).map_comp x y z

/-- The actual finite-cell right module: Hom_pretr(i(-),P). -/
def cellModule {C : DGCat k} (P : FiniteCellDG C) : RightModule k C :=
  ⟨(cellEmbedding C).op.comp (Cochains k) (dgRepresentable k P)⟩

/-- Every module value is the literal source twisted Hom complex. -/
theorem cellModule_value {C : DGCat k} (P : FiniteCellDG C) (y : Cᵒᵖ) :
    (cellModule P).toEnrichedFunctor.obj y =
      dgHomComplex k ((cellEmbedding C).obj y.unop) P := rfl

/-- Perfection uses actual localized retraction maps onto the native finite cell. -/
def IsPerfectModule (C : DGCat k) (M : RightModule k C) : Prop :=
  ∃ P : FiniteCellDG C,
    ∃ (i : (moduleQ (fun y => canonicalEvaluation y)).obj M ⟶
          (moduleQ (fun y => canonicalEvaluation y)).obj (cellModule P))
      (r : (moduleQ (fun y => canonicalEvaluation y)).obj (cellModule P) ⟶
          (moduleQ (fun y => canonicalEvaluation y)).obj M),
      i ≫ r = 𝟙 ((moduleQ (fun y => canonicalEvaluation y)).obj M)

/-- The full enhanced Perf category has genuine cofibrant DG-module Hom complexes. -/
abbrev PerfectDGCategory (C : DGCat k) :=
  DGFullSubcategory (fun M : RightModule k C => IsCofibrantModule M ∧ IsPerfectModule C M)

/-- A genuine small DG realization of this particular enhanced perfect category. -/
structure SmallPerfectModel (C : DGCat k) where
  category : DGCat k
  realization : EnrichedFunctor (Cochains k) category (PerfectDGCategory C)
  quasiEquivalence : realization.IsQuasiEquivalence

/-- The actual locally Kan simplicial category, with source DG/AW composition. -/
abbrev DGSimplicial (C : Type v) [DGCategory k C] :=
  ForgetEnrichment SSet.{u} (DGSimplicialCategory k C)

/-- The native homotopy-coherent nerve retains every enriched simplex. It is
`DGScalarNerveMaps.coherentNerve`, the nerve of `DGSimplicial C`. -/
abbrev dgNerve (C : Type v) [DGCategory k C] : SSet.{max u v} :=
  DGScalarNerveMaps.coherentNerve (R := k) C

/-- The actual coherent nerve of a chosen small perfect realization. -/
def perfectNerve {C : DGCat k} (P : SmallPerfectModel C) : SSet.{u} :=
  dgNerve (k := k) P.category

end MathlibExt.CategoryTheory.PerfectDGModuleModels
