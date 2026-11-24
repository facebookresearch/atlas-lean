/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGMoritaClosedModels
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
public import MathlibExt.CategoryTheory.DGSource.DGFullSubcategory

/-!
# Tensor-graph normalization of the native Morita adjunction

Strict tensor functors are curried through their actual Yoneda graph.
The column isomorphisms are maps of right modules, and every homogeneous
E/C tensor action is fixed. A single enriched bimodule replacement
functor retains all morphisms and the full E-action before passage to
the small right-quasi-representable model.

The normalized closedness constructor chooses the adjunction and its
object comparisons together. Its Hom equivalence is fixed on every
strict functor E tensor Q(C) to D, using the actual Q(E)-augmentation,
graph currying and source-normalized small realization.

Source: Toën, arXiv:math/0408337v7, Theorem6.1 and its proof, printed
pp31–34; Keller, Deriving DG categories, §6. Native enriched tensor,
DG-functor and module operations retain the pinned TauCeti notices in
the imported source ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGMoritaGraphCurryingModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGMoritaClosedModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open scoped TensorProduct

universe u v
variable {k : Type u} [CommRing k]

/-- Graph columns are cofibrant right modules. The enriched bar
replacement is used on this actual full subcategory. -/
def HasCofibrantColumns (C D : DGCat k) (M : Bimodule k C D) : Prop :=
  ∀ c : C, IsCofibrantModule (M.toEnrichedFunctor.obj c)

abbrev ColumnCofibrantBimodules (C D : DGCat k) :=
  DGFullSubcategory (HasCofibrantColumns C D)

/-- The literal homogeneous generator of the source tensor Hom. -/
def tensorGenerator {E C : DGCat k} {e e' : E} {c c' : C}
    {p q r : ℤ} (a : DGHom k p e e') (b : DGHom k q c c') (h : p + q = r) :
    DGHom k r (show E × C from (e,c)) (show E × C from (e',c')) :=
  ((HomologicalComplex.ιTensorObj (dgHomComplex k e e') (dgHomComplex k c c') p q r h).hom)
    (a ⊗ₜ[k] b)

/-- Currying fixes each actual right-module column and every tensor generator. -/
structure GraphCurrying {E C D : DGCat k} (F : tensor E C ⟶ D) where
  functor : EnrichedFunctor (Cochains k) E (Bimodule k C D)
  cofibrantColumns : ∀ e : E, HasCofibrantColumns C D (functor.obj e)
  column : ∀ (e : E) (c : C), (functor.obj e).toEnrichedFunctor.obj c ≅
    (graph F).toEnrichedFunctor.obj (e,c)
  action : ∀ (e e' : E) (c c' : C) (p q r : ℤ)
    (a : DGHom k p e e') (b : DGHom k q c c') (h : p + q = r),
    dgComp k
      (dgComp k (DGFunctor.dgApp k p c (functor.dgMap p a))
        ((functor.obj e').toEnrichedFunctor.dgMap q b) h)
      ((DGFunctor.homEquivDGCycles k _ _ (column e' c').hom).val) (add_zero r) =
    dgComp k ((DGFunctor.homEquivDGCycles k _ _ (column e c).hom).val)
      ((graph F).toEnrichedFunctor.dgMap r (tensorGenerator (E := E) (C := C) a b h)) (zero_add r)

/-- Actual enriched lifting into the full column-cofibrant subcategory. -/
def columnCofibrantFunctor {E C D : DGCat k} {F : tensor E C ⟶ D} (G : GraphCurrying F) :
    EnrichedFunctor (Cochains k) E (ColumnCofibrantBimodules C D) where
  obj e := ⟨G.functor.obj e, G.cofibrantColumns e⟩
  map e e' := G.functor.map e e'
  map_id e := G.functor.map_id e
  map_comp e e' e'' := G.functor.map_comp e e' e''

/-- The actual closed component of a DG-functor natural transformation
whose values are bimodules. -/
def component {A : Type v} [DGCategory k A] {C D : DGCat k}
    {F G : EnrichedFunctor (Cochains k) A (Bimodule k C D)}
    (η : (⟨F⟩ : DGFunctor k A (Bimodule k C D)) ⟶ ⟨G⟩) (x : A) :
    F.obj x ⟶ G.obj x :=
  (DGFunctor.homEquivDGCycles k (F.obj x) (G.obj x)).symm
    ⟨η.dgApp x, η.dgApp_mem_dgCycles x⟩

/-- One enriched replacement functor is used for all E, columns and
homogeneous natural transformations. Its augmentation is a native
module-action-preserving natural transformation. -/
structure BimoduleReplacementFunctor (C D : DGCat k) where
  functor : EnrichedFunctor (Cochains k) (ColumnCofibrantBimodules C D) (Bimodule k C D)
  augmentation :
    (⟨functor⟩ : DGFunctor k (ColumnCofibrantBimodules C D) (Bimodule k C D)) ⟶
      ⟨DGFullSubcategory.inclusion (R := k) (P := HasCofibrantColumns C D)⟩
  cofibrant : ∀ M : ColumnCofibrantBimodules C D, IsCofibrantBimodule (functor.obj M)
  trivial : ∀ M : ColumnCofibrantBimodules C D, IsBimoduleTrivialFibration (component augmentation M)
  representable : ∀ M : ColumnCofibrantBimodules C D,
    IsRightQuasiRepresentable (fun y => canonicalEvaluation y) M.obj →
      IsRightQuasiRepresentable (fun y => canonicalEvaluation y) (functor.obj M)

/-- Native inclusion of the actual full cofibrant/RQR DG subcategory. -/
def smallRealization {C D : DGCat k} (S : SmallQuasiFunctorModel C D) :
    EnrichedFunctor (Cochains k) S.category (Bimodule k C D) :=
  S.realization.comp (Cochains k)
    (DGFullSubcategory.inclusion (R := k) (P := IsQuasiFunctorObject C D))

variable {Q : ReplacementFunctor k} {C : DGCat k} {T : LocalizedTensorModel Q C}
    (M : MoritaClosedModel Q C T)

/-- The actual graph representative for one tensor functor. All E-actions
are retained in the two comparison maps, not just the object columns. -/
structure GraphRepresentative (E D : DGCat k)
    (R : BimoduleReplacementFunctor (Q.functor.obj C) D)
    (F : tensor E (Q.functor.obj C) ⟶ D) where
  tensorAugmentation : TensorMapModel (Q.augmentation.app E) (𝟙 (Q.functor.obj C))
  curry : GraphCurrying (tensorAugmentation.functor ≫ F)
  small : Q.functor.obj E ⟶ (M.quasiFunctorModel D).category
  comparison : EnrichedFunctor (Cochains k) (Q.functor.obj E)
    (Bimodule k (Q.functor.obj C) D)
  cofibrant : ∀ e : Q.functor.obj E, IsCofibrantBimodule (comparison.obj e)
  toGraph :
    (⟨comparison⟩ : DGFunctor k (Q.functor.obj E) (Bimodule k (Q.functor.obj C) D)) ⟶
      ⟨(columnCofibrantFunctor curry).comp (Cochains k) R.functor⟩
  toSmall :
    (⟨comparison⟩ : DGFunctor k (Q.functor.obj E) (Bimodule k (Q.functor.obj C) D)) ⟶
      ⟨small.comp (Cochains k) (smallRealization (M.quasiFunctorModel D))⟩
  graph_weak : ∀ e : Q.functor.obj E, IsBimoduleTrivialFibration (component toGraph e)
  small_weak : ∀ e : Q.functor.obj E, IsBimoduleTrivialFibration (component toSmall e)

/-- The exact localized class supplied by a source-normalized graph representative. -/
def graphClass {E D : DGCat k} {F : tensor E (Q.functor.obj C) ⟶ D}
    {R : BimoduleReplacementFunctor (Q.functor.obj C) D} (P : GraphRepresentative M E D R F) :
    (toHo k).obj E ⟶ (toHo k).obj (M.quasiFunctorModel D).category := by
  letI : IsIso ((toHo k).map (Q.augmentation.app E)) :=
    Localization.inverts (toHo k) (quasiEquivalences k) _ (Q.trivialFibration E).2
  exact inv ((toHo k).map (Q.augmentation.app E)) ≫ (toHo k).map P.small

/-- The normalized comparison is on all strict tensor functors and all E.
Functoriality of the native adjunction then controls its localization
generators and canonical quasi-functor maps. -/
structure NormalizedClosedModel where
  replacement : ∀ D : DGCat k, BimoduleReplacementFunctor (Q.functor.obj C) D
  graph : ∀ (E D : DGCat k) (F : tensor E (Q.functor.obj C) ⟶ D),
    GraphRepresentative M E D (replacement D) F
  hom_equiv : ∀ (E D : DGCat k) (F : tensor E (Q.functor.obj C) ⟶ D),
    (M.adjunction.homEquiv ((toHo k).obj E) ((toHo k).obj D)
      (eqToHom (T.object_eq E) ≫ (toHo k).map ((graph E D F).tensorAugmentation.functor ≫ F))) ≫
        (M.objectIso D).hom = graphClass M (graph E D F)

end MathlibExt.CategoryTheory.DGMoritaGraphCurryingModels
