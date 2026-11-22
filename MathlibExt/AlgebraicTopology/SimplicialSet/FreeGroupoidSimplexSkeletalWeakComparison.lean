/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexWeakComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplexMonomorphisms
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The original k-comparison on skeleta and their sequential union
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.FreeGroupoidSimplex

private instance originalCofibrant (X : SSet.{u}) : IsCofibrant X := by
  let _ : Cofibration ((⊥ : X.Subcomplex).ι) :=
    (cofibration_iff _).2 (by change Mono _; infer_instance)
  exact (isCofibrant_iff_of_isInitial ((⊥ : X.Subcomplex).ι)
    (Subcomplex.isInitialBot (X := X))).2 inferInstance

private theorem skeletonOfBot_eq (X : SSet.{u}) (n : ℕ) :
    skeletonOfMono ((⊥ : X.Subcomplex).ι) n = X.skeleton n := by
  change Subcomplex.range ((⊥ : X.Subcomplex).ι) ⊔ X.skeleton n = X.skeleton n
  simp only [Subcomplex.range, Subcomplex.ι, Subfunctor.range_ι, bot_sup_eq]

private theorem initialComparison (X : SSet.{u}) (hX : IsInitial X) :
    realizationWeakEquivalences (kComparison.app X) := by
  let : kFunctor.{u}.IsLeftAdjoint := kAdjunction.isLeftAdjoint
  have hK := hX.isInitialObj kFunctor _
  let : IsIso (kComparison.app X) := isIso_of_isInitial hX hK _
  exact realizationWeakEquivalences.of_isIso _

private theorem bottomComparison (X : SSet.{u}) :
    realizationWeakEquivalences (kComparison.app ((⊥ : X.Subcomplex) : SSet.{u})) :=
  initialComparison _ (by exact Subcomplex.isInitialBot (X := X))

private theorem sigmaComparisonWeak {ι : Type u} (F : ι → SSet.{u})
    (h : ∀ i, realizationWeakEquivalences (kComparison.app (F i))) :
    realizationWeakEquivalences (kComparison.app (∐ F)) := by
  let : kFunctor.{u}.IsLeftAdjoint := kAdjunction.isLeftAdjoint
  let e := PreservesCoproduct.iso kFunctor F
  have he : kComparison.app (∐ F) ≫ e.hom =
      Limits.Sigma.map (fun i => kComparison.app (F i)) := by
    apply Limits.Sigma.hom_ext
    intro i
    have hn : Sigma.ι F i ≫ kComparison.app (∐ F) =
        kComparison.app (F i) ≫ kFunctor.map (Sigma.ι F i) :=
      kComparison.naturality (Sigma.ι F i)
    have he : kFunctor.map (Sigma.ι F i) ≫ e.hom =
        Sigma.ι (fun i => kFunctor.obj (F i)) i := by
      change _ ≫ (PreservesCoproduct.iso kFunctor F).hom = _
      have hInv : inv (sigmaComparison kFunctor F) = e.hom := by
        apply IsIso.inv_eq_of_hom_inv_id
        change (PreservesCoproduct.iso kFunctor F).inv ≫ e.hom = 𝟙 _
        exact e.inv_hom_id
      rw [← hInv]
      exact map_ι_comp_inv_sigmaComparison kFunctor F i
    rw [← Category.assoc, hn, Category.assoc, he]
    exact (Sigma.ι_map (fun i => kComparison.app (F i)) i).symm
  have hw : realizationWeakEquivalences (kComparison.app (∐ F) ≫ e.hom) := by
    rw [he]
    exact sigma_map_mem_realizationWeakEquivalences _ h
  exact realizationWeakEquivalences.of_postcomp _ _
    (realizationWeakEquivalences.of_isIso _) hw

private theorem comparisonWeak_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    (h : realizationWeakEquivalences (kComparison.app X)) :
    realizationWeakEquivalences (kComparison.app Y) := by
  have hw : realizationWeakEquivalences (e.hom ≫ kComparison.app Y) := by
    have hn : e.hom ≫ kComparison.app Y = kComparison.app X ≫ kFunctor.map e.hom :=
      kComparison.naturality e.hom
    rw [hn]
    exact realizationWeakEquivalences.comp_mem _ _ h
      (realizationWeakEquivalences.of_isIso _)
  exact realizationWeakEquivalences.of_precomp _ _
    (realizationWeakEquivalences.of_isIso _) hw

private theorem boundaryComparisonWeak (n : ℕ)
    (h : ∀ X : SSet.{u},
      realizationWeakEquivalences (kComparison.app (X.skeleton n : SSet.{u}))) :
    realizationWeakEquivalences (kComparison.app (boundary.{u} n : SSet.{u})) := by
  have ht : (boundary.{u} n : SSet.{u}).skeleton n = ⊤ := by
    apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ n).2
    intro m hm x _
    exact SSet.mem_skeleton _ x hm
  exact comparisonWeak_of_iso
    (Subcomplex.eqToIso ht ≪≫ Subcomplex.topIso _) (h _)

private theorem skeletonComparisonStep (n : ℕ)
    (h : ∀ X : SSet.{u},
      realizationWeakEquivalences (kComparison.app (X.skeleton n : SSet.{u})))
    (X : SSet.{u}) :
    realizationWeakEquivalences (kComparison.app (X.skeleton (n + 1) : SSet.{u})) := by
  let i : ((⊥ : X.Subcomplex) : SSet.{u}) ⟶ X := Subcomplex.ι ⊥
  let : kFunctor.{u}.IsLeftAdjoint := kAdjunction.isLeftAdjoint
  have hStage : realizationWeakEquivalences
      (kComparison.app (skeletonOfMono i n : SSet.{u})) :=
    comparisonWeak_of_iso (Subcomplex.eqToIso (skeletonOfBot_eq X n)).symm (h X)
  have hBoundary := boundaryComparisonWeak n h
  have hA : realizationWeakEquivalences
      (kComparison.app (relativeCellComplexOfMono.sigmaBoundary i n)) :=
    sigmaComparisonWeak _ (fun _ => hBoundary)
  have hB : realizationWeakEquivalences
      (kComparison.app (relativeCellComplexOfMono.sigmaStdSimplex i n)) :=
    sigmaComparisonWeak _ (fun _ => kComparison_representable_realizationWeak ⦋n⦌)
  let _ : WeakEquivalence
      (kComparison.app (relativeCellComplexOfMono.sigmaBoundary i n)) :=
    (weakEquivalence_iff _).2 hA
  let _ : WeakEquivalence
      (kComparison.app (relativeCellComplexOfMono.sigmaStdSimplex i n)) :=
    (weakEquivalence_iff _).2 hB
  let _ : WeakEquivalence
      (kComparison.app (skeletonOfMono i n : SSet.{u})) :=
    (weakEquivalence_iff _).2 hStage
  have sq := (relativeCellComplexOfMono.isPushout i n).flip
  have sq' := sq.map kFunctor
  let _ : Cofibration (relativeCellComplexOfMono.l i n) :=
    (cofibration_iff _).2 (by change Mono _; infer_instance)
  let _ : Cofibration (kFunctor.map (relativeCellComplexOfMono.l i n)) :=
    (cofibration_iff _).2 (by change Mono _; infer_instance)
  have hw : WeakEquivalence
      (kComparison.app (skeletonOfMono i (n + 1) : SSet.{u})) :=
    weakEquivalence_map_of_isPushouts_of_cofibrant sq sq'
      (kComparison.naturality (relativeCellComplexOfMono.l i n))
      (kComparison.naturality (relativeCellComplexOfMono.t i n))
      (kComparison.naturality (relativeCellComplexOfMono.b i n))
      (kComparison.naturality (relativeCellComplexOfMono.r i n))
  have hw' : realizationWeakEquivalences
      (kComparison.app (skeletonOfMono i (n + 1) : SSet.{u})) :=
    (weakEquivalence_iff _).1 hw
  exact comparisonWeak_of_iso (Subcomplex.eqToIso (skeletonOfBot_eq X (n + 1))) hw'

/-- The original comparison is a realization weak equivalence on every finite
stage of every original simplicial set's skeleton filtration. -/
theorem kComparison_skeleton_realizationWeak (X : SSet.{u}) (n : ℕ) :
    realizationWeakEquivalences (kComparison.app (X.skeleton n : SSet.{u})) := by
  induction n generalizing X with
  | zero =>
    exact comparisonWeak_of_iso (Subcomplex.eqToIso (SSet.skeleton_zero X)).symm
      (bottomComparison X)
  | succ n hn => exact skeletonComparisonStep n hn X

/-- The original global k-comparison is a realization weak equivalence, using
the same native sequential union of original skeleta and its k-image. -/
theorem kComparison_realizationWeak (X : SSet.{u}) :
    realizationWeakEquivalences (kComparison.app X) := by
  let i : ((⊥ : X.Subcomplex) : SSet.{u}) ⟶ X := Subcomplex.ι ⊥
  let cell := relativeCellComplexOfMono i
  let F : ℕ ⥤ SSet.{u} := cell.F
  let cF : Cocone F := ⟨X, cell.incl⟩
  let : kFunctor.{u}.IsLeftAdjoint := kAdjunction.isLeftAdjoint
  let cG : Cocone (F ⋙ kFunctor) := kFunctor.mapCocone cF
  apply realizationWeakEquivalences.of_isColimit_nat_mono
    (Functor.whiskerLeft F kComparison) cell.isColimit
    (isColimitOfPreserves kFunctor cell.isColimit) (kComparison.app X)
  · intro n
    exact kComparison.naturality (cell.incl.app n)
  · intro n m f
    change Mono (Subcomplex.homOfLE ((skeletonOfMono i).monotone (leOfHom f)))
    infer_instance
  · intro n m f
    change Mono
      (kFunctor.map (Subcomplex.homOfLE ((skeletonOfMono i).monotone (leOfHom f))))
    infer_instance
  · intro n
    change realizationWeakEquivalences
      (kComparison.app (skeletonOfMono i n : SSet.{u}))
    exact comparisonWeak_of_iso (Subcomplex.eqToIso (skeletonOfBot_eq X n)).symm
      (kComparison_skeleton_realizationWeak X n)

end SSet.FreeGroupoidSimplex
