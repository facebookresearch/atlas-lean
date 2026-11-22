/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalAllVertexRelativeComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSimplexTupleWeakness
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The whole original all-vertex power diagram

For each actual outer k≥2 the map retains all k+1 original vertices of every
full-J power. Row fibrations and every operator-relative weak map are derived.
The true diagonal product Iso and zero-power Iso then identify the native
homotopy pullback comparison with the original raw unit on every base coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory

namespace SimplicialSpace.RezkCompletionAllVertex
open RezkCompletionRaw RezkCompletionCoreDiagonal OriginalAllVertexComparison
open FixedTupleSpinePrefix OriginalChosenSpineFixedTupleBaseChange

/-- The actual full tuple of zero-objects in every original power, with all coefficient
operators. -/
def originalAllVertexTupleDiagram (W : SimplicialSpace.{u}) (k : ℕ) :
    SimplicialObject SSet.{u} where
  obj n := tupleVertexBase ((powerDiagram W).obj n) k
  map f := originalTupleBaseMap ((powerDiagram W).map f) k
  map_id n := by
    rw [(powerDiagram W).map_id]
    change CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) => 𝟙 _) = 𝟙 _
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    simp only [CategoryTheory.Limits.Pi.map_π, Category.id_comp, Category.comp_id]
  map_comp f g := by
    rw [(powerDiagram W).map_comp]
    change CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) =>
      ((powerDiagram W).map f).hom.app (op ⦋0⦌) ≫
        ((powerDiagram W).map g).hom.app (op ⦋0⦌)) =
      CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) =>
        ((powerDiagram W).map f).hom.app (op ⦋0⦌)) ≫
      CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) =>
        ((powerDiagram W).map g).hom.app (op ⦋0⦌))
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, CategoryTheory.Limits.Pi.map_π,
      CategoryTheory.Limits.Pi.map_π_assoc]

/-- The literal map of every simplex in every full original power to all its vertices. -/
def originalAllVertexPowerMap (W : SimplicialSpace.{u}) (k : ℕ) :
    rowPowerDiagram W (op ⦋k⦌) ⟶ originalAllVertexTupleDiagram W k where
  app n := simplexAllVertexMap ((powerDiagram W).obj n) k
  naturality _n _m f := simplexAllVertexMap_naturality ((powerDiagram W).map f) k

/-- Every row fibration is the actual full all-vertex restriction of its original Segal power. -/
theorem originalAllVertexPowerMap_row_fibration (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (k : ℕ) (n : SimplexCategory) :
    Fibration ((originalAllVertexPowerMap W k).app (op n)) :=
  OriginalAllVertexReedy.allVertexMap_fibration ((powerDiagram W).obj (op n)) k
    (powerDiagram_segal W hW (op n)).1

/-- Genuine row fibrations imply the native Sharp property by right properness. -/
theorem originalAllVertexPowerMap_row_sharp (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (k : ℕ) (n : SimplexCategory) :
    SSet.SharpComparisonDraft.Sharp ((originalAllVertexPowerMap W k).app (op n)) := by
  let _ : Fibration ((originalAllVertexPowerMap W k).app (op n)) :=
    originalAllVertexPowerMap_row_fibration W hW k n
  intro T t
  let _ : Fibration ((cospan ((originalAllVertexPowerMap W k).app (op n)) t).map
      WalkingCospan.Hom.inl) := originalAllVertexPowerMap_row_fibration W hW k n
  exact weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
    (cospan ((originalAllVertexPowerMap W k).app (op n)) t)

/-- The native operator-relative map is exactly the original full-tuple relative pullback lift. -/
theorem originalAllVertexPowerMap_relativeComparison (W : SimplicialSpace.{u})
    (k : ℕ) {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.EquifibredDiagonal.relativeComparison (originalAllVertexPowerMap W k) f =
      simplexAllVertexRelativeMap ((powerDiagram W).map f.op) k := rfl

/-- ALL original coefficient operators have weak full-tuple relative maps, derived from actual
MF. -/
theorem originalAllVertexPowerMap_relativeComparison_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k)
    {n m : SimplexCategory} (f : n ⟶ m) :
    WeakEquivalence (SSet.EquifibredDiagonal.relativeComparison
        (originalAllVertexPowerMap W k) f) := by
  rw [weakEquivalence_iff, originalAllVertexPowerMap_relativeComparison]
  apply (simplexAllVertexRelativeMap_weak_iff ((powerDiagram W).map f.op) k
    (powerDiagram_segal W hW (op m)).1 (powerDiagram_segal W hW (op n)).1).mpr
  intro x
  exact OriginalTupleMappingFibreWeakness.simplexAllVertexFibreMap_weak
    ((powerDiagram W).map f.op) (powerDiagram_segal W hW (op m))
    (powerDiagram_segal W hW (op n)) k hk x
    (fun i => RezkCorePowerFibres.originalPowerOperator_mappingFibre_weak W hW f.op
      (x i.castSucc) (x i.succ))

/-- Rezk's Theorem 6.1 gives diagonal sharpness for this original all-vertex
power map. The project corollary supplies all native homotopy pullback
comparisons; both hypothesis families are derived above. -/
theorem originalAllVertexPowerMap_all_simplex_and_homotopy_pullback (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k) :
    SSet.SharpSaturation.allSimplexComparisons
        (SSet.simplicialDiagonalFunctor.map (originalAllVertexPowerMap W k)) ∧
      SSet.SharpComparisonDraft.Sharp
        (SSet.simplicialDiagonalFunctor.map (originalAllVertexPowerMap W k)) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)),
        WeakEquivalence (SSet.RezkOriginal61.kappa (originalAllVertexPowerMap W k) n v) :=
  SSet.RezkOriginal61.all_simplex_sharp_and_native_homotopy_pullback
    (originalAllVertexPowerMap W k) (originalAllVertexPowerMap_row_sharp W hW k)
    (originalAllVertexPowerMap_relativeComparison_weak W hW k hk)

/-- Every selected product coordinate is a full natural map of the original tuple diagram. -/
def originalAllVertexTupleProjection (W : SimplicialSpace.{u}) (k : ℕ) (i : Fin (k + 1)) :
    originalAllVertexTupleDiagram W k ⟶ rowPowerDiagram W (op ⦋0⦌) where
  app n := CategoryTheory.Limits.Pi.π _ i
  naturality n m f := by
    change CategoryTheory.Limits.Pi.map
        (fun _ : Fin (k + 1) => ((powerDiagram W).map f).hom.app (op ⦋0⦌)) ≫
        CategoryTheory.Limits.Pi.π _ i =
      CategoryTheory.Limits.Pi.π _ i ≫ ((powerDiagram W).map f).hom.app (op ⦋0⦌)
    exact CategoryTheory.Limits.Pi.map_π
      (fun _ : Fin (k + 1) => ((powerDiagram W).map f).hom.app (op ⦋0⦌)) i

/-- The whole tuple fan is genuinely limiting, checked by every actual coefficient evaluation. -/
def originalAllVertexTupleIsLimit (W : SimplicialSpace.{u}) (k : ℕ) :
    IsLimit (Fan.mk _ (fun i : Fin (k + 1) => originalAllVertexTupleProjection W k i)) :=
  evaluationJointlyReflectsLimits _ fun n =>
    (isLimitMapConeFanMkEquiv ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj n)
      (fun _ : Fin (k + 1) => rowPowerDiagram W (op ⦋0⦌))
      (fun i => originalAllVertexTupleProjection W k i)).symm (productIsProduct _)

/-- The actual diagonal preserves this complete finite fan and all its original projections. -/
def originalAllVertexTupleDiagonalIsLimit (W : SimplicialSpace.{u}) (k : ℕ) :
    IsLimit (Fan.mk _ (fun i : Fin (k + 1) =>
      SSet.simplicialDiagonalFunctor.map (originalAllVertexTupleProjection W k i))) :=
  isLimitFanMkObjOfIsLimit SSet.simplicialDiagonalFunctor
    (fun _ : Fin (k + 1) => rowPowerDiagram W (op ⦋0⦌))
    (fun i => originalAllVertexTupleProjection W k i) (originalAllVertexTupleIsLimit W k)

/-- The whole original tuple diagonal is canonically the chosen product of all Raw(W)₀ factors. -/
def originalAllVertexTupleDiagonalIso (W : SimplicialSpace.{u}) (k : ℕ) :
    SSet.simplicialDiagonalFunctor.obj (originalAllVertexTupleDiagram W k) ≅
      tupleVertexBase (rawCompletion W) k :=
  (originalAllVertexTupleDiagonalIsLimit W k).conePointUniqueUpToIso (productIsProduct _)

/-- Every forward and inverse product leg is retained, including all original coordinate indices. -/
theorem originalAllVertexTupleDiagonalIso_legs (W : SimplicialSpace.{u}) (k : ℕ) :
    (∀ i : Fin (k + 1), (originalAllVertexTupleDiagonalIso W k).hom ≫
        CategoryTheory.Limits.Pi.π _ i =
      SSet.simplicialDiagonalFunctor.map (originalAllVertexTupleProjection W k i)) ∧
    (∀ i : Fin (k + 1), (originalAllVertexTupleDiagonalIso W k).inv ≫
        SSet.simplicialDiagonalFunctor.map (originalAllVertexTupleProjection W k i) =
      CategoryTheory.Limits.Pi.π _ i) := by
  constructor <;> intro i
  · exact IsLimit.conePointUniqueUpToIso_hom_comp
      (originalAllVertexTupleDiagonalIsLimit W k)
      (productIsProduct (fun _ : Fin (k + 1) => (rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk i)
  · exact IsLimit.conePointUniqueUpToIso_inv_comp
      (originalAllVertexTupleDiagonalIsLimit W k)
      (productIsProduct (fun _ : Fin (k + 1) => (rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk i)

/-- The actual diagonal map is the literal all-vertex map of Raw(W), through the constructed Iso. -/
theorem originalAllVertexPowerMap_diagonal (W : SimplicialSpace.{u}) (k : ℕ) :
    SSet.simplicialDiagonalFunctor.map (originalAllVertexPowerMap W k) ≫
        (originalAllVertexTupleDiagonalIso W k).hom = simplexAllVertexMap (rawCompletion W) k := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, (originalAllVertexTupleDiagonalIso_legs W k).1 i]
  let d : rowPowerDiagram W (op ⦋k⦌) ⟶ rowPowerDiagram W (op ⦋0⦌) :=
    ((powerDiagram W ⋙ forget).flip).map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
  have hd : SSet.simplicialDiagonalFunctor.map d =
      (rawCompletion W).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op := by rfl
  have hf : originalAllVertexPowerMap W k ≫ originalAllVertexTupleProjection W k i = d := by
    apply NatTrans.ext
    funext n
    change CategoryTheory.Limits.Pi.lift (fun j : Fin (k + 1) =>
        ((powerDiagram W).obj n).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ j).op) ≫
        CategoryTheory.Limits.Pi.π _ i =
      ((powerDiagram W).obj n).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op
    exact CategoryTheory.Limits.Pi.lift_comp_π _ i
  have hc := (SSet.simplicialDiagonalFunctor.map_comp (originalAllVertexPowerMap W k)
    (originalAllVertexTupleProjection W k i)).symm
  refine hc.trans ((congrArg SSet.simplicialDiagonalFunctor.map hf).trans ?_)
  refine hd.trans ?_
  change (rawCompletion W).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ i).op =
    CategoryTheory.Limits.Pi.lift (fun j : Fin (k + 1) =>
      (rawCompletion W).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ j).op) ≫
      CategoryTheory.Limits.Pi.π _ i
  exact (CategoryTheory.Limits.Pi.lift_comp_π
    (fun j : Fin (k + 1) =>
      (rawCompletion W).diagram.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ j).op) i).symm

/-- The same genuine zero-power Iso acts on every one of the original vertex factors. -/
def originalZeroAllVertexTupleIso (W : SimplicialSpace.{u}) (k : ℕ) :
    (originalAllVertexTupleDiagram W k).obj (op ⦋0⦌) ≅ tupleVertexBase W k :=
  CategoryTheory.Limits.Pi.mapIso (fun _ : Fin (k + 1) => originalZeroPowerRowIso W (op ⦋0⦌))

/-- The raw coaugmentation on every original object factor, with the actual chosen product. -/
def originalRawUnitTuple (W : SimplicialSpace.{u}) (k : ℕ) :
    tupleVertexBase W k ⟶ tupleVertexBase (rawCompletion W) k :=
  originalTupleBaseMap (rawCompletionUnit W) k

/-- The actual row-zero base map is the original raw unit in ALL coordinates. -/
theorem originalAllVertexTuple_rowZero_rawUnit (W : SimplicialSpace.{u}) (k : ℕ) :
    SSet.EquifibredDiagonal.rowVertexToDiagonal (originalAllVertexTupleDiagram W k) ⦋0⦌ 0 ≫
        (originalAllVertexTupleDiagonalIso W k).hom =
      (originalZeroAllVertexTupleIso W k).hom ≫ originalRawUnitTuple W k := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, (originalAllVertexTupleDiagonalIso_legs W k).1 i]
  have hn : SSet.EquifibredDiagonal.rowVertexToDiagonal
        (originalAllVertexTupleDiagram W k) ⦋0⦌ 0 ≫
        SSet.simplicialDiagonalFunctor.map (originalAllVertexTupleProjection W k i) =
      (originalAllVertexTupleProjection W k i).app (op ⦋0⦌) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 :=
    SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality
      (originalAllVertexTupleProjection W k i) ⦋0⦌ 0
  refine hn.trans ?_
  change CategoryTheory.Limits.Pi.π
      (fun _ : Fin (k + 1) => (rowPowerDiagram W (op ⦋0⦌)).obj (op ⦋0⦌)) i ≫
    SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 = _
  rw [originalZeroPowerRowIso_rowVertex]
  symm
  simp only [originalZeroAllVertexTupleIso, originalRawUnitTuple, originalTupleBaseMap,
    Category.assoc, CategoryTheory.Limits.Pi.map_π]
  have hp :
      (CategoryTheory.Limits.Pi.mapIso
          (fun _ : Fin (k + 1) => originalZeroPowerRowIso W (op ⦋0⦌))).hom ≫
        CategoryTheory.Limits.Pi.π (fun _ : Fin (k + 1) => W.diagram _⦋0⦌) i ≫
        (rawCompletionUnit W).hom.app (op ⦋0⦌) =
      CategoryTheory.Limits.Pi.π
          (fun _ : Fin (k + 1) => (rowPowerDiagram W (op ⦋0⦌)).obj (op ⦋0⦌)) i ≫
        (originalZeroPowerRowIso W (op ⦋0⦌)).hom ≫
        (rawCompletionUnit W).hom.app (op ⦋0⦌) := by
    simpa only [Category.assoc] using congrArg
      (fun g => g ≫ (rawCompletionUnit W).hom.app (op ⦋0⦌))
      (CategoryTheory.Limits.Pi.mapIso_hom_π
        (fun _ : Fin (k + 1) => originalZeroPowerRowIso W (op ⦋0⦌)) i)
  exact hp

/-- The whole row-zero source and base Isos preserve the original all-vertex arrow. -/
theorem originalZeroAllVertexTupleIso_endpoint (W : SimplicialSpace.{u}) (k : ℕ) :
    (originalZeroPowerRowIso W (op ⦋k⦌)).hom ≫ simplexAllVertexMap W k =
      (originalAllVertexPowerMap W k).app (op ⦋0⦌) ≫
        (originalZeroAllVertexTupleIso W k).hom :=
  simplexAllVertexMap_naturality (powerZeroUnitIso W).hom k

/-- The actual native homotopy-pullback cospan changes by the full constructed product Isos. -/
def originalAllVertexZeroRawCospanIso (W : SimplicialSpace.{u}) (k : ℕ) :
    cospan (SSet.simplicialDiagonalFunctor.map (originalAllVertexPowerMap W k))
        (SSet.EquifibredDiagonal.rowVertexToDiagonal (originalAllVertexTupleDiagram W k) ⦋0⦌ 0) ≅
      cospan (simplexAllVertexMap (rawCompletion W) k) (originalRawUnitTuple W k) :=
  cospanIsoMk (originalAllVertexTupleDiagonalIso W k) (Iso.refl _)
    (originalZeroAllVertexTupleIso W k)
    (by
      change SSet.simplicialDiagonalFunctor.map (originalAllVertexPowerMap W k) ≫
          (originalAllVertexTupleDiagonalIso W k).hom =
        𝟙 _ ≫ simplexAllVertexMap (rawCompletion W) k
      rw [Category.id_comp]
      exact originalAllVertexPowerMap_diagonal W k)
    (originalAllVertexTuple_rowZero_rawUnit W k)

/-- Every original outer simplex maps into the full raw-unit homotopy pullback, not merely its
vertices. -/
def originalAllVertexToRawUnitHomotopyPullback (W : SimplicialSpace.{u}) (k : ℕ) :
    W.diagram _⦋k⦌ ⟶ (homotopyPullback (C := SSet.{u})).obj
      (cospan (simplexAllVertexMap (rawCompletion W) k) (originalRawUnitTuple W k)) :=
  (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
    SSet.RezkOriginal61.kappa (originalAllVertexPowerMap W k) ⦋0⦌ 0 ≫
      ((homotopyPullback (C := SSet.{u})).mapIso (originalAllVertexZeroRawCospanIso W k)).hom

/-- Its weakness follows from actual full Rezk 6.1 and genuine Isos, not a supplied diagonal
outcome. -/
theorem originalAllVertexToRawUnitHomotopyPullback_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k) :
    WeakEquivalence (originalAllVertexToRawUnitHomotopyPullback W k) := by
  let _ : WeakEquivalence (SSet.RezkOriginal61.kappa (originalAllVertexPowerMap W k) ⦋0⦌ 0) :=
    (originalAllVertexPowerMap_all_simplex_and_homotopy_pullback W hW k hk).2.2 ⦋0⦌ 0
  unfold originalAllVertexToRawUnitHomotopyPullback
  infer_instance

end SimplicialSpace.RezkCompletionAllVertex
