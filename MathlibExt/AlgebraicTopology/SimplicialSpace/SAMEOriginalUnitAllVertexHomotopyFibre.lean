/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Higher SAME-unit fibre comparisons on the original tuple bases.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalAllVertexPowerHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalUnitMappingHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.OriginalFiniteTrivialCofibrationProducts

/-!
# Actual higher SAME-unit fibre maps before target Segalness

The full power kappa is transported by the actual baseline beta_k, its finite
product on all object factors, and the unchanged original tuple base. The
native homotopy-pullback comparison then yields the literal Unit9 relative
pullback and every original higher tuple-fibre map. Target Reedy fibrancy is
derived from the fixed baseline. Target Segalness is not a hypothesis.
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

/-- The same baseline beta in every original outer degree, without a replacement of the
constructor. -/
def sameBaselineBetaRow (W : SimplicialSpace.{u}) (k : ℕ) :
    (rawCompletion W).diagram _⦋k⦌ ⟶ (RezkCompletionData.completion.obj W).diagram _⦋k⦌ :=
  (RezkBaselineReplacement.unit.app (rawCompletion W)).hom.app (op ⦋k⦌)

/-- Every scalar row beta is weak by the actual baseline component theorem. -/
theorem sameBaselineBetaRow_weak (W : SimplicialSpace.{u}) (k : ℕ) :
    WeakEquivalence (sameBaselineBetaRow W k) :=
  (weakEquivalence_iff _).mpr (RezkBaselineReplacement.unit_components (rawCompletion W) k).2

/-- The fixed beta on the entire k+1-tuple of original Raw(W) object factors. -/
def sameBaselineBetaTuple (W : SimplicialSpace.{u}) (k : ℕ) :
    tupleVertexBase (rawCompletion W) k ⟶ tupleVertexBase (RezkCompletionData.completion.obj W) k :=
  CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) => sameBetaZero W)

/-- Finite TCof products derive this tuple weakness with no Raw(W)₀ Kan assumption. -/
theorem sameBaselineBetaTuple_weak (W : SimplicialSpace.{u}) (k : ℕ) :
    WeakEquivalence (sameBaselineBetaTuple W k) :=
  (weakEquivalence_iff _).mpr
    (SSet.betaFiniteProduct_realizationWeak (k + 1) (sameBetaZero W)
      (sameBetaZero_trivialCofibration W))

/-- The original SAME coaugmentation on every one of the prescribed object factors. -/
def sameOriginalUnitTuple (W : SimplicialSpace.{u}) (k : ℕ) :
    tupleVertexBase W k ⟶ tupleVertexBase (RezkCompletionData.completion.obj W) k :=
  originalTupleBaseMap (RezkCompletionData.unit.app W) k

/-- The actual full raw unit followed by finite beta is the literal SAME unit tuple. -/
theorem originalRawUnitTuple_betaTuple (W : SimplicialSpace.{u}) (k : ℕ) :
    originalRawUnitTuple W k ≫ sameBaselineBetaTuple W k = sameOriginalUnitTuple W k := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro i
  change (CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) =>
      (rawCompletionUnit W).hom.app (op ⦋0⦌)) ≫
    CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) => sameBetaZero W)) ≫
      CategoryTheory.Limits.Pi.π _ i =
    CategoryTheory.Limits.Pi.map (fun _ : Fin (k + 1) =>
      (rawCompletionUnit W).hom.app (op ⦋0⦌) ≫ sameBetaZero W) ≫
      CategoryTheory.Limits.Pi.π _ i
  simp only [Category.assoc, CategoryTheory.Limits.Pi.map_π,
    CategoryTheory.Limits.Pi.map_π_assoc]

/-- Actual beta naturality retains all original vertex projections, not only the two endpoints. -/
theorem sameBaselineBetaRow_allVertex (W : SimplicialSpace.{u}) (k : ℕ) :
    simplexAllVertexMap (rawCompletion W) k ≫ sameBaselineBetaTuple W k =
      sameBaselineBetaRow W k ≫ simplexAllVertexMap (RezkCompletionData.completion.obj W) k :=
  (simplexAllVertexMap_naturality (RezkBaselineReplacement.unit.app (rawCompletion W)) k).symm

/-- The raw cospan moves by beta_k, finite beta₀, and the identity of the original full tuple. -/
def originalAllVertexRawToSameUnitTupleCospanMap (W : SimplicialSpace.{u}) (k : ℕ) :
    cospan (simplexAllVertexMap (rawCompletion W) k) (originalRawUnitTuple W k) ⟶
      cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
        (sameOriginalUnitTuple W k) :=
  cospanHomMk (sameBaselineBetaTuple W k) (sameBaselineBetaRow W k)
    (𝟙 (tupleVertexBase W k)) (sameBaselineBetaRow_allVertex W k)
    (by
      change originalRawUnitTuple W k ≫ sameBaselineBetaTuple W k =
        𝟙 (tupleVertexBase W k) ≫ sameOriginalUnitTuple W k
      simpa only [Category.id_comp] using originalRawUnitTuple_betaTuple W k)

/-- All three actual cospan component weaknesses are derived beta facts or the identity. -/
theorem originalAllVertexRawToSameUnitTupleHomotopyMap_weak (W : SimplicialSpace.{u}) (k : ℕ) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalAllVertexRawToSameUnitTupleCospanMap W k)) := by
  apply homotopyPullback_map_weakEquivalence
  intro j
  cases j with
  | none => exact sameBaselineBetaTuple_weak W k
  | some pair =>
      cases pair with
      | left => exact sameBaselineBetaRow_weak W k
      | right => exact inferInstanceAs (WeakEquivalence (𝟙 (tupleVertexBase W k)))

/-- Every original W_k maps to the native homotopy pullback over the actual SAME unit tuple. -/
def originalAllVertexToFixedSameUnitTupleHomotopyPullback (W : SimplicialSpace.{u}) (k : ℕ) :
    W.diagram _⦋k⦌ ⟶ (homotopyPullback (C := SSet.{u})).obj
      (cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
        (sameOriginalUnitTuple W k)) :=
  originalAllVertexToRawUnitHomotopyPullback W k ≫
    (homotopyPullback (C := SSet.{u})).map (originalAllVertexRawToSameUnitTupleCospanMap W k)

/-- The full Rezk 6.1 comparison and finite TCof beta transport derive this weakness. -/
theorem originalAllVertexToFixedSameUnitTupleHomotopyPullback_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k) :
    WeakEquivalence (originalAllVertexToFixedSameUnitTupleHomotopyPullback W k) := by
  let : WeakEquivalence (originalAllVertexToRawUnitHomotopyPullback W k) :=
    originalAllVertexToRawUnitHomotopyPullback_weak W hW k hk
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalAllVertexRawToSameUnitTupleCospanMap W k)) :=
    originalAllVertexRawToSameUnitTupleHomotopyMap_weak W k
  unfold originalAllVertexToFixedSameUnitTupleHomotopyPullback
  infer_instance

/-- The actual full HP composite is the original Unit_k relative pullback lift,
followed by the target's native comparison, with BOTH whole projections proved. -/
theorem originalAllVertexToFixedSameUnitTupleHomotopyPullback_factor
    (W : SimplicialSpace.{u}) (k : ℕ) :
    originalAllVertexToFixedSameUnitTupleHomotopyPullback W k =
      simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k ≫
        (homotopyPullbackComparison (C := SSet.{u})).app
          (cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
            (sameOriginalUnitTuple W k)) := by
  let eta := originalAllVertexPowerMap W k
  let a := (originalAllVertexZeroRawCospanIso W k).hom ≫
    originalAllVertexRawToSameUnitTupleCospanMap W k
  let lift := SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison eta ⦋0⦌ 0
  have both : (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫ lift ≫ lim.map a =
      simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k := by
    apply pullback.hom_ext
    · calc
        _ = (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
            (lift ≫ pullback.fst _ _) ≫ a.app WalkingCospan.left := by
          simp only [Category.assoc]
          rw [limit.map_π a WalkingCospan.left]
        _ = (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
            SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋k⦌)) ⦋0⦌ 0 ≫
              sameBaselineBetaRow W k := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs eta ⦋0⦌ 0).1]
          rfl
        _ = (rawCompletionUnit W).hom.app (op ⦋k⦌) ≫ sameBaselineBetaRow W k := by
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun q => q ≫ sameBaselineBetaRow W k)
              (originalZeroPowerRowIso_inv_rowVertex W (op ⦋k⦌)))
        _ = (RezkCompletionData.unit.app W).hom.app (op ⦋k⦌) := rfl
        _ = simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k ≫
            pullback.fst _ _ := (simplexAllVertexRelativeMap_legs _ _).1.symm
    · calc
        _ = (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
            (lift ≫ pullback.snd _ _) ≫ a.app WalkingCospan.right := by
          simp only [Category.assoc]
          rw [limit.map_π a WalkingCospan.right]
        _ = (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
            (originalAllVertexPowerMap W k).app (op ⦋0⦌) ≫
              (originalZeroAllVertexTupleIso W k).hom := by
          rw [(SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs eta ⦋0⦌ 0).2]
          rfl
        _ = (originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫
            ((originalZeroPowerRowIso W (op ⦋k⦌)).hom ≫ simplexAllVertexMap W k) := by
          rw [← originalZeroAllVertexTupleIso_endpoint]
        _ = simplexAllVertexMap W k := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        _ = simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k ≫
            pullback.snd _ _ := (simplexAllVertexRelativeMap_legs _ _).2.symm
  have naturality := (homotopyPullbackComparison (C := SSet.{u})).naturality a
  calc
    originalAllVertexToFixedSameUnitTupleHomotopyPullback W k =
        ((originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫ lift) ≫
          ((homotopyPullbackComparison (C := SSet.{u})).app _ ≫
            (homotopyPullback (C := SSet.{u})).map a) := by
      simp only [originalAllVertexToFixedSameUnitTupleHomotopyPullback,
        originalAllVertexToRawUnitHomotopyPullback, SSet.RezkOriginal61.kappa,
        SSet.SharpComparisonDraft.comparison, Functor.mapIso_hom, a, eta, lift,
        Functor.map_comp, Category.assoc]
    _ = ((originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫ lift) ≫
        (lim.map a ≫ (homotopyPullbackComparison (C := SSet.{u})).app _) := by
      rw [← naturality]
    _ = ((originalZeroPowerRowIso W (op ⦋k⦌)).inv ≫ lift ≫ lim.map a) ≫
        (homotopyPullbackComparison (C := SSet.{u})).app _ := by simp only [Category.assoc]
    _ = _ := congrArg (fun q => q ≫ (homotopyPullbackComparison (C := SSet.{u})).app
      (cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
        (sameOriginalUnitTuple W k))) both

/-- The target all-vertex fibration comes from the SAME baseline RF, without target Segalness. -/
theorem sameOriginalUnit_allVertexRelativeMap_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k) :
    WeakEquivalence (simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k) := by
  let : Fibration (simplexAllVertexMap (RezkCompletionData.completion.obj W) k) :=
    OriginalAllVertexReedy.allVertexMap_fibration (RezkCompletionData.completion.obj W) k
      (RezkCompletionData.completion_fibrant W)
  let comparison := (homotopyPullbackComparison (C := SSet.{u})).app
    (cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
      (sameOriginalUnitTuple W k))
  let : Fibration ((cospan (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
      (sameOriginalUnitTuple W k)).map WalkingCospan.Hom.inl) := by
    change Fibration (simplexAllVertexMap (RezkCompletionData.completion.obj W) k)
    infer_instance
  have hcomparison : WeakEquivalence comparison :=
    weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _
  have htotal : WeakEquivalence (simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k ≫
      comparison) := by
    rw [← originalAllVertexToFixedSameUnitTupleHomotopyPullback_factor]
    exact originalAllVertexToFixedSameUnitTupleHomotopyPullback_weak W hW k hk
  exact weakEquivalence_of_postcomp
    (simplexAllVertexRelativeMap (RezkCompletionData.unit.app W) k) comparison
    (hg := hcomparison) (hfg := htotal)

/-- Every actual higher SAME-unit fibre map is derived before target Segalness or completion. -/
theorem sameOriginalUnit_simplexAllVertexFibreMap_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (simplexAllVertexFibreMap
        (RezkCompletionData.unit.app W) k x) :=
  (simplexAllVertexRelativeMap_weak_iff (RezkCompletionData.unit.app W) k hW.1
    (RezkCompletionData.completion_fibrant W)).mp
      ((weakEquivalence_iff _).mp (sameOriginalUnit_allVertexRelativeMap_weak W hW k hk)) x

end SimplicialSpace.RezkCompletionAllVertex
