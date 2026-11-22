/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalProductBoundarySquare
import MathlibExt.AlgebraicTopology.SimplicialSet.IncomingHCPasting
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback

/-!
# Simplex operators on diagonal skeletal cells

Diagonal cell maps respect every simplex operator, and cells of degree at most a skeletal stage map naturally into that stage. The stage invariant combines sharpness with weak incoming-cell comparisons; sharp row maps establish it at degree zero. With weak relative comparisons for all simplex operators, an existing stage invariant gives weak comparisons for operator maps into its cells.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalCell
open SharpComparisonDraft RezkCompatiblePushout RezkSkeletalProduct

/-- The actual two outer-operator descriptions of a diagonal cell coincide,
for EVERY ordinal map, including noninjective and collapsed operators. -/
theorem diagonalCellMap_operator (X : SimplicialObject SSet.{u})
    {n m : ℕ} (theta : ⦋n⦌ ⟶ ⦋m⦌) :
    (X.map theta.op ▷ Δ[n]) ≫ diagonalCellMap X n =
      (X.obj (op ⦋m⦌) ◁ SSet.stdSimplex.map theta) ≫ diagonalCellMap X m := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s⟩
  change (X.map (SSet.stdSimplex.objEquiv s).op).app a ((X.map theta.op).app a x) =
    (X.map (SSet.stdSimplex.objEquiv s ≫ theta).op).app a x
  rw [op_comp, Functor.map_comp, NatTrans.comp_app, comp_apply]

/-- The SAME original kth cell into a finite skeleton stage s≥k. -/
def cellToStage (X : SimplicialObject SSet.{u}) (k s : ℕ) (h : k ≤ s) :
    X.obj (op ⦋k⦌) ⊗ Δ[k] ⟶ diagonalFiltration X s :=
  Subcomplex.lift (diagonalCellMap X k) (by
    unfold diagonalFiltration
    exact le_iSup_of_le k (le_iSup_of_le h le_rfl))

@[reassoc (attr := simp)]
theorem cellToStage_ι (X : SimplicialObject SSet.{u}) (k s : ℕ) (h : k ≤ s) :
    cellToStage X k s h ≫ (diagonalFiltration X s).ι = diagonalCellMap X k :=
  Subcomplex.lift_ι _ _

/-- Cell naturality is at the original finite skeleton map. -/
@[reassoc]
theorem cellToStage_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (k s : ℕ) (h : k ≤ s) :
    cellToStage X k s h ≫ diagonalFiltrationNatMap eta s =
      (eta.app (op ⦋k⦌) ▷ Δ[k]) ≫ cellToStage Y k s h := by
  apply (cancel_mono (diagonalFiltration Y s).ι).mp
  simp only [Category.assoc, diagonalFiltrationNatMap_ι, cellToStage_ι_assoc, cellToStage_ι]
  exact (diagonalCellMap_naturality eta k).symm

/-- The actual induction invariant includes Sharp AND every incoming old
cell, so the successor argument never invents the attachment HC assertion. -/
def stageCellInvariant {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (s : ℕ) : Prop :=
  Sharp (diagonalFiltrationNatMap eta s) ∧
    ∀ k (h : k ≤ s), WeakEquivalence
      (pullback.lift (cellToStage X k s h) (eta.app (op ⦋k⦌) ▷ Δ[k])
        (cellToStage_naturality eta k s h) ≫
        comparison (diagonalFiltrationNatMap eta s) (cellToStage Y k s h))

/-- The actual zeroth cell isomorphism retains the inclusion map. -/
theorem zeroIso_hom_cell (X : SimplicialObject SSet.{u}) :
    (diagonalFiltration_zero_iso X).hom = cellToStage X 0 0 (by rfl) := by
  apply (cancel_mono (diagonalFiltration X 0).ι).mp
  simp [diagonalFiltration_zero_iso, Subcomplex.eqToIso, cellToStage]

/-- The first skeletal invariant is derived from original row Sharp;
neither stage Sharp nor its cell HC is a caller outcome. -/
theorem zero_stage_invariant {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n))) : stageCellInvariant eta 0 := by
  let E : Arrow.mk (eta.app (op ⦋0⦌) ▷ Δ[0]) ≅ Arrow.mk (diagonalFiltrationNatMap eta 0) :=
    Arrow.isoMk (diagonalFiltration_zero_iso X) (diagonalFiltration_zero_iso Y) (by
      change (diagonalFiltration_zero_iso X).hom ≫ diagonalFiltrationNatMap eta 0 =
        (eta.app (op ⦋0⦌) ▷ Δ[0]) ≫ (diagonalFiltration_zero_iso Y).hom
      rw [zeroIso_hom_cell, zeroIso_hom_cell]
      exact cellToStage_naturality eta 0 0 (by rfl))
  have stageSharp : Sharp (diagonalFiltrationNatMap eta 0) :=
    (SharpCoproductClosure.sharp_arrowIso_iff E).mp (tensor_map_sharp _ _ (hrows ⦋0⦌))
  refine ⟨stageSharp, ?_⟩
  intro k h
  have hk : k = 0 := Nat.le_zero.mp h
  subst k
  let : IsIso (cellToStage X 0 0 h) := by
    rw [← zeroIso_hom_cell]
    infer_instance
  let : IsIso (cellToStage Y 0 0 h) := by
    rw [← zeroIso_hom_cell]
    infer_instance
  exact strictSquare_hc
    (IsPullback.of_horiz_isIso (CommSq.mk (cellToStage_naturality eta 0 0 h))) stageSharp

/-- ALL operators into an old cell inherit HC to its actual finite stage.
The stage invariant is the previous induction state, not a successor output.
No injectivity, surjectivity, or source-degree bound on theta is imposed. -/
theorem operator_cell_incoming_from_actual_stage_invariant
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    {k m s : ℕ} (theta : ⦋k⦌ ⟶ ⦋m⦌) (h : k ≤ s)
    (previous : stageCellInvariant eta s) :
    WeakEquivalence
      (pullback.lift ((X.map theta.op ▷ Δ[k]) ≫ cellToStage X k s h)
        (eta.app (op ⦋m⦌) ▷ Δ[k]) (by
          calc
            ((X.map theta.op ▷ Δ[k]) ≫ cellToStage X k s h) ≫ diagonalFiltrationNatMap eta s =
                (X.map theta.op ▷ Δ[k]) ≫ ((eta.app (op ⦋k⦌) ▷ Δ[k]) ≫ cellToStage Y k s h) := by
              rw [Category.assoc, cellToStage_naturality]
            _ = (eta.app (op ⦋m⦌) ▷ Δ[k]) ≫ ((Y.map theta.op ▷ Δ[k]) ≫ cellToStage Y k s h) := by
              simp only [← comp_whiskerRight, ← Category.assoc]
              rw [eta.naturality theta.op]) ≫
        comparison (diagonalFiltrationNatMap eta s)
            ((Y.map theta.op ▷ Δ[k]) ≫ cellToStage Y k s h)) := by
  let original : CommSq (X.map theta.op) (eta.app (op ⦋m⦌))
      (eta.app (op ⦋k⦌)) (Y.map theta.op) := CommSq.mk (eta.naturality theta.op)
  have originalHC : WeakEquivalence
      (pullback.lift (X.map theta.op) (eta.app (op ⦋m⦌)) original.w ≫
        comparison (eta.app (op ⦋k⦌)) (Y.map theta.op)) := by
    let := hoperators theta
    let : WeakEquivalence (comparison (eta.app (op ⦋k⦌)) (Y.map theta.op)) := hrows ⦋k⦌ _ _
    change WeakEquivalence (EquifibredDiagonal.relativeComparison eta theta ≫ _)
    infer_instance
  have tensorHC := finite_tensor_hc original (hrows ⦋k⦌) originalHC (K := (Δ[k] : SSet.{u}))
  have tensorNatural : (X.map theta.op ▷ Δ[k]) ≫ (eta.app (op ⦋k⦌) ▷ Δ[k]) =
      (eta.app (op ⦋m⦌) ▷ Δ[k]) ≫ (Y.map theta.op ▷ Δ[k]) := by
    simp only [← comp_whiskerRight]
    rw [eta.naturality theta.op]
  exact (RezkIncomingHC.first_hc_iff_rectangle
    (X.map theta.op ▷ Δ[k]) (cellToStage X k s h) (eta.app (op ⦋m⦌) ▷ Δ[k])
    (eta.app (op ⦋k⦌) ▷ Δ[k]) (diagonalFiltrationNatMap eta s)
    (Y.map theta.op ▷ Δ[k]) (cellToStage Y k s h) tensorNatural
    (cellToStage_naturality eta k s h) (tensor_map_sharp _ _ (hrows ⦋k⦌))
    previous.1 (previous.2 k h)).mp tensorHC

end SSet.RezkSkeletalCell
