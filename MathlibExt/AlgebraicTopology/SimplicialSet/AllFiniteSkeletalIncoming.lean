/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.AllSkeletalSharpCellInvariants

/-!
# Homotopy cartesian transition squares of diagonal skeleta

Diagonal skeletal transition maps compose according to their degree inequalities. If all row maps are sharp and all simplex-operator relative comparisons are weak equivalences, every transition from the nth to the mth diagonal skeleton, for n ≤ m, has a weak pullback-to-homotopy-pullback comparison in its naturality square.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkAllFiniteSkeletalIncoming
open SharpComparisonDraft RezkSkeletalCell RezkSkeletalSuccessor RezkAllSkeletalInvariants

private theorem hc_transport_eq {A X B Y : SSet.{u}}
    {f f' : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g g' : B ⟶ Y}
    (sq : CommSq f s p g) (sq' : CommSq f' s p g') (hf : f = f') (hg : g = g')
    (hc : WeakEquivalence (pullback.lift f' s sq'.w ≫ comparison p g')) :
    WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g) := by
  exact (RezkCompatiblePushout.hc_weakSquare_iff sq sq' (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, Category.id_comp] using hf)
    (by simp) (by simp)
    (by simpa only [Category.comp_id, Category.id_comp] using hg)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hc

@[reassoc]
theorem filtrationMap_comp (X : SimplicialObject SSet.{u}) {n m k : ℕ}
    (hnm : n ≤ m) (hmk : m ≤ k) :
    diagonalFiltrationMap X hnm ≫ diagonalFiltrationMap X hmk =
      diagonalFiltrationMap X (hnm.trans hmk) := by
  apply (cancel_mono (diagonalFiltration X k).ι).mp
  simp [Category.assoc, diagonalFiltrationMap]

/-- Every ORIGINAL finite-stage incoming square is HC, not merely every
cell square. The native successor comparison is composed using actual
finite Sharp maps; total Sharp is never a premise. -/
theorem all_finite_skeletal_incoming_hc
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ a : SimplexCategory, Sharp (eta.app (op a)))
    (hoperators : ∀ {a b : SimplexCategory} (f : a ⟶ b),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f))
    (n m : ℕ) (h : n ≤ m) :
    WeakEquivalence
      (pullback.lift (diagonalFiltrationMap X h) (diagonalFiltrationNatMap eta n)
        (diagonalFiltrationMap_naturality eta h).symm ≫
        comparison (diagonalFiltrationNatMap eta m) (diagonalFiltrationMap Y h)) := by
  have all := all_skeletal_sharp_and_cell_incoming eta hrows hoperators
  induction m, h using Nat.le_induction with
  | base =>
      have sq : IsPullback (diagonalFiltrationMap X le_rfl) (diagonalFiltrationNatMap eta n)
          (diagonalFiltrationNatMap eta n) (diagonalFiltrationMap Y le_rfl) := by
        simpa [diagonalFiltrationMap] using
            IsPullback.of_id_fst (f := diagonalFiltrationNatMap eta n)
      exact RezkCompatiblePushout.strictSquare_hc sq (all n).1
  | succ m h prior =>
      have next := successor_sharp_and_both_incoming eta hrows hoperators m (all m)
      have rectangle := (RezkIncomingHC.first_hc_iff_rectangle
        (diagonalFiltrationMap X h) (diagonalFiltrationMap X (Nat.le_succ m))
        (diagonalFiltrationNatMap eta n) (diagonalFiltrationNatMap eta m)
        (diagonalFiltrationNatMap eta (m + 1))
        (diagonalFiltrationMap Y h) (diagonalFiltrationMap Y (Nat.le_succ m))
        (diagonalFiltrationMap_naturality eta h).symm
        (diagonalFiltrationMap_naturality eta (Nat.le_succ m)).symm
        (all m).1 next.1 next.2.1).mp prior
      let actual := CommSq.mk
        (diagonalFiltrationMap_naturality eta (h.trans (Nat.le_succ m))).symm
      let pasted := (CommSq.mk (diagonalFiltrationMap_naturality eta h).symm).horiz_comp
        (CommSq.mk (diagonalFiltrationMap_naturality eta (Nat.le_succ m)).symm)
      exact hc_transport_eq actual pasted
        (filtrationMap_comp X h (Nat.le_succ m)).symm
        (filtrationMap_comp Y h (Nat.le_succ m)).symm rectangle

end SSet.RezkAllFiniteSkeletalIncoming
