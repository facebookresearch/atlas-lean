/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
import MathlibExt.AlgebraicTopology.SingularSet.Coproducts
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationCoproducts
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Selected TopCat fibrations and disjoint product projections

Actual singular coproduct preservation and Kan lifting give coproduct
closure for the selected TopCat fibrations. Every coefficient space is
fibrant in this model, so the actual disjoint product projection is a
fibration. The projection retains the exact summand and base coordinate.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped SSet.modelCategoryQuillen TopCat.modelCategory

universe u

namespace TopCat

private theorem singular_fibration_iff {E B : TopCat.{u}} (p : E ⟶ B) :
    Fibration (toSSet.map p) ↔ Fibration p := by
  rw [SSet.modelCategoryQuillen.fibration_iff, HomotopicalAlgebra.fibration_iff]
  change SSet.modelCategoryQuillen.J.rlp (toSSet.map p) ↔ realizedHornInclusions.rlp p
  rw [← hornRLP_iff_toSSet_mem_J_rlp]

private theorem fibration_sigmaMap_aux
    {ι : Type u} {A B : ι → TopCat.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) := by
  apply (singular_fibration_iff (Limits.Sigma.map q)).mp
  let cA := sigmaComparison toSSet A
  let cB := sigmaComparison toSSet B
  let _ : IsIso cA := inferInstance
  let _ : IsIso cB := inferInstance
  have hs : Fibration (Limits.Sigma.map (fun c => toSSet.map (q c))) :=
    SSet.fibration_sigmaMap _ (fun c => (singular_fibration_iff (q c)).mpr (hq c))
  let _ : Fibration (Limits.Sigma.map (fun c => toSSet.map (q c))) := hs
  have hn : Limits.Sigma.map (fun c => toSSet.map (q c)) ≫ cB =
      cA ≫ toSSet.map (Limits.Sigma.map q) := by
    dsimp only [cA, cB]
    apply Sigma.hom_ext
    intro c
    simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison,
      ← Functor.map_comp, Sigma.ι_map]
  have he : toSSet.map (Limits.Sigma.map q) =
      inv cA ≫ Limits.Sigma.map (fun c => toSSet.map (q c)) ≫ cB := by
    calc
      toSSet.map (Limits.Sigma.map q) = inv cA ≫ cA ≫ toSSet.map (Limits.Sigma.map q) := by simp
      _ = inv cA ≫ Limits.Sigma.map (fun c => toSSet.map (q c)) ≫ cB := by rw [← hn]
  rw [he]
  infer_instance

/-- Actual coproducts of selected TopCat fibrations are selected fibrations. -/
theorem fibration_sigmaMap
    {ι : Type u} {A B : ι → TopCat.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) :=
  fibration_sigmaMap_aux q hq

private theorem everySpace_isFibrant (X : TopCat.{u}) : IsFibrant X := by
  rw [isFibrant_iff, HomotopicalAlgebra.fibration_iff]
  change realizedHornInclusions.rlp (terminal.from X)
  rw [hornRLP_iff_toSSet_mem_J_rlp, ← SSet.modelCategoryQuillen.fibration_iff]
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj toSSet _ terminalIsTerminal)]
  exact toSSet_obj_kanComplex X

private def nativeProductProjection (X B : TopCat.{u}) : TopCat.of (X × B) ⟶ B :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private theorem nativeProductProjection_fibration (X B : TopCat.{u}) :
    Fibration (nativeProductProjection X B) := by
  let _ : IsFibrant X := everySpace_isFibrant X
  have he : nativeProductProjection X B = (prodIsoProd X B).inv ≫ Limits.prod.snd :=
    (prodIsoProd_inv_snd X B).symm
  rw [he]
  infer_instance

/-- The actual disjoint product projection retains the exact summand
and drops only the coefficient coordinate. -/
def sigmaProductProjection {ι : Type u} (X B : ι → TopCat.{u}) :
    TopCat.of (Σ c, X c × B c) ⟶ TopCat.of (Σ c, B c) :=
  TopCat.ofHom ⟨Sigma.map id (fun _ => Prod.snd),
    continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_snd)⟩

private theorem sigmaProductProjection_apply_aux
    {ι : Type u} (X B : ι → TopCat.{u}) (c : ι) (x : X c) (b : B c) :
    sigmaProductProjection X B ⟨c, x, b⟩ = ⟨c, b⟩ := rfl

/-- The literal total and base coordinates of the disjoint projection. -/
theorem sigmaProductProjection_apply
    {ι : Type u} (X B : ι → TopCat.{u}) (c : ι) (x : X c) (b : B c) :
    sigmaProductProjection X B ⟨c, x, b⟩ = ⟨c, b⟩ :=
  sigmaProductProjection_apply_aux X B c x b

private theorem fibration_sigmaProductProjection_aux
    {ι : Type u} (X B : ι → TopCat.{u}) : Fibration (sigmaProductProjection X B) := by
  let A : ι → TopCat.{u} := fun c => TopCat.of (X c × B c)
  let q : ∀ c, A c ⟶ B c := fun c => nativeProductProjection (X c) (B c)
  let eA := sigmaIsoSigma A
  let eB := sigmaIsoSigma B
  let _ : Fibration (Limits.Sigma.map q) :=
    fibration_sigmaMap q (fun c => nativeProductProjection_fibration (X c) (B c))
  have hn : eA.hom ≫ sigmaProductProjection X B = Limits.Sigma.map q ≫ eB.hom := by
    dsimp only [eA, eB, q, A]
    apply Sigma.hom_ext
    intro c
    simp only [Sigma.ι_map_assoc, sigmaIsoSigma_hom_ι_assoc, sigmaIsoSigma_hom_ι]
    apply TopCat.ext
    intro z
    rfl
  have he : sigmaProductProjection X B = eA.inv ≫ Limits.Sigma.map q ≫ eB.hom := by
    calc
      sigmaProductProjection X B = eA.inv ≫ eA.hom ≫ sigmaProductProjection X B := by simp
      _ = eA.inv ≫ Limits.Sigma.map q ≫ eB.hom := by rw [hn]
  rw [he]
  infer_instance

/-- The actual disjoint product projection is a selected TopCat fibration
for arbitrary coefficient and base spaces. -/
theorem fibration_sigmaProductProjection
    {ι : Type u} (X B : ι → TopCat.{u}) : Fibration (sigmaProductProjection X B) :=
  fibration_sigmaProductProjection_aux X B

end TopCat
