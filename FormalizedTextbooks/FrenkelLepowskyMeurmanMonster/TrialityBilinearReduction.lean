/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Bilinear reduction of actual triality product preservation to the source blocks.
Diagonal factors are proved already; commutativity removes reversed pairs.
Source: Conway, Invent. Math. 79 (1985), §12; Seysen, §8.1, Table 5.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityBasisVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCommutativity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A source octad block basis vector in the actual Griess space. -/
noncomputable def trialityOctadBasis (o : Fin 759) (e : Fin 64) : GriessSpace :=
  trialityBlocksEquiv.symm (0, (0, (Pi.single o (Pi.single e 1), 0)))

@[simp] theorem trialityOctadBasis_blocks (o : Fin 759) (e : Fin 64) :
    trialityBlocksEquiv (trialityOctadBasis o e) =
      (0, (0, (Pi.single o (Pi.single e 1), 0))) :=
  trialityBlocksEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Triality acts on each octad basis vector by the published 64 by 64 matrix. -/
theorem sExtra_octad_basis (o : Fin 759) (e : Fin 64) :
    sExtra (trialityOctadBasis o e) =
      ∑ f, trialityRealMatrix f e • trialityOctadBasis o f := by
  apply trialityBlocksEquiv.injective
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityOctadBasis_blocks, map_sum, map_smul]
  simp only [trialityBlockAction, LinearEquiv.prodCongr_apply, map_zero]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, Prod.fst_sum]
  · ext p k
    simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, LinearEquiv.piCongrRight_apply]
    by_cases hp : p = o
    · subst p
      simp only [Pi.single_eq_same, trialityOctadAction_matrix, Matrix.mulVec_single_one]
      simp [Pi.single_apply]
    · simp [hp]
  · simp [Prod.snd_sum]

/-- Reconstruct an arbitrary vector from the four families of source coordinates. -/
theorem triality_source_basis_decomposition (x : GriessSpace) :
    x = (∑ i, (trialityBlocksEquiv x).1 i • trialityDiagonalVector (Pi.single i 1)) +
      (∑ s, ∑ p, (trialityBlocksEquiv x).2.1 s p • trialityABCBasis s p) +
      (∑ o, ∑ e, (trialityBlocksEquiv x).2.2.1 o e • trialityOctadBasis o e) +
      (∑ s, ∑ k, (trialityBlocksEquiv x).2.2.2 s k • trialityXYZBasis s k) := by
  apply trialityBlocksEquiv.injective
  simp only [map_add, map_sum, map_smul, trialityDiagonalVector, trialityABCBasis_blocks,
    trialityOctadBasis_blocks, trialityXYZBasis_blocks, LinearEquiv.apply_symm_apply]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum, Pi.single_apply, Finset.sum_apply]

/-- Source coordinates indexing all four actual summands. -/
abbrev TrialitySourceIndex := (Fin 24) ⊕ ((Fin 3 × Fin 276) ⊕
  ((Fin 759 × Fin 64) ⊕ (Fin 3 × Fin 49152)))

/-- The full published source basis, expressed in the actual Griess space. -/
noncomputable def trialitySourceBasis : TrialitySourceIndex → GriessSpace
  | Sum.inl i => trialityDiagonalVector (Pi.single i 1)
  | Sum.inr (Sum.inl (s, p)) => trialityABCBasis s p
  | Sum.inr (Sum.inr (Sum.inl (o, e))) => trialityOctadBasis o e
  | Sum.inr (Sum.inr (Sum.inr (s, k))) => trialityXYZBasis s k

/-- The source basis spans the full actual 196884-dimensional space. -/
theorem trialitySourceBasis_span :
    Submodule.span ℝ (Set.range trialitySourceBasis) = ⊤ := by
  apply top_unique
  intro x _
  let P := Submodule.span ℝ (Set.range trialitySourceBasis)
  have hb (i : TrialitySourceIndex) : trialitySourceBasis i ∈ P :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [triality_source_basis_decomposition x]
  apply P.add_mem
  · apply P.add_mem
    · apply P.add_mem
      · apply P.sum_mem
        intro i _
        exact P.smul_mem _ (hb (Sum.inl i))
      · apply P.sum_mem
        intro s _
        apply P.sum_mem
        intro p _
        exact P.smul_mem _ (hb (Sum.inr (Sum.inl (s, p))))
    · apply P.sum_mem
      intro o _
      apply P.sum_mem
      intro e _
      exact P.smul_mem _ (hb (Sum.inr (Sum.inr (Sum.inl (o, e)))))
  · apply P.sum_mem
    intro s _
    apply P.sum_mem
    intro k _
    exact P.smul_mem _ (hb (Sum.inr (Sum.inr (Sum.inr (s, k)))))

/-- Bilinearity reduces preservation to the actual source block basis. -/
theorem griessProduct_invariance_iff_source_basis (e : GriessSpace ≃ₗ[ℝ] GriessSpace) :
    (∀ x y, e (griessProd x y) = griessProd (e x) (e y)) ↔
    ∀ i j : TrialitySourceIndex,
      e (griessProd (trialitySourceBasis i) (trialitySourceBasis j)) =
        griessProd (e (trialitySourceBasis i)) (e (trialitySourceBasis j)) := by
  constructor
  · intro h i j
    exact h _ _
  · intro h
    have hm : griessProd.compr₂ e.toLinearMap =
        griessProd.compl₁₂ e.toLinearMap e.toLinearMap := by
      apply LinearMap.ext_on_range trialitySourceBasis_span
      intro i
      apply LinearMap.ext_on_range trialitySourceBasis_span
      intro j
      simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_toLinearMap] using h i j
    intro x y
    simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_toLinearMap] using LinearMap.congr_fun (LinearMap.congr_fun hm x) y

/-- The explicit product equation for a given pair of actual vectors. -/
def TrialityProductPreserved (x y : GriessSpace) : Prop :=
  sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y)

theorem trialityProductPreserved_symm (x y : GriessSpace) :
    TrialityProductPreserved x y ↔ TrialityProductPreserved y x := by
  simp only [TrialityProductPreserved, griessProd_comm x y,
    griessProd_comm (sExtra x) (sExtra y)]

set_option maxRecDepth 10000 in
/-- The six unordered pairs of non-diagonal source blocks suffice for full
triality preservation. All pairs involving a diagonal factor are discharged
by the already proved actual diagonal multiplication theorem. -/
theorem sExtra_preserves_product_of_source_pairs
    (hAA : ∀ s p t q, TrialityProductPreserved
      (trialityABCBasis s p) (trialityABCBasis t q))
    (hAO : ∀ s p o e, TrialityProductPreserved
      (trialityABCBasis s p) (trialityOctadBasis o e))
    (hAT : ∀ s p t k, TrialityProductPreserved
      (trialityABCBasis s p) (trialityXYZBasis t k))
    (hOO : ∀ o e p f, TrialityProductPreserved
      (trialityOctadBasis o e) (trialityOctadBasis p f))
    (hOT : ∀ o e t k, TrialityProductPreserved
      (trialityOctadBasis o e) (trialityXYZBasis t k))
    (hTT : ∀ s k t l, TrialityProductPreserved
      (trialityXYZBasis s k) (trialityXYZBasis t l)) :
    ∀ x y, sExtra (griessProd x y) = griessProd (sExtra x) (sExtra y) := by
  apply (griessProduct_invariance_iff_source_basis sExtra).mpr
  intro i j
  change TrialityProductPreserved (trialitySourceBasis i) (trialitySourceBasis j)
  rcases i with i | (⟨s, p⟩ | (⟨o, e⟩ | ⟨t, k⟩)) <;>
    rcases j with j | (⟨u, q⟩ | (⟨v, f⟩ | ⟨w, l⟩)) <;>
    simp only [trialitySourceBasis]
  · exact sExtra_preserves_diagonal_product _ _
  · exact sExtra_preserves_diagonal_product _ _
  · exact sExtra_preserves_diagonal_product _ _
  · exact sExtra_preserves_diagonal_product _ _
  · exact (trialityProductPreserved_symm _ _).mpr
      (sExtra_preserves_diagonal_product _ _)
  · exact hAA _ _ _ _
  · exact hAO _ _ _ _
  · exact hAT _ _ _ _
  · exact (trialityProductPreserved_symm _ _).mpr
      (sExtra_preserves_diagonal_product _ _)
  · exact (trialityProductPreserved_symm _ _).mpr (hAO _ _ _ _)
  · exact hOO _ _ _ _
  · exact hOT _ _ _ _
  · exact (trialityProductPreserved_symm _ _).mpr
      (sExtra_preserves_diagonal_product _ _)
  · exact (trialityProductPreserved_symm _ _).mpr (hAT _ _ _ _)
  · exact (trialityProductPreserved_symm _ _).mpr (hOT _ _ _ _)
  · exact hTT _ _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
