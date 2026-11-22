/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadInnerAnodyne
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomZero
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# The complete original space of two-bead extensions

Restriction is the original simplicial internal-Hom map. Its literal
pullback over an original two-bead map retains every prism and every
simplicial operator. Both the restriction and its full fibre projection
lift against all monomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.OriginalTwoBead

/-- The original full coefficient restriction along the two-bead inclusion. -/
def restriction {n : ℕ} (k : Fin (n + 1)) (K : SSet.{u}) :
    (ihom (Δ[n] : SSet.{u})).obj K ⟶
      (ihom (union k : SSet.{u})).obj K :=
  (pre (union k).ι).app K

/-- The full original restriction is a trivial Kan fibration into a quasicategory. -/
theorem restriction_boundaryRLP {n : ℕ} (k : Fin (n + 1))
    (K : SSet.{u}) [Quasicategory K] :
    modelCategoryQuillen.I.rlp (restriction k K) :=
  rlp_I_pre_app_of_innerAnodyneExtensions (inclusion_innerAnodyne k) K

/-- Every original monomorphism lifts in the full restriction map. -/
theorem restriction_monoLifting {n : ℕ} (k : Fin (n + 1))
    (K : SSet.{u}) [Quasicategory K]
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (restriction k K) :=
  rlp_monomorphisms_of_rlp_I (restriction_boundaryRLP k K) i
    (MorphismProperty.monomorphisms.infer_property i)

/-- The actual whole restriction is a scalar realization weak equivalence. -/
theorem restriction_weak {n : ℕ} (k : Fin (n + 1))
    (K : SSet.{u}) [Quasicategory K] :
    realizationWeakEquivalences (restriction k K) :=
  modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (restriction_boundaryRLP k K)

/-- The original vertex of the complete coefficient complex for a bead map. -/
noncomputable def coefficientPoint {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} (σ : (union k : SSet.{u}) ⟶ K) :
    (Δ[0] : SSet.{u}) ⟶ (ihom (union k : SSet.{u})).obj K :=
  yonedaEquiv.symm ((ihom₀Equiv _ _).symm σ)

/-- All original simplex-prism extensions of the complete two-bead map. -/
noncomputable def extensionSpace {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} (σ : (union k : SSet.{u}) ⟶ K) : SSet.{u} :=
  pullback (restriction k K) (coefficientPoint k σ)

/-- Literal projection retaining the whole original simplex prism. -/
noncomputable def extensionSimplex {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} (σ : (union k : SSet.{u}) ⟶ K) :
    extensionSpace k σ ⟶ (ihom (Δ[n] : SSet.{u})).obj K :=
  pullback.fst _ _

/-- Literal point projection of the full original extension space. -/
noncomputable def extensionProjection {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} (σ : (union k : SSet.{u}) ⟶ K) :
    extensionSpace k σ ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd _ _

/-- Every original extension restricts to the same complete original bead map. -/
theorem extension_restriction {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} (σ : (union k : SSet.{u}) ⟶ K) :
    extensionSimplex k σ ≫ restriction k K =
      extensionProjection k σ ≫ coefficientPoint k σ :=
  pullback.condition

/-- The literal full extension fibre projection has all original boundary lifts. -/
theorem extensionProjection_boundaryRLP {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K] (σ : (union k : SSet.{u}) ⟶ K) :
    modelCategoryQuillen.I.rlp (extensionProjection k σ) :=
  modelCategoryQuillen.I.rlp.pullback_snd (restriction k K) (coefficientPoint k σ)
    (restriction_boundaryRLP k K)

/-- All original coefficient monomorphisms lift in the full fibre. -/
theorem extensionProjection_monoLifting {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K] (σ : (union k : SSet.{u}) ⟶ K)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (extensionProjection k σ) :=
  rlp_monomorphisms_of_rlp_I (extensionProjection_boundaryRLP k σ) i
    (MorphismProperty.monomorphisms.infer_property i)

/-- The full original space of extensions is weakly contractible. -/
theorem extensionProjection_weak {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K] (σ : (union k : SSet.{u}) ⟶ K) :
    realizationWeakEquivalences (extensionProjection k σ) :=
  modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (extensionProjection_boundaryRLP k σ)

/-- The full original space of extensions is a Kan complex. -/
theorem extensionSpace_kan {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K] (σ : (union k : SSet.{u}) ⟶ K) :
    KanComplex (extensionSpace k σ) := by
  have hr := rlp_monomorphisms_of_rlp_I (extensionProjection_boundaryRLP k σ)
  have hf : modelCategoryQuillen.J.rlp (extensionProjection k σ) :=
    fun _ _ f h => hr f (modelCategoryQuillen.J_le_monomorphisms f h)
  let _ : Fibration (extensionProjection k σ) :=
    (modelCategoryQuillen.fibration_iff _).2 hf
  exact (isFibrant_iff_of_isTerminal (extensionProjection k σ)
    stdSimplex.isTerminalObj₀).2 inferInstance

/-- There is an actual original simplex extension, with its literal restriction. -/
theorem exists_original_extension {n : ℕ} (k : Fin (n + 1))
    {K : SSet.{u}} [Quasicategory K] (σ : (union k : SSet.{u}) ⟶ K) :
    ∃ τ : (Δ[n] : SSet.{u}) ⟶ K, (union k).ι ≫ τ = σ := by
  obtain ⟨x, hx⟩ := exists_vertex_lift_of_rlp_I (restriction_boundaryRLP k K)
    ((ihom₀Equiv _ _).symm σ)
  refine ⟨ihom₀Equiv _ _ x, ?_⟩
  apply (ihom₀Equiv _ _).symm.injective
  rw [ihom₀Equiv_symm_pre, Equiv.symm_apply_apply]
  exact hx

end SSet.OriginalTwoBead
