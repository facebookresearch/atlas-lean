/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyModel
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidRealizationWeakEquivalence
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Fundamental groupoids after attaching higher cells

Attaching a family of cells of one fixed dimension at least three preserves the
two-truncation of the old-space inclusion. The associated simplicial model gives
an isomorphism of fundamental groupoids and, for a cofibrant space, an
equivalence on the topological attachment.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology.CWComplex Opposite
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory

universe u

public section

namespace AlgebraicTopology.CellFamilySimplicialModel

/-- A cell of dimension at least three has its complete two-truncation
already in its boundary. This is the actual standard boundary inclusion. -/
theorem truncation_boundary_isIso (n : ℕ) (hn : 2 ≤ n) :
    IsIso ((SSet.truncation 2).map (SSet.boundary.{u} (n + 1)).ι) := by
  let t := (SSet.truncation 2).map (SSet.boundary.{u} (n + 1)).ι
  let : ∀ k, IsIso (t.app k) := fun k => by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective
      (fun z : {s : (Δ[n + 1] : SSet.{u}).obj (op k.unop.obj) //
        s ∈ (SSet.boundary.{u} (n + 1)).obj (op k.unop.obj)} => z.val)
    refine ⟨Subtype.val_injective, ?_⟩
    intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    have hk : k.unop.obj.len ≤ 2 := k.unop.property
    have hlt : k.unop.obj.len < n + 1 := Nat.lt_succ_of_le (hk.trans hn)
    change z ∈ (SSet.boundary.{u} (n + 1)).obj (op ⦋k.unop.obj.len⦌)
    rw [SSet.boundary_obj_eq_univ k.unop.obj.len (n + 1) hlt]
    exact Set.mem_univ z
  exact NatIso.isIso_of_isIso_app t

private theorem truncation_boundarySum_isIso (n : ℕ) (hn : 2 ≤ n) (I : Type u) :
    IsIso ((SSet.truncation 2).map (boundarySum.{u} n I)) := by
  let F : SSet.{u} ⥤ SSet.Truncated.{u} 2 := SSet.truncation 2
  let : F.IsLeftAdjoint := (SSet.coskAdj 2).isLeftAdjoint
  let A : SSet.{u} := (SSet.boundary.{u} (n + 1)).toSSet
  let B : SSet.{u} := Δ[n + 1]
  let i : A ⟶ B := (SSet.boundary.{u} (n + 1)).ι
  let fA : I → SSet.{u} := fun _ => A
  let fB : I → SSet.{u} := fun _ => B
  let dA : Discrete I ⥤ SSet.Truncated.{u} 2 := Discrete.functor (fun j => F.obj (fA j))
  let dB : Discrete I ⥤ SSet.Truncated.{u} 2 := Discrete.functor (fun j => F.obj (fB j))
  let cA : Cofan (fun j : I => F.obj (fA j)) :=
    Cofan.mk (F.obj (∐ fA)) (fun j => F.map (Sigma.ι fA j))
  let cB : Cofan (fun j : I => F.obj (fB j)) :=
    Cofan.mk (F.obj (∐ fB)) (fun j => F.map (Sigma.ι fB j))
  let a : dA ⟶ dB := Discrete.natTrans (fun _ => F.map i)
  let phi : F.obj (∐ fA) ⟶ F.obj (∐ fB) :=
    F.map (CategoryTheory.Limits.Sigma.map (fun _ : I => i))
  have hA : IsColimit cA := isColimitOfHasCoproductOfPreservesColimit F fA
  have hB : IsColimit cB := isColimitOfHasCoproductOfPreservesColimit F fB
  have ha : (MorphismProperty.isomorphisms (SSet.Truncated.{u} 2)).functorCategory (Discrete I) a
    := by
    intro j
    change IsIso (F.map i)
    exact truncation_boundary_isIso n hn
  have hphi : ∀ j : Discrete I, cA.ι.app j ≫ phi = a.app j ≫ cB.ι.app j := by
    intro j
    change F.map (Sigma.ι fA j.as) ≫ F.map (CategoryTheory.Limits.Sigma.map (fun _ : I => i)) =
      F.map i ≫ F.map (Sigma.ι fB j.as)
    exact (F.map_comp _ _).symm.trans
      ((congrArg F.map (Sigma.ι_map (fun _ : I => i) j.as)).trans (F.map_comp _ _))
  have h : IsIso phi :=
    MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := MorphismProperty.isomorphisms (SSet.Truncated.{u} 2))
      (J := Discrete I) dA dB cA cB hA hB a ha phi hphi
  rw [boundarySum_eq]
  exact h

/-- The actual original singular-space inclusion remains an isomorphism
on its entire two-truncation after attaching this family of higher cells. -/
theorem truncation_oldInclusion_isIso (X : TopCat.{u}) (n : ℕ) (hn : 2 ≤ n)
    (I : Type u) (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    IsIso ((SSet.truncation 2).map (oldInclusion X n I att)) := by
  let F : SSet.{u} ⥤ SSet.Truncated.{u} 2 := SSet.truncation 2
  let : F.IsLeftAdjoint := (SSet.coskAdj 2).isLeftAdjoint
  let : IsIso (F.map (boundarySum n I)) := truncation_boundarySum_isIso n hn I
  exact ((isPushout X n I att).map F).isIso_inr_of_isIso

/-- The unchanged old-space leg of the same actual higher-cell model induces
an isomorphism of fundamental groupoids on every component. -/
theorem oldInclusionFundamentalGroupoid_isIso (X : TopCat.{u}) (n : ℕ) (hn : 2 ≤ n)
    (I : Type u) (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    (SSet.mapFundamentalGroupoid (oldInclusion X n I att)).IsIso :=
  SSet.isIso_mapFundamentalGroupoid_of_isIso (oldInclusion X n I att)
    (truncation_oldInclusion_isIso X n hn I att)

/-- The actual higher-cell inclusion of the literal original space induces
an equivalence of fundamental groupoids, derived from the same model and its
actual weak comparison rather than from a supplied topological witness. -/
theorem inclusionFundamentalGroupoid_isEquivalence (X : TopCat.{u})
    [HomotopicalAlgebra.IsCofibrant X]
    (n : ℕ) (hn : 2 ≤ n) (I : Type u)
    (att : I → ((classicalCellDiskPair.{u} (n + 1)).snd ⟶ X)) :
    (SSet.mapFundamentalGroupoid
      (TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att))).IsEquivalence := by
  let a := oldInclusion X n I att
  let c := toSingular X n I att
  let f := TopCat.toSSet.map (CellFamilyAttachment.inclusion X n att)
  let : (SSet.mapFundamentalGroupoid a).IsIso :=
    oldInclusionFundamentalGroupoid_isIso X n hn I att
  let : (SSet.mapFundamentalGroupoid a).IsEquivalence := inferInstance
  let : (SSet.mapFundamentalGroupoid c).IsEquivalence :=
    SSet.realizationWeakEquivalences.isEquivalence_mapFundamentalGroupoid
      (toSingular_weak X n I att)
  let e : SSet.mapFundamentalGroupoid f ≅
      SSet.mapFundamentalGroupoid a ⋙ SSet.mapFundamentalGroupoid c :=
    SSet.congrMapFundamentalGroupoidOfEq (toSingular_old X n I att).symm ≪≫
      (SSet.mapFundamentalGroupoidComp a c).symm
  exact Functor.isEquivalence_of_iso e.symm

end AlgebraicTopology.CellFamilySimplicialModel

end
