/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexAttachmentCompat
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Realized horn inclusions in the boundary-generated left class

Every realized horn inclusion has the left lifting property against every topological map that
has right lifting against the realized boundary inclusions. This is the inclusion of the
realized-horn family in the left class LLP(RLP(realized boundaries)).

A horn inclusion is built from the horn toward its top simplex by finitely many boundary-cell
attachments. Geometric realization preserves these pushout attachments, placing the realized
horn map in that left class. The statement holds in every universe u.
-/

@[expose] public section

open CategoryTheory MorphismProperty Simplicial
open scoped Simplicial

universe u

namespace TopCat

private theorem hornInclusionMemLLP (n : ℕ) (k : Fin (n + 2)) :
    (realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι) := by
  obtain ⟨len, C, hC0, _hCk, hmono, hstep⟩ :=
    SSet.boundary.exists_finite_attachment_chain_of_le_of_finite
      (SSet.horn.{u} (n + 1) k) ⊤ le_top
  have hStep : ∀ (i : ℕ) (h : i < len),
      (realizedBoundaryInclusions.{u}).rlp.llp
        (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
          (hmono ⟨i, Nat.lt_trans h (Nat.lt_succ_self len)⟩
            ⟨i + 1, Nat.succ_lt_succ h⟩ (Nat.le_succ i)))) := by
    intro i h
    obtain ⟨m, t, b, hle, hPush, _, _⟩ := hstep i h
    have hPushTop : IsPushout (SSet.toTop.{u}.map t)
        (SSet.toTop.{u}.map (SSet.boundary.{u} m).ι)
        (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE hle))
        (SSet.toTop.{u}.map b) :=
      hPush.map SSet.toTop.{u}
    have hBase : realizedBoundaryInclusions.{u}
        (SSet.toTop.{u}.map (SSet.boundary.{u} m).ι) :=
      boundary_mem_realizedBoundaryInclusions m
    have hMem : (realizedBoundaryInclusions.{u}).pushouts
        (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE hle)) :=
      MorphismProperty.pushouts_mk _ hPushTop hBase
    exact MorphismProperty.pushouts_le_llp_rlp _ _ hMem
  have hComp : ∀ (j : ℕ) (hj : j ≤ len),
      (realizedBoundaryInclusions.{u}).rlp.llp
        (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨j, Nat.lt_succ_of_le hj⟩
            (Nat.zero_le j)))) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have h1 : (SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨0, Nat.lt_succ_of_le hj⟩
            (Nat.zero_le 0)) : (C ⟨0, Nat.zero_lt_succ len⟩).toSSet ⟶
              (C ⟨0, Nat.zero_lt_succ len⟩).toSSet) =
          𝟙 (C ⟨0, Nat.zero_lt_succ len⟩).toSSet :=
        SSet.Subcomplex.homOfLE_refl _
      have hId : SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨0, Nat.lt_succ_of_le hj⟩
            (Nat.zero_le 0)) : (C ⟨0, Nat.zero_lt_succ len⟩).toSSet ⟶
              (C ⟨0, Nat.zero_lt_succ len⟩).toSSet) =
          𝟙 (SSet.toTop.{u}.obj (C ⟨0, Nat.zero_lt_succ len⟩).toSSet) := by
        rw [h1]
        simp
      rw [hId]
      exact MorphismProperty.llp_of_isIso _ _
    | succ n ih =>
      intro hj
      have hn : n ≤ len := Nat.le_of_succ_le hj
      have hlt : n < len := Nat.lt_of_succ_le hj
      have ih' := ih hn
      have hs := hStep n hlt
      have hEq : SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨n + 1, Nat.lt_succ_of_le hj⟩
            (Nat.zero_le (n + 1)))) =
          SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
            (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨n, Nat.lt_succ_of_le hn⟩
              (Nat.zero_le n))) ≫
            SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
              (hmono ⟨n, Nat.lt_trans hlt (Nat.lt_succ_self len)⟩
                ⟨n + 1, Nat.succ_lt_succ hlt⟩ (Nat.le_succ n))) := by
        rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_comp]
      rw [hEq]
      exact MorphismProperty.comp_mem _ _ _ ih' hs
  have hTop : (realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
        (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨len, Nat.lt_succ_of_le le_rfl⟩
          (Nat.zero_le len)))) :=
    hComp len le_rfl
  have hInv : (realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map (SSet.Subcomplex.eqToIso hC0).inv) :=
    MorphismProperty.llp_of_isIso _ _
  have hCk : (realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map (SSet.Subcomplex.eqToIso _hCk).hom) :=
    MorphismProperty.llp_of_isIso _ _
  have hIso : (realizedBoundaryInclusions.{u}).rlp.llp
      (SSet.toTop.{u}.map
        (SSet.Subcomplex.topIso (Δ[n + 1] : SSet.{u})).hom) :=
    MorphismProperty.llp_of_isIso _ _
  have hSSet : (SSet.horn.{u} (n + 1) k).ι =
      (SSet.Subcomplex.eqToIso hC0).inv ≫
        SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨len, Nat.lt_succ_of_le le_rfl⟩
            (Nat.zero_le len)) ≫
        (SSet.Subcomplex.eqToIso _hCk).hom ≫
        (SSet.Subcomplex.topIso (Δ[n + 1] : SSet.{u})).hom := by
    simp only [SSet.Subcomplex.eqToIso_inv, SSet.Subcomplex.eqToIso_hom,
      SSet.Subcomplex.topIso_hom, SSet.Subcomplex.homOfLE_ι]
  have hFactor : SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) k).ι =
      SSet.toTop.{u}.map (SSet.Subcomplex.eqToIso hC0).inv ≫
        SSet.toTop.{u}.map (SSet.Subcomplex.homOfLE
          (hmono ⟨0, Nat.zero_lt_succ len⟩ ⟨len, Nat.lt_succ_of_le le_rfl⟩
            (Nat.zero_le len))) ≫
        SSet.toTop.{u}.map (SSet.Subcomplex.eqToIso _hCk).hom ≫
        SSet.toTop.{u}.map
          (SSet.Subcomplex.topIso (Δ[n + 1] : SSet.{u})).hom := by
    simp only [hSSet, Functor.map_comp]
  rw [hFactor]
  exact MorphismProperty.comp_mem _ _ _ hInv
    (MorphismProperty.comp_mem _ _ _ hTop
      (MorphismProperty.comp_mem _ _ _ hCk hIso))

/-- In TopCat of any universe u, every realized simplicial horn inclusion has left lifting against
every map with right lifting against the realized simplicial boundary inclusions. -/
theorem realizedHornInclusions_le_boundaryRLPLLP :
    (realizedHornInclusions : MorphismProperty TopCat.{u}) ≤
      (realizedBoundaryInclusions : MorphismProperty TopCat.{u}).rlp.llp := by
  unfold realizedHornInclusions
  apply iSup_le
  intro n
  rw [MorphismProperty.ofHoms_le_iff]
  intro i
  exact hornInclusionMemLLP n i

end TopCat
