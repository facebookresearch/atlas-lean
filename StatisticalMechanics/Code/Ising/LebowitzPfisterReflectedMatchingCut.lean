/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterMatchingCutCurrent
import Code.Ising.FiniteVolumeRelabel









open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]




structure LPReflectedMatchingCut
    (G : SimpleGraph W) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) where
  reflect : Equiv.Perm W
  involutive : Function.Involutive reflect
  reflect_left : forall i, reflect (left i) = right i
  reflect_right : forall i, reflect (right i) = left i
  reflect_g0 : reflect g0 = g1
  reflect_g1 : reflect g1 = g0
  adj_iff : forall x y, G.Adj (reflect x) (reflect y) <-> G.Adj x y
  coupling : forall e, J (Sym2.map reflect e) = J e


def lpReflectSource
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (S : Finset W) : Finset W :=
  S.map R.reflect.toEmbedding

theorem lpReflectSource_symmDiff
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (A B : Finset W) :
    lpReflectSource R (A ∆ B) =
      lpReflectSource R A ∆ lpReflectSource R B := by
  unfold lpReflectSource
  ext x
  simp only [Finset.mem_map, Finset.mem_symmDiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨y, hA, rfl⟩,
        fun ⟨z, hz, heq⟩ => hB (by simpa [R.reflect.injective heq] using hz)⟩
    · exact Or.inr ⟨⟨y, hB, rfl⟩,
        fun ⟨z, hz, heq⟩ => hA (by simpa [R.reflect.injective heq] using hz)⟩
  · rintro (⟨⟨y, hA, rfl⟩, hB⟩ | ⟨⟨y, hB, rfl⟩, hA⟩)
    · exact ⟨y, Or.inl ⟨hA,
        fun hy => hB ⟨y, hy, rfl⟩⟩, rfl⟩
    · exact ⟨y, Or.inr ⟨hB,
        fun hy => hA ⟨y, hy, rfl⟩⟩, rfl⟩

@[simp] theorem lpReflectSource_empty
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1) :
    lpReflectSource R ∅ = ∅ := by
  simp [lpReflectSource]


theorem lpReflectSource_seam
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1) (i : I) :
    lpReflectSource R (lpMatchingSeamSource left right i) =
      lpMatchingSeamSource left right i := by
  rw [lpMatchingSeamSource, lpReflectSource_symmDiff]
  change ({R.reflect (left i)} : Finset W) ∆ {R.reflect (right i)} =
    ({left i} : Finset W) ∆ {right i}
  rw [R.reflect_left, R.reflect_right]
  exact (symmDiff_comm ({right i} : Finset W) {left i})


theorem lpReflectSource_ghost
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1) :
    lpReflectSource R (lpMatchingGhostSource g0 g1) =
      lpMatchingGhostSource g0 g1 := by
  rw [lpMatchingGhostSource, lpReflectSource_symmDiff]
  change ({R.reflect g0} : Finset W) ∆ {R.reflect g1} =
    ({g0} : Finset W) ∆ {g1}
  rw [R.reflect_g0, R.reflect_g1]
  exact (symmDiff_comm ({g1} : Finset W) {g0})



theorem lpReflectSource_matchingCommonSource
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1) (i j : I) :
    lpReflectSource R
        (lpMatchingSeamSource left right i ∆
          lpMatchingSeamSource left right j ∆
          lpMatchingGhostSource g0 g1) =
      lpMatchingSeamSource left right i ∆
        lpMatchingSeamSource left right j ∆
        lpMatchingGhostSource g0 g1 := by
  rw [lpReflectSource_symmDiff, lpReflectSource_symmDiff,
    lpReflectSource_seam, lpReflectSource_seam, lpReflectSource_ghost]



theorem lpReflectedMatchingCut_bondEnergy
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {J : Sym2 W -> Real} {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (sigma : ConfigSpace W) :
    (∑ e ∈ G.edgeFinset,
        J e * bond (isingCfgEquiv R.reflect sigma) e) =
      ∑ e ∈ G.edgeFinset, J e * bond sigma e := by
  have hadj : forall x y,
      G.Adj x y <-> G.Adj (R.reflect x) (R.reflect y) :=
    fun x y => (R.adj_iff x y).symm
  have hmapmap : forall e : Sym2 W,
      Sym2.map R.reflect (Sym2.map R.reflect e) = e := by
    intro e
    rw [Sym2.map_map]
    induction e with
    | h x y =>
        simp only [Sym2.map_mk]
        change s(R.reflect (R.reflect x), R.reflect (R.reflect y)) = s(x, y)
        rw [R.involutive x, R.involutive y]
  symm
  apply Finset.sum_bij'
      (i := fun e _ => Sym2.map R.reflect e)
      (j := fun e _ => Sym2.map R.reflect e)
  · intro e he
    exact StatMech.FK.fvs_mem_edgeFinset_map G G R.reflect hadj he
  · intro e he
    exact StatMech.FK.fvs_mem_edgeFinset_map G G R.reflect hadj he
  · intro e he
    exact hmapmap e
  · intro e he
    exact hmapmap e
  · intro e he
    rw [bond_isingCfgEquiv, hmapmap, R.coupling]



theorem lpReflectedMatchingCut_boltzmannJ
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {J : Sym2 W -> Real} {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (beta : Real) (sigma : ConfigSpace W) :
    boltzmannJ G beta J (isingCfgEquiv R.reflect sigma) =
      boltzmannJ G beta J sigma := by
  unfold boltzmannJ
  rw [lpReflectedMatchingCut_bondEnergy R sigma]



theorem lpReflectedMatchingCut_expectationJ
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {J : Sym2 W -> Real} {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (beta : Real) (S : Finset W) :
    expectationJ G beta J (lpReflectSource R S) =
      expectationJ G beta J S := by
  unfold expectationJ
  congr 1
  calc
    (∑ sigma : ConfigSpace W,
        spinProd (lpReflectSource R S) sigma *
          boltzmannJ G beta J sigma) =
      ∑ sigma : ConfigSpace W,
        spinProd S (isingCfgEquiv R.reflect sigma) *
          boltzmannJ G beta J (isingCfgEquiv R.reflect sigma) := by
        apply Finset.sum_congr rfl
        intro sigma _
        rw [spinProd_isingCfgEquiv,
          lpReflectedMatchingCut_boltzmannJ R beta sigma]
        rfl
    _ = ∑ sigma : ConfigSpace W,
        spinProd S sigma * boltzmannJ G beta J sigma :=
      Equiv.sum_comp (isingCfgEquiv R.reflect)
        (fun sigma : ConfigSpace W =>
          spinProd S sigma * boltzmannJ G beta J sigma)




theorem lpReflectedMatchingCut_currentSum
    {G : SimpleGraph W} [DecidableRel G.Adj]
    {J : Sym2 W -> Real} {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (beta : Real) (S : Finset W) :
    currentSum G beta J (lpReflectSource R S) =
      currentSum G beta J S := by
  have h := lpReflectedMatchingCut_expectationJ R beta S
  rw [current_representation, current_representation] at h
  exact (div_left_inj'
    (ne_of_gt (acr_currentSum_empty_pos G beta J))).mp h

end

end StatMech.Ising
