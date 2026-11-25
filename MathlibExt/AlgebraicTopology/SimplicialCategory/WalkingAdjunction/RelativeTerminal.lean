/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.TerminalVertex
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Relative terminal-boundary extension

The full boundary criterion expresses that a vertex is terminal in a
quasicategory. Riehl–Verity, arXiv:1310.8279v4, Lemma 4.3.5, proves its
relative extension property by correcting a chosen source filler across
one larger sphere and then lifting a genuine inner horn. The proof uses
the selected terminal vertex and its selected image; no relative filler
or coherent adjunction extension is supplied as an assumption.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction

/-- The intrinsic full-boundary criterion for a terminal vertex, expressed by
the original last-vertex map. No relative lifting conclusion is part of this predicate. -/
abbrev RightTerminalVertex {X : SSet.{u}} (t : (Δ[0] : SSet.{u}) ⟶ X) : Prop :=
  SSet.IsTerminalVertex t

private def lastVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))

private def lastBoundaryVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  lastVertex n ≫ boundary.ι (0 : Fin (n + 2))

private theorem lastVertex_deltaZero (n : ℕ) :
    lastVertex.{u} n ≫ stdSimplex.δ (0 : Fin (n + 2)) = lastVertex (n + 1) := by
  change stdSimplex.map _ ≫ stdSimplex.map _ = stdSimplex.map _
  rw [← CategoryTheory.Functor.map_comp]
  apply congrArg stdSimplex.map
  ext j
  simp [SimplexCategory.const, SimplexCategory.δ]

private theorem lastVertex_sigmaLast (n : ℕ) :
    lastVertex.{u} (n + 1) ≫ stdSimplex.σ (Fin.last n) = lastVertex n := by
  change stdSimplex.map _ ≫ stdSimplex.map _ = stdSimplex.map _
  rw [← CategoryTheory.Functor.map_comp]
  apply congrArg stdSimplex.map
  ext j
  simp [SimplexCategory.const, SimplexCategory.σ]

private theorem lastBoundaryVertex_inclusion (n : ℕ) :
    lastBoundaryVertex.{u} n ≫ ∂Δ[n + 1].ι = lastVertex (n + 1) := by
  rw [lastBoundaryVertex, Category.assoc, boundary.ι_ι, lastVertex_deltaZero]

private theorem compatible_simplex_faces {B : SSet.{u}} {n : ℕ}
    (d : (Δ[n + 2] : SSet.{u}) ⟶ B) :
    boundary.IsCompatible (fun j : Fin (n + 3) => stdSimplex.δ j ≫ d) := by
  rw [boundary.isCompatible_succ_iff]
  intro j k hjk
  have hf := (boundary.isCompatible_succ_iff _).mp (boundary.ι_isCompatible (n + 1))
  have h := congrArg (fun f => f ≫ ∂Δ[n + 2].ι ≫ d) (hf j k hjk)
  simpa only [Category.assoc, boundary.ι_ι_assoc] using h

private theorem compatible_update {B : SSet.{u}} {n : ℕ}
    {faces : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ B)}
    (hf : boundary.IsCompatible faces) (i : Fin (n + 3))
    (b : (Δ[n + 1] : SSet.{u}) ⟶ B)
    (hb : ∀ j : Fin (n + 2), stdSimplex.δ j ≫ b = stdSimplex.δ j ≫ faces i) :
    boundary.IsCompatible (Function.update faces i b) := by
  rw [boundary.isCompatible_succ_iff] at hf ⊢
  intro j k hjk
  by_cases hji : j = i
  · subst j
    have hki : k ≠ i := ne_of_gt hjk
    simp only [Function.update_self, Function.update_of_ne hki]
    exact (hb _).trans (hf i k hjk)
  · by_cases hki : k = i
    · subst k
      simp only [Function.update_self, Function.update_of_ne hji]
      exact (hf j i hjk).trans (hb _).symm
    · simp only [Function.update_of_ne hji, Function.update_of_ne hki]
      exact hf j k hjk

private theorem critical_boundary_factor (n : ℕ) (j : Fin (n + 2)) :
    ∃ (a : Fin (n + 2)) (b : Fin (n + 3)),
      b ≠ (Fin.last (n + 1)).castSucc ∧
      (stdSimplex.δ j : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]) ≫
          stdSimplex.δ (Fin.last (n + 1)).castSucc = stdSimplex.δ a ≫ stdSimplex.δ b := by
  by_cases hj : j = Fin.last (n + 1)
  · subst j
    refine ⟨Fin.last (n + 1), (Fin.last (n + 1)).succ, ?_, ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
    · exact stdSimplex.δ_comp_δ_self
  · have hv : j.val ≠ n + 1 := by
      intro h
      apply hj
      exact Fin.ext h
    have hlt : j.castSucc < (Fin.last (n + 1)).castSucc := by
      change j.val < n + 1
      have hb := j.isLt
      omega
    refine ⟨((Fin.last (n + 1)).castSucc).pred (by simp), j.castSucc, ne_of_lt hlt, ?_⟩
    exact stdSimplex.δ_comp_δ' hlt

/-- RV's relative terminal-boundary lemma, with an actual constructed diagonal.
Only the chosen terminal vertex and its actual image are needed. Local inner
fibrancy suffices for the final genuine inner-horn lift. -/
theorem exists_relative_terminal_extension {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    (t : (Δ[0] : SSet.{u}) ⟶ E) (ht : RightTerminalVertex t)
    (hpt : RightTerminalVertex (t ≫ p)) (n : ℕ)
    (u₀ : (∂Δ[n + 1] : SSet.{u}) ⟶ E) (v₀ : (Δ[n + 1] : SSet.{u}) ⟶ B)
    (sq : CommSq u₀ ∂Δ[n + 1].ι p v₀)
    (hu : stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) ≫
      boundary.ι (0 : Fin (n + 2)) ≫ u₀ = t) :
    ∃ l : (Δ[n + 1] : SSet.{u}) ⟶ E, ∂Δ[n + 1].ι ≫ l = u₀ ∧ l ≫ p = v₀ := by
  obtain ⟨w, hw⟩ := ht n u₀ hu
  let c : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let d : (Δ[n + 2] : SSet.{u}) ⟶ B := stdSimplex.σ (Fin.last (n + 1)) ≫ w ≫ p
  let faces : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ B) :=
    fun j => stdSimplex.δ j ≫ d
  have hf : boundary.IsCompatible faces := compatible_simplex_faces d
  have hc : faces c = w ≫ p := by
    dsimp only [faces, d, c]
    rw [← Category.assoc, stdSimplex.δ_comp_σ_self, Category.id_comp]
  have hrel : ∂Δ[n + 1].ι ≫ (w ≫ p) = ∂Δ[n + 1].ι ≫ v₀ := by
    rw [← Category.assoc, hw]
    exact sq.w
  have hfaces (j : Fin (n + 2)) : stdSimplex.δ j ≫ v₀ = stdSimplex.δ j ≫ faces c := by
    rw [hc]
    have h := congrArg (fun f => boundary.ι j ≫ f) hrel
    simpa only [Category.assoc, boundary.ι_ι_assoc] using h.symm
  have hf' : boundary.IsCompatible (Function.update faces c v₀) :=
    compatible_update hf c v₀ hfaces
  let h : (∂Δ[n + 2] : SSet.{u}) ⟶ B := hf'.desc
  have hzero : boundary.ι (0 : Fin (n + 3)) ≫ h = faces 0 := by
    dsimp only [h]
    rw [boundary.IsCompatible.ι_desc, Function.update_of_ne]
    intro he
    have hv := congrArg Fin.val he
    dsimp [c] at hv
    omega
  have hwt : lastVertex (n + 1) ≫ w = t := by
    calc
      lastVertex (n + 1) ≫ w = (lastBoundaryVertex n ≫ ∂Δ[n + 1].ι) ≫ w :=
        congrArg (fun f => f ≫ w) (lastBoundaryVertex_inclusion n).symm
      _ = lastBoundaryVertex n ≫ u₀ := by rw [Category.assoc, hw]
      _ = t := (Category.assoc _ _ _).trans hu
  have hlast : lastVertex (n + 1) ≫ boundary.ι (0 : Fin (n + 3)) ≫ h = t ≫ p := by
    rw [hzero]
    change lastVertex (n + 1) ≫ stdSimplex.δ (0 : Fin (n + 3)) ≫
      stdSimplex.σ (Fin.last (n + 1)) ≫ w ≫ p = t ≫ p
    simp only [← Category.assoc, lastVertex_deltaZero, lastVertex_sigmaLast, hwt]
  obtain ⟨k, hk⟩ := hpt (n + 1) h hlast
  let g : (Λ[n + 2, c] : SSet.{u}) ⟶ E :=
    Λ[n + 2, c].ι ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w
  have hs : CommSq g Λ[n + 2, c].ι p k := by
    constructor
    apply horn.hom_ext'
    intro j hj
    simp only [g, Category.assoc, horn.ι_ι_assoc]
    rw [← boundary.ι_ι_assoc j k, hk]
    dsimp only [h]
    rw [boundary.IsCompatible.ι_desc, Function.update_of_ne hj]
  have hpos : 0 < c := by
    change 0 < n + 1
    omega
  have htop : c < Fin.last (n + 2) := by
    change n + 1 < n + 2
    omega
  have : HasLiftingProperty Λ[n + 2, c].ι p :=
    (mem_innerFibrations p) _ (horn_ι_mem_innerHornInclusions hpos htop)
  have hrestrict (j : Fin (n + 3)) (hj : j ≠ c) :
      stdSimplex.δ j ≫ hs.lift = stdSimplex.δ j ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w := by
    calc
      stdSimplex.δ j ≫ hs.lift = horn.ι c j hj ≫ Λ[n + 2, c].ι ≫ hs.lift :=
        (horn.ι_ι_assoc c j hj hs.lift).symm
      _ = horn.ι c j hj ≫ g := by rw [hs.fac_left]
      _ = stdSimplex.δ j ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w := by
        simp only [g, horn.ι_ι_assoc]
  refine ⟨stdSimplex.δ c ≫ hs.lift, ?_, ?_⟩
  · apply boundary.hom_ext
    intro j
    have huj : boundary.ι j ≫ u₀ = stdSimplex.δ j ≫ w := by
      rw [← hw, ← Category.assoc, boundary.ι_ι]
    rw [boundary.ι_ι_assoc, huj]
    obtain ⟨a, b, hb, hfac⟩ := critical_boundary_factor.{u} n j
    calc
      stdSimplex.δ j ≫ stdSimplex.δ c ≫ hs.lift =
          (stdSimplex.δ j ≫ stdSimplex.δ c) ≫ hs.lift := (Category.assoc _ _ _).symm
      _ = (stdSimplex.δ a ≫ stdSimplex.δ b) ≫ hs.lift :=
        congrArg (fun f => f ≫ hs.lift) hfac
      _ = stdSimplex.δ a ≫ stdSimplex.δ b ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w := by
        rw [Category.assoc, hrestrict b hb]
      _ = (stdSimplex.δ j ≫ stdSimplex.δ c) ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w :=
        congrArg (fun f => f ≫ stdSimplex.σ (Fin.last (n + 1)) ≫ w) hfac.symm
      _ = stdSimplex.δ j ≫ w := by
        rw [Category.assoc, ← Category.assoc (stdSimplex.δ c)
          (stdSimplex.σ (Fin.last (n + 1))) w]
        dsimp only [c]
        rw [stdSimplex.δ_comp_σ_self, Category.id_comp]
  · rw [Category.assoc, hs.fac_right, ← boundary.ι_ι_assoc c k, hk]
    dsimp only [h]
    rw [boundary.IsCompatible.ι_desc, Function.update_self]

end SSet.WalkingAdjunction
