/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWBoundaryRLP
public import MathlibExt.AlgebraicTopology.SimplicialSet.PreFibrantSpecialHorn
public import MathlibExt.AlgebraicTopology.SimplicialSet.Remark33

/-!
# Contractible fibers and boundary transposition

This file proves the under-slice transposition of boundary lifting problems
and HTT Lemma 2.1.3.4: a left fibration whose projection over every vertex is
a trivial Kan fibration is itself a trivial Kan fibration. The degree-zero
case uses nonempty fibers. No Kan assumption is imposed on the base.

The proof corrects the back face of a preliminary horn filler using a simplex
in its contractible fiber, then uses induction on the boundary dimension.
The actual mapping-space pullback square supplies the fiber comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite MorphismProperty
open scoped Simplicial

universe u

namespace SSet

variable {X Y S T E B : SSet.{u}}

/-! ### §0. Face-family and vertex helpers -/

/-- The `0`-th vertex is preserved by face maps omitting a
positive vertex: `vertexZeroStd n` followed by
`stdSimplex.δ a.succ` is `vertexZeroStd (n + 1)`. This is
the fact used privately in SliceLeftFibration §3, recorded
here in reusable form. -/
theorem vertexZeroStd_comp_stdSimplex_δ_succ {n : ℕ} (a : Fin (n + 2)) :
    vertexZeroStd n ≫ stdSimplex.δ a.succ = vertexZeroStd (n + 1) := by
  have h1 : (SimplexCategory.δ a.succ).toOrderHom 0 = 0 := by
    change Fin.succAbove a.succ (0 : Fin (n + 2)) = (0 : Fin (n + 3))
    simp [Fin.succAbove]
  rw [stdSimplex_δ_eq_map, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.const_comp, h1]

/-- `vertexZeroStd 0` is the first face inclusion
`δ₁ : Δ[0] ⟶ Δ[1]`. -/
theorem vertexZeroStd_zero :
    vertexZeroStd 0 = stdSimplex.δ (0 : Fin 1).succ := by
  rw [vertexZeroStd, stdSimplex_δ_eq_map]
  congr 2
  ext i
  fin_cases i
  rfl

/-- The codimension-one faces of a standard simplex form a
compatible horn family, for any missing index. -/
theorem horn_isCompatible_of_stdSimplex {n : ℕ}
    (Θ : (Δ[n + 1] : SSet.{u}) ⟶ E) (i : Fin (n + 2)) :
    horn.IsCompatible (i := i) (fun j _ => stdSimplex.δ j ≫ Θ) := by
  obtain _ | m := n
  · simp
  · rw [horn.isCompatible_iff]
    intro j k _ _ hjk
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [Fin.pred_succ, Fin.castPred_castSucc, ← Category.assoc,
      ← Category.assoc,
      CosimplicialObject.δ_comp_δ stdSimplex (show j ≤ k by
        have hjk' := hjk
        simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hjk' ⊢
        omega)]

/-- The codimension-one faces of a standard simplex form a
compatible boundary family. -/
theorem boundary_isCompatible_of_stdSimplex {n : ℕ}
    (Θ : (Δ[n + 1] : SSet.{u}) ⟶ E) :
    boundary.IsCompatible (fun j => stdSimplex.δ j ≫ Θ) := by
  have h := boundary_isCompatible_of_hom ((boundary (n + 1)).ι ≫ Θ)
  simp only [← Category.assoc, boundary.ι_ι] at h
  exact h

/-- The constant vertex map `Δ[0] ⟶ Δ[n]` at vertex `0`,
followed by a face inclusion omitting a positive vertex, is
`vertexZeroStd n`. -/
theorem const_zero_comp_stdSimplex_δ_succ {n : ℕ} (j : Fin (n + 1)) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
        stdSimplex.δ j.succ =
      vertexZeroStd n := by
  have h1 : (SimplexCategory.δ j.succ).toOrderHom 0 = 0 := by
    change Fin.succAbove j.succ (0 : Fin (n + 1)) = (0 : Fin (n + 2))
    simp [Fin.succAbove]
  rw [vertexZeroStd, stdSimplex_δ_eq_map,
    ← CategoryTheory.Functor.map_comp, SimplexCategory.const_comp, h1]

/-! ### §0'. Face and degeneracy identities for `Δ[·]`

The standard-simplex identities the horn correction in §2
consumes, stated in sum-of-successors index form so that
rewrites match the indices produced by the transport of
SliceLeftFibration §2. -/

/-- `δ₀ ≫ σ₁ = σ₀ ≫ δ₀` on standard simplices. -/
private theorem stdSimplex_δ_zero_comp_σ_succ_zero (k : ℕ) :
    stdSimplex.δ (0 : Fin (k + 3)) ≫ stdSimplex.σ (0 : Fin (k + 1)).succ =
      stdSimplex.σ (0 : Fin (k + 1)) ≫ stdSimplex.δ (0 : Fin (k + 2)) := by
  rw [show (0 : Fin (k + 3)) = Fin.castSucc (0 : Fin (k + 2)) from rfl,
    CosimplicialObject.δ_comp_σ_of_le stdSimplex (by simp)]

/-- `δ₁ ≫ σ₁ = 𝟙` on standard simplices. -/
private theorem stdSimplex_δ_succ_zero_comp_σ_succ_zero (k : ℕ) :
    stdSimplex.δ (0 : Fin (k + 2)).succ ≫
        stdSimplex.σ (0 : Fin (k + 1)).succ =
      𝟙 (Δ[k + 1] : SSet.{u}) := by
  rw [show (0 : Fin (k + 2)).succ =
      Fin.castSucc (0 : Fin (k + 1)).succ from rfl,
    CosimplicialObject.δ_comp_σ_self]

/-- `δ₂ ≫ σ₁ = 𝟙` on standard simplices. -/
private theorem stdSimplex_δ_succ_succ_zero_comp_σ_succ_zero (k : ℕ) :
    stdSimplex.δ (0 : Fin (k + 1)).succ.succ ≫
        stdSimplex.σ (0 : Fin (k + 1)).succ =
      𝟙 (Δ[k + 1] : SSet.{u}) :=
  CosimplicialObject.δ_comp_σ_succ stdSimplex

/-- `δ_{c + 2} ≫ σ₀ = σ₀ ≫ δ_{c + 1}` on standard simplices. -/
private theorem stdSimplex_δ_succ_succ_comp_σ_zero (m : ℕ)
    (c : Fin (m + 1)) :
    stdSimplex.δ c.succ.succ ≫ stdSimplex.σ (0 : Fin (m + 2)) =
      stdSimplex.σ (0 : Fin (m + 1)) ≫ stdSimplex.δ c.succ := by
  have h := CosimplicialObject.δ_comp_σ_of_gt' stdSimplex
    (i := c.succ.succ) (j := (0 : Fin (m + 2))) (by
      have h1 : ((0 : Fin (m + 2)).succ).val = 1 := by simp
      have h2 : (c.succ.succ).val = c.val + 2 := by simp
      rw [Fin.lt_def, h1, h2]; omega)
  rwa [Fin.pred_succ] at h

/-- `δ_{c + 3} ≫ σ₁ = σ₁ ≫ δ_{c + 2}` on standard simplices. -/
private theorem stdSimplex_δ_succ_succ_succ_comp_σ_succ_zero (m : ℕ)
    (c : Fin (m + 1)) :
    stdSimplex.δ c.succ.succ.succ ≫ stdSimplex.σ (0 : Fin (m + 2)).succ =
      stdSimplex.σ (0 : Fin (m + 1)).succ ≫ stdSimplex.δ c.succ.succ := by
  have h := CosimplicialObject.δ_comp_σ_of_gt' stdSimplex
    (i := c.succ.succ.succ) (j := (0 : Fin (m + 2)).succ) (by
      have h1 : ((0 : Fin (m + 2)).succ.succ).val = 2 := by simp
      have h2 : (c.succ.succ.succ).val = c.val + 3 := by simp
      rw [Fin.lt_def, h1, h2]; omega)
  rwa [Fin.pred_succ] at h

/-- `δ₀ ≫ δ₁ = δ₀ ≫ δ₀` on standard simplices, in successor
index form. -/
private theorem stdSimplex_δ_zero_comp_δ_succ_zero (k : ℕ) :
    stdSimplex.δ (0 : Fin (k + 2)) ≫ stdSimplex.δ (0 : Fin (k + 2)).succ =
      stdSimplex.δ (0 : Fin (k + 2)) ≫ stdSimplex.δ (0 : Fin (k + 3)) := by
  rw [show (0 : Fin (k + 3)) = Fin.castSucc (0 : Fin (k + 2)) from rfl,
    CosimplicialObject.δ_comp_δ_self]

/-- `δ_a ≫ δ₀ = δ₀ ≫ δ_{a + 1}` on standard simplices. -/
private theorem stdSimplex_δ_comp_δ_zero (k : ℕ) (a : Fin (k + 2)) :
    stdSimplex.δ a ≫ stdSimplex.δ (0 : Fin (k + 3)) =
      stdSimplex.δ (0 : Fin (k + 2)) ≫ stdSimplex.δ a.succ := by
  rw [show (0 : Fin (k + 3)) = Fin.castSucc (0 : Fin (k + 2)) from rfl,
    ← CosimplicialObject.δ_comp_δ stdSimplex
      (show (0 : Fin (k + 2)) ≤ a by simp)]

/-- `δ_last ≫ σ₀ = σ₀ ≫ δ_last` on standard simplices. -/
private theorem stdSimplex_δ_last_comp_σ_zero (m : ℕ) :
    stdSimplex.δ (Fin.last (m + 2)) ≫ stdSimplex.σ (0 : Fin (m + 2)) =
      stdSimplex.σ (0 : Fin (m + 1)) ≫
        stdSimplex.δ (Fin.last (m + 1)) := by
  rw [show Fin.last (m + 2) = (Fin.last (m + 1)).succ from
      (Fin.succ_last (m + 1)).symm,
    show (0 : Fin (m + 2)) = Fin.castSucc (0 : Fin (m + 1)) from rfl]
  exact CosimplicialObject.δ_comp_σ_of_gt stdSimplex
    (show Fin.castSucc (0 : Fin (m + 1)) < Fin.last (m + 1) by
      simp [Fin.lt_def, Fin.val_last])

/-! ### §1. The boundary/slice transposition
(the additional comparison obligation)

Boundary lifting against `p` in dimension `n + 1` from
boundary lifting against every slice comparison map of `p`
in dimension `n`, by the face transport of
SliceLeftFibration §2: this mirrors the proof there (§3)
that `sliceUnderComparison` is a left fibration, which is
the horn-level analogue. -/

/-- **The transposition** (the additional comparison obligation): if
every slice comparison map of `p : X ⟶ S` has the right
lifting property against `(boundary n).ι`, then `p` has
the right lifting property against `(boundary (n + 1)).ι`.
A square against `p` with top map `u` transposes to the
square against `sliceUnderComparison (p := p) x` with
`x = u(0)`, bottom map given by the bottom simplex and the
`0`-th face of `u`, and top map glued from the remaining
faces of `u`. -/
theorem hasLiftingProperty_boundary_succ_of_sliceUnderComparison
    {p : X ⟶ S} {n : ℕ}
    (h : ∀ x : (Δ[0] : SSet.{u}) ⟶ X,
      HasLiftingProperty (boundary n).ι
        (sliceUnderComparison (p := p) x)) :
    HasLiftingProperty (boundary (n + 1)).ι p := by
  refine ⟨?_⟩
  intro top bottom sq
  -- The first face `F1` of `top` and the vertex `x = top(0)`.
  set F1 : (Δ[n] : SSet.{u}) ⟶ X :=
    boundary.ι (0 : Fin (n + 1)).succ ≫ top with hF1
  set x : (Δ[0] : SSet.{u}) ⟶ X :=
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ F1 with hx
  have hcomm : ∀ a : Fin (n + 2), (boundary.ι a ≫ top) ≫ p =
      stdSimplex.δ a ≫ bottom := by
    intro a
    rw [Category.assoc, sq.w, ← Category.assoc, boundary.ι_ι]
  -- Every positive face of `top` has `0`-th vertex `x`.
  have hvtx : ∀ j : Fin (n + 1),
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
          (boundary.ι j.succ ≫ top) = x := by
    intro j
    have hι : SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
          boundary.ι j.succ =
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
          boundary.ι (0 : Fin (n + 1)).succ := by
      rw [← cancel_mono (boundary (n + 1)).ι, Category.assoc,
        boundary.ι_ι, const_zero_comp_stdSimplex_δ_succ,
        Category.assoc, boundary.ι_ι,
        const_zero_comp_stdSimplex_δ_succ]
    calc SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
          (boundary.ι j.succ ≫ top)
        = SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫ F1 := by
          rw [hF1, ← Category.assoc, hι, Category.assoc]
      _ = x := hx.symm
  -- The bottom simplex has `0`-th vertex `x ≫ p`.
  have hP2 : vertexZeroStd n ≫ bottom = x ≫ p := by
    have e1 : vertexZeroStd n ≫ bottom =
        SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) ≫
          (stdSimplex.δ (0 : Fin (n + 1)).succ ≫ bottom) := by
      rw [← Category.assoc, const_zero_comp_stdSimplex_δ_succ]
    rw [e1, ← hcomm (0 : Fin (n + 1)).succ, ← Category.assoc]
  -- The bottom map of the transposed square.
  set sComp : (Δ[n] : SSet.{u}) ⟶ sliceUnder S (x ≫ p) :=
    sliceUnder.ofStdSimplex S (x ≫ p) bottom hP2 with hsComp
  have hsComp_proj : sComp ≫ sliceUnder.proj S (x ≫ p) =
      stdSimplex.δ (0 : Fin (n + 2)) ≫ bottom := by
    rw [hsComp, sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
      sliceUnder.stdSimplexOf_ofStdSimplex]
  set bot' : (Δ[n] : SSet.{u}) ⟶
      pullback (sliceUnder.proj S (x ≫ p)) p :=
    pullback.lift sComp (boundary.ι (0 : Fin (n + 2)) ≫ top)
      (hsComp_proj.trans (hcomm (0 : Fin (n + 2))).symm) with hbot'
  have hbot'fst : bot' ≫ pullback.fst (sliceUnder.proj S (x ≫ p)) p =
      sComp :=
    pullback.lift_fst _ _ _
  have hbot'snd : bot' ≫ pullback.snd (sliceUnder.proj S (x ≫ p)) p =
      boundary.ι (0 : Fin (n + 2)) ≫ top :=
    pullback.lift_snd _ _ _
  by_cases hn : n = 0
  · -- Dimension `0`: the transposed top map is out of `∂Δ[0]`.
    subst hn
    have hxF1 : x = F1 := by
      rw [hx]
      have hcc : SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) =
          𝟙 (Δ[0] : SSet.{u}) :=
        (toDeltaZero_eq _).trans (toDeltaZero_eq _).symm
      rw [hcc, Category.id_comp]
    have hinit : IsInitial
        ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) :=
      (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso boundary_zero).symm
    set top' := hinit.to (sliceUnder X x) with htop'
    have := h x
    set sq' : CommSq top' (boundary 0).ι
        (sliceUnderComparison (p := p) x) bot' :=
      ⟨boundary.hom_ext₀⟩ with hsq'
    set L : (Δ[1] : SSet.{u}) ⟶ X :=
      sliceUnder.stdSimplexOf X x sq'.lift with hL
    refine ⟨⟨CommSq.LiftStruct.mk L ?_ ?_⟩⟩
    · apply boundary.hom_ext
      intro a
      by_cases ha : a = 0
      · subst ha
        rw [← Category.assoc, boundary.ι_ι, hL,
          ← sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
          ← sliceUnderComparison_snd (p := p) x, ← Category.assoc,
          sq'.fac_right, hbot'snd]
      · obtain ⟨j, rfl⟩ := a.eq_succ_of_ne_zero ha
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        rw [← Category.assoc, boundary.ι_ι,
          show (0 : Fin (0 + 1)).succ = (0 : Fin 1).succ from rfl,
          ← vertexZeroStd_zero, hL, sliceUnder.stdSimplexOf_vertex]
        exact hxF1.trans hF1
    · calc L ≫ p
          = sliceUnder.stdSimplexOf S (x ≫ p)
              (sq'.lift ≫ sliceUnder.map X x p) := by
            rw [hL, ← sliceUnder.stdSimplexOf_map]
        _ = bottom := by
            have hmap : sq'.lift ≫ sliceUnder.map X x p = sComp := by
              rw [← sliceUnderComparison_fst (p := p) x,
                ← Category.assoc, sq'.fac_right, hbot'fst]
            rw [hmap, hsComp, sliceUnder.stdSimplexOf_ofStdSimplex]
  · -- Dimension `m + 1`: the transposed top map is glued
    -- from the positive faces of `top`.
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hP1 : ∀ j : Fin (m + 2),
        vertexZeroStd m ≫ (boundary.ι j.succ ≫ top) = x :=
      fun j => hvtx j
    set faces : Fin (m + 2) → ((Δ[m] : SSet.{u}) ⟶ sliceUnder X x) :=
      fun j => sliceUnder.ofStdSimplex X x (boundary.ι j.succ ≫ top)
        (hP1 j) with hfaces
    have hfaces_std : ∀ j : Fin (m + 2),
        sliceUnder.stdSimplexOf X x (faces j) =
          boundary.ι j.succ ≫ top :=
      fun j => sliceUnder.stdSimplexOf_ofStdSimplex X x _ _
    have hfX : boundary.IsCompatible
        (fun a : Fin (m + 3) => boundary.ι a ≫ top) :=
      boundary_isCompatible_of_hom top
    rw [boundary.isCompatible_succ_iff] at hfX
    have hcompat : boundary.IsCompatible faces := by
      by_cases hm : m = 0
      · subst hm
        trivial
      · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        rw [boundary.isCompatible_succ_iff]
        intro j k hjk
        apply sliceUnder.ext_of_stdSimplexOf_eq X x
        rw [sliceUnder.stdSimplexOf_δ, sliceUnder.stdSimplexOf_δ,
          hfaces_std, hfaces_std]
        have e1 : (k.pred (Fin.ne_zero_of_lt hjk)).succ = k :=
          Fin.succ_pred k _
        have hlt : j.succ < k.succ := by
          rw [Fin.lt_def] at hjk ⊢
          simp only [Fin.val_succ] at hjk ⊢
          omega
        have e2 : (j.castPred (Fin.ne_last_of_lt hjk)).succ =
            (j.succ).castPred
              (Fin.ne_last_of_lt (hlt.trans_le (Fin.le_last _))) :=
          (Fin.ext (by simp [Fin.coe_castPred])).symm
        rw [e1, e2]
        have hfx := hfX (j.succ) (k.succ) hlt
        rwa [Fin.pred_succ] at hfx
    set top' := hcompat.desc with htop'
    have := h x
    have hsq'w : top' ≫ sliceUnderComparison (p := p) x =
        (boundary (m + 1)).ι ≫ bot' := by
      apply pullback.hom_ext
      · calc (top' ≫ sliceUnderComparison (p := p) x) ≫
              pullback.fst (sliceUnder.proj S (x ≫ p)) p
            = top' ≫ sliceUnder.map X x p := by
              simp only [Category.assoc, sliceUnderComparison_fst]
          _ = ((boundary (m + 1)).ι ≫ bot') ≫
              pullback.fst (sliceUnder.proj S (x ≫ p)) p := by
              simp only [Category.assoc, hbot'fst]
              apply boundary.hom_ext
              intro j
              rw [← Category.assoc, ← Category.assoc, htop',
                boundary.IsCompatible.ι_desc, boundary.ι_ι]
              apply sliceUnder.ext_of_stdSimplexOf_eq S (x ≫ p)
              rw [sliceUnder.stdSimplexOf_map, hfaces_std,
                sliceUnder.stdSimplexOf_δ, hsComp,
                sliceUnder.stdSimplexOf_ofStdSimplex]
              exact hcomm j.succ
      · calc (top' ≫ sliceUnderComparison (p := p) x) ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p
            = top' ≫ sliceUnder.proj X x := by
              rw [Category.assoc, sliceUnderComparison_snd]
          _ = ((boundary (m + 1)).ι ≫ bot') ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p := by
              rw [Category.assoc, hbot'snd]
              apply boundary.hom_ext
              intro j
              rw [← Category.assoc, ← Category.assoc, htop',
                boundary.IsCompatible.ι_desc, boundary.ι_ι,
                sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf, hfaces_std]
              have hlt0 : (0 : Fin (m + 3)) < j.succ := by
                rw [Fin.lt_def]; simp
              have hfx := hfX 0 j.succ hlt0
              rw [Fin.pred_succ] at hfx
              have e0 : (0 : Fin (m + 3)).castPred
                    (Fin.ne_last_of_lt hlt0) =
                  (0 : Fin (m + 2)) :=
                Fin.ext (by simp)
              rw [e0] at hfx
              exact hfx.symm
    set sq' : CommSq top' (boundary (m + 1)).ι
        (sliceUnderComparison (p := p) x) bot' := ⟨hsq'w⟩ with hsq'
    set L : (Δ[m + 2] : SSet.{u}) ⟶ X :=
      sliceUnder.stdSimplexOf X x sq'.lift with hL
    refine ⟨⟨CommSq.LiftStruct.mk L ?_ ?_⟩⟩
    · apply boundary.hom_ext
      intro a
      by_cases ha : a = 0
      · subst ha
        rw [← Category.assoc, boundary.ι_ι, hL,
          ← sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
          ← sliceUnderComparison_snd (p := p) x, ← Category.assoc,
          sq'.fac_right, hbot'snd]
      · obtain ⟨j, rfl⟩ := a.eq_succ_of_ne_zero ha
        rw [← Category.assoc, boundary.ι_ι, hL,
          ← sliceUnder.stdSimplexOf_δ, ← boundary.ι_ι, Category.assoc,
          sq'.fac_left, htop', boundary.IsCompatible.ι_desc, hfaces_std]
    · calc L ≫ p
          = sliceUnder.stdSimplexOf S (x ≫ p)
              (sq'.lift ≫ sliceUnder.map X x p) := by
            rw [hL, ← sliceUnder.stdSimplexOf_map]
        _ = bottom := by
            have hmap : sq'.lift ≫ sliceUnder.map X x p = sComp := by
              rw [← sliceUnderComparison_fst (p := p) x,
                ← Category.assoc, sq'.fac_right, hbot'fst]
            rw [hmap, hsComp, sliceUnder.stdSimplexOf_ofStdSimplex]

/-! ### §2. The mapping-space correction and Lemma A

The heart of the additional comparison obligation: a left fibration with
trivial fibers induces trivial Kan fibrations on naive
mapping spaces. The private correction lemma below is the
`Ψ`/`Σ` gluing of SliceLeftFibration (2b): an inner horn
`Λ[k + 2, 1]` whose `0`-th face is a fiber simplex joining
the back face of `Σ` to the constant simplex corrects the
back face of the `1`-st face of its filler to be constant. -/

/-- **The correction step**: given `Sigma0 : Δ[k + 1] ⟶ E` over
`Tb` with `0`-th vertex `x`, whose back face `δ₀Sigma0` lifts
to the fiber over `y ≫ q` through `φ'` with constant
boundary (the hypothesis `hφcompat`), there is another
simplex `Sigma1` over `Tb` with the same vertex, the same
positive faces as `Sigma0`, and constant back face at `y`. -/
private theorem exists_simplex_with_const_backFace {q : E ⟶ B}
    [LeftFibration q]
    (hFib : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      modelCategoryQuillen.I.rlp (pullback.snd q b))
    {x y : (Δ[0] : SSet.{u}) ⟶ E} {k : ℕ}
    {Tb : (Δ[k + 1] : SSet.{u}) ⟶ B} {Sigma0 : (Δ[k + 1] : SSet.{u}) ⟶ E}
    (hSigmaq : Sigma0 ≫ q = Tb) (hSigmav : vertexZeroStd k ≫ Sigma0 = x)
    (hTb : stdSimplex.δ (0 : Fin (k + 2)) ≫ Tb =
      toDeltaZero (Δ[k] : SSet.{u}) ≫ (y ≫ q))
    (φ' : (Δ[k] : SSet.{u}) ⟶ pullback q (y ≫ q))
    (hφ' : φ' ≫ pullback.fst q (y ≫ q) =
      stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma0)
    (ŷ : (Δ[0] : SSet.{u}) ⟶ pullback q (y ≫ q))
    (hŷ : ŷ ≫ pullback.fst q (y ≫ q) = y)
    (hφcompat : boundary.IsCompatible
      (fun j : Fin (k + 2) =>
        if j = (0 : Fin (k + 1)).succ then φ'
        else toDeltaZero (Δ[k] : SSet.{u}) ≫ ŷ)) :
    ∃ Sigma1 : (Δ[k + 1] : SSet.{u}) ⟶ E,
      Sigma1 ≫ q = Tb ∧ vertexZeroStd k ≫ Sigma1 = x ∧
        stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma1 =
          toDeltaZero (Δ[k] : SSet.{u}) ≫ y ∧
        ∀ a : Fin (k + 1),
          stdSimplex.δ a.succ ≫ Sigma1 = stdSimplex.δ a.succ ≫ Sigma0 := by
  -- The joining simplex `Ψ'` in the fiber, and `Ψ` in `E`.
  obtain ⟨Ψ', hΨ'faces, hΨ'snd⟩ := exists_simplex_lift_boundary hφcompat
    (hFib (y ≫ q) _ (modelCategoryQuillen.boundary_ι_mem_I (k + 1)))
    (toDeltaZero (Δ[k + 1] : SSet.{u}))
    (fun _ => (toDeltaZero_eq _).trans (toDeltaZero_eq _).symm)
  set Ψ : (Δ[k + 1] : SSet.{u}) ⟶ E :=
    Ψ' ≫ pullback.fst q (y ≫ q) with hΨ
  have hΨ'face : ∀ j : Fin (k + 2),
      stdSimplex.δ j ≫ Ψ' =
        if j = (0 : Fin (k + 1)).succ then φ'
        else toDeltaZero (Δ[k] : SSet.{u}) ≫ ŷ :=
    fun j => hΨ'faces j
  have hΨface : ∀ j : Fin (k + 2),
      stdSimplex.δ j ≫ Ψ =
        if j = (0 : Fin (k + 1)).succ then
          stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma0
        else toDeltaZero (Δ[k] : SSet.{u}) ≫ y := by
    intro j
    rw [hΨ, ← Category.assoc, hΨ'face]
    by_cases hj : j = (0 : Fin (k + 1)).succ
    · rw [ite_eq_left hj, ite_eq_left hj, hφ']
    · rw [ite_eq_right hj, ite_eq_right hj, Category.assoc, hŷ]
  have hΨq : Ψ ≫ q = toDeltaZero (Δ[k + 1] : SSet.{u}) ≫ (y ≫ q) := by
    rw [hΨ, Category.assoc, pullback.condition, ← Category.assoc, hΨ'snd]
  -- The degenerate simplex `Θ = σ₁Sigma0`.
  set Θ : (Δ[k + 2] : SSet.{u}) ⟶ E :=
    stdSimplex.σ (0 : Fin (k + 1)).succ ≫ Sigma0 with hΘ
  have hΘ0 : stdSimplex.δ (0 : Fin (k + 3)) ≫ Θ =
      stdSimplex.σ (0 : Fin (k + 1)) ≫
        (stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma0) := by
    rw [hΘ, ← Category.assoc, stdSimplex_δ_zero_comp_σ_succ_zero,
      Category.assoc]
  have hΘq : Θ ≫ q = stdSimplex.σ (0 : Fin (k + 1)).succ ≫ Tb := by
    rw [hΘ, Category.assoc, hSigmaq]
  -- The inner horn `Λ[k + 2, 1]` family.
  set fam : ∀ (j : Fin (k + 3)) (_ : j ≠ (0 : Fin (k + 2)).succ),
      (Δ[k + 1] : SSet.{u}) ⟶ E :=
    fun j _ => if j = 0 then Ψ else stdSimplex.δ j ≫ Θ with hfam
  have hcompatΩ : horn.IsCompatible fam := by
    rw [horn.isCompatible_iff]
    intro j v hj hv hjv
    by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨b, rfl⟩ := v.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjv)
      have hb0 : b ≠ 0 := fun hb => hv (by rw [hb])
      have hf0 : fam (0 : Fin (k + 3)) hj = Ψ := ite_eq_left rfl
      have hfv : fam b.succ hv = stdSimplex.δ b.succ ≫ Θ :=
        ite_eq_right (Fin.succ_ne_zero b)
      have e0 : (0 : Fin (k + 3)).castPred (Fin.ne_last_of_lt hjv) =
          (0 : Fin (k + 2)) :=
        Fin.ext (by simp)
      have eδ : stdSimplex.δ (0 : Fin (k + 2)) ≫ stdSimplex.δ b.succ =
          stdSimplex.δ b ≫ stdSimplex.δ (0 : Fin (k + 3)) := by
        rw [show (0 : Fin (k + 3)) = Fin.castSucc (0 : Fin (k + 2))
            from rfl,
          CosimplicialObject.δ_comp_δ stdSimplex (by simp)]
      rw [Fin.pred_succ, e0, hf0, hfv]
      have hmain : stdSimplex.δ b ≫ Ψ =
          stdSimplex.δ b ≫ (stdSimplex.σ (0 : Fin (k + 1)) ≫
            (stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma0)) := by
        by_cases hb1 : b = (0 : Fin (k + 1)).succ
        · subst hb1
          rw [hΨface, ite_eq_left rfl, ← Category.assoc,
            CosimplicialObject.δ_comp_σ_succ, Category.id_comp]
        · obtain ⟨d, rfl⟩ := b.eq_succ_of_ne_zero hb0
          have hd : d ≠ 0 := fun hd0 => hb1 (by rw [hd0])
          obtain ⟨e, rfl⟩ := d.eq_succ_of_ne_zero hd
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (show k ≠ 0 from fun hk0 => by subst hk0; exact Fin.elim0 e)
          have hface : stdSimplex.δ e.succ ≫
                (stdSimplex.δ (0 : Fin (m + 3)) ≫ Sigma0) =
              toDeltaZero (Δ[m] : SSet.{u}) ≫ y := by
            have hfc := hφcompat
            rw [boundary.isCompatible_succ_iff] at hfc
            have hlt : (0 : Fin (m + 2)).succ < e.succ.succ := by
              have h1 : ((0 : Fin (m + 2)).succ).val = 1 := by simp
              have h2 : (e.succ.succ).val = e.val + 2 := by simp
              rw [Fin.lt_def, h1, h2]; omega
            have h := hfc ((0 : Fin (m + 2)).succ) (e.succ.succ) hlt
            rw [Fin.pred_succ] at h
            have hne : e.succ.succ ≠ (0 : Fin (m + 2)).succ := fun hcon => by
              have hv := congrArg Fin.val hcon
              rw [show (e.succ.succ).val = e.val + 2 by simp,
                show ((0 : Fin (m + 2)).succ).val = 1 by simp] at hv
              omega
            simp only [ite_true, hne, ite_false] at h
            have hcst : ∀ (a : Fin (m + 2)),
                stdSimplex.δ a ≫
                    (toDeltaZero (Δ[m + 1] : SSet.{u}) ≫ ŷ) =
                  toDeltaZero (Δ[m] : SSet.{u}) ≫ ŷ :=
              fun a => by
                rw [← Category.assoc,
                  toDeltaZero_eq (stdSimplex.δ a ≫ toDeltaZero _)]
            rw [hcst] at h
            have h2 := congrArg
              (fun f => f ≫ pullback.fst q (y ≫ q)) h
            rwa [Category.assoc, hφ', Category.assoc, hŷ] at h2
          rw [hΨface, ite_eq_right hb1, ← Category.assoc,
            stdSimplex_δ_succ_succ_comp_σ_zero, Category.assoc, hface,
            ← Category.assoc,
            toDeltaZero_eq (stdSimplex.σ (0 : Fin (m + 1)) ≫
              toDeltaZero (Δ[m] : SSet.{u}))]
      rw [hmain, ← hΘ0, ← Category.assoc, ← eδ, Category.assoc]
    · have hv0 : v ≠ 0 := Fin.ne_zero_of_lt hjv
      have hfj : fam j hj = stdSimplex.δ j ≫ Θ := ite_eq_right hj0
      have hfv : fam v hv = stdSimplex.δ v ≫ Θ := ite_eq_right hv0
      rw [hfj, hfv]
      exact (horn_isCompatible_of_stdSimplex Θ
        ((0 : Fin (k + 2)).succ)).δ_pred_comp j v hj hv hjv
  -- Fill the inner horn against `q`.
  obtain ⟨Ω, hΩfaces, hΩq⟩ := exists_simplex_lift_horn hcompatΩ
    (innerFibration_hasLiftingProperty_horn (p := q)
      (Fin.succ_pos (0 : Fin (k + 2)))
      (by
        have h1 : ((0 : Fin (k + 2)).succ).val = 1 := by simp
        rw [Fin.lt_def, h1, Fin.val_last]; omega))
    (stdSimplex.σ (0 : Fin (k + 1)).succ ≫ Tb) (by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have hf0 : fam (0 : Fin (k + 3)) hj = Ψ := ite_eq_left rfl
        have hR : stdSimplex.δ (0 : Fin (k + 3)) ≫
              (stdSimplex.σ (0 : Fin (k + 1)).succ ≫ Tb) =
            toDeltaZero (Δ[k + 1] : SSet.{u}) ≫ (y ≫ q) := by
          rw [← Category.assoc, stdSimplex_δ_zero_comp_σ_succ_zero,
            Category.assoc, hTb, ← Category.assoc,
            toDeltaZero_eq (stdSimplex.σ (0 : Fin (k + 1)) ≫
              toDeltaZero (Δ[k] : SSet.{u}))]
        rw [hf0, hΨq]
        exact hR.symm
      · have hfj : fam j hj = stdSimplex.δ j ≫ Θ := ite_eq_right hj0
        rw [hfj, Category.assoc, hΘq, ← Category.assoc])
  have hΩ2 : stdSimplex.δ (0 : Fin (k + 1)).succ.succ ≫ Ω = Sigma0 := by
    have hne : (0 : Fin (k + 1)).succ.succ ≠ (0 : Fin (k + 2)).succ := by
      intro hcon
      have hv := congrArg Fin.val hcon
      rw [show ((0 : Fin (k + 1)).succ.succ).val = 2 by simp,
        show ((0 : Fin (k + 2)).succ).val = 1 by simp] at hv
      omega
    have hfj : fam ((0 : Fin (k + 1)).succ.succ) hne =
        stdSimplex.δ (0 : Fin (k + 1)).succ.succ ≫ Θ :=
      ite_eq_right (Fin.succ_ne_zero _)
    rw [hΩfaces _ hne, hfj, hΘ, ← Category.assoc,
      stdSimplex_δ_succ_succ_zero_comp_σ_succ_zero, Category.id_comp]
  -- The corrected simplex is the `1`-st face of `Ω`.
  set Sigma1 : (Δ[k + 1] : SSet.{u}) ⟶ E :=
    stdSimplex.δ (0 : Fin (k + 2)).succ ≫ Ω with hSigma1
  have hSigma1q : Sigma1 ≫ q = Tb := by
    rw [hSigma1, Category.assoc, hΩq, ← Category.assoc,
      stdSimplex_δ_succ_zero_comp_σ_succ_zero, Category.id_comp]
  have hSigma10 : stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma1 =
      toDeltaZero (Δ[k] : SSet.{u}) ≫ y := by
    have hf0 : fam (0 : Fin (k + 3))
        ((Fin.succ_ne_zero (0 : Fin (k + 2))).symm) = Ψ :=
      ite_eq_left rfl
    calc stdSimplex.δ (0 : Fin (k + 2)) ≫ Sigma1
        = stdSimplex.δ (0 : Fin (k + 2)) ≫
            (stdSimplex.δ (0 : Fin (k + 3)) ≫ Ω) := by
          rw [hSigma1, ← Category.assoc, stdSimplex_δ_zero_comp_δ_succ_zero,
            Category.assoc]
      _ = toDeltaZero (Δ[k] : SSet.{u}) ≫ y := by
          rw [hΩfaces (0 : Fin (k + 3)) (Fin.succ_ne_zero _).symm, hf0,
            hΨface, ite_eq_right (Fin.succ_ne_zero (0 : Fin (k + 1))).symm]
  have hSigma1v : vertexZeroStd k ≫ Sigma1 = x := by
    have e1 : vertexZeroStd k ≫ Sigma1 = vertexZeroStd (k + 1) ≫ Ω := by
      rw [hSigma1, ← Category.assoc, vertexZeroStd_comp_stdSimplex_δ_succ]
    have e2 : vertexZeroStd (k + 1) ≫ Ω =
        vertexZeroStd k ≫
          (stdSimplex.δ (0 : Fin (k + 1)).succ.succ ≫ Ω) := by
      rw [← vertexZeroStd_comp_stdSimplex_δ_succ ((0 : Fin (k + 1)).succ),
        Category.assoc]
    rw [e1, e2, hΩ2, hSigmav]
  have hSigma1faces : ∀ a : Fin (k + 1),
      stdSimplex.δ a.succ ≫ Sigma1 = stdSimplex.δ a.succ ≫ Sigma0 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      have eδδ : stdSimplex.δ (0 : Fin (k + 1)).succ ≫
            stdSimplex.δ (0 : Fin (k + 2)).succ =
          stdSimplex.δ (0 : Fin (k + 1)).succ ≫
            stdSimplex.δ (0 : Fin (k + 1)).succ.succ := by
        rw [show (0 : Fin (k + 2)).succ =
            Fin.castSucc (0 : Fin (k + 1)).succ from rfl,
          CosimplicialObject.δ_comp_δ_self]
      rw [hSigma1, ← Category.assoc, eδδ, Category.assoc, hΩ2]
    · obtain ⟨c, rfl⟩ := a.eq_succ_of_ne_zero ha
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (show k ≠ 0 from fun hk0 => by subst hk0; exact Fin.elim0 c)
      have eδδ : stdSimplex.δ c.succ.succ ≫
            stdSimplex.δ (0 : Fin (m + 3)).succ =
          stdSimplex.δ (0 : Fin (m + 2)).succ ≫
            stdSimplex.δ c.succ.succ.succ := by
        rw [show (0 : Fin (m + 3)).succ =
            Fin.castSucc (0 : Fin (m + 2)).succ from rfl]
        exact (CosimplicialObject.δ_comp_δ stdSimplex
          (i := (0 : Fin (m + 2)).succ) (j := c.succ.succ) (by
            have h1 : ((0 : Fin (m + 2)).succ).val = 1 := by simp
            have h2 : (c.succ.succ).val = c.val + 2 := by simp
            rw [Fin.le_def, h1, h2]; omega)).symm
      have hne : c.succ.succ.succ ≠ (0 : Fin (m + 3)).succ := by
        intro hcon
        have hv := congrArg Fin.val hcon
        rw [show (c.succ.succ.succ).val = c.val + 3 by simp,
          show ((0 : Fin (m + 3)).succ).val = 1 by simp] at hv
        omega
      have hfj : fam c.succ.succ.succ hne =
          stdSimplex.δ c.succ.succ.succ ≫ Θ :=
        ite_eq_right (Fin.succ_ne_zero _)
      have hmid : stdSimplex.δ c.succ.succ.succ ≫ Θ =
          stdSimplex.σ (0 : Fin (m + 1)).succ ≫
            (stdSimplex.δ c.succ.succ ≫ Sigma0) := by
        rw [hΘ, ← Category.assoc,
          stdSimplex_δ_succ_succ_succ_comp_σ_succ_zero, Category.assoc]
      rw [hSigma1, ← Category.assoc, eδδ, Category.assoc,
        hΩfaces _ hne, hfj, hmid, ← Category.assoc,
        stdSimplex_δ_succ_zero_comp_σ_succ_zero, Category.id_comp]
  exact ⟨Sigma1, hSigma1q, hSigma1v, hSigma10, hSigma1faces⟩

/-- **Lemma A**: a left fibration whose fibers over vertices
are trivial Kan fibrations to the point induces trivial Kan
fibrations on all naive left mapping spaces. The boundary
problem transposes to a left horn `Λ[k + 1, 0]` against
`q`, and the correction lemma fixes its back face. -/
theorem mappingSpaceLeftTrivialFibration_of_leftFibration_of_fibers
    {q : E ⟶ B} [LeftFibration q]
    (hFib : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      modelCategoryQuillen.I.rlp (pullback.snd q b)) :
    MappingSpaceLeftTrivialFibration q := by
  intro x y
  rw [modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary]
  intro k
  refine ⟨?_⟩
  intro top bottom sq
  set ŷ : (Δ[0] : SSet.{u}) ⟶ pullback q (y ≫ q) :=
    pullback.lift y (𝟙 (Δ[0] : SSet.{u})) (by simp) with hŷdef
  have hŷ : ŷ ≫ pullback.fst q (y ≫ q) = y := pullback.lift_fst _ _ _
  set Tb : (Δ[k + 1] : SSet.{u}) ⟶ B :=
    mappingSpaceLeft.stdSimplexOf B (x ≫ q) (y ≫ q) bottom with hTbdef
  have hTb : stdSimplex.δ (0 : Fin (k + 2)) ≫ Tb =
      toDeltaZero (Δ[k] : SSet.{u}) ≫ (y ≫ q) :=
    mappingSpaceLeft.stdSimplexOf_back B (x ≫ q) (y ≫ q) bottom
  by_cases hk : k = 0
  · subst hk
    obtain ⟨Sigma0, hSigmafaces, hSigmaq⟩ := exists_simplex_lift_horn
      (n := 0) (i := (0 : Fin 2)) (f := fun _ _ => x)
      ((horn.isCompatible_zero_iff_true _).mpr trivial)
      (LeftFibration.hasLiftingProperty_horn (p := q) (by decide))
      Tb (by
        intro j hj
        have hj1 : j = (0 : Fin 1).succ := by
          apply Fin.ext
          have h0 : j.val ≠ 0 := fun hv => hj (Fin.ext (by simp [hv]))
          have hlt := j.is_lt
          have hz : ((0 : Fin 1).succ).val = 1 := by simp
          rw [hz]
          omega
        subst hj1
        rw [← vertexZeroStd_zero]
        exact (mappingSpaceLeft.stdSimplexOf_vertex B (x ≫ q) (y ≫ q)
          bottom).symm)
    have hSigmav : vertexZeroStd 0 ≫ Sigma0 = x := by
      rw [vertexZeroStd_zero]
      exact hSigmafaces (0 : Fin 1).succ (Fin.succ_ne_zero _)
    set φ' : (Δ[0] : SSet.{u}) ⟶ pullback q (y ≫ q) :=
      pullback.lift (stdSimplex.δ (0 : Fin (0 + 2)) ≫ Sigma0)
        (toDeltaZero (Δ[0] : SSet.{u}))
        (by rw [Category.assoc, hSigmaq]; exact hTb) with hφ'def
    have hφ' : φ' ≫ pullback.fst q (y ≫ q) =
        stdSimplex.δ (0 : Fin (0 + 2)) ≫ Sigma0 :=
      pullback.lift_fst _ _ _
    have hφcompat : boundary.IsCompatible
        (fun j : Fin (0 + 2) =>
          if j = (0 : Fin (0 + 1)).succ then φ'
          else toDeltaZero (Δ[0] : SSet.{u}) ≫ ŷ) :=
      (boundary.isCompatible_zero_iff_true _).mpr trivial
    obtain ⟨Sigma1, hS1q, hS1v, hS10, -⟩ :=
      exists_simplex_with_const_backFace hFib hSigmaq hSigmav hTb φ'
        hφ' ŷ hŷ hφcompat
    set lift : (Δ[0] : SSet.{u}) ⟶ mappingSpaceLeft E x y :=
      mappingSpaceLeft.ofStdSimplex E x y Sigma1 hS1v hS10 with hlift
    refine ⟨⟨CommSq.LiftStruct.mk lift ?_ ?_⟩⟩
    · exact boundary.hom_ext₀
    · apply mappingSpaceLeft.ext_of_stdSimplexOf_eq B (x ≫ q) (y ≫ q)
      rw [hlift, mappingSpaceLeft.stdSimplexOf_map,
        mappingSpaceLeft.stdSimplexOf_ofStdSimplex, hS1q, hTbdef]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    set G : Fin (m + 2) → ((Δ[m + 1] : SSet.{u}) ⟶ E) :=
      fun a => mappingSpaceLeft.stdSimplexOf E x y
        (boundary.ι a ≫ top) with hG
    set fam : ∀ (j : Fin (m + 3)) (_ : j ≠ (0 : Fin (m + 3))),
        (Δ[m + 1] : SSet.{u}) ⟶ E :=
      fun j hj => G (j.pred hj) with hfam
    have hfTop : boundary.IsCompatible
        (fun a : Fin (m + 2) => boundary.ι a ≫ top) :=
      boundary_isCompatible_of_hom top
    have hcompat : horn.IsCompatible fam := by
      by_cases hm : m = 0
      · subst hm
        rw [horn.isCompatible_iff]
        intro j v hj hv hjv
        obtain ⟨a, rfl⟩ := j.eq_succ_of_ne_zero hj
        obtain ⟨b, rfl⟩ := v.eq_succ_of_ne_zero hv
        have hab : a < b := by
          have h2 := hjv
          simp only [Fin.lt_def, Fin.val_succ] at h2 ⊢
          omega
        have ha0 : a = (0 : Fin (0 + 2)) := by
          apply Fin.ext
          have hb2 := b.is_lt
          have hz : (0 : Fin (0 + 2)).val = 0 := by simp
          rw [hz]
          omega
        have hb1 : b = (0 : Fin (0 + 1)).succ := by
          apply Fin.ext
          have hb2 := b.is_lt
          have hz : ((0 : Fin (0 + 1)).succ).val = 1 := by simp
          have ha0v : a.val = 0 := by
            have h := congrArg Fin.val ha0
            simpa using h
          rw [hz]
          omega
        subst ha0
        subst hb1
        rw [Fin.pred_succ]
        have hf1 : fam (0 : Fin (0 + 2)).succ hj = G 0 := by
          change G (((0 : Fin (0 + 2)).succ).pred _) = G 0
          rw [Fin.pred_succ]
        have hf2 : fam (0 : Fin (0 + 1)).succ.succ hv =
            G (0 : Fin (0 + 1)).succ := by
          change G (((0 : Fin (0 + 1)).succ).succ.pred _) =
            G (0 : Fin (0 + 1)).succ
          rw [Fin.pred_succ]
        rw [hf1, hf2]
        have e1 : ((0 : Fin (0 + 2)).succ).castPred
              (Fin.ne_last_of_lt hjv) =
            (0 : Fin (0 + 1)).succ :=
          Fin.ext (by simp)
        rw [e1, ← vertexZeroStd_zero]
        exact (mappingSpaceLeft.stdSimplexOf_vertex E x y _).trans
          (mappingSpaceLeft.stdSimplexOf_vertex E x y _).symm
      · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
        rw [boundary.isCompatible_succ_iff] at hfTop
        rw [horn.isCompatible_iff]
        intro j v hj hv hjv
        obtain ⟨a, rfl⟩ := j.eq_succ_of_ne_zero hj
        obtain ⟨b, rfl⟩ := v.eq_succ_of_ne_zero hv
        have hab : a < b := by
          have h2 := hjv
          simp only [Fin.lt_def, Fin.val_succ] at h2 ⊢
          omega
        have hf1 : fam a.succ hj = G a := by
          change G (a.succ.pred _) = G a
          rw [Fin.pred_succ]
        have hf2 : fam b.succ hv = G b := by
          change G (b.succ.pred _) = G b
          rw [Fin.pred_succ]
        rw [Fin.pred_succ, hf1, hf2]
        obtain ⟨d, rfl⟩ := b.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hab)
        have halt : a < Fin.last (l + 2) := by
          have hd := d.is_lt
          rw [Fin.lt_def] at hab ⊢
          simp only [Fin.val_succ, Fin.val_last] at hab ⊢
          omega
        have e2 : (a.succ).castPred (Fin.ne_last_of_lt hjv) =
            (a.castPred (Fin.ne_last_of_lt halt)).succ :=
          Fin.ext (by simp [Fin.coe_castPred])
        rw [e2]
        change stdSimplex.δ d.succ ≫
              mappingSpaceLeft.stdSimplexOf E x y (boundary.ι a ≫ top) =
            stdSimplex.δ (a.castPred (Fin.ne_last_of_lt halt)).succ ≫
              mappingSpaceLeft.stdSimplexOf E x y
                (boundary.ι d.succ ≫ top)
        rw [← mappingSpaceLeft.stdSimplexOf_δ,
          ← mappingSpaceLeft.stdSimplexOf_δ]
        have key := hfTop a d.succ hab
        rw [Fin.pred_succ] at key
        exact congrArg (mappingSpaceLeft.stdSimplexOf E x y) key
    have hcommhorn : ∀ (j : Fin (m + 3)) (hj : j ≠ (0 : Fin (m + 3))),
        fam j hj ≫ q = stdSimplex.δ j ≫ Tb := by
      intro j hj
      obtain ⟨a, rfl⟩ := j.eq_succ_of_ne_zero hj
      have hf1 : fam a.succ hj = G a := by
        change G (a.succ.pred _) = G a
        rw [Fin.pred_succ]
      rw [hf1]
      change mappingSpaceLeft.stdSimplexOf E x y (boundary.ι a ≫ top) ≫ q =
        stdSimplex.δ a.succ ≫ Tb
      rw [← mappingSpaceLeft.stdSimplexOf_map, Category.assoc, sq.w,
        ← Category.assoc, boundary.ι_ι, mappingSpaceLeft.stdSimplexOf_δ,
        hTbdef]
    obtain ⟨Sigma0, hSigmafaces0, hSigmaq⟩ := exists_simplex_lift_horn
      hcompat (LeftFibration.hasLiftingProperty_horn (p := q) (by
        have h1 : (0 : Fin (m + 3)).val = 0 := by simp
        rw [Fin.lt_def, h1, Fin.val_last]; omega)) Tb hcommhorn
    have hSigmafaces : ∀ a : Fin (m + 2),
        stdSimplex.δ a.succ ≫ Sigma0 = G a := by
      intro a
      rw [hSigmafaces0 (a.succ) (Fin.succ_ne_zero a)]
      change G (a.succ.pred _) = G a
      rw [Fin.pred_succ]
    have hSigmav : vertexZeroStd (m + 1) ≫ Sigma0 = x := by
      have e1 : vertexZeroStd (m + 1) ≫ Sigma0 =
          vertexZeroStd m ≫
            (stdSimplex.δ (0 : Fin (m + 2)).succ ≫ Sigma0) := by
        rw [← Category.assoc, vertexZeroStd_comp_stdSimplex_δ_succ]
      rw [e1, hSigmafaces]
      exact mappingSpaceLeft.stdSimplexOf_vertex E x y _
    set φ' : (Δ[m + 1] : SSet.{u}) ⟶ pullback q (y ≫ q) :=
      pullback.lift (stdSimplex.δ (0 : Fin (m + 3)) ≫ Sigma0)
        (toDeltaZero (Δ[m + 1] : SSet.{u}))
        (by rw [Category.assoc, hSigmaq]; exact hTb) with hφ'def
    have hφ' : φ' ≫ pullback.fst q (y ≫ q) =
        stdSimplex.δ (0 : Fin (m + 3)) ≫ Sigma0 :=
      pullback.lift_fst _ _ _
    have hφ'faces : ∀ a : Fin (m + 2),
        stdSimplex.δ a ≫ φ' = toDeltaZero (Δ[m] : SSet.{u}) ≫ ŷ := by
      intro a
      apply pullback.hom_ext
      · calc (stdSimplex.δ a ≫ φ') ≫ pullback.fst q (y ≫ q)
            = stdSimplex.δ (0 : Fin (m + 2)) ≫
                (stdSimplex.δ a.succ ≫ Sigma0) := by
              rw [Category.assoc, hφ', ← Category.assoc,
                stdSimplex_δ_comp_δ_zero, Category.assoc]
          _ = (toDeltaZero (Δ[m] : SSet.{u}) ≫ ŷ) ≫
                pullback.fst q (y ≫ q) := by
              rw [hSigmafaces, Category.assoc, hŷ]
              exact mappingSpaceLeft.stdSimplexOf_back E x y _
      · exact (toDeltaZero_eq _).trans (toDeltaZero_eq _).symm
    have hφcompat : boundary.IsCompatible
        (fun j : Fin (m + 3) =>
          if j = (0 : Fin (m + 2)).succ then φ'
          else toDeltaZero (Δ[m + 1] : SSet.{u}) ≫ ŷ) := by
      rw [boundary.isCompatible_succ_iff]
      intro j v hjv
      have hcst : ∀ (a : Fin (m + 2)),
          stdSimplex.δ a ≫ (toDeltaZero (Δ[m + 1] : SSet.{u}) ≫ ŷ) =
            toDeltaZero (Δ[m] : SSet.{u}) ≫ ŷ :=
        fun a => by
          rw [← Category.assoc,
            toDeltaZero_eq (stdSimplex.δ a ≫ toDeltaZero _)]
      by_cases hj1 : j = (0 : Fin (m + 2)).succ
      · subst hj1
        have hv1 : v ≠ (0 : Fin (m + 2)).succ :=
          fun hv => absurd (hv ▸ hjv) (lt_irrefl _)
        simp only [ite_true, hv1, ite_false]
        rw [hφ'faces, hcst]
      · by_cases hv1 : v = (0 : Fin (m + 2)).succ
        · subst hv1
          have hj0 : j = 0 := by
            apply Fin.ext
            have h1 : ((0 : Fin (m + 2)).succ).val = 1 := by simp
            have hz : (0 : Fin (m + 3)).val = 0 := by simp
            rw [Fin.lt_def, h1] at hjv
            rw [hz]
            omega
          subst hj0
          have h0ne : ¬ ((0 : Fin (m + 3)) = (0 : Fin (m + 2)).succ) :=
            (Fin.succ_ne_zero _).symm
          simp only [h0ne, ite_false, ite_true]
          have e0 : (0 : Fin (m + 3)).castPred
                (Fin.ne_last_of_lt hjv) =
              (0 : Fin (m + 2)) :=
            Fin.ext (by simp)
          rw [Fin.pred_succ, hcst, e0, hφ'faces]
        · simp only [hj1, ite_false, hv1, ite_false]
          rw [hcst, hcst]
    obtain ⟨Sigma1, hS1q, hS1v, hS10, hS1faces⟩ :=
      exists_simplex_with_const_backFace hFib hSigmaq hSigmav hTb φ'
        hφ' ŷ hŷ hφcompat
    set lift : (Δ[m + 1] : SSet.{u}) ⟶ mappingSpaceLeft E x y :=
      mappingSpaceLeft.ofStdSimplex E x y Sigma1 hS1v hS10 with hlift
    refine ⟨⟨CommSq.LiftStruct.mk lift ?_ ?_⟩⟩
    · apply boundary.hom_ext
      intro a
      rw [← Category.assoc, boundary.ι_ι]
      apply mappingSpaceLeft.ext_of_stdSimplexOf_eq E x y
      rw [hlift, mappingSpaceLeft.stdSimplexOf_δ,
        mappingSpaceLeft.stdSimplexOf_ofStdSimplex, hS1faces,
        hSigmafaces]
    · apply mappingSpaceLeft.ext_of_stdSimplexOf_eq B (x ≫ q) (y ≫ q)
      rw [hlift, mappingSpaceLeft.stdSimplexOf_map,
        mappingSpaceLeft.stdSimplexOf_ofStdSimplex, hS1q, hTbdef]

/-! ### §3. Fibers of the slice comparison map

The fiber of `sliceUnderComparison (p := p) x` over a
vertex `w` of `S_{x/} ×_S X` is the fiber of the
mapping-space map `Homᴸ(p)` over the corresponding vertex
of `Homᴸ_S(x ≫ p, y ≫ p)`, where `y` is the vertex of `X`
under `w`: the pullback pasting law applied to the landed
fiber square
`SSet.isPullback_mappingSpaceLeft_sliceUnderComparison`
(BoundaryLiftingCore §3). -/

/-- **Fibers of the slice comparison map from mapping
spaces**: if `p` induces trivial Kan fibrations on naive
left mapping spaces, every fiber of every slice comparison
map of `p` is a trivial Kan fibration to the point. -/
theorem sliceUnderComparison_fiber_I_rlp_of_mappingSpaceLeftTrivialFibration
    {p : X ⟶ S} (hp : MappingSpaceLeftTrivialFibration p)
    (x : (Δ[0] : SSet.{u}) ⟶ X)
    (w : (Δ[0] : SSet.{u}) ⟶ pullback (sliceUnder.proj S (x ≫ p)) p) :
    modelCategoryQuillen.I.rlp
      (pullback.snd (sliceUnderComparison (p := p) x) w) := by
  set y : (Δ[0] : SSet.{u}) ⟶ X :=
    w ≫ pullback.snd (sliceUnder.proj S (x ≫ p)) p with hy
  set σw : (Δ[1] : SSet.{u}) ⟶ S :=
    sliceUnder.stdSimplexOf S (x ≫ p)
      (w ≫ pullback.fst (sliceUnder.proj S (x ≫ p)) p) with hσw
  have hback : stdSimplex.δ (0 : Fin 2) ≫ σw =
      toDeltaZero (Δ[0] : SSet.{u}) ≫ (y ≫ p) := by
    have e1 : stdSimplex.δ (0 : Fin 2) ≫ σw =
        (w ≫ pullback.fst (sliceUnder.proj S (x ≫ p)) p) ≫
          sliceUnder.proj S (x ≫ p) :=
      (sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf S (x ≫ p) _).symm
    have e2 : (w ≫ pullback.fst (sliceUnder.proj S (x ≫ p)) p) ≫
          sliceUnder.proj S (x ≫ p) = y ≫ p := by
      simp only [hy, Category.assoc, pullback.condition]
    rw [e1, e2, ← toDeltaZero_eq (𝟙 (Δ[0] : SSet.{u})), Category.id_comp]
  set e : (Δ[0] : SSet.{u}) ⟶ mappingSpaceLeft S (x ≫ p) (y ≫ p) :=
    mappingSpaceLeft.ofStdSimplex S (x ≫ p) (y ≫ p) σw
      (sliceUnder.stdSimplexOf_vertex S (x ≫ p) _) hback with he
  have hw : w = e ≫ mappingSpaceLeftToPullback (p := p) x y := by
    apply pullback.hom_ext
    · have step1 : (e ≫ mappingSpaceLeftToPullback (p := p) x y) ≫
            pullback.fst (sliceUnder.proj S (x ≫ p)) p =
          e ≫ mappingSpaceLeft.toSliceUnder S (x ≫ p) (y ≫ p) := by
        simp only [Category.assoc, mappingSpaceLeftToPullback_fst]
      rw [step1, he, mappingSpaceLeft.ofStdSimplex_comp_toSliceUnder]
      exact (sliceUnder.ofStdSimplex_stdSimplexOf S (x ≫ p) _).symm
    · have hsnd : (e ≫ mappingSpaceLeftToPullback (p := p) x y) ≫
            pullback.snd (sliceUnder.proj S (x ≫ p)) p = y := by
        rw [show (e ≫ mappingSpaceLeftToPullback (p := p) x y) ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p =
            e ≫ (toDeltaZero (mappingSpaceLeft S (x ≫ p) (y ≫ p)) ≫ y)
          from by
            simp only [Category.assoc, mappingSpaceLeftToPullback_snd],
          ← Category.assoc, toDeltaZero_eq (e ≫ toDeltaZero _),
          ← toDeltaZero_eq (𝟙 (Δ[0] : SSet.{u})), Category.id_comp]
      exact hsnd.symm
  -- Pasting: the fiber square of `sliceUnderComparison` over
  -- `w` is the fiber square of the mapping-space map over `e`.
  set t := isPullback_mappingSpaceLeft_sliceUnderComparison x y
  set l : pullback (sliceUnderComparison (p := p) x) w ⟶
      mappingSpaceLeft X x y :=
    t.lift (pullback.fst (sliceUnderComparison (p := p) x) w)
      (pullback.snd (sliceUnderComparison (p := p) x) w ≫ e)
      (by
        rw [Category.assoc, ← hw]
        exact pullback.condition) with hl
  have hs : IsPullback
      (l ≫ mappingSpaceLeft.toSliceUnder X x y)
      (pullback.snd (sliceUnderComparison (p := p) x) w)
      (sliceUnderComparison (p := p) x)
      (e ≫ mappingSpaceLeftToPullback (p := p) x y) := by
    rw [hl, t.lift_fst, ← hw]
    exact IsPullback.of_hasPullback _ _
  have hsq := IsPullback.of_right hs (t.lift_snd _ _ _) t
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
    (hp x y)

/-! ### §4. HTT Lemma 2.1.3.4 (the additional comparison obligation) -/

/-- Boundary lifting in dimension `0` from the fiber
hypothesis: a vertex of the base lifts through its fiber,
which is a trivial Kan fibration to the point. -/
theorem hasLiftingProperty_boundary_zero_of_fibers_I_rlp {q : E ⟶ B}
    (hFib : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      modelCategoryQuillen.I.rlp (pullback.snd q b)) :
    HasLiftingProperty (boundary 0).ι q := by
  refine ⟨?_⟩
  intro top bottom sq
  have : HasLiftingProperty (boundary 0).ι (pullback.snd q bottom) :=
    hFib bottom _ (modelCategoryQuillen.boundary_ι_mem_I 0)
  set top' : ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶
      pullback q bottom :=
    pullback.lift top (toDeltaZero _)
      (by rw [sq.w, toDeltaZero_eq ((boundary 0).ι)]) with htop'
  set sq' : CommSq top' (boundary 0).ι (pullback.snd q bottom)
      (𝟙 (Δ[0] : SSet.{u})) :=
    ⟨by rw [htop', pullback.lift_snd, Category.comp_id,
      toDeltaZero_eq ((boundary 0).ι)]⟩ with hsq'
  refine ⟨⟨CommSq.LiftStruct.mk (sq'.lift ≫ pullback.fst q bottom)
    ?_ ?_⟩⟩
  · rw [← Category.assoc, sq'.fac_left, htop', pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      sq'.fac_right, Category.id_comp]

/-- **HTT Lemma 2.1.3.4, boundary form**: a left fibration
whose fiber projections over vertices are trivial Kan
fibrations has the right lifting property against every
boundary inclusion, by induction on the dimension through
the transposition of §1 applied to `q` itself (its slice
comparison maps are left fibrations with trivial fibers by
§§2–3). -/
theorem hasLiftingProperty_boundary_of_leftFibration_of_fibers :
    ∀ (n : ℕ) {E B : SSet.{u}} (q : E ⟶ B) [LeftFibration q],
      (∀ b : (Δ[0] : SSet.{u}) ⟶ B,
        modelCategoryQuillen.I.rlp (pullback.snd q b)) →
      HasLiftingProperty (boundary n).ι q := by
  intro n
  induction n with
  | zero =>
      intro E B q _ hFib
      exact hasLiftingProperty_boundary_zero_of_fibers_I_rlp hFib
  | succ n ih =>
      intro E B q _ hFib
      apply hasLiftingProperty_boundary_succ_of_sliceUnderComparison
      intro x
      apply ih
      intro w
      exact
        sliceUnderComparison_fiber_I_rlp_of_mappingSpaceLeftTrivialFibration
          (mappingSpaceLeftTrivialFibration_of_leftFibration_of_fibers
            hFib) x w

/-- **HTT Lemma 2.1.3.4, consumed form**
(the additional comparison obligation): a left fibration whose fiber
projections `pullback.snd q b` over all vertices are
trivial Kan fibrations is itself a trivial Kan fibration. -/
theorem modelCategoryQuillen_I_rlp_of_leftFibration_of_fibers
    {q : E ⟶ B} [LeftFibration q]
    (hFib : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      modelCategoryQuillen.I.rlp (pullback.snd q b)) :
    modelCategoryQuillen.I.rlp q :=
  (modelCategoryQuillen_I_rlp_iff_hasLiftingProperty_boundary q).mpr
    (fun n => hasLiftingProperty_boundary_of_leftFibration_of_fibers n q
      hFib)

/-- The converse direction of HTT Lemma 2.1.3.4, in the
consumed form: the fibers of a trivial Kan fibration over
vertices are trivial Kan fibrations to the point, by base
change. -/
theorem modelCategoryQuillen_I_rlp_pullback_snd_of_I_rlp {q : E ⟶ B}
    (hq : modelCategoryQuillen.I.rlp q) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    modelCategoryQuillen.I.rlp (pullback.snd q b) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback q b) hq

/-- **HTT Lemma 2.1.3.4 as an equivalence** for left
fibrations, in the consumed form where contractibility of
a fiber is triviality of its projection to the point. -/
theorem modelCategoryQuillen_I_rlp_iff_fibers_of_leftFibration
    {q : E ⟶ B} [LeftFibration q] :
    modelCategoryQuillen.I.rlp q ↔
      ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
        modelCategoryQuillen.I.rlp (pullback.snd q b) :=
  ⟨fun hq b => modelCategoryQuillen_I_rlp_pullback_snd_of_I_rlp hq b,
    modelCategoryQuillen_I_rlp_of_leftFibration_of_fibers⟩

/-! ### §5. Boundary lifting from a pointwise mapping-space condition -/

/-- **Stevenson's Step 3 as a boundary statement**: an
inner fibration inducing trivial Kan fibrations on naive
left mapping spaces lifts against `(boundary (n + 1)).ι`
for every `n` — the slice comparison maps are left
fibrations (SliceLeftFibration §3) with trivial fibers
(§3), hence trivial Kan fibrations (§4), and the
transposition (§1) applies. -/
theorem hasLiftingProperty_boundary_succ_of_mappingSpaceLeftTrivialFibration
    {p : X ⟶ S} [InnerFibration p]
    (hp : MappingSpaceLeftTrivialFibration p) (n : ℕ) :
    HasLiftingProperty (boundary (n + 1)).ι p :=
  hasLiftingProperty_boundary_succ_of_sliceUnderComparison (fun x =>
    hasLiftingProperty_boundary_of_leftFibration_of_fibers n
      (sliceUnderComparison (p := p) x)
      (fun w =>
        sliceUnderComparison_fiber_I_rlp_of_mappingSpaceLeftTrivialFibration
          hp x w))

/-! ### §6. Left fibrations between Kan complexes (plan (2a))

The remaining half of the additional comparison obligation, as planned in
SliceLeftFibration (2a): a left fibration between Kan
complexes is a Kan fibration. Only the right outer horns
`Λ[n + 1, last]` are at issue; the argument degenerates
the common faces of the bottom simplex and of a filler in
`E` to a right horn in `B`, then corrects by two left-horn
lifts. -/

/-- **Left fibrations between Kan complexes are Kan
fibrations** (plan (2a) of SliceLeftFibration): if `E` and
`B` are Kan complexes and `f : E ⟶ B` is a left fibration,
then `f` has the right lifting property against every horn
inclusion. -/
theorem modelCategoryQuillen_J_rlp_of_leftFibration_of_kanComplex
    {f : E ⟶ B} [LeftFibration f] [KanComplex E] [KanComplex B] :
    modelCategoryQuillen.J.rlp f := by
  intro A B' g hg
  simp only [modelCategoryQuillen.J, iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  by_cases hi : i < Fin.last (n + 1)
  · exact LeftFibration.hasLiftingProperty_horn hi
  · have hiE : i = Fin.last (n + 1) :=
      le_antisymm (Fin.le_last i) (not_lt.mp hi)
    subst hiE
    refine ⟨?_⟩
    intro top τ sq
    -- Fill the horn in `E`, using that `E` is Kan.
    obtain ⟨σ₀, hσ₀⟩ := horn.IsCompatible.exists_lift_of_kanComplex
      (horn.IsCompatible.of_hom top)
    have hσ₀' : ∀ (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)),
        stdSimplex.δ j ≫ σ₀ =
          horn.ι (Fin.last (n + 1)) j hj ≫ top :=
      fun j hj => hσ₀ j hj
    set τ₀ : (Δ[n + 1] : SSet.{u}) ⟶ B := σ₀ ≫ f with hτ₀
    have hcommon : ∀ (j : Fin (n + 2)) (hj : j ≠ Fin.last (n + 1)),
        stdSimplex.δ j ≫ τ₀ = stdSimplex.δ j ≫ τ := by
      intro j hj
      rw [hτ₀, ← Category.assoc, hσ₀' j hj, Category.assoc, sq.w,
        ← Category.assoc, horn.ι_ι]
    -- The right horn in `B` obtained by degenerating `τ₀`.
    set Θb : (Δ[n + 2] : SSet.{u}) ⟶ B :=
      stdSimplex.σ (0 : Fin (n + 2)) ≫ τ₀ with hΘb
    set Fb : ∀ (j : Fin (n + 3)) (_ : j ≠ Fin.last (n + 2)),
        (Δ[n + 1] : SSet.{u}) ⟶ B :=
      fun j _ => if j = 0 then τ else stdSimplex.δ j ≫ Θb with hFb
    have hΘb0 : stdSimplex.δ (0 : Fin (n + 3)) ≫ Θb = τ₀ := by
      rw [hΘb, ← Category.assoc,
        show stdSimplex.δ (0 : Fin (n + 3)) ≫
              stdSimplex.σ (0 : Fin (n + 2)) =
            𝟙 (Δ[n + 1] : SSet.{u}) from by
          rw [show (0 : Fin (n + 3)) =
              Fin.castSucc (0 : Fin (n + 2)) from rfl,
            CosimplicialObject.δ_comp_σ_self],
        Category.id_comp]
    have hFbcompat : horn.IsCompatible Fb := by
      rw [horn.isCompatible_iff]
      intro j v hj hv hjv
      by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨b, rfl⟩ := v.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjv)
        have hf0 : Fb (0 : Fin (n + 3)) hj = τ := ite_eq_left rfl
        have hfv : Fb b.succ hv = stdSimplex.δ b.succ ≫ Θb :=
          ite_eq_right (Fin.succ_ne_zero b)
        have e0 : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt hjv) =
            (0 : Fin (n + 2)) :=
          Fin.ext (by simp)
        have eδ : stdSimplex.δ (0 : Fin (n + 2)) ≫ stdSimplex.δ b.succ =
            stdSimplex.δ b ≫ stdSimplex.δ (0 : Fin (n + 3)) := by
          rw [show (0 : Fin (n + 3)) = Fin.castSucc (0 : Fin (n + 2))
              from rfl,
            CosimplicialObject.δ_comp_δ stdSimplex (by simp)]
        have hb : b ≠ Fin.last (n + 1) := by
          intro hcon
          apply hv
          apply Fin.ext
          have h1 : (b.succ).val = b.val + 1 := by simp
          have h2 : (Fin.last (n + 2)).val = n + 2 := Fin.val_last _
          have h3 : b.val = n + 1 := by
            have h := congrArg Fin.val hcon
            simpa [Fin.val_last] using h
          rw [h1, h2, h3]
        rw [Fin.pred_succ, e0, hf0, hfv, ← Category.assoc, eδ,
          Category.assoc, hΘb0]
        exact (hcommon b hb).symm
      · have hv0 : v ≠ 0 := Fin.ne_zero_of_lt hjv
        have hfj : Fb j hj = stdSimplex.δ j ≫ Θb := ite_eq_right hj0
        have hfv : Fb v hv = stdSimplex.δ v ≫ Θb := ite_eq_right hv0
        rw [hfj, hfv]
        exact (horn_isCompatible_of_stdSimplex Θb
          (Fin.last (n + 2))).δ_pred_comp j v hj hv hjv
    obtain ⟨T, hT⟩ := hFbcompat.exists_lift_of_kanComplex
    have h0last : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro hcon
      have hv := congrArg Fin.val hcon
      have hz : (0 : Fin (n + 3)).val = 0 := by simp
      rw [hz, Fin.val_last] at hv
      omega
    have hT0 : stdSimplex.δ (0 : Fin (n + 3)) ≫ T = τ :=
      (hT (0 : Fin (n + 3)) h0last).trans (ite_eq_left rfl)
    have hTface : ∀ (j : Fin (n + 3)) (hj : j ≠ Fin.last (n + 2)),
        j ≠ 0 → stdSimplex.δ j ≫ T = stdSimplex.δ j ≫ Θb :=
      fun j hj hj0 => (hT j hj).trans (ite_eq_right hj0)
    -- The degenerate simplex in `E` whose faces are the
    -- horn family for the last face lift.
    set ΘG : (Δ[n + 1] : SSet.{u}) ⟶ E :=
      stdSimplex.σ (0 : Fin (n + 1)) ≫
        (stdSimplex.δ (Fin.last (n + 1)) ≫ σ₀) with hΘG
    have hΘGf : ΘG ≫ f =
        stdSimplex.σ (0 : Fin (n + 1)) ≫
          (stdSimplex.δ (Fin.last (n + 1)) ≫ τ₀) := by
      calc ΘG ≫ f
          = stdSimplex.σ (0 : Fin (n + 1)) ≫
              (stdSimplex.δ (Fin.last (n + 1)) ≫ (σ₀ ≫ f)) := by
            rw [hΘG]
            simp only [Category.assoc]
        _ = stdSimplex.σ (0 : Fin (n + 1)) ≫
              (stdSimplex.δ (Fin.last (n + 1)) ≫ τ₀) := rfl
    have hlast_ne : Fin.last (n + 2) ≠ 0 := by
      intro hcon
      have hv := congrArg Fin.val hcon
      have hz : (0 : Fin (n + 3)).val = 0 := by simp
      rw [Fin.val_last, hz] at hv
      omega
    -- The faces of `ΘG ≫ f` agree with the faces of the
    -- last face of `T` away from `0`.
    have hkey : ∀ (j : Fin (n + 2)), j ≠ 0 →
        stdSimplex.δ j ≫ (ΘG ≫ f) =
          stdSimplex.δ j ≫ (stdSimplex.δ (Fin.last (n + 2)) ≫ T) := by
      intro j hj0
      have hjc0 : j.castSucc ≠ (0 : Fin (n + 3)) := by
        intro hcon
        apply hj0
        apply Fin.ext
        have hv := congrArg Fin.val hcon
        simpa [Fin.val_castSucc] using hv
      have hjcl : j.castSucc ≠ Fin.last (n + 2) := by
        intro hcon
        have hv := congrArg Fin.val hcon
        have hjlt := j.is_lt
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
      have hjlt : j.castSucc < Fin.last (n + 2) := by
        rw [Fin.lt_def]
        simp only [Fin.val_castSucc, Fin.val_last]
        have := j.is_lt
        omega
      have hpred : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hjlt) =
          Fin.last (n + 1) :=
        Fin.pred_last
      have eT : stdSimplex.δ j ≫
            (stdSimplex.δ (Fin.last (n + 2)) ≫ T) =
          stdSimplex.δ (Fin.last (n + 1)) ≫
            (stdSimplex.δ j.castSucc ≫ T) := by
        have h := (horn_isCompatible_of_stdSimplex T
          (0 : Fin (n + 3))).δ_pred_comp (j.castSucc)
          (Fin.last (n + 2)) hjc0 hlast_ne hjlt
        rw [hpred, Fin.castPred_castSucc] at h
        exact h.symm
      rw [eT, hΘGf, hTface j.castSucc hjcl hjc0]
      by_cases hj1 : j = (0 : Fin (n + 1)).succ
      · subst hj1
        have ecast : ((0 : Fin (n + 1)).succ).castSucc =
            (0 : Fin (n + 2)).succ := rfl
        have eL : stdSimplex.δ (0 : Fin (n + 1)).succ ≫
              (stdSimplex.σ (0 : Fin (n + 1)) ≫
                (stdSimplex.δ (Fin.last (n + 1)) ≫ τ₀)) =
            stdSimplex.δ (Fin.last (n + 1)) ≫ τ₀ := by
          rw [← Category.assoc, CosimplicialObject.δ_comp_σ_succ,
            Category.id_comp]
        have eR : stdSimplex.δ (Fin.last (n + 1)) ≫
              (stdSimplex.δ ((0 : Fin (n + 1)).succ).castSucc ≫ Θb) =
            stdSimplex.δ (Fin.last (n + 1)) ≫ τ₀ := by
          apply congrArg
            (fun g => stdSimplex.δ (Fin.last (n + 1)) ≫ g)
          rw [ecast, hΘb, ← Category.assoc,
            CosimplicialObject.δ_comp_σ_succ, Category.id_comp]
        rw [eL, eR]
      · obtain ⟨c, rfl⟩ := j.eq_succ_of_ne_zero hj0
        have hc0 : c ≠ 0 := fun hc => hj1 (by rw [hc])
        obtain ⟨e, rfl⟩ := c.eq_succ_of_ne_zero hc0
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
          (show n ≠ 0 from fun hn => by subst hn; exact Fin.elim0 e)
        have eτ : stdSimplex.δ e.succ ≫
              (stdSimplex.δ (Fin.last (m + 2)) ≫ τ₀) =
            stdSimplex.δ (Fin.last (m + 1)) ≫
              (stdSimplex.δ (Fin.castSucc e).succ ≫ τ₀) := by
          have hjlt2 : Fin.castSucc (e.succ) < Fin.last (m + 2) := by
            rw [Fin.lt_def]
            simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last]
            have := e.is_lt
            omega
          have hpred2 : (Fin.last (m + 2)).pred
                (Fin.ne_zero_of_lt hjlt2) =
              Fin.last (m + 1) :=
            Fin.pred_last
          have h := (horn_isCompatible_of_stdSimplex τ₀
            (0 : Fin (m + 3))).δ_pred_comp (Fin.castSucc (e.succ))
            (Fin.last (m + 2)) (by
              intro hcon
              have hv := congrArg Fin.val hcon
              simp [Fin.val_castSucc] at hv) (by
              intro hcon
              have hv := congrArg Fin.val hcon
              have hz : (0 : Fin (m + 3)).val = 0 := by simp
              rw [Fin.val_last, hz] at hv
              omega) hjlt2
          rw [hpred2, Fin.castPred_castSucc] at h
          have ecast2 : Fin.castSucc (e.succ) = (Fin.castSucc e).succ :=
            Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ])
          rw [ecast2] at h
          exact h.symm
        have eL : stdSimplex.δ e.succ.succ ≫
              (stdSimplex.σ (0 : Fin (m + 2)) ≫
                (stdSimplex.δ (Fin.last (m + 2)) ≫ τ₀)) =
            stdSimplex.σ (0 : Fin (m + 1)) ≫
              (stdSimplex.δ (Fin.last (m + 1)) ≫
                (stdSimplex.δ (Fin.castSucc e).succ ≫ τ₀)) := by
          rw [← Category.assoc, stdSimplex_δ_succ_succ_comp_σ_zero,
            Category.assoc, eτ]
        have eRi : stdSimplex.δ (Fin.castSucc (e.succ.succ)) ≫ Θb =
            stdSimplex.σ (0 : Fin (m + 2)) ≫
              (stdSimplex.δ (Fin.castSucc e).succ ≫ τ₀) := by
          rw [show Fin.castSucc (e.succ.succ) =
              (Fin.castSucc e).succ.succ from
            Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]),
            hΘb, ← Category.assoc,
            stdSimplex_δ_succ_succ_comp_σ_zero, Category.assoc]
        have eR : stdSimplex.δ (Fin.last (m + 2)) ≫
              (stdSimplex.δ (Fin.castSucc (e.succ.succ)) ≫ Θb) =
            stdSimplex.σ (0 : Fin (m + 1)) ≫
              (stdSimplex.δ (Fin.last (m + 1)) ≫
                (stdSimplex.δ (Fin.castSucc e).succ ≫ τ₀)) := by
          rw [eRi, ← Category.assoc, stdSimplex_δ_last_comp_σ_zero,
            Category.assoc]
        rw [eL, eR]
    -- The last face, by a left horn lift against `f`.
    obtain ⟨L, hLfaces, hLf⟩ := exists_simplex_lift_horn
      (horn_isCompatible_of_stdSimplex ΘG (0 : Fin (n + 2)))
      (LeftFibration.hasLiftingProperty_horn (p := f) (by
        have h1 : (0 : Fin (n + 2)).val = 0 := by simp
        rw [Fin.lt_def, h1, Fin.val_last]; omega))
      (stdSimplex.δ (Fin.last (n + 2)) ≫ T) (by
        intro j hj
        show (stdSimplex.δ j ≫ ΘG) ≫ f =
          stdSimplex.δ j ≫ (stdSimplex.δ (Fin.last (n + 2)) ≫ T)
        rw [Category.assoc]
        exact hkey j hj)
    have hLfaces' : ∀ (j : Fin (n + 2)) (hj : j ≠ (0 : Fin (n + 2))),
        stdSimplex.δ j ≫ L = stdSimplex.δ j ≫ ΘG :=
      fun j hj => hLfaces j hj
    -- The correcting left horn `Λ[n + 2, 0]` in `E` over `T`.
    set ΘE : (Δ[n + 2] : SSet.{u}) ⟶ E :=
      stdSimplex.σ (0 : Fin (n + 2)) ≫ σ₀ with hΘE
    have hΘEf : ΘE ≫ f = Θb := by
      calc ΘE ≫ f
          = stdSimplex.σ (0 : Fin (n + 2)) ≫ (σ₀ ≫ f) := by
            rw [hΘE, Category.assoc]
        _ = Θb := rfl
    set famΩ : ∀ (j : Fin (n + 3)) (_ : j ≠ (0 : Fin (n + 3))),
        (Δ[n + 1] : SSet.{u}) ⟶ E :=
      fun j _ => if j = Fin.last (n + 2) then L
        else stdSimplex.δ j ≫ ΘE with hfamΩ
    have hcompatΩ : horn.IsCompatible famΩ := by
      rw [horn.isCompatible_iff]
      intro j v hj hv hjv
      by_cases hvlast : v = Fin.last (n + 2)
      · subst hvlast
        have hfj : famΩ j hj = stdSimplex.δ j ≫ ΘE :=
          ite_eq_right (Fin.ne_last_of_lt hjv)
        have hfv : famΩ (Fin.last (n + 2)) hv = L := ite_eq_left rfl
        have hpred : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hjv) =
            Fin.last (n + 1) :=
          Fin.pred_last
        rw [hpred, hfj, hfv]
        have hcastPredne :
            j.castPred (Fin.ne_last_of_lt hjv) ≠ (0 : Fin (n + 2)) := by
          intro hcon
          apply hj
          apply Fin.ext
          have hv2 := congrArg Fin.val hcon
          simpa [Fin.coe_castPred] using hv2
        rw [hLfaces' (j.castPred (Fin.ne_last_of_lt hjv)) hcastPredne]
        by_cases hj1 : j = (0 : Fin (n + 2)).succ
        · subst hj1
          have ecast : ((0 : Fin (n + 2)).succ).castPred
                (Fin.ne_last_of_lt hjv) =
              (0 : Fin (n + 1)).succ :=
            Fin.ext (by simp)
          have eL : stdSimplex.δ (Fin.last (n + 1)) ≫
                (stdSimplex.δ (0 : Fin (n + 2)).succ ≫ ΘE) =
              stdSimplex.δ (Fin.last (n + 1)) ≫ σ₀ := by
            apply congrArg
              (fun g => stdSimplex.δ (Fin.last (n + 1)) ≫ g)
            rw [hΘE, ← Category.assoc,
              CosimplicialObject.δ_comp_σ_succ, Category.id_comp]
          have eR : stdSimplex.δ (0 : Fin (n + 1)).succ ≫ ΘG =
              stdSimplex.δ (Fin.last (n + 1)) ≫ σ₀ := by
            rw [hΘG, ← Category.assoc,
              CosimplicialObject.δ_comp_σ_succ, Category.id_comp]
          rw [ecast, eL, eR]
        · obtain ⟨c, rfl⟩ := j.eq_succ_of_ne_zero hj
          have hc0 : c ≠ 0 := fun hc => hj1 (by rw [hc])
          obtain ⟨e, rfl⟩ := c.eq_succ_of_ne_zero hc0
          have hjv' : e.val + 2 < n + 2 := by
            have h := hjv
            rw [Fin.lt_def] at h
            simpa only [Fin.val_succ, Fin.val_last] using h
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (show n ≠ 0 by omega)
          have helt : e < Fin.last (m + 1) := by
            rw [Fin.lt_def, Fin.val_last]
            omega
          have helt1 : e.succ < Fin.last (m + 2) := by
            rw [Fin.lt_def]
            simp only [Fin.val_succ, Fin.val_last]
            omega
          have e2b : (e.succ).castPred (Fin.ne_last_of_lt helt1) =
              (e.castPred (Fin.ne_last_of_lt helt)).succ :=
            Fin.ext (by simp [Fin.coe_castPred])
          have ecast1 : (e.succ.succ).castPred
                (Fin.ne_last_of_lt hjv) =
              (e.castPred (Fin.ne_last_of_lt helt)).succ.succ := by
            have e2a : (e.succ.succ).castPred
                  (Fin.ne_last_of_lt hjv) =
                ((e.succ).castPred (Fin.ne_last_of_lt helt1)).succ :=
              Fin.ext (by simp [Fin.coe_castPred])
            rw [e2a, e2b]
          have eL : stdSimplex.δ (Fin.last (m + 2)) ≫
                (stdSimplex.δ e.succ.succ ≫ ΘE) =
              stdSimplex.σ (0 : Fin (m + 1)) ≫
                (stdSimplex.δ (Fin.last (m + 1)) ≫
                  (stdSimplex.δ e.succ ≫ σ₀)) := by
            have eLi : stdSimplex.δ e.succ.succ ≫ ΘE =
                stdSimplex.σ (0 : Fin (m + 2)) ≫
                  (stdSimplex.δ e.succ ≫ σ₀) := by
              rw [hΘE, ← Category.assoc,
                stdSimplex_δ_succ_succ_comp_σ_zero, Category.assoc]
            rw [eLi, ← Category.assoc, stdSimplex_δ_last_comp_σ_zero,
              Category.assoc]
          have eσ : stdSimplex.δ (Fin.last (m + 1)) ≫
                (stdSimplex.δ e.succ ≫ σ₀) =
              stdSimplex.δ (e.castPred (Fin.ne_last_of_lt helt)).succ ≫
                (stdSimplex.δ (Fin.last (m + 2)) ≫ σ₀) := by
            have hpred3 : (Fin.last (m + 2)).pred
                  (Fin.ne_zero_of_lt helt1) =
                Fin.last (m + 1) :=
              Fin.pred_last
            have h := (horn_isCompatible_of_stdSimplex σ₀
              (0 : Fin (m + 3))).δ_pred_comp (e.succ)
              (Fin.last (m + 2)) (Fin.succ_ne_zero e) (by
                intro hcon
                have hv := congrArg Fin.val hcon
                have hz : (0 : Fin (m + 3)).val = 0 := by simp
                rw [Fin.val_last, hz] at hv
                omega) helt1
            rw [hpred3, e2b] at h
            exact h
          have eR : stdSimplex.δ
                (e.castPred (Fin.ne_last_of_lt helt)).succ.succ ≫ ΘG =
              stdSimplex.σ (0 : Fin (m + 1)) ≫
                (stdSimplex.δ (e.castPred
                    (Fin.ne_last_of_lt helt)).succ ≫
                  (stdSimplex.δ (Fin.last (m + 2)) ≫ σ₀)) := by
            rw [hΘG, ← Category.assoc,
              stdSimplex_δ_succ_succ_comp_σ_zero, Category.assoc]
          rw [ecast1, eL, eσ, eR]
      · have hfj : famΩ j hj = stdSimplex.δ j ≫ ΘE :=
          ite_eq_right (Fin.ne_last_of_lt hjv)
        have hfv : famΩ v hv = stdSimplex.δ v ≫ ΘE :=
          ite_eq_right hvlast
        rw [hfj, hfv]
        exact (horn_isCompatible_of_stdSimplex ΘE
          (0 : Fin (n + 3))).δ_pred_comp j v hj hv hjv
    obtain ⟨Ω, hΩfaces, hΩf⟩ := exists_simplex_lift_horn hcompatΩ
      (LeftFibration.hasLiftingProperty_horn (p := f) (by
        have h1 : (0 : Fin (n + 3)).val = 0 := by simp
        rw [Fin.lt_def, h1, Fin.val_last]; omega)) T (by
        intro j hj
        by_cases hjlast : j = Fin.last (n + 2)
        · subst hjlast
          have hfj : famΩ (Fin.last (n + 2)) hj = L := ite_eq_left rfl
          rw [hfj]
          exact hLf
        · have hfj : famΩ j hj = stdSimplex.δ j ≫ ΘE :=
            ite_eq_right hjlast
          rw [hfj, Category.assoc, hΘEf]
          exact (hTface j hjlast hj).symm)
    refine ⟨⟨CommSq.LiftStruct.mk (stdSimplex.δ (0 : Fin (n + 3)) ≫ Ω)
      ?_ ?_⟩⟩
    · apply horn.hom_ext'
      intro j hj
      rw [← Category.assoc, horn.ι_ι, ← Category.assoc]
      by_cases hj0 : j = 0
      · subst hj0
        have eδδ : stdSimplex.δ (0 : Fin (n + 2)) ≫
              stdSimplex.δ (0 : Fin (n + 3)) =
            stdSimplex.δ (0 : Fin (n + 2)) ≫
              stdSimplex.δ (0 : Fin (n + 2)).succ :=
          (stdSimplex_δ_zero_comp_δ_succ_zero n).symm
        have hne : (0 : Fin (n + 2)).succ ≠ Fin.last (n + 2) := by
          intro hcon
          have hv := congrArg Fin.val hcon
          have h1 : ((0 : Fin (n + 2)).succ).val = 1 := by simp
          rw [h1, Fin.val_last] at hv
          omega
        have hf : famΩ (0 : Fin (n + 2)).succ (Fin.succ_ne_zero _) =
            stdSimplex.δ (0 : Fin (n + 2)).succ ≫ ΘE :=
          ite_eq_right hne
        have eΘ : stdSimplex.δ (0 : Fin (n + 2)).succ ≫ ΘE = σ₀ := by
          rw [hΘE, ← Category.assoc,
            CosimplicialObject.δ_comp_σ_succ, Category.id_comp]
        rw [eδδ, Category.assoc, hΩfaces _ (Fin.succ_ne_zero _), hf, eΘ]
        exact hσ₀' (0 : Fin (n + 2)) hj
      · obtain ⟨a, rfl⟩ := j.eq_succ_of_ne_zero hj0
        have eδδ : stdSimplex.δ a.succ ≫ stdSimplex.δ (0 : Fin (n + 3)) =
            stdSimplex.δ (0 : Fin (n + 2)) ≫ stdSimplex.δ a.succ.succ := by
          rw [show (0 : Fin (n + 3)) = Fin.castSucc (0 : Fin (n + 2))
              from rfl]
          exact (CosimplicialObject.δ_comp_δ stdSimplex
            (i := (0 : Fin (n + 2))) (j := a.succ) (by simp)).symm
        have hne : a.succ.succ ≠ Fin.last (n + 2) := by
          intro hcon
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val hcon
          simp only [Fin.val_succ, Fin.val_last] at hv
          simp only [Fin.val_succ, Fin.val_last]
          omega
        have hf : famΩ a.succ.succ (Fin.succ_ne_zero _) =
            stdSimplex.δ a.succ.succ ≫ ΘE :=
          ite_eq_right hne
        have eΘ : stdSimplex.δ (0 : Fin (n + 2)) ≫
              (stdSimplex.δ a.succ.succ ≫ ΘE) =
            stdSimplex.δ a.succ ≫ σ₀ := by
          have eΘi : stdSimplex.δ a.succ.succ ≫ ΘE =
              stdSimplex.σ (0 : Fin (n + 1)) ≫
                (stdSimplex.δ a.succ ≫ σ₀) := by
            rw [hΘE, ← Category.assoc,
              stdSimplex_δ_succ_succ_comp_σ_zero, Category.assoc]
          rw [eΘi, ← Category.assoc,
            show stdSimplex.δ (0 : Fin (n + 2)) ≫
                  stdSimplex.σ (0 : Fin (n + 1)) =
                𝟙 (Δ[n] : SSet.{u}) from by
              rw [show (0 : Fin (n + 2)) =
                  Fin.castSucc (0 : Fin (n + 1)) from rfl,
                CosimplicialObject.δ_comp_σ_self],
            Category.id_comp]
        rw [eδδ, Category.assoc, hΩfaces _ (Fin.succ_ne_zero _), hf, eΘ]
        exact hσ₀' a.succ hj
    · rw [Category.assoc, hΩf, hT0]

/-- **The weak-equivalence upgrade** (plan (2a) of
SliceLeftFibration): a left fibration which is a
`KanComplex.W` weak equivalence is a trivial Kan
fibration — it is a Kan fibration by
`SSet.modelCategoryQuillen_J_rlp_of_leftFibration_of_kanComplex`
(its source and target are Kan complexes since it is in
`KanComplex.W`), and a Kan fibration in `KanComplex.W` is
a trivial Kan fibration by the landed
`SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp`. -/
theorem modelCategoryQuillen_I_rlp_of_leftFibration_of_W
    {f : E ⟶ B} [LeftFibration f] (hf : KanComplex.W f) :
    modelCategoryQuillen.I.rlp f := by
  have : KanComplex E := hf.kanComplex_source
  have : KanComplex B := hf.kanComplex_target
  exact modelCategoryQuillen.J_rlp_inf_W_le_I_rlp f
    ⟨modelCategoryQuillen_J_rlp_of_leftFibration_of_kanComplex, hf⟩

/-- **HTT Lemma 2.1.3.4 with `KanComplex.W` fibers**: a
left fibration whose fiber over every vertex is
contractible in the sense that its projection to the point
lies in `KanComplex.W` (in particular each fiber is a
contractible Kan complex) is a trivial Kan fibration. -/
theorem modelCategoryQuillen_I_rlp_of_leftFibration_of_W_fibers
    {q : E ⟶ B} [LeftFibration q]
    (hFib : ∀ b : (Δ[0] : SSet.{u}) ⟶ B,
      KanComplex.W (pullback.snd q b)) :
    modelCategoryQuillen.I.rlp q := by
  apply modelCategoryQuillen_I_rlp_of_leftFibration_of_fibers
  intro b
  exact modelCategoryQuillen_I_rlp_of_leftFibration_of_W (hFib b)

/-! ### §7. The pointwise Dwyer–Kan condition -/

/-- Step 1 in Dwyer–Kan form implies Step 1 in
mapping-space-fibration form, by the weak-equivalence
upgrade of §6 applied to the mapping-space maps, which are
left fibrations by SliceLeftFibration §3 (through
`SSet.leftFibration_sliceUnderComparison`). Over pre-fibrant
`X, S`, Remark 3.3 (landed as
`SSet.leftMappingSpacesKan_of_isPreFibrant`) makes the
mapping spaces Kan complexes, upgrading the realization
weak equivalences to `KanComplex.W` via
`SSet.dwyerKanFullyFaithfulLeft.kanComplexW`. -/
theorem mappingSpaceLeftTrivialFibration_of_dwyerKanFullyFaithfulLeft
    {p : X ⟶ S} [InnerFibration p] [IsPreFibrant S]
    (hp : dwyerKanFullyFaithfulLeft p) :
    MappingSpaceLeftTrivialFibration p := by
  have : IsPreFibrant X := isPreFibrant_of_innerFibration p
  intro a b
  have : LeftFibration (mappingSpaceLeft.map X a b p) :=
    leftFibration_mappingSpaceLeft_map_of_leftFibration_sliceUnderComparison
      (p := p) a b
  exact modelCategoryQuillen_I_rlp_of_leftFibration_of_W
    (hp.kanComplexW (leftMappingSpacesKan_of_isPreFibrant X)
      (fun a b => leftMappingSpacesKan_of_isPreFibrant S (a ≫ p) (b ≫ p)) a b)

end SSet

end
