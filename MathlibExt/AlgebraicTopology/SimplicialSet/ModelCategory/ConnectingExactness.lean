/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ConnectingMap

/-!
# Connecting exactness at the total space

For a Kan fibration `p : E ⟶ B`, a class in `πₙ(E)` that maps trivially to `πₙ(B)`
comes from the strict fiber `Subcomplex.fiber p b`. The proof lifts a
`PtSimplex`-level `RelStruct₀` relation for `SSet.PtSimplex.map p` to a fiber-valued
pointed simplex together with a `RelStruct₀` over `E`.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial SSet Limits HomotopicalAlgebra Opposite MonoidalCategory
  CartesianMonoidalCategory
open SSet.modelCategoryQuillen

namespace SSet.ConnectingMap

variable {E B : SSet.{u}} {e : E _⦋0⦌} {b : B _⦋0⦌}

private lemma liftRelStruct₀_toFiber
    {n : ℕ} (p : E ⟶ B) (hb : p.app _ e = b) [Fibration p]
    (s : E.PtSimplex n e)
    (rel : (SSet.PtSimplex.map p hb s).RelStruct₀
      (RelativeMorphism.const : B.PtSimplex n b)) :
    ∃ t : (Subcomplex.fiber p b : SSet.{u}).PtSimplex n
        (Subcomplex.fiber.basePoint (f := p) e hb),
      Nonempty (s.RelStruct₀
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι rfl t)) := by
  let i0 : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
  let zero : Fin (n + 2) := i0.castSucc
  let one : Fin (n + 2) := i0.succ
  let faces : ∀ (j : Fin (n + 2)) (_ : j ≠ one), Δ[n] ⟶ E :=
    fun j _ => if j = zero then RelativeMorphism.map s else SSet.const e
  have hfaces : horn.IsCompatible faces := by
    obtain _ | m := n
    · trivial
    · rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      by_cases hj0 : j = zero
      · subst j
        have hk0 : k ≠ zero := by
          intro h
          subst k
          simp [zero, i0] at hjk
        simp only [faces, ite_eq_left, ite_eq_right hk0, SSet.comp_const]
        exact s.δ_map _
      · have hk0 : k ≠ zero := by
          intro h
          subst k
          simp [zero, i0] at hjk
        simp [faces, hj0, hk0, SSet.comp_const]
  have hcomm : ∀ (j : Fin (n + 2)) (hj : j ≠ one),
      faces j hj ≫ p = stdSimplex.δ j ≫ rel.map := by
    intro j hj
    by_cases hj0 : j = zero
    · subst j
      change RelativeMorphism.map (SSet.PtSimplex.map p hb s) =
        stdSimplex.δ zero ≫ rel.map
      dsimp [zero, i0]
      exact rel.δ_castSucc_map.symm
    · calc
        faces j hj ≫ p = SSet.const (X := Δ[n]) b := by
          simp [faces, hj0, SSet.const_comp, hb]
        _ = stdSimplex.δ j ≫ rel.map := by
          symm
          apply rel.δ_map_of_gt j
          have : one < j := by
            have hjval0 : j.val ≠ 0 := by
              intro hval
              apply hj0
              apply Fin.ext
              simpa [zero, i0] using hval
            have hjval1 : j.val ≠ 1 := by
              intro hval
              apply hj
              apply Fin.ext
              simpa [one, i0] using hval
            change 1 < j.val
            omega
          simpa [one, i0] using this
  let L : Δ[n + 1] ⟶ E := hfaces.lift p rel.map hcomm
  have hLproj : L ≫ p = rel.map :=
    hfaces.lift_comp (p := p) (b := rel.map) (comm := hcomm)
  have hL0 : stdSimplex.δ zero ≫ L = RelativeMorphism.map s := by
    have h := hfaces.δ_lift (p := p) (b := rel.map) (comm := hcomm)
      zero (by simp [zero, one, i0])
    simpa [L, faces] using h
  have hLj : ∀ (j : Fin (n + 2)), one < j →
      stdSimplex.δ j ≫ L = SSet.const e := by
    intro j hj
    have h := hfaces.δ_lift (p := p) (b := rel.map) (comm := hcomm)
      j (ne_of_gt hj)
    have hj0 : j ≠ zero := by
      intro hzero
      subst j
      simp [zero, one, i0] at hj
    simpa [L, faces, hj0] using h
  let tMap : Δ[n] ⟶ E := stdSimplex.δ one ≫ L
  have htProj : tMap ≫ p = SSet.const (X := Δ[n]) b := by
    calc
      tMap ≫ p = stdSimplex.δ one ≫ (L ≫ p) := by
        simp [tMap, Category.assoc]
      _ = stdSimplex.δ one ≫ rel.map := by rw [hLproj]
      _ = RelativeMorphism.map (RelativeMorphism.const : B.PtSimplex n b) :=
        by simpa [one, i0] using rel.δ_succ_map
      _ = SSet.const (X := Δ[n]) b := rfl
  have htBoundary : (SSet.boundary n).ι ≫ tMap =
      SSet.const (X := SSet.boundary n) e := by
    obtain _ | m := n
    · rw [SSet.boundary_zero]
      exact Subsingleton.elim _ _
    · apply SSet.boundary.hom_ext
      intro k
      rw [← Category.assoc, SSet.boundary.ι_ι]
      rw [SSet.comp_const]
      let lowerZero : Fin (m + 2) := ⟨0, by omega⟩
      by_cases hk : k = lowerZero
      · subst k
        dsimp [tMap]
        rw [← Category.assoc]
        have hδ0 :
            stdSimplex.δ lowerZero ≫
                stdSimplex.δ one =
              stdSimplex.δ lowerZero ≫
                stdSimplex.δ zero := by
          simpa [one, zero, i0, lowerZero] using
            (SSet.stdSimplex.δ_comp_δ_self
              (i := (0 : Fin (m + 2)))).symm
        rw [hδ0]
        rw [Category.assoc, hL0]
        exact s.δ_map _
      · let lowerOne : Fin (m + 2) :=
          (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).succ
        have hkval0 : k.val ≠ 0 := by
          intro hval
          apply hk
          apply Fin.ext
          simpa [lowerZero] using hval
        have hk1 : lowerOne ≤ k := by
          change 1 ≤ k.val
          omega
        dsimp [tMap]
        rw [← Category.assoc]
        have hδk :
            stdSimplex.δ k ≫ stdSimplex.δ one =
              stdSimplex.δ lowerOne ≫
                stdSimplex.δ k.succ := by
          simpa [one, i0, lowerOne] using
            (SSet.stdSimplex.δ_comp_δ hk1).symm
        rw [hδk]
        have hone_lt : one < k.succ := by
          change 1 < k.val + 1
          omega
        rw [Category.assoc, hLj k.succ hone_lt]
        exact SSet.comp_const _ _
  have hRange : Subcomplex.range tMap ≤ Subcomplex.fiber p b := by
    rw [Subcomplex.range_le_fiber_iff]
    exact htProj
  let tFibMap : Δ[n] ⟶ (Subcomplex.fiber p b : SSet.{u}) :=
    Subcomplex.lift tMap hRange
  have htFibMapι : tFibMap ≫ (Subcomplex.fiber p b).ι = tMap :=
    Subcomplex.lift_ι _ _
  let tFib : (Subcomplex.fiber p b : SSet.{u}).PtSimplex n
      (Subcomplex.fiber.basePoint (f := p) e hb) :=
    { map := tFibMap
      comm := by
        have h_boundary_lift :
            (SSet.boundary n).ι ≫ tFibMap ≫
                (Subcomplex.fiber p b).ι = SSet.const e := by
          calc
            (SSet.boundary n).ι ≫ tFibMap ≫
                  (Subcomplex.fiber p b).ι =
                (SSet.boundary n).ι ≫
                  (tFibMap ≫ (Subcomplex.fiber p b).ι) := rfl
            _ = (SSet.boundary n).ι ≫ tMap := by rw [htFibMapι]
            _ = SSet.const e := htBoundary
        have h_const_fiber :
            SSet.const (X := SSet.boundary n)
                (Subcomplex.fiber.basePoint (f := p) e hb) ≫
              (Subcomplex.fiber p b).ι = SSet.const e := by
          calc
            SSet.const (X := SSet.boundary n)
                  (Subcomplex.fiber.basePoint (f := p) e hb) ≫
                  (Subcomplex.fiber p b).ι =
                SSet.const
                  (X := SSet.boundary n)
                  ((Subcomplex.fiber p b).ι.app _
                    (Subcomplex.fiber.basePoint (f := p) e hb)) := by
                      rw [SSet.const_comp]
            _ = SSet.const (X := SSet.boundary n) e := by
                  have hpoint : (Subcomplex.fiber p b).ι.app _
                      (Subcomplex.fiber.basePoint (f := p) e hb) = e := by
                    change (Subcomplex.fiber.basePoint (f := p) e hb).val = e
                    exact Subcomplex.fiber.basePoint_val
                  rw [hpoint]
        have h_eq :
            (SSet.boundary n).ι ≫ tFibMap =
              SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) := by
          apply (cancel_mono (Subcomplex.fiber p b).ι).mp
          calc
            (SSet.boundary n).ι ≫ tFibMap ≫
                  (Subcomplex.fiber p b).ι =
                SSet.const e := h_boundary_lift
            _ = SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) ≫
                  (Subcomplex.fiber p b).ι := h_const_fiber.symm
        have h_ofSimplex :
            SSet.const (X := SSet.boundary n)
                (Subcomplex.fiber.basePoint (f := p) e hb) =
              SSet.const
                  (X := SSet.boundary n)
                  (Y := (Subcomplex.ofSimplex
                    (Subcomplex.fiber.basePoint (f := p) e hb) : SSet))
                  (⟨Subcomplex.fiber.basePoint (f := p) e hb,
                    Subcomplex.mem_ofSimplex_obj _⟩ :
                    (Subcomplex.ofSimplex
                      (Subcomplex.fiber.basePoint (f := p) e hb) : SSet).obj
                        (op ⦋0⦌)) ≫
                (Subcomplex.ofSimplex
                  (Subcomplex.fiber.basePoint (f := p) e hb)).ι := by
          rw [Subcomplex.ofSimplex_ι]
          rfl
        calc
          (SSet.boundary n).ι ≫ tFibMap =
              SSet.const (Subcomplex.fiber.basePoint (f := p) e hb) := h_eq
          _ = SSet.const
                (⟨Subcomplex.fiber.basePoint (f := p) e hb,
                  Subcomplex.mem_ofSimplex_obj _⟩ :
                  (Subcomplex.ofSimplex
                    (Subcomplex.fiber.basePoint (f := p) e hb) : SSet).obj
                      (op ⦋0⦌)) ≫
                (Subcomplex.ofSimplex
                  (Subcomplex.fiber.basePoint (f := p) e hb)).ι := by
                    rw [h_ofSimplex] }
  refine ⟨tFib, ⟨?_⟩⟩
  refine
    { map := L
      δ_castSucc_map := hL0
      δ_succ_map := by
        change stdSimplex.δ one ≫ L =
          RelativeMorphism.map tFib ≫ (Subcomplex.fiber p b).ι
        rw [htFibMapι]
      δ_map_of_lt := by
        intro j hj
        exact (Fin.not_lt_zero j hj).elim
      δ_map_of_gt := by
        intro j hj
        exact hLj j hj }

theorem connecting_exactness_at_E
    {E B : SSet} {n : ℕ} {e : E _⦋0⦌} {b : B _⦋0⦌}
    (p : E ⟶ B) (hb : p.app _ e = b)
    [Fibration p] [KanComplex B]
    (q : KanComplex.π n E e) :
    KanComplex.π.map p hb n q = 1 →
      ∃ r : KanComplex.π n (Subcomplex.fiber p b)
          (Subcomplex.fiber.basePoint (f := p) e hb),
        KanComplex.π.map (Subcomplex.fiber p b).ι rfl n r = q := by
  have : IsFibrant E := isFibrant_of_fibration p
  let : KanComplex E := inferInstance
  intro hq
  induction q using KanComplex.π.rec with
  | mk s =>
    rw [KanComplex.π.map_mk, KanComplex.π.mk_eq_one_iff] at hq
    obtain ⟨rel⟩ := hq
    obtain ⟨t, ht⟩ := liftRelStruct₀_toFiber p hb s rel
    refine ⟨KanComplex.π.mk t, ?_⟩
    rw [KanComplex.π.map_mk]
    change
      (KanComplex.π.mk
        (SSet.PtSimplex.map (Subcomplex.fiber p b).ι rfl t) :
          KanComplex.π n E e) =
        KanComplex.π.mk s
    rw [KanComplex.π.mk_eq_mk_iff]
    exact ⟨ht.some.symm⟩

end SSet.ConnectingMap
