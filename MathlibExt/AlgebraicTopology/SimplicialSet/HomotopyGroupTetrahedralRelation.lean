/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.MinimalOneReduced

/-!
# The native degree-two tetrahedral relation

Two explicit four-dimensional horn fillings relate the four pointed faces of
an arbitrary three-simplex. The first converts a zeroth-slot product filler
to a last-slot product filler with reversed inputs. The second compares the
two pairs of faces of the given tetrahedron.

The final one-reduced specialization uses the actual canonical pointed
representative of each two-face. The native product order is explicit:
`[d₀ t] * [d₂ t] = [d₃ t] * [d₁ t]`. Once native second homotopy is regarded
as its commutative additive group, this is the normalized boundary relation
`[d₀ t] - [d₁ t] + [d₂ t] - [d₃ t] = 0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace SSet

namespace PtSimplex.MulStruct

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}

/-- A degree-two product filler in slot zero gives a product filler in the
native last slot with the two inputs reversed. Its map is the actual missing
face of a four-horn whose other faces are the original filler and explicit
degeneracies. -/
noncomputable def toLastSlotTwo
    {p q r : X.PtSimplex 2 x} (h : p.MulStruct q r (0 : Fin 2)) :
    q.MulStruct p r (Fin.last 1) := by
  let dq₂ := PtSimplex.RelStruct.refl q (2 : Fin 3)
  let dp₁ := PtSimplex.RelStruct.refl p (1 : Fin 3)
  let dq₀ := PtSimplex.RelStruct.refl q (0 : Fin 3)
  let α (j : Fin 5) (_ : j ≠ (1 : Fin 5)) : Δ[3] ⟶ X :=
    if j = 0 then dq₂.map else
      if j = 2 then dp₁.map else
        if j = 3 then h.map else dq₀.map
  have hα : horn.IsCompatible α := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k
    all_goals try norm_num at hj
    all_goals try norm_num at hk
    all_goals try norm_num at hjk
    · change stdSimplex.δ (1 : Fin 4) ≫ dq₂.map =
        stdSimplex.δ (0 : Fin 4) ≫ dp₁.map
      rw [dq₂.δ_map_of_lt 1 (by decide), dp₁.δ_map_of_lt 0 (by decide)]
    · change stdSimplex.δ (2 : Fin 4) ≫ dq₂.map =
        stdSimplex.δ (0 : Fin 4) ≫ h.map
      exact dq₂.δ_castSucc_map.trans h.δ_castSucc_castSucc_map.symm
    · change stdSimplex.δ (3 : Fin 4) ≫ dq₂.map =
        stdSimplex.δ (0 : Fin 4) ≫ dq₀.map
      exact dq₂.δ_succ_map.trans dq₀.δ_castSucc_map.symm
    · change stdSimplex.δ (2 : Fin 4) ≫ dp₁.map =
        stdSimplex.δ (2 : Fin 4) ≫ h.map
      exact dp₁.δ_succ_map.trans h.δ_succ_succ_map.symm
    · change stdSimplex.δ (3 : Fin 4) ≫ dp₁.map =
        stdSimplex.δ (2 : Fin 4) ≫ dq₀.map
      rw [dp₁.δ_map_of_gt 3 (by decide), dq₀.δ_map_of_gt 2 (by decide)]
    · change stdSimplex.δ (3 : Fin 4) ≫ h.map =
        stdSimplex.δ (3 : Fin 4) ≫ dq₀.map
      rw [h.δ_map_of_gt 3 (by decide), dq₀.δ_map_of_gt 3 (by decide)]
  let φ : Δ[4] ⟶ X := hα.liftOfKanComplex
  have hφ (j : Fin 5) (hj : j ≠ (1 : Fin 5)) :
      stdSimplex.δ j ≫ φ = α j hj :=
    hα.δ_liftOfKanComplex j hj
  have hf₀ : stdSimplex.δ (0 : Fin 4) ≫
      stdSimplex.δ (1 : Fin 5) ≫ φ = const x := by
    rw [dsimp% stdSimplex.δ_comp_δ_assoc (i := (0 : Fin 4))
        (j := (0 : Fin 4)) (by decide), hφ 0 (by decide)]
    change stdSimplex.δ (0 : Fin 4) ≫ dq₂.map = const x
    exact dq₂.δ_map_of_lt 0 (by decide)
  have hf₁ : stdSimplex.δ (1 : Fin 4) ≫
      stdSimplex.δ (1 : Fin 5) ≫ φ = (RelativeMorphism.map p) := by
    rw [dsimp% stdSimplex.δ_comp_δ_self_assoc (i := (1 : Fin 4)),
      hφ 2 (by decide)]
    change stdSimplex.δ (1 : Fin 4) ≫ dp₁.map = RelativeMorphism.map p
    exact dp₁.δ_castSucc_map
  have hf₂ : stdSimplex.δ (2 : Fin 4) ≫
      stdSimplex.δ (1 : Fin 5) ≫ φ = (RelativeMorphism.map r) := by
    rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := (1 : Fin 4))
        (j := (2 : Fin 4)) (by decide),
      hφ 3 (by decide)]
    change stdSimplex.δ (1 : Fin 4) ≫ h.map = RelativeMorphism.map r
    exact h.δ_succ_castSucc_map
  have hf₃ : stdSimplex.δ (3 : Fin 4) ≫
      stdSimplex.δ (1 : Fin 5) ≫ φ = (RelativeMorphism.map q) := by
    rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := (1 : Fin 4))
        (j := (3 : Fin 4)) (by decide),
      hφ 4 (by decide)]
    change stdSimplex.δ (1 : Fin 4) ≫ dq₀.map = RelativeMorphism.map q
    exact dq₀.δ_succ_map
  refine
    { map := stdSimplex.δ (1 : Fin 5) ≫ φ
      δ_castSucc_castSucc_map := ?_
      δ_succ_castSucc_map := ?_
      δ_succ_succ_map := ?_
      δ_map_of_lt := ?_
      δ_map_of_gt := ?_ }
  · simpa using hf₁
  · simpa using hf₂
  · simpa using hf₃
  · intro j hj
    fin_cases j
    · simpa using hf₀
    all_goals norm_num at hj
  · intro j hj
    fin_cases j <;> norm_num at hj

end PtSimplex.MulStruct

namespace KanComplex.π

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}

/-- The two pairs of pointed faces of a tetrahedron have equal products in
native second homotopy, in the explicit order dictated by the simplicial
orientation. No product, homotopy, or Hurewicz witness is assumed. -/
theorem tetrahedral_relation_two
    (t : Δ[3] ⟶ X) (p₀ p₁ p₂ p₃ : X.PtSimplex 2 x)
    (h₀ : stdSimplex.δ (0 : Fin 4) ≫ t = (RelativeMorphism.map p₀))
    (h₁ : stdSimplex.δ (1 : Fin 4) ≫ t = (RelativeMorphism.map p₁))
    (h₂ : stdSimplex.δ (2 : Fin 4) ≫ t = (RelativeMorphism.map p₂))
    (h₃ : stdSimplex.δ (3 : Fin 4) ≫ t = (RelativeMorphism.map p₃)) :
    π.mk p₀ * π.mk p₂ = π.mk p₃ * π.mk p₁ := by
  obtain ⟨r, ⟨h⟩⟩ := PtSimplex.MulStruct.nonempty p₃ p₁ (Fin.last 1)
  let dp₀ := PtSimplex.RelStruct.refl p₀ (1 : Fin 3)
  let dp₃ := PtSimplex.RelStruct.refl p₃ (1 : Fin 3)
  let α (j : Fin 5) (_ : j ≠ (3 : Fin 5)) : Δ[3] ⟶ X :=
    if j = 0 then dp₀.map else
      if j = 1 then h.map else
        if j = 2 then t else dp₃.map
  have hα : horn.IsCompatible α := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k
    all_goals try norm_num at hj
    all_goals try norm_num at hk
    all_goals try norm_num at hjk
    · change stdSimplex.δ (0 : Fin 4) ≫ dp₀.map =
        stdSimplex.δ (0 : Fin 4) ≫ h.map
      rw [dp₀.δ_map_of_lt 0 (by decide), h.δ_map_of_lt 0 (by decide)]
    · change stdSimplex.δ (1 : Fin 4) ≫ dp₀.map =
        stdSimplex.δ (0 : Fin 4) ≫ t
      exact dp₀.δ_castSucc_map.trans h₀.symm
    · change stdSimplex.δ (3 : Fin 4) ≫ dp₀.map =
        stdSimplex.δ (0 : Fin 4) ≫ dp₃.map
      rw [dp₀.δ_map_of_gt 3 (by decide), dp₃.δ_map_of_lt 0 (by decide)]
    · change stdSimplex.δ (1 : Fin 4) ≫ h.map =
        stdSimplex.δ (1 : Fin 4) ≫ t
      exact h.δ_castSucc_castSucc_map.trans h₁.symm
    · change stdSimplex.δ (3 : Fin 4) ≫ h.map =
        stdSimplex.δ (1 : Fin 4) ≫ dp₃.map
      exact h.δ_succ_succ_map.trans dp₃.δ_castSucc_map.symm
    · change stdSimplex.δ (3 : Fin 4) ≫ t =
        stdSimplex.δ (2 : Fin 4) ≫ dp₃.map
      exact h₃.trans dp₃.δ_succ_map.symm
  let φ : Δ[4] ⟶ X := hα.liftOfKanComplex
  have hφ (j : Fin 5) (hj : j ≠ (3 : Fin 5)) :
      stdSimplex.δ j ≫ φ = α j hj :=
    hα.δ_liftOfKanComplex j hj
  have hf₀ : stdSimplex.δ (0 : Fin 4) ≫
      stdSimplex.δ (3 : Fin 5) ≫ φ = (RelativeMorphism.map p₀) := by
    rw [dsimp% stdSimplex.δ_comp_δ_assoc (i := (0 : Fin 4))
        (j := (2 : Fin 4)) (by decide), hφ 0 (by decide)]
    change stdSimplex.δ (2 : Fin 4) ≫ dp₀.map = RelativeMorphism.map p₀
    exact dp₀.δ_succ_map
  have hf₁ : stdSimplex.δ (1 : Fin 4) ≫
      stdSimplex.δ (3 : Fin 5) ≫ φ = (RelativeMorphism.map r) := by
    rw [dsimp% stdSimplex.δ_comp_δ_assoc (i := (1 : Fin 4))
        (j := (2 : Fin 4)) (by decide), hφ 1 (by decide)]
    change stdSimplex.δ (2 : Fin 4) ≫ h.map = RelativeMorphism.map r
    exact h.δ_succ_castSucc_map
  have hf₂ : stdSimplex.δ (2 : Fin 4) ≫
      stdSimplex.δ (3 : Fin 5) ≫ φ = (RelativeMorphism.map p₂) := by
    rw [dsimp% stdSimplex.δ_comp_δ_assoc (i := (2 : Fin 4))
        (j := (2 : Fin 4)) (by decide), hφ 2 (by decide)]
    change stdSimplex.δ (2 : Fin 4) ≫ t = RelativeMorphism.map p₂
    exact h₂
  have hf₃ : stdSimplex.δ (3 : Fin 4) ≫
      stdSimplex.δ (3 : Fin 5) ≫ φ = const x := by
    rw [dsimp% stdSimplex.δ_comp_δ_self_assoc (i := (3 : Fin 4)),
      hφ 4 (by decide)]
    change stdSimplex.δ (3 : Fin 4) ≫ dp₃.map = const x
    exact dp₃.δ_map_of_gt 3 (by decide)
  have hz : p₂.MulStruct p₀ r (0 : Fin 2) :=
    { map := stdSimplex.δ (3 : Fin 5) ≫ φ
      δ_castSucc_castSucc_map := by simpa using hf₀
      δ_succ_castSucc_map := by simpa using hf₁
      δ_succ_succ_map := by simpa using hf₂
      δ_map_of_lt := by
        intro j hj
        fin_cases j <;> norm_num at hj
      δ_map_of_gt := by
        intro j hj
        fin_cases j
        · norm_num at hj
        · norm_num at hj
        · norm_num at hj
        · simpa using hf₃ }
  exact hz.toLastSlotTwo.mul_eq.trans h.mul_eq.symm

/-- If every edge is the degenerate edge at `x`, the four faces of every
three-simplex satisfy the native tetrahedral relation. Each face is converted
to the existing canonical pointed two-simplex without changing its map. -/
theorem tetrahedral_relation_of_edges_degenerate
    (x : X _⦋0⦌) (hedge : ∀ s : X _⦋1⦌, s = X.σ 0 x)
    (s : X _⦋3⦌) :
    π.mk (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ 0 s)) *
        π.mk (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ 2 s)) =
      π.mk (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ 3 s)) *
        π.mk (MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ 1 s)) := by
  let p (i : Fin 4) :=
    MinimalFibration.ptTwoOfSimplexOfEdgesDegenerate x hedge (X.δ i s)
  have hp (i : Fin 4) : stdSimplex.δ i ≫ yonedaEquiv.symm s = RelativeMorphism.map (p i) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl
  exact tetrahedral_relation_two (yonedaEquiv.symm s)
    (p 0) (p 1) (p 2) (p 3) (hp 0) (hp 1) (hp 2) (hp 3)

end KanComplex.π

end SSet
