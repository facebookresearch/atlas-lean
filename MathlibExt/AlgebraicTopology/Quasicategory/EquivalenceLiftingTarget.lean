/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLifting
public import MathlibExt.AlgebraicTopology.Quasicategory.RelativeOuterHornN2

/-!
# Target-prescribed strict equivalence-edge lifting

An inner fibration with quasicategory codomain and strict source-prescribed
equivalence lifting also lifts equivalences with a prescribed target.
The target vertex, its preimage equality and the actual image edge are
retained. Source quasicategory structure is inferred from the inner
fibration and its codomain.

For `g : y ⟶ p(x)`, lift its inverse `b` to `f : x ⟶ x'`. The complete
base unit triangle `(g, b, id_y)` extends the right two-horn with source
faces `d₀ = f`, `d₁ = id_x'`. Its missing face is `a : x' ⟶ x`, and the
source triangle gives `[a] ≫ [f] = id_x'`. Cancellation of the invertible
`[f]` proves that `a` is an equivalence. This is a project derivation of
the scoped endpoint symmetry in Cisinski Proposition 3.3.18.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Strict equivalence lifting with prescribed target for an inner
fibration with quasicategory codomain. The source vertex equality and
the equality of actual image `1`-simplices are explicit. -/
theorem HasStrictEquivalenceLifting.exists_lift_target {X Y : SSet.{u}}
    {p : X ⟶ Y} [InnerFibration p] [Quasicategory Y]
    [HasStrictEquivalenceLifting p] {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (g : Edge y (p.app (op ⦋0⦌) x)) (hg : g.IsEquivalence) :
    ∃ (x' : X _⦋0⦌) (_ : p.app (op ⦋0⦌) x' = y) (a : Edge x' x),
      a.IsEquivalence ∧ (a.map p).edge = g.edge := by
  obtain ⟨I⟩ := hg.nonempty_invStruct
  obtain ⟨x', hx', f, hf, hfb⟩ :=
    HasStrictEquivalenceLifting.exists_lift I.inv I.invStructInv.isEquivalence
  let F : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm f.edge
  let H : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm (Edge.id x').edge
  let B : (Δ[2] : SSet.{u}) ⟶ Y := yonedaEquiv.symm I.homInvId.simplex
  have hHF : stdSimplex.δ (0 : Fin 2) ≫ H = stdSimplex.δ (0 : Fin 2) ≫ F := by
    dsimp only [H, F]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm, Edge.tgt_eq, f.tgt_eq]
  obtain ⟨σ₀, σ₀1, σ₀0⟩ := horn₂₂.isPushout.exists_desc H F hHF
  have hF : F ≫ p = stdSimplex.δ (0 : Fin 3) ≫ B := by
    dsimp only [F, B]
    rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, I.homInvId.d₀]
    change yonedaEquiv.symm (f.map p).edge = yonedaEquiv.symm I.inv.edge
    rw [hfb]
  have hH : H ≫ p = stdSimplex.δ (1 : Fin 3) ≫ B := by
    dsimp only [H, B]
    rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, I.homInvId.d₁,
      ← Edge.map_edge, Edge.map_id, hx']
  have hsq : σ₀ ≫ p = Λ[2, 2].ι ≫ B := by
    apply horn.hom_ext'
    intro j hj
    fin_cases j <;> simp only [Fin.isValue, Fin.reduceFinMk]
    · rw [← Category.assoc, σ₀0, horn.ι_ι_assoc]
      exact hF
    · rw [← Category.assoc, σ₀1, horn.ι_ι_assoc]
      exact hH
    · exact (hj rfl).elim
  have hcritical : (Edge.mk'
      (yonedaEquiv (horn.ι 2 0 (by decide) ≫ σ₀))).IsEquivalence := by
    rw [σ₀0]
    exact hf.of_edge_eq (by dsimp only [F]; rw [Equiv.apply_symm_apply]; rfl)
  obtain ⟨σ, hσhorn, hσbase⟩ :=
    exists_fill_relativeSpecialOuterHorn_two_two σ₀ B hsq hcritical
  have σ0 : stdSimplex.δ (0 : Fin 3) ≫ σ = F := by
    rw [← σ₀0, ← hσhorn, horn.ι_ι_assoc]
  have σ1 : stdSimplex.δ (1 : Fin 3) ≫ σ = H := by
    rw [← σ₀1, ← hσhorn, horn.ι_ι_assoc]
  have s0 : X.δ 0 (yonedaEquiv σ) = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, σ0]
    exact Equiv.apply_symm_apply _ _
  have s1 : X.δ 1 (yonedaEquiv σ) = (Edge.id x').edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, σ1]
    exact Equiv.apply_symm_apply _ _
  obtain ⟨z₀, z₁, z₂, a₀, f₀, h, c, hc⟩ :=
    Edge.CompStruct.exists_of_simplex (yonedaEquiv σ)
  have hf₀ : f₀.edge = f.edge := by rw [← c.d₀, hc]; exact s0
  have hh : h.edge = (Edge.id x').edge := by rw [← c.d₁, hc]; exact s1
  have hz₀ : z₀ = x' := by rw [← h.src_eq, hh, Edge.src_eq]
  have hz₁ : z₁ = x := by rw [← f₀.src_eq, hf₀, f.src_eq]
  let a : Edge x' x := a₀.ofEq hz₀ hz₁
  have ca : Edge.CompStruct a f (Edge.id x') := c.ofEq rfl hf₀ hh
  have ha : a.IsEquivalence := by
    have : IsIso (HomotopyCategory.homMk f) := hf
    have : IsIso (HomotopyCategory.homMk a ≫ HomotopyCategory.homMk f) := by
      rw [HomotopyCategory.homMk_comp_homMk ca, HomotopyCategory.homMk_id]
      infer_instance
    exact IsIso.of_isIso_comp_right (HomotopyCategory.homMk a) (HomotopyCategory.homMk f)
  have hBase : p.app (op ⦋2⦌) (yonedaEquiv σ) = I.homInvId.simplex := by
    simpa only [B, yonedaEquiv_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv hσbase
  have haedge : a.edge = X.δ 2 (yonedaEquiv σ) := by
    change a₀.edge = X.δ 2 (yonedaEquiv σ)
    rw [← c.d₂, hc]
  refine ⟨x', hx', a, ha, ?_⟩
  rw [Edge.map_edge, haedge]
  calc
    p.app _ (X.δ 2 (yonedaEquiv σ)) = Y.δ 2 (p.app _ (yonedaEquiv σ)) :=
      NatTrans.naturality_apply p (SimplexCategory.δ (2 : Fin 3)).op _
    _ = g.edge := by rw [hBase, I.homInvId.d₂]

end SSet
