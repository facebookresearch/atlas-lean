/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeSpecialOuterHornRight
public import MathlibExt.AlgebraicTopology.SimplicialSet.HornOpposite
public import MathlibExt.AlgebraicTopology.Quasicategory.Opposite
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Opposite transport for strict relative outer horns

The generic opposite-horn square and filler equivalences carry a relative
left outer-horn problem to a relative right outer-horn problem. Reversal sends
the critical edge to the opposite critical edge. Applying the right theorem
and transporting its filler back preserves both the horn restriction and the
complete prescribed base simplex in every dimension at least two.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

private lemma horn_rev_zero_eq (n : ℕ) :
    Λ[n + 2, (0 : Fin (n + 3)).rev] = Λ[n + 2, Fin.last (n + 2)] := by
  rw [Fin.rev_zero]

private lemma opIso_inv_app_vertex (m : ℕ)
    (g : (Δ[m] : SSet.{u}) _⦋1⦌) (i : Fin 2) :
    (show (Δ[m] : SSet.{u}) _⦋1⦌ from
      (stdSimplex.opIso.{u} ⦋m⦌).inv.app _ g) i = (g i.rev).rev := by
  have h1 : (show (Δ[m] : SSet.{u}) _⦋1⦌ from
      (stdSimplex.opIso.{u} ⦋m⦌).inv.app _ g) =
      (show (Δ[m] : SSet.{u}) _⦋1⦌ from
        stdSimplex.opObjEquiv.{u, u}.symm g) := rfl
  rw [h1]
  exact stdSimplex.opObjEquiv_opObjEquiv_symm_apply.{u, u} g i

private lemma opIso_inv_app_edge {m : ℕ}
    (a b : Fin (m + 1)) (h : a ≤ b) (h' : b.rev ≤ a.rev) :
    (show (Δ[m] : SSet.{u}) _⦋1⦌ from
      (stdSimplex.opIso.{u} ⦋m⦌).inv.app _
        (stdSimplex.edge m a b h)) =
      stdSimplex.edge m b.rev a.rev h' := by
  refine stdSimplex.ext _ _ (fun i => ?_)
  rw [opIso_inv_app_vertex]
  fin_cases i
  · change ((stdSimplex.edge.{u} m a b h) 1).rev =
      (stdSimplex.edge.{u} m b.rev a.rev h') 0
    rfl
  · change ((stdSimplex.edge.{u} m a b h) 0).rev =
      (stdSimplex.edge.{u} m b.rev a.rev h') 1
    rfl

private lemma opIso_inv_rightHornEdgeSimplex (n : ℕ) :
    (stdSimplex.opIso ⦋n + 2⦌).inv.app _
        (rightHornEdgeSimplex.{u} n).val =
      (leftHornEdgeSimplex.{u} n).val := by
  have hright : (rightHornEdgeSimplex.{u} n).val =
      stdSimplex.edge (n + 2)
        (⟨n + 1, by omega⟩ : Fin (n + 3))
        (Fin.last (n + 2)) (by simp [Fin.le_def]) := rfl
  have hleft : (leftHornEdgeSimplex.{u} n).val =
      stdSimplex.edge (n + 2) (0 : Fin (n + 3))
        (⟨1, by omega⟩ : Fin (n + 3)) (Fin.zero_le _) := rfl
  rw [hright, hleft]
  have hrLast :
      (Fin.last (n + 2) : Fin (n + 3)).rev = 0 := by
    ext
    simp
  have hrSucc :
      ((⟨n + 1, by omega⟩ : Fin (n + 3))).rev = 1 := by
    ext
    simp
  have happ := opIso_inv_app_edge
    (⟨n + 1, by omega⟩ : Fin (n + 3)) (Fin.last (n + 2))
    (by simp [Fin.le_def])
    (by rw [hrLast, hrSucc]; exact Fin.zero_le _)
  simp only [hrLast, hrSucc] at happ
  exact happ

/-- At the zero horn, the generic opposite-square equivalence carries the
left critical edge to the right critical edge, with its orientation reversed. -/
lemma rightHornEdge_opArrowHomEquiv_zero
    {C D : SSet.{u}} {q : C ⟶ D} {n : ℕ}
    (sq : Arrow.mk Λ[n + 2, (0 : Fin (n + 3))].ι ⟶ Arrow.mk q) :
    let σOp : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ C.op :=
      (Subcomplex.eqToIso (by rw [Fin.rev_zero])).inv ≫
        (horn.opArrowHomEquiv
          (n + 2) (0 : Fin (n + 3)) q sq).left
    (rightHornEdge σOp).edge =
      opObjEquiv.symm (leftHornEdge sq.left).edge := by
  dsimp only
  rw [rightHornEdge_edge, horn.opArrowHomEquiv_apply_left]
  let eEq := Subcomplex.eqToIso (horn_rev_zero_eq n)
  let eHorn := hornOppositeIso (n + 2) (0 : Fin (n + 3))
  let eLeft := eEq.inv ≫ eHorn.inv
  have hEq_ι : eEq.inv ≫
      Λ[n + 2, (0 : Fin (n + 3)).rev].ι =
        Λ[n + 2, Fin.last (n + 2)].ι :=
    Subcomplex.homOfLE_ι (horn_rev_zero_eq n).symm.le
  have hι : eLeft ≫ opFunctor.map Λ[n + 2, (0 : Fin (n + 3))].ι =
      Λ[n + 2, Fin.last (n + 2)].ι ≫
        (stdSimplex.opIso ⦋n + 2⦌).inv := by
    dsimp only [eLeft, eHorn, eEq]
    calc
      (Subcomplex.eqToIso (horn_rev_zero_eq n)).inv ≫
          (hornOppositeIso (n + 2) (0 : Fin (n + 3))).inv ≫
            opFunctor.map Λ[n + 2, (0 : Fin (n + 3))].ι =
        (Subcomplex.eqToIso (horn_rev_zero_eq n)).inv ≫
          ((hornOppositeIso (n + 2) (0 : Fin (n + 3))).inv ≫
            opFunctor.map Λ[n + 2, (0 : Fin (n + 3))].ι) :=
          rfl
      _ = (Subcomplex.eqToIso (horn_rev_zero_eq n)).inv ≫
          (Λ[n + 2, (0 : Fin (n + 3)).rev].ι ≫
            (stdSimplex.opIso ⦋n + 2⦌).inv) := by
          rw [horn.opArrowIso_inv_ι]
      _ = ((Subcomplex.eqToIso (horn_rev_zero_eq n)).inv ≫
          Λ[n + 2, (0 : Fin (n + 3)).rev].ι) ≫
            (stdSimplex.opIso ⦋n + 2⦌).inv :=
          (Category.assoc _ _ _).symm
      _ = _ := by rw [hEq_ι]
  have hamb := congrArg
    (fun z => z.app (op ⦋1⦌) (rightHornEdgeSimplex n)) hι
  have hval : (eLeft.app _ (rightHornEdgeSimplex n)).val =
      (show (Δ[n + 2] : SSet.{u}) _⦋1⦌ from
        (stdSimplex.opIso ⦋n + 2⦌).inv.app _
          (rightHornEdgeSimplex n).val) := by
    exact hamb
  change (opFunctor.map sq.left).app _
      (eLeft.app _ (rightHornEdgeSimplex n)) =
    opObjEquiv.symm (leftHornEdge sq.left).edge
  rw [opFunctor_map]
  congr 1
  have hφ : opObjEquiv (eLeft.app _ (rightHornEdgeSimplex n)) =
      leftHornEdgeSimplex n := by
    refine Subtype.ext ?_
    change (eLeft.app _ (rightHornEdgeSimplex n)).val =
      (leftHornEdgeSimplex n).val
    rw [hval]
    exact opIso_inv_rightHornEdgeSimplex n
  rw [hφ, leftHornEdge_edge]


/-- Strict relative left special outer horn filling in every dimension at
least two, obtained from the right theorem by opposite transport. Both the horn
restriction and the complete prescribed base simplex are preserved. -/
theorem exists_fill_relativeSpecialOuterHorn_left_of_isEquivalence
    {C D : SSet.{u}} {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    {n : ℕ}
    (σ₀ : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ C)
    (σBar : (Δ[n + 2] : SSet.{u}) ⟶ D)
    (hsq : σ₀ ≫ q =
      Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σBar)
    (h : (leftHornEdge σ₀).IsEquivalence) :
    ∃ σ : (Δ[n + 2] : SSet.{u}) ⟶ C,
      Λ[n + 2, (0 : Fin (n + 3))].ι ≫ σ = σ₀ ∧
        σ ≫ q = σBar := by
  let _ : Quasicategory C := quasicategory_of_innerFibration q
  let _ : Quasicategory C.op := quasicategory_op C
  let _ : Quasicategory D.op := quasicategory_op D
  let _ : InnerFibration (opFunctor.map q) := InnerFibration.op
  let sq : Arrow.mk Λ[n + 2, (0 : Fin (n + 3))].ι ⟶ Arrow.mk q :=
    { left := σ₀
      right := σBar
      w := hsq }
  let sqOp₀ := horn.opArrowHomEquiv
    (n + 2) (0 : Fin (n + 3)) q sq
  have hrev : (0 : Fin (n + 3)).rev = Fin.last (n + 2) := Fin.rev_zero (n + 2)
  cases hrev
  let sqOp : Arrow.mk Λ[n + 2, Fin.last (n + 2)].ι ⟶
      Arrow.mk (opFunctor.map q) := sqOp₀
  have hedge : (rightHornEdge sqOp.left).IsEquivalence := by
    have he := rightHornEdge_opArrowHomEquiv_zero sq
    have he' : (rightHornEdge sqOp.left).edge = ((leftHornEdge σ₀).op).edge := by
      rw [Edge.op_edge]
      exact he
    exact (Edge.isEquivalence_iff_of_edge_eq he').mpr h.op
  obtain ⟨σ', hleft, hright⟩ :=
    exists_fill_relativeSpecialOuterHorn_right_of_isEquivalence
      (q := opFunctor.map q) sqOp.left sqOp.right sqOp.w hedge
  let lOp : Arrow.LiftStruct sqOp :=
    { l := σ'
      fac_left := hleft
      fac_right := hright }
  let l : Arrow.LiftStruct sq :=
    (horn.opLiftStructEquiv sq).symm lOp
  exact ⟨l.l, l.fac_left, l.fac_right⟩


end SSet
