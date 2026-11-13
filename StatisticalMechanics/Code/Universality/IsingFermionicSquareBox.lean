/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicMedialComplex
import Code.FrontierD.FKQgt4SquareFiniteDuality
import Code.Lattice.EarContraction
import Mathlib.Combinatorics.SimpleGraph.Matching










namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


inductive FKIsingSquareBoundarySide
  | bottom | right | top | left
deriving DecidableEq, Fintype




abbrev FKIsingSquareBoundaryIndex (n : Nat) :=
  FKIsingSquareBoundarySide × Fin (2 * n)

private theorem centered_offset_natAbs_le (n : Nat) (k : Fin (2 * n)) :
    ((k.val : Int) - (n : Int)).natAbs ≤ n := by
  have hk : k.val < 2 * n := k.isLt
  have hlo : -(n : Int) ≤ (k.val : Int) - (n : Int) := by omega
  have hhi : (k.val : Int) - (n : Int) ≤ (n : Int) := by omega
  have habs : |(k.val : Int) - (n : Int)| ≤ (n : Int) :=
    abs_le.mpr ⟨hlo, hhi⟩
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

private theorem centered_reverse_natAbs_le (n : Nat) (k : Fin (2 * n)) :
    ((n : Int) - (k.val : Int)).natAbs ≤ n := by
  rw [show (n : Int) - (k.val : Int) = -((k.val : Int) - n) by ring,
    Int.natAbs_neg]
  exact centered_offset_natAbs_le n k


def fkIsingSquareBoundarySite (n : Nat) :
    FKIsingSquareBoundaryIndex n -> Site 2
  | (.bottom, k) => ![(k.val : Int) - n, -(n : Int)]
  | (.right, k) => ![(n : Int), (k.val : Int) - n]
  | (.top, k) => ![(n : Int) - k.val, (n : Int)]
  | (.left, k) => ![-(n : Int), (n : Int) - k.val]

theorem fkIsingSquareBoundarySite_mem_box (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundarySite n i ∈ box 2 n := by
  rcases i with ⟨side, k⟩
  cases side <;> intro j <;> fin_cases j <;>
    simp [fkIsingSquareBoundarySite, centered_offset_natAbs_le,
      centered_reverse_natAbs_le]



def fkIsingSquareBoundaryVertex (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    (fkSquareBoxPlanar n).V :=
  ⟨fkIsingSquareBoundarySite n i, fkIsingSquareBoundarySite_mem_box n i⟩


def fkIsingSquareBoundaryOrderKey (n : Nat) :
    FKIsingSquareBoundaryIndex n -> Nat
  | (.bottom, k) => k.val
  | (.right, k) => 2 * n + k.val
  | (.top, k) => 4 * n + k.val
  | (.left, k) => 6 * n + k.val

theorem fkIsingSquareBoundaryOrderKey_lt (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundaryOrderKey n i < 8 * n := by
  rcases i with ⟨side, k⟩
  have hk := k.isLt
  cases side <;> simp [fkIsingSquareBoundaryOrderKey] <;> omega

theorem fkIsingSquareBoundaryOrderKey_injective (n : Nat) :
    Function.Injective (fkIsingSquareBoundaryOrderKey n) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ h
  cases s <;> cases t <;> simp [fkIsingSquareBoundaryOrderKey] at h ⊢ <;>
    try omega


def fkIsingSquareBoundaryOrderFin (n : Nat) :
    FKIsingSquareBoundaryIndex n -> Fin (8 * n) :=
  fun i => ⟨fkIsingSquareBoundaryOrderKey n i,
    fkIsingSquareBoundaryOrderKey_lt n i⟩

theorem fkIsingSquareBoundaryOrderFin_bijective (n : Nat) :
    Function.Bijective (fkIsingSquareBoundaryOrderFin n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro i j h
    apply fkIsingSquareBoundaryOrderKey_injective n
    exact Fin.mk.inj h
  · simp [FKIsingSquareBoundaryIndex]
    have hcard : Fintype.card FKIsingSquareBoundarySide = 4 := by
      decide
    rw [hcard]
    omega



def fkIsingSquareBoundaryOrderEquiv (n : Nat) :
    FKIsingSquareBoundaryIndex n ≃ Fin (8 * n) :=
  Equiv.ofBijective (fkIsingSquareBoundaryOrderFin n)
    (fkIsingSquareBoundaryOrderFin_bijective n)


def fkIsingSquareBoundarySucc (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareBoundaryIndex n) :=
  (fkIsingSquareBoundaryOrderEquiv n).trans
    ((svFinitePeriodicSuccEquiv (by omega : 0 < 8 * n)).trans
      (fkIsingSquareBoundaryOrderEquiv n).symm)


def fkIsingSquareBoundaryOrder (n : Nat) :
    List (FKIsingSquareBoundaryIndex n) :=
  List.ofFn fun i : Fin (8 * n) =>
    (fkIsingSquareBoundaryOrderEquiv n).symm i

theorem fkIsingSquareBoundaryOrder_length (n : Nat) :
    (fkIsingSquareBoundaryOrder n).length = 8 * n := by
  simp [fkIsingSquareBoundaryOrder]

theorem fkIsingSquareBoundaryOrder_nodup (n : Nat) :
    (fkIsingSquareBoundaryOrder n).Nodup := by
  unfold fkIsingSquareBoundaryOrder
  exact List.nodup_ofFn.mpr
    (fkIsingSquareBoundaryOrderEquiv n).symm.injective

theorem fkIsingSquareBoundarySucc_ne (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundarySucc n hn i ≠ i := by
  intro h
  have h' := congrArg (fkIsingSquareBoundaryOrderEquiv n) h
  have hsucc : finitePeriodicSucc (by omega : 0 < 8 * n)
      (fkIsingSquareBoundaryOrderEquiv n i) =
        fkIsingSquareBoundaryOrderEquiv n i := by
    simpa [fkIsingSquareBoundarySucc] using h'
  exact finitePeriodicSucc_ne_self (by omega : 1 < 8 * n) _ hsucc


def fkIsingSquareMarkedA (n : Nat) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), -(n : Int)], by
    intro i
    fin_cases i <;> simp⟩


def fkIsingSquareMarkedB (n : Nat) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), (n : Int)], by
    intro i
    fin_cases i <;> simp⟩


def fkIsingSquareMarkedAIndex (n : Nat) (hn : 0 < n) :
    FKIsingSquareBoundaryIndex n :=
  (.bottom, ⟨0, by omega⟩)


def fkIsingSquareMarkedBIndex (n : Nat) (hn : 0 < n) :
    FKIsingSquareBoundaryIndex n :=
  (.left, ⟨0, by omega⟩)

theorem fkIsingSquareBoundaryVertex_markedA (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedAIndex n hn) =
      fkIsingSquareMarkedA n := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [fkIsingSquareBoundaryVertex, fkIsingSquareMarkedAIndex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedA]

theorem fkIsingSquareBoundaryVertex_markedB (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedBIndex n hn) =
      fkIsingSquareMarkedB n := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [fkIsingSquareBoundaryVertex, fkIsingSquareMarkedBIndex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedB]


def fkIsingSquareWiredArc (n : Nat) (x : (fkSquareBoxPlanar n).V) : Prop :=
  (x.1 0) = -(n : Int)

theorem fkIsingSquareMarkedA_mem_wiredArc (n : Nat) :
    fkIsingSquareWiredArc n (fkIsingSquareMarkedA n) := by
  rfl

theorem fkIsingSquareMarkedB_mem_wiredArc (n : Nat) :
    fkIsingSquareWiredArc n (fkIsingSquareMarkedB n) := by
  rfl

theorem fkIsingSquareBoundary_left_mem_wiredArc (n : Nat)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredArc n
      (fkIsingSquareBoundaryVertex n (.left, k)) := by
  rfl




def fkIsingSquareWiredExteriorStar (n : Nat) :
    SimpleGraph (fkSquareBoxPlanar n).V where
  Adj x y := x ≠ y ∧ fkIsingSquareWiredArc n x ∧
    fkIsingSquareWiredArc n y ∧
      (x = fkIsingSquareMarkedA n ∨ y = fkIsingSquareMarkedA n)
  symm := by
    rintro x y ⟨hne, hx, hy, hroot⟩
    exact ⟨hne.symm, hy, hx, hroot.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem fkIsingSquareWiredExteriorStar_le_clique (n : Nat) :
    fkIsingSquareWiredExteriorStar n ≤
      boundaryCliqueGraph (fkIsingSquareWiredArc n) := by
  classical
  intro x y hxy
  rw [boundaryCliqueGraph_adj]
  exact ⟨hxy.1, hxy.2.1, hxy.2.2.1⟩


theorem fkIsingSquareWiredExteriorStar_reachable
    (n : Nat) {x y : (fkSquareBoxPlanar n).V}
    (hx : fkIsingSquareWiredArc n x)
    (hy : fkIsingSquareWiredArc n y) :
    (fkIsingSquareWiredExteriorStar n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact Reachable.refl _
  by_cases hxa : x = fkIsingSquareMarkedA n
  · exact (show (fkIsingSquareWiredExteriorStar n).Adj x y by
      exact ⟨hxy, hx, hy, Or.inl hxa⟩).reachable
  by_cases hya : y = fkIsingSquareMarkedA n
  · exact (show (fkIsingSquareWiredExteriorStar n).Adj x y by
      exact ⟨hxy, hx, hy, Or.inr hya⟩).reachable
  have hxa' : (fkIsingSquareWiredExteriorStar n).Adj x
      (fkIsingSquareMarkedA n) := by
    exact ⟨hxa, hx, fkIsingSquareMarkedA_mem_wiredArc n, Or.inr rfl⟩
  have hay : (fkIsingSquareWiredExteriorStar n).Adj
      (fkIsingSquareMarkedA n) y := by
    exact ⟨Ne.symm hya, fkIsingSquareMarkedA_mem_wiredArc n, hy,
      Or.inl rfl⟩
  exact hxa'.reachable.trans hay.reachable

private theorem reachable_of_adj_reachable_square
    {V : Type*} {G K : SimpleGraph V}
    (hstep : ∀ {u v}, G.Adj u v → K.Reachable u v)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih



theorem fkIsingSquare_sup_wiredExteriorStar_reachable_iff_clique
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    (x y : (fkSquareBoxPlanar n).V) :
    (H ⊔ fkIsingSquareWiredExteriorStar n).Reachable x y ↔
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
  classical
  constructor
  · exact fun h => h.mono (sup_le_sup_left
      (fkIsingSquareWiredExteriorStar_le_clique n) H)
  · intro h
    apply reachable_of_adj_reachable_square (G :=
      H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)) (K :=
      H ⊔ fkIsingSquareWiredExteriorStar n) ?_ h
    intro u v huv
    rcases huv with hH | hclique
    · exact Adj.reachable (show (H ⊔ fkIsingSquareWiredExteriorStar n).Adj u v from
        Or.inl hH)
    · rw [boundaryCliqueGraph_adj] at hclique
      exact (fkIsingSquareWiredExteriorStar_reachable n
        hclique.2.1 hclique.2.2).mono le_sup_right


inductive FKIsingSquareWiredGadgetVertex (n : Nat)
  | physical : (fkSquareBoxPlanar n).V → FKIsingSquareWiredGadgetVertex n
  | exteriorRoot : FKIsingSquareWiredGadgetVertex n
deriving DecidableEq, Fintype


def fkIsingSquareWiredExteriorGadget (n : Nat) :
    SimpleGraph (FKIsingSquareWiredGadgetVertex n) where
  Adj x y :=
    (∃ v, fkIsingSquareWiredArc n v ∧
      x = .exteriorRoot ∧ y = .physical v) ∨
    (∃ v, fkIsingSquareWiredArc n v ∧
      y = .exteriorRoot ∧ x = .physical v)
  symm := by
    intro x y h
    rcases h with ⟨v, hv, rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
    · exact Or.inr ⟨v, hv, rfl, rfl⟩
    · exact Or.inl ⟨v, hv, rfl, rfl⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨v, _, hroot, hphysical⟩ |
      ⟨v, _, hroot, hphysical⟩ <;>
      cases hroot <;> cases hphysical⟩


def fkIsingSquareLiftPhysicalGraph (n : Nat)
    (H : SimpleGraph (fkSquareBoxPlanar n).V) :
    SimpleGraph (FKIsingSquareWiredGadgetVertex n) where
  Adj x y := ∃ u v, x = .physical u ∧ y = .physical v ∧ H.Adj u v
  symm := by
    rintro x y ⟨u, v, rfl, rfl, huv⟩
    exact ⟨v, u, rfl, rfl, huv.symm⟩
  loopless := ⟨by
    rintro x ⟨u, v, hx, hy, huv⟩
    subst x
    cases hy
    exact H.irrefl huv⟩


def fkIsingSquareWiredGadgetProjection (n : Nat) :
    FKIsingSquareWiredGadgetVertex n → (fkSquareBoxPlanar n).V
  | .physical v => v
  | .exteriorRoot => fkIsingSquareMarkedA n


theorem fkIsingSquareWiredGadgetProjection_reachable
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    {x y : FKIsingSquareWiredGadgetVertex n}
    (hxy : (fkIsingSquareLiftPhysicalGraph n H ⊔
      fkIsingSquareWiredExteriorGadget n).Adj x y) :
    (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredGadgetProjection n x)
      (fkIsingSquareWiredGadgetProjection n y) := by
  classical
  rcases hxy with hphysical | hgadget
  · rcases hphysical with ⟨u, v, rfl, rfl, huv⟩
    exact Adj.reachable (show
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj u v from Or.inl huv)
  · rcases hgadget with ⟨v, hv, rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
    · by_cases h : fkIsingSquareMarkedA n = v
      · subst v
        exact Reachable.refl _
      · exact Adj.reachable (show
          (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj
            (fkIsingSquareMarkedA n) v from
        Or.inr ((boundaryCliqueGraph_adj
          (bdry := fkIsingSquareWiredArc n) _ _).2
            ⟨h, fkIsingSquareMarkedA_mem_wiredArc n, hv⟩))
    · by_cases h : v = fkIsingSquareMarkedA n
      · subst v
        exact Reachable.refl _
      · exact Adj.reachable (show
          (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Adj
            v (fkIsingSquareMarkedA n) from
        Or.inr ((boundaryCliqueGraph_adj
          (bdry := fkIsingSquareWiredArc n) _ _).2
            ⟨h, hv, fkIsingSquareMarkedA_mem_wiredArc n⟩))



theorem fkIsingSquare_wiredExteriorGadget_reachable_iff_clique
    (n : Nat) (H : SimpleGraph (fkSquareBoxPlanar n).V)
    (x y : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareLiftPhysicalGraph n H ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical x) (.physical y) ↔
      (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y := by
  classical
  constructor
  · intro h
    obtain ⟨p⟩ := h
    suffices hwalk : ∀ {u v : FKIsingSquareWiredGadgetVertex n},
        (fkIsingSquareLiftPhysicalGraph n H ⊔
          fkIsingSquareWiredExteriorGadget n).Walk u v →
        (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
          (fkIsingSquareWiredGadgetProjection n u)
          (fkIsingSquareWiredGadgetProjection n v) by
      exact hwalk p
    intro u v q
    induction q with
    | nil => exact Reachable.refl _
    | cons huv q ih =>
        exact (fkIsingSquareWiredGadgetProjection_reachable n H huv).trans ih
  · intro h
    obtain ⟨p⟩ := h
    suffices hwalk : ∀ {u v : (fkSquareBoxPlanar n).V},
        (H ⊔ boundaryCliqueGraph (fkIsingSquareWiredArc n)).Walk u v →
        (fkIsingSquareLiftPhysicalGraph n H ⊔
          fkIsingSquareWiredExteriorGadget n).Reachable
            (.physical u) (.physical v) by
      exact hwalk p
    intro u v q
    induction q with
    | nil => exact Reachable.refl _
    | @cons u v w huv q ih =>
        have hstep : (fkIsingSquareLiftPhysicalGraph n H ⊔
            fkIsingSquareWiredExteriorGadget n).Reachable
              (.physical u) (.physical v) := by
          rcases huv with hH | hclique
          · exact Adj.reachable (show
                (fkIsingSquareLiftPhysicalGraph n H ⊔
                  fkIsingSquareWiredExteriorGadget n).Adj
                    (.physical u) (.physical v) by
              exact Or.inl ⟨u, v, rfl, rfl, hH⟩)
          · rw [boundaryCliqueGraph_adj] at hclique
            have hu : (fkIsingSquareWiredExteriorGadget n).Adj
                (.physical u) .exteriorRoot :=
              Or.inr ⟨u, hclique.2.1, rfl, rfl⟩
            have hv : (fkIsingSquareWiredExteriorGadget n).Adj
                (.exteriorRoot) (.physical v) :=
              Or.inl ⟨v, hclique.2.2, rfl, rfl⟩
            exact Adj.reachable (Or.inr hu) |>.trans (Adj.reachable (Or.inr hv))
        exact hstep.trans ih


def fkIsingSquareAfterA (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).V :=
  fkIsingSquareBoundaryVertex n
    (.bottom, ⟨1, by omega⟩)


def fkIsingSquareAfterB (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).V :=
  fkIsingSquareBoundaryVertex n
    (.left, ⟨1, by omega⟩)

theorem fkIsingSquareMarkedA_adj_afterA (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedA n) (fkIsingSquareAfterA n hn) := by
  change (hypercubicLattice 2).Adj
    (![-(n : Int), -(n : Int)] : Site 2)
    (![(1 : Int) - n, -(n : Int)] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [show -(n : Int) - ((1 : Int) - n) = -1 by ring]

theorem fkIsingSquareMarkedB_adj_afterB (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedB n) (fkIsingSquareAfterB n hn) := by
  change (hypercubicLattice 2).Adj
    (![-(n : Int), (n : Int)] : Site 2)
    (![-(n : Int), (n : Int) - 1] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp


inductive FKIsingSquareEdgeAxis
  | horizontal | vertical
deriving DecidableEq



structure FKIsingSquareEdgeOrientation (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) where
  tail : (fkSquareBoxPlanar n).V
  head : (fkSquareBoxPlanar n).V
  edge_eq : s(tail, head) = e.1
  axis : FKIsingSquareEdgeAxis
  step : match axis with
    | .horizontal => head.1 = tail.1 + ![1, 0]
    | .vertical => head.1 = tail.1 + ![0, 1]



theorem fkIsingSquareOrientedEdge_nonempty (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Nonempty (FKIsingSquareEdgeOrientation n e) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hxy : (hypercubicLattice 2).Adj x.1 y.1 := he
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · refine ⟨⟨y, x, by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩, .horizontal, ?_⟩⟩
      simpa using h
    · refine ⟨⟨x, y, rfl, .horizontal, ?_⟩⟩
      funext i
      fin_cases i
      · have hi := congrFun h 0
        simp [Matrix.cons_val_zero, Pi.add_apply] at hi ⊢
        omega
      · have hi := congrFun h 1
        simp [Matrix.cons_val_one, Pi.add_apply] at hi ⊢
        omega
    · refine ⟨⟨y, x, by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩, .vertical, ?_⟩⟩
      simpa using h
    · refine ⟨⟨x, y, rfl, .vertical, ?_⟩⟩
      funext i
      fin_cases i
      · have hi := congrFun h 0
        simp [Matrix.cons_val_zero, Pi.add_apply] at hi ⊢
        omega
      · have hi := congrFun h 1
        simp [Matrix.cons_val_one, Pi.add_apply] at hi ⊢
        omega


theorem fkIsingSquareOrientedEdge_unique (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (a b : FKIsingSquareEdgeOrientation n e) : a = b := by
  rcases a with ⟨ta, ah, ae, aa, astep⟩
  rcases b with ⟨bt, bh, be, ba, bstep⟩
  have hedge : s(ta, ah) = s(bt, bh) := ae.trans be.symm
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · rcases hsame with ⟨rfl, rfl⟩
    cases aa <;> cases ba
    · rfl
    · exfalso
      have h0 := congrFun (astep.symm.trans bstep) 0
      simp [Matrix.cons_val_zero, Pi.add_apply] at h0
    · exfalso
      have h0 := congrFun (astep.symm.trans bstep) 0
      simp [Matrix.cons_val_zero, Pi.add_apply] at h0
    · rfl
  · rcases hswap with ⟨h1, h2⟩
    cases aa <;> cases ba
    · exfalso
      have ha0 := congrFun astep 0
      have hb0 := congrFun bstep 0
      rw [h1, h2] at ha0
      simp [Matrix.cons_val_zero, Pi.add_apply] at ha0 hb0
      omega
    · exfalso
      have ha0 := congrFun astep 0
      have hb0 := congrFun bstep 0
      rw [h1, h2] at ha0
      simp [Matrix.cons_val_zero, Pi.add_apply] at ha0 hb0
      omega
    · exfalso
      have ha1 := congrFun astep 1
      have hb1 := congrFun bstep 1
      rw [h1, h2] at ha1
      simp [Matrix.cons_val_one, Pi.add_apply] at ha1 hb1
      omega
    · exfalso
      have ha1 := congrFun astep 1
      have hb1 := congrFun bstep 1
      rw [h1, h2] at ha1
      simp [Matrix.cons_val_one, Pi.add_apply] at ha1 hb1
      omega


def fkIsingSquareOrientedEdge (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    FKIsingSquareEdgeOrientation n e :=
  Classical.choice (fkIsingSquareOrientedEdge_nonempty n e)

theorem fkIsingSquareOrientedEdge_eq (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    s((fkIsingSquareOrientedEdge n e).tail,
      (fkIsingSquareOrientedEdge n e).head) = e.1 :=
  (fkIsingSquareOrientedEdge n e).edge_eq



inductive FKIsingSquareEdgeEndpoint
  | tail | head
deriving DecidableEq, Fintype


inductive FKIsingSquareCornerTurn
  | counterclockwise | clockwise
deriving DecidableEq, Fintype




def fkIsingSquareSideCorner :
    FKIsingMedialSide ->
      FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn
  | .west => (.tail, .counterclockwise)
  | .south => (.tail, .clockwise)
  | .east => (.head, .counterclockwise)
  | .north => (.head, .clockwise)


def fkIsingSquareCornerSide :
    FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn ->
      FKIsingMedialSide
  | (.tail, .counterclockwise) => .west
  | (.tail, .clockwise) => .south
  | (.head, .counterclockwise) => .east
  | (.head, .clockwise) => .north

@[simp] theorem fkIsingSquareCornerSide_sideCorner
    (side : FKIsingMedialSide) :
    fkIsingSquareCornerSide (fkIsingSquareSideCorner side) = side := by
  cases side <;> rfl

@[simp] theorem fkIsingSquareSideCorner_cornerSide
    (corner : FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn) :
    fkIsingSquareSideCorner (fkIsingSquareCornerSide corner) = corner := by
  rcases corner with ⟨endpoint, turn⟩
  cases endpoint <;> cases turn <;> rfl



def fkIsingSquareSideCornerEquiv :
    FKIsingMedialSide ≃
      FKIsingSquareEdgeEndpoint × FKIsingSquareCornerTurn where
  toFun := fkIsingSquareSideCorner
  invFun := fkIsingSquareCornerSide
  left_inv := fkIsingSquareCornerSide_sideCorner
  right_inv := fkIsingSquareSideCorner_cornerSide


def fkIsingSquareDartEndpoint (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkSquareBoxPlanar n).V :=
  match (fkIsingSquareSideCorner d.2).1 with
  | .tail => (fkIsingSquareOrientedEdge n d.1).tail
  | .head => (fkIsingSquareOrientedEdge n d.1).head



theorem fkIsingSquareDartEndpoint_mem (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d ∈ d.1.1 := by
  rcases d with ⟨e, side⟩
  have hedge := fkIsingSquareOrientedEdge_eq n e
  rw [← hedge]
  rw [Sym2.mem_iff]
  cases side <;> simp [fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner]


inductive FKIsingSquareDirection
  | east | north | west | south
deriving DecidableEq, Fintype



def fkIsingSquareDirectionAvailable (n : Nat)
    (u : (fkSquareBoxPlanar n).V) : FKIsingSquareDirection -> Prop
  | .east => u.1 0 < (n : Int)
  | .north => u.1 1 < (n : Int)
  | .west => -(n : Int) < u.1 0
  | .south => -(n : Int) < u.1 1

theorem fkIsingSquareVertex_coordinate_bounds (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (i : Fin 2) :
    -(n : Int) ≤ u.1 i ∧ u.1 i ≤ (n : Int) := by
  have hi := u.2 i
  have habs : |u.1 i| ≤ (n : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hi
  exact abs_le.mp habs


noncomputable def fkIsingSquareNextDirection (n : Nat)
    (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) : FKIsingSquareDirection := by
  classical
  exact match d with
  | .east =>
      if fkIsingSquareDirectionAvailable n u .north then .north
      else if fkIsingSquareDirectionAvailable n u .west then .west
      else .south
  | .north =>
      if fkIsingSquareDirectionAvailable n u .west then .west
      else if fkIsingSquareDirectionAvailable n u .south then .south
      else .east
  | .west =>
      if fkIsingSquareDirectionAvailable n u .south then .south
      else if fkIsingSquareDirectionAvailable n u .east then .east
      else .north
  | .south =>
      if fkIsingSquareDirectionAvailable n u .east then .east
      else if fkIsingSquareDirectionAvailable n u .north then .north
      else .west


noncomputable def fkIsingSquarePreviousDirection (n : Nat)
    (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) : FKIsingSquareDirection := by
  classical
  exact match d with
  | .east =>
      if fkIsingSquareDirectionAvailable n u .south then .south
      else if fkIsingSquareDirectionAvailable n u .west then .west
      else .north
  | .north =>
      if fkIsingSquareDirectionAvailable n u .east then .east
      else if fkIsingSquareDirectionAvailable n u .south then .south
      else .west
  | .west =>
      if fkIsingSquareDirectionAvailable n u .north then .north
      else if fkIsingSquareDirectionAvailable n u .east then .east
      else .south
  | .south =>
      if fkIsingSquareDirectionAvailable n u .west then .west
      else if fkIsingSquareDirectionAvailable n u .north then .north
      else .east

theorem fkIsingSquareNextDirection_available (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareDirectionAvailable n u
      (fkIsingSquareNextDirection n u d) := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable] <;> omega

theorem fkIsingSquarePreviousDirection_available (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareDirectionAvailable n u
      (fkIsingSquarePreviousDirection n u d) := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable] <;> omega

theorem fkIsingSquarePreviousDirection_next (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquarePreviousDirection n u
      (fkIsingSquareNextDirection n u d) = d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquareNextDirection_previous (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNextDirection n u
      (fkIsingSquarePreviousDirection n u d) = d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]


def fkIsingSquareNeighborSite (u : Site 2) :
    FKIsingSquareDirection -> Site 2
  | .east => u + ![1, 0]
  | .north => u + ![0, 1]
  | .west => u + ![-1, 0]
  | .south => u + ![0, -1]

theorem fkIsingSquareNeighborSite_mem (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNeighborSite u.1 d ∈ box 2 n := by
  intro i
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have hb : -(n : Int) ≤ fkIsingSquareNeighborSite u.1 d i ∧
      fkIsingSquareNeighborSite u.1 d i ≤ (n : Int) := by
    cases d <;> fin_cases i <;>
      simp [fkIsingSquareNeighborSite, Pi.add_apply,
        fkIsingSquareDirectionAvailable] at hd ⊢ <;>
      omega
  have ha : |fkIsingSquareNeighborSite u.1 d i| ≤ (n : Int) :=
    abs_le.mpr hb
  rw [Int.abs_eq_natAbs] at ha
  exact_mod_cast ha


def fkIsingSquareNeighbor (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    (fkSquareBoxPlanar n).V :=
  ⟨fkIsingSquareNeighborSite u.1 d,
    fkIsingSquareNeighborSite_mem n u d hd⟩

theorem fkIsingSquare_adj_neighbor (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    (fkSquareBoxPlanar n).G.Adj u (fkIsingSquareNeighbor n u d hd) := by
  change (hypercubicLattice 2).Adj u.1
    (fkIsingSquareNeighborSite u.1 d)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  cases d <;> simp [fkIsingSquareNeighborSite, Pi.add_apply]


def fkIsingSquareDirectionEdge (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(u, fkIsingSquareNeighbor n u d hd),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquare_adj_neighbor n u d hd)⟩



def fkIsingSquareDartDirection (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingSquareDirection :=
  match (fkIsingSquareOrientedEdge n d.1).axis,
      (fkIsingSquareSideCorner d.2).1 with
  | .horizontal, .tail => .east
  | .horizontal, .head => .west
  | .vertical, .tail => .north
  | .vertical, .head => .south



theorem fkIsingSquareDartDirection_available (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartDirection n d) := by
  rcases d with ⟨e, side⟩
  have bt0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 0
  have bt1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 1
  have bh0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).head 0
  have bh1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).head 1
  have step := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;> cases side <;>
    simp [fkIsingSquareDartDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner, fkIsingSquareDirectionAvailable,
      haxis] at step ⊢
  all_goals
    try have h0 := congrFun step 0
    try have h1 := congrFun step 1
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    try change (fkIsingSquareOrientedEdge n e).head.1 0 =
      (fkIsingSquareOrientedEdge n e).tail.1 0 + 1 at h0
    try change (fkIsingSquareOrientedEdge n e).head.1 0 =
      (fkIsingSquareOrientedEdge n e).tail.1 0 at h0
    try change (fkIsingSquareOrientedEdge n e).head.1 1 =
      (fkIsingSquareOrientedEdge n e).tail.1 1 + 1 at h1
    try change (fkIsingSquareOrientedEdge n e).head.1 1 =
      (fkIsingSquareOrientedEdge n e).tail.1 1 at h1
    omega


def fkIsingSquareDirectionEdgeOrientation (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    FKIsingSquareEdgeOrientation n
      (fkIsingSquareDirectionEdge n u d hd) := by
  cases d
  · exact ⟨u, fkIsingSquareNeighbor n u .east hd,
      rfl, .horizontal, rfl⟩
  · exact ⟨u, fkIsingSquareNeighbor n u .north hd,
      rfl, .vertical, rfl⟩
  · refine ⟨fkIsingSquareNeighbor n u .west hd, u,
      ?_, .horizontal, ?_⟩
    · change s(fkIsingSquareNeighbor n u .west hd, u) =
        s(u, fkIsingSquareNeighbor n u .west hd)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
    · simp only
      funext i
      fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          Pi.add_apply] <;> rfl
  · refine ⟨fkIsingSquareNeighbor n u .south hd, u,
      ?_, .vertical, ?_⟩
    · change s(fkIsingSquareNeighbor n u .south hd, u) =
        s(u, fkIsingSquareNeighbor n u .south hd)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
    · simp only
      funext i
      fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          Pi.add_apply] <;> rfl



theorem fkIsingSquareOrientedEdge_directionEdge (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareOrientedEdge n
        (fkIsingSquareDirectionEdge n u d hd) =
      fkIsingSquareDirectionEdgeOrientation n u d hd :=
  fkIsingSquareOrientedEdge_unique n _ _ _



def fkIsingSquareEndpointForDirection :
    FKIsingSquareDirection -> FKIsingSquareEdgeEndpoint
  | .east | .north => .tail
  | .west | .south => .head



def fkIsingSquareDirectionDart (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareDirectionEdge n u d hd,
    fkIsingSquareCornerSide (fkIsingSquareEndpointForDirection d, turn))

@[simp] theorem fkIsingSquareDirectionDart_endpoint (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareDirectionDart n u d hd turn) = u := by
  unfold fkIsingSquareDirectionDart fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareDirectionDart_direction (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDartDirection n
      (fkIsingSquareDirectionDart n u d hd turn) = d := by
  unfold fkIsingSquareDirectionDart fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareDirectionDart_turn (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    (fkIsingSquareSideCorner
      (fkIsingSquareDirectionDart n u d hd turn).2).2 = turn := by
  cases d <;> cases turn <;> rfl

theorem fkIsingSquareDirectionDart_congr (n : Nat)
    (u : (fkSquareBoxPlanar n).V) {d e : FKIsingSquareDirection}
    (h : d = e) (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDirectionDart n u d hd turn =
      fkIsingSquareDirectionDart n u e he turn := by
  subst e
  rfl



theorem fkIsingSquareDirectionEdge_reconstruct (n : Nat)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n x)
      (fkIsingSquareDartDirection n x)
      (fkIsingSquareDartDirection_available n x) = x.1 := by
  rcases x with ⟨e, side⟩
  apply Subtype.ext
  rw [← fkIsingSquareOrientedEdge_eq n e]
  have step := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  · simp [haxis] at step
    have haE : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).tail .east := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .west)
    have haW : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).head .west := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .east)
    have hE : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).tail .east haE =
        (fkIsingSquareOrientedEdge n e).head := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).tail.1 + ![1, 0] =
        (fkIsingSquareOrientedEdge n e).head.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    have hW : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).head .west haW =
        (fkIsingSquareOrientedEdge n e).tail := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).head.1 + ![-1, 0] =
        (fkIsingSquareOrientedEdge n e).tail.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    cases side <;> simp [fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      fkIsingSquareDirectionEdge, hE, hW]
  · simp [haxis] at step
    have haN : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).tail .north := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .west)
    have haS : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).head .south := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .east)
    have hN : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).tail .north haN =
        (fkIsingSquareOrientedEdge n e).head := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).tail.1 + ![0, 1] =
        (fkIsingSquareOrientedEdge n e).head.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    have hS : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).head .south haS =
        (fkIsingSquareOrientedEdge n e).tail := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).head.1 + ![0, -1] =
        (fkIsingSquareOrientedEdge n e).tail.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    cases side <;> simp [fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      fkIsingSquareDirectionEdge, hN, hS]



theorem fkIsingSquareDirectionDart_reconstruct (n : Nat)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n x)
      (fkIsingSquareDartDirection n x)
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareSideCorner x.2).2 = x := by
  apply Prod.ext
  · exact fkIsingSquareDirectionEdge_reconstruct n x
  · rcases x with ⟨e, side⟩
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
      cases side <;>
      simp [fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] <;> rfl




noncomputable def fkIsingSquareBondMate (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  let u := fkIsingSquareDartEndpoint n x
  let d := fkIsingSquareDartDirection n x
  let hd := fkIsingSquareDartDirection_available n x
  match (fkIsingSquareSideCorner x.2).2 with
  | .counterclockwise =>
      fkIsingSquareDirectionDart n u
        (fkIsingSquareNextDirection n u d)
        (fkIsingSquareNextDirection_available n hn u d hd) .clockwise
  | .clockwise =>
      fkIsingSquareDirectionDart n u
        (fkIsingSquarePreviousDirection n u d)
        (fkIsingSquarePreviousDirection_available n hn u d hd)
        .counterclockwise

theorem fkIsingSquareBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareBondMate n hn) := by
  intro x
  cases ht : (fkIsingSquareSideCorner x.2).2
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir := fkIsingSquarePreviousDirection_next n hn _ _
      (fkIsingSquareDartDirection_available n x)
    calc
      _ = fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n x)
          (fkIsingSquareDartDirection n x)
          (fkIsingSquareDartDirection_available n x)
          .counterclockwise :=
        fkIsingSquareDirectionDart_congr n _ hdir _ _ _
      _ = x := by
        simpa [ht] using fkIsingSquareDirectionDart_reconstruct n x

  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir := fkIsingSquareNextDirection_previous n hn _ _
      (fkIsingSquareDartDirection_available n x)
    calc
      _ = fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n x)
          (fkIsingSquareDartDirection n x)
          (fkIsingSquareDartDirection_available n x) .clockwise :=
        fkIsingSquareDirectionDart_congr n _ hdir _ _ _
      _ = x := by
        simpa [ht] using fkIsingSquareDirectionDart_reconstruct n x

@[simp] theorem fkIsingSquareDartEndpoint_bondMate
    (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n (fkIsingSquareBondMate n hn x) =
      fkIsingSquareDartEndpoint n x := by
  cases ht : (fkIsingSquareSideCorner x.2).2 <;>
    simp [fkIsingSquareBondMate, ht]

theorem fkIsingSquareNextDirection_ne (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNextDirection n u d ≠ d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquarePreviousDirection_ne (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquarePreviousDirection n u d ≠ d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquareNeighbor_ne (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNeighbor n u d hd ≠ u :=
  (fkIsingSquare_adj_neighbor n u d hd).ne'

theorem fkIsingSquareNeighbor_injective (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (h : fkIsingSquareNeighbor n u d hd =
      fkIsingSquareNeighbor n u e he) : d = e := by
  have hv := congrArg Subtype.val h
  cases d <;> cases e <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hv ⊢

theorem fkIsingSquareDirectionEdge_injective (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (h : fkIsingSquareDirectionEdge n u d hd =
      fkIsingSquareDirectionEdge n u e he) : d = e := by
  have hs : s(u, fkIsingSquareNeighbor n u d hd) =
      s(u, fkIsingSquareNeighbor n u e he) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · exact fkIsingSquareNeighbor_injective n u d e hd he hsame.2
  · exact False.elim
      ((fkIsingSquareNeighbor_ne n u e he) hswap.1.symm)

theorem fkIsingSquareBondMate_edge_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBondMate n hn x).1 ≠ x.1 := by
  intro h
  cases ht : (fkIsingSquareSideCorner x.2).2
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart] at h
    rw [← fkIsingSquareDirectionEdge_reconstruct n x] at h
    exact fkIsingSquareNextDirection_ne n hn _ _
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareDirectionEdge_injective n _ _ _ _ _ h)
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart] at h
    rw [← fkIsingSquareDirectionEdge_reconstruct n x] at h
    exact fkIsingSquarePreviousDirection_ne n hn _ _
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareDirectionEdge_injective n _ _ _ _ _ h)

theorem fkIsingSquareBondMate_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareBondMate n hn x ≠ x := by
  intro h
  exact fkIsingSquareBondMate_edge_ne n hn x (congrArg Prod.fst h)

theorem fkIsingSquareBondMate_cornerTurn_ne (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  cases ht : (fkIsingSquareSideCorner d.2).2 <;>
    simp [fkIsingSquareBondMate, ht, fkIsingSquareDirectionDart_turn]

theorem fkIsingSquareBondMate_ne_localMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareBondMate n hn x ≠
      FKIsingMedialDart.localMate omega x := by
  intro h
  apply fkIsingSquareBondMate_edge_ne n hn x
  have hf := congrArg Prod.fst h
  rcases x with ⟨e, side⟩
  cases ho : omega e.1 <;> cases side <;>
    simpa [FKIsingMedialDart.localMate, ho] using hf


def fkIsingSquareBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) where
  toFun := fkIsingSquareBondMate n hn
  invFun := fkIsingSquareBondMate n hn
  left_inv := fkIsingSquareBondMate_involutive n hn
  right_inv := fkIsingSquareBondMate_involutive n hn


def fkIsingSquareSourcePrimalEdge (n : Nat) (hn : 0 < n) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(fkIsingSquareMarkedA n, fkIsingSquareAfterA n hn),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquareMarkedA_adj_afterA n hn)⟩


def fkIsingSquareTerminalPrimalEdge (n : Nat) (hn : 0 < n) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(fkIsingSquareMarkedB n, fkIsingSquareAfterB n hn),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquareMarkedB_adj_afterB n hn)⟩


def fkIsingSquareSourceEdgeOrientation (n : Nat) (hn : 0 < n) :
    FKIsingSquareEdgeOrientation n (fkIsingSquareSourcePrimalEdge n hn) where
  tail := fkIsingSquareMarkedA n
  head := fkIsingSquareAfterA n hn
  edge_eq := rfl
  axis := .horizontal
  step := by
    funext i
    fin_cases i
    · simp [fkIsingSquareMarkedA, fkIsingSquareAfterA,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]
      ring
    · simp [fkIsingSquareMarkedA, fkIsingSquareAfterA,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]


def fkIsingSquareTerminalEdgeOrientation (n : Nat) (hn : 0 < n) :
    FKIsingSquareEdgeOrientation n (fkIsingSquareTerminalPrimalEdge n hn) where
  tail := fkIsingSquareAfterB n hn
  head := fkIsingSquareMarkedB n
  edge_eq := by
    change s(fkIsingSquareAfterB n hn, fkIsingSquareMarkedB n) =
      s(fkIsingSquareMarkedB n, fkIsingSquareAfterB n hn)
    rw [Sym2.eq_iff]
    exact Or.inr ⟨rfl, rfl⟩
  axis := .vertical
  step := by
    funext i
    fin_cases i <;>
      simp [fkIsingSquareMarkedB, fkIsingSquareAfterB,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]

theorem fkIsingSquareOrientedEdge_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareOrientedEdge n (fkIsingSquareSourcePrimalEdge n hn) =
      fkIsingSquareSourceEdgeOrientation n hn :=
  fkIsingSquareOrientedEdge_unique n _ _ _

theorem fkIsingSquareOrientedEdge_terminal (n : Nat) (hn : 0 < n) :
    fkIsingSquareOrientedEdge n (fkIsingSquareTerminalPrimalEdge n hn) =
      fkIsingSquareTerminalEdgeOrientation n hn :=
  fkIsingSquareOrientedEdge_unique n _ _ _

theorem fkIsingSquareMarkedA_ne_markedB (n : Nat) (hn : 0 < n) :
    fkIsingSquareMarkedA n ≠ fkIsingSquareMarkedB n := by
  intro h
  have h1 := congrArg (fun x : (fkSquareBoxPlanar n).V => x.1 1) h
  simp [fkIsingSquareMarkedA, fkIsingSquareMarkedB] at h1
  omega

theorem fkIsingSquareMarkedA_not_adj_markedB (n : Nat) (hn : 0 < n) :
    ¬(fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedA n) (fkIsingSquareMarkedB n) := by
  change ¬(hypercubicLattice 2).Adj
    (![-(n : Int), -(n : Int)] : Site 2)
    (![-(n : Int), (n : Int)] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp
  omega

private theorem adj_of_mem_edge_of_ne {V : Type*} (G : SimpleGraph V)
    (e : G.edgeSet) {x y : V} (hx : x ∈ e.1) (hy : y ∈ e.1)
    (hxy : x ≠ y) : G.Adj x y := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      rw [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact he
      · exact he.symm
      · exact False.elim (hxy rfl)



inductive FKIsingSquareMedialCarrier (n : Nat)
  | dart : FKIsingMedialDart (fkSquareBoxPlanar n) ->
      FKIsingSquareMedialCarrier n
  | source : FKIsingSquareMedialCarrier n
  | terminal : FKIsingSquareMedialCarrier n
deriving DecidableEq, Fintype


def fkIsingSquareSourceAttachment (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n :=
  .dart (fkIsingSquareSourcePrimalEdge n hn, .west)


def fkIsingSquareTerminalAttachment (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n :=
  .dart (fkIsingSquareTerminalPrimalEdge n hn, .north)

theorem fkIsingSquare_source_ne_terminal (n : Nat) :
    (FKIsingSquareMedialCarrier.source : FKIsingSquareMedialCarrier n) ≠
      .terminal := by
  simp

theorem fkIsingSquare_sourceAttachment_ne_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareSourceAttachment n hn ≠ .source := by
  simp [fkIsingSquareSourceAttachment]

theorem fkIsingSquare_terminalAttachment_ne_terminal (n : Nat) (hn : 0 < n) :
    fkIsingSquareTerminalAttachment n hn ≠ .terminal := by
  simp [fkIsingSquareTerminalAttachment]

@[simp] theorem fkIsingSquareDartEndpoint_sourceAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareSourcePrimalEdge n hn, .west) =
      fkIsingSquareMarkedA n := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_source]
  rfl

@[simp] theorem fkIsingSquareDartEndpoint_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareTerminalPrimalEdge n hn, .north) =
      fkIsingSquareMarkedB n := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_terminal]
  rfl

theorem fkIsingSquareSourceAttachment_ne_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareSourcePrimalEdge n hn, FKIsingMedialSide.west) ≠
      (fkIsingSquareTerminalPrimalEdge n hn, FKIsingMedialSide.north) := by
  intro h
  have he := congrArg (fkIsingSquareDartEndpoint n) h
  apply fkIsingSquareMarkedA_ne_markedB n hn
  simpa using he

theorem fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareSourcePrimalEdge n hn, .west) ≠
      (fkIsingSquareTerminalPrimalEdge n hn, .north) := by
  intro h
  have he := congrArg (fkIsingSquareDartEndpoint n) h
  rw [fkIsingSquareDartEndpoint_bondMate,
    fkIsingSquareDartEndpoint_sourceAttachment] at he
  rw [fkIsingSquareDartEndpoint_terminalAttachment] at he
  exact fkIsingSquareMarkedA_ne_markedB n hn he

theorem fkIsingSquareBondMate_sourceEdge_ne_terminalEdge
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBondMate n hn
      (fkIsingSquareSourcePrimalEdge n hn, .west)).1 ≠
    (fkIsingSquareBondMate n hn
      (fkIsingSquareTerminalPrimalEdge n hn, .north)).1 := by
  intro hedge
  let da := fkIsingSquareBondMate n hn
    (fkIsingSquareSourcePrimalEdge n hn, .west)
  let db := fkIsingSquareBondMate n hn
    (fkIsingSquareTerminalPrimalEdge n hn, .north)
  have haMem : fkIsingSquareMarkedA n ∈ da.1.1 := by
    have hmem := fkIsingSquareDartEndpoint_mem n da
    have hend : fkIsingSquareDartEndpoint n da =
        fkIsingSquareMarkedA n := by
      simp [da]
    rwa [hend] at hmem
  have hbMemDb : fkIsingSquareMarkedB n ∈ db.1.1 := by
    have hmem := fkIsingSquareDartEndpoint_mem n db
    have hend : fkIsingSquareDartEndpoint n db =
        fkIsingSquareMarkedB n := by
      simp [db]
    rwa [hend] at hmem
  have hbMem : fkIsingSquareMarkedB n ∈ da.1.1 := by
    change fkIsingSquareMarkedB n ∈ da.1.1
    rw [hedge]
    exact hbMemDb
  exact fkIsingSquareMarkedA_not_adj_markedB n hn
    (adj_of_mem_edge_of_ne (fkSquareBoxPlanar n).G da.1
      haMem hbMem (fkIsingSquareMarkedA_ne_markedB n hn))

@[simp] theorem fkIsingSquare_localMate_fst
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (FKIsingMedialDart.localMate omega d).1 = d.1 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate, h]

theorem fkIsingSquare_localMate_cornerTurn_ne
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (FKIsingMedialDart.localMate omega d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate, fkIsingSquareSideCorner, h]


def fkIsingSquareSourceInteriorDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareSourcePrimalEdge n hn, .west)


def fkIsingSquareTerminalInteriorDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareTerminalPrimalEdge n hn, .north)



noncomputable def fkIsingSquareCutBondMate (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> FKIsingSquareMedialCarrier n
  | .source => .dart (fkIsingSquareSourceInteriorDart n hn)
  | .terminal => .dart (fkIsingSquareTerminalInteriorDart n hn)
  | .dart d =>
      if d = fkIsingSquareSourceInteriorDart n hn then .source
      else if d = fkIsingSquareTerminalInteriorDart n hn then .terminal
      else if d = fkIsingSquareBondMate n hn
          (fkIsingSquareSourceInteriorDart n hn) then
        .dart (fkIsingSquareBondMate n hn
          (fkIsingSquareTerminalInteriorDart n hn))
      else if d = fkIsingSquareBondMate n hn
          (fkIsingSquareTerminalInteriorDart n hn) then
        .dart (fkIsingSquareBondMate n hn
          (fkIsingSquareSourceInteriorDart n hn))
      else .dart (fkIsingSquareBondMate n hn d)

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareCutBondMate n hn) := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareBondMate_involutive n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABa : a ≠ B a := Ne.symm hBaA
  have hBBb : b ≠ B b := Ne.symm hBbB
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    rw [hInv b] at hh
    exact hBaB hh
  have hBbA : B b ≠ a := Ne.symm hABb
  have hBaBb : B a ≠ B b := by
    intro h
    exact hAB (hInv.injective h)
  have hBbBa : B b ≠ B a := Ne.symm hBaBb
  intro x
  cases x with
  | source =>
      simp [fkIsingSquareCutBondMate, a, b, B, hABa, hAB, hBaA, hBaB]
  | terminal =>
      simp [fkIsingSquareCutBondMate, a, b, B, hAB, hAB.symm,
        hBBb, hBbA, hBbB]
  | dart d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hABa, hAB, hBaA, hBaB]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hAB, hAB.symm,
          hBBb, hBbA, hBbB]
      by_cases hba : d = B a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB,
          hBaBb, hBbA, hBbB, hInv]
      by_cases hbb : d = B b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBbB, hBbA,
          hBbBa, hBaA, hBaB, hInv]
      · have hBdA : B d ≠ a := by
          intro h
          apply hba
          have hh := congrArg B h
          rw [hInv d] at hh
          exact hh
        have hBdB : B d ≠ b := by
          intro h
          apply hbb
          have hh := congrArg B h
          rw [hInv d] at hh
          exact hh
        have hBdBa : B d ≠ B a := by
          intro h
          exact ha (hInv.injective h)
        have hBdBb : B d ≠ B b := by
          intro h
          exact hb (hInv.injective h)
        simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb,
          hBdA, hBdB, hBdBa, hBdBb, hInv]
        exact fkIsingSquareBondMate_involutive n hn d

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareMedialCarrier n) :
    fkIsingSquareCutBondMate n hn x ≠ x := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareBondMate_involutive n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    rw [hInv b] at hh
    exact hBaB hh
  have hBaBb : B a ≠ B b := by
    intro h
    exact hAB ((fkIsingSquareBondMate_involutive n hn).injective h)
  cases x with
  | source => simp [fkIsingSquareCutBondMate]
  | terminal => simp [fkIsingSquareCutBondMate]
  | dart d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareCutBondMate, a]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, hAB.symm]
      by_cases hba : d = B a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB,
          hBaBb, hABb]
        exact Ne.symm hBaBb
      by_cases hbb : d = B b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBbB,
          Ne.symm hABb, Ne.symm hBaBb, hBaA, hBaB]
        exact hBaBb
      · simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb,
          fkIsingSquareBondMate_ne n hn d]


def fkIsingSquareCutBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareMedialCarrier n) where
  toFun := fkIsingSquareCutBondMate n hn
  invFun := fkIsingSquareCutBondMate n hn
  left_inv := fkIsingSquareCutBondMate_involutive n hn
  right_inv := fkIsingSquareCutBondMate_involutive n hn

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_ne_localMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareCutBondMate n hn (.dart d) ≠
      .dart (FKIsingMedialDart.localMate omega d) := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    have hInv := fkIsingSquareBondMate_involutive n hn b
    change B (B b) = b at hInv
    rw [hInv] at hh
    exact hBaB hh
  have hEdge : (B a).1 ≠ (B b).1 :=
    fkIsingSquareBondMate_sourceEdge_ne_terminalEdge n hn
  have hBbBa : B b ≠ B a := by
    intro h
    exact hEdge (congrArg Prod.fst h).symm
  by_cases ha : d = a
  · subst d
    simp [fkIsingSquareCutBondMate, a]
  by_cases hb : d = b
  · subst d
    simp [fkIsingSquareCutBondMate, a, b, hAB.symm]
  by_cases hba : d = B a
  · subst d
    intro h
    simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB, hABb] at h
    have hf := congrArg Prod.fst h
    exact hEdge (by simpa using hf.symm)
  by_cases hbb : d = B b
  · subst d
    intro h
    simp [fkIsingSquareCutBondMate, a, b, B, hBbB, Ne.symm hABb,
      hBbBa, hBaA, hBaB] at h
    have hf := congrArg Prod.fst h
    exact hEdge (by simpa using hf)
  · intro h
    simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb] at h
    exact fkIsingSquareBondMate_ne_localMate n hn omega d h

theorem fkIsingSquareCutBondMate_dart_cornerTurn_ne
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : fkIsingSquareCutBondMate n hn (.dart d) = .dart f) :
    (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  by_cases ha : d = a
  · subst d
    simp [fkIsingSquareCutBondMate, a] at h
  by_cases hb : d = b
  · subst d
    have hba' : b ≠ fkIsingSquareSourceInteriorDart n hn := by
      intro h'
      exact fkIsingSquareSourceAttachment_ne_terminalAttachment n hn h'.symm
    simp [fkIsingSquareCutBondMate, b, hba'] at h
  by_cases hba : d = B a
  · have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
    have hBaB : B a ≠ b :=
      fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
    rw [show d = B a from hba] at h ⊢
    simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB] at h
    subst f
    have hta := fkIsingSquareBondMate_cornerTurn_ne n hn a
    have htb := fkIsingSquareBondMate_cornerTurn_ne n hn b
    have haT : (fkIsingSquareSideCorner a.2).2 = .counterclockwise := by
      simp [a, fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
    have hbT : (fkIsingSquareSideCorner b.2).2 = .clockwise := by
      simp [b, fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
    rw [haT] at hta
    rw [hbT] at htb
    have hBaT : (fkIsingSquareSideCorner (B a).2).2 = .clockwise := by
      cases h' : (fkIsingSquareSideCorner (B a).2).2
      · exact False.elim (hta (by simpa [B] using h'))
      · rfl
    have hBbT : (fkIsingSquareSideCorner (B b).2).2 = .counterclockwise := by
      cases h' : (fkIsingSquareSideCorner (B b).2).2
      · rfl
      · exact False.elim (htb (by simpa [B] using h'))
    rw [hBaT, hBbT]
    decide
  by_cases hbb : d = B b
  · have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
    have hBbA : B b ≠ a := by
      intro hba'
      have hh := congrArg B hba'
      rw [show B (B b) = b from
        fkIsingSquareBondMate_involutive n hn b] at hh
      exact fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment
        n hn hh.symm
    have hBbBa : B b ≠ B a := by
      intro hh
      exact fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
        ((fkIsingSquareBondMate_involutive n hn).injective hh.symm)
    rw [show d = B b from hbb] at h ⊢
    simp [fkIsingSquareCutBondMate, a, b, B, hBbA, hBbB, hBbBa] at h
    subst f
    have hta := fkIsingSquareBondMate_cornerTurn_ne n hn a
    have htb := fkIsingSquareBondMate_cornerTurn_ne n hn b
    have haT : (fkIsingSquareSideCorner a.2).2 = .counterclockwise := by
      simp [a, fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
    have hbT : (fkIsingSquareSideCorner b.2).2 = .clockwise := by
      simp [b, fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
    rw [haT] at hta
    rw [hbT] at htb
    have hBaT : (fkIsingSquareSideCorner (B a).2).2 = .clockwise := by
      cases h' : (fkIsingSquareSideCorner (B a).2).2
      · exact False.elim (hta (by simpa [B] using h'))
      · rfl
    have hBbT : (fkIsingSquareSideCorner (B b).2).2 = .counterclockwise := by
      cases h' : (fkIsingSquareSideCorner (B b).2).2
      · rfl
      · exact False.elim (htb (by simpa [B] using h'))
    rw [hBaT, hBbT]
    decide
  · have ha' : d ≠ fkIsingSquareSourceInteriorDart n hn := by
      simpa [a] using ha
    have hb' : d ≠ fkIsingSquareTerminalInteriorDart n hn := by
      simpa [b] using hb
    have hba' : d ≠ fkIsingSquareBondMate n hn
        (fkIsingSquareSourceInteriorDart n hn) := by simpa [a, B] using hba
    have hbb' : d ≠ fkIsingSquareBondMate n hn
        (fkIsingSquareTerminalInteriorDart n hn) := by simpa [b, B] using hbb
    simp [fkIsingSquareCutBondMate, ha', hb', hba', hbb'] at h
    subst f
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d




def fkIsingSquareLoopGraph (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareMedialCarrier n) where
  Adj x y :=
    (∃ d, x = .dart d ∧
      y = .dart (FKIsingMedialDart.localMate omega d)) ∨
      y = fkIsingSquareCutBondMate n hn x
  symm := by
    intro x y h
    rcases h with ⟨d, rfl, rfl⟩ | rfl
    · left
      refine ⟨FKIsingMedialDart.localMate omega d, rfl, ?_⟩
      rw [FKIsingMedialDart.localMate_involutive]
    · right
      exact (fkIsingSquareCutBondMate_involutive n hn x).symm
  loopless := ⟨by
    intro x h
    rcases h with ⟨d, hx, hy⟩ | h
    · subst x
      injection hy with heq
      exact FKIsingMedialDart.localMate_ne omega d heq.symm
    · exact fkIsingSquareCutBondMate_ne n hn x h.symm⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in


theorem fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hcutW : fkIsingSquareCutBondMate n hn W ≠ S := by
    simpa [W, S, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .west)
  have hcutS : fkIsingSquareCutBondMate n hn S ≠ W := by
    simpa [W, S, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .south)
  have hcutE : fkIsingSquareCutBondMate n hn E ≠ N := by
    simpa [E, N, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .east)
  have hcutN : fkIsingSquareCutBondMate n hn N ≠ E := by
    simpa [E, N, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .north)
  have hcutWr : S ≠ fkIsingSquareCutBondMate n hn W := Ne.symm hcutW
  have hcutSr : W ≠ fkIsingSquareCutBondMate n hn S := Ne.symm hcutS
  have hcutEr : N ≠ fkIsingSquareCutBondMate n hn E := Ne.symm hcutE
  have hcutNr : E ≠ fkIsingSquareCutBondMate n hn N := Ne.symm hcutN
  have hlocal_of_ne
      (d : FKIsingMedialVertex (fkSquareBoxPlanar n)) (hd : d ≠ e) side :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  have hadj_dart
      (rho : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (d : FKIsingMedialDart (fkSquareBoxPlanar n))
      (z : FKIsingSquareMedialCarrier n) :
      (fkIsingSquareLoopGraph n hn rho).Adj (.dart d) z ↔
        z = .dart (FKIsingMedialDart.localMate rho d) ∨
          z = fkIsingSquareCutBondMate n hn (.dart d) := by
    constructor
    · rintro (⟨f, hdf, rfl⟩ | hbond)
      · injection hdf with h
        subst f
        exact Or.inl rfl
      · exact Or.inr hbond
    · rintro (rfl | rfl)
      · exact Or.inl ⟨d, rfl, rfl⟩
      · exact Or.inr rfl
  ext x y
  cases x with
  | source =>
      cases y <;>
        simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj]
  | terminal =>
      cases y <;>
        simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj]
  | dart d =>
      cases y with
      | source =>
          simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj]
      | terminal =>
          simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj]
      | dart f =>
          rcases d with ⟨d, ds⟩
          rcases f with ⟨f, fs⟩
          by_cases hd : d = e <;> by_cases hf : f = e
          · subst d
            subst f
            cases ds <;> cases fs <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                FKIsingMedialDart.localMate, setOpen, setClosed,
                SimpleGraph.deleteEdges_adj,
                SimpleGraph.sup_adj, SimpleGraph.edge_adj,
                hcutW, hcutN, hcutE, hcutS,
                hcutWr, hcutNr, hcutEr, hcutSr]
          · subst d
            cases ds <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                FKIsingMedialDart.localMate, setOpen, setClosed,
                SimpleGraph.deleteEdges_adj,
                SimpleGraph.sup_adj, SimpleGraph.edge_adj, hf]
          · subst f
            have hl := hlocal_of_ne d hd ds
            cases fs <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                hl, SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, hd]
          · have hl := hlocal_of_ne d hd ds
            have hold :
                s((FKIsingSquareMedialCarrier.dart (d, ds)),
                    (FKIsingSquareMedialCarrier.dart (f, fs))) ∉
                  ({s(W, S), s(E, N)} :
                    Set (Sym2 (FKIsingSquareMedialCarrier n))) := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              constructor <;> intro h
              · rcases Sym2.eq_iff.mp h with h | h <;>
                  exact hd
                    (Prod.mk.inj
                      (FKIsingSquareMedialCarrier.dart.inj h.1)).1
              · rcases Sym2.eq_iff.mp h with h | h <;>
                  exact hd
                    (Prod.mk.inj
                      (FKIsingSquareMedialCarrier.dart.inj h.1)).1
            rw [hadj_dart]
            rw [medialTwoEdgeSwitch, SimpleGraph.sup_adj,
              SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj]
            rw [hadj_dart]
            rw [hl]
            simp [hold, SimpleGraph.edge_adj, W, N, E, S, hd, hf]

noncomputable instance fkIsingSquareLoopGraphDecidableAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareLoopGraph n hn omega).Adj :=
  Classical.decRel _

@[simp] theorem fkIsingSquareCutBondMate_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareCutBondMate n hn .source =
      .dart (fkIsingSquareSourceInteriorDart n hn) := rfl

@[simp] theorem fkIsingSquareCutBondMate_terminal
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCutBondMate n hn .terminal =
      .dart (fkIsingSquareTerminalInteriorDart n hn) := rfl

theorem fkIsingSquareLoopGraph_source_adj (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Adj .source
      (.dart (fkIsingSquareSourceInteriorDart n hn)) := by
  exact Or.inr rfl

theorem fkIsingSquareLoopGraph_terminal_adj (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Adj .terminal
      (.dart (fkIsingSquareTerminalInteriorDart n hn)) := by
  exact Or.inr rfl

theorem fkIsingSquareLoopGraph_adj_source_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj .source z ↔
      z = .dart (fkIsingSquareSourceInteriorDart n hn) := by
  change ((∃ d, (.source : FKIsingSquareMedialCarrier n) = .dart d ∧
      z = .dart (FKIsingMedialDart.localMate omega d)) ∨
      z = fkIsingSquareCutBondMate n hn .source) ↔ _
  simp [fkIsingSquareCutBondMate]

theorem fkIsingSquareLoopGraph_adj_terminal_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj .terminal z ↔
      z = .dart (fkIsingSquareTerminalInteriorDart n hn) := by
  change ((∃ d, (.terminal : FKIsingSquareMedialCarrier n) = .dart d ∧
      z = .dart (FKIsingMedialDart.localMate omega d)) ∨
      z = fkIsingSquareCutBondMate n hn .terminal) ↔ _
  simp [fkIsingSquareCutBondMate]

theorem fkIsingSquareLoopGraph_adj_dart_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj (.dart d) z ↔
      z = .dart (FKIsingMedialDart.localMate omega d) ∨
      z = fkIsingSquareCutBondMate n hn (.dart d) := by
  constructor
  · rintro (⟨e, hde, rfl⟩ | hbond)
    · injection hde with he
      subst e
      exact Or.inl rfl
    · exact Or.inr hbond
  · rintro (rfl | rfl)
    · exact Or.inl ⟨d, rfl, rfl⟩
    · exact Or.inr rfl


def fkIsingSquareLocalSmoothingGraph (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareMedialCarrier n) where
  Adj x y := ∃ d, x = .dart d ∧
    y = .dart (FKIsingMedialDart.localMate omega d)
  symm := by
    rintro _ _ ⟨d, rfl, rfl⟩
    refine ⟨FKIsingMedialDart.localMate omega d, rfl, ?_⟩
    rw [FKIsingMedialDart.localMate_involutive]
  loopless := ⟨by
    rintro _ ⟨d, rfl, h⟩
    injection h with h
    exact FKIsingMedialDart.localMate_ne omega d h.symm⟩

@[simp] theorem fkIsingSquareLocalSmoothingGraph_adj_dart_iff
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLocalSmoothingGraph n omega).Adj (.dart d) z ↔
      z = .dart (FKIsingMedialDart.localMate omega d) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    injection hf with h
    subst f
    rfl
  · rintro rfl
    exact ⟨d, rfl, rfl⟩



theorem fkIsingSquareLoopGraph_isAlternating_localSmoothing
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).IsAlternating
      (fkIsingSquareLocalSmoothingGraph n omega) := by
  intro v w w' hne hvw hvw'
  cases v with
  | source =>
      rw [fkIsingSquareLoopGraph_adj_source_iff] at hvw hvw'
      exact False.elim (hne (hvw.trans hvw'.symm))
  | terminal =>
      rw [fkIsingSquareLoopGraph_adj_terminal_iff] at hvw hvw'
      exact False.elim (hne (hvw.trans hvw'.symm))
  | dart d =>
      rw [fkIsingSquareLoopGraph_adj_dart_iff] at hvw hvw'
      rw [fkIsingSquareLocalSmoothingGraph_adj_dart_iff,
        fkIsingSquareLocalSmoothingGraph_adj_dart_iff]
      rcases hvw with hw | hw <;> rcases hvw' with hw' | hw'
      · exact False.elim (hne (hw.trans hw'.symm))
      · subst w
        subst w'
        simp only [eq_self, true_iff]
        exact fkIsingSquareCutBondMate_ne_localMate n hn omega d
      · subst w
        subst w'
        simp [fkIsingSquareCutBondMate_ne_localMate n hn omega d]
      · exact False.elim (hne (hw.trans hw'.symm))


def fkIsingSquareCarrierOddClass (n : Nat) :
    FKIsingSquareMedialCarrier n -> Prop
  | .source => False
  | .terminal => True
  | .dart d => (fkIsingSquareSideCorner d.2).2 = .counterclockwise

theorem fkIsingSquareLoopGraph_adj_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hxy : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
    fkIsingSquareCarrierOddClass n x ↔
      ¬ fkIsingSquareCarrierOddClass n y := by
  cases x with
  | source =>
      rw [fkIsingSquareLoopGraph_adj_source_iff] at hxy
      subst y
      simp [fkIsingSquareCarrierOddClass,
        fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
  | terminal =>
      rw [fkIsingSquareLoopGraph_adj_terminal_iff] at hxy
      subst y
      simp [fkIsingSquareCarrierOddClass,
        fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
  | dart d =>
      rw [fkIsingSquareLoopGraph_adj_dart_iff] at hxy
      rcases hxy with rfl | hbond
      · simp only [fkIsingSquareCarrierOddClass]
        have hnturn := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;> simp_all
      · cases hy : fkIsingSquareCutBondMate n hn (.dart d) with
        | source =>
            rw [hy] at hbond
            subst y
            have hh := congrArg (fkIsingSquareCutBondMate n hn) hy
            rw [fkIsingSquareCutBondMate_involutive] at hh
            simp [fkIsingSquareCutBondMate] at hh
            subst d
            simp [fkIsingSquareCarrierOddClass,
              fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
        | terminal =>
            rw [hy] at hbond
            subst y
            have hh := congrArg (fkIsingSquareCutBondMate n hn) hy
            rw [fkIsingSquareCutBondMate_involutive] at hh
            simp [fkIsingSquareCutBondMate] at hh
            subst d
            simp [fkIsingSquareCarrierOddClass,
              fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
        | dart f =>
            rw [hy] at hbond
            subst y
            simp only [fkIsingSquareCarrierOddClass]
            have hnturn := fkIsingSquareCutBondMate_dart_cornerTurn_ne
              n hn d f hy
            cases hd : (fkIsingSquareSideCorner d.2).2 <;>
              cases hf : (fkIsingSquareSideCorner f.2).2 <;> simp_all

theorem fkIsingSquareLoopGraph_source_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).degree .source = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset .source =
      {.dart (fkIsingSquareSourceInteriorDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareLoopGraph_adj_source_iff]
  rw [hfin]
  simp

theorem fkIsingSquareLoopGraph_terminal_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).degree .terminal = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset .terminal =
      {.dart (fkIsingSquareTerminalInteriorDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareLoopGraph_adj_terminal_iff]
  rw [hfin]
  simp

theorem fkIsingSquareLoopGraph_dart_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareLoopGraph n hn omega).degree (.dart d) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset (.dart d) =
      {.dart (FKIsingMedialDart.localMate omega d),
        fkIsingSquareCutBondMate n hn (.dart d)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fkIsingSquareLoopGraph_adj_dart_iff n hn omega d z
  rw [hfin]
  exact Finset.card_pair
    (fkIsingSquareCutBondMate_ne_localMate n hn omega d).symm



theorem fkIsingSquareLoopGraph_source_reachable_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Reachable .source .terminal := by
  apply jeb_two_odd_reachable_fin (fkIsingSquareLoopGraph n hn omega)
  · rw [fkIsingSquareLoopGraph_source_degree]
    exact odd_one
  · rw [fkIsingSquareLoopGraph_terminal_degree]
    exact odd_one
  · intro z hsource hterminal
    cases z with
    | source => exact False.elim (hsource rfl)
    | terminal => exact False.elim (hterminal rfl)
    | dart d =>
        rw [fkIsingSquareLoopGraph_dart_degree]
        exact even_two




def fkIsingSquareCompletedLoopGraph (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareMedialCarrier n) :=
  fkIsingSquareLoopGraph n hn omega ⊔
    SimpleGraph.edge .source .terminal

noncomputable instance fkIsingSquareCompletedLoopGraphDecidableAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareCompletedLoopGraph n hn omega).Adj :=
  Classical.decRel _



theorem fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareCompletedLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  rw [fkIsingSquareCompletedLoopGraph,
    fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch]
  ext x y
  cases x <;> cases y <;>
    simp [fkIsingSquareCompletedLoopGraph, medialTwoEdgeSwitch,
      SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]

theorem fkIsingSquareCompletedLoopGraph_reachable_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareCompletedLoopGraph n hn omega).Reachable .source z ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  rw [fkIsingSquareCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨_, hterminal⟩ | ⟨_, hsource⟩)
    · exact h
    · exact (fkIsingSquareLoopGraph_source_reachable_terminal
        n hn omega).trans hterminal
    · exact hsource
  · exact Or.inl

theorem fkIsingSquareCompletedLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree .source = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset .source =
        {.dart (fkIsingSquareSourceInteriorDart n hn), .terminal} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph,
      fkIsingSquareLoopGraph_adj_source_iff, SimpleGraph.edge_adj,
      fkIsingSquare_source_ne_terminal n]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareCompletedLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree .terminal = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset .terminal =
        {.dart (fkIsingSquareTerminalInteriorDart n hn), .source} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph,
      fkIsingSquareLoopGraph_adj_terminal_iff, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareCompletedLoopGraph_dart_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree (.dart d) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset (.dart d) =
        (fkIsingSquareLoopGraph n hn omega).neighborFinset (.dart d) := by
    ext z
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph, SimpleGraph.edge_adj]
  rw [hfin, SimpleGraph.card_neighborFinset_eq_degree,
    fkIsingSquareLoopGraph_dart_degree]

theorem fkIsingSquareCompletedLoopGraph_even_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    Even ((fkIsingSquareCompletedLoopGraph n hn omega).degree z) := by
  cases z with
  | source =>
      rw [fkIsingSquareCompletedLoopGraph_source_degree n hn omega]
      exact even_two
  | terminal =>
      rw [fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega]
      exact even_two
  | dart d =>
      rw [fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d]
      exact even_two


def fkIsingSquareExplorationFinset (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Finset (FKIsingSquareMedialCarrier n) :=
  Finset.univ.filter fun z =>
    (fkIsingSquareLoopGraph n hn omega).Reachable .source z

theorem mem_fkIsingSquareExplorationFinset_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationFinset n hn omega ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  simp [fkIsingSquareExplorationFinset]




theorem fkIsingSquare_open_local_mem_of_closed_west_mem_not_east
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceWest : G.Reachable .source W := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .west))
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact hwest
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply heast
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact hsourceWest.trans h
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G
    (fkIsingSquareCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareExplorationFinset_iff,
    ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2



theorem fkIsingSquare_open_local_mem_of_closed_east_mem_not_west
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceEast : G.Reachable .source E := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .east))
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact heast
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply hwest
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact hsourceEast.trans h.symm
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G
    (fkIsingSquareCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareExplorationFinset_iff,
    ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2



theorem fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceWest : ¬ G.Reachable .source W := by
    simpa only [G, fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff] using hwest
  have hsourceEast : ¬ G.Reachable .source E := by
    simpa only [G, fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff] using heast
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hiff (z : FKIsingSquareMedialCarrier n) :
      (fkIsingSquareCompletedLoopGraph n hn
          (setOpen e.1 omega)).Reachable .source z ↔
        G.Reachable .source z := by
    rw [fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G
      hwestSouth heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach :
      (fkIsingSquareCompletedLoopGraph n hn
        (setOpen e.1 omega)).Reachable .source (.dart (e, side)) := by
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact hopen
  have hclosed : (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) := by
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact (hiff _).1 hopenReach
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · apply hwest
    rw [mem_fkIsingSquareExplorationFinset_iff]
    have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
      (setClosed e.1 omega) (e, .south) (.dart (e, .west))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
    exact ((mem_fkIsingSquareExplorationFinset_iff _ _ _ _).1 hclosed).trans
      hadj.reachable
  · apply heast
    rw [mem_fkIsingSquareExplorationFinset_iff]
    have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
      (setClosed e.1 omega) (e, .north) (.dart (e, .east))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
    exact ((mem_fkIsingSquareExplorationFinset_iff _ _ _ _).1 hclosed).trans
      hadj.reachable




theorem fkIsingSquare_local_switch_component_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_mem_of_closed_west_mem_not_east
          n hn omega e hwest heast⟩)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_mem_of_closed_east_mem_not_west
          n hn omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem
          n hn omega e hwest heast⟩

theorem fkIsingSquare_source_mem_exploration (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.source : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationFinset_iff]

theorem fkIsingSquare_terminal_mem_exploration (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.terminal : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationFinset_iff]
  exact fkIsingSquareLoopGraph_source_reachable_terminal n hn omega



noncomputable def fkIsingSquareExplorationPath (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Path .source .terminal :=
  (fkIsingSquareLoopGraph_source_reachable_terminal n hn omega).some.toPath

def fkIsingSquareExplorationOrder (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    List (FKIsingSquareMedialCarrier n) :=
  (fkIsingSquareExplorationPath n hn omega :
    (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).support

theorem fkIsingSquareExplorationOrder_nodup (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareExplorationOrder n hn omega).Nodup :=
  (fkIsingSquareExplorationPath n hn omega).isPath.support_nodup

theorem fkIsingSquareExplorationPath_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i ≤ (fkIsingSquareExplorationPath n hn omega :
      (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).length) :
    fkIsingSquareCarrierOddClass n
        ((fkIsingSquareExplorationPath n hn omega :
          (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).getVert i) ↔
      Odd i := by
  let p : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  change fkIsingSquareCarrierOddClass n (p.getVert i) ↔ Odd i
  induction i with
  | zero =>
      simp [p, fkIsingSquareCarrierOddClass]
  | succ i ih =>
      have hi0 : i < p.length := by simpa [p] using hi
      have hadj := p.adj_getVert_succ hi0
      have hflip := fkIsingSquareLoopGraph_adj_oddClass n hn omega hadj
      have ih' := ih (by simpa [p] using Nat.le_of_lt hi0)
      have hrev : fkIsingSquareCarrierOddClass n (p.getVert (i + 1)) ↔
          ¬ fkIsingSquareCarrierOddClass n (p.getVert i) := by
        tauto
      rw [hrev, ih', Nat.odd_add_one]





theorem fkIsingSquarePath_mem_support_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal)
    (hp : p.IsPath)
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ p.support ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  let H := fkIsingSquareLoopGraph n hn omega
  let G := fkIsingSquareCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    exact Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    change ¬(fkIsingSquareLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareMedialCarrier n) .source
    intro h
    have h' := h.symm
    rw [fkIsingSquareLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareMedialCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareMedialCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨hp.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source => exact fkIsingSquareCompletedLoopGraph_source_degree n hn omega
    | terminal => exact fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega
    | dart d => exact fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d
  constructor
  · intro hz
    exact (p.takeUntil z hz).reachable
  · intro hz
    have hclosed : ∀ v, v ∈ q.toSubgraph.verts →
        ∀ w, G.Adj v w → q.toSubgraph.Adj v w := by
      intro v hv w hadj
      exact (hq.adj_toSubgraph_iff_of_isCycles hcycles hv w).2 hadj
    obtain ⟨c, hc⟩ :=
      q.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
    have hsource : (.source : FKIsingSquareMedialCarrier n) ∈ c.supp := by
      rw [← hc, Walk.mem_verts_toSubgraph]
      simp [q]
    have hzG : G.Reachable .source z := by
      rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff]
      exact hz
    have hzc : z ∈ c.supp := by
      rw [c.mem_supp_iff]
      exact hsource ▸ ConnectedComponent.sound hzG.symm
    rw [← hc, Walk.mem_verts_toSubgraph] at hzc
    simp only [q, Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzc
    · simp
    · simpa only [Walk.support_mapLe_eq_support] using hzc


theorem mem_fkIsingSquareExplorationOrder_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationOrder n hn omega ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  simpa only [fkIsingSquareExplorationOrder] using
    fkIsingSquarePath_mem_support_iff_reachable n hn omega
      (fkIsingSquareExplorationPath n hn omega)
      (fkIsingSquareExplorationPath n hn omega).isPath z

theorem mem_fkIsingSquareExplorationOrder_iff_finset
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationOrder n hn omega ↔
      z ∈ fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationFinset_iff]





theorem fkIsingSquareExplorationPath_mem_edges_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hx : x ∈ fkIsingSquareExplorationOrder n hn omega)
    (hadj : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
    s(x, y) ∈ (fkIsingSquareExplorationPath n hn omega :
      (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).edges := by
  let H := fkIsingSquareLoopGraph n hn omega
  let G := fkIsingSquareCompletedLoopGraph n hn omega
  let p : H.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareMedialCarrier n) .source :=
    Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    change ¬(fkIsingSquareLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareMedialCarrier n) .source
    intro h
    have h' := h.symm
    rw [fkIsingSquareLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareMedialCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareMedialCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨(fkIsingSquareExplorationPath n hn omega).isPath.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source => exact fkIsingSquareCompletedLoopGraph_source_degree n hn omega
    | terminal => exact fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega
    | dart d => exact fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d
  have hxq : x ∈ q.toSubgraph.verts := by
    rw [Walk.mem_verts_toSubgraph]
    simp only [q, Walk.support_cons, List.mem_cons,
      Walk.support_mapLe_eq_support]
    right
    simpa [p, fkIsingSquareExplorationOrder] using hx
  have hqadj : q.toSubgraph.Adj x y :=
    (hq.adj_toSubgraph_iff_of_isCycles hcycles hxq y).2 (hle hadj)
  rw [Walk.adj_toSubgraph_iff_mem_edges] at hqadj
  simp only [q, Walk.edges_cons, List.mem_cons,
    Walk.edges_mapLe_eq_edges] at hqadj
  rcases hqadj with hxy | hxy
  · rcases Sym2.eq_iff.mp hxy with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj)
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj.symm)
  · exact hxy


def fkIsingSquarePathUsesLocalSide (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide) : Prop :=
  (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
    fkIsingSquareExplorationOrder n hn omega



theorem idxOf_succ_of_pair_infix_nodup {alpha : Type*} [DecidableEq alpha]
    {x y : alpha} {l : List alpha} (hl : l.Nodup)
    (hxy : [x, y] <:+: l) :
    l.idxOf y = l.idxOf x + 1 := by
  rw [List.infix_iff_prefix_suffix] at hxy
  rcases hxy with ⟨t, hpre, hsuf⟩
  rw [List.prefix_iff_eq_append] at hpre
  rw [List.suffix_iff_eq_append] at hsuf
  let a := l.take (l.length - t.length)
  let b := t.drop 2
  have hl' : a ++ [x, y] ++ b = l := by
    calc
      a ++ [x, y] ++ b = a ++ ([x, y] ++ b) := by simp
      _ = a ++ t := by
        rw [show [x, y] ++ b = t by simpa [b] using hpre]
      _ = l := by simpa [a] using hsuf
  have hn := hl' ▸ hl
  rw [← hl']
  simp only [List.idxOf_append]
  rw [List.nodup_append] at hn
  rcases hn with ⟨hnaxy, _hnb, _hdisjb⟩
  rw [List.nodup_append] at hnaxy
  rcases hnaxy with ⟨_hna, hnxy, hdisj⟩
  have hxA : x ∉ a := by
    intro hx
    exact (hdisj x hx x (by simp)) rfl
  have hyA : y ∉ a := by
    intro hy
    exact (hdisj y hy y (by simp)) rfl
  have hxyne : x ≠ y := by
    simpa using (List.nodup_cons.mp hnxy).1
  simp [hxA, hyA, hxyne]
  omega



theorem isAlternating_path_edge_iff_odd {V : Type*}
    {G M : SimpleGraph V} {u v : V}
    (halt : G.IsAlternating M) (p : G.Walk u v) (hp : p.IsPath)
    (hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1)) :
    ∀ i, i < p.length ->
      (M.Adj (p.getVert i) (p.getVert (i + 1)) ↔ Odd i) := by
  intro i hi
  induction i with
  | zero =>
      constructor
      · intro h
        exact False.elim (hfirst (by simpa only [p.getVert_zero] using h))
      · intro h
        rcases h with ⟨k, hk⟩
        omega
  | succ i ih =>
      have hi0 : i < p.length := by omega
      have hi2 : i + 2 ≤ p.length := by omega
      have hprev := p.adj_getVert_succ hi0
      have hnext := p.adj_getVert_succ hi
      have hne : p.getVert i ≠ p.getVert (i + 2) := by
        intro h
        have := hp.getVert_injOn (show i ≤ p.length by omega) hi2 h
        omega
      have ha : M.Adj (p.getVert i) (p.getVert (i + 1)) ↔
          ¬ M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
        simpa only [M.adj_comm, Nat.succ_eq_add_one,
          Nat.add_assoc, Nat.reduceAdd] using
            halt hne hprev.symm hnext
      have hflip : M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) ↔
          ¬ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
        tauto
      have ih' := ih hi0
      rw [hflip, ih', Nat.odd_add_one]



theorem fkIsingSquare_localMate_infix_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareMedialCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
        fkIsingSquareExplorationOrder n hn omega ∨
      [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
          FKIsingSquareMedialCarrier n), .dart (e, side)] <:+:
        fkIsingSquareExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareLoopGraph n hn omega).Adj
      (.dart (e, side))
      (.dart (FKIsingMedialDart.localMate omega (e, side))) :=
    (fkIsingSquareLoopGraph_adj_dart_iff n hn omega
      (e, side) _).2 (Or.inl rfl)
  apply Walk.infix_support_iff_mem_edges.mpr
  apply fkIsingSquareExplorationPath_mem_edges_of_adj n hn omega h hadj


theorem fkIsingSquare_localMate_idxOf_adjacent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    (fkIsingSquareExplorationOrder n hn omega).idxOf
        (.dart (FKIsingMedialDart.localMate omega (e, side))) =
      (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) + 1 ∨
    (fkIsingSquareExplorationOrder n hn omega).idxOf (.dart (e, side)) =
      (fkIsingSquareExplorationOrder n hn omega).idxOf
        (.dart (FKIsingMedialDart.localMate omega (e, side))) + 1 := by
  rcases fkIsingSquare_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exact Or.inl (idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hforward)
  · exact Or.inr (idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hbackward)



theorem fkIsingSquare_localMate_infix_of_counterclockwise
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    [(.dart (e, side) : FKIsingSquareMedialCarrier n),
        .dart (FKIsingMedialDart.localMate omega (e, side))] <:+:
      fkIsingSquareExplorationOrder n hn omega := by
  let H := fkIsingSquareLoopGraph n hn omega
  let M := fkIsingSquareLocalSmoothingGraph n omega
  let p : H.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  let x : FKIsingSquareMedialCarrier n := .dart (e, side)
  let y : FKIsingSquareMedialCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  rcases fkIsingSquare_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exact hforward
  · exfalso
    have hy : y ∈ p.support := hbackward.mem (by simp [y])
    have hx : x ∈ p.support := hbackward.mem (by simp [x])
    have hidx := idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareExplorationOrder_nodup n hn omega) hbackward
    change p.support.idxOf x = p.support.idxOf y + 1 at hidx
    have hjlt : p.support.idxOf y < p.length := by
      have hxlt : p.support.idxOf x < p.support.length :=
        List.idxOf_lt_length_iff.mpr hx
      rw [p.length_support, hidx] at hxlt
      omega
    have hgety : p.getVert (p.support.idxOf y) = y :=
      p.getVert_support_idxOf hy
    have hgetx : p.getVert (p.support.idxOf y + 1) = x := by
      have hx' := p.getVert_support_idxOf hx
      rw [hidx] at hx'
      exact hx'
    have hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1) := by
      intro hlocal
      rcases hlocal with ⟨d, hd, _⟩
      simpa [p] using hd
    have hodd : Odd (p.support.idxOf y) :=
      (isAlternating_path_edge_iff_odd
        (fkIsingSquareLoopGraph_isAlternating_localSmoothing n hn omega)
        p (fkIsingSquareExplorationPath n hn omega).isPath hfirst
        (p.support.idxOf y) hjlt).1 (by
          rw [hgety, hgetx]
          exact ⟨FKIsingMedialDart.localMate omega (e, side), rfl,
            by rw [FKIsingMedialDart.localMate_involutive]⟩)
    have hclass : fkIsingSquareCarrierOddClass n y :=
      by
        rw [← hgety]
        exact (fkIsingSquareExplorationPath_oddClass n hn omega
          (p.support.idxOf y) (Nat.le_of_lt hjlt)).2 hodd
    have hne := fkIsingSquare_localMate_cornerTurn_ne n omega (e, side)
    change (fkIsingSquareSideCorner
      (FKIsingMedialDart.localMate omega (e, side)).2).2 =
        .counterclockwise at hclass
    exact hne (hclass.trans hccw.symm)

theorem fkIsingSquare_open_pathUses_west_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ↔
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setOpen e.1 omega) (e, .west) (.dart (e, .north))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_open_pathUses_east_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ↔
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setOpen e.1 omega) (e, .east) (.dart (e, .south))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_closed_pathUses_west_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ↔
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .south := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setClosed e.1 omega) (e, .west) (.dart (e, .south))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

theorem fkIsingSquare_closed_pathUses_east_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ↔
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .north := by
  unfold fkIsingSquarePathUsesLocalSide
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationOrder_iff_reachable]
  have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
    (setClosed e.1 omega) (e, .east) (.dart (e, .north))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩




theorem walkSplice_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v a b c d : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hc : c ∈ p.support) (hd : d ∈ p.support)
    (hab : p.support.idxOf a < p.support.idxOf b)
    (hbc : p.support.idxOf b < p.support.idxOf c)
    (hcd : p.support.idxOf c < p.support.idxOf d) :
    ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v,
      q.IsPath ∧
        q.support = p.support.take (p.support.idxOf a + 1) ++
          p.support.drop (p.support.idxOf d) := by
  let cut : Set (Sym2 V) := {s(a, b), s(c, d)}
  let K := G.deleteEdges cut
  let pa := p.takeUntil a ha
  let pd := p.dropUntil d hd
  have hpa_support : pa.support =
      p.support.take (p.support.idxOf a + 1) := by
    simp [pa, Walk.takeUntil_eq_take,
      Walk.take_support_eq_support_take_succ]
  have hid_le : p.support.idxOf d ≤ p.length := by
    have hid_lt := List.idxOf_lt_length_of_mem hd
    simpa [Walk.length_support] using hid_lt
  have hpd_support : pd.support = p.support.drop (p.support.idxOf d) := by
    simp [pd, Walk.dropUntil_eq_drop,
      Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hid_le]
  have hpa_avoid : ∀ e, e ∈ pa.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · have hbpa := pa.snd_mem_support_of_mem_edges hf
      rw [hpa_support, List.mem_take_iff_idxOf_lt hb] at hbpa
      omega
    · have hcpa := pa.fst_mem_support_of_mem_edges hf
      rw [hpa_support, List.mem_take_iff_idxOf_lt hc] at hcpa
      omega
  have hsplit_nodup :
      (p.support.take (p.support.idxOf d) ++
        p.support.drop (p.support.idxOf d)).Nodup := by
    simpa only [List.take_append_drop] using hp.support_nodup
  have hdisj : List.Disjoint (p.support.take (p.support.idxOf d))
      (p.support.drop (p.support.idxOf d)) :=
    hsplit_nodup.disjoint
  have ha_take : a ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt ha]
    omega
  have hc_take : c ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hc]
    omega
  have hpd_avoid : ∀ e, e ∈ pd.edges → e ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · exact hdisj ha_take (hpd_support ▸ pd.fst_mem_support_of_mem_edges hf)
    · exact hdisj hc_take (hpd_support ▸ pd.fst_mem_support_of_mem_edges hf)
  have hKle : K ≤ medialTwoEdgeSwitch G a b c d := by
    intro x y hxy
    exact Or.inl (Or.inl hxy)
  have hadne : a ≠ d := by
    intro heq
    subst d
    omega
  have had : (medialTwoEdgeSwitch G a b c d).Adj a d := by
    change (((G.deleteEdges {s(a, b), s(c, d)}) ⊔ edge a d) ⊔
      edge c b).Adj a d
    exact Or.inl (Or.inr (by simpa [SimpleGraph.edge_adj] using hadne))
  let paK : K.Walk u a := pa.toDeleteEdges cut hpa_avoid
  let pdK : K.Walk d v := pd.toDeleteEdges cut hpd_avoid
  let pa' := paK.mapLe hKle
  let pd' := pdK.mapLe hKle
  let q := pa'.append (pd'.cons had)
  have hpa'_support : pa'.support = pa.support := by
    rw [Walk.support_mapLe_eq_support]
    apply Walk.support_transfer
  have hpd'_support : pd'.support = pd.support := by
    rw [Walk.support_mapLe_eq_support]
    apply Walk.support_transfer
  have hq_support : q.support =
      p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf d) := by
    dsimp only [q]
    rw [Walk.support_append, hpa'_support]
    simp only [Walk.support_cons, List.tail_cons]
    rw [hpd'_support, hpa_support, hpd_support]
  have hai_le : p.support.idxOf a + 1 ≤ p.support.idxOf d := by omega
  have hsub :
      (p.support.take (p.support.idxOf a + 1) ++
        p.support.drop (p.support.idxOf d)).Sublist p.support := by
    simpa [List.dropSlice_eq, Nat.add_sub_of_le hai_le] using
      List.dropSlice_sublist (p.support.idxOf a + 1)
        (p.support.idxOf d - (p.support.idxOf a + 1)) p.support
  refine ⟨q, ?_, hq_support⟩
  rw [Walk.isPath_def, hq_support]
  exact List.Nodup.sublist hsub hp.support_nodup



theorem walkSplice_membership_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {u v a b c d : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hc : c ∈ p.support) (hd : d ∈ p.support)
    (hab : p.support.idxOf a < p.support.idxOf b)
    (hbc : p.support.idxOf b < p.support.idxOf c)
    (hcd : p.support.idxOf c < p.support.idxOf d) :
    ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v,
      q.IsPath ∧
        q.support = p.support.take (p.support.idxOf a + 1) ++
          p.support.drop (p.support.idxOf d) ∧
        a ∈ q.support ∧ d ∈ q.support ∧
        b ∉ q.support ∧ c ∉ q.support := by
  obtain ⟨q, hq, hq_support⟩ :=
    walkSplice_of_order G p hp ha hb hc hd hab hbc hcd
  have hsplit_nodup :
      (p.support.take (p.support.idxOf d) ++
        p.support.drop (p.support.idxOf d)).Nodup := by
    simpa only [List.take_append_drop] using hp.support_nodup
  have hdisj : List.Disjoint (p.support.take (p.support.idxOf d))
      (p.support.drop (p.support.idxOf d)) :=
    hsplit_nodup.disjoint
  have hb_take_d : b ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hb]
    omega
  have hc_take_d : c ∈ p.support.take (p.support.idxOf d) := by
    rw [List.mem_take_iff_idxOf_lt hc]
    omega
  have ha_q : a ∈ q.support := by
    rw [hq_support, List.mem_append]
    exact Or.inl ((List.mem_take_iff_idxOf_lt ha).2 (by omega))
  have hd_drop : d ∈ p.support.drop (p.support.idxOf d) := by
    rw [List.drop_eq_getElem_cons (List.idxOf_lt_length_of_mem hd),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hd)]
    simp
  have hd_q : d ∈ q.support := by
    rw [hq_support, List.mem_append]
    exact Or.inr hd_drop
  have hb_q : b ∉ q.support := by
    rw [hq_support, List.mem_append]
    rintro (hb_take | hb_drop)
    · rw [List.mem_take_iff_idxOf_lt hb] at hb_take
      omega
    · exact hdisj hb_take_d hb_drop
  have hc_q : c ∉ q.support := by
    rw [hq_support, List.mem_append]
    rintro (hc_take | hc_drop)
    · rw [List.mem_take_iff_idxOf_lt hc] at hc_take
      omega
    · exact hdisj hc_take_d hc_drop
  exact ⟨q, hq, hq_support, ha_q, hd_q, hb_q, hc_q⟩

private def fkIsingSquareWalkCast {V : Type*} {G H : SimpleGraph V}
    (h : G = H) {u v : V} (p : G.Walk u v) : H.Walk u v :=
  h ▸ p

@[simp] private theorem fkIsingSquareWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] private theorem fkIsingSquareWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl

theorem fkIsingSquare_closed_west_south_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+:
      fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .west rfl h

theorem fkIsingSquare_closed_east_north_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+:
      fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self,
    fkIsingSquareSideCorner] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .east rfl h

theorem fkIsingSquare_open_west_north_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    [(.dart (e, .west) : FKIsingSquareMedialCarrier n), .dart (e, .north)] <:+:
      fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .west rfl h

theorem fkIsingSquare_open_east_south_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    [(.dart (e, .east) : FKIsingSquareMedialCarrier n), .dart (e, .south)] <:+:
      fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self,
    fkIsingSquareSideCorner] using
    fkIsingSquare_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .east rfl h



theorem fkIsingSquare_double_visit_closed_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
    p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ∨
      p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west)) := by
  let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  have hWmem : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈ p := by
    simpa [p, fkIsingSquarePathUsesLocalSide] using hwest
  have hne : p.idxOf (.dart (e, .west)) ≠ p.idxOf (.dart (e, .east)) := by
    intro hi
    have heq := (List.idxOf_inj hWmem).mp hi
    simp at heq
  have hSmem : (.dart (e, .south) : FKIsingSquareMedialCarrier n) ∈ p :=
    hWS.mem (by simp)
  have hSE : p.idxOf (.dart (e, .south)) ≠
      p.idxOf (.dart (e, .east)) := by
    intro hi
    have heq := (List.idxOf_inj hSmem).mp hi
    simp at heq
  have hNmem : (.dart (e, .north) : FKIsingSquareMedialCarrier n) ∈ p :=
    hEN.mem (by simp)
  have hNW : p.idxOf (.dart (e, .north)) ≠
      p.idxOf (.dart (e, .west)) := by
    intro hi
    have heq := (List.idxOf_inj hNmem).mp hi
    simp at heq
  change p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ∨
    p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west))
  change p.idxOf (.dart (e, .south)) = p.idxOf (.dart (e, .west)) + 1 at hiWS
  change p.idxOf (.dart (e, .north)) = p.idxOf (.dart (e, .east)) + 1 at hiEN
  omega




theorem fkIsingSquare_double_visit_open_pair_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (_hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (_heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
  classical
  let W := fkIsingSquarePathUsesLocalSide n hn
    (setOpen e.1 omega) e .west
  let E := fkIsingSquarePathUsesLocalSide n hn
    (setOpen e.1 omega) e .east
  have hWN := fkIsingSquare_open_pathUses_west_iff_north n hn omega e
  have hES := fkIsingSquare_open_pathUses_east_iff_south n hn omega e
  by_cases hW : W
  · by_cases hE : E
    · exact Or.inr (Or.inr (Or.inl
        ⟨hW, hWN.1 hW, hE, hES.1 hE⟩))
    · exact Or.inl ⟨hW, hWN.1 hW, hE,
        fun hS => hE (hES.2 hS)⟩
  · by_cases hE : E
    · exact Or.inr (Or.inl ⟨hW,
        fun hN => hW (hWN.2 hN), hE, hES.1 hE⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hW,
        fun hN => hW (hWN.2 hN), hE,
        fun hS => hE (hES.2 hS)⟩))




theorem fkIsingSquare_double_visit_open_pair_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧
      fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let G := fkIsingSquareLoopGraph n hn (setClosed e.1 omega)
  let p : G.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn (setClosed e.1 omega)
  have hp : p.IsPath :=
    (fkIsingSquareExplorationPath n hn (setClosed e.1 omega)).isPath
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hW : W ∈ p.support := by
    simpa [W, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using hwest
  have hS : S ∈ p.support := by
    simpa [S, p, fkIsingSquareExplorationOrder] using
      hWS.mem (by simp)
  have hE : E ∈ p.support := by
    simpa [E, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using heast
  have hN : N ∈ p.support := by
    simpa [N, p, fkIsingSquareExplorationOrder] using
      hEN.mem (by simp)
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  change p.support.idxOf S = p.support.idxOf W + 1 at hiWS
  change p.support.idxOf N = p.support.idxOf E + 1 at hiEN
  have horder := fkIsingSquare_double_visit_closed_order
    n hn omega e hwest heast
  change p.support.idxOf S < p.support.idxOf E ∨
    p.support.idxOf N < p.support.idxOf W at horder
  have hopen : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch G W S E N := by
    simpa [G, W, N, E, S] using
      fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  rcases horder with hSE | hNW
  · obtain ⟨q, hq, _hq_support, hWq, hNq, hSq, hEq⟩ :=
      walkSplice_membership_of_order G p hp hW hS hE hN
        (by omega) hSE (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      fkIsingSquareWalkCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWalkCast_isPath] using hq
    have hmem (z : FKIsingSquareMedialCarrier n) :
        z ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) ↔
          z ∈ qOpen.support := by
      rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
        ← fkIsingSquarePath_mem_support_iff_reachable n hn
          (setOpen e.1 omega) qOpen hqOpen]
    have hWqOpen : W ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hWq
    have hNqOpen : N ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hNq
    have hSqOpen : S ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hSq
    have hEqOpen : E ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hEq
    left
    refine ⟨?_, ?_, ?_, ?_⟩
    · change W ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem W).2 hWqOpen
    · change N ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem N).2 hNqOpen
    · change E ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hEqOpen ((hmem E).1 h)
    · change S ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hSqOpen ((hmem S).1 h)
  · have hpair : medialTwoEdgeSwitch G E N W S =
        medialTwoEdgeSwitch G W S E N :=
      medialTwoEdgeSwitch_swap_pairs G W S E N
    have hopen' : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G E N W S := hopen.trans hpair.symm
    obtain ⟨q, hq, _hq_support, hEq, hSq, hNq, hWq⟩ :=
      walkSplice_membership_of_order G p hp hE hN hW hS
        (by omega) hNW (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      fkIsingSquareWalkCast hopen'.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWalkCast_isPath] using hq
    have hmem (z : FKIsingSquareMedialCarrier n) :
        z ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) ↔
          z ∈ qOpen.support := by
      rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
        ← fkIsingSquarePath_mem_support_iff_reachable n hn
          (setOpen e.1 omega) qOpen hqOpen]
    have hEqOpen : E ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hEq
    have hSqOpen : S ∈ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hSq
    have hNqOpen : N ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hNq
    have hWqOpen : W ∉ qOpen.support := by
      simpa only [qOpen, fkIsingSquareWalkCast_support] using hWq
    right
    refine ⟨?_, ?_, ?_, ?_⟩
    · change W ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hWqOpen ((hmem W).1 h)
    · change N ∉ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact fun h => hNqOpen ((hmem N).1 h)
    · change E ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem E).2 hEqOpen
    · change S ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
      exact (hmem S).2 hSqOpen



theorem fkIsingSquare_local_switch_path_membership_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (¬ fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east ∧
      ∀ side, fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e side) ∨
    (fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east) := by
  simpa only [fkIsingSquarePathUsesLocalSide,
    mem_fkIsingSquareExplorationOrder_iff_finset] using
      fkIsingSquare_local_switch_component_classification n hn omega e


def FKIsingSquareDirection.eighthTurn : FKIsingSquareDirection -> Int
  | .east => 0
  | .north => 2
  | .west => 4
  | .south => 6



def fkIsingSquareCornerTangentCode
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) : Int :=
  d.eighthTurn + match turn with
    | .counterclockwise => 3
    | .clockwise => 5




def fkIsingSquareCarrierTangentCode (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> Int
  | .dart d => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n d) (fkIsingSquareSideCorner d.2).2
  | .source => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n
        (fkIsingSquareSourceInteriorDart n hn))
      (fkIsingSquareSideCorner
        (fkIsingSquareSourceInteriorDart n hn).2).2 + 4
  | .terminal => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n
        (fkIsingSquareTerminalInteriorDart n hn))
      (fkIsingSquareSideCorner
        (fkIsingSquareTerminalInteriorDart n hn).2).2


def fkIsingSquareSignedEighthTurn (a b : Int) : Int :=
  (b - a + 4) % 8 - 4




def fkIsingSquareExteriorCutStart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareBondMate n hn (fkIsingSquareSourceInteriorDart n hn)

def fkIsingSquareExteriorCutEnd (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareBondMate n hn (fkIsingSquareTerminalInteriorDart n hn)

@[simp] theorem fkIsingSquareDartDirection_sourceInterior
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartDirection n
      (fkIsingSquareSourcePrimalEdge n hn, .west) =
      .east := by
  simp [fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_source,
    fkIsingSquareSourceEdgeOrientation]

@[simp] theorem fkIsingSquareDartDirection_terminalInterior
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartDirection n
      (fkIsingSquareTerminalPrimalEdge n hn, .north) =
      .south := by
  simp [fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_terminal,
    fkIsingSquareTerminalEdgeOrientation]

@[simp] theorem fkIsingSquareCarrierTangentCode_exteriorCutStart
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierTangentCode n hn
      (.dart (fkIsingSquareExteriorCutStart n hn)) = 7 := by
  simp only [fkIsingSquareExteriorCutStart, fkIsingSquareBondMate,
    fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
  simp only [fkIsingSquareCarrierTangentCode,
    fkIsingSquareDirectionDart_direction, fkIsingSquareDirectionDart_turn,
    fkIsingSquareCornerTangentCode]
  rw [fkIsingSquareDartEndpoint_sourceAttachment,
    fkIsingSquareDartDirection_sourceInterior]
  simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedA, FKIsingSquareDirection.eighthTurn, hn]

@[simp] theorem fkIsingSquareCarrierTangentCode_exteriorCutEnd
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierTangentCode n hn
      (.dart (fkIsingSquareExteriorCutEnd n hn)) = 3 := by
  simp only [fkIsingSquareExteriorCutEnd, fkIsingSquareBondMate,
    fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
  simp only [fkIsingSquareCarrierTangentCode,
    fkIsingSquareDirectionDart_direction, fkIsingSquareDirectionDart_turn,
    fkIsingSquareCornerTangentCode]
  rw [fkIsingSquareDartEndpoint_terminalAttachment,
    fkIsingSquareDartDirection_terminalInterior]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedB, FKIsingSquareDirection.eighthTurn, hn]




def fkIsingSquareExteriorCutTurn (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  if d = fkIsingSquareExteriorCutStart n hn ∧
      f = fkIsingSquareExteriorCutEnd n hn then 8
  else if d = fkIsingSquareExteriorCutEnd n hn ∧
      f = fkIsingSquareExteriorCutStart n hn then -8
  else 0

@[simp] theorem fkIsingSquareExteriorCutTurn_forward
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareExteriorCutTurn n hn
      (fkIsingSquareExteriorCutStart n hn)
      (fkIsingSquareExteriorCutEnd n hn) = 8 := by
  simp [fkIsingSquareExteriorCutTurn,
    fkIsingSquareExteriorCutStart, fkIsingSquareExteriorCutEnd,
    fkIsingSquareBondMate_sourceEdge_ne_terminalEdge]

@[simp] theorem fkIsingSquareExteriorCutTurn_reverse
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareExteriorCutTurn n hn
      (fkIsingSquareExteriorCutEnd n hn)
      (fkIsingSquareExteriorCutStart n hn) = -8 := by
  have hne : fkIsingSquareExteriorCutEnd n hn ≠
      fkIsingSquareExteriorCutStart n hn := by
    intro h
    exact fkIsingSquareBondMate_sourceEdge_ne_terminalEdge n hn
      (congrArg Prod.fst h.symm)
  simp [fkIsingSquareExteriorCutTurn, hne]



theorem fkIsingSquareExteriorCutTurn_forward_unique (z : Int)
    (hzmod : z % 8 = 0) (hzlo : 4 < z) (hzhi : z ≤ 12) : z = 8 := by
  omega


theorem fkIsingSquareExteriorCutTurn_reverse_unique (z : Int)
    (hzmod : z % 8 = 0) (hzlo : -12 ≤ z) (hzhi : z < -4) : z = -8 := by
  omega



theorem fkIsingSquareExteriorCut_principal_forward
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutStart n hn)))
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutEnd n hn)) + 4) = 0 := by
  simp [fkIsingSquareSignedEighthTurn]

theorem fkIsingSquareExteriorCut_principal_reverse
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareSignedEighthTurn
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutEnd n hn)))
      (fkIsingSquareCarrierTangentCode n hn
        (.dart (fkIsingSquareExteriorCutStart n hn)) + 4) = 0 := by
  simp [fkIsingSquareSignedEighthTurn]






def fkIsingSquareExplorationTransitionTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) : Int :=
  match x, y with
  | .source, .dart f =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn .source)
        (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4)
  | .dart d, .terminal =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d))
        (fkIsingSquareCarrierTangentCode n hn .terminal)
  | .dart d, .dart f =>
      if f = FKIsingMedialDart.localMate omega d then
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareCarrierTangentCode n hn (.dart d) + 4)
          (fkIsingSquareCarrierTangentCode n hn (.dart f))
      else
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareCarrierTangentCode n hn (.dart d))
          (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4) +
            fkIsingSquareExteriorCutTurn n hn d f
  | _, _ =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn x)
        (fkIsingSquareCarrierTangentCode n hn y)

@[simp] theorem fkIsingSquareExplorationTransitionTurn_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareExplorationTransitionTurn n hn omega (.dart d)
        (.dart (FKIsingMedialDart.localMate omega d)) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d) + 4)
        (fkIsingSquareCarrierTangentCode n hn
          (.dart (FKIsingMedialDart.localMate omega d))) := by
  simp [fkIsingSquareExplorationTransitionTurn]

theorem fkIsingSquareExplorationTransitionTurn_bond
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : f ≠ FKIsingMedialDart.localMate omega d) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart d) (.dart f) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d))
        (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4) +
          fkIsingSquareExteriorCutTurn n hn d f := by
    simp [fkIsingSquareExplorationTransitionTurn, h]

theorem fkIsingSquareExplorationTransitionTurn_exterior_forward
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (h : fkIsingSquareExteriorCutEnd n hn ≠
      FKIsingMedialDart.localMate omega
        (fkIsingSquareExteriorCutStart n hn)) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart (fkIsingSquareExteriorCutStart n hn))
        (.dart (fkIsingSquareExteriorCutEnd n hn)) = 8 := by
  simp [fkIsingSquareExplorationTransitionTurn, h,
    fkIsingSquareExteriorCut_principal_forward,
    fkIsingSquareSignedEighthTurn]

theorem fkIsingSquareExplorationTransitionTurn_exterior_reverse
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (h : fkIsingSquareExteriorCutStart n hn ≠
      FKIsingMedialDart.localMate omega
        (fkIsingSquareExteriorCutEnd n hn)) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart (fkIsingSquareExteriorCutEnd n hn))
        (.dart (fkIsingSquareExteriorCutStart n hn)) = -8 := by
  simp [fkIsingSquareExplorationTransitionTurn, h,
    fkIsingSquareExteriorCut_principal_reverse,
    fkIsingSquareSignedEighthTurn]




theorem fkIsingSquareExplorationTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases ha : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [fkIsingSquareExplorationTransitionTurn,
      fkIsingSquareCarrierTangentCode, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      FKIsingMedialDart.localMate, setOpen, setClosed,
      fkIsingSquareSignedEighthTurn,
      FKIsingSquareDirection.eighthTurn, ha]


def fkIsingSquareExplorationTurnSteps (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) : List Int :=
  let path := fkIsingSquareExplorationOrder n hn omega
  List.zipWith (fkIsingSquareExplorationTransitionTurn n hn omega)
    path path.tail



def fkIsingSquareLiftedTurnCount (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) : Int :=
  let path := fkIsingSquareExplorationOrder n hn omega
  if z ∈ path then
    ((fkIsingSquareExplorationTurnSteps n hn omega).take
      (path.idxOf z)).sum
  else 0



theorem fkIsingSquareLiftedTurnCount_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareExplorationOrder n hn omega).length) :
    fkIsingSquareLiftedTurnCount n hn omega
        (fkIsingSquareExplorationOrder n hn omega)[i + 1] =
      fkIsingSquareLiftedTurnCount n hn omega
        (fkIsingSquareExplorationOrder n hn omega)[i] +
      fkIsingSquareExplorationTransitionTurn n hn omega
        (fkIsingSquareExplorationOrder n hn omega)[i]
        (fkIsingSquareExplorationOrder n hn omega)[i + 1] := by
  let p := fkIsingSquareExplorationOrder n hn omega
  let t := fkIsingSquareExplorationTurnSteps n hn omega
  have hi' : i + 1 < p.length := by simpa [p] using hi
  have hi0 : i < p.length := by omega
  have hmem0 : p[i] ∈ p := List.getElem_mem _
  have hmem1 : p[i + 1] ∈ p := List.getElem_mem _
  have hnodup : p.Nodup := by
    simpa [p] using fkIsingSquareExplorationOrder_nodup n hn omega
  have hidx0 : p.idxOf p[i] = i :=
    List.get_idxOf hnodup ⟨i, hi0⟩
  have hidx1 : p.idxOf p[i + 1] = i + 1 :=
    List.get_idxOf hnodup ⟨i + 1, hi'⟩
  have htlen : i < t.length := by
    simp [t, fkIsingSquareExplorationTurnSteps]
    omega
  have htget :
      t[i] = fkIsingSquareExplorationTransitionTurn n hn omega
        p[i] p[i + 1] := by
    simp [t, fkIsingSquareExplorationTurnSteps, p]
  change (if p[i + 1] ∈ p then
      (t.take (p.idxOf p[i + 1])).sum else 0) = _
  rw [if_pos hmem1]
  change _ = (if p[i] ∈ p then
      (t.take (p.idxOf p[i])).sum else 0) + _
  rw [if_pos hmem0, hidx0, hidx1,
    List.sum_take_succ t i htlen, htget]




theorem fkIsingSquareLiftedTurnCount_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (h : fkIsingSquarePathUsesLocalSide n hn omega e side) :
    (fkIsingSquareLiftedTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) =
      fkIsingSquareLiftedTurnCount n hn omega (.dart (e, side)) +
        fkIsingSquareExplorationTransitionTurn n hn omega
          (.dart (e, side))
          (.dart (FKIsingMedialDart.localMate omega (e, side)))) ∨
    (fkIsingSquareLiftedTurnCount n hn omega (.dart (e, side)) =
      fkIsingSquareLiftedTurnCount n hn omega
        (.dart (FKIsingMedialDart.localMate omega (e, side))) +
        fkIsingSquareExplorationTransitionTurn n hn omega
          (.dart (FKIsingMedialDart.localMate omega (e, side)))
          (.dart (e, side))) := by
  let p := fkIsingSquareExplorationOrder n hn omega
  let x : FKIsingSquareMedialCarrier n := .dart (e, side)
  let y : FKIsingSquareMedialCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  have hxy := fkIsingSquare_localMate_infix_explorationOrder
    n hn omega e side h
  have hx : x ∈ p := by simpa [x, p] using h
  have hy : y ∈ p := hxy.elim
    (fun hf => hf.mem (by simp [y]))
    (fun hb => hb.mem (by simp [y]))
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareLiftedTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    left
    simpa only [p, x, y, List.getElem_idxOf hix,
      ← hi, List.getElem_idxOf hiy] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareLiftedTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    right
    simpa only [p, x, y, List.getElem_idxOf hiy,
      ← hi, List.getElem_idxOf hix] using hs

theorem fkIsingSquare_closed_west_south_turnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .west)) - 2 := by
  have hm := fkIsingSquareLiftedTurnCount_localMate
    n hn (setClosed e.1 omega) e .west h
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨hWS, hSW, _hEN, _hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hWS, hSW] at hm
  omega

theorem fkIsingSquare_closed_east_north_turnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedTurnCount n hn (setClosed e.1 omega)
        (.dart (e, .east)) - 2 := by
  have hm := fkIsingSquareLiftedTurnCount_localMate
    n hn (setClosed e.1 omega) e .east h
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, hEN, hNE, _hWN, _hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setClosed_self] at hm
  rw [hEN, hNE] at hm
  omega

theorem fkIsingSquare_open_west_north_turnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .west)) + 2 := by
  have hm := fkIsingSquareLiftedTurnCount_localMate
    n hn (setOpen e.1 omega) e .west h
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, hWN, hNW, _hES, _hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hWN, hNW] at hm
  omega

theorem fkIsingSquare_open_east_south_turnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedTurnCount n hn (setOpen e.1 omega)
        (.dart (e, .east)) + 2 := by
  have hm := fkIsingSquareLiftedTurnCount_localMate
    n hn (setOpen e.1 omega) e .east h
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨_hWS, _hSW, _hEN, _hNE, _hWN, _hNW, hES, hSE⟩
  simp only [FKIsingMedialDart.localMate, setOpen_self] at hm
  rw [hES, hSE] at hm
  omega



def fkIsingSquareObservationFrameTurn (n : Nat) :
    FKIsingSquareMedialCarrier n -> Int
  | _ => 0



def fkIsingSquarePhysicalTransitionTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) : Int :=
  fkIsingSquareExplorationTransitionTurn n hn omega x y +
    fkIsingSquareObservationFrameTurn n y -
    fkIsingSquareObservationFrameTurn n x



theorem fkIsingSquarePhysicalTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨hWS, hSW, hEN, hNE, hWN, hNW, hES, hSE⟩
  simp only [fkIsingSquarePhysicalTransitionTurn,
    fkIsingSquareObservationFrameTurn, hWS, hSW, hEN, hNE,
    hWN, hNW, hES, hSE]
  omega


def fkIsingSquarePhysicalTurnCount (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) : Int :=
  fkIsingSquareLiftedTurnCount n hn omega z +
    fkIsingSquareObservationFrameTurn n z




def fkIsingSquareLiftedWinding (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) : Real :=
  ((fkIsingSquarePhysicalTurnCount n hn omega z -
      fkIsingSquarePhysicalTurnCount n hn omega .terminal : Int) : Real) *
    (Real.pi / 4)


theorem fkIsingSquareLiftedWinding_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareExplorationOrder n hn omega).length) :
    fkIsingSquareLiftedWinding n hn omega
        (fkIsingSquareExplorationOrder n hn omega)[i + 1] =
      fkIsingSquareLiftedWinding n hn omega
          (fkIsingSquareExplorationOrder n hn omega)[i] +
        (fkIsingSquarePhysicalTransitionTurn n hn omega
          (fkIsingSquareExplorationOrder n hn omega)[i]
          (fkIsingSquareExplorationOrder n hn omega)[i + 1] : Real) *
            (Real.pi / 4) := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquarePhysicalTransitionTurn]
  rw [fkIsingSquareLiftedTurnCount_succ n hn omega i hi]
  push_cast
  ring

@[simp] theorem fkIsingSquareLiftedWinding_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareLiftedWinding n hn omega .terminal = 0 := by
  simp [fkIsingSquareLiftedWinding]

theorem fkIsingSquare_closed_west_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .west)) - Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_closed_west_south_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_closed_east_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .east)) - Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_closed_east_north_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_open_west_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .west)) + Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_open_west_north_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_open_east_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .east)) + Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_open_east_south_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring


def fkIsingSquareSitePosition (x : Site 2) : Complex :=
  (x 0 : Real) + Complex.I * (x 1 : Real)


def fkIsingSquareCarrierPosition (n : Nat) (_hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> Complex
  | .dart d =>
      (fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).tail.1 +
        fkIsingSquareSitePosition (fkIsingSquareOrientedEdge n d.1).head.1) / 2
  | .source => fkIsingSquareSitePosition (fkIsingSquareMarkedA n).1 - 1 / 2
  | .terminal => fkIsingSquareSitePosition (fkIsingSquareMarkedB n).1 - 1 / 2



def fkIsingSquareDobrushinDomain (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareMedialCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareCarrierPosition n hn
  exploration := fkIsingSquareExplorationOrder n hn
  source_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  terminal_mem := by
    intro omega
    simp [fkIsingSquareExplorationOrder, fkIsingSquareExplorationPath]
  winding := fkIsingSquareLiftedWinding n hn
  winding_terminal := fkIsingSquareLiftedWinding_terminal n hn

end

end StatMech.Universality
