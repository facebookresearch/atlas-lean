/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusShellEmbedding

open Finset

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {d k : Nat}


def isingTorusCoordinateSwap (i j : Fin d) :
    IsingDyadicTorus d k ≃ IsingDyadicTorus d k where
  toFun x a := x (Equiv.swap i j a)
  invFun x a := x (Equiv.swap i j a)
  left_inv x := by
    funext a
    change x (Equiv.swap i j (Equiv.swap i j a)) = x a
    rw [Equiv.swap_apply_self]
  right_inv x := by
    funext a
    change x (Equiv.swap i j (Equiv.swap i j a)) = x a
    rw [Equiv.swap_apply_self]

@[simp] theorem isingTorusCoordinateSwap_apply
    (i j a : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusCoordinateSwap i j x a = x (Equiv.swap i j a) := rfl

@[simp] theorem isingTorusCoordinateSwap_add
    (i j : Fin d) (x y : IsingDyadicTorus d k) :
    isingTorusCoordinateSwap i j (x + y) =
      isingTorusCoordinateSwap i j x + isingTorusCoordinateSwap i j y := rfl

@[simp] theorem isingTorusCoordinateSwap_step
    (i j l : Fin d) :
    isingTorusCoordinateSwap (k := k) i j (isingTorusStep l) =
      isingTorusStep (Equiv.swap i j l) := by
  funext a
  by_cases ha : Equiv.swap i j a = l
  · have hal : a = Equiv.swap i j l := by
      calc
        a = Equiv.swap i j (Equiv.swap i j a) :=
          (Equiv.swap_apply_self i j a).symm
        _ = Equiv.swap i j l := congrArg (Equiv.swap i j) ha
    change (Pi.single l (1 : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) (Equiv.swap i j a) =
      (Pi.single (Equiv.swap i j l) (1 : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) a
    rw [ha, hal]
    simp
  · have hal : a ≠ Equiv.swap i j l := by
      intro h
      apply ha
      rw [h, Equiv.swap_apply_self]
    change (Pi.single l (1 : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) (Equiv.swap i j a) =
      (Pi.single (Equiv.swap i j l) (1 : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) a
    rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hal]

@[simp] theorem isingTorusCoordinateSwap_involutive
    (i j : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusCoordinateSwap i j (isingTorusCoordinateSwap i j x) = x := by
  exact (isingTorusCoordinateSwap (k := k) i j).left_inv x


theorem isingTorusGraph_adj_coordinateSwap
    (i j : Fin d) (x y : IsingDyadicTorus d k) :
    (isingTorusGraph d k).Adj x y ↔
      (isingTorusGraph d k).Adj
        (isingTorusCoordinateSwap i j x)
        (isingTorusCoordinateSwap i j y) := by
  let s := isingTorusCoordinateSwap (k := k) i j
  have forward (a b : IsingDyadicTorus d k) :
      (isingTorusGraph d k).Adj a b ->
        (isingTorusGraph d k).Adj (s a) (s b) := by
    rintro ⟨l, h | h⟩
    · refine ⟨Equiv.swap i j l, Or.inl ?_⟩
      have hs := congrArg s h
      simpa [s] using hs
    · refine ⟨Equiv.swap i j l, Or.inr ?_⟩
      have hs := congrArg s h
      simpa [s] using hs
  constructor
  · exact forward x y
  · intro h
    have h' := forward (s x) (s y) h
    simpa [s] using h'



theorem isingTorusTwoPoint_coordinateSwap
    (i j : Fin d) (beta : Real) (x y : IsingDyadicTorus d k) :
    isingTorusTwoPoint beta x y =
      isingTorusTwoPoint beta
        (isingTorusCoordinateSwap i j x)
        (isingTorusCoordinateSwap i j y) := by
  simp only [isingTorusTwoPoint_eq_twoPointJ]
  unfold twoPointJ
  rw [expectationJ_one_eq_isingExpectation,
    expectationJ_one_eq_isingExpectation]
  let s := isingTorusCoordinateSwap (k := k) i j
  have hrel := Ising.isingExpectation_spinProd_relabel
    (isingTorusGraph d k) (isingTorusGraph d k) s
    (isingTorusGraph_adj_coordinateSwap i j) beta 0 (sourcePair x y)
  have hmap : (sourcePair x y).map s.toEmbedding =
      sourcePair (s x) (s y) := by
    ext a
    simp only [sourcePair, Finset.mem_map, Finset.mem_symmDiff,
      Finset.mem_singleton]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rcases hb with ⟨hbx, hby⟩ | ⟨hby, hbx⟩
      · exact Or.inl ⟨congrArg s hbx, fun h => hby (s.injective h)⟩
      · exact Or.inr ⟨congrArg s hby, fun h => hbx (s.injective h)⟩
    · rintro (⟨hax, hay⟩ | ⟨hay, hax⟩)
      · refine ⟨x, Or.inl ⟨rfl, ?_⟩, hax.symm⟩
        intro hxy
        apply hay
        exact hax.trans (congrArg s hxy)
      · refine ⟨y, Or.inr ⟨rfl, ?_⟩, hay.symm⟩
        intro hyx
        apply hax
        exact hay.trans (congrArg s hyx)
  rw [hmap] at hrel
  exact hrel

@[simp] theorem isingTorusCoordinateSwap_zero
    (i j : Fin d) :
    isingTorusCoordinateSwap (k := k) i j 0 = 0 := rfl

theorem isingTorusCoordinateSwap_coordinateShift_left
    (i j : Fin d) (r : Nat) :
    isingTorusCoordinateSwap (k := k) i j
        (isingTorusCoordinateShift i r) =
      isingTorusCoordinateShift j r := by
  funext a
  by_cases ha : Equiv.swap i j a = i
  · have hal : a = j := by
      calc
        a = Equiv.swap i j (Equiv.swap i j a) :=
          (Equiv.swap_apply_self i j a).symm
        _ = Equiv.swap i j i := congrArg (Equiv.swap i j) ha
        _ = j := Equiv.swap_apply_left i j
    change (Pi.single i (r : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) (Equiv.swap i j a) =
      (Pi.single j (r : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) a
    rw [ha, hal]
    simp
  · have hal : a ≠ j := by
      intro h
      apply ha
      rw [h, Equiv.swap_apply_right]
    change (Pi.single i (r : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) (Equiv.swap i j a) =
      (Pi.single j (r : ZMod (2 ^ (k + 2))) :
        IsingDyadicTorus d k) a
    rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hal]


theorem isingTorusTwoPoint_axis_eq_axis
    (i j : Fin d) (beta : Real) (r : Nat) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) =
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift j r) := by
  rw [isingTorusTwoPoint_coordinateSwap i j]
  rw [isingTorusCoordinateSwap_zero,
    isingTorusCoordinateSwap_coordinateShift_left]



theorem isingTorusTwoPoint_embedded_shell_le_axis
    (j : Fin d) (beta : Real) (hbeta : 0 <= beta)
    {n : Nat} (hn : 1 <= n) (hnHalf : n < 2 ^ (k + 1))
    (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) <=
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift j n) := by
  obtain ⟨i, hi⟩ := exists_isingTorusTwoPoint_embedded_shell_le_axis
    beta hbeta hn hnHalf x hx
  exact hi.trans_eq (isingTorusTwoPoint_axis_eq_axis i j beta n)

end StatMech.FrontierA
