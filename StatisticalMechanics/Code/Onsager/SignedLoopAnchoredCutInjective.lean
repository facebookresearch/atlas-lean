/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopAnchoredCut





open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]



def ons_multibondSupportGraph (ends : P → V × V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ edge : P,
    ends edge = (x, y) ∨ ends edge = (y, x)
  symm := by
    rintro x y ⟨hne, edge, h | h⟩
    · exact ⟨hne.symm, edge, Or.inr h⟩
    · exact ⟨hne.symm, edge, Or.inl h⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance ons_multibondSupportGraph_decidableAdj
    (ends : P → V × V) : DecidableRel (ons_multibondSupportGraph ends).Adj :=
  Classical.decRel _



theorem multibondCut_eq_propagate_adj
    (ends : P → V × V) (s t : V → Bool)
    (hcut : multibondCut ends s = multibondCut ends t)
    {x y : V} (hxy : (ons_multibondSupportGraph ends).Adj x y)
    (hx : s x = t x) : s y = t y := by
  obtain ⟨_, edge, hedge | hedge⟩ := hxy
  · have hmem : edge ∈ multibondCut ends s ↔
        edge ∈ multibondCut ends t := by rw [hcut]
    rw [mem_multibondCut, mem_multibondCut, hedge] at hmem
    cases hsx : s x <;> cases hsy : s y <;>
      cases htx : t x <;> cases hty : t y <;> simp_all
  · have hmem : edge ∈ multibondCut ends s ↔
        edge ∈ multibondCut ends t := by rw [hcut]
    rw [mem_multibondCut, mem_multibondCut, hedge] at hmem
    cases hsx : s x <;> cases hsy : s y <;>
      cases htx : t x <;> cases hty : t y <;> simp_all


theorem multibondCut_eq_propagate_walk
    (ends : P → V × V) (s t : V → Bool)
    (hcut : multibondCut ends s = multibondCut ends t)
    {x y : V} (walk : (ons_multibondSupportGraph ends).Walk x y)
    (hx : s x = t x) : s y = t y := by
  induction walk with
  | nil => exact hx
  | @cons u v z huv walk ih =>
      exact ih (multibondCut_eq_propagate_adj ends s t hcut huv hx)



theorem multibondCut_anchored_injective_of_reachable
    (ends : P → V × V) (root : V)
    (hreach : ∀ v : V,
      (ons_multibondSupportGraph ends).Reachable root v) :
    Function.Injective (fun config : AnchoredConfig V root =>
      multibondCut ends config.1) := by
  intro s t hcut
  apply Subtype.ext
  funext v
  obtain ⟨walk⟩ := hreach v
  apply multibondCut_eq_propagate_walk ends s.1 t.1 hcut walk
  rw [s.2, t.2]


theorem multibondCut_anchored_injective_of_connected
    (ends : P → V × V) (root : V)
    (hconnected : (ons_multibondSupportGraph ends).Connected) :
    Function.Injective (fun config : AnchoredConfig V root =>
      multibondCut ends config.1) :=
  multibondCut_anchored_injective_of_reachable ends root
    (fun v => hconnected.preconnected root v)

end

end StatMech.Onsager
