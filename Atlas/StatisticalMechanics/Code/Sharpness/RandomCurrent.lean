/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib

open SimpleGraph Finset

set_option linter.unusedSectionVars false

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]






abbrev Current (V : Type*) : Type _ := Sym2 V → ℕ



noncomputable def incidentFlux (n : Current V) (x : V) : ℕ :=
  ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e), n e




noncomputable def sources (n : Current V) : Finset V :=
  Finset.univ.filter (fun x => Odd (incidentFlux G n x))

@[simp]
theorem mem_sources {n : Current V} {x : V} :
    x ∈ sources G n ↔ Odd (incidentFlux G n x) := by
  simp [sources]




noncomputable def weight (β : ℝ) (J : Sym2 V → ℝ) (n : Current V) : ℝ :=
  ∏ e ∈ G.edgeFinset, (β * J e) ^ (n e) / (Nat.factorial (n e))


@[simp]
theorem weight_zero (β : ℝ) (J : Sym2 V → ℝ) :
    weight G β J (fun _ => 0) = 1 := by
  simp [weight]



def currentSubgraph (n : Current V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ 1 ≤ n s(x, y)
  symm := by
    intro x y ⟨hadj, hpos⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => hadj.ne rfl⟩

@[simp]
theorem currentSubgraph_adj (n : Current V) (x y : V) :
    (currentSubgraph G n).Adj x y ↔ G.Adj x y ∧ 1 ≤ n s(x, y) := Iff.rfl

instance decidableRel_currentSubgraph (n : Current V) :
    DecidableRel (currentSubgraph G n).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ 1 ≤ n s(x, y)))


theorem currentSubgraph_le (n : Current V) : currentSubgraph G n ≤ G :=
  fun _ _ h => h.1




def CurrentConnected (n : Current V) (x y : V) : Prop :=
  (currentSubgraph G n).Reachable x y

@[refl]
theorem CurrentConnected.refl (n : Current V) (x : V) : CurrentConnected G n x x :=
  SimpleGraph.Reachable.refl x

theorem CurrentConnected.symm {n : Current V} {x y : V}
    (h : CurrentConnected G n x y) : CurrentConnected G n y x :=
  SimpleGraph.Reachable.symm h

theorem CurrentConnected.trans {n : Current V} {x y z : V}
    (hxy : CurrentConnected G n x y) (hyz : CurrentConnected G n y z) :
    CurrentConnected G n x z :=
  SimpleGraph.Reachable.trans hxy hyz






def oddSubgraph (n : Current V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ Odd (n s(x, y))
  symm := by
    intro x y ⟨hadj, hodd⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => hadj.ne rfl⟩

@[simp]
theorem oddSubgraph_adj (n : Current V) (x y : V) :
    (oddSubgraph G n).Adj x y ↔ G.Adj x y ∧ Odd (n s(x, y)) := Iff.rfl

instance decidableRel_oddSubgraph (n : Current V) :
    DecidableRel (oddSubgraph G n).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x y ∧ Odd (n s(x, y))))


theorem oddSubgraph_le (n : Current V) : oddSubgraph G n ≤ G :=
  fun _ _ h => h.1



theorem oddSubgraph_le_currentSubgraph (n : Current V) :
    oddSubgraph G n ≤ currentSubgraph G n := by
  intro x y ⟨hadj, hodd⟩
  exact ⟨hadj, hodd.pos⟩




abbrev IsBackbonePath (n : Current V) (x y : V) : Type _ :=
  (oddSubgraph G n).Path x y








noncomputable def backbone (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) : IsBackbonePath G n x y :=
  (Finset.univ : Finset (IsBackbonePath G n x y)).min'
    (Finset.univ_nonempty_iff.mpr h)



theorem backbone_le (n : Current V) (x y : V)
    [LinearOrder (IsBackbonePath G n x y)]
    (h : Nonempty (IsBackbonePath G n x y)) (p : IsBackbonePath G n x y) :
    backbone G n x y h ≤ p :=
  Finset.min'_le _ _ (Finset.mem_univ p)



theorem IsBackbonePath.currentConnected {n : Current V} {x y : V}
    (p : IsBackbonePath G n x y) : CurrentConnected G n x y :=
  (p.1.mapLe (oddSubgraph_le_currentSubgraph G n)).reachable






def percolationField (n : Current V) : Sym2 V → Bool :=
  fun e => decide (1 ≤ n e)

@[simp]
theorem percolationField_apply (n : Current V) (e : Sym2 V) :
    percolationField n e = true ↔ 1 ≤ n e := by
  simp [percolationField]




theorem currentSubgraph_eq_percolationField (n : Current V) :
    currentSubgraph G n =
      G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true} := by
  ext x y
  simp only [currentSubgraph_adj, inf_adj, fromEdgeSet_adj, Set.mem_setOf_eq,
    percolationField_apply]
  constructor
  · rintro ⟨hadj, hpos⟩
    exact ⟨hadj, hpos, hadj.ne⟩
  · rintro ⟨hadj, hpos, _⟩
    exact ⟨hadj, hpos⟩



theorem currentConnected_iff_percolationField (n : Current V) (x y : V) :
    CurrentConnected G n x y ↔
      (G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true}).Reachable x y := by
  rw [CurrentConnected, currentSubgraph_eq_percolationField]





def ghost : Option V := none





def withGhost : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some x, some y => G.Adj x y
    | some _, none => True
    | none, some _ => True
    | none, none => False
  symm := by
    rintro (_ | x) (_ | y) h
    · exact h
    · exact h
    · exact h
    · exact G.symm h
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl x h⟩

@[simp]
theorem withGhost_adj_some_some (x y : V) :
    (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

@[simp]
theorem withGhost_adj_some_ghost (x : V) :
    (withGhost G).Adj (some x) ghost := trivial

@[simp]
theorem withGhost_adj_ghost_some (x : V) :
    (withGhost G).Adj ghost (some x) := trivial



theorem withGhost_ghost_adj (x : V) : (withGhost G).Adj ghost (some x) := trivial



theorem withGhost_restrict (x y : V) :
    (withGhost G).Adj (some x) (some y) ↔ G.Adj x y := Iff.rfl

end Sharpness

end StatMech
