/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.UniversalCurveStability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-! Tests for stable marked graphs, contractions and universal stability. -/

open MathlibExt.AlgebraicGeometry.UniversalCurveStability

namespace MathlibExtTest.UniversalCurveStability

/-! ### Concrete stable graphs of genus two with one marking -/

/-- One vertex of genus two, no edges. -/
abbrev smooth : StableGraph 2 1 where
  vertices := 1
  nonempty := by decide
  edges := 0
  endpoint e := e.elim0
  genus _ := 2
  marking _ := 0
  connected v w := by rw [Subsingleton.elim v w]
  totalGenus := by decide
  stable := by decide

/-- One vertex of genus one carrying a loop. -/
abbrev loopGraph : StableGraph 2 1 where
  vertices := 1
  nonempty := by decide
  edges := 1
  endpoint _ _ := 0
  genus _ := 1
  marking _ := 0
  connected v w := by rw [Subsingleton.elim v w]
  totalGenus := by decide
  stable := by decide

/-- Two genus-one vertices joined by one edge, marked on the first: `Γ(1, {1})`. -/
abbrev bridge : StableGraph 2 1 where
  vertices := 2
  nonempty := by decide
  edges := 1
  endpoint _ h := h
  genus _ := 1
  marking _ := 0
  connected v w := by
    fin_cases v <;> fin_cases w
    · exact .refl
    · exact .single ⟨0, Finset.mem_univ _, .inl ⟨rfl, rfl⟩⟩
    · exact .single ⟨0, Finset.mem_univ _, .inr ⟨rfl, rfl⟩⟩
    · exact .refl
  totalGenus := by decide
  stable := by decide

/-- `bridge` with its vertex labels exchanged. -/
abbrev bridgeFlip : StableGraph 2 1 :=
  { bridge with marking := fun _ ↦ 1, stable := by decide }

/-- A rational marked vertex joined to a genus-one vertex by two edges: `Γ_1`. -/
abbrev banana : StableGraph 2 1 where
  vertices := 2
  nonempty := by decide
  edges := 2
  endpoint _ h := h
  genus v := if v = 0 then 0 else 1
  marking _ := 0
  connected v w := by
    fin_cases v <;> fin_cases w
    · exact .refl
    · exact .single ⟨0, Finset.mem_univ _, .inl ⟨rfl, rfl⟩⟩
    · exact .single ⟨0, Finset.mem_univ _, .inr ⟨rfl, rfl⟩⟩
    · exact .refl
  totalGenus := by decide
  stable := by decide

/-- Like `banana`, but the second edge is a loop at the rational vertex. -/
abbrev loopBridge : StableGraph 2 1 :=
  { banana with
    endpoint := fun e h ↦ if e = 0 then h else 0
    connected := fun v w ↦ by
      fin_cases v <;> fin_cases w
      · exact .refl
      · exact .single ⟨0, Finset.mem_univ _, .inl ⟨rfl, rfl⟩⟩
      · exact .single ⟨0, Finset.mem_univ _, .inr ⟨rfl, rfl⟩⟩
      · exact .refl
    stable := by decide }

/-- A rational vertex carrying both markings, joined to a genus-one vertex by two
edges. -/
abbrev bananaTwoMarks : StableGraph 2 2 :=
  { banana with marking := fun _ ↦ 0, stable := by decide }

/-! ### Valence counts both branches of a loop; marking counts -/

example : valence loopGraph.endpoint 0 = 2 := by decide
example : valence loopBridge.endpoint 0 = 3 := by decide
example : valence loopBridge.endpoint 1 = 1 := by decide
example : valence banana.endpoint 1 = 2 := by decide
-- `valence` is the endpoint-incidence degree of the multigraph API.
example : EndpointMapMultigraph.degreeWithin (loopGraph.endpoint · 0) (loopGraph.endpoint · 1)
    Finset.univ 0 = 2 := by
  rw [← valence_eq_degreeWithin]
  decide

example : markingCount banana.marking 0 = 1 := by decide
example : markingCount banana.marking 1 = 0 := by decide
example : markingCount bananaTwoMarks.marking 0 = 2 := by decide

-- A rational vertex with one loop and no marking is not stable.
example : ¬ 0 < 2 * ((0 : ℕ) : ℤ) - 2 +
    valence (fun (_ : Fin 1) (_ : Fin 2) ↦ (0 : Fin 1)) 0 +
      markingCount (Fin.elim0 : Fin 0 → Fin 1) 0 := by decide

/-! ### Determining graphs (Kass--Pagani Corollary 3.6) -/

example : IsDeterminingGraph bridge := by unfold IsDeterminingGraph; decide
example : IsDeterminingGraph banana := by unfold IsDeterminingGraph; decide
example : ¬ IsDeterminingGraph smooth := by unfold IsDeterminingGraph; decide
example : ¬ IsDeterminingGraph loopGraph := by unfold IsDeterminingGraph; decide
-- Two vertices, two edges and a rational vertex with one marking, but a loop.
example : ¬ IsDeterminingGraph loopBridge := by unfold IsDeterminingGraph; decide
-- The rational vertex carries two markings.
example : ¬ IsDeterminingGraph bananaTwoMarks := by
  unfold IsDeterminingGraph; decide

/-! ### Isomorphisms, including branch permutations -/

/-- Reversing the orientation of the loop is an automorphism. -/
def loopReverse : GraphIso loopGraph loopGraph where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  branch _ := Equiv.swap 0 1
  endpoint := by decide
  genus := by decide
  marking := by decide

/-- Exchanging the vertices of `bridge` also reverses its edge. -/
def bridgeSwap : GraphIso bridge bridgeFlip where
  vertex := Equiv.swap 0 1
  edge := Equiv.refl _
  branch _ := Equiv.swap 0 1
  endpoint := by decide
  genus := by decide
  marking := by decide

/-! ### Contractions and the genus update -/

/-- Contracting the edge of `bridge` adds the two genera. -/
def contractBridge : GraphContraction bridge smooth where
  selected := Finset.univ
  vertex _ := 0
  onto := by decide
  edge := @Equiv.equivOfIsEmpty _ _ ⟨fun e ↦ e.2 (Finset.mem_univ _)⟩ _
  branch _ := Equiv.refl _
  surviving e := (e.2 (Finset.mem_univ _)).elim
  contracted := by decide
  fiberConnected v w _ := by
    fin_cases v <;> fin_cases w
    · exact .refl
    · exact .single ⟨0, Finset.mem_univ _, .inl ⟨rfl, rfl⟩⟩
    · exact .single ⟨0, Finset.mem_univ _, .inr ⟨rfl, rfl⟩⟩
    · exact .refl
  marking := by decide
  genus := by decide

/-- Contracting a selected loop raises the genus of its vertex by one. -/
def contractLoop : GraphContraction loopGraph smooth where
  selected := Finset.univ
  vertex _ := 0
  onto := by decide
  edge := @Equiv.equivOfIsEmpty _ _ ⟨fun e ↦ e.2 (Finset.mem_univ _)⟩ _
  branch _ := Equiv.refl _
  surviving e := (e.2 (Finset.mem_univ _)).elim
  contracted := by decide
  fiberConnected v w _ := by rw [Subsingleton.elim v w]
  marking := by decide
  genus := by decide

/-- Contracting one edge of `banana` turns the other edge into a loop. -/
def contractBanana : GraphContraction banana loopGraph where
  selected := {0}
  vertex _ := 0
  onto := by decide
  edge :=
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ ⟨1, by decide⟩
      left_inv := fun ⟨e, he⟩ ↦ by
        fin_cases e
        · exact absurd (Finset.mem_singleton_self _) he
        · rfl
      right_inv := fun i ↦ Subsingleton.elim _ _ }
  branch _ := Equiv.refl _
  surviving _ _ := rfl
  contracted := by decide
  fiberConnected v w _ := by
    fin_cases v <;> fin_cases w
    · exact .refl
    · exact .single ⟨0, Finset.mem_singleton_self _, .inl ⟨rfl, rfl⟩⟩
    · exact .single ⟨0, Finset.mem_singleton_self _, .inr ⟨rfl, rfl⟩⟩
    · exact .refl
  marking := by decide
  genus := by decide

/-! ### Universal stability on concrete graphs -/

section Stability

variable {d : ℚ} (φ : UniversalStability 2 1 d)

-- Contraction sums the weights over the fibre.
example : φ.weight smooth 0 = φ.weight bridge 0 + φ.weight bridge 1 := by
  simpa [contractBridge, Fin.sum_univ_two] using φ.contraction _ _ contractBridge 0

example : φ.weight smooth 0 = φ.weight loopGraph 0 := by
  simpa [contractLoop] using φ.contraction _ _ contractLoop 0

example : φ.weight loopGraph 0 = φ.weight banana 0 + φ.weight banana 1 := by
  simpa [contractBanana, Fin.sum_univ_two] using
    φ.contraction _ _ contractBanana 0

-- A one-vertex graph carries the whole degree.
example : φ.weight smooth 0 = d := by
  simpa using φ.total smooth

-- Isomorphisms transport weights to the corresponding vertex.
example : φ.weight bridgeFlip 1 = φ.weight bridge 0 :=
  φ.isomorphism _ _ bridgeSwap 0

-- On a two-vertex graph the weights add up to the degree.
example : φ.weight bridge 0 + φ.weight bridge 1 = d := by
  simpa [Fin.sum_univ_two] using φ.total bridge

end Stability

example : (zeroStability 2 1).weight banana 1 = 0 := rfl

example : (zeroStability 2 1).weight smooth 0 =
    ∑ v, if contractBridge.vertex v = 0 then (zeroStability 2 1).weight bridge v
      else 0 :=
  (zeroStability 2 1).contraction _ _ contractBridge 0

end MathlibExtTest.UniversalCurveStability
