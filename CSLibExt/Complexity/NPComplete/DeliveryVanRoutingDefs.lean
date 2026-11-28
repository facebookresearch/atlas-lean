/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DELIVERY VAN ROUTING: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3, problem [4] DELIVERY VAN ROUTING (reference: H. Boers,
"The 'race graph': an NP-complete problem", manuscript, 1982, not available; transformation from
3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting

/-- An instance: the vertex count `n`, the arcs `(tail, head, w)` with the weight `w` as a
(positive part, negative part) pair, and the vertex `s`. -/
abbrev DeliveryVanRoutingInstance := ℕ × List (ℕ × ℕ × (ℕ × ℕ)) × ℕ

/-- The integer weight `w(a)` of an arc. -/
def weight (a : ℕ × ℕ × (ℕ × ℕ)) : ℤ := (a.2.2.1 : ℤ) - a.2.2.2

/-- Well-formedness of an instance: no two arcs with the same tail and head, every arc joins two
distinct vertices in range, and `s ∈ V`. -/
def WellFormed (i : DeliveryVanRoutingInstance) : Prop :=
  (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1) ∧ i.2.2 < i.1

/-- Some ordering `P` of all the arcs is an Euler tour that starts and ends at `s` and whose
every prefix has total weight at most `0`. -/
def DeliveryVanRoutingFeasible (i : DeliveryVanRoutingInstance) : Prop :=
  ∃ P : List (Fin i.2.1.length), P.Perm (List.finRange i.2.1.length) ∧
    (∀ j (h : j + 1 < P.length), (i.2.1[P[j]]).2.1 = (i.2.1[P[j + 1]]).1) ∧
    (∃ h : 0 < P.length, (i.2.1[P[0]]).1 = i.2.2 ∧ (i.2.1[P[P.length - 1]]).2.1 = i.2.2) ∧
    ∀ j ≤ P.length, ((P.take j).map fun a => weight i.2.1[a]).sum ≤ 0

open Classical in
/-- DELIVERY VAN ROUTING as a decision problem over bitstrings. -/
noncomputable def deliveryVanRoutingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DeliveryVanRoutingInstance) x with
  | some i => decide (WellFormed i ∧ DeliveryVanRoutingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DeliveryVanRouting
