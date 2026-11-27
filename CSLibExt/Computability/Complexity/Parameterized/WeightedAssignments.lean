/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagRows
public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitOutput
import CSLibExt.Computability.Complexity.Parameterized.Support
public import CSLibExt.Computability.Complexity.Parameterized.CircuitChecks
import Mathlib.Data.Finset.Sort

/-!
# Exact-weight Boolean assignments and increasing selections

The true positions of a Boolean list of weight $k$ form a $k$-element set. Its
increasing enumeration supplies the slot assignment in the local consistency graph.
The converse uses the indicator list of the image of a strictly increasing selection.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

private theorem bits_range_read {n : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range n) (i : ℕ) :
    (Support.bits (List.range n) s).getD i false = decide (i ∈ s) := by
  by_cases hi : i < n
  · have hlen : i < (Support.bits (List.range n) s).length := by simpa [Support.bits] using hi
    rw [List.getD_eq_getElem _ _ hlen]
    simp [Support.bits]
  · have hout : i ∉ s := fun h => hi (Finset.mem_range.mp (hs h))
    have hlen : (Support.bits (List.range n) s).length ≤ i := by simp [Support.bits]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, hout]

private theorem bits_literal {n : ℕ} {s : Finset ℕ} (hs : s ⊆ Finset.range n) :
    (fun l : ℕ × Bool => (Support.bits (List.range n) s).getD l.1 false = l.2) =
      WeightedClauses.literalTrue (s : Set ℕ) := by
  funext ⟨v, pos⟩
  apply propext
  rw [bits_range_read hs]
  cases pos <;> simp [WeightedClauses.literalTrue]

/-- An exact-weight Boolean witness satisfies a signed formula family precisely when a
strictly increasing selection of the same size satisfies one of its alternatives. -/
theorem exact_weight_iff_hasAssignment (k n : ℕ) (family : List Formula) :
    (∃ b : List Bool, b.length = n ∧ (b.filter id).length = k ∧
      NormalFormMachine.Satisfies (fun l : ℕ × Bool => b.getD l.1 false = l.2) family) ↔
      HasAssignment k n family := by
  classical
  have h := Support.numbered_assignments (List.range n) List.nodup_range k
    (fun b => NormalFormMachine.Satisfies (fun l : ℕ × Bool => b.getD l.1 false = l.2) family)
  have hrange : (List.range n).toFinset = Finset.range n := by ext i; simp
  rw [List.length_range, hrange] at h
  rw [h]
  constructor
  · rintro ⟨s, hs, hk, p, hp, hmodel⟩
    have sub : s ⊆ Finset.range n := hs
    let f := s.orderEmbOfFin hk
    refine ⟨p, hp, f, (fun i => Finset.mem_range.mp (sub (s.orderEmbOfFin_mem hk i))),
      f.strictMono, ?_⟩
    change NormalFormMachine.Models (WeightedClauses.literalTrue (Set.range (s.orderEmbOfFin hk))) p
    rw [Finset.range_orderEmbOfFin]
    rw [bits_literal sub] at hmodel
    exact hmodel
  · rintro ⟨p, hp, f, hf, hmono, hmodel⟩
    let s := Finset.univ.image f
    have sub : s ⊆ Finset.range n := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (hf j)
    have card : s.card = k := by
      rw [show s = Finset.univ.image f from rfl, Finset.card_image_of_injective _ hmono.injective]
      simp
    have eqn : (s : Set ℕ) = Set.range f := by ext i; simp [s, Set.mem_range]
    refine ⟨s, sub, card, p, hp, ?_⟩
    rw [bits_literal sub, eqn]
    exact hmodel

/-- Attach any semantics-preserving family of signed formulas to the original weighted
circuit problem. The given decoder equation also permits noncanonical source encodings. -/
theorem weightedCircuitSat_iff_hasAssignment_of_family {x : List Bool} {n : ℕ} {C : List WCGate}
    (hx : MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, C)) (d k : ℕ)
    (family : List Formula) (sem : ∀ b : List Bool, b.length = n →
      (NormalFormMachine.Satisfies (fun l : ℕ × Bool => b.getD l.1 false = l.2) family ↔
        NormalForm.validCircuit 1 d C ∧ (wcCircuitEval C b).getLast? = some true)) :
    WeightedCircuitSat 1 d x k ↔ HasAssignment k n family := by
  rw [← exact_weight_iff_hasAssignment]
  simp only [WeightedCircuitSat, hx, decide_eq_true_eq]
  constructor
  · rintro ⟨wf, weft, depth, b, hb, weight, heval⟩
    exact ⟨b, hb, weight, (sem b hb).mpr ⟨(NormalForm.validCircuit_iff ..).mpr
      ⟨wf, weft, depth⟩, heval⟩⟩
  · rintro ⟨b, hb, weight, hm⟩
    obtain ⟨valid, heval⟩ := (sem b hb).mp hm
    obtain ⟨wf, weft, depth⟩ := (NormalForm.validCircuit_iff ..).mp valid
    exact ⟨wf, weft, depth, b, hb, weight, heval⟩

/-- On every successfully decoded circuit, the constructed signed family has a strictly
increasing selection exactly when the source weighted circuit is a yes instance. -/
theorem weightedCircuitSat_iff_familyHasAssignment {x : List Bool} {n : ℕ} {C : List WCGate}
    (hx : MetaMathlibExt.BitstringEncoding.bitDecode x = some (n, C)) (d k : ℕ) :
    WeightedCircuitSat 1 d x k ↔ HasAssignment k n (CircuitNormalMachine.family d n C) := by
  apply weightedCircuitSat_iff_hasAssignment_of_family hx d k
  intro b hb
  have eqn : CircuitNormalMachine.literalHolds b = (fun l : ℕ × Bool => b.getD l.1 false = l.2) :=
    funext fun _ => rfl
  simpa only [hb, eqn] using CircuitNormalMachine.family_satisfies d C b

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
