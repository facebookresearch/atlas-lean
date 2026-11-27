/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# Removing unused inputs from a weighted circuit

The declared number of variables is encoded in binary. Enumerating all
of them need not be polynomial in the encoded input. The circuit reads at
most one variable per gate. A small pool of fresh variables suffices to
preserve the range of weights that can be assigned to the variables it reads.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support

open Cslib.Complexity.Classes

/-- The variable read by a gate, if its variable index is valid. -/
def inputOf (n : ℕ) : WCGate → Option ℕ
  | (0, [i]) => if i < n then some i else none
  | _ => none

/-- Input variables actually named by a valid input gate. -/
def active (n : ℕ) (C : List WCGate) : Finset ℕ := (C.filterMap (inputOf n)).toFinset

theorem active_card_le (n : ℕ) (C : List WCGate) : (active n C).card ≤ C.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

private theorem active_mem_iff {n i : ℕ} {C : List WCGate} :
    i ∈ active n C ↔ i < n ∧ (0, [i]) ∈ C := by
  simp only [active, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨g, hg, h⟩
    unfold inputOf at h
    split at h
    · split at h <;> simp_all
    · contradiction
  · rintro ⟨hi, hg⟩
    exact ⟨_, hg, by simp [inputOf, hi]⟩

theorem active_subset (n : ℕ) (C : List WCGate) : active n C ⊆ Finset.range n :=
  fun _ h => Finset.mem_range.mpr (active_mem_iff.mp h).1

/-- The entire trace of gate values depends only on the active variables. -/
theorem eval_eq_of_agree {n : ℕ} (C : List WCGate) {a b : Fin n → Bool}
    (agree : ∀ i : Fin n, i.val ∈ active n C → a i = b i) :
    circuitEval (C.map (acGateOfPair (n := n))) a =
      circuitEval (C.map (acGateOfPair (n := n))) b := by
  unfold circuitEval
  simp only [List.foldl_map]
  apply List.foldl_ext
  intro vs g hg
  rw [← gateValue_ofPair, ← gateValue_ofPair]
  congr 2
  unfold serialGateEval
  split <;> try rfl
  split <;> try rfl
  apply agree
  exact active_mem_iff.mpr ⟨by assumption, hg⟩

/-- An assignment on a retained subset of the variables extends to weight `k`
iff its number of true variables is in the feasible interval. -/
theorem exists_extension_iff {α : Type*} [DecidableEq α] (U A : Finset α)
    (hA : A ⊆ U) (k : ℕ) (ok : Finset α → Prop) :
    (∃ S ⊆ U, S.card = k ∧ ok (S ∩ A)) ↔
      k ≤ U.card ∧ ∃ T ⊆ A, T.card ≤ k ∧ k ≤ T.card + (U.card - A.card) ∧ ok T := by
  have hfree := Finset.card_sdiff_add_card_eq_card hA
  constructor
  · rintro ⟨S, hSU, rfl, hs⟩
    refine ⟨Finset.card_le_card hSU, S ∩ A, Finset.inter_subset_right,
      Finset.card_le_card Finset.inter_subset_left, ?_, hs⟩
    have hsub : S \ A ⊆ U \ A := fun x hx =>
      Finset.mem_sdiff.mpr ⟨hSU (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
    have := Finset.card_le_card hsub
    have := Finset.card_sdiff_add_card_inter S A
    omega
  · rintro ⟨_, T, hT, hTk, hk, hok⟩
    obtain ⟨D, hD, hn⟩ := Finset.exists_subset_card_eq
      (s := U \ A) (n := k - T.card) (by omega)
    have dis : Disjoint T D := Finset.disjoint_left.mpr fun _ hx hy =>
      (Finset.mem_sdiff.mp (hD hy)).2 (hT hx)
    have eqT : (T ∪ D) ∩ A = T := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨ht | hd, ha⟩
        · exact ht
        · exact ((Finset.mem_sdiff.mp (hD hd)).2 ha).elim
      · exact fun ht => ⟨Or.inl ht, hT ht⟩
    refine ⟨T ∪ D, Finset.union_subset (hT.trans hA)
      (fun _ hx => (Finset.mem_sdiff.mp (hD hx)).1), ?_, by simpa only [eqT] using hok⟩
    rw [Finset.card_union_of_disjoint dis, hn]
    omega

/-- The replacement pool has one dummy variable for each unit between the smallest
and largest feasible true weight on the active variables. -/
def dummyCount (n m k : ℕ) : ℕ := min k m - (k - (n - m))

/-- Label fresh variables starting at `n`, beyond the old inputs. Only the
short range of fresh indices is enumerated by the construction. -/
def compactUniverse (n k : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A ∪ (Finset.range (dummyCount n A.card k)).image (n + ·)

theorem compactUniverse_card {n : ℕ} (k : ℕ) (A : Finset ℕ) (ha : A ⊆ Finset.range n) :
    (compactUniverse n k A).card = A.card + dummyCount n A.card k := by
  unfold compactUniverse
  have hinj : Function.Injective (n + ·) := fun _ _ h => Nat.add_left_cancel h
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ hinj]
  · simp
  · apply Finset.disjoint_left.mpr
    rintro x hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    have := Finset.mem_range.mp (ha hx)
    omega

theorem compactUniverse_size {n : ℕ} (k : ℕ) (C : List WCGate) :
    (compactUniverse n k (active n C)).card ≤ 2 * C.length := by
  rw [compactUniverse_card k _ (active_subset _ _)]
  have := active_card_le n C
  unfold dummyCount
  omega

/-- Let `A` be a subset of the `n` input variables and suppose `k ≤ n`. For any condition
on the selected variables in `A`, there is a selection of exactly `k` of the original inputs
meeting the condition if and only if there is a selection of exactly `min k A.card` inputs
from `compactUniverse n k A` meeting the same condition. -/
theorem compress_weight {n k : ℕ} (hk : k ≤ n) (A : Finset ℕ)
    (hA : A ⊆ Finset.range n) (ok : Finset ℕ → Prop) :
    (∃ S ⊆ Finset.range n, S.card = k ∧ ok (S ∩ A)) ↔
      ∃ S ⊆ compactUniverse n k A, S.card = min k A.card ∧ ok (S ∩ A) := by
  have hsub : A ⊆ compactUniverse n k A := Finset.subset_union_left
  rw [exists_extension_iff _ A hA, exists_extension_iff _ A hsub]
  rw [compactUniverse_card k A hA, Finset.card_range]
  have hm : A.card ≤ n := by simpa using Finset.card_le_card hA
  unfold dummyCount
  constructor <;> rintro ⟨_, T, ht, h₁, h₂, ho⟩
  all_goals
    have := Finset.card_le_card ht
    exact ⟨by omega, T, ht, by omega, by omega, ho⟩

/-- Turn on the entries indexed by a set of labels in an enumeration. -/
def bits (labels : List ℕ) (S : Finset ℕ) : List Bool :=
  labels.map fun v => decide (v ∈ S)

private theorem bits_weight (labels : List ℕ) (hn : labels.Nodup) (S : Finset ℕ)
    (hS : S ⊆ labels.toFinset) : ((bits labels S).filter id).length = S.card := by
  rw [← List.countP_eq_length_filter, bits, List.countP_map]
  have he : labels.toFinset.filter (· ∈ S) = S := by
    ext i
    exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨hS h, h⟩⟩
  exact (hn.card_eq_countP (P := (· ∈ S))).symm.trans (congrArg Finset.card he)

/-- Quantifying over exact-weight Boolean lists is equivalent to quantifying over
sets of active labels, for any numbering without repetitions. -/
theorem numbered_assignments (labels : List ℕ) (hn : labels.Nodup) (k : ℕ)
    (test : List Bool → Prop) :
    (∃ a : List Bool, a.length = labels.length ∧ (a.filter id).length = k ∧ test a) ↔
      ∃ S ⊆ labels.toFinset, S.card = k ∧ test (bits labels S) := by
  constructor
  · rintro ⟨a, hlen, hw, ha⟩
    let S := labels.toFinset.filter (fun v => a.getD (labels.idxOf v) false = true)
    have hs : S ⊆ labels.toFinset := Finset.filter_subset _ _
    have eq : bits labels S = a := by
      apply List.ext_getElem
      · simp [bits, hlen]
      · intro i hi hj
        have hl : i < labels.length := by omega
        have hv := List.getElem_mem hl
        simp [bits, S, hv, hn.idxOf_getElem i hl, List.getElem?_eq_getElem hj]
    exact ⟨S, hs, (bits_weight _ hn S hs).symm.trans (eq ▸ hw), eq ▸ ha⟩
  · rintro ⟨S, hs, hk, hh⟩
    exact ⟨bits labels S, by simp [bits], (bits_weight _ hn S hs).trans hk, hh⟩

/-- Leave graph wiring intact and rewrite only variable payloads. Out-of-range
input references still read false in the new instance. -/
def reindexGate (n : ℕ) (labels : List ℕ) : WCGate → WCGate
  | (0, [i]) => (0, [if i < n then labels.idxOf i else labels.length])
  | g => g

private theorem reindex_checks (n : ℕ) (labels : List ℕ) (C : List WCGate) :
    WCWellFormed (C.map (reindexGate n labels)) ↔ WCWellFormed C := by
  have one (j : ℕ) (g : WCGate) :
      (∀ a ∈ (reindexGate n labels g).2, (reindexGate n labels g).1 = 2 ∨
        (reindexGate n labels g).1 = 3 ∨ (reindexGate n labels g).1 = 4 → a < j) ↔
      (∀ a ∈ g.2, g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4 → a < j) := by
    unfold reindexGate
    split <;> simp
  simp only [WCWellFormed, List.length_map, List.getElem_map, one]

private theorem reindex_wefts (n : ℕ) (labels : List ℕ) (C : List WCGate) :
    wcCircuitWefts (C.map (reindexGate n labels)) = wcCircuitWefts C := by
  unfold wcCircuitWefts
  rw [List.foldl_map]
  apply List.foldl_ext
  intro vs g _
  unfold reindexGate
  split <;> rfl

private theorem reindex_depths (n : ℕ) (labels : List ℕ) (C : List WCGate) :
    wcCircuitDepths (C.map (reindexGate n labels)) = wcCircuitDepths C := by
  unfold wcCircuitDepths
  rw [List.foldl_map]
  apply List.foldl_ext
  intro vs g _
  unfold reindexGate
  split <;> rfl

/-- Evaluate the original circuit with true inputs `S`, without allocating a
list of the (binary-encoded) declared length. -/
def evalSet (n : ℕ) (C : List WCGate) (S : Finset ℕ) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n))) (fun i => decide (i.val ∈ S))

private theorem eval_full (n : ℕ) (C : List WCGate) (S : Finset ℕ) :
    wcCircuitEval C (bits (List.range n) S) = evalSet n C (S ∩ active n C) := by
  have hlen : (bits (List.range n) S).length = n := by simp [bits]
  unfold wcCircuitEval evalSet
  generalize ha : bits (List.range n) S = a at hlen ⊢
  subst n
  apply eval_eq_of_agree
  intro i hi
  simp only [Finset.mem_inter, hi, and_true]
  calc
    a.getD i.val false = (bits (List.range a.length) S).getD i.val false :=
      congrArg (fun (xs : List Bool) => xs.getD i.val false) ha.symm
    _ = _ := by simp [bits, i.isLt]

private theorem eval_reindexed (n : ℕ) (labels : List ℕ) (C : List WCGate)
    (cover : active n C ⊆ labels.toFinset) (S : Finset ℕ) :
    wcCircuitEval (C.map (reindexGate n labels)) (bits labels S) =
      evalSet n C (S ∩ active n C) := by
  unfold wcCircuitEval evalSet circuitEval
  simp only [List.foldl_map]
  apply List.foldl_ext
  intro vs g hg
  rw [← gateValue_ofPair, ← gateValue_ofPair]
  congr 2
  unfold reindexGate
  split
  · rename_i i
    by_cases hi : i < n
    · have hv : i ∈ active n C := active_mem_iff.mpr ⟨hi, hg⟩
      have hl := List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp (cover hv))
      simp [serialGateEval, hi, bits, hv, hl, List.getElem_idxOf hl]
    · simp [serialGateEval, hi, bits]
  · unfold serialGateEval
    split <;> first | rfl | solve_by_elim

/-- A list of at most twice as many labels as gates, computable using the
actual variables and a short list of dummy variables. -/
def labels (n k : ℕ) (C : List WCGate) : List ℕ :=
  (compactUniverse n k (active n C)).sort

theorem labels_length_le (n k : ℕ) (C : List WCGate) : (labels n k C).length ≤ 2 * C.length := by
  simpa [labels] using compactUniverse_size (n := n) k C

/-- Suppose `k ≤ n` and let `m` be the number of active inputs of the circuit `C` on `n`
inputs. For any weft and depth bounds, weighted circuit satisfiability accepts `C` at weight
`k` if and only if it accepts the circuit reindexed on the compact input labels at weight
`min k m` under the same bounds. -/
theorem reindex_correct (n k : ℕ) (hk : k ≤ n) (C : List WCGate) (t d : ℕ) :
    let L := labels n k C
    let E := MetaMathlibExt.BitstringEncoding.bitEncode (α := ℕ × List WCGate)
    WeightedCircuitSat t d (E (n, C)) k ↔
      WeightedCircuitSat t d (E (L.length, C.map (reindexGate n L))) (min k (active n C).card) := by
  let A := active n C
  let L := labels n k C
  let ok (s : Finset ℕ) := (evalSet n C s).getLast? = some true
  have hsub : A ⊆ L.toFinset := by
    change A ⊆ (compactUniverse n k A).sort.toFinset
    rw [Finset.sort_toFinset]
    exact Finset.subset_union_left
  have congr (a : List Bool) : a.length = n ↔ a.length = (List.range n).length := by simp
  dsimp only
  simp only [WeightedCircuitSat, MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode,
    decide_eq_true_eq, reindex_checks, reindex_wefts, reindex_depths]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  change (∃ a : List Bool, a.length = n ∧ (a.filter id).length = k ∧
    (wcCircuitEval C a).getLast? = some true) ↔
    ∃ a : List Bool, a.length = L.length ∧ (a.filter id).length = min k A.card ∧
      (wcCircuitEval (C.map (reindexGate n L)) a).getLast? = some true
  simp_rw [congr]
  rw [numbered_assignments (List.range n) List.nodup_range,
      numbered_assignments L (Finset.sort_nodup ..)]
  have hU : (List.range n).toFinset = Finset.range n := by ext; simp
  simp_rw [eval_full, eval_reindexed n L C hsub]
  change (∃ S ⊆ (List.range n).toFinset, S.card = k ∧ ok (S ∩ A)) ↔
    ∃ S ⊆ L.toFinset, S.card = min k A.card ∧ ok (S ∩ A)
  rw [hU]
  simpa only [L, labels, Finset.sort_toFinset] using compress_weight hk A (active_subset ..) ok

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support
