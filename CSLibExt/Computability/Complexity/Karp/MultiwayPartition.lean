/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.Karp.PartitionSizes
import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListCount
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import CSLibExt.Computability.Complexity.PolynomialEncoding.UnaryNat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.IntervalCases

/-!
# MULTIWAY NUMBER PARTITION is NP-complete

This module proves NP membership with a polynomial-time verifier for part masks and a
common binary target sum. It proves NP-hardness via a reduction from PARTITION that
uses two zero entries to enforce the nonempty-parts condition.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PARTITION
[SP12], from which NP-hardness follows by reduction.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayPartition

/-- **Multiway number partition instances.** A multiway number partition instance is a pair
$(a, K)$ consisting of a list $a$ of natural numbers and a natural number $K$ (the number of
parts). -/
abbrev MultiwayPartitionInstance := List ℕ × ℕ

/-- **Feasible multiway number partition instances.** Let $(a, K)$ be a multiway number partition
instance with $a = (a_0, \dots, a_{m-1})$. It is feasible when $K \ge 1$ and there is a map $f$
from $\{0, \dots, m-1\}$ onto $\{0, \dots, K-1\}$ such that the sums
$\sum_{j < m,\, f(j) = p} a_j$ for $p = 0, \dots, K-1$ are all equal. In other words, the entries
of $a$, counted with repetition, can be split into $K$ nonempty parts with equal sums. -/
def MultiwayPartitionFeasible
    (i : MultiwayPartitionInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1.length ∧ 0 < i.2 ∧
    (∀ j < i.1.length, assign.getD j 0 < i.2) ∧
    (∀ p < i.2, ∃ j < i.1.length, assign.getD j 0 = p) ∧
    ∃ T, ∀ p < i.2, (Finset.range i.1.length).sum
      (fun j => if assign.getD j 0 = p then i.1.getD j 0 else 0) = T

open Classical in
/-- **The MULTIWAY NUMBER PARTITION decision problem.** MULTIWAY NUMBER PARTITION is the decision
problem on bitstrings that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding, to a multiway number partition instance $(a, K)$ that is feasible. Bitstrings
that do not decode to a multiway number partition instance are rejected. -/
noncomputable def multiwayPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiwayPartitionInstance) x with
  | some i => decide (MultiwayPartitionFeasible i)
  | none => false

-- Write an assignment as one Boolean mask per part.
open BitstringEncoding Cslib.Complexity.Karp

private theorem sum_pick_label (as assign : List ℕ) (p : ℕ)
    (h : assign.length = as.length) :
    (SSVerify.pick as (assign.map (fun q => decide (q = p)))).sum =
      (Finset.range as.length).sum (fun j => if assign.getD j 0 = p then as.getD j 0 else 0) := by
  induction as generalizing assign with
  | nil => simp [SSVerify.pick]
  | cons a as ih =>
    cases assign with
    | nil => simp at h
    | cons q qs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.length_cons, Finset.sum_range_succ']
      by_cases e : q = p <;>
        simp [SSVerify.pick, e, ih qs h, Nat.add_comm]

private def merge : List Bool → List Bool → Option (List Bool)
  | [], [] => some []
  | b :: r, c :: u =>
    if b && c then none else (merge r u).map ((b || c) :: ·)
  | _, _ => none

private def column (rs : List (List Bool)) (j : ℕ) : ℕ :=
  (rs.map fun r => (r.getD j false).toNat).sum

private theorem merge_eq_some_iff {r u v : List Bool} :
    merge r u = some v ↔ r.length = u.length ∧ v.length = u.length ∧
      ∀ j < u.length, (r.getD j false).toNat + (u.getD j false).toNat =
        (v.getD j false).toNat := by
  induction r generalizing u v with
  | nil => cases u <;> cases v <;> simp [merge]
  | cons b r ih =>
    cases u with
    | nil => simp [merge]
    | cons c u =>
      cases v with
      | nil => cases b <;> cases c <;> simp [merge]
      | cons d v =>
        have h : (∀ j < u.length + 1,
            ((b :: r).getD j false).toNat + ((c :: u).getD j false).toNat =
              ((d :: v).getD j false).toNat) ↔
            b.toNat + c.toNat = d.toNat ∧ ∀ j < u.length,
              (r.getD j false).toNat + (u.getD j false).toNat =
                (v.getD j false).toNat := by
          constructor
          · intro h
            exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
          · rintro ⟨h0, htail⟩ (j | j) hj
            · exact h0
            · exact htail j (by omega)
        simp only [List.length_cons, Nat.add_right_cancel_iff, h, merge]
        cases b <;> cases c <;> cases d <;> simp [ih, and_assoc]

private def mergeRows : List (List Bool) → List Bool → Option (List Bool)
  | [], u => some u
  | r :: rs, u => (merge r u).bind (mergeRows rs)

private theorem mergeRows_eq_some_iff {rs : List (List Bool)} {u v : List Bool} :
    mergeRows rs u = some v ↔ v.length = u.length ∧
      (∀ r ∈ rs, r.length = u.length) ∧
      ∀ j < u.length, column rs j + (u.getD j false).toNat = (v.getD j false).toNat := by
  induction rs generalizing u v with
  | nil =>
    simp only [mergeRows, Option.some.injEq, List.not_mem_nil, false_implies,
      implies_true, true_and, column, List.map_nil, List.sum_nil, zero_add]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hlen, h⟩
      apply List.ext_getElem hlen.symm
      intro j hju hjv
      have hj := h j hju
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hju,
        List.getElem?_eq_getElem hjv, Option.getD_some] at hj
      cases hu : u[j] <;> cases hv : v[j] <;> simp_all
  | cons r rs ih =>
    simp only [mergeRows, Option.bind_eq_some_iff, merge_eq_some_iff, ih, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hr, hw, hru⟩, hv, hrs, hrw⟩
      refine ⟨hv.trans hw, ?_, fun j hj => ?_⟩
      · rintro a (rfl | ha)
        · exact hr
        · exact (hrs _ ha).trans hw
      · have h₁ := hru j hj
        have h₂ := hrw j (hw ▸ hj)
        simp only [column, List.map_cons, List.sum_cons]
        unfold column at h₂
        omega
    · rintro ⟨hv, hr, hall⟩
      let w := List.zipWith (· || ·) r u
      have hru := hr r (Or.inl rfl)
      have hw : w.length = u.length := by simp [w, hru]
      have hbits (j : ℕ) (hj : j < u.length) :
          (r.getD j false).toNat + (u.getD j false).toNat = (w.getD j false).toNat := by
        have hx := hall j hj
        simp only [column, List.map_cons, List.sum_cons] at hx
        have hq : w.getD j false = (r.getD j false || u.getD j false) := by
          simp [w, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
            List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (hru ▸ hj)]
        rw [hq]
        have hvb : (v.getD j false).toNat ≤ 1 := by cases v.getD j false <;> decide
        cases hb : r.getD j false <;> cases hc : u.getD j false <;>
          simp only [hb, hc, Bool.or_false, Bool.or_true, Bool.toNat_false, Bool.toNat_true,
            Nat.add_zero, Nat.zero_add] at hx ⊢
        omega
      refine ⟨w, ⟨hru, hw, hbits⟩, hv.trans hw.symm, ?_, ?_⟩
      · exact fun a ha => (hr a (Or.inr ha)).trans hw.symm
      · intro j hj
        have hj' : j < u.length := hw ▸ hj
        have h₁ := hall j hj'
        have h₂ := hbits j hj'
        simp only [column, List.map_cons, List.sum_cons] at h₁ ⊢
        omega

private def covers (rs : List (List Bool)) (m : ℕ) : Prop :=
  mergeRows rs (List.replicate m false) = some (List.replicate m true)

private theorem covers_iff {rs : List (List Bool)} {m : ℕ} :
    covers rs m ↔ (∀ r ∈ rs, r.length = m) ∧ ∀ j < m, column rs j = 1 := by
  rw [covers, mergeRows_eq_some_iff]
  simp only [List.length_replicate, true_and]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  simp [List.getD_eq_getElem?_getD, hj]

private theorem column_eq_sum (rs : List (List Bool)) (j : ℕ) :
    column rs j = (Finset.range rs.length).sum (fun p => ((rs.getD p []).getD j false).toNat) := by
  induction rs with
  | nil => simp [column]
  | cons r rs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    change (r.getD j false).toNat + column rs j =
      (∑ p ∈ Finset.range rs.length, ((rs.getD p []).getD j false).toNat) +
        (r.getD j false).toNat
    rw [ih, Nat.add_comm]

private theorem column_eq_one_iff (rs : List (List Bool)) (j : ℕ) :
    column rs j = 1 ↔ ∃! p, p < rs.length ∧ (rs.getD p []).getD j false = true := by
  rw [column_eq_sum]
  have h (p : ℕ) : ((rs.getD p []).getD j false).toNat =
      if (rs.getD p []).getD j false = true then 1 else 0 := by
    cases (rs.getD p []).getD j false <;> rfl
  simp_rw [h]
  rw [Finset.sum_boole, Nat.cast_id, Finset.card_eq_one_iff_existsUnique]
  simp only [Finset.mem_filter, Finset.mem_range]

private theorem row_any_iff (r : List Bool) :
    r.any id = true ↔ ∃ j < r.length, r.getD j false = true := by
  simp only [List.any_eq_true, id_eq, List.exists_mem_iff_getElem]
  apply exists_congr
  intro j
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h⟩

private theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (z : α) {j : ℕ}
    (hj : j < n) : (List.ofFn f).getD j z = f ⟨j, hj⟩ := by
  have h : j < (List.ofFn f).length := by simpa using hj
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private def valid (as : List ℕ) (k : ℕ) (rs : List (List Bool)) (T : ℕ) : Prop :=
  rs.length = k ∧ 0 < k ∧ covers rs as.length ∧
    ∀ r ∈ rs, r.any id = true ∧ (SSVerify.pick as r).sum = T

private theorem feasible_iff_valid (as : List ℕ) (k : ℕ) :
    MultiwayPartitionFeasible (as, k) ↔ ∃ rs T, valid as k rs T := by
  classical
  constructor
  · rintro ⟨a, hl, hk, hrange, hon, T, hT⟩
    change a.length = as.length at hl
    let rs := List.ofFn fun p : Fin k => a.map (fun q => decide (q = p.val))
    have hn : rs.length = k := List.length_ofFn
    have hr (p : ℕ) (hp : p < k) : rs.getD p [] = a.map (fun q => decide (q = p)) :=
      getD_ofFn _ _ hp
    have hbit (p : ℕ) (hp : p < k) (j : ℕ) (hj : j < as.length) :
        (rs.getD p []).getD j false = true ↔ a.getD j 0 = p := by
      have hja : j < a.length := hl ▸ hj
      rw [hr p hp]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hja]
    refine ⟨rs, T, hn, hk, covers_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · intro r hm
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hm
      have hpk : p < k := hn ▸ hp
      have he := hr p hpk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
        Option.getD_some] at he
      simp [he, hl]
    · intro j hj
      apply (column_eq_one_iff _ _).mpr
      refine ⟨a.getD j 0, ⟨by simpa [hn] using hrange j hj, ?_⟩, ?_⟩
      · exact (hbit _ (hrange j hj) j hj).mpr rfl
      · rintro p ⟨hp, hb⟩
        exact ((hbit _ (hn ▸ hp) j hj).mp hb).symm
    · intro r hm
      obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hm
      have hpk : p < k := hn ▸ hp
      have he := hr p hpk
      have he₀ : rs.getD p [] = rs[p] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
      rw [← he₀]
      refine ⟨(row_any_iff _).mpr ?_, ?_⟩
      · obtain ⟨j, hj, hh⟩ := hon p hpk
        refine ⟨j, ?_, (hbit p hpk j hj).mpr hh⟩
        rw [hr p hpk, List.length_map, hl]
        exact hj
      · rw [hr p hpk, sum_pick_label as a p hl]
        exact hT p hpk
  · rintro ⟨rs, T, hn, hk, hc, hs⟩
    obtain ⟨hl, hall⟩ := covers_iff.mp hc
    have he (j : Fin as.length) :
        ∃ p, p < rs.length ∧ (rs.getD p []).getD j.val false = true :=
      ((column_eq_one_iff rs j.val).mp (hall _ j.isLt)).exists
    let a := List.ofFn fun j : Fin as.length => Classical.choose (he j)
    have ha : a.length = as.length := List.length_ofFn
    have hag (j : ℕ) (hj : j < as.length) : a.getD j 0 = Classical.choose (he ⟨j, hj⟩) :=
      getD_ofFn _ _ hj
    have h_range (j : ℕ) (hj : j < as.length) : a.getD j 0 < k := by
      rw [hag j hj, ← hn]
      exact (Classical.choose_spec (he ⟨j, hj⟩)).1
    have hb (p : ℕ) (hp : p < k) (j : ℕ) (hj : j < as.length) :
        (rs.getD p []).getD j false = true ↔ a.getD j 0 = p := by
      have h₀ := Classical.choose_spec (he ⟨j, hj⟩)
      obtain ⟨q, _, hq⟩ := (column_eq_one_iff rs j).mp (hall j hj)
      constructor
      · intro h
        rw [hag j hj, hq _ h₀, hq p ⟨hn.symm ▸ hp, h⟩]
      · intro h
        rw [hag j hj] at h
        rw [← h]
        exact h₀.2
    have hrow (p : ℕ) (hp : p < k) : rs.getD p [] ∈ rs := by
      have hpr : p < rs.length := hn.symm ▸ hp
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpr, Option.getD_some]
      exact List.getElem_mem _
    refine ⟨a, ha, hk, h_range, ?_, T, ?_⟩
    · intro p hp
      obtain ⟨j, hj, hh⟩ := (row_any_iff _).mp (hs _ (hrow p hp)).1
      rw [hl _ (hrow p hp)] at hj
      exact ⟨j, hj, (hb p hp j hj).mp hh⟩
    · intro p hp
      have hm : rs.getD p [] = a.map (fun q => decide (q = p)) := by
        apply List.ext_getElem ((hl _ (hrow p hp)).trans (by simp [ha]))
        intro j h1 h2
        have hj : j < as.length := hl _ (hrow p hp) ▸ h1
        have hja : j < a.length := ha ▸ hj
        have hh := hb p hp j hj
        have ge (l : List Bool) (h : j < l.length) : l.getD j false = l[j] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
        have hga : a.getD j 0 = a[j] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hja]
        rw [ge _ h1, hga] at hh
        rw [Bool.eq_iff_iff]
        simpa only [List.getElem_map, decide_eq_true_eq] using hh
      rw [← sum_pick_label _ _ _ ha, ← hm]
      exact (hs _ (hrow p hp)).2

-- Check one framed mask and update the mask of positions already assigned.
namespace Row

open Turing Function TM2Program
open Cslib.Complexity.FramedCNF Cslib.Complexity.PolynomialEncoding

private inductive K | input | rev | row | used | next | mask
  deriving DecidableEq

private inductive Lab | read | back | merge (seen : Bool) | restore | copy | good | bad
  deriving DecidableEq

private instance instFintypeK : Fintype K where
  elems := {K.input, .rev, .row, .used, .next, .mask}
  complete k := by cases k <;> decide

private instance instFintypeLab : Fintype Lab where
  elems := {Lab.read, .back, .merge false, .merge true, .restore, .copy, .good, .bad}
  complete l := by
    cases l with
    | merge b => cases b <;> decide
    | _ => decide

private def storeMask (b seen : Bool) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .pop .used (fun _ o => o.getD false) <| .push .next (b || ·) <|
    .push .mask (fun _ => b) <| .goto fun _ => .merge (seen || b)

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .read => Block.read .input .rev some id .read .back .bad
  | .back => moveB .rev .row some id .back (.merge false)
  | .merge seen => .peek .row (fun _ o => o.isSome) <| .branch id
      (.peek .used (fun _ o => o.isSome) <| .branch id
        (.pop .row (fun _ o => o.getD false) <| .branch id
          (.peek .used (fun _ o => o.getD false) <| .branch id
            (.goto fun _ => .bad) (storeMask true seen)) (storeMask false seen))
        (.goto fun _ => .bad))
      (.peek .used (fun _ o => o.isNone) <| .branch id
        (.goto fun _ => if seen then .restore else .bad) (.goto fun _ => .bad))
  | .restore => moveB .next .used some id .restore .copy
  | .copy => moveB .mask .row some id .copy .good
  | .good | .bad => .halt

private def st (input rev row used next mask : List Bool) : K → List Bool
  | .input => input
  | .rev => rev
  | .row => row
  | .used => used
  | .next => next
  | .mask => mask

private theorem mergeStep (b c seen : Bool) (r u next mask x : List Bool) (v : Bool)
    (h : (b && c) = false) :
    Run prog 1 ⟨some (.merge seen), v, st x [] (b :: r) (c :: u) next mask⟩
      ⟨some (.merge (seen || b)), c, st x [] r u ((b || c) :: next) (b :: mask)⟩ := by
  have hst (d : Bool) :
      update (update (update (update (st x [] (b :: r) (c :: u) next mask)
        .row r) .used u) .next (d :: next)) .mask (b :: mask) =
        st x [] r u (d :: next) (b :: mask) := by
    funext k
    cases k <;> rfl
  apply Run.single
  cases b <;> cases c <;> simp [prog, storeMask, st, TM2.stepAux, hst] at h ⊢

private theorem loop (r u x next mask : List Bool) (seen v : Bool) :
    ∃ v' S, RunLe prog (r.length + 1)
      ⟨some (.merge seen), v, st x [] r u next mask⟩
      ⟨some (if (merge r u).isSome && (seen || r.any id) then .restore else .bad), v', S⟩ ∧
      ((seen || r.any id) = true → ∀ w, merge r u = some w →
        S = st x [] [] [] (w.reverse ++ next) (r.reverse ++ mask)) := by
  induction r generalizing u next mask seen v with
  | nil =>
    cases u with
    | cons c u =>
      exact ⟨false, st x [] [] (c :: u) next mask,
        (Run.single (by simp [prog, st, merge, TM2.stepAux])).le (by simp), by simp [merge]⟩
    | nil =>
      refine ⟨true, st x [] [] [] next mask,
        (Run.single (by simp [prog, st, merge, TM2.stepAux])).le (by simp), ?_⟩
      intro _ w h
      simp [merge] at h
      subst w
      rfl
  | cons b r ih =>
    cases u with
    | nil =>
      exact ⟨false, st x [] (b :: r) [] next mask,
        (Run.single (by simp [prog, st, merge, TM2.stepAux])).le (by simp), by simp [merge]⟩
    | cons c u =>
      by_cases h : (b && c) = false
      · have h₁ := mergeStep b c seen r u next mask x v h
        obtain ⟨v', S, h₂, hS⟩ := ih u ((b || c) :: next) (b :: mask) (seen || b) c
        have htest : ((merge (b :: r) (c :: u)).isSome && (seen || (b :: r).any id)) =
            ((merge r u).isSome && (seen || b || r.any id)) := by
          have hm : merge (b :: r) (c :: u) = (merge r u).map ((b || c) :: ·) := by
            simp only [merge, h, Bool.false_eq_true, reduceIte]
          rw [hm, Option.isSome_map, List.any_cons, id_eq, Bool.or_assoc]
        refine ⟨v', S, ?_, ?_⟩
        · rw [htest]
          exact ((h₁.le le_rfl).trans h₂).mono (by simp; omega)
        · intro hs w hw
          simp only [merge, h, Bool.false_eq_true, reduceIte] at hw
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hw
          rw [hS (by simpa [List.any_cons, Bool.or_assoc] using hs) w' hw']
          simp [List.reverse_cons, List.append_assoc]
      · cases b <;> cases c <;> simp at h
        refine ⟨true, st x [] r (true :: u) next mask, ?_, by simp [merge]⟩
        refine ⟨1, by simp, Run.single ?_⟩
        have hst : update (st x [] (true :: r) (true :: u) next mask) .row r =
            st x [] r (true :: u) next mask := by
          funext k
          cases k <;> rfl
        simp [prog, st, merge, TM2.stepAux, hst]

private def one (x u : List Bool) : Option (List Bool × List Bool × List Bool) :=
  (undelimit x).bind fun (r, t) =>
    if r.any id then (merge r u).map fun w => (r, t, w) else none

private theorem from_back (r x u : List Bool) :
    ∃ v S, Run prog (r.length + 1)
      ⟨some .back, false, st x r.reverse [] u [] []⟩
      ⟨some (.merge false), v, S⟩ ∧ S = st x [] r u [] [] := by
  obtain ⟨v, S, hr, he, hrow, hf⟩ := moveB_run (M := prog)
    (a := K.rev) (b := K.row) (self := .back) (next := .merge false)
    (d := some) (g := id) rfl (by decide) r.reverse r.reverse [] false
    (st x r.reverse [] u [] []) (by simp [st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v, S, by simpa using hr, ?_⟩
  funext k
  cases k with
  | rev => exact he
  | row => simpa [st] using hrow
  | _ => exact hf _ (by decide) (by decide)

private theorem restore_run (r w x : List Bool) (v : Bool) :
    ∃ v' S, Run prog (w.length + r.length + 2)
      ⟨some .restore, v, st x [] [] [] w.reverse r.reverse⟩
      ⟨some .good, v', S⟩ ∧ S = st x [] r w [] [] := by
  let S := st x [] [] [] w.reverse r.reverse
  obtain ⟨v₁, T, h₁, hn, hu, hf⟩ := moveB_run (M := prog)
    (a := K.next) (b := K.used) (self := .restore) (next := .copy)
    (d := some) (g := id) rfl (by decide) w.reverse w.reverse [] v S
    (by simp [S, st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  obtain ⟨v₂, U, h₂, hm, hr, hg⟩ := moveB_run (M := prog)
    (a := K.mask) (b := K.row) (self := .copy) (next := .good)
    (d := some) (g := id) rfl (by decide) r.reverse r.reverse [] v₁ T
    (by simpa [S, st] using hf .mask (by decide) (by decide))
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v₂, U, (h₁.trans h₂).of_eq (by simp; omega), ?_⟩
  funext k
  cases k with
  | row => simpa only [List.map_id, List.reverse_reverse,
      (hf K.row (by decide) (by decide)), S, st, List.append_nil] using hr
  | used => simpa [hg .used (by decide) (by decide), S, st] using hu
  | next => exact (hg .next (by decide) (by decide)).trans hn
  | mask => exact hm
  | input | rev => exact (hg _ (by decide) (by decide)).trans (hf _ (by decide) (by decide))

private theorem run (x u : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (6 * x.length + 6)
      ⟨some .read, v, st x [] [] u [] []⟩
      ⟨some (if (one x u).isSome then .good else .bad), v', S⟩ ∧
      ∀ r t w, one x u = some (r, t, w) → S = st t [] r w [] [] := by
  cases hd : undelimit x with
  | none =>
    obtain ⟨v', S, hr⟩ := Block.run_none (M := prog) (a := K.input) (b := K.rev)
      (d := some) (g := id) (self := .read) (good := .back) (bad := .bad)
      rfl (by decide) id (fun _ => rfl) x v (st x [] [] u [] []) (by simp [st]) hd
    exact ⟨v', S, by simpa [one, hd] using hr.mono (show x.length + 1 ≤ _ by omega),
      by simp [one, hd]⟩
  | some p =>
    obtain ⟨r, t⟩ := p
    have hX := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hd
    subst x
    obtain ⟨S, h₁, hx, hy, hf⟩ := Block.run_delimit (M := prog)
      (a := K.input) (b := K.rev) (d := some) (g := id)
      (self := .read) (good := .back) (bad := .bad)
      rfl (by decide) id (fun _ => rfl) r t v (st (delimit r ++ t) [] [] u [] [])
      (by simp [st])
    have hS : S = st t r.reverse [] u [] [] := by
      funext k
      cases k with
      | input => exact hx
      | rev => simpa [st] using hy
      | _ => exact hf _ (by decide) (by decide)
    obtain ⟨v₁, S₁, h₂, rfl⟩ := from_back r t u
    rw [hS] at h₁
    obtain ⟨v₂, S₂, h₃, hS₂⟩ := loop r u t [] [] false v₁
    have h123 := ((h₁.trans h₂).le le_rfl).trans h₃
    have hd' : one (delimit r ++ t) u =
        if r.any id then (merge r u).map (fun w => (r, t, w)) else none := by
      rw [one, undelimit_delimit]
      rfl
    by_cases hr : r.any id = true
    · rw [hd', ite_eq_left hr]
      cases hm : merge r u with
      | none =>
        simp only [hm, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
          reduceIte] at h123
        exact ⟨v₂, S₂, h123.mono (by simp only [List.length_append, length_delimit]; omega),
          by simp⟩
      | some w =>
        have he := hS₂ (by simpa only [Bool.false_or] using hr) w hm
        simp only [hm, hr, Option.isSome_some, Bool.false_or, Bool.and_true,
          reduceIte, List.append_nil] at h123 he
        rw [he] at h123
        obtain ⟨v₃, U, h₄, hu⟩ := restore_run r w t v₂
        have ⟨hru, hwu, _⟩ := merge_eq_some_iff.mp hm
        refine ⟨v₃, U, (h123.trans (h₄.le le_rfl)).mono ?_, ?_⟩
        · simp only [List.length_append, length_delimit]
          omega
        · intro r' t' w' hh
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl, rfl⟩ := hh
          exact hu
    · rw [hd', ite_eq_right hr]
      have he : r.any id = false := Bool.eq_false_iff.mpr hr
      simp only [he, Bool.false_or, Bool.and_false, Bool.false_eq_true, reduceIte] at h123
      exact ⟨v₂, S₂, h123.mono (by simp only [List.length_append, length_delimit]; omega),
        by simp⟩

end Row

-- Check each mask against the shared target, and tally the accepted parts in unary.
namespace Core

open Turing Function TM2Program TM2Embedding Cslib.Complexity.SatVerifier
open Cslib.Complexity.PolynomialEncoding

private inductive K | saved | scratch | row (k : Row.K) | ss (k : SSVerify.K) | count (k : EmitSS.K)
  deriving DecidableEq

private inductive Lab
  | loop | row (l : Row.Lab) | copy1 | copy2 | mask1 | mask2 | ss (l : SSVerify.Lab)
  | clear | bump | finish | bad
  deriving DecidableEq

@[reducible] private def Γ : K → Type
  | .ss _ => Sym
  | .count k => EmitSS.Γ k
  | _ => Bool

private def rowEmb : SEmb (fun _ : Row.K => Bool) Γ where
  e := K.row
  inj _ _ h := K.row.inj h
  ι _ := Equiv.refl _

private def ssEmb : SEmb (fun _ : SSVerify.K => Sym) Γ where
  e := K.ss
  inj _ _ h := K.ss.inj h
  ι _ := Equiv.refl _

private def rowLabel : Row.Lab → Lab
  | .good => .copy1
  | .bad => .bad
  | l => .row l

private def ssLabel : SSVerify.Lab → Lab
  | .yes => .clear
  | .no => .bad
  | l => .ss l

private def ssKeys : List K := ssVerifyComp.ks.map .ss

private def prog : Lab → TM2.Stmt Γ Lab Bool
  | .loop => .peek (.row .input) (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .row .read) (.goto fun _ => .finish)
  | .row l => mapS rowEmb rowLabel (Row.prog l)
  | .copy1 => moveB .saved .scratch some id .copy1 .copy2
  | .copy2 => splitB .scratch .saved (.ss .X) some id Sym.bit .copy2 .mask1
  | .mask1 => moveB (.row .row) .scratch some id .mask1 .mask2
  | .mask2 => moveB .scratch (.ss .W) some Sym.bit .mask2 (.ss SSVerify.start)
  | .ss l => mapS ssEmb ssLabel (SSVerify.prog l)
  | .clear => cleanS ssKeys .clear .bump
  | .bump => incr (.count .A) EmitSS.U .loop
  | .finish | .bad => .halt

private theorem embeds_row : Embeds rowEmb rowLabel Row.prog prog := by
  intro l
  cases l with
  | good | bad => exact Or.inr rfl
  | _ => exact Or.inl rfl

private theorem embeds_ss : Embeds ssEmb ssLabel SSVerify.prog prog := by
  intro l
  cases l with
  | yes | no => exact Or.inr rfl
  | _ => exact Or.inl rfl

private def st (x y : List Bool) (R : Row.K → List Bool) (S : SSVerify.K → List Sym)
    (C : (k : EmitSS.K) → List (EmitSS.Γ k)) : (k : K) → List (Γ k)
  | .saved => x
  | .scratch => y
  | .row k => R k
  | .ss k => S k
  | .count k => C k

private def cntSt (n : ℕ) : (k : EmitSS.K) → List (EmitSS.Γ k)
  | .A => cnt EmitSS.U n
  | _ => []

private def ready (x y u : List Bool) (n : ℕ) : (k : K) → List (Γ k) :=
  st x [] (Row.st y [] [] u [] []) (fun _ => []) (cntSt n)

private def rowLengthBound (N : ℕ) : ℕ := 6 * N + 6

private theorem run_row (x y u : List Bool) (n : ℕ) (v : Bool) :
    ∃ v' T, RunLe prog (rowLengthBound y.length)
      ⟨some (.row .read), v, ready x y u n⟩
      ⟨some (if (Row.one y u).isSome then .copy1 else .bad), v', T⟩ ∧
      ∀ r t w, Row.one y u = some (r, t, w) →
        T = st x [] (Row.st t [] r w [] []) (fun _ => []) (cntSt n) := by
  obtain ⟨v', S, hr, hs⟩ := Row.run y u v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed rowLabel embeds_row hr
    (S' := ready x y u n) (by
      intro k
      change _ = (Row.st y [] [] u [] [] k).map id
      rw [List.map_id]
      rfl)
  have hl : rowLabel (if (Row.one y u).isSome then .good else .bad) =
      (if (Row.one y u).isSome then .copy1 else .bad) := by
    split <;> rfl
  rw [hl] at ht
  refine ⟨v', T, ht, ?_⟩
  intro r t w h
  rw [hs r t w h] at ha
  funext k
  cases k with
  | row k =>
    have hk := ha k
    change T (.row k) = (Row.st t [] r w [] [] k).map id at hk
    simpa only [List.map_id, st] using hk
  | _ => exact hf _ (by simp [rowEmb])

private theorem copy_run (x r t w : List Bool) (n : ℕ) (v : Bool) :
    ∃ v' T, Run prog (2 * x.length + 2 * r.length + 4)
      ⟨some .copy1, v, st x [] (Row.st t [] r w [] []) (fun _ => []) (cntSt n)⟩
      ⟨some (.ss SSVerify.start), v', T⟩ ∧
      T = st x [] (Row.st t [] [] w [] [])
        (SSVerify.st (x.map Sym.bit) (r.map Sym.bit) [] [] []) (cntSt n) := by
  let S := st x [] (Row.st t [] r w [] []) (fun _ => []) (cntSt n)
  obtain ⟨U, h₁, hx, hz, hX, hf⟩ := copyB_run (M := prog)
    (a := K.saved) (b := .ss .X) (t := .scratch) (first := .copy1) (second := .copy2)
    (next := .mask1) (da := some) (dt := some) (ga := id) (gb := Sym.bit) (gt := id)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    x [] v S (by simp [S, st]) (by simp [EndsBitBlock]) (by simp [EndsBitBlock, S, st])
  obtain ⟨v', V, h₂, hr, hs, hW, hg⟩ := Cslib.Complexity.Host.move2_run
    (M := prog) (a := K.row .row) (t := K.scratch) (b := K.ss .W)
    (d := some) (gt := id) (dt := some) (g := Sym.bit)
    (l₁ := .mask1) (l₂ := .mask2) (l₃ := .ss SSVerify.start) rfl rfl
    (by decide) (by decide) (by decide) (fun _ => rfl)
    r r [] false U (by simpa [S, st, Row.st] using (hf (.row .row)
      (by decide) (by decide) (by decide))) (by simp [IsBitBlock])
    (by simp [EndsBitBlock]) (by simpa [S, st] using hz)
  refine ⟨v', V, (h₁.trans h₂).of_eq (by omega), ?_⟩
  funext k
  have hkeep (k : K) (ha : k ≠ .row .row) (hb : k ≠ .scratch) (hc : k ≠ .ss .W)
      (hd : k ≠ .saved) (he : k ≠ .ss .X) : V k = S k := by
    rw [hg k ha hb hc, hf k hd he hb]
  cases k with
  | saved => exact (hg _ (by decide) (by decide) (by decide)).trans hx
  | scratch => simpa [S, st] using hs
  | row k =>
    cases k with
    | row => exact hr
    | _ => exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  | ss k =>
    cases k with
    | X => simpa [hg (.ss .X) (by decide) (by decide) (by decide), S, st] using hX
    | W =>
      have h₀ := hf (.ss .W) (by decide) (by decide) (by decide)
      simpa [h₀, S, st] using hW
    | _ => exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  | count k => exact hkeep _ (by simp) (by simp) (by simp) (by simp) (by simp)

private def ssTM : FinTM2 where
  K := SSVerify.K
  k₀ := .X
  k₁ := .W
  Γ := fun _ => Sym
  Λ := SSVerify.Lab
  main := SSVerify.start
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstance
  m := SSVerify.prog

private noncomputable def pushBound := MetaMathlibExt.TM2Composition.pushBound ssTM

private noncomputable def ssBudget (N : ℕ) : ℕ :=
  128 * (N + 1) ^ 3 + (N + pushBound * (128 * (N + 1) ^ 3) + 1)

private theorem run_ss (x r t w : List Bool) (n : ℕ) (v : Bool) (N : ℕ)
    (hx : x.length ≤ N) (hr : r.length ≤ N) :
    ∃ v' T, RunLe prog (ssBudget N)
      ⟨some (.ss SSVerify.start), v, st x [] (Row.st t [] [] w [] [])
        (SSVerify.st (x.map Sym.bit) (r.map Sym.bit) [] [] []) (cntSt n)⟩
      ⟨some (if SSVerify.ssCheck x r then .bump else .bad), v', T⟩ ∧
      (SSVerify.ssCheck x r = true → T = ready x t w n) := by
  let S := SSVerify.st (x.map Sym.bit) (r.map Sym.bit) [] [] []
  let I := st x [] (Row.st t [] [] w [] []) S (cntSt n)
  obtain ⟨v₁, U, run⟩ := SSVerify.run x r v S rfl rfl (by intro k hX hW; cases k <;> simp_all [S])
  have hcost : 16 * (x.length + r.length + 1) ^ 3 ≤ 128 * (N + 1) ^ 3 := by
    have h := Nat.pow_le_pow_left (show x.length + r.length + 1 ≤ 2 * (N + 1) by omega) 3
    rw [mul_pow] at h
    exact (Nat.mul_le_mul_left 16 h).trans (by omega)
  have lengths (k : SSVerify.K) : (U k).length ≤ N + pushBound * (128 * (N + 1) ^ 3) := by
    obtain ⟨steps, hle, hrun⟩ := run
    have hh := Cslib.Complexity.Host.stk_length_le ssTM (N := N) (by
      intro k
      change (S k).length ≤ N
      cases k <;> simp [S, hx, hr]) hrun
    exact (hh k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hle.trans hcost)) _)
  obtain ⟨V, hrV, ha, hf⟩ := runLe_embed ssLabel embeds_ss run
    (S' := I) (by
      intro k
      change S k = (S k).map id
      rw [List.map_id])
  cases h : SSVerify.ssCheck x r with
  | false =>
    refine ⟨v₁, V, ?_, by simp⟩
    simp only [h, Bool.false_eq_true, reduceIte, ssLabel] at hrV ⊢
    exact hrV.mono (hcost.trans (Nat.le_add_right _ _))
  | true =>
    simp only [h, reduceIte, ssLabel] at hrV ⊢
    have hl : ∀ k ∈ ssKeys, (V k).length ≤ N + pushBound * (128 * (N + 1) ^ 3) := by
      intro k hk
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
      have hj : V (.ss j) = U j := by
        have hj := ha j
        change V (.ss j) = (U j).map id at hj
        simpa only [List.map_id] using hj
      rw [hj]
      exact lengths j
    let T : (k : K) → List (Γ k) := fun k => if k ∈ ssKeys then [] else V k
    have hc : RunLe prog (N + pushBound * (128 * (N + 1) ^ 3) + 1)
        ⟨some .clear, v₁, V⟩ ⟨some .bump, false, T⟩ :=
      clean_run (M := prog) (ks := ssKeys) rfl
        (ssVerifyComp.ks_nodup.map (fun _ _ h => K.ss.inj h)) _ v₁ V hl
    refine ⟨false, T, (hrV.trans hc).mono ?_, fun _ => ?_⟩
    · exact Nat.add_le_add_right hcost _
    · funext k
      cases k with
      | ss j =>
        have hj : K.ss j ∈ ssKeys := List.mem_map.mpr ⟨j, ssVerifyComp.mem_ks _, rfl⟩
        simp [T, hj, ready, st]
      | _ =>
        simp only [T, ssKeys, List.mem_map]
        rw [ite_eq_right (by simp), hf _ (by simp [ssEmb])]
        rfl

private def scanMasks (x : List Bool) :
    List (List Bool) → List Bool → ℕ → Option (ℕ × List Bool)
  | [], u, n => some (n, u)
  | r :: rs, u, n => if r.any id && SSVerify.ssCheck x r then
      (merge r u).bind (fun w => scanMasks x rs w (n + 1)) else none

private def scan (x y u : List Bool) (n fuel : ℕ) : Option (ℕ × List Bool) :=
  (undelimitBlocksAux fuel y).bind (fun rs => scanMasks x rs u n)

private theorem scan_cons (x : List Bool) {b : Bool} {y : List Bool} (u : List Bool) (n f : ℕ) :
    scan x (b :: y) u n (f + 1) = ((Row.one (b :: y) u).bind fun (r, t, w) =>
      if SSVerify.ssCheck x r then scan x t w (n + 1) f else none) := by
  cases hd : undelimit (b :: y) with
  | none => simp [scan, undelimitBlocksAux, Row.one, hd]
  | some pair =>
    obtain ⟨r, t⟩ := pair
    simp only [scan, undelimitBlocksAux, Row.one, hd, Option.bind_some]
    cases hr : r.any id <;> cases hs : SSVerify.ssCheck x r <;>
      cases hm : merge r u <;> cases ht : undelimitBlocksAux f t <;>
      simp only [scanMasks, hr, hs, ht, hm, Option.map_none, Option.map_some, Option.bind_some,
        Option.bind_none, Bool.false_and, Bool.true_and, Bool.false_eq_true, reduceIte]

private theorem one_data {y u r t w : List Bool} (h : Row.one y u = some (r, t, w)) :
    y = delimit r ++ t := by
  unfold Row.one at h
  obtain ⟨⟨a, b⟩, ht, hb⟩ := Option.bind_eq_some_iff.mp h
  change (if a.any id then (merge a u).map fun c => (a, b, c) else none) = _ at hb
  split at hb
  · obtain ⟨c, _, he⟩ := Option.map_eq_some_iff.mp hb
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp ht
  · contradiction

private noncomputable def cost (N : ℕ) : ℕ := ssBudget N + (10 * N + 20)

private theorem scan_run (x : List Bool) (N : ℕ) (hx : x.length ≤ N) (fuel : ℕ) :
    ∀ (y u : List Bool) (n : ℕ) (v : Bool), y.length ≤ fuel → y.length ≤ N →
      ∃ v' T, RunLe prog (fuel * cost N + 1)
        ⟨some .loop, v, ready x y u n⟩
        ⟨some (if (scan x y u n fuel).isSome then .finish else .bad), v', T⟩ ∧
    ∀ m a, scan x y u n fuel = some (m, a) → T = ready x [] a m := by
  have empty (f : ℕ) (u : List Bool) (n : ℕ) (v : Bool) :
      Run prog 1 ⟨some .loop, v, ready x [] u n⟩
        ⟨some (if (scan x [] u n f).isSome then .finish else .bad), false, ready x [] u n⟩ ∧
      scan x [] u n f = some (n, u) := by
    have he : scan x [] u n f = some (n, u) := by cases f <;> rfl
    exact ⟨Run.single (by simp [prog, ready, st, Row.st, TM2.stepAux, he]), he⟩
  induction fuel with
  | zero =>
    intro y u n v hf _
    obtain rfl : y = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain ⟨h, h'⟩ := empty 0 u n v
    exact ⟨false, ready x [] u n, h.le (by simp), by simp [h']⟩
  | succ f ih =>
    intro y u n v hf hy
    cases y with
    | nil =>
      obtain ⟨h, h'⟩ := empty (f + 1) u n v
      exact ⟨false, ready x [] u n, h.le (by omega), by simp [h']⟩
    | cons b ys =>
      let y := b :: ys
      change y.length ≤ f + 1 at hf
      change y.length ≤ N at hy
      have he := scan_cons x (b := b) (y := ys) u n f
      change scan x y u n (f + 1) = _ at he
      have start : Run prog 1 ⟨some .loop, v, ready x y u n⟩
          ⟨some (.row .read), true, ready x y u n⟩ :=
        Run.single (by simp [prog, ready, st, Row.st, y, TM2.stepAux])
      obtain ⟨v₁, S₁, h₁, hs₁⟩ := run_row x y u n true
      have hstart := (start.le le_rfl).trans h₁
      change ∃ v' T, RunLe prog ((f + 1) * cost N + 1)
        ⟨some .loop, v, ready x y u n⟩
        ⟨some (if (scan x y u n (f + 1)).isSome then .finish else .bad), v', T⟩ ∧
        ∀ m a, scan x y u n (f + 1) = some (m, a) → T = ready x [] a m
      cases ho : Row.one y u with
      | none =>
        have hnone : scan x y u n (f + 1) = none := by rw [he, ho]; rfl
        simp only [ho, Option.isSome_none, Bool.false_eq_true, reduceIte] at hstart
        simp only [hnone, Option.isSome_none, Bool.false_eq_true, reduceIte]
        refine ⟨v₁, S₁, hstart.mono ?_, by simp⟩
        have hc : 1 + rowLengthBound y.length ≤ cost N := by
          unfold rowLengthBound cost
          omega
        rw [Nat.succ_mul f (cost N)]
        omega
      | some p =>
        obtain ⟨r, t, w⟩ := p
        have hsplit := congrArg List.length (one_data ho)
        simp only [List.length_append, length_delimit] at hsplit
        have hr : r.length ≤ N := by omega
        have ht : t.length ≤ f := by omega
        have htn : t.length ≤ N := by omega
        have hs := hs₁ r t w ho
        simp only [ho, Option.isSome_some, reduceIte, hs] at hstart
        obtain ⟨v₂, S₂, h₂, rfl⟩ := copy_run x r t w n v₁
        obtain ⟨v₃, S₃, h₃, hs₃⟩ := run_ss x r t w n v₂ N hx hr
        have run := (hstart.trans (h₂.le le_rfl)).trans h₃
        have hbase : 1 + rowLengthBound y.length + (2 * x.length + 2 * r.length + 4) +
            ssBudget N + 1 ≤ cost N := by
          unfold rowLengthBound cost
          omega
        have hres : scan x y u n (f + 1) =
            (if SSVerify.ssCheck x r then scan x t w (n + 1) f else none) := by
          rw [he, ho]
          rfl
        rw [hres]
        cases hs' : SSVerify.ssCheck x r with
        | false =>
          simp only [hs', Bool.false_eq_true, reduceIte, Option.isSome_none] at run ⊢
          refine ⟨v₃, S₃, run.mono ?_, by simp⟩
          rw [Nat.succ_mul f (cost N)]
          omega
        | true =>
          have hs₃' := hs₃ hs'
          simp only [hs', reduceIte, hs₃'] at run ⊢
          have bump : Run prog 1 ⟨some .bump, v₃, ready x t w n⟩
              ⟨some .loop, v₃, ready x t w (n + 1)⟩ := by
            apply Run.single
            simp only [prog, incr, TM2.stepAux, TM2.Cfg.mk.injEq, true_and]
            funext k
            rcases k with _ | _ | j | j | j <;> try rfl
            cases j <;> rfl
          obtain ⟨v₄, S₄, h₄, hS₄⟩ := ih t w (n + 1) v₃ ht htn
          refine ⟨v₄, S₄, ((run.trans (bump.le le_rfl)).trans h₄).mono ?_, hS₄⟩
          rw [Nat.succ_mul f (cost N)]
          omega

private theorem scanMasks_spec {x : List Bool} {rs : List (List Bool)} {u a : List Bool}
    {n m : ℕ} : scanMasks x rs u n = some (m, a) ↔ m = n + rs.length ∧
      mergeRows rs u = some a ∧ ∀ r ∈ rs, r.any id = true ∧ SSVerify.ssCheck x r = true := by
  induction rs generalizing u n with
  | nil =>
    simp only [scanMasks, mergeRows, Option.some.injEq, Prod.mk.injEq, List.length_nil,
      Nat.add_zero, List.not_mem_nil, false_implies, implies_true, and_true]
    rw [eq_comm (a := n)]
  | cons r rs ih =>
    simp only [scanMasks, mergeRows, List.length_cons, List.mem_cons]
    by_cases h : (r.any id && SSVerify.ssCheck x r) = true
    · rw [ite_eq_left h, Option.bind_eq_some_iff, Option.bind_eq_some_iff]
      simp only [ih]
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
      constructor
      · rintro ⟨w, hw, hlen, hr, ht⟩
        exact ⟨by omega, ⟨w, hw, hr⟩, fun q hq => hq.elim (fun e => e ▸ ⟨h₁, h₂⟩) (ht q)⟩
      · rintro ⟨hlen, ⟨w, hw, hr⟩, ht⟩
        exact ⟨w, hw, by omega, hr, fun q hq => ht q (.inr hq)⟩
    · rw [ite_eq_right h]
      simp only [reduceCtorEq, false_iff]
      rintro ⟨_, _, ht⟩
      exact h (Bool.and_eq_true_iff.mpr (ht r (.inl rfl)))

end Core

open Cslib.Complexity.PolynomialEncoding Computability

private theorem encode_list (as : List ℕ) :
    bitEncode as = as.flatMap (fun a => delimit (encodeNat a)) := by
  change ((as.map encodeNat).map delimit).flatten = _
  simp [List.map_map, List.flatMap_def, Function.comp_def]

private theorem ssCheck_k (as : List ℕ) (ts r : List Bool) :
    SSVerify.ssCheck (delimit ts ++ bitEncode as) r = true ↔
    encodeNat (decodeNat ts) = ts ∧ (SSVerify.pick as r).sum = decodeNat ts := by
  unfold SSVerify.ssCheck SSVerify.decodeSS Cslib.CookLevin.decodeNatPrefix
  simp only [undelimit_delimit]
  by_cases ht : encodeNat (decodeNat ts) = ts
  · have hn : SSVerify.numsAux (bitEncode as).length (bitEncode as) = some as :=
      (SSVerify.numsAux_eq_some _ _ _ le_rfl).mpr (encode_list as)
    simp [ht, hn]
  · simp [ht]

-- The certificate frames the list of masks and then appends the binary target sum.
private def check (x w : List Bool) : Bool :=
  match bitDecode (α := MultiwayPartitionInstance) x, undelimit w with
  | some (as, k), some (r, t) =>
    match Core.scan (delimit t ++ bitEncode as) r (List.replicate as.length false) 0 r.length with
    | some (n, u) => decide (0 < n ∧ n = k ∧ u = List.replicate as.length true)
    | none => false
  | _, _ => false

private theorem check_data (as : List ℕ) (k : ℕ) (r t : List Bool) :
    (match Core.scan (delimit t ++ bitEncode as) r (List.replicate as.length false) 0 r.length with
    | some (n, u) => decide (0 < n ∧ n = k ∧ u = List.replicate as.length true)
    | none => false) = true ↔
    ∃ rs, undelimitBlocks r = some rs ∧
      encodeNat (decodeNat t) = t ∧ valid as k rs (decodeNat t) := by
  cases hd : undelimitBlocks r with
  | none =>
    unfold Core.scan
    rw [← undelimitBlocks, hd]
    simp
  | some rs =>
    have he : Core.scan (delimit t ++ bitEncode as) r (List.replicate as.length false) 0 r.length =
        Core.scanMasks (delimit t ++ bitEncode as) rs (List.replicate as.length false) 0 := by
      unfold Core.scan
      rw [← undelimitBlocks, hd]
      rfl
    rw [he]
    have hex : (∃ r', some rs = some r' ∧ encodeNat (decodeNat t) = t ∧
        valid as k r' (decodeNat t)) ↔
          encodeNat (decodeNat t) = t ∧ valid as k rs (decodeNat t) := by
      constructor
      · rintro ⟨r', hr, hv⟩
        obtain rfl := Option.some.inj hr
        exact hv
      · exact fun h => ⟨rs, rfl, h⟩
    rw [hex]
    unfold valid covers
    generalize hs : Core.scanMasks (delimit t ++ bitEncode as) rs
      (List.replicate as.length false) 0 = o
    cases o with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨ht, hlen, hk, hcov, hr⟩
      have hm := Core.scanMasks_spec.mpr ⟨show k = 0 + rs.length by omega, hcov,
        fun a hm => ⟨(hr a hm).1, (ssCheck_k as t a).mpr ⟨ht, (hr a hm).2⟩⟩⟩
      rw [hs] at hm
      contradiction
    | some p =>
      obtain ⟨n, u⟩ := p
      obtain ⟨hn, hcov, hr⟩ := Core.scanMasks_spec.mp hs
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨hp, hnk, rfl⟩
        have hne : rs ≠ [] := by
          intro h
          simp [h] at hn
          omega
        obtain ⟨a, ha, rfl⟩ := List.exists_cons_of_ne_nil hne
        have ht := ((ssCheck_k as t a).mp (hr a (by simp)).2).1
        exact ⟨ht, by simp only [Nat.zero_add] at hn; omega, by omega, hcov, fun a ha =>
          ⟨(hr a ha).1, ((ssCheck_k as t a).mp (hr a ha).2).2⟩⟩
      · rintro ⟨_, hl, hk, hm, _⟩
        have h := hcov.symm.trans hm
        exact ⟨by omega, by omega, Option.some.inj h⟩

private theorem parts_length_le {as : List ℕ} {k : ℕ} (hf : MultiwayPartitionFeasible (as, k)) :
    k ≤ as.length := by
  obtain ⟨assign, _, _, hlt, hsurj, _⟩ := hf
  let f : Fin as.length → Fin k := fun j => ⟨assign.getD j.val 0, hlt j.val j.isLt⟩
  have h : Function.Surjective f := by
    intro p
    obtain ⟨j, hj, he⟩ := hsurj p.val p.isLt
    exact ⟨⟨j, hj⟩, Fin.ext he⟩
  simpa using Fintype.card_le_of_surjective f h

private theorem frames_length (rs : List (List Bool)) (m : ℕ)
    (h : ∀ r ∈ rs, r.length = m) : ((rs.map delimit).flatten).length = rs.length * (2 * m + 1) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, length_delimit,
      List.length_cons]
    rw [h r (by simp), ih (fun a ha => h a (by simp [ha])), Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem exists_certificate (x : List Bool) : multiwayPartitionDec x = true ↔
    ∃ w, w.length ≤ 4 * (x.length + 1) ^ 2 ∧ check x w = true := by
  cases hd : bitDecode (α := MultiwayPartitionInstance) x with
  | none => simp [multiwayPartitionDec, check, hd]
  | some pair =>
    obtain ⟨as, k⟩ := pair
    simp only [multiwayPartitionDec, hd, decide_eq_true_eq]
    constructor
    · intro h
      have hkn := parts_length_le h
      obtain ⟨rs, T, hv⟩ := (feasible_iff_valid as k).mp h
      let r := (rs.map delimit).flatten
      let w := delimit r ++ encodeNat T
      have hr : undelimitBlocks r = some rs := undelimitBlocks_flatten_delimit _
      refine ⟨w, ?_, ?_⟩
      · have hs := decoded_fst_list_length_le hd
        obtain ⟨p, tail, hx, hp, _⟩ := decoded_pair_parts hd
        have hb := decoded_list_nat_encode_length_le hp
        have hpl : p.length ≤ x.length := by rw [hx]; simp; omega
        have ht : (encodeNat T).length ≤ (bitEncode as).length := by
          obtain ⟨a, has, he⟩ : ∃ r ∈ rs, (SSVerify.pick as r).sum = T := by
            cases rs with
            | nil => simp [valid] at hv; omega
            | cons a rest => exact ⟨a, by simp, (hv.2.2.2 a (by simp)).2⟩
          have hs' := (SSVerify.pick_sublist as a).sum_le_sum (fun _ _ => Nat.zero_le _)
          rw [he] at hs'
          simpa [BinaryNatEncoding.length_encodeNat] using
            (Nat.size_le_size hs').trans (by
              simpa using Partition.sum_encoding_length_le as)
        have hrl := frames_length rs as.length (covers_iff.mp hv.2.2.1).1
        change r.length = _ at hrl
        rw [hv.1] at hrl
        have hrn := Nat.mul_le_mul hkn (show 2 * as.length + 1 ≤ 2 * x.length + 1 by omega)
        have hxn := Nat.mul_le_mul_right (2 * x.length + 1) hs
        simp only [w, List.length_append, length_delimit]
        nlinarith
      · simp only [check, hd, w, undelimit_delimit]
        exact (check_data _ _ _ _).mpr ⟨rs, hr, by simp, by simpa using hv⟩
    · rintro ⟨w, _, hw⟩
      cases h : undelimit w with
      | none => simp [check, hd, h] at hw
      | some p =>
        obtain ⟨r, t⟩ := p
        simp only [check, hd, h] at hw
        obtain ⟨rs, _, _, hv⟩ := (check_data as k r t).mp hw
        exact (feasible_iff_valid as k).mpr ⟨rs, decodeNat t, hv⟩

-- Decode the inputs, run the mask checker, and verify coverage and the binary part count.
namespace Verifier

open Turing Function TM2Program TM2Embedding
open Cslib.Complexity.FramedCNF

private inductive K
  | source | sourceBuf | witness | witnessBuf | buffer | cmpL | cmpR
  | items (k : ListNatMachine.K) | groups (k : NormalizeMachine.K)
  | tallyInput | tallyBuf | core (k : Core.K)
  deriving DecidableEq

private inductive Lab
  | source (l : PairSplit.Lab) | groups (l : NormalizeMachine.Lab)
  | items (l : ListNatMachine.Lab) | witness (l : PairSplit.Lab)
  | listRev | listSplit | tally (l : ListCount.Lab) | frame | prepend
  | core (l : Core.Lab) | startFinish | cover | count (l : UnaryNat.Lab) | compare | yes | no
  deriving DecidableEq

@[reducible] private def Γ : K → Type
  | .core k => Core.Γ k
  | _ => Bool

private def sourceKey : PairSplit.K → K
  | .input => .source
  | .left => .items .input
  | .scratch => .sourceBuf

private def witnessKey : PairSplit.K → K
  | .input => .witness
  | .left => .core (.row .input)
  | .scratch => .witnessBuf

private def tallyKey : ListCount.K → K
  | .input => .tallyInput
  | .scratch => .tallyBuf
  | .count => .core (.row .used)

private def sourceEmb : SEmb (fun _ : PairSplit.K => Bool) Γ where
  e := sourceKey
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases k <;> exact Equiv.refl Bool

private def witnessEmb : SEmb (fun _ : PairSplit.K => Bool) Γ where
  e := witnessKey
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases k <;> exact Equiv.refl Bool

private def tallyEmb : SEmb (fun _ : ListCount.K => Bool) Γ where
  e := tallyKey
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι k := match k with
    | .input | .scratch => Equiv.refl Bool
    | .count => Equiv.boolNot

private def itemsEmb : SEmb (fun _ : ListNatMachine.K => Bool) Γ :=
  ⟨K.items, fun _ _ h => K.items.inj h, fun _ => Equiv.refl Bool⟩

private def groupsKey : NormalizeMachine.K → K
  | .input => .source
  | k => .groups k

private def groupsEmb : SEmb (fun _ : NormalizeMachine.K => Bool) Γ where
  e := groupsKey
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι k := by cases k <;> exact Equiv.refl Bool

private def coreEmb : SEmb Core.Γ Γ :=
  ⟨K.core, fun _ _ h => K.core.inj h, fun _ => Equiv.refl _⟩

private def countEmb : SEmb EmitSS.Γ Γ :=
  ⟨fun k => K.core (.count k), fun _ _ h => Core.K.count.inj (K.core.inj h),
    fun _ => Equiv.refl _⟩

private def sourceLabel : PairSplit.Lab → Lab
  | .good => .groups (.read none)
  | .bad => .no
  | l => .source l

private def groupsLabel : NormalizeMachine.Lab → Lab
  | .done => .items .loop
  | l => .groups l

private def itemsLabel : ListNatMachine.Lab → Lab
  | .good => .witness .read
  | .bad => .no
  | l => .items l

private def witnessLabel : PairSplit.Lab → Lab
  | .good => .listRev
  | .bad => .no
  | l => .witness l

private def tallyLabel : ListCount.Lab → Lab
  | .good => .frame
  | .bad => .no
  | l => .tally l

private def coreLabel : Core.Lab → Lab
  | .finish => .startFinish
  | .bad => .no
  | l => .core l

private def countLabel : UnaryNat.Lab → Lab
  | .done => .compare
  | l => .count l

private def countStart : UnaryNat.Lab := .emit .hv

private def prog : Lab → TM2.Stmt Γ Lab Bool
  | .source l => mapS sourceEmb sourceLabel (PairSplit.prog l)
  | .groups l => mapS groupsEmb groupsLabel (NormalizeMachine.prog l)
  | .items l => mapS itemsEmb itemsLabel (ListNatMachine.prog l)
  | .witness l => mapS witnessEmb witnessLabel (PairSplit.prog l)
  | .listRev => moveB (.items .output) .buffer some id .listRev .listSplit
  | .listSplit => splitB .buffer .tallyInput (.core .saved) some id id .listSplit (.tally .loop)
  | .tally l => mapS tallyEmb tallyLabel (ListCount.prog l)
  | .frame => emitFrame .witness .buffer some id .frame .prepend
  | .prepend => moveB .buffer (.core .saved) some id .prepend (.core .loop)
  | .core l => mapS coreEmb coreLabel (Core.prog l)
  | .startFinish => .peek (.core (.count .A)) (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .cover) (.goto fun _ => .no)
  | .cover => .peek (.core (.row .used)) (fun _ o => o.isSome) <| .branch id
      (.pop (.core (.row .used)) (fun _ o => o.getD false) <| .branch id
        (.goto fun _ => .cover) (.goto fun _ => .no)) (.goto fun _ => .count countStart)
  | .count l => mapS countEmb countLabel (UnaryNat.prog false l)
  | .compare => cmpB (.core (.count .O)) (.groups .output) .cmpL .cmpR some some id id
      .compare .yes .no
  | .yes | .no => .halt

private theorem embeds_source : Embeds sourceEmb sourceLabel PairSplit.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_groups : Embeds groupsEmb groupsLabel NormalizeMachine.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_items : Embeds itemsEmb itemsLabel ListNatMachine.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_witness : Embeds witnessEmb witnessLabel PairSplit.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_tally : Embeds tallyEmb tallyLabel ListCount.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_core : Embeds coreEmb coreLabel Core.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_count : Embeds countEmb countLabel (UnaryNat.prog false) prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private def init (x w : List Bool) : (k : K) → List (Γ k)
  | .source => x
  | .witness => w
  | _ => []

private theorem decode_instance (x : List Bool) : bitDecode (α := MultiwayPartitionInstance) x =
    (undelimit x).bind fun (p, k) => (bitDecode (α := List ℕ) p).map (·, decodeNat k) := by
  cases h : undelimit x with
  | none => simp only [bitDecode, BitstringEncoding.toEncoding, h, Option.bind_none]
  | some pair =>
    obtain ⟨p, k⟩ := pair
    simp only [bitDecode, BitstringEncoding.toEncoding, h, Option.bind_some]
    cases (undelimitBlocks p).bind (List.mapM (bitDecode (α := ℕ))) <;> rfl

private theorem init_source (x w : List Bool) :
    Agree sourceEmb (PairSplit.st x [] []) (init x w) := by
  intro k
  cases k with
  | input => change x = x.map id; simp
  | _ => rfl

private theorem source_run (x w : List Bool) :
    ∃ v T, RunLe prog (17 * x.length + 7)
      ⟨some (.source .read), false, init x w⟩
      ⟨some (if (bitDecode (α := MultiwayPartitionInstance) x).isSome then
        .witness .read else .no), v, T⟩ ∧
      ∀ as k, bitDecode (α := MultiwayPartitionInstance) x = some (as, k) →
        T (.items .output) = bitEncode as ∧ T (.groups .output) = encodeNat k ∧
        T .witness = w ∧ T .witnessBuf = [] ∧ T .tallyInput = [] ∧ T .tallyBuf = [] ∧
        T .buffer = [] ∧ ∀ j, T (.core j) = [] := by
  obtain ⟨v₁, S₁, h₁, hf₁, ha₁⟩ := PairSplit.run_embedded sourceEmb sourceLabel embeds_source
    x false (init x w) (init_source x w)
  cases hd : undelimit x with
  | none =>
    have he : bitDecode (α := MultiwayPartitionInstance) x = none := by simp [decode_instance, hd]
    simp only [he, hd, Option.isSome_none, Bool.false_eq_true, reduceIte, sourceLabel] at h₁ ⊢
    exact ⟨v₁, S₁, h₁.mono (by omega), by simp⟩
  | some pr =>
    obtain ⟨p, k⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hd
    have hlen := congrArg List.length hx
    simp only [List.length_append, length_delimit] at hlen
    have he : bitDecode (α := MultiwayPartitionInstance) x =
        (bitDecode (α := List ℕ) p).map (·, decodeNat k) := by rw [decode_instance, hd]; rfl
    simp only [hd, Option.isSome_some, reduceIte, sourceLabel] at h₁
    have ha := ha₁ p k hd
    have hgroup : Agree groupsEmb (NormalizeMachine.st k [] []) S₁ := by
      intro j
      cases j with
      | input =>
        have hh := ha PairSplit.K.input
        change S₁ .source = k.map id at hh ⊢
        exact hh
      | buffer =>
        exact hf₁ (.groups .buffer) (by intro a; cases a <;> simp [sourceEmb, sourceKey])
      | output =>
        exact hf₁ (.groups .output) (by intro a; cases a <;> simp [sourceEmb, sourceKey])
    obtain ⟨v₂, h₂⟩ := normalizeNat_run_frame k [] v₁
    obtain ⟨U, hU, ha₂, hf₂⟩ := runLe_embed groupsLabel embeds_groups h₂ hgroup
    have h₁₂ := h₁.trans hU
    have hi : Agree itemsEmb (ListNatMachine.st p [] [] (NormalizeMachine.st [] [] [])) U := by
      intro j
      have hf : U (.items j) = S₁ (.items j) :=
        hf₂ _ (by intro a; cases a <;> simp [groupsEmb, groupsKey])
      rw [show U (itemsEmb.e j) = S₁ (.items j) from hf]
      cases j with
      | input => exact ha PairSplit.K.left
      | acc | output =>
        exact hf₁ _ (by intro a; cases a <;> simp [sourceEmb, sourceKey])
      | nat q =>
        cases q <;> exact hf₁ _ (by intro a; cases a <;> simp [sourceEmb, sourceKey])
    obtain ⟨v₃, V, h₃, hf₃, ha₃⟩ := ListNatMachine.run_embedded itemsEmb itemsLabel embeds_items
      p v₂ U hi
    have htot := (h₁₂.trans h₃).mono (show _ ≤ 17 * x.length + 7 by omega)
    rw [he]
    cases hp : bitDecode (α := List ℕ) p with
    | none =>
      simp only [hp, Option.isSome_none, Option.map_none, Bool.false_eq_true, reduceIte,
        itemsLabel] at htot ⊢
      exact ⟨v₃, V, htot, by simp⟩
    | some as =>
      simp only [hp, Option.isSome_some, Option.map_some, reduceIte, itemsLabel] at htot ⊢
      refine ⟨v₃, V, htot, ?_⟩
      intro a n hn
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
      have hitems := ha₃ as hp ListNatMachine.K.output
      change V (.items .output) = (bitEncode as).map id at hitems
      rw [List.map_id] at hitems
      have hgroups := ha₂ NormalizeMachine.K.output
      change U (.groups .output) = (normalizeNat k ++ []).map id at hgroups
      rw [List.append_nil, List.map_id, normalizeNat_eq_encode_decode] at hgroups
      have hg : V (.groups .output) = encodeNat (decodeNat k) :=
        (hf₃ _ (by simp [itemsEmb])).trans hgroups
      have hf (j : K) (hs : ∀ a, sourceKey a ≠ j) (hb : ∀ b, groupsKey b ≠ j)
          (hc : ∀ c, K.items c ≠ j) : V j = init x w j :=
        (hf₃ j hc).trans ((hf₂ j hb).trans (hf₁ j hs))
      refine ⟨hitems, hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try intro j)
      all_goals apply hf <;> intro a <;> cases a <;> simp [sourceKey, groupsKey]

private theorem prepare (as : List ℕ) (k : ℕ) (r t : List Bool) (v : Bool)
    (S : (j : K) → List (Γ j)) (hi : S (.items .output) = bitEncode as)
    (hk : S (.groups .output) = encodeNat k) (ht : S .witness = t)
    (htx : S .tallyInput = []) (htb : S .tallyBuf = []) (hb : S .buffer = [])
    (hr : S (.core (.row .input)) = r)
    (h0 : ∀ j, j ≠ Core.K.row .input → S (.core j) = []) :
    ∃ v' U, RunLe prog (6 * (bitEncode as).length + 3 * t.length + 7)
      ⟨some .listRev, v, S⟩ ⟨some (.core .loop), v', U⟩ ∧
      Agree coreEmb
        (Core.ready (delimit t ++ bitEncode as) r (List.replicate as.length false) 0) U ∧
      U (.groups .output) = encodeNat k := by
  let x := bitEncode as
  obtain ⟨v₁, S₁, h₁, _, hb₁, hf₁⟩ := moveB_run (M := prog)
    (a := K.items .output) (b := .buffer) (d := some) (g := id)
    (self := .listRev) (next := .listSplit) rfl (by decide) x x [] v S
    (by simpa [x] using hi) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  obtain ⟨S₂, h₂, hb₂, hcnt, hsave, hf₂⟩ := splitB_run (M := prog)
    (a := K.buffer) (b := .tallyInput) (c := .core .saved)
    (d := some) (gb := id) (gc := id) (self := .listSplit) (next := .tally .loop)
    rfl (by decide) (by decide) (by decide) id (fun _ => rfl)
    x.reverse [] v₁ S₁ (by simp [EndsBitBlock]) (by simpa [hb] using hb₁)
  have keep (j : K) (h : j ≠ .tallyInput) (h' : j ≠ .core .saved)
      (h'' : j ≠ .items .output) (hh : j ≠ .buffer) : S₂ j = S j :=
    (hf₂ j hh h h').trans (hf₁ j h'' hh)
  have hcount : Agree tallyEmb (ListCount.st x [] []) S₂ := by
    intro j
    cases j with
    | input =>
      change S₂ .tallyInput = x.map id
      simpa [hf₁ .tallyInput (by decide) (by decide), htx] using hcnt
    | scratch =>
      exact (keep .tallyBuf (by decide) (by decide) (by decide) (by decide)).trans htb
    | count =>
      exact (keep (.core (.row .used)) (by decide) (by decide) (by decide) (by decide)).trans
        (h0 (.row .used) (by decide))
  obtain ⟨v₂, S₃, h₃, hf₃, ha₃⟩ := ListCount.run_embedded tallyEmb tallyLabel embeds_tally
    x false S₂ hcount
  have hd : bitDecode (α := List ℕ) x = some as := bitDecode_bitEncode as
  simp only [hd, Option.isSome_some, reduceIte, tallyLabel] at h₃
  have hu := ha₃ as hd ListCount.K.count
  change S₃ (.core (.row .used)) = (List.replicate as.length true).map (! ·) at hu
  simp only [List.map_replicate, Bool.not_true] at hu
  have keep₃ (j : K) (h : j ≠ .tallyInput) (h' : j ≠ .core .saved)
      (h'' : j ≠ .items .output) (hh : j ≠ .buffer) (ha : j ≠ .tallyBuf)
      (hc : j ≠ .core (.row .used)) : S₃ j = S j := by
    have hframe : ∀ a, tallyEmb.e a ≠ j := by
      intro a
      cases a
      · exact h.symm
      · exact ha.symm
      · exact hc.symm
    rw [hf₃ j hframe, keep j h h' h'' hh]
  obtain ⟨S₄, h₄, _, hb₄, hf₄⟩ := emitFrame_run (M := prog)
    (a := K.witness) (b := .buffer) (d := some) (g := id) (self := .frame) (next := .prepend)
    rfl (by decide) id (fun _ => rfl) t [] v₂ S₃ (by simp [EndsBitBlock])
    (by simpa using (keep₃ .witness (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ht)
  have he : S₄ .buffer = (delimit t).reverse := by
    simpa [hf₃ .buffer (by intro a; cases a <;> simp [tallyEmb, tallyKey]), hb₂] using hb₄
  obtain ⟨v₅, S₅, h₅, _, hsave₅, hf₅⟩ := moveB_run (M := prog)
    (a := K.buffer) (b := .core .saved) (d := some) (g := id)
    (self := .prepend) (next := .core .loop) rfl (by decide)
    (delimit t).reverse (delimit t).reverse [] false S₄ (by simpa using he)
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hss : S₅ (.core .saved) = delimit t ++ x := by
    have h₀ : S₁ (.core .saved) = [] :=
      (hf₁ _ (by decide) (by decide)).trans (h0 .saved (by decide))
    have h₁ : S₄ (.core .saved) = x := by
      rw [hf₄ _ (by decide) (by decide),
        hf₃ _ (by intro a; cases a <;> simp [tallyEmb, tallyKey])]
      simpa [h₀] using hsave
    simpa [h₁] using hsave₅
  have keep₅ (j : K) (h : j ≠ .buffer) (h' : j ≠ .core .saved) (hw : j ≠ .witness) :
      S₅ j = S₃ j := (hf₅ j h h').trans (hf₄ j hw h)
  have ready : Agree coreEmb
      (Core.ready (delimit t ++ bitEncode as) r (List.replicate as.length false) 0) S₅ := by
    intro j
    change S₅ (.core j) = (Core.ready _ _ _ _ j).map id
    rw [List.map_id]
    cases j with
    | saved => exact hss
    | row a =>
      cases a with
      | used => exact (keep₅ _ (by decide) (by decide) (by decide)).trans hu
      | input =>
        rw [keep₅ _ (by decide) (by decide) (by decide),
          keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hr
      | _ =>
        rw [keep₅ _ (by decide) (by decide) (by decide),
          keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact h0 _ (by decide)
    | scratch | ss _ | count _ =>
      rw [keep₅ _ (by simp) (by simp) (by simp),
        keep₃ _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), h0 _ (by simp)]
      first | rfl | (rename_i j; cases j <;> rfl)
  refine ⟨v₅, S₅, ?_, ready, ?_⟩
  · have h := (((h₁.trans h₂).le le_rfl).trans h₃).trans ((h₄.trans h₅).le le_rfl)
    exact h.mono (by simp only [List.length_reverse, length_delimit]; simp [x]; omega)
  · rw [keep₅ _ (by decide) (by decide) (by decide),
      keep₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hk

private theorem cover_run (u : List Bool) (v : Bool) (S : (j : K) → List (Γ j))
    (hu : S (.core (.row .used)) = u) :
    ∃ v' T, RunLe prog (u.length + 1) ⟨some .cover, v, S⟩
      ⟨some (if u.all id then .count countStart else .no), v', T⟩ ∧
      ∀ j, j ≠ .core (.row .used) → T j = S j := by
  induction u generalizing v S with
  | nil =>
    exact ⟨false, S, (Run.single (by simp [prog, TM2.stepAux, hu])).le (by simp), by simp⟩
  | cons b u ih =>
    let T := update S (.core (.row .used)) u
    have step : Run prog 1 ⟨some .cover, v, S⟩
        ⟨some (if b then .cover else .no), b, T⟩ := by
      apply Run.single
      cases b <;> simp [prog, TM2.stepAux, hu, T]
    cases b with
    | false =>
      exact ⟨false, T, step.le (by simp), fun j hj => update_of_ne hj _ _⟩
    | true =>
      obtain ⟨v', U, hr, hf⟩ := ih true T (by simp [T])
      refine ⟨v', U, ?_, fun j hj => (hf j hj).trans (update_of_ne hj _ _)⟩
      simpa only [List.all_cons, id_eq, Bool.true_and] using
        ((step.le le_rfl).trans hr).mono (by simp; omega)

private theorem finish_run (ssx u : List Bool) (n k N : ℕ) (v : Bool)
    (S : (j : K) → List (Γ j)) (hs : Agree coreEmb (Core.ready ssx [] u n) S)
    (hk : S (.groups .output) = encodeNat k)
    (hn : n ≤ N) (hu : u.length ≤ N) (hg : (encodeNat k).length ≤ N) :
    ∃ v' T, RunLe prog (712 * N + 312) ⟨some .startFinish, v, S⟩
      ⟨some (if 0 < n ∧ n = k ∧ u.all id = true then .yes else .no), v', T⟩ := by
  have hcounter (j : EmitSS.K) : S (.core (.count j)) = Core.cntSt n j := by
    have h := hs (.count j)
    change S (.core (.count j)) = (Core.cntSt n j).map id at h
    simpa only [List.map_id] using h
  have hused : S (.core (.row .used)) = u := by
    have h := hs (.row .used)
    change S (.core (.row .used)) = u.map id at h
    simpa only [List.map_id] using h
  cases n with
  | zero =>
    have h : S (.core (.count .A)) = [] := hcounter .A
    exact ⟨false, S, (Run.single (by simp [prog, TM2.stepAux, h])).le (by omega)⟩
  | succ n =>
    have h : S (.core (.count .A)) = EmitSS.U :: cnt EmitSS.U n := hcounter .A
    have first : Run prog 1 ⟨some .startFinish, v, S⟩ ⟨some .cover, true, S⟩ :=
      Run.single (by simp [prog, TM2.stepAux, h])
    obtain ⟨v₁, S₁, h₁, hf₁⟩ := cover_run u true S hused
    have hr := (first.le le_rfl).trans h₁
    cases he : u.all id with
    | false =>
      simp only [he, Bool.false_eq_true, reduceIte, and_false] at hr ⊢
      exact ⟨v₁, S₁, hr.mono (by omega)⟩
    | true =>
      let C := Core.cntSt (n + 1)
      have ha : Agree countEmb C S₁ := by
        intro j
        change S₁ (.core (.count j)) = (C j).map id
        rw [List.map_id, hf₁ _ (by simp)]
        exact hcounter j
      obtain ⟨v₂, C₂, h₂, hout, _, _, _, _, _⟩ := UnaryNat.run_raw (n + 1) [] v₁ C
        rfl rfl rfl rfl rfl
      obtain ⟨S₂, h₂', ha₂, hf₂⟩ := runLe_embed countLabel embeds_count h₂ ha
      have h₂o := ha₂ EmitSS.K.O
      change S₂ (.core (.count .O)) = (C₂ .O).map id at h₂o
      rw [List.map_id, hout, List.append_nil] at h₂o
      have hkg : S₂ (.groups .output) = encodeNat k :=
        (hf₂ _ (by simp [countEmb])).trans ((hf₁ _ (by decide)).trans hk)
      obtain ⟨p, v₃, S₃, _, hpre, _, hc, _, _, _, _, _⟩ := cmpB_run (M := prog)
        (a := K.core (.count .O)) (b := .groups .output) (ta := .cmpL) (tb := .cmpR)
        (da := some) (db := some) (ea := id) (eb := id) (self := .compare)
        (eqL := .yes) (neL := .no)
        rfl ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
        (encodeNat (n + 1)) (encodeNat k) (encodeNat (n + 1)) [] (encodeNat k) [] v₂ S₂
        (by simpa using h₂o) (by simpa using hkg)
        (by simp [IsBitBlock]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
        (by simp [EndsBitBlock])
      have hp := hpre.length_le
      simp only [he, reduceIte] at hr
      have ht := (hr.trans h₂').trans (hc.le le_rfl)
      refine ⟨v₃, S₃, ?_⟩
      simp only [and_true, Nat.succ_pos, true_and]
      simpa only [Cslib.Complexity.SatVerifier.encodeNat_inj] using ht.mono
        (show _ ≤ 712 * N + 312 by omega)

private noncomputable def budget (N : ℕ) : ℕ := N * Core.cost N + 752 * N + 344

private theorem run (x w : List Bool) :
    ∃ v T, RunLe prog (budget (4 * (x.length + w.length + 1)))
      ⟨some (.source .read), false, init x w⟩
      ⟨some (if check x w then .yes else .no), v, T⟩ := by
  let N := 4 * (x.length + w.length + 1)
  obtain ⟨v₁, S₁, h₁, ha₁⟩ := source_run x w
  cases hd : bitDecode (α := MultiwayPartitionInstance) x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, reduceIte] at h₁
    refine ⟨v₁, S₁, ?_⟩
    simp only [check, hd, Bool.false_eq_true, reduceIte]
    exact h₁.mono (by unfold budget; omega)
  | some a =>
    obtain ⟨as, k⟩ := a
    simp only [hd, Option.isSome_some, reduceIte] at h₁
    obtain ⟨ha, hk, hw, hwb, htx, htb, hb, hc⟩ := ha₁ as k hd
    have hW : Agree witnessEmb (PairSplit.st w [] []) S₁ := by
      intro j
      cases j with
      | input => change S₁ .witness = w.map id; simpa using hw
      | scratch => exact hwb
      | left => exact hc (.row .input)
    obtain ⟨v₂, S₂, h₂, hf₂, ha₂⟩ := PairSplit.run_embedded witnessEmb witnessLabel
      embeds_witness w v₁ S₁ hW
    have h12 := h₁.trans h₂
    cases hwd : undelimit w with
    | none =>
      simp only [hwd, Option.isSome_none, Bool.false_eq_true, reduceIte, witnessLabel] at h12
      refine ⟨v₂, S₂, ?_⟩
      simp only [check, hd, hwd, Bool.false_eq_true, reduceIte]
      exact h12.mono (by unfold budget; omega)
    | some p =>
      obtain ⟨r, ts⟩ := p
      simp only [hwd, Option.isSome_some, reduceIte, witnessLabel] at h12
      have keep (j : K) (h : j ≠ .core (.row .input)) (h' : j ≠ .witness) (hh : j ≠ .witnessBuf) :
          S₂ j = S₁ j := hf₂ j (by
        intro a
        cases a
        · exact h'.symm
        · exact h.symm
        · exact hh.symm)
      have ht := ha₂ r ts hwd PairSplit.K.input
      change S₂ .witness = ts.map id at ht
      rw [List.map_id] at ht
      have hr := ha₂ r ts hwd PairSplit.K.left
      change S₂ (.core (.row .input)) = r.map id at hr
      rw [List.map_id] at hr
      obtain ⟨v₃, S₃, h₃, ha₃, hk₃⟩ := prepare as k r ts v₂ S₂
        ((keep _ (by decide) (by decide) (by decide)).trans ha)
        ((keep _ (by decide) (by decide) (by decide)).trans hk) ht
        ((keep _ (by decide) (by decide) (by decide)).trans htx)
        ((keep _ (by decide) (by decide) (by decide)).trans htb)
        ((keep _ (by decide) (by decide) (by decide)).trans hb) hr
        (by intro j hj; rw [keep _ (by simpa using hj) (by simp) (by simp), hc])
      have hwlen := congrArg List.length ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hwd)
      simp only [List.length_append, length_delimit] at hwlen
      obtain ⟨px, rx, hxx, hpx, hrx⟩ := decoded_pair_parts hd
      have hxlen := congrArg List.length hxx
      simp only [List.length_append, length_delimit] at hxlen
      have hcanon := decoded_list_nat_encode_length_le hpx
      have hlen := decoded_list_length_le hpx
      have hklen : (encodeNat k).length ≤ N := by
        change some (decodeNat rx) = some k at hrx
        obtain rfl := Option.some.inj hrx
        rw [← normalizeNat_eq_encode_decode]
        have hh := length_normalizeNat_le rx
        unfold N
        omega
      let y := delimit ts ++ bitEncode as
      let u := List.replicate as.length false
      have hy : y.length ≤ N := by
        simp only [y, List.length_append, length_delimit]
        unfold N
        omega
      have hrN : r.length ≤ N := by unfold N; omega
      obtain ⟨v₄, C, h₄, hC⟩ := Core.scan_run y N hy r.length r u 0 v₃ le_rfl hrN
      obtain ⟨S₄, h₄', ha₄, hf₄⟩ := runLe_embed coreLabel embeds_core h₄ ha₃
      have hbase : 17 * x.length + 7 + (w.length + 1) +
          (6 * (bitEncode as).length + 3 * ts.length + 7) ≤ 39 * N + 15 := by
        unfold N
        omega
      have hscan := Nat.mul_le_mul_right (Core.cost N) hrN
      have all := (h12.trans h₃).trans h₄'
      have hkg : S₄ (.groups .output) = encodeNat k :=
        (hf₄ _ (by simp [coreEmb])).trans hk₃
      generalize he : Core.scan y r u 0 r.length = ans
      cases ans with
      | none =>
        simp only [he, Option.isSome_none, Bool.false_eq_true, reduceIte, coreLabel] at all
        refine ⟨v₄, S₄, ?_⟩
        simp only [check, hd, hwd]
        change RunLe prog _ _ ⟨some (if (match Core.scan y r u 0 r.length with
          | some (n, u') => decide (0 < n ∧ n = k ∧ u' = List.replicate as.length true)
          | none => false) then .yes else .no), v₄, S₄⟩
        rw [he]
        exact all.mono (show _ ≤ budget N by unfold budget; omega)
      | some p =>
        obtain ⟨n, us⟩ := p
        have hC' := hC n us he
        simp only [he, Option.isSome_some, reduceIte, coreLabel] at all
        rw [hC'] at ha₄
        have hh := he
        unfold Core.scan at hh
        obtain ⟨rs, hdecode, ht⟩ := Option.bind_eq_some_iff.mp hh
        obtain ⟨hcount, hmerge, _⟩ := Core.scanMasks_spec.mp ht
        have hpart := blocks_length_le hdecode
        have hn : n ≤ N := by omega
        have hlen' := (mergeRows_eq_some_iff.mp hmerge).1
        simp only [u, List.length_replicate] at hlen'
        have hu : us.length ≤ N := by unfold N; omega
        have hall : us.all id = true ↔ us = List.replicate as.length true := by
          rw [← hlen', List.eq_replicate_length, List.all_eq_true]
          rfl
        obtain ⟨v₅, S₅, h₅⟩ := finish_run y us n k N v₄ S₄ ha₄ hkg hn hu hklen
        refine ⟨v₅, S₅, ?_⟩
        simp only [check, hd, hwd]
        change RunLe prog _ _ ⟨some (if (match Core.scan y r u 0 r.length with
          | some (n, u') => decide (0 < n ∧ n = k ∧ u' = List.replicate as.length true)
          | none => false) then .yes else .no), v₅, S₅⟩
        rw [he]
        simpa only [hall, decide_eq_true_eq] using (all.trans h₅).mono (show _ ≤ budget N by
          unfold budget
          omega)

private noncomputable instance instFintypeCoreK : Fintype Core.K :=
  Fintype.ofList ([.saved, .scratch] ++ Finset.univ.toList.map Core.K.row ++
    Finset.univ.toList.map Core.K.ss ++ Finset.univ.toList.map Core.K.count) (by
      intro k; cases k <;> simp)

private noncomputable instance instFintypeCoreLab : Fintype Core.Lab :=
  Fintype.ofList ([.loop, .copy1, .copy2, .mask1, .mask2, .clear, .bump, .finish, .bad] ++
    Finset.univ.toList.map Core.Lab.row ++ Finset.univ.toList.map Core.Lab.ss) (by
      intro l; cases l <;> simp)

private noncomputable instance instFintypeK : Fintype K :=
  Fintype.ofList ([.source, .sourceBuf, .witness, .witnessBuf, .buffer,
    .cmpL, .cmpR, .tallyInput, .tallyBuf] ++
    Finset.univ.toList.map K.items ++ Finset.univ.toList.map K.groups ++
    Finset.univ.toList.map K.core) (by intro k; cases k <;> simp)

private noncomputable instance instFintypeLab : Fintype Lab :=
  Fintype.ofList
    ([.listRev, .listSplit, .frame, .prepend, .startFinish, .cover, .compare, .yes, .no] ++
    Finset.univ.toList.map Lab.source ++ Finset.univ.toList.map Lab.groups ++
    Finset.univ.toList.map Lab.items ++ Finset.univ.toList.map Lab.witness ++
    Finset.univ.toList.map Lab.tally ++ Finset.univ.toList.map Lab.core ++
    Finset.univ.toList.map Lab.count) (by intro l; cases l <;> simp)

private noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by
    cases k with
    | core k =>
      cases k with
      | count j => exact EmitSS.instFintypeΓ j
      | _ => infer_instance
    | _ => infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

private noncomputable def scale : Polynomial ℕ := Polynomial.C 4 * (Polynomial.X + 1)

private noncomputable def time : Polynomial ℕ :=
  let Q := Polynomial.C 128 * (scale + 1) ^ 3
  scale * (Q + (scale + Polynomial.C Core.pushBound * Q + 1) + (Polynomial.C 10 * scale + 20)) +
    Polynomial.C 752 * scale + 344

private theorem isPolyTime_check : ComplexityTheory.IsPolyTime
    (fun p : List Bool × List Bool => check p.1 p.2) :=
  Cslib.Complexity.Host.isPolyTime_verifier (c := comp) (cX := .source) (cW := .witness)
    (gX := id) (gW := id) (start := .source .read) (yes := .yes) (no := .no) check time
    (by decide) (by decide) rfl rfl (fun x w => by
      have he : update (update (fun j : K => ([] : List (Γ j))) .source x) .witness w =
          init x w := by
        funext k
        cases k <;> rfl
      simpa [he, time, budget, Core.cost, Core.ssBudget, scale] using run x w)

end Verifier

private theorem multiway_mem_NP : multiwayPartitionDec ∈ ComplexityTheory.NP := by
  refine ⟨Polynomial.C 4 * (Polynomial.X + 1) ^ 2, _, Verifier.isPolyTime_check, ?_⟩
  intro x
  simpa using exists_certificate x

-- Reduce from PARTITION with two zero entries, one available for each part.
private theorem sum_pick_compl (as : List ℕ) (w : List Bool) (h : w.length = as.length) :
    (SSVerify.pick as w).sum + (SSVerify.pick as (w.map (! ·))).sum = as.sum := by
  induction as generalizing w with
  | nil => simp [SSVerify.pick]
  | cons a as ih =>
    cases w with
    | nil => simp at h
    | cons b w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have eq := ih w h
      cases b <;> simp [SSVerify.pick] <;> omega

private theorem complement_map (assign : List ℕ) (h : ∀ q ∈ assign, q < 2) :
    (assign.map fun q => decide (q = 1)) = (assign.map fun q => decide (q = 0)).map (! ·) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  have := h q hq
  by_cases hq' : q = 0
  · subst q
    rfl
  · have : q = 1 := by omega
    subst q
    rfl

private theorem feasible_pad (as : List ℕ) :
    MultiwayPartitionFeasible (0 :: 0 :: as, 2) ↔ Partition.PartitionFeasible as := by
  constructor
  · rintro ⟨assign, hlen, _, hrange, _, T, hT⟩
    change assign.length = (0 :: 0 :: as).length at hlen
    have hq (q : ℕ) (hq : q ∈ assign) : q < 2 := by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      simpa [List.getD, List.getElem?_eq_getElem hj] using hrange j (hlen ▸ hj)
    let w := assign.map (fun q => decide (q = 0))
    have hw : w.length = (0 :: 0 :: as).length := by simpa [w] using hlen
    have ht0 := (sum_pick_label (0 :: 0 :: as) assign 0 hlen).trans (hT 0 (by change 0 < 2; decide))
    have ht1 := (sum_pick_label (0 :: 0 :: as) assign 1 hlen).trans (hT 1 (by change 1 < 2; decide))
    rw [complement_map assign hq] at ht1
    have hs := sum_pick_compl (0 :: 0 :: as) w hw
    change (SSVerify.pick (0 :: 0 :: as) w).sum = T at ht0
    change (SSVerify.pick (0 :: 0 :: as) (w.map (! ·))).sum = T at ht1
    rw [ht0, ht1] at hs
    have htail : (SSVerify.pick (0 :: 0 :: as) w).sum = (SSVerify.pick as w.tail.tail).sum := by
      simp [SSVerify.sum_pick_cons]
    refine ⟨SSVerify.pick as w.tail.tail, SSVerify.pick_sublist _ _, ?_⟩
    simp only [List.sum_cons, zero_add] at hs
    omega
  · rintro ⟨s, hs, he⟩
    obtain ⟨w, hw, rfl⟩ := SSVerify.exists_pick hs
    let assign := 0 :: 1 :: (w.map fun b => if b then 0 else 1)
    have hlen : assign.length = (0 :: 0 :: as).length := by simp [assign, hw]
    have hq (q : ℕ) (hq : q ∈ assign) : q < 2 := by
      simp only [assign, List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | rfl | ⟨b, _, rfl⟩
      · decide
      · decide
      · cases b <;> decide
    refine ⟨assign, hlen, by change 0 < 2; decide, ?_, ?_, (SSVerify.pick as w).sum, ?_⟩
    · intro j hj
      have hja : j < assign.length := by rwa [hlen]
      apply hq
      rw [List.getD, List.getElem?_eq_getElem hja, Option.getD_some]
      exact List.getElem_mem _
    · intro p hp
      change p < 2 at hp
      interval_cases p
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
    · intro p hp
      change p < 2 at hp
      have a0 : assign.map (fun q => decide (q = 0)) = true :: false :: w := by
        simp only [assign, List.map_cons, List.map_map, decide_true, Nat.one_ne_zero,
          decide_false, List.cons.injEq, true_and]
        conv_rhs => rw [← List.map_id w]
        apply List.map_congr_left
        intro b _
        cases b <;> rfl
      have a1 := complement_map assign hq
      rw [a0] at a1
      have hsum := sum_pick_compl as w hw
      interval_cases p
      · rw [← sum_pick_label _ _ _ hlen, a0]
        simp [SSVerify.sum_pick_cons]
      · rw [← sum_pick_label _ _ _ hlen, a1]
        simp only [List.map_cons, Bool.not_true, Bool.not_false, SSVerify.sum_pick_cons,
          List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte, zero_add]
        omega

private def pad (x : List Bool) : List Bool := delimit (false :: false :: x) ++ bitEncode (2 : ℕ)

open Cslib.Complexity.PolynomialEncoding in
private theorem pad_correct (x : List Bool) :
    Partition.partitionDec x = multiwayPartitionDec (pad x) := by
  classical
  have ha (r : List Bool) :
      bitDecode (α := List ℕ) (false :: r) =
        (bitDecode (α := List ℕ) r).map (0 :: ·) := by
    change bitDecode (delimit [] ++ r) = _
    rw [decode_list_delimit]
    rfl
  have hb : bitDecode (α := MultiwayPartitionInstance) (pad x) =
      (bitDecode (α := List ℕ) x).map (fun as => (0 :: 0 :: as, 2)) := by
    rw [show pad x = delimit (false :: false :: x) ++ bitEncode (2 : ℕ) from rfl]
    have hn := bitDecode_bitEncode (2 : ℕ)
    have ha' := ha (false :: x)
    have ha₀ := ha x
    simp only [bitDecode, BitstringEncoding.toEncoding, undelimit_delimit] at hn ha' ha₀ ⊢
    rw [ha', ha₀, hn]
    cases (undelimitBlocks x).bind (List.mapM (bitDecode (α := ℕ))) <;> rfl
  simp only [Partition.partitionDec, multiwayPartitionDec, hb]
  cases bitDecode (α := List ℕ) x with
  | none => rfl
  | some as =>
    rw [Option.map_some, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    exact (feasible_pad as).symm

namespace PadMachine

open Turing Function TM2Program Cslib.Complexity.PolynomialEncoding

private inductive K | input | scratch | output
  deriving DecidableEq

private inductive Lab | start | frame | finish | done
  deriving DecidableEq

private instance instFintypeK : Fintype K where
  elems := {K.input, .scratch, .output}
  complete k := by cases k <;> decide

private instance instFintypeLab : Fintype Lab where
  elems := {Lab.start, .frame, .finish, .done}
  complete l := by cases l <;> decide

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => pushList .scratch [true, false, true, false] <|
      emitR .output (bitEncode (2 : ℕ)) .frame
  | .frame => emitFrame .input .scratch some id .frame .finish
  | .finish => moveB .scratch .output some id .finish .done
  | .done => .halt

private def st (x y z : List Bool) : K → List Bool
  | .input => x
  | .scratch => y
  | .output => z

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (4 * x.length + 8) ⟨some .start, false, st x [] []⟩
      ⟨some .done, v, S⟩ ∧ S .output = pad x := by
  let p : List Bool := [false, true, false, true]
  let t := bitEncode (2 : ℕ)
  have h₀ : Run prog 1 ⟨some .start, false, st x [] []⟩
      ⟨some .frame, false, st x p t⟩ := by
    apply Run.single
    simp only [prog, stepAux_pushList, emitR, emit, TM2.stepAux, TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k <;> rfl
  obtain ⟨S, h₁, _, hs, ho⟩ := emitFrame_run (M := prog)
    (a := K.input) (b := .scratch) (self := .frame) (next := .finish)
    (d := some) (g := id) rfl (by decide) id (fun _ => rfl) x [] false (st x p t)
    (by simp [EndsBitBlock]) (by simp [st])
  have he : S .scratch = (delimit (false :: false :: x)).reverse := by
    simpa [st, p, delimit, List.reverse_cons, List.append_assoc] using hs
  obtain ⟨v, T, h₂, _, ht, _⟩ := moveB_run (M := prog)
    (a := K.scratch) (b := .output) (self := .finish) (next := .done)
    (d := some) (g := id) rfl (by decide) (delimit (false :: false :: x)).reverse
    (delimit (false :: false :: x)).reverse [] false S
    (by simpa using he) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v, T, (h₀.trans (h₁.trans h₂)).le ?_, ?_⟩
  · simp only [List.length_reverse, length_delimit, List.length_cons]
    omega
  · simpa [pad, t, ho .output (by decide) (by decide), st] using ht

private noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .scratch, .output]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

private theorem isPolyTime_pad : ComplexityTheory.IsPolyTime pad :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .input) (cO := .output) (gX := id) (start := .start) (done := .done)
    (Equiv.refl Bool) pad (Polynomial.C 4 * Polynomial.X + Polynomial.C 8) rfl (fun x => by
      have he : update (fun _ : K => ([] : List Bool)) .input x = st x [] [] := by
        funext k
        cases k <;> rfl
      simpa [he] using run x)

end PadMachine

private theorem multiway_npHard : ∀ L : ComplexityTheory.DecisionProblem,
    L ∈ ComplexityTheory.NP → Cslib.CookLevin.PolyManyOneRed L multiwayPartitionDec :=
  Cslib.Complexity.NPHard.of_polyManyOneRed Partition.partition_npComplete.2
    ⟨pad, PadMachine.isPolyTime_pad, pad_correct⟩

/-- **MULTIWAY NUMBER PARTITION is NP-complete.** Let MULTIWAY NUMBER PARTITION be the decision
problem that accepts exactly the bitstrings decoding to a feasible multiway number partition
instance: a list of natural numbers and a number $K \ge 1$ such that the entries of the list,
counted with repetition, can be split into $K$ nonempty parts with equal sums. Then MULTIWAY
NUMBER PARTITION is in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

For $K = 2$ this is PARTITION restricted to splits into two nonempty parts: the one-entry list
$(0)$, for instance, is a yes-instance of PARTITION but has no split into two nonempty parts.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), PARTITION [SP12], from which NP-hardness follows by
reduction. -/
theorem multiwayPartition_npComplete :
    multiwayPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayPartitionDec :=
  ⟨multiway_mem_NP, multiway_npHard⟩

end MetaMathlibExt.Complexity.NPComplete.MultiwayPartition
