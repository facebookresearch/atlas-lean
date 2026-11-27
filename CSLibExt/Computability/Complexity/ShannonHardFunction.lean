/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import MathlibExt.Complexity.ShannonCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Shannon's circuit-size lower bound

`shannon_hard_function` shows that at least half of the Boolean functions on `n ≥ 10` inputs
require more than `2 ^ n / (10 * n)` wires in a mod-free flat circuit. Its `wireCount` counts
each occurrence of a predecessor. The proof counts sets of truth tables available after a
bounded number of binary Boolean operations, starting with all variables and both constants.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ShannonHardFunction

open Cslib.Complexity.Classes

/-- **Wire count of a flat circuit.** The wire count of a flat Boolean circuit on $n$ inputs,
given as a list of gates, is the sum over its gates of the lengths of their predecessor lists:
every reference of a gate to a gate index is counted, with multiplicity, while input variables
and constants contribute nothing and the modulus of a mod gate is not counted. -/
def wireCount {n : ℕ} (C : List (ACGate n)) : ℕ :=
  (C.map gateInputs).flatten.length

private abbrev TruthTable (n : ℕ) := (Fin n → Bool) → Bool

private def initial (n : ℕ) : Finset (TruthTable n) :=
  insert (fun _ => false) (insert (fun _ => true) (Finset.univ.image fun i x => x i))

/-- One step can keep the current tables, or adjoin a binary operation of two of them. -/
private def extensions {n : ℕ} (S : Finset (TruthTable n)) : Finset (Finset (TruthTable n)) :=
  insert S <| ((Finset.univ : Finset (Bool → Bool → Bool)) ×ˢ (S ×ˢ S)).image
    fun (op, a, b) => insert (fun x => op (a x) (b x)) S

private def reachable (n : ℕ) : ℕ → Finset (Finset (TruthTable n))
  | 0 => {initial n}
  | t + 1 => (reachable n t).biUnion extensions

private theorem reachable_mono (n : ℕ) : Monotone (reachable n) :=
  monotone_nat_of_le_succ fun _ S hS =>
    Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_insert_self ..⟩

private theorem advance {n t : ℕ} {S : Finset (TruthTable n)} (hS : S ∈ reachable n t)
    (op : Bool → Bool → Bool) {a b : TruthTable n} (ha : a ∈ S) (hb : b ∈ S) :
    insert (fun x => op (a x) (b x)) S ∈ reachable n (t + 1) := by
  refine Finset.mem_biUnion.mpr ⟨S, hS, ?_⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(op, a, b), by simp [ha, hb], rfl⟩

/-- An unbounded fan-in gate can accumulate its result using one step per predecessor. -/
private theorem simulate_fold {n t : ℕ} {S : Finset (TruthTable n)} (hS : S ∈ reachable n t)
    (op : Bool → Bool → Bool) (base : TruthTable n) (hb : base ∈ S)
    (read : ℕ → TruthTable n) (l : List ℕ) (hl : ∀ a ∈ l, read a ∈ S) :
    ∃ T ∈ reachable n (t + l.length), S ⊆ T ∧
      (fun x => l.foldr (fun a b => op (read a x) b) (base x)) ∈ T := by
  induction l with
  | nil => exact ⟨S, hS, Finset.Subset.rfl, hb⟩
  | cons a l ih =>
    obtain ⟨T, hT, hST, hfold⟩ := ih fun i hi => hl i (List.mem_cons_of_mem _ hi)
    have h := advance hT op (hST (hl a List.mem_cons_self)) hfold
    exact ⟨_, h, hST.trans (Finset.subset_insert ..), Finset.mem_insert_self ..⟩

private theorem simulate_gate {n t : ℕ} {S : Finset (TruthTable n)} (hS : S ∈ reachable n t)
    (hs : initial n ⊆ S) (vs : (Fin n → Bool) → List Bool) (g : ACGate n)
    (href : ∀ a ∈ gateInputs g, (fun x => (vs x).getD a false) ∈ S)
    (hmod : IsModFree [g]) :
    ∃ T ∈ reachable n (t + (gateInputs g).length), S ⊆ T ∧
      (fun x => gateValue (vs x) x g) ∈ T := by
  have hc (b : Bool) : (fun _ => b) ∈ S := hs (by cases b <;> simp [initial])
  cases g with
  | var i =>
    exact ⟨S, hS, Finset.Subset.rfl, hs (by simp [initial, gateValue])⟩
  | const b => exact ⟨S, hS, Finset.Subset.rfl, hc b⟩
  | notGate a =>
    have ha := href a (List.mem_singleton_self _)
    exact ⟨_, advance hS (fun b _ => !b) ha ha, Finset.subset_insert ..,
      Finset.mem_insert_self ..⟩
  | andGate l =>
    obtain ⟨T, hT, hST, hl⟩ := simulate_fold hS Bool.and _ (hc true) _ l href
    refine ⟨T, hT, hST, ?_⟩
    convert hl using 1
    funext x
    clear href hmod hl hT
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg ((vs x).getD a false && ·) ih
  | orGate l =>
    obtain ⟨T, hT, hST, hl⟩ := simulate_fold hS Bool.or _ (hc false) _ l href
    refine ⟨T, hT, hST, ?_⟩
    convert hl using 1
    funext x
    clear href hmod hl hT
    induction l with
    | nil => rfl
    | cons a l ih => exact congrArg ((vs x).getD a false || ·) ih
  | modGate m l => exact (hmod _ List.mem_cons_self).elim

/-- All gate values of a circuit occur together after one step per wire. -/
private theorem simulate {n : ℕ} (C : List (ACGate n)) (hw : WellFormedCircuit C)
    (hm : IsModFree C) :
    ∃ S ∈ reachable n (wireCount C), initial n ⊆ S ∧ ∀ i < C.length,
      (fun x => (circuitEval C x).getD i false) ∈ S := by
  induction C using List.reverseRecOn with
  | nil => exact ⟨_, Finset.mem_singleton_self _, Finset.Subset.rfl, by simp⟩
  | append_singleton C g ih =>
    have hw' : WellFormedCircuit C := by
      intro j hj a ha
      apply hw j (by simp; omega) a
      rwa [List.getElem_append_left hj]
    obtain ⟨S, hS, hs, hval⟩ := ih hw' fun a ha => hm a (List.mem_append_left _ ha)
    have hg : ∀ a ∈ gateInputs g, a < C.length := by
      simpa using hw C.length (by simp)
    obtain ⟨T, hT, hST, hgate⟩ := simulate_gate hS hs (circuitEval C) g
      (fun a ha => hval a (hg a ha)) (fun a ha => hm a (List.mem_append_right _ ha))
    have hcount : wireCount (C ++ [g]) = wireCount C + (gateInputs g).length := by
      simp [wireCount]
    refine ⟨T, hcount ▸ hT, hs.trans hST, fun i hi => ?_⟩
    by_cases hi' : i < C.length
    · convert hST (hval i hi') using 1
      funext x
      rw [circuitEval_append_singleton, List.getD_append _ _ _ _ (by simpa)]
    · have : i = C.length := by simp at hi; omega
      subst i
      convert hgate using 1
      funext x
      rw [circuitEval_append_singleton, List.getD_append_right _ _ _ _ (by simp)]
      simp

private theorem card_initial (n : ℕ) : (initial n).card ≤ n + 2 := by
  unfold initial
  apply (Finset.card_insert_le ..).trans
  apply Nat.succ_le_succ
  apply (Finset.card_insert_le ..).trans
  exact Nat.succ_le_succ (Finset.card_image_le.trans_eq (by simp))

private theorem card_of_mem_reachable {n t : ℕ} {S : Finset (TruthTable n)}
    (hS : S ∈ reachable n t) : S.card ≤ n + 2 + t := by
  induction t generalizing S with
  | zero =>
    obtain rfl := Finset.mem_singleton.mp hS
    exact card_initial n
  | succ t ih =>
    obtain ⟨T, hT, h⟩ := Finset.mem_biUnion.mp hS
    rcases Finset.mem_insert.mp h with rfl | h
    · exact (ih hT).trans (Nat.le_succ _)
    · obtain ⟨⟨op, a, b⟩, _, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.card_insert_le ..).trans (Nat.succ_le_succ (ih hT))

private theorem card_extensions {n : ℕ} (S : Finset (TruthTable n)) :
    (extensions S).card ≤ 16 * (S.card * S.card) + 1 := by
  refine (Finset.card_insert_le ..).trans (Nat.succ_le_succ (Finset.card_image_le.trans_eq ?_))
  simp [Finset.card_product]

/-- Bound the number of reachable sets and then count all their possible output tables. -/
private theorem card_outputs {n s M : ℕ} (hM : n + 2 + s ≤ M) :
    ((reachable n s).biUnion id).card ≤ (16 * (M * M) + 1) ^ s * M := by
  have hstates (t : ℕ) (ht : t ≤ s) : (reachable n t).card ≤ (16 * (M * M) + 1) ^ t := by
    induction t with
    | zero => simp [reachable]
    | succ t ih =>
      rw [reachable, pow_succ]
      apply (Finset.card_biUnion_le_card_mul _ _ _ ?_).trans
        (Nat.mul_le_mul_right _ (ih (by omega)))
      intro S hS
      have h := card_of_mem_reachable hS
      have h' : S.card ≤ M := by omega
      exact (card_extensions S).trans (by gcongr)
  exact (Finset.card_biUnion_le_card_mul _ _ M (fun S hS =>
    (card_of_mem_reachable hS).trans hM)).trans (Nat.mul_le_mul_right M (hstates s le_rfl))

private theorem card_outputs_bound {n : ℕ} (hn : 10 ≤ n) :
    ((reachable n (2 ^ n / (10 * n))).biUnion id).card * 2 ≤ 2 ^ (2 ^ n) := by
  let s := 2 ^ n / (10 * n)
  let M := 2 ^ (n + 1)
  have hn' : 2 * (n + 2) ≤ 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  have hbudget : 10 * (n * s) ≤ 2 ^ n := by
    simpa [s, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using
      Nat.div_mul_le_self (2 ^ n) (10 * n)
  have hM : n + 2 + s ≤ M := by
    dsimp [M]
    rw [pow_succ]
    have := Nat.div_le_self (2 ^ n) (10 * n)
    dsimp [s]
    omega
  have hbase : 16 * (M * M) + 1 ≤ 2 ^ (3 * n) := calc
    16 * (M * M) + 1 ≤ 2 ^ 5 * (M * M) := by
      have : 0 < M * M := by dsimp [M]; positivity
      omega
    _ = 2 ^ (5 + ((n + 1) + (n + 1))) := by simp [M, pow_add]
    _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ ((16 * (M * M) + 1) ^ s * M) * 2 := Nat.mul_le_mul_right 2 (card_outputs hM)
    _ ≤ ((2 ^ (3 * n)) ^ s * M) * 2 := by gcongr
    _ = 2 ^ ((3 * n) * s + (n + 1) + 1) := by rw [← pow_mul, pow_succ, pow_add]
    _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_assoc]; omega)

/-- **Shannon: most Boolean functions need exponential circuits.** For every natural number
$n \ge 10$, at least $2^{2^n}/2$ of the Boolean functions $f$ on $n$ input bits have the
following property: for every well-formed flat Boolean circuit $C$ on $n$ inputs without mod
gates whose wire count (the total length of the predecessor lists of its gates) is at most
$\lfloor 2^n / (10 n) \rfloor$, there is an input $x \in \{0,1\}^n$ such that $C$ has no
gates or the value of the last gate of $C$ on $x$ differs from $f(x)$.

Source: C. E. Shannon, "The
synthesis of two-terminal switching circuits", Bell System Technical Journal 28 (1949),
59-98. -/
theorem shannon_hard_function :
    ∀ n : ℕ, 10 ≤ n →
      (Set.ncard {f : (Fin n → Bool) → Bool | ∀ C : List (ACGate n),
        WellFormedCircuit C → IsModFree C → wireCount C ≤ 2 ^ n / (10 * n) →
          ∃ x : Fin n → Bool, (circuitEval C x).getLast? ≠ some (f x)} ≥
        2 ^ (2 ^ n) / 2) := by
  intro n hn
  let s := 2 ^ n / (10 * n)
  let outputs := (reachable n s).biUnion id
  have hhard : (↑outputsᶜ : Set (TruthTable n)) ⊆
      {f | ∀ C : List (ACGate n), WellFormedCircuit C → IsModFree C → wireCount C ≤ s →
        ∃ x, (circuitEval C x).getLast? ≠ some (f x)} := by
    intro f hf C hw hm hsize
    by_contra! heval
    obtain ⟨S, hS, _, hval⟩ := simulate C hw hm
    have hlen : 0 < C.length := by
      by_contra! h
      obtain rfl : C = [] := List.length_eq_zero_iff.mp (by omega)
      simpa [circuitEval] using heval (fun _ => false)
    have heq : (fun x => (circuitEval C x).getD (C.length - 1) false) = f := by
      funext x
      have hx := heval x
      rw [List.getLast?_eq_getElem?, length_circuitEval] at hx
      simp [List.getD_eq_getElem?_getD, hx]
    have hfS := hval (C.length - 1) (by omega)
    rw [heq] at hfS
    exact Finset.mem_compl.mp hf (Finset.mem_biUnion.mpr ⟨S, reachable_mono n hsize hS, hfS⟩)
  apply le_trans _ (Set.ncard_le_ncard hhard)
  rw [Set.ncard_coe_finset, Finset.card_compl,
    MathlibExt.Complexity.ShannonCounting.card_bool_functions]
  have h : outputs.card * 2 ≤ 2 ^ (2 ^ n) := card_outputs_bound hn
  omega

end MetaMathlibExt.Complexity.KeyTheorems.ShannonHardFunction
