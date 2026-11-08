/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.DPLL.Solver
public import CSLibExt.Computability.Complexity.Karp.ThreeSat

/-!
# Correctness of the SAT-to-3SAT translation

Component 1 of the SAT ≤ 3SAT reduction specified in
`CSLibExt.Computability.Complexity.Karp.ThreeSat`:

* `is3_to3`: every clause of `to3 φ` has at most three literals;
* `cnfSat_to3_iff`: `to3 φ` is satisfiable exactly when `φ` is;
* `satDec_eq_sat3Dec_reduce3`: `reduce3` maps SAT instances to 3SAT instances and
  non-instances to non-instances.

Soundness reads an assignment for `φ` off the even variables (`ren`). Completeness extends an
assignment `v` for `φ` (`lift`): even variable `2 n` gets `v n`, and the fresh variable that the
chain of a clause `C` asserts after its `i`-th literal gets "`v` satisfies one of the literals of
`C` after the `i`-th" (`freshVal`). Different clauses use disjoint ranges of fresh numbers, which
`freshVal` locates by walking `to3Aux`.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL Cslib.Algorithms.SAT.DPLL

/-! ### Clause lengths -/

/-- Every clause of `chainTail` has at most three literals. -/
theorem length_le_three_of_mem_chainTail :
    ∀ {ls : CNFClause} {z : ℕ}, ∀ D ∈ chainTail ls z, D.length ≤ 3
  | [], _, D, h => by simp [chainTail] at h
  | [_], _, D, h => by
    simp only [chainTail, List.mem_singleton] at h
    simp [h]
  | _ :: _ :: _, _, D, h => by
    simp only [chainTail, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact length_le_three_of_mem_chainTail D h

/-- Every clause of `chain` has at most three literals. -/
theorem length_le_three_of_mem_chain {C : CNFClause} {u : ℕ} :
    ∀ D ∈ chain C u, D.length ≤ 3 := by
  intro D h
  match C, h with
  | [], h => simp_all [chain]
  | [_], h => simp_all [chain]
  | _ :: _ :: _, h =>
    simp only [chain, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact length_le_three_of_mem_chainTail D h

/-- Every clause of `to3Aux` has at most three literals. -/
theorem length_le_three_of_mem_to3Aux : ∀ {φ : CNF}, ∀ D ∈ (to3Aux φ).2, D.length ≤ 3
  | [], D, h => by simp [to3Aux] at h
  | _ :: _, D, h => by
    simp only [to3Aux, List.mem_append] at h
    rcases h with h | h
    · exact length_le_three_of_mem_chain D h
    · exact length_le_three_of_mem_to3Aux D h

/-- Every clause of the translation has at most three literals. -/
theorem is3_to3 (φ : CNF) : is3 (to3 φ) = true := by
  simpa [is3, to3] using length_le_three_of_mem_to3Aux (φ := φ)

/-! ### Soundness: an assignment for `to3 φ` gives one for `φ` -/

/-- If an assignment satisfies `chainTail (l :: ls) z` and makes fresh variable `z` true, its
restriction to even variables satisfies `l :: ls`. -/
theorem chainTail_sound {v' : ℕ → Bool} {ls : CNFClause} :
    ∀ {l : ℕ × Bool} {z : ℕ}, CNF.Satisfies v' (chainTail (l :: ls) z) →
      v' (fresh z) = true → CNFClause.Satisfies (fun n => v' (ren n)) (l :: ls) := by
  induction ls with
  | nil =>
    intro l z h hz
    rcases CNFClause.satisfies_cons.1 (CNF.satisfies_cons.1 h).1 with h1 | h1
    · simp [hz] at h1
    · rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
      · exact CNFClause.satisfies_cons.2 (Or.inl h1)
      · simp at h1
  | cons l' ls ih =>
    intro l z h hz
    simp only [chainTail, CNF.satisfies_cons] at h
    obtain ⟨h1, h2⟩ := h
    rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
    · simp [hz] at h1
    rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
    · exact CNFClause.satisfies_cons.2 (Or.inl h1)
    rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
    · exact CNFClause.satisfies_cons.2 (Or.inr (ih h2 h1))
    · simp at h1

/-- An assignment satisfying `chain C u` satisfies `C` on the even variables. -/
theorem chain_sound {v' : ℕ → Bool} {C : CNFClause} {u : ℕ}
    (h : CNF.Satisfies v' (chain C u)) : CNFClause.Satisfies (fun n => v' (ren n)) C := by
  match C, h with
  | [], h => simp [chain] at h
  | [l], h => simpa [chain, renLit] using h
  | l :: l' :: ls, h =>
    simp only [chain, CNF.satisfies_cons] at h
    obtain ⟨h1, h2⟩ := h
    rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
    · exact CNFClause.satisfies_cons.2 (Or.inl h1)
    rcases CNFClause.satisfies_cons.1 h1 with h1 | h1
    · exact CNFClause.satisfies_cons.2 (Or.inr (chainTail_sound h2 h1))
    · simp at h1

/-- An assignment satisfying `to3Aux φ` satisfies `φ` on the even variables. -/
theorem to3Aux_sound {v' : ℕ → Bool} :
    ∀ {φ : CNF}, CNF.Satisfies v' (to3Aux φ).2 → CNF.Satisfies (fun n => v' (ren n)) φ
  | [], _ => CNF.satisfies_nil _
  | _ :: _, h => by
    simp only [to3Aux, CNF.satisfies_append] at h
    exact CNF.satisfies_cons.2 ⟨chain_sound h.1, to3Aux_sound h.2⟩

/-! ### Completeness: an assignment for `φ` extends to one for `to3 φ` -/

/-- An assignment that agrees with `v` on even variables and makes fresh variable `z - j` true
exactly when `v` satisfies a literal of `(l :: ls).drop j` satisfies `chainTail (l :: ls) z`. -/
theorem chainTail_complete {v v' : ℕ → Bool} (hv : ∀ n, v' (ren n) = v n) {ls : CNFClause} :
    ∀ {l : ℕ × Bool} {z : ℕ},
      (∀ j ≤ ls.length, v' (fresh (z - j)) = clauseSatisfied v ((l :: ls).drop j)) →
      CNF.Satisfies v' (chainTail (l :: ls) z) := by
  induction ls with
  | nil =>
    intro l z hz
    have h0 := hz 0 le_rfl
    simp only [Nat.sub_zero, List.drop_zero] at h0
    cases h : v' (fresh z) <;> simp_all [chainTail, renLit, clauseSatisfied]
  | cons l' ls ih =>
    intro l z hz
    simp only [chainTail, CNF.satisfies_cons]
    refine ⟨?_, ih fun j hj => ?_⟩
    · have h0 := hz 0 (Nat.zero_le _)
      have h1 := hz 1 (by simp)
      simp only [Nat.sub_zero, List.drop_zero, List.drop_succ_cons] at h0 h1
      cases h : v' (fresh z) <;> simp_all [renLit, clauseSatisfied]
    · have h := hz (j + 1) (by simpa using hj)
      rw [Nat.sub_sub, Nat.add_comm 1 j]
      simpa using h

/-- If `v` satisfies `C`, an assignment that agrees with `v` on even variables and gives the fresh
variables `[u, u + used C)` their `clauseSatisfied` values satisfies `chain C u`. -/
theorem chain_complete {v v' : ℕ → Bool} (hv : ∀ n, v' (ren n) = v n) {C : CNFClause} {u : ℕ}
    (hC : CNFClause.Satisfies v C)
    (hz : ∀ w, u ≤ w → w < u + used C →
      v' (fresh w) = clauseSatisfied v (C.drop (u + used C - w))) :
    CNF.Satisfies v' (chain C u) := by
  match C, hC, hz with
  | [], hC, _ => simp at hC
  | [l], hC, _ => simpa [chain, renLit, hv] using hC
  | l :: l' :: ls, hC, hz =>
    simp only [chain, CNF.satisfies_cons]
    have hk : used (l :: l' :: ls) = ls.length + 1 := by simp [used]
    rw [hk] at hz
    refine ⟨?_, chainTail_complete hv fun j hj => ?_⟩
    · have h1 := hz (u + ls.length) (by omega) (by omega)
      rw [show u + (ls.length + 1) - (u + ls.length) = 1 by omega] at h1
      rcases CNFClause.satisfies_cons.1 hC with h | h
      · refine CNFClause.satisfies_cons.2 (Or.inl ?_)
        change v' (ren l.1) = l.2
        rw [hv]
        exact h
      · refine CNFClause.satisfies_cons.2 (Or.inr (CNFClause.satisfies_cons.2 (Or.inl ?_)))
        change v' (fresh (u + ls.length)) = true
        rw [h1]
        exact clauseSatisfied_eq_true_iff.2 h
    · have h := hz (u + ls.length - j) (by omega) (by omega)
      rw [show u + (ls.length + 1) - (u + ls.length - j) = j + 1 by omega] at h
      simpa using h

/-- The value that the assignment built from `v` gives fresh variable number `w` in `to3 φ`: the
clause `C` whose range `[u, u + used C)` contains `w` is located through `to3Aux`, and `w` is true
when `v` satisfies a literal of `C` past position `u + used C - w`. -/
def freshVal (v : ℕ → Bool) : CNF → ℕ → Bool
  | [], _ => false
  | C :: φ, w =>
      if w < (to3Aux φ).1 then freshVal v φ w
      else clauseSatisfied v (C.drop ((to3Aux φ).1 + used C - w))

/-- If `v` satisfies `φ`, an assignment that agrees with `v` on even variables and with
`freshVal v φ` on fresh variables below `(to3Aux φ).1` satisfies `to3Aux φ`. -/
theorem to3Aux_complete {v v' : ℕ → Bool} (hv : ∀ n, v' (ren n) = v n) :
    ∀ {φ : CNF}, CNF.Satisfies v φ → (∀ w < (to3Aux φ).1, v' (fresh w) = freshVal v φ w) →
      CNF.Satisfies v' (to3Aux φ).2
  | [], _, _ => CNF.satisfies_nil _
  | C :: φ, hφ, hw => by
    rw [CNF.satisfies_cons] at hφ
    simp only [to3Aux, CNF.satisfies_append]
    refine ⟨chain_complete hv hφ.1 fun w h1 h2 => ?_, to3Aux_complete hv hφ.2 fun w h => ?_⟩
    · rw [hw w (by simpa [to3Aux] using h2)]
      simp [freshVal, Nat.not_lt.2 h1]
    · rw [hw w (by simp only [to3Aux]; omega)]
      simp [freshVal, h]

/-- The assignment for `to3 φ` built from an assignment `v` for `φ`: `v` on even variables,
`freshVal` on fresh ones (`Nat.log2 (fresh w - 1) - 1 = w`). -/
def lift (v : ℕ → Bool) (φ : CNF) (n : ℕ) : Bool :=
  if n % 2 = 0 then v (n / 2) else freshVal v φ (Nat.log2 (n - 1) - 1)

/-- `lift v φ` agrees with `v` on the renamed variables. -/
theorem lift_ren (v : ℕ → Bool) (φ : CNF) (n : ℕ) : lift v φ (ren n) = v n := by
  simp [lift, ren]

/-- `lift v φ` gives fresh variables their `freshVal`. -/
theorem lift_fresh (v : ℕ → Bool) (φ : CNF) (w : ℕ) : lift v φ (fresh w) = freshVal v φ w := by
  have h1 : fresh w % 2 = 1 := by
    simp only [fresh, pow_succ]
    omega
  have h2 : Nat.log2 (fresh w - 1) - 1 = w := by
    simp [fresh]
  simp [lift, h1, h2]

/-- The translation preserves satisfiability. -/
theorem cnfSat_to3_iff (φ : CNF) : CNFSat (to3 φ) ↔ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies, cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨v', h⟩
    exact ⟨_, to3Aux_sound h⟩
  · rintro ⟨v, h⟩
    exact ⟨lift v φ, to3Aux_complete (lift_ren v φ) h fun w _ => lift_fresh v φ w⟩

/-! ### The reduction on bit strings -/

/-- No formula encodes to the empty string. -/
theorem encodeCNF_ne_nil (φ : CNF) : encodeCNF φ ≠ [] := by
  simp [encodeCNF]

/-- `reduce3` preserves membership: the correctness condition of SAT ≤ 3SAT. Polynomial time,
the other half of `Cslib.CookLevin.PolyManyOneRed`, is proved for the machine separately. -/
theorem satDec_eq_sat3Dec_reduce3 (x : List Bool) : satDec x = sat3Dec (reduce3 x) := by
  unfold satDec sat3Dec reduce3
  cases h : decodeCNF x with
  | none =>
    have hx : x ∉ SATLang := by
      rintro ⟨ψ, rfl, -⟩
      simp at h
    have hy : ¬ ∃ ψ : CNF, encodeCNF ψ = [] ∧ is3 ψ = true ∧ CNFSat ψ :=
      fun ⟨ψ, hψ, _⟩ => encodeCNF_ne_nil ψ hψ
    simp [hx, hy]
  | some φ =>
    rw [decodeCNF_eq_some_iff] at h
    subst h
    have hx : encodeCNF φ ∈ SATLang ↔ CNFSat φ :=
      ⟨fun ⟨ψ, hψ, hs⟩ => encodeCNF_injective hψ ▸ hs, fun hs => ⟨φ, rfl, hs⟩⟩
    have hy : (∃ ψ : CNF, encodeCNF ψ = encodeCNF (to3 φ) ∧ is3 ψ = true ∧ CNFSat ψ) ↔
        CNFSat φ := by
      constructor
      · rintro ⟨ψ, hψ, -, hs⟩
        rw [encodeCNF_injective hψ] at hs
        exact (cnfSat_to3_iff φ).1 hs
      · intro hs
        exact ⟨to3 φ, rfl, is3_to3 φ, (cnfSat_to3_iff φ).2 hs⟩
    by_cases hs : CNFSat φ <;> simp [hx, hy, hs]

end Cslib.Complexity.Karp
