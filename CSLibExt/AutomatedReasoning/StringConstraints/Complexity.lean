/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SAT and bounded string constraints: reduction correctness
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.Bounded
public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
public import CSLibExt.Logics.Propositional.CNF.Basic

/-!
# SAT and bounded string constraints: reduction correctness

Boolean satisfiability translates to satisfiability of bounded string
constraints at length bound `1`: a Boolean variable becomes a string
variable whose value is `[true]` or `[false]`, and a clause becomes a
disjunction of word equations. This module proves the translation
correct (the iff), and bridges it to the bounded solver: `CNFSat φ`
iff the bounded solver accepts the encoding at bound `1`
(`cnfSat_iff_boundedSatB`), so the encoding lands in the finite
search space of `Bounded.lean`.

What is *not* proved here: NP-hardness and NP membership of bounded
string-constraint satisfiability. NP-hardness would need a formal
polynomial-time bound for the translation (the translation is a
linear syntactic fold, but no formal time bound is proved), and NP
membership would need an executable polynomial-time checker
(`boundedSatB` is the checker by `boundedSatB_iff`, but it is
`noncomputable`, so no executable checker is formalized). Formal
membership in CSLib's `NP` complexity class is not claimed; the scope
note in `Bounded.lean` covers the cost model.

## Main results

- `encodeCNF`: the SAT-to-string-constraints translation.
- `cnfSat_iff_stringSat`: correctness of the translation.
- `cnfSat_iff_boundedSatB`: the bridge to the bounded solver.

## References

* S. A. Cook, *The complexity of theorem-proving procedures*,
  STOC 1971; L. A. Levin, *Universal search problems*, 1973.
* A. Kieżun, V. Ganesh, et al., *HAMPI*, ACM TOSEM 2012: HAMPI's
  bounded fragment is the one this reduction targets.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

open Cslib.Logic.PL

/-- SAT as string constraints: each clause is a disjunction of word
equations `x = [b]`, one per literal. -/
def encodeCNF (φ : CNF) : Formula Bool ℕ :=
  andChain (φ.map (fun C =>
    orChain (C.map (fun l =>
      Formula.atom (Atom.eq (Term.var l.1) (Term.const [l.2]))))))

/-- **Correctness of the SAT-to-string-constraints translation** at
length bound `1`: Boolean assignments become length-`≤ 1` string
assignments and back. -/
theorem cnfSat_iff_stringSat (φ : CNF) :
    CNFSat φ ↔ ∃ σ : ℕ → List Bool, (∀ i, (σ i).length ≤ 1) ∧
      Sat σ (encodeCNF φ) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun x => [v x], fun _ => by simp, ?_⟩
    rw [encodeCNF, sat_andChain]
    intro f hf
    rw [List.mem_map] at hf
    obtain ⟨C, hC, rfl⟩ := hf
    rw [sat_orChain]
    obtain ⟨x, b, hlit, hval⟩ := hv C hC
    refine ⟨Formula.atom (Atom.eq (Term.var x) (Term.const [b])), ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨(x, b), hlit, rfl⟩
    · change eval (fun x => [v x]) (Term.var x)
          = eval (fun x => [v x]) (Term.const [b])
      simp [hval]
  · rintro ⟨σ, -, hSat⟩
    rw [encodeCNF, sat_andChain] at hSat
    refine ⟨fun x => decide (σ x = [true]), fun C hC => ?_⟩
    have hCsat := hSat _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
    rw [sat_orChain] at hCsat
    obtain ⟨g, hg, hgsat⟩ := hCsat
    rw [List.mem_map] at hg
    obtain ⟨⟨x, b⟩, hlit, rfl⟩ := hg
    refine ⟨x, b, hlit, ?_⟩
    have hσ : σ x = [b] := hgsat
    cases b with
    | true => simp [hσ]
    | false => simp [hσ]

/-- **SAT iff the bounded solver accepts the encoding** at length
bound `1`, for any variable list covering the variables of the
encoding. This is the bridge from the reduction to the bounded
solver: `boundedSatB_iff` (soundness / completeness of the finite
search) plus the reduction correctness. -/
theorem cnfSat_iff_boundedSatB (φ : CNF) (vs : List ℕ)
    (hvars : ∀ i ∈ varsOfFormula (encodeCNF φ), i ∈ vs) :
    CNFSat φ ↔ boundedSatB vs (encodeCNF φ) 1 = true := by
  rw [cnfSat_iff_stringSat, boundedSatB_iff vs _ 1 hvars]
  constructor
  · rintro ⟨σ, hbound, hSat⟩
    exact ⟨σ, fun i _ => hbound i, hSat⟩
  · rintro ⟨σ, hbound, hSat⟩
    refine ⟨fun i => if i ∈ vs then σ i else [], ?_, ?_⟩
    · intro i
      change (if i ∈ vs then σ i else []).length ≤ 1
      split_ifs with hi
      · exact hbound i hi
      · simp
    · exact (sat_congr (fun i hi => by
        split_ifs with h
        · rfl
        · exact absurd (hvars i hi) h)).mpr hSat

end Cslib.AutomatedReasoning.StringConstraints
