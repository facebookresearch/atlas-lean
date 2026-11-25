/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turing reducibility between sets of naturals
-/
module

public import CSLibExt.Computability.Decidability.Undecidable
public import Mathlib.Computability.TuringDegree

/-!
# Turing reducibility between sets of naturals

Mathlib's Turing reducibility `f ≤ᵀ g` (`Mathlib/Computability/TuringDegree.lean`) relates partial
functions `ℕ →. ℕ`: `f` is partial recursive with oracle `g`. A set of naturals `p` is compared
through its characteristic function `charFun p` (Sipser, §6.3):

* `ComputablePred.of_turingReducible`, `TM2Decidable.of_turingReducible`:
  if `charFun p ≤ᵀ charFun q` and `q` is decidable, then `p` is decidable;
* `not_turingReducible_halting`: the halting set is not Turing reducible to any decidable set;
* `turingReducible_of_manyOneReducible`: many-one reducibility implies Turing reducibility;
* `turingEquivalent_charFun_not`: every set is Turing equivalent to its complement. For the
  halting set, the complement is not many-one reducible to it (`not_manyOneReducible_not_halting`),
  so Turing reducibility is strictly coarser.

## Main definitions

- `charFun` (with `charFun_of_pos`, `charFun_of_neg`, `one_mem_charFun`, `zero_mem_charFun`),
  `haltingSet`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §6.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open scoped Computability
open Nat.Partrec (Code)
open Encodable Denumerable

/-- **Characteristic function of a set of naturals.** The characteristic function of a set $p$ of
natural numbers is the partial function $\mathbb{N} \rightharpoonup \mathbb{N}$ that is defined at
every $n$, with value $1$ if $n \in p$ and value $0$ otherwise. -/
noncomputable def charFun (p : ℕ → Prop) : ℕ →. ℕ :=
  open Classical in fun n ↦ Part.some (if p n then 1 else 0)

theorem charFun_of_pos {p : ℕ → Prop} {n : ℕ} (h : p n) : charFun p n = Part.some 1 := by
  simp [charFun, h]

theorem charFun_of_neg {p : ℕ → Prop} {n : ℕ} (h : ¬p n) : charFun p n = Part.some 0 := by
  simp [charFun, h]

@[simp]
theorem one_mem_charFun {p : ℕ → Prop} {n : ℕ} : 1 ∈ charFun p n ↔ p n := by
  by_cases h : p n <;> simp [charFun_of_pos, charFun_of_neg, h]

@[simp]
theorem zero_mem_charFun {p : ℕ → Prop} {n : ℕ} : 0 ∈ charFun p n ↔ ¬p n := by
  by_cases h : p n <;> simp [charFun_of_pos, charFun_of_neg, h]

/-- **A set is decidable iff its characteristic function is partial recursive.** A set $p$ of
natural numbers is decidable (computable as a predicate) if and only if its characteristic function
is partial recursive. -/
theorem computablePred_iff_partrec_charFun {p : ℕ → Prop} :
    ComputablePred p ↔ Partrec (charFun p) := by
  classical
  constructor
  · rintro ⟨_, hp⟩
    refine (Computable.cond hp (Computable.const 1) (Computable.const 0)).partrec.of_eq fun n ↦ ?_
    by_cases h : p n <;> simp [charFun_of_pos, charFun_of_neg, h]
  · intro h
    have hc : Computable fun n ↦ if p n then 1 else 0 := h.of_eq fun n ↦ by
      by_cases hn : p n <;> simp [charFun_of_pos, charFun_of_neg, hn]
    refine ⟨inferInstance, (Primrec.eq.decide.to_comp.comp hc (Computable.const 1)).of_eq
      fun n ↦ ?_⟩
    by_cases h : p n <;> simp [h]

/-- **Decidability transfers down Turing reducibility.** Let $p$ and $q$ be sets of natural numbers
such that the characteristic function of $p$ is Turing reducible to the characteristic function of
$q$. If $q$ is decidable, then $p$ is decidable. -/
theorem ComputablePred.of_turingReducible {p q : ℕ → Prop} (h : charFun p ≤ᵀ charFun q)
    (hq : ComputablePred q) : ComputablePred p :=
  computablePred_iff_partrec_charFun.mpr <| partrec_iff_forall_turingReducible.mpr fun _ ↦
    h.trans ((computablePred_iff_partrec_charFun.mp hq).turingReducible)

theorem TM2Decidable.of_turingReducible {p q : ℕ → Prop} (h : charFun p ≤ᵀ charFun q)
    (hq : TM2Decidable q) : TM2Decidable p :=
  tm2Decidable_iff_computablePred.mpr
    (ComputablePred.of_turingReducible h (tm2Decidable_iff_computablePred.mp hq))

/-- **Halting set.** Fix the standard bijective numbering $n \mapsto c_n$ of the codes of partial
recursive functions $\mathbb{N} \rightharpoonup \mathbb{N}$. The halting set is the set of natural
numbers $n$ such that the partial recursive function with code $c_n$ is defined at $0$. -/
def haltingSet (n : ℕ) : Prop := ((ofNat Code n).eval 0).Dom

theorem not_computablePred_haltingSet : ¬ComputablePred haltingSet := fun h ↦
  ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr <| by
    obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.mp h
    refine ⟨f ∘ encode, hf.comp Computable.encode, funext fun c ↦ ?_⟩
    have := congrFun hfeq (encode c)
    simp only [haltingSet, ofNat_encode] at this
    simp [this])

/-- **The halting set is not Turing reducible to a decidable set.** For every decidable set $q$ of
natural numbers, the characteristic function of the halting set is not Turing reducible to the
characteristic function of $q$. -/
theorem not_turingReducible_halting {q : ℕ → Prop} (hq : ComputablePred q) :
    ¬charFun haltingSet ≤ᵀ charFun q := fun h ↦
  not_computablePred_haltingSet (ComputablePred.of_turingReducible h hq)

/-- **Many-one reducibility implies Turing reducibility.** If $p$ and $q$ are sets of natural
numbers and $p$ is many-one reducible to $q$, that is, there is a computable
$f : \mathbb{N} \to \mathbb{N}$ with $n \in p \iff f(n) \in q$ for all $n$, then the characteristic
function of $p$ is Turing reducible to the characteristic function of $q$. -/
theorem turingReducible_of_manyOneReducible {p q : ℕ → Prop} (h : p ≤₀ q) :
    charFun p ≤ᵀ charFun q := by
  obtain ⟨f, hf, hpq⟩ := h
  refine RecursiveIn.iff_nat.mpr ((Nat.RecursiveIn.comp (.oracle _ (Set.mem_singleton _))
    (Partrec.nat_iff.mp hf.partrec).recursiveIn).of_eq fun n ↦ ?_)
  change (Part.some (f n)).bind (fun m ↦ charFun q m) = charFun p n
  rw [Part.bind_some]
  by_cases h : p n
  · rw [charFun_of_pos h, charFun_of_pos ((hpq n).mp h)]
  · rw [charFun_of_neg h, charFun_of_neg (mt (hpq n).mpr h)]

/-- **Every set is Turing equivalent to its complement.** For every set $p$ of natural numbers,
the characteristic function of the complement $\mathbb{N} \setminus p$ and the characteristic
function of $p$ are Turing equivalent: each is Turing reducible to the other. -/
theorem turingEquivalent_charFun_not (p : ℕ → Prop) : charFun (fun n ↦ ¬p n) ≡ᵀ charFun p := by
  have hsub : Nat.Partrec fun m : ℕ ↦ (Part.some (1 - m) : Part ℕ) :=
    Partrec.nat_iff.mp (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp.partrec
  refine ⟨RecursiveIn.iff_nat.mpr ((Nat.RecursiveIn.comp hsub.recursiveIn
    (.oracle _ (Set.mem_singleton _))).of_eq fun n ↦ ?_), RecursiveIn.iff_nat.mpr
      ((Nat.RecursiveIn.comp hsub.recursiveIn (.oracle _ (Set.mem_singleton _))).of_eq
        fun n ↦ ?_)⟩
  · by_cases h : p n <;> simp [charFun_of_pos, charFun_of_neg, h]
  · by_cases h : p n <;> simp [charFun_of_pos, charFun_of_neg, h]

/-- **The complement of the halting set is not many-one reducible to it.** There is no computable
function $f : \mathbb{N} \to \mathbb{N}$ such that, for every $n$, $n$ is outside the halting set
if and only if $f(n)$ is in the halting set.

The halting set is recognizable and its complement is not. Since every set is Turing equivalent to
its complement, Turing reducibility is strictly coarser than many-one reducibility. -/
theorem not_manyOneReducible_not_halting : ¬(fun n ↦ ¬haltingSet n) ≤₀ haltingSet := by
  intro h
  have hre : TM2Recognizable haltingSet :=
    tm2Recognizable_of_manyOneReducible ⟨ofNat Code, (Primrec.ofNat Code).to_comp,
      fun _ ↦ Iff.rfl⟩ (tm2Recognizable_halting 0)
  have henc : (fun c : Code ↦ ¬(c.eval 0).Dom) ≤₀ fun n ↦ ¬haltingSet n :=
    ⟨encode, Computable.encode, fun c ↦ by simp [haltingSet, ofNat_encode]⟩
  exact not_tm2CoRecognizable_halting 0 (tm2Recognizable_of_manyOneReducible (henc.trans h) hre)

end Cslib.Decidability
