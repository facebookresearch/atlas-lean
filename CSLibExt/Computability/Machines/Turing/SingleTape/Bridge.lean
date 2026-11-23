/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.ToRecursive
public import CSLibExt.Computability.Machines.Turing.SingleTape.OfRecursive
public import CSLibExt.Computability.Decidability.Undecidable

/-!
# Single-tape machines decide and recognize exactly the recursive predicates

CSLib's single-tape machines (`Cslib.Turing.SingleTapeTM`) and Mathlib's multi-stack machines
(`Turing.FinTM2`) have the same decidable and recognizable predicates, and both are Mathlib's
`ComputablePred` and `REPred`. The two halves are `ToRecursive` (a machine's halting set is r.e.,
its outputs partial recursive) and `OfRecursive` (r.e. and computable predicates get single-tape
machines, through Mathlib's `TM2 → TM1 → TM0` translations).

Consequences on the single-tape model: Post's theorem, and the halting problem for
`Nat.Partrec.Code` is recognizable but neither decidable nor co-recognizable.

## Main results

- `singleTapeDecidable_iff_computablePred`, `singleTapeRecognizable_iff_rePred`,
  `singleTapeCoRecognizable_iff_rePred_not`: the bridges to Mathlib.
- `singleTapeDecidable_iff_tm2Decidable`, `singleTapeRecognizable_iff_tm2Recognizable`: the
  single-tape and multi-stack classes agree.
- `singleTapeDecidable_iff_singleTapeRecognizable_and_singleTapeCoRecognizable`: Post's theorem.
- `not_singleTapeDecidable_halting`, `singleTapeRecognizable_halting`,
  `not_singleTapeCoRecognizable_halting`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013: Corollary 3.15
  with multi-stack machines in place of multitape machines (here through recursion theory, not a
  direct simulation), Theorem 4.22 (Post's theorem), Theorem 5.1 (the halting problem) and
  Corollary 4.23 (its complement is not recognizable; there for `A_TM`).
-/

@[expose] public section

set_option autoImplicit false

open Computability Nat.Partrec

namespace Cslib.Decidability

variable {α : Type*} [Primcodable α] {p : α → Prop}

/-- **Single-tape decidable predicates are exactly the computable predicates.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is decidable by a single-tape machine if and only
if it is computable, that is, $p$ is decidable and its Boolean characteristic function
$\alpha \to \mathrm{Bool}$ is computable. -/
theorem singleTapeDecidable_iff_computablePred : SingleTapeDecidable p ↔ ComputablePred p :=
  ⟨SingleTapeDecidable.computablePred, SingleTapeDecidable.of_computablePred⟩

/-- **Single-tape recognizable predicates are exactly the r.e. predicates.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is recognizable by a single-tape machine if and
only if it is recursively enumerable, that is, the partial function on $\alpha$ that is defined,
with a trivial value, exactly where $p$ holds is partial recursive. -/
theorem singleTapeRecognizable_iff_rePred : SingleTapeRecognizable p ↔ REPred p :=
  ⟨SingleTapeRecognizable.rePred, SingleTapeRecognizable.of_rePred⟩

/-- **Single-tape co-recognizable predicates are those with an r.e. complement.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is co-recognizable by a single-tape machine if
and only if its complement $\neg p$ is recursively enumerable, that is, the partial function on
$\alpha$ that is defined, with a trivial value, exactly where $\neg p$ holds is partial
recursive. -/
theorem singleTapeCoRecognizable_iff_rePred_not :
    SingleTapeCoRecognizable p ↔ REPred fun a ↦ ¬p a :=
  singleTapeRecognizable_iff_rePred

/-- **Single-tape and multi-stack machines decide the same predicates.** -/
theorem singleTapeDecidable_iff_tm2Decidable : SingleTapeDecidable p ↔ TM2Decidable p := by
  rw [singleTapeDecidable_iff_computablePred, tm2Decidable_iff_computablePred]

/-- **Single-tape and multi-stack machines recognize the same predicates.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is recognizable by a single-tape machine if and
only if it is recognizable by a multi-stack machine. -/
theorem singleTapeRecognizable_iff_tm2Recognizable :
    SingleTapeRecognizable p ↔ TM2Recognizable p := by
  rw [singleTapeRecognizable_iff_rePred, tm2Recognizable_iff_rePred]

/-- **Post's theorem** for single-tape machines: a predicate is decidable iff it is recognizable
and co-recognizable. -/
theorem singleTapeDecidable_iff_singleTapeRecognizable_and_singleTapeCoRecognizable :
    SingleTapeDecidable p ↔ SingleTapeRecognizable p ∧ SingleTapeCoRecognizable p := by
  rw [singleTapeDecidable_iff_computablePred, singleTapeCoRecognizable_iff_rePred_not,
    singleTapeRecognizable_iff_rePred]
  exact ComputablePred.computable_iff_re_compl_re'

/-- **Decidable predicates are recognizable by single-tape machines.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a single-tape machine, then
$p$ is recognizable by a single-tape machine. -/
theorem SingleTapeDecidable.singleTapeRecognizable (h : SingleTapeDecidable p) :
    SingleTapeRecognizable p :=
  (singleTapeDecidable_iff_singleTapeRecognizable_and_singleTapeCoRecognizable.mp h).1

/-- **Single-tape decidable predicates are co-recognizable.** Let $\alpha$ be a primcodable type
(it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive
recursive). If a predicate $p$ on $\alpha$ is decidable by a single-tape machine, then $p$ is
co-recognizable by a single-tape machine, that is, its complement $\neg p$ is recognizable by a
single-tape machine. -/
theorem SingleTapeDecidable.singleTapeCoRecognizable (h : SingleTapeDecidable p) :
    SingleTapeCoRecognizable p :=
  (singleTapeDecidable_iff_singleTapeRecognizable_and_singleTapeCoRecognizable.mp h).2

/-- **Single-tape decidable predicates are closed under complement.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a single-tape machine, then so
is its complement $\neg p$. -/
theorem SingleTapeDecidable.not (h : SingleTapeDecidable p) :
    SingleTapeDecidable fun a ↦ ¬p a :=
  singleTapeDecidable_iff_computablePred.mpr (singleTapeDecidable_iff_computablePred.mp h).not

/-- **The halting problem for partial recursive codes is undecidable on single-tape machines.**
For every $n \in \mathbb{N}$, no single-tape machine decides whether a partial recursive code halts
on input $n$.

Source: Sipser, Theorem 5.1, for codes of partial recursive functions run on $n$. -/
theorem not_singleTapeDecidable_halting (n : ℕ) :
    ¬SingleTapeDecidable fun c : Code ↦ (c.eval n).Dom :=
  fun h ↦ not_tm2Decidable_halting n (singleTapeDecidable_iff_tm2Decidable.mp h)

/-- **The halting problem for partial recursive codes is recognizable on single-tape machines.**
For every $n \in \mathbb{N}$, the set of partial recursive codes whose program halts on input $n$
is recognizable by a single-tape machine. -/
theorem singleTapeRecognizable_halting (n : ℕ) :
    SingleTapeRecognizable fun c : Code ↦ (c.eval n).Dom :=
  singleTapeRecognizable_iff_tm2Recognizable.mpr (tm2Recognizable_halting n)

/-- **The halting problem for partial recursive codes is not co-recognizable on single-tape
machines.** For every $n \in \mathbb{N}$, the set of partial recursive codes whose program halts on
input $n$ is not co-recognizable by a single-tape machine: no single-tape machine halts on exactly
the codes whose program does not halt on input $n$.

Source: Sipser, Corollary 4.23 (there for $A_{TM}$), with partial recursive codes run on $n$. -/
theorem not_singleTapeCoRecognizable_halting (n : ℕ) :
    ¬SingleTapeCoRecognizable fun c : Code ↦ (c.eval n).Dom :=
  fun h ↦ not_tm2CoRecognizable_halting n (singleTapeRecognizable_iff_tm2Recognizable.mp h)

end Cslib.Decidability
