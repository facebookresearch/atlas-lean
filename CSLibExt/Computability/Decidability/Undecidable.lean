/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Undecidability for multi-stack machines: halting, Rice, mapping reductions
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import Mathlib.Computability.Halting
public import Mathlib.Computability.Reduce

/-!
# Undecidability for multi-stack machines: halting, Rice, mapping reductions

Mathlib proves the halting problem and Rice's theorem for partial recursive codes
(`Nat.Partrec.Code`). Through `tm2Decidable_iff_computablePred` they become statements about
Mathlib's bundled multi-stack machines.

* No `FinTM2` decides whether a code halts on a fixed input (`not_tm2Decidable_halting`). The
  halting set is recognizable but not co-recognizable.
* Some `FinTM2` has an undecidable halting set (`exists_not_tm2Decidable_tm2HaltsOn`). This is
  the halting problem for the machines themselves.
* Rice's theorem (`rice_tm2`): a machine-decidable property of codes that holds for one partial
  recursive function holds for all of them.
* Mathlib's `ManyOneReducible` is exactly reducibility by a function whose action on codes a
  `FinTM2` computes (`manyOneReducible_iff_exists_tm2`), and it transfers decidability and
  recognizability downward.

## Main results

- `not_tm2Decidable_halting`, `tm2Recognizable_halting`, `not_tm2CoRecognizable_halting`.
- `exists_not_tm2Decidable_tm2HaltsOn`.
- `rice_tm2`.
- `manyOneReducible_iff_exists_tm2`, `tm2Decidable_of_manyOneReducible`,
  `tm2Recognizable_of_manyOneReducible`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Turing Encodable MetaMathlibExt.TM2Recursive
open Nat.Partrec (Code)

/-! ### The halting problem -/

/-- **The halting problem is undecidable by multi-stack machines.** For every $n \in \mathbb{N}$,
no multi-stack machine decides whether a partial recursive code halts on input $n$. -/
theorem not_tm2Decidable_halting (n : ℕ) : ¬TM2Decidable fun c : Code ↦ (c.eval n).Dom :=
  fun h ↦ ComputablePred.halting_problem n (tm2Decidable_iff_computablePred.mp h)

/-- **The halting problem is recognizable by multi-stack machines.** For every
$n \in \mathbb{N}$, the set of partial recursive codes whose program halts on input $n$ is
recognizable by a multi-stack machine. -/
theorem tm2Recognizable_halting (n : ℕ) : TM2Recognizable fun c : Code ↦ (c.eval n).Dom :=
  tm2Recognizable_iff_rePred.mpr (ComputablePred.halting_problem_re n)

/-- **The halting problem is not co-recognizable by multi-stack machines.** For every
$n \in \mathbb{N}$, the set of partial recursive codes whose program halts on input $n$ is not
co-recognizable by a multi-stack machine: no multi-stack machine halts on exactly the codes
whose program does not halt on input $n$. -/
theorem not_tm2CoRecognizable_halting (n : ℕ) :
    ¬TM2CoRecognizable fun c : Code ↦ (c.eval n).Dom :=
  fun h ↦ ComputablePred.halting_problem_not_re n (tm2CoRecognizable_iff_rePred_not.mp h)

/-- **Some multi-stack machine has an undecidable halting set.** There is a multi-stack machine
$M$, with a bijection between its input alphabet and the Booleans, such that no multi-stack
machine decides, for $n \in \mathbb{N}$, whether $M$ halts when started on the binary
representation of $n$ (written in $M$'s input alphabet through the bijection).

The halting set of a code interpreter on input $0$ is r.e., hence the halting set of a
multi-stack machine, and deciding it would decide the halting problem. -/
theorem exists_not_tm2Decidable_tm2HaltsOn :
    ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
      ¬TM2Decidable fun n : ℕ ↦ TM2HaltsOn tm ((encodeNat n).map e.symm) := by
  let q : ℕ → Prop := fun n ↦ ((Denumerable.ofNat Code n).eval 0).Dom
  have hq : REPred q :=
    Partrec.comp (ComputablePred.halting_problem_re 0) (Computable.ofNat Code)
  obtain ⟨tm, e, h⟩ := exists_tm2HaltsOn_iff_of_rePred hq
  refine ⟨tm, e, fun hdec ↦ not_tm2Decidable_halting 0 ?_⟩
  obtain ⟨f, hf, hfq⟩ := hdec
  refine ⟨f, hf, fun c ↦ ?_⟩
  have hc := hfq (encode c)
  rw [encode_nat] at hc
  refine hc.trans ((h (encode c)).symm.trans ?_)
  simp [q]

/-! ### Rice's theorem -/

/-- **Rice's theorem for multi-stack machines.** Let $C$ be a set of partial functions
$\mathbb{N} \to \mathbb{N}$. If a multi-stack machine decides, for each partial recursive code,
whether the function the code computes lies in $C$, then for all partial recursive functions
$f$ and $g$, $f \in C$ implies $g \in C$. -/
theorem rice_tm2 (C : Set (ℕ →. ℕ)) (h : TM2Decidable fun c : Code ↦ c.eval ∈ C)
    {f g : ℕ →. ℕ} (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hfC : f ∈ C) : g ∈ C :=
  ComputablePred.rice C (tm2Decidable_iff_computablePred.mp h) hf hg hfC

/-! ### Mapping reductions -/

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- **Mapping reductions are computed by multi-stack machines.** Let $p$ and $q$ be predicates on
primitive recursively encodable types $\alpha$ and $\beta$, and write $\langle x \rangle \in
\mathbb{N}$ for the code of $x$. Then $p$ is many-one reducible to $q$ if and only if there is a
function $f : \alpha \to \beta$ with $p(a) \iff q(f(a))$ for all $a \in \alpha$, together with a
function $F : \mathbb{N} \to \mathbb{N}$ that a multi-stack machine computes on binary
representations and that satisfies $F(\langle a \rangle) = \langle f(a) \rangle$ for all
$a \in \alpha$. -/
theorem manyOneReducible_iff_exists_tm2 {p : α → Prop} {q : β → Prop} :
    ManyOneReducible p q ↔ ∃ f : α → β, (∃ F : ℕ → ℕ,
      Nonempty (TM2Computable encodeNat encodeNat F) ∧ ∀ a, F (encode a) = encode (f a)) ∧
        ∀ a, p a ↔ q (f a) := by
  constructor
  · rintro ⟨f, hf, hpq⟩
    let F : ℕ → ℕ := fun n ↦ ((decode (α := α) n).map fun a ↦ encode (f a)).getD 0
    have hF : Computable F :=
      Computable.option_getD (Computable.option_map Computable.decode
        ((Computable.encode.comp (hf.comp Computable.snd)).to₂)) (Computable.const 0)
    obtain ⟨hT⟩ := tm2Computable_of_computable hF
    exact ⟨f, ⟨F, ⟨hT⟩, fun a ↦ by simp [F, encodek]⟩, hpq⟩
  · rintro ⟨f, ⟨F, ⟨hF⟩, hFf⟩, hpq⟩
    refine ⟨f, ?_, hpq⟩
    refine Computable.encode_iff.mp ?_
    exact ((computable_of_tm2Computable hF).comp Computable.encode).of_eq hFf

/-- **Decidability transfers along mapping reductions.** Let $p$ and $q$ be predicates on
primitive recursively encodable types $\alpha$ and $\beta$. If $p$ is many-one reducible to $q$
and $q$ is decidable by a multi-stack machine, then $p$ is decidable by a multi-stack machine. -/
theorem tm2Decidable_of_manyOneReducible {p : α → Prop} {q : β → Prop}
    (h : ManyOneReducible p q) (hq : TM2Decidable q) : TM2Decidable p :=
  tm2Decidable_iff_computablePred.mpr
    (ComputablePred.computable_of_manyOneReducible h (tm2Decidable_iff_computablePred.mp hq))

/-- **Recognizability transfers along mapping reductions.** Let $p$ and $q$ be predicates on
primitive recursively encodable types $\alpha$ and $\beta$. If $p$ is many-one reducible to $q$
and $q$ is recognizable by a multi-stack machine, then $p$ is recognizable by a multi-stack
machine. -/
theorem tm2Recognizable_of_manyOneReducible {p : α → Prop} {q : β → Prop}
    (h : ManyOneReducible p q) (hq : TM2Recognizable q) : TM2Recognizable p := by
  obtain ⟨f, hf, hpq⟩ := h
  have : REPred fun a ↦ q (f a) := Partrec.comp (tm2Recognizable_iff_rePred.mp hq) hf
  exact tm2Recognizable_iff_rePred.mpr (this.of_eq fun a ↦ (hpq a).symm)

end Cslib.Decidability
