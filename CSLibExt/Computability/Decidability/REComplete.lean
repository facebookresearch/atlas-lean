/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The halting set is r.e.-complete
-/
module

public import CSLibExt.Computability.Decidability.TuringReducible

/-!
# The halting set is r.e.-complete

`haltingSet` (codes that halt on `0`) is recognizable (`rePred_haltingSet`, from Mathlib's
`ComputablePred.halting_problem_re`), and every recognizable predicate many-one reduces to it
(`manyOneReducible_haltingSet`): if `c` computes a partial function with domain `p`, then `a`
maps to the code `comp c (const (encode a))`, which ignores its input and runs `c` on `encode a`
(an instance of the s-m-n theorem). The reduction is injective, so the halting set is even
one-one complete (`oneOneReducible_haltingSet`). Recognizability transfers down many-one reductions
(`REPred.of_manyOneReducible`), so a predicate is recognizable iff it many-one reduces to the
halting set (`rePred_iff_manyOneReducible_haltingSet`), and equivalently iff a multi-stack
machine recognizes it (`tm2Recognizable_iff_manyOneReducible_haltingSet`).

## Main results

- `rePred_haltingSet`, `oneOneReducible_haltingSet`, `manyOneReducible_haltingSet`,
  `rePred_iff_oneOneReducible_haltingSet`, `rePred_iff_manyOneReducible_haltingSet`,
  `tm2Recognizable_iff_manyOneReducible_haltingSet`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.3
  (mapping reducibility) and §6.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Nat.Partrec (Code)
open Encodable Denumerable

/-- **Composing a code with a constant code ignores the input.** Let $c$ be a code of a partial
recursive function and let $n, m \in \mathbb{N}$. The code that first computes the constant
function with value $n$ and then applies $c$, evaluated at $m$, gives the same partial value as
$c$ evaluated at $n$: one is defined exactly when the other is, and then they are equal. -/
theorem eval_comp_const (c : Code) (n m : ℕ) : (Code.comp c (Code.const n)).eval m = c.eval n := by
  simp only [Code.eval, Code.eval_const]
  exact Part.bind_some n c.eval

/-- **Recognizability transfers down many-one reductions.** Let $\alpha$ and $\beta$ be types
with primitive recursive encodings into $\mathbb{N}$, and let $p$ and $q$ be predicates on
$\alpha$ and on $\beta$. Suppose that $p$ many-one reduces to $q$, that is, there is a computable
function $f : \alpha \to \beta$ such that for every $a \in \alpha$, $p(a)$ holds if and only if
$q(f(a))$ holds. If $q$ is recognizable (recursively enumerable: the domain of a partial
computable function on $\beta$), then $p$ is recognizable. -/
theorem REPred.of_manyOneReducible {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop}
    {q : β → Prop} (h : ManyOneReducible p q) (hq : REPred q) : REPred p := by
  obtain ⟨f, hf, hpq⟩ := h
  exact REPred.of_eq (p := fun a ↦ q (f a)) (Partrec.comp (g := fun a ↦ f a) hq hf)
    fun a ↦ (hpq a).symm

/-- **The halting set is recognizable.** The halting set, the set of numbers $n$ such that the
code with number $n$ halts on input $0$, is recursively enumerable: it is the domain of a partial
computable function on $\mathbb{N}$. -/
theorem rePred_haltingSet : REPred haltingSet :=
  Partrec.comp (g := fun n ↦ ofNat Code n) (ComputablePred.halting_problem_re 0)
    (Computable.ofNat Code)

/-- **Every recognizable predicate one-one reduces to the halting set.** Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$, and let $p$ be a recognizable (recursively
enumerable) predicate on $\alpha$, that is, the domain of a partial computable function on
$\alpha$. Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive
function with code number $n$ halts on input $0$. Then there is an injective computable function
$f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds if and only if $f(a)$
lies in the halting set.

The proof takes for $f(a)$ the number of the code that ignores its input and runs a code for $p$
on the number encoding $a$; distinct $a$ give distinct codes. -/
theorem oneOneReducible_haltingSet {α : Type*} [Primcodable α] {p : α → Prop} (hp : REPred p) :
    OneOneReducible p haltingSet := by
  -- a code whose domain is `p`, read through `decode`
  have hG : Partrec fun n : ℕ ↦ (Part.ofOption (decode (α := α) n)).bind fun a ↦
      (Part.assert (p a) fun _ ↦ Part.some ()).map fun _ ↦ (0 : ℕ) :=
    Partrec.bind (Computable.ofOption Computable.decode)
      ((hp.comp Computable.snd).map (Computable.const 0).to₂)
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG)
  refine ⟨fun a ↦ encode (Code.comp c (Code.const (encode a))),
    (Primrec.encode.comp (Code.primrec₂_comp.comp (Primrec.const c)
      (Code.primrec_const.comp Primrec.encode))).to_comp, fun a b h ↦ ?_, fun a ↦ ?_⟩
  · have h' := encode_injective h
    simp only [Code.comp.injEq, true_and] at h'
    exact encode_injective (Code.const_inj h')
  simp only [haltingSet, ofNat_encode, eval_comp_const, hc, encodek]
  simp [Part.assert]

/-- **Every recognizable predicate many-one reduces to the halting set.** Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$, and let $p$ be a recognizable (recursively
enumerable) predicate on $\alpha$, that is, the domain of a partial computable function on
$\alpha$. Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive
function with code number $n$ halts on input $0$. Then there is a computable function
$f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds if and only if $f(a)$
lies in the halting set. -/
theorem manyOneReducible_haltingSet {α : Type*} [Primcodable α] {p : α → Prop} (hp : REPred p) :
    ManyOneReducible p haltingSet :=
  (oneOneReducible_haltingSet hp).to_many_one

/-- **A predicate is recognizable iff it many-one reduces to the halting set.** Let $\alpha$ be a
type with a primitive recursive encoding into $\mathbb{N}$ and let $p$ be a predicate on $\alpha$.
Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive function
with code number $n$ halts on input $0$. Then $p$ is recognizable (recursively enumerable: the
domain of a partial computable function on $\alpha$) if and only if there is a computable function
$f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds if and only if $f(a)$
lies in the halting set. -/
theorem rePred_iff_manyOneReducible_haltingSet {α : Type*} [Primcodable α] {p : α → Prop} :
    REPred p ↔ ManyOneReducible p haltingSet :=
  ⟨manyOneReducible_haltingSet, fun h ↦ REPred.of_manyOneReducible h rePred_haltingSet⟩

/-- **A predicate is recognizable iff it one-one reduces to the halting set.** Let $\alpha$ be a
type with a primitive recursive encoding into $\mathbb{N}$ and let $p$ be a predicate on $\alpha$.
Here the halting set is the set of $n \in \mathbb{N}$ such that the partial recursive function
with code number $n$ halts on input $0$. Then $p$ is recognizable (recursively enumerable: the
domain of a partial computable function on $\alpha$) if and only if there is an injective
computable function $f : \alpha \to \mathbb{N}$ such that for every $a \in \alpha$, $p(a)$ holds
if and only if $f(a)$ lies in the halting set. -/
theorem rePred_iff_oneOneReducible_haltingSet {α : Type*} [Primcodable α] {p : α → Prop} :
    REPred p ↔ OneOneReducible p haltingSet :=
  ⟨oneOneReducible_haltingSet, fun h ↦ REPred.of_manyOneReducible h.to_many_one rePred_haltingSet⟩

theorem tm2Recognizable_iff_manyOneReducible_haltingSet {α : Type*} [Primcodable α]
    {p : α → Prop} : TM2Recognizable p ↔ ManyOneReducible p haltingSet :=
  tm2Recognizable_iff_rePred.trans rePred_iff_manyOneReducible_haltingSet

end Cslib.Decidability
