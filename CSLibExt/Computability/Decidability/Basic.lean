/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidable, recognizable and co-recognizable predicates on multi-stack machines
-/
module

public import MathlibExt.Computability.TuringMachine.Recursive.Equiv
public import MathlibExt.Computability.TuringMachine.Recursive.Halts

/-!
# Decidable, recognizable and co-recognizable predicates on multi-stack machines

The language classes of computability theory, defined by Mathlib's bundled multi-stack machines
(`Turing.FinTM2`). An element `a` of a `Primcodable` type is given to a machine as the
binary word `encodeNat (encode a)`.

* `TM2Decidable p`: a machine computes a total function `f : ℕ → ℕ` with `f (encode a) = 1`
  exactly when `p a`.
* `TM2Recognizable p`: a machine halts on `encode a` exactly when `p a`.
* `TM2CoRecognizable p`: the complement of `p` is recognizable.

Through the Turing–Kleene equivalence (`computable_iff_nonempty_tm2Computable`) and its
partial form (`rePred_iff_exists_tm2HaltsOn`), these classes coincide with Mathlib's
`ComputablePred` and `REPred`. Post's theorem then transfers: a predicate is decidable iff it
is recognizable and co-recognizable.

## Main results

- `tm2Decidable_iff_computablePred`, `tm2Recognizable_iff_rePred`,
  `tm2CoRecognizable_iff_rePred_not` : the bridges to Mathlib.
- `TM2Decidable.tm2Recognizable`, `TM2Decidable.tm2CoRecognizable`, `TM2Decidable.not` :
  decidable predicates are recognizable and co-recognizable, and closed under complement.
- `tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable` : Post's theorem.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Theorem 4.22.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Turing Encodable MetaMathlibExt.TM2Recursive

variable {α : Type*} [Primcodable α]

/-- **Decidability by multi-stack machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is decidable by a multi-stack machine when there is a function
$f : \mathbb{N} \to \mathbb{N}$ computed by a multi-stack Turing machine, with input and output
numbers written in binary, such that for every $a \in \alpha$, $f(\mathrm{encode}(a)) = 1$ if and
only if $p(a)$. -/
def TM2Decidable (p : α → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Nonempty (TM2Computable encodeNat encodeNat f) ∧ ∀ a, f (encode a) = 1 ↔ p a

/-- **Recognizability by multi-stack machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is recognizable by a multi-stack machine when there are a multi-stack
Turing machine $M$ and an identification of its input alphabet with the Booleans such that for
every $a \in \alpha$, $p(a)$ holds if and only if $M$ halts when started on the binary word of
$\mathrm{encode}(a)$. -/
def TM2Recognizable (p : α → Prop) : Prop :=
  ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
    ∀ a, p a ↔ TM2HaltsOn tm ((encodeNat (encode a)).map e.symm)

/-- **Co-recognizability by multi-stack machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is co-recognizable by a multi-stack machine when its complement
$\neg p$ is recognizable by a multi-stack machine. -/
def TM2CoRecognizable (p : α → Prop) : Prop := TM2Recognizable fun a ↦ ¬p a

/-! ### Bridges to Mathlib -/

/-- **Multi-stack decidable predicates are exactly the computable predicates.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is decidable by a multi-stack machine if and
only if it is computable, that is, $p$ is decidable and its Boolean characteristic function
$\alpha \to \mathrm{Bool}$ is computable. -/
theorem tm2Decidable_iff_computablePred {p : α → Prop} :
    TM2Decidable p ↔ ComputablePred p := by
  constructor
  · rintro ⟨f, ⟨hf⟩, hp⟩
    refine ComputablePred.computable_iff.mpr ⟨fun a ↦ f (encode a) == 1, ?_, ?_⟩
    · exact (Primrec.beq.to_comp.comp ((computable_of_tm2Computable hf).comp Computable.encode)
        (Computable.const 1))
    · funext a
      simp [← hp a]
  · intro hp
    obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hp
    let F : ℕ → ℕ := fun n ↦ ((decode (α := α) n).map fun a ↦ cond (g a) 1 0).getD 0
    have hF : Computable F :=
      Computable.option_getD (Computable.option_map Computable.decode
        ((Computable.cond (hg.comp Computable.snd) (Computable.const 1)
          (Computable.const 0)).to₂)) (Computable.const 0)
    obtain ⟨hT⟩ := tm2Computable_of_computable hF
    refine ⟨F, ⟨hT⟩, fun a ↦ ?_⟩
    cases h : g a <;> simp [F, encodek, h]

/-- **Multi-stack recognizable predicates are exactly the r.e. predicates.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is recognizable by a multi-stack machine if and
only if it is recursively enumerable, that is, the partial function on $\alpha$ that is defined,
with a trivial value, exactly where $p$ holds is partial recursive. -/
theorem tm2Recognizable_iff_rePred {p : α → Prop} : TM2Recognizable p ↔ REPred p := by
  constructor
  · rintro ⟨tm, e, hp⟩
    have : REPred fun a : α ↦ TM2HaltsOn tm ((encodeNat (encode a)).map e.symm) :=
      Partrec.comp (rePred_tm2HaltsOn tm e) Computable.encode
    exact REPred.of_eq this fun a ↦ (hp a).symm
  · intro hp
    let q : ℕ → Prop := fun n ↦ ∃ a, decode (α := α) n = some a ∧ p a
    have hq : REPred q := by
      have hb : Partrec fun n ↦ (Part.ofOption (decode (α := α) n)).bind fun a ↦
          Part.assert (p a) fun _ ↦ Part.some () :=
        Partrec.bind (Computable.ofOption Computable.decode) (hp.comp Computable.snd)
      refine Partrec.of_eq hb fun n ↦ ?_
      cases h : decode (α := α) n with
      | none =>
        simp only [Part.ofOption, Part.bind_none]
        refine Part.ext' ⟨fun h' ↦ h'.elim, fun ⟨⟨a, ha, _⟩, _⟩ ↦ ?_⟩ (fun h' ↦ h'.elim)
        rw [h] at ha
        cases ha
      | some a =>
        simp only [Part.ofOption, Part.bind_some]
        refine Part.ext' ⟨fun ⟨hpa, _⟩ ↦ ⟨⟨a, h, hpa⟩, trivial⟩,
          fun ⟨⟨a', ha', hpa'⟩, _⟩ ↦ ⟨?_, trivial⟩⟩ (fun _ _ ↦ rfl)
        rw [h, Option.some.injEq] at ha'
        exact ha' ▸ hpa'
    obtain ⟨tm, e, h⟩ := exists_tm2HaltsOn_iff_of_rePred hq
    refine ⟨tm, e, fun a ↦ ?_⟩
    rw [← h]
    simp [q, encodek]

/-- **Multi-stack co-recognizable predicates are exactly the co-r.e. predicates.** Let $\alpha$ be
a primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). A predicate $p$ on $\alpha$ is co-recognizable by a multi-stack machine if
and only if its complement $\neg p$ is recursively enumerable, that is, the partial function on
$\alpha$ that is defined, with a trivial value, exactly where $\neg p$ holds is partial
recursive. -/
theorem tm2CoRecognizable_iff_rePred_not {p : α → Prop} :
    TM2CoRecognizable p ↔ REPred fun a ↦ ¬p a :=
  tm2Recognizable_iff_rePred

/-! ### Decidable predicates -/

/-- **Decidable predicates are recognizable by multi-stack machines.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-stack machine, then
$p$ is recognizable by a multi-stack machine. -/
theorem TM2Decidable.tm2Recognizable {p : α → Prop} (h : TM2Decidable p) : TM2Recognizable p :=
  tm2Recognizable_iff_rePred.mpr (tm2Decidable_iff_computablePred.mp h).to_re

/-- **Decidability by multi-stack machines is closed under complement.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-stack machine, then
so is its complement $\neg p$. -/
theorem TM2Decidable.not {p : α → Prop} (h : TM2Decidable p) : TM2Decidable fun a ↦ ¬p a :=
  tm2Decidable_iff_computablePred.mpr (tm2Decidable_iff_computablePred.mp h).not

/-- **Decidable predicates are co-recognizable by multi-stack machines.** Let $\alpha$ be a
primcodable type (it has an encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is
primitive recursive). If a predicate $p$ on $\alpha$ is decidable by a multi-stack machine, then
$p$ is co-recognizable by a multi-stack machine, that is, its complement $\neg p$ is recognizable
by a multi-stack machine. -/
theorem TM2Decidable.tm2CoRecognizable {p : α → Prop} (h : TM2Decidable p) :
    TM2CoRecognizable p :=
  h.not.tm2Recognizable

/-- **Post's theorem for multi-stack machines.** Let $\alpha$ be a primcodable type (it has an
encoding $\mathrm{encode} : \alpha \to \mathbb{N}$ whose decoding is primitive recursive). A
predicate $p$ on $\alpha$ is decidable by a multi-stack machine if and only if it is both
recognizable and co-recognizable by a multi-stack machine. -/
theorem tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable {p : α → Prop} :
    TM2Decidable p ↔ TM2Recognizable p ∧ TM2CoRecognizable p := by
  rw [tm2Decidable_iff_computablePred, tm2CoRecognizable_iff_rePred_not,
    tm2Recognizable_iff_rePred]
  exact ComputablePred.computable_iff_re_compl_re'

end Cslib.Decidability
