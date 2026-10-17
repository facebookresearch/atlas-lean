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

/-- `p` is **decidable** by a multi-stack machine: some `FinTM2` computes a total function
`f : ℕ → ℕ` under `encodeNat` with `f (encode a) = 1` exactly when `p a`. -/
def TM2Decidable (p : α → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Nonempty (TM2Computable encodeNat encodeNat f) ∧ ∀ a, f (encode a) = 1 ↔ p a

/-- `p` is **recognizable** by a multi-stack machine: some `FinTM2` halts on the input word
`encodeNat (encode a)` exactly when `p a`. -/
def TM2Recognizable (p : α → Prop) : Prop :=
  ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
    ∀ a, p a ↔ TM2HaltsOn tm ((encodeNat (encode a)).map e.symm)

/-- `p` is **co-recognizable**: its complement is recognizable. -/
def TM2CoRecognizable (p : α → Prop) : Prop := TM2Recognizable fun a ↦ ¬p a

/-! ### Bridges to Mathlib -/

/-- Decidability by a multi-stack machine is Mathlib's `ComputablePred`. -/
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

/-- Recognizability by a multi-stack machine is Mathlib's `REPred`. -/
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

/-- Co-recognizability by a multi-stack machine is `REPred` of the complement. -/
theorem tm2CoRecognizable_iff_rePred_not {p : α → Prop} :
    TM2CoRecognizable p ↔ REPred fun a ↦ ¬p a :=
  tm2Recognizable_iff_rePred

/-! ### Decidable predicates -/

/-- A decidable predicate is recognizable. -/
theorem TM2Decidable.tm2Recognizable {p : α → Prop} (h : TM2Decidable p) : TM2Recognizable p :=
  tm2Recognizable_iff_rePred.mpr (tm2Decidable_iff_computablePred.mp h).to_re

/-- The complement of a decidable predicate is decidable. -/
theorem TM2Decidable.not {p : α → Prop} (h : TM2Decidable p) : TM2Decidable fun a ↦ ¬p a :=
  tm2Decidable_iff_computablePred.mpr (tm2Decidable_iff_computablePred.mp h).not

/-- A decidable predicate is co-recognizable. -/
theorem TM2Decidable.tm2CoRecognizable {p : α → Prop} (h : TM2Decidable p) :
    TM2CoRecognizable p :=
  h.not.tm2Recognizable

/-- **Post's theorem** for multi-stack machines: a predicate is decidable iff it is recognizable
and co-recognizable. -/
theorem tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable {p : α → Prop} :
    TM2Decidable p ↔ TM2Recognizable p ∧ TM2CoRecognizable p := by
  rw [tm2Decidable_iff_computablePred, tm2CoRecognizable_iff_rePred_not,
    tm2Recognizable_iff_rePred]
  exact ComputablePred.computable_iff_re_compl_re'

end Cslib.Decidability
