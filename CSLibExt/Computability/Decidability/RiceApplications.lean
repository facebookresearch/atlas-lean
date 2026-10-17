/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Emptiness and equivalence of programs are undecidable
-/
module

public import CSLibExt.Computability.Decidability.Undecidable

/-!
# Emptiness and equivalence of programs are undecidable

Two classical applications of Rice's theorem and mapping reductions, for partial recursive codes
and decision by multi-stack machines (`FinTM2`):

* **Emptiness** (Sipser's `E_TM`): whether a code is defined nowhere is undecidable
  (`not_tm2Decidable_empty`). It is co-recognizable, since a dovetailed search finds an input
  and step bound at which the code halts (`tm2CoRecognizable_empty`), hence not recognizable
  (`not_tm2Recognizable_empty`).
* **Equivalence** (Sipser's `EQ_TM`): whether two codes recognize the same language (halt on the
  same inputs) is neither recognizable (`not_tm2Recognizable_eq`, by reducing emptiness to it) nor
  co-recognizable (`not_tm2CoRecognizable_eq`, by reducing halting on `0` to it).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Theorems 5.2, 5.4 and 5.30.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability
open Nat.Partrec (Code)

/-- `E`: the codes defined on no input. -/
def EmptyCode (c : Code) : Prop := ∀ n, ¬(c.eval n).Dom

/-- **Emptiness is undecidable** (Rice: the identity is defined, the empty function is not). -/
theorem not_tm2Decidable_empty : ¬TM2Decidable EmptyCode := by
  intro h
  have : (fun n : ℕ ↦ Part.some n) ∈ {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} :=
    rice_tm2 {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} h (f := fun _ ↦ Part.none) Nat.Partrec.none
      Nat.Partrec.some (fun n h ↦ h)
  exact this 0 trivial

/-- The complement of emptiness is recognizable: search for an input `n` and a step bound
`k` at which `evaln k c n` halts. -/
theorem tm2Recognizable_not_empty : TM2Recognizable fun c ↦ ¬EmptyCode c := by
  refine tm2Recognizable_iff_rePred.mpr ?_
  let D : Code → ℕ → Bool := fun c m ↦ (Code.evaln m.unpair.2 c m.unpair.1).isSome
  have hD : Primrec₂ D :=
    Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
  have hp : Partrec fun c ↦ Nat.rfind fun m ↦ Part.some (D c m) :=
    Partrec.rfind hD.to_comp.partrec₂
  refine hp.dom_re.of_eq fun c ↦ ?_
  refine Nat.rfind_dom.trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true, EmptyCode, not_forall,
    not_not]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hm.symm
    exact ⟨m.unpair.1, Part.dom_iff_mem.mpr ⟨x, Code.evaln_complete.mpr ⟨_, hx⟩⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hn
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    refine ⟨Nat.pair n k, (Option.isSome_iff_exists.mpr ⟨x, ?_⟩).symm⟩
    simpa [Nat.unpair_pair] using hk

/-- Emptiness is co-recognizable. -/
theorem tm2CoRecognizable_empty : TM2CoRecognizable EmptyCode := tm2Recognizable_not_empty

/-- **Emptiness is not recognizable**: it would then be decidable, by Post's theorem. -/
theorem not_tm2Recognizable_empty : ¬TM2Recognizable EmptyCode := fun h ↦
  not_tm2Decidable_empty
    (tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable.mpr ⟨h, tm2CoRecognizable_empty⟩)

/-! ### Equivalence -/

/-- `EQ`: pairs of codes recognizing the same language, that is, halting on the same inputs. -/
def EqCode (p : Code × Code) : Prop := p.1.eval.Dom = p.2.eval.Dom

theorem eqCode_iff {c₁ c₂ : Code} : EqCode (c₁, c₂) ↔ ∀ n, (c₁.eval n).Dom ↔ (c₂.eval n).Dom :=
  Set.ext_iff

/-- A code defined nowhere. -/
theorem exists_code_empty : ∃ e : Code, e.eval = fun _ ↦ Part.none :=
  Code.exists_code.mp Nat.Partrec.none

/-- Emptiness reduces to equivalence: compare with a code defined nowhere. -/
theorem manyOneReducible_empty_eq : ManyOneReducible EmptyCode EqCode := by
  obtain ⟨e, he⟩ := exists_code_empty
  refine ⟨fun c ↦ (c, e), Computable.pair Computable.id (Computable.const e), fun c ↦ ?_⟩
  rw [eqCode_iff, he]
  exact ⟨fun h n ↦ ⟨fun hn ↦ h n hn, fun hn ↦ hn.elim⟩, fun h n hn ↦ (h n).mp hn⟩

/-- **Equivalence is not recognizable.** -/
theorem not_tm2Recognizable_eq : ¬TM2Recognizable EqCode := fun h ↦
  not_tm2Recognizable_empty (tm2Recognizable_of_manyOneReducible manyOneReducible_empty_eq h)

/-- The code that runs `c` on `0` and then outputs `0`, whatever its input. -/
def haltsOnZeroCode (c : Code) : Code :=
  Code.comp (Code.const 0) (Code.comp c (Code.const 0))

theorem eval_haltsOnZeroCode (c : Code) (n : ℕ) :
    (haltsOnZeroCode c).eval n = (c.eval 0).map fun _ ↦ 0 := by
  have hk : (Code.const 0).eval = fun _ ↦ Part.some 0 := funext (Code.eval_const 0)
  simp only [haltsOnZeroCode, Code.eval, hk, Part.bind_eq_bind]
  exact (congrArg (fun x : Part ℕ ↦ x.bind fun _ ↦ Part.some 0) (Part.bind_some 0 c.eval)).trans
    (Part.bind_some_eq_map _ _)

/-- Halting on `0` reduces to equivalence: `c` halts on `0` iff `haltsOnZeroCode c` halts on
every input, like `Code.const 0`. -/
theorem manyOneReducible_halting_eq :
    ManyOneReducible (fun c : Code ↦ (c.eval 0).Dom) EqCode := by
  refine ⟨fun c ↦ (haltsOnZeroCode c, Code.const 0), Computable.pair ?_ (Computable.const _),
    fun c ↦ ?_⟩
  · exact (Code.primrec₂_comp.comp (Primrec.const _) (Code.primrec₂_comp.comp Primrec.id
      (Primrec.const _))).to_comp
  · rw [eqCode_iff]
    simp only [eval_haltsOnZeroCode, Code.eval_const, Part.map_Dom, Part.some_dom, iff_true]
    exact ⟨fun h _ ↦ h, fun h ↦ h 0⟩

/-- **Equivalence is not co-recognizable**: the complement of halting on `0` would reduce to
the complement of equivalence. -/
theorem not_tm2CoRecognizable_eq : ¬TM2CoRecognizable EqCode := by
  intro h
  obtain ⟨f, hf, hpq⟩ := manyOneReducible_halting_eq
  have hred : ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) fun p ↦ ¬EqCode p :=
    ⟨f, hf, fun c ↦ not_congr (hpq c)⟩
  exact not_tm2CoRecognizable_halting 0 (tm2Recognizable_of_manyOneReducible hred h)

end Cslib.Decidability
