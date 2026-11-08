/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finiteness of the language of a program is neither recognizable nor co-recognizable
-/
module

public import CSLibExt.Computability.Decidability.Totality

/-!
# Finiteness of the language of a program is neither recognizable nor co-recognizable

`FiniteCode c`: the partial recursive code `c` halts on finitely many inputs. Decision is by
`FinTM2`. Both reductions use the step-bounded evaluator `Nat.Partrec.Code.evaln` on input `0`:

* Halting on `0` reduces to finiteness (`manyOneReducible_halting_finite`): the code computing
  `untilHaltsFun c` (from `Totality.lean`) halts on `k` iff `c` has not halted on `0` within `k`
  steps (`untilHaltsFun_dom`). Its domain is a finite initial segment if `c` halts on `0`, and
  all of `ℕ` otherwise. So finiteness is not co-recognizable (`not_tm2CoRecognizable_finite`).
* Non-halting on `0` reduces to finiteness (`manyOneReducible_not_halting_finite`): the code
  computing `haltsWithinFun c` halts on `k` iff `c` halts on `0` within `k` steps
  (`haltsWithinFun_dom`). Its domain is cofinite if `c` halts on `0`, and empty otherwise. So
  finiteness is not recognizable (`not_tm2Recognizable_finite`).

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV (`Fin`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability
open Nat.Partrec (Code)

/-- `FIN`: the codes with a finite domain. -/
def FiniteCode (c : Code) : Prop := c.eval.Dom.Finite

/-- `untilHaltsFun c` is defined exactly below the first step bound at which `c` halts on `0`. -/
theorem untilHaltsFun_dom {c : Code} {k : ℕ} :
    (untilHaltsFun c k).Dom ↔ (Code.evaln k c 0).isSome = false := by
  unfold untilHaltsFun
  cases (Code.evaln k c 0).isSome <;> simp

/-- **Halting reduces to finiteness.** -/
theorem manyOneReducible_halting_finite :
    ManyOneReducible (fun c : Code ↦ (c.eval 0).Dom) FiniteCode := by
  obtain ⟨g, hg, hgeval⟩ := MetaMathlibExt.exists_computable_code partrec₂_untilHaltsFun
  refine ⟨g, hg, fun c ↦ ?_⟩
  have hdom : (g c).eval.Dom = {k | (Code.evaln k c 0).isSome = false} := by
    ext k
    exact (congrArg Part.Dom (hgeval c k)).to_iff.trans untilHaltsFun_dom
  simp only [FiniteCode, hdom]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    refine (Set.finite_lt_nat k).subset fun j hj ↦ ?_
    by_contra hjk
    have hle : k ≤ j := Nat.le_of_not_lt hjk
    have := Code.evaln_mono hle hk
    simp_all
  · intro hfin
    by_contra hd
    refine Set.infinite_univ (hfin.subset fun k _ ↦ ?_)
    cases he : Code.evaln k c 0 with
    | none => simp [he]
    | some x => exact absurd (Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound he⟩) hd

/-- **Finiteness is not co-recognizable.** -/
theorem not_tm2CoRecognizable_finite : ¬TM2CoRecognizable FiniteCode := by
  intro h
  obtain ⟨f, hf, hpq⟩ := manyOneReducible_halting_finite
  exact not_tm2CoRecognizable_halting 0
    (tm2Recognizable_of_manyOneReducible ⟨f, hf, fun c ↦ not_congr (hpq c)⟩ h)

/-- On input `k`: output `0` if `c` halts on `0` within `k` steps, and loop otherwise. -/
def haltsWithinFun (c : Code) (k : ℕ) : Part ℕ :=
  bif (Code.evaln k c 0).isSome then Part.some 0 else Part.none

/-- `haltsWithinFun c` is defined exactly from the first step bound at which `c` halts on `0`. -/
theorem haltsWithinFun_dom {c : Code} {k : ℕ} :
    (haltsWithinFun c k).Dom ↔ (Code.evaln k c 0).isSome = true := by
  unfold haltsWithinFun
  cases (Code.evaln k c 0).isSome <;> simp

theorem partrec₂_haltsWithinFun : Partrec₂ haltsWithinFun :=
  Partrec.cond (Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
    (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const 0)))).to_comp (Partrec.const' _)
    Partrec.none

/-- **Non-halting reduces to finiteness.** -/
theorem manyOneReducible_not_halting_finite :
    ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) FiniteCode := by
  obtain ⟨g, hg, hgeval⟩ := MetaMathlibExt.exists_computable_code partrec₂_haltsWithinFun
  refine ⟨g, hg, fun c ↦ ?_⟩
  have hdom : (g c).eval.Dom = {k | (Code.evaln k c 0).isSome = true} := by
    ext k
    exact (congrArg Part.Dom (hgeval c k)).to_iff.trans haltsWithinFun_dom
  simp only [FiniteCode, hdom]
  constructor
  · intro hd
    convert Set.finite_empty
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    exact hd (Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound hx⟩)
  · intro hfin hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    refine Set.infinite_of_not_bddAbove (fun ⟨b, hb⟩ ↦ ?_) hfin
    have hmem : k + b + 1 ∈ {k | (Code.evaln k c 0).isSome = true} :=
      Option.isSome_iff_exists.mpr ⟨x, Code.evaln_mono (by omega) hk⟩
    have := hb hmem
    omega

/-- **Finiteness is not recognizable.** -/
theorem not_tm2Recognizable_finite : ¬TM2Recognizable FiniteCode := fun h ↦
  not_tm2CoRecognizable_halting 0
    (tm2Recognizable_of_manyOneReducible manyOneReducible_not_halting_finite h)

/-- Finiteness is undecidable. -/
theorem not_tm2Decidable_finite : ¬TM2Decidable FiniteCode := fun h ↦
  not_tm2Recognizable_finite h.tm2Recognizable

end Cslib.Decidability
