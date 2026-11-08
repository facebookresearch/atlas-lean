/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recognizable languages are the enumerable ones
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import Mathlib.Computability.PartrecCode

/-!
# Recognizable languages are the enumerable ones

Sipser's Theorem 3.21: a language is Turing-recognizable iff some enumerator enumerates it. An
*enumerator* is modelled as a computable function `e : ℕ → Option α`: at step `n` it prints
`a` when `e n = some a`, and prints nothing when `e n = none`. It enumerates `p` when the
printed elements are exactly those satisfying `p` (`Enumerates`). Repetitions are allowed, and
the empty language is enumerated by `fun _ ↦ none`.

* From a recognizer, step `⟨x, k⟩` prints the element encoded by `x` if the recognizer, run as a
  code for `k` steps (`Nat.Partrec.Code.evaln`), accepts it.
* From an enumerator, recognize `a` by searching for a step that prints `a`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 3.21.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Encodable
open Nat.Partrec (Code)

variable {α : Type*} [Primcodable α]

/-- The enumerator `e` prints exactly the elements satisfying `p`. -/
def Enumerates (e : ℕ → Option α) (p : α → Prop) : Prop := ∀ a, p a ↔ ∃ n, e n = some a

/-- **Recognizable languages are enumerable.** -/
theorem TM2Recognizable.exists_enumerator {p : α → Prop} (h : TM2Recognizable p) :
    ∃ e : ℕ → Option α, Computable e ∧ Enumerates e p := by
  have hre : REPred p := tm2Recognizable_iff_rePred.mp h
  -- a code semi-deciding `p` on encodings
  have hG : Partrec fun x : ℕ ↦ (Part.ofOption (decode₂ α x)).bind fun a ↦
      (Part.assert (p a) fun _ ↦ Part.some ()).map fun _ ↦ (0 : ℕ) :=
    Partrec.bind (Computable.ofOption Primrec.decode₂.to_comp)
      ((hre.comp Computable.snd).map (Computable.const 0).to₂)
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG)
  have hspec : ∀ a : α, (c.eval (encode a)).Dom ↔ p a := fun a ↦ by
    rw [hc]
    simp [Part.assert]
  refine ⟨fun n ↦ bif (Code.evaln n.unpair.2 c n.unpair.1).isSome then decode₂ α n.unpair.1
      else none, ?_, fun a ↦ ⟨fun ha ↦ ?_, ?_⟩⟩
  · exact (Primrec.cond (Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.const c))
      (Primrec.fst.comp Primrec.unpair))))
      (Primrec.decode₂.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const none)).to_comp
  · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hspec a).mpr ha)
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
    refine ⟨Nat.pair (encode a) k, ?_⟩
    simp only [Nat.unpair_pair, show Code.evaln k c (encode a) = some v from hk, Option.isSome_some,
      Bool.cond_true, encodek₂]
  · rintro ⟨n, hn⟩
    cases hs : (Code.evaln n.unpair.2 c n.unpair.1).isSome
    · simp [hs] at hn
    · simp only [hs, Bool.cond_true, decode₂_eq_some] at hn
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
      refine (hspec a).mp (Part.dom_iff_mem.mpr ⟨w, ?_⟩)
      rw [hn]
      exact Code.evaln_sound hw

/-- **Enumerable languages are recognizable.** -/
theorem tm2Recognizable_of_enumerates {p : α → Prop} {e : ℕ → Option α} (he : Computable e)
    (hep : Enumerates e p) : TM2Recognizable p := by
  classical
  refine tm2Recognizable_iff_rePred.mpr ?_
  have htest : Computable₂ fun (a : α) (n : ℕ) ↦ decide (e n = some a) :=
    (Primrec.eq.decide.to_comp).comp (he.comp Computable.snd)
      (Computable.option_some.comp Computable.fst)
  have hsearch : Partrec fun a : α ↦ Nat.rfind fun n ↦ Part.some (decide (e n = some a)) :=
    Partrec.rfind htest.partrec₂
  refine hsearch.dom_re.of_eq fun a ↦ (Nat.rfind_dom'.trans ?_).trans (hep a).symm
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, of_decide_eq_true hn.symm⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, (decide_eq_true hn).symm⟩⟩

/-- **Sipser, Theorem 3.21**: a language is recognizable iff some enumerator enumerates it. -/
theorem tm2Recognizable_iff_exists_enumerator {p : α → Prop} :
    TM2Recognizable p ↔ ∃ e : ℕ → Option α, Computable e ∧ Enumerates e p :=
  ⟨TM2Recognizable.exists_enumerator, fun ⟨_, he, hep⟩ ↦ tm2Recognizable_of_enumerates he hep⟩

end Cslib.Decidability
