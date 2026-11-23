/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal programs are not recognizable
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import Mathlib.Computability.PartrecCode

/-!
# Minimal programs are not recognizable

The *description* of a partial recursive code is its encoding written in binary, and
`descLength c` is its length (`Nat.size (encode c)`). A code is *minimal* (`MinimalCode`) when
no code with a shorter description recognizes the same language, that is, halts on the same
inputs. Several codes may tie for the shortest description of a language, and all of them are
minimal. Sipser's Theorem 6.7 says the minimal machines are not Turing-recognizable. The proof
uses the recursion theorem (`Nat.Partrec.Code.fixed_point₂`):

* There are minimal codes of arbitrarily large encoding (`exists_minimalCode_gt`): the languages
  `{n}` are pairwise distinct, and each has a minimal code.
* If `MinimalCode` were recognizable, some code `c` could find, by a dovetailed search, a minimal
  code `D` with encoding at least `2 ^ encode c`, and then behave as `D`. Then `c` recognizes the
  same language as `D` with a strictly shorter description, contradicting the minimality of `D`
  (`not_tm2Recognizable_minimalCode`).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Theorem 6.7.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Encodable Denumerable
open Nat.Partrec (Code)

/-- **Description length of a code.** For a code $c$ of a partial recursive function, the
description length of $c$ is the number of binary digits of the encoding of $c$ as a natural
number, that is, the least $k$ such that this encoding is less than $2^k$ (so it is $0$ when the
encoding is $0$). -/
def descLength (c : Code) : ℕ := Nat.size (encode c)

/-- **Minimal codes.** A code $c$ of a partial recursive function is minimal when no code with a
shorter description has the same domain: for every code $d$ whose description length is strictly
less than that of $c$, the domain of $d$ (the set of inputs on which its evaluation is defined)
differs from the domain of $c$. The set of minimal codes is denoted $\mathrm{MIN}$. -/
def MinimalCode (c : Code) : Prop :=
  ∀ d : Code, descLength d < descLength c → d.eval.Dom ≠ c.eval.Dom

/-- **Codes with singleton domain.** For every natural number $n$ there is a code $c$ of a partial
recursive function whose evaluation is defined exactly at $n$, that is, the domain of the partial
function computed by $c$ is $\{n\}$. -/
theorem exists_code_dom_singleton (n : ℕ) : ∃ c : Code, c.eval.Dom = {n} := by
  have : Partrec fun x : ℕ ↦ cond (decide (x = n)) (Part.some 0) Part.none :=
    Partrec.cond (Primrec.eq.comp Primrec.id (Primrec.const n)).decide.to_comp
      (Partrec.const' _) Partrec.none
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 this)
  refine ⟨c, Set.ext fun x ↦ ?_⟩
  change (c.eval x).Dom ↔ x = n
  rw [hc]
  by_cases hx : x = n <;> simp [hx]

/-- **Every language of a code has a minimal code.** For every code $c$ of a partial recursive
function there is a minimal code $D$ whose domain equals the domain of $c$, where the domain of a
code is the set of inputs on which its evaluation is defined. -/
theorem exists_minimalCode_dom (c : Code) :
    ∃ D : Code, MinimalCode D ∧ D.eval.Dom = c.eval.Dom := by
  classical
  have hex : ∃ k, ∃ D : Code, encode D = k ∧ D.eval.Dom = c.eval.Dom := ⟨_, c, rfl, rfl⟩
  obtain ⟨D, hDk, hD⟩ := Nat.find_spec hex
  refine ⟨D, fun d hd hdD ↦ ?_, hD⟩
  have hlt : encode d < encode D :=
    lt_of_not_ge fun hle ↦ absurd (Nat.size_le_size hle) (not_le.mpr hd)
  exact Nat.find_min hex (hDk ▸ hlt) ⟨d, rfl, hdD.trans hD⟩

/-- **Minimal codes are unbounded.** For every natural number $N$ there is a minimal code $D$ of a
partial recursive function whose encoding as a natural number is greater than $N$. -/
theorem exists_minimalCode_gt (N : ℕ) : ∃ D : Code, MinimalCode D ∧ N < encode D := by
  choose c hc using exists_code_dom_singleton
  choose D hDmin hDdom using fun n ↦ exists_minimalCode_dom (c n)
  have hinj : Function.Injective fun n ↦ encode (D n) := fun m n h ↦ by
    have hmn := congrArg (fun e : Code ↦ e.eval.Dom) (encode_injective h)
    simp only [hDdom, hc] at hmn
    exact Set.singleton_eq_singleton_iff.mp hmn
  by_contra H
  push Not at H
  exact Set.infinite_range_of_injective hinj
    ((Set.finite_le_nat N).subset (Set.range_subset_iff.mpr fun n ↦ H _ (hDmin n)))

/-- **Minimal codes are not recognizable.** The set $\mathrm{MIN}$ of minimal codes of partial
recursive functions is not recognizable by a multi-stack Turing machine: there is no finite
multi-stack machine that, for every code $c$, halts on the binary encoding of the natural-number
encoding of $c$ exactly when $c$ is minimal.

Source: M. Sipser, Introduction to the Theory of Computation, 3rd ed., Theorem 6.7. -/
theorem not_tm2Recognizable_minimalCode : ¬TM2Recognizable MinimalCode := by
  intro h
  have hre : REPred MinimalCode := tm2Recognizable_iff_rePred.mp h
  -- a code `e` semi-deciding `MinimalCode` on encodings
  have hG : Partrec fun n : ℕ ↦ (Part.ofOption (decode (α := Code) n)).bind fun D ↦
      (Part.assert (MinimalCode D) fun _ ↦ Part.some ()).map fun _ ↦ (0 : ℕ) :=
    Partrec.bind (Computable.ofOption Computable.decode)
      ((hre.comp Computable.snd).map (Computable.const 0).to₂)
  obtain ⟨e, he⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hG)
  have hspec : ∀ d : ℕ, (e.eval d).Dom ↔ MinimalCode (ofNat Code d) := fun d ↦ by
    rw [he, ← encode_ofNat (α := Code) d]
    simp [Part.assert]
  -- search for a minimal code with a larger encoding, by dovetailing over `⟨d, k⟩`
  let test : Code → ℕ → Bool := fun c m ↦
    decide (2 ^ encode c ≤ m.unpair.1) && (Code.evaln m.unpair.2 e m.unpair.1).isSome
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have htest : Primrec₂ test :=
    Primrec.and.comp
      (Primrec.nat_le.comp (hpow.comp (Primrec.const 2) (Primrec.encode.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))).decide
      (Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.const e))
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))))
  let F : Code → ℕ →. ℕ := fun c x ↦
    (Nat.rfind fun m ↦ Part.some (test c m)).bind fun m ↦ (ofNat Code m.unpair.1).eval x
  have hF : Partrec₂ F :=
    Partrec.bind ((Partrec.rfind htest.to_comp.partrec₂).comp Computable.fst)
      (Code.eval_part.comp ((Computable.ofNat Code).comp
        (Computable.fst.comp (Computable.unpair.comp Computable.snd)))
        (Computable.snd.comp Computable.fst))
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hF
  -- the search succeeds
  obtain ⟨D, hD, hcD⟩ := exists_minimalCode_gt (2 ^ encode c)
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hspec (encode D)).mpr (by rwa [ofNat_encode]))
  obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
  have hdom : (Nat.rfind fun m ↦ Part.some (test c m)).Dom :=
    Nat.rfind_dom'.mpr ⟨Nat.pair (encode D) k, Part.mem_some_iff.mpr
      (show test c (Nat.pair (encode D) k) = true by
        simp only [test, Nat.unpair_pair, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hcD.le, Option.isSome_iff_exists.mpr ⟨v, hk⟩⟩).symm, fun _ ↦ trivial⟩
  set m := (Nat.rfind fun m ↦ Part.some (test c m)).get hdom
  have hm : test c m = true := by
    have := Nat.rfind_spec (Part.get_mem hdom)
    simpa using this
  simp only [test, Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨hlt, hsome⟩ := hm
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hsome
  have hmin : MinimalCode (ofNat Code m.unpair.1) :=
    (hspec _).mp (Part.dom_iff_mem.mpr ⟨w, Code.evaln_sound hw⟩)
  have heval : c.eval = (ofNat Code m.unpair.1).eval := by
    rw [hc]
    funext x
    simp only [F]
    rw [Part.eq_some_iff.mpr (Part.get_mem hdom), Part.bind_some]
  have hshort : descLength c < descLength (ofNat Code m.unpair.1) := by
    unfold descLength
    rw [encode_ofNat]
    exact lt_of_le_of_lt (Nat.size_le.mpr (Nat.lt_two_pow_self)) (Nat.lt_size.mpr hlt)
  exact hmin c hshort (congrArg PFun.Dom heval)

end Cslib.Decidability
