/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Totality of programs is neither recognizable nor co-recognizable
-/
module

public import CSLibExt.Computability.Decidability.RiceApplications
public import MathlibExt.Computability.PartrecCode

/-!
# Totality of programs is neither recognizable nor co-recognizable

`TotalCode c`: the partial recursive code `c` halts on every input. Decision is by `FinTM2`.

* Halting on `0` reduces to totality (`manyOneReducible_halting_total`): `haltsOnZeroCode c`
  ignores its input, runs `c` on `0` and outputs `0`. Since the complement of halting is not
  recognizable, totality is not co-recognizable (`not_tm2CoRecognizable_total`).
* Non-halting on `0` reduces to totality as well (`manyOneReducible_not_halting_total`): on input
  `k`, the code computing `untilHaltsFun c` loops if `c` halts on `0` within `k` steps
  (`Nat.Partrec.Code.evaln`), and outputs `0` otherwise. It is total exactly when `c` never
  halts on `0`. So totality is not recognizable either (`not_tm2Recognizable_total`).

The family of codes for `untilHaltsFun` is built with the parametrized s-m-n theorem
`MetaMathlibExt.exists_computable_code`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV (`Tot`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability
open Nat.Partrec (Code)

/-- **Total codes.** A code $c$ of a partial recursive function is total when it halts on every
input: writing $\varphi_c$ for the partial function on $\mathbb{N}$ that $c$ computes,
$\varphi_c(n)$ is defined for every $n \in \mathbb{N}$. -/
def TotalCode (c : Code) : Prop := ∀ n, (c.eval n).Dom

/-- **Halting on zero reduces to totality.** Writing $\varphi_c$ for the partial function on
$\mathbb{N}$ computed by a code $c$ of a partial recursive function, the set of codes $c$ with
$\varphi_c(0)$ defined is many-one reducible to the set of total codes, the codes that halt on
every input: there is a computable function $f$ from codes to codes such that, for every code
$c$, $\varphi_c(0)$ is defined if and only if $f(c)$ is total. -/
theorem manyOneReducible_halting_total :
    ManyOneReducible (fun c : Code ↦ (c.eval 0).Dom) TotalCode := by
  refine ⟨haltsOnZeroCode, ?_, fun c ↦ ?_⟩
  · exact (Code.primrec₂_comp.comp (Primrec.const _) (Code.primrec₂_comp.comp Primrec.id
      (Primrec.const _))).to_comp
  · simp only [TotalCode, eval_haltsOnZeroCode, Part.map_Dom]
    exact ⟨fun h _ ↦ h, fun h ↦ h 0⟩

/-- **Totality is not co-recognizable.** The set of total codes, the codes of partial recursive
functions that halt on every input, is not co-recognizable by multi-stack machines: no
multi-stack machine halts on the binary encoding of a code $c$ exactly when $c$ is not total. -/
theorem not_tm2CoRecognizable_total : ¬TM2CoRecognizable TotalCode := by
  intro h
  obtain ⟨f, hf, hpq⟩ := manyOneReducible_halting_total
  exact not_tm2CoRecognizable_halting 0
    (tm2Recognizable_of_manyOneReducible ⟨f, hf, fun c ↦ not_congr (hpq c)⟩ h)

/-- **Diverging once a code halts on zero.** For a code $c$ of a partial recursive function, this
is the partial function $\mathbb{N} \to \mathbb{N}$ that on input $k$ is undefined if $c$ halts
on input $0$ within $k$ steps of bounded evaluation, and equals $0$ otherwise. -/
def untilHaltsFun (c : Code) (k : ℕ) : Part ℕ :=
  bif (Code.evaln k c 0).isSome then Part.none else Part.some 0

theorem partrec₂_untilHaltsFun : Partrec₂ untilHaltsFun :=
  Partrec.cond (Primrec.option_isSome.comp (Code.primrec_evaln.comp (Primrec.pair
    (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const 0)))).to_comp Partrec.none
    (Partrec.const' _)

/-- **Non-halting on zero reduces to totality.** Writing $\varphi_c$ for the partial function on
$\mathbb{N}$ computed by a code $c$ of a partial recursive function, the set of codes $c$ with
$\varphi_c(0)$ undefined is many-one reducible to the set of total codes, the codes that halt on
every input: there is a computable function $f$ from codes to codes such that, for every code
$c$, $\varphi_c(0)$ is undefined if and only if $f(c)$ is total. -/
theorem manyOneReducible_not_halting_total :
    ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) TotalCode := by
  obtain ⟨g, hg, hgeval⟩ := MetaMathlibExt.exists_computable_code partrec₂_untilHaltsFun
  refine ⟨g, hg, fun c ↦ ?_⟩
  simp only [TotalCode, hgeval, untilHaltsFun]
  constructor
  · intro h k
    cases he : Code.evaln k c 0 with
    | none => trivial
    | some x => exact absurd (Part.dom_iff_mem.mpr ⟨x, Code.evaln_sound he⟩) h
  · intro h hd
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    have := h k
    rw [show Code.evaln k c 0 = some x from hk] at this
    exact this

/-- **Totality is not recognizable.** The set of total codes, the codes of partial recursive
functions that halt on every input, is not recognizable by multi-stack machines: no multi-stack
machine halts on the binary encoding of a code $c$ exactly when $c$ is total. -/
theorem not_tm2Recognizable_total : ¬TM2Recognizable TotalCode := fun h ↦
  not_tm2CoRecognizable_halting 0
    (tm2Recognizable_of_manyOneReducible manyOneReducible_not_halting_total h)

/-- **Totality is undecidable.** The set of total codes, the codes of partial recursive functions
that halt on every input, is not decidable by multi-stack machines: no multi-stack machine
computes a total function $f : \mathbb{N} \to \mathbb{N}$ that takes the value $1$ at the number
encoding a code $c$ exactly when $c$ is total. -/
theorem not_tm2Decidable_total : ¬TM2Decidable TotalCode := fun h ↦
  not_tm2Recognizable_total h.tm2Recognizable

end Cslib.Decidability
