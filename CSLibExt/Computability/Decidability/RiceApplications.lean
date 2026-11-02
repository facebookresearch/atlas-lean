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

/-- **Codes with empty domain.** The set $E$ consists of the codes $c$ of partial recursive
functions on $\mathbb{N}$ that are defined on no input: for every $n \in \mathbb{N}$, the
function computed by $c$ is undefined at $n$. -/
def EmptyCode (c : Code) : Prop := ∀ n, ¬(c.eval n).Dom

/-- **Emptiness is undecidable.** The set $E$ of codes of partial recursive functions on
$\mathbb{N}$ that are defined on no input is not decidable by multi-stack machines.

By Rice's theorem: the identity function is defined, the empty function is not. -/
theorem not_tm2Decidable_empty : ¬TM2Decidable EmptyCode := by
  intro h
  have : (fun n : ℕ ↦ Part.some n) ∈ {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} :=
    rice_tm2 {f : ℕ →. ℕ | ∀ n, ¬(f n).Dom} h (f := fun _ ↦ Part.none) Nat.Partrec.none
      Nat.Partrec.some (fun n h ↦ h)
  exact this 0 trivial

/-- **Nonemptiness is recognizable.** The set of codes of partial recursive functions
$\mathbb{N} \to \mathbb{N}$ that are defined on at least one input is recognizable by
multi-stack machines: some multi-stack machine halts on the binary encoding of a code $c$ exactly
when the function coded by $c$ is defined on some input.

The machine searches for an input $n$ and a step bound $k$ such that the evaluation of $c$ on $n$
halts within $k$ steps. -/
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

/-- **Emptiness is co-recognizable.** The set of codes of partial recursive functions
$\mathbb{N} \to \mathbb{N}$ that are defined on no input is co-recognizable by multi-stack
machines: some multi-stack machine halts on the binary encoding of a code $c$ exactly when the
function coded by $c$ is defined on at least one input. -/
theorem tm2CoRecognizable_empty : TM2CoRecognizable EmptyCode := tm2Recognizable_not_empty

/-- **Emptiness is not recognizable.** The set $E$ of codes of partial recursive functions on
$\mathbb{N}$ that are defined on no input is not recognizable by multi-stack machines: no
multi-stack machine, started on the binary encoding of a code, halts exactly when the code is
in $E$.

Since $E$ is co-recognizable, it would otherwise be decidable, by Post's theorem. -/
theorem not_tm2Recognizable_empty : ¬TM2Recognizable EmptyCode := fun h ↦
  not_tm2Decidable_empty
    (tm2Decidable_iff_tm2Recognizable_and_tm2CoRecognizable.mpr ⟨h, tm2CoRecognizable_empty⟩)

/-! ### Equivalence -/

/-- **Equivalent codes.** The set $EQ$ consists of the pairs $(c_1, c_2)$ of codes of partial
recursive functions on $\mathbb{N}$ that recognize the same language, that is, whose computed
functions have the same domain: for every $n \in \mathbb{N}$, the function computed by $c_1$ is
defined at $n$ if and only if the function computed by $c_2$ is. -/
def EqCode (p : Code × Code) : Prop := p.1.eval.Dom = p.2.eval.Dom

theorem eqCode_iff {c₁ c₂ : Code} : EqCode (c₁, c₂) ↔ ∀ n, (c₁.eval n).Dom ↔ (c₂.eval n).Dom :=
  Set.ext_iff

/-- **A code defined nowhere.** There is a code $e$ of a partial recursive function on
$\mathbb{N}$ whose computed function is the empty partial function, undefined at every input. -/
theorem exists_code_empty : ∃ e : Code, e.eval = fun _ ↦ Part.none :=
  Code.exists_code.mp Nat.Partrec.none

/-- **Emptiness reduces to equivalence.** The set $E$ of codes of partial recursive functions
defined on no input is many-one reducible to the set $EQ$ of pairs of codes with the same
domain: there is a computable map $f$ from codes to pairs of codes such that, for every code $c$,
$c \in E$ if and only if $f(c) \in EQ$.

One can take $f(c) = (c, e)$ for a code $e$ defined nowhere. -/
theorem manyOneReducible_empty_eq : ManyOneReducible EmptyCode EqCode := by
  obtain ⟨e, he⟩ := exists_code_empty
  refine ⟨fun c ↦ (c, e), Computable.pair Computable.id (Computable.const e), fun c ↦ ?_⟩
  rw [eqCode_iff, he]
  exact ⟨fun h n ↦ ⟨fun hn ↦ h n hn, fun hn ↦ hn.elim⟩, fun h n hn ↦ (h n).mp hn⟩

/-- **Equivalence is not recognizable.** The set $EQ$ of pairs of codes of partial recursive
functions on $\mathbb{N}$ with the same domain is not recognizable by multi-stack machines: no
multi-stack machine, started on the binary encoding of a pair of codes, halts exactly when the
pair is in $EQ$. -/
theorem not_tm2Recognizable_eq : ¬TM2Recognizable EqCode := fun h ↦
  not_tm2Recognizable_empty (tm2Recognizable_of_manyOneReducible manyOneReducible_empty_eq h)

/-- **Halting-on-zero code.** For a code $c$ of a partial recursive function on $\mathbb{N}$, the
code $h(c)$ is the composition $k_0 \circ c \circ k_0$, where $k_0$ is the code of the constant
function $0$: whatever its input, $h(c)$ runs $c$ on $0$ and, if this halts, outputs $0$. -/
def haltsOnZeroCode (c : Code) : Code :=
  Code.comp (Code.const 0) (Code.comp c (Code.const 0))

theorem eval_haltsOnZeroCode (c : Code) (n : ℕ) :
    (haltsOnZeroCode c).eval n = (c.eval 0).map fun _ ↦ 0 := by
  have hk : (Code.const 0).eval = fun _ ↦ Part.some 0 := funext (Code.eval_const 0)
  simp only [haltsOnZeroCode, Code.eval, hk, Part.bind_eq_bind]
  exact (congrArg (fun x : Part ℕ ↦ x.bind fun _ ↦ Part.some 0) (Part.bind_some 0 c.eval)).trans
    (Part.bind_some_eq_map _ _)

/-- **Halting on zero reduces to equivalence.** The set of codes $c$ of partial recursive
functions on $\mathbb{N}$ that halt on input $0$ (are defined at $0$) is many-one reducible to
the set $EQ$ of pairs of codes with the same domain: there is a computable map $f$ from codes to
pairs of codes such that, for every code $c$, $c$ halts on $0$ if and only if $f(c) \in EQ$.

One can take $f(c) = (h(c), k_0)$, where $h(c)$ runs $c$ on $0$ and then outputs $0$ whatever
its input, and $k_0$ is the code of the constant function $0$. -/
theorem manyOneReducible_halting_eq :
    ManyOneReducible (fun c : Code ↦ (c.eval 0).Dom) EqCode := by
  refine ⟨fun c ↦ (haltsOnZeroCode c, Code.const 0), Computable.pair ?_ (Computable.const _),
    fun c ↦ ?_⟩
  · exact (Code.primrec₂_comp.comp (Primrec.const _) (Code.primrec₂_comp.comp Primrec.id
      (Primrec.const _))).to_comp
  · rw [eqCode_iff]
    simp only [eval_haltsOnZeroCode, Code.eval_const, Part.map_Dom, Part.some_dom, iff_true]
    exact ⟨fun h _ ↦ h, fun h ↦ h 0⟩

/-- **Equivalence is not co-recognizable.** The set $EQ$ of pairs of codes of partial recursive
functions on $\mathbb{N}$ with the same domain is not co-recognizable by multi-stack machines:
no multi-stack machine, started on the binary encoding of a pair of codes, halts exactly when
the pair is not in $EQ$.

The complement of halting on $0$ would reduce to the complement of equivalence. -/
theorem not_tm2CoRecognizable_eq : ¬TM2CoRecognizable EqCode := by
  intro h
  obtain ⟨f, hf, hpq⟩ := manyOneReducible_halting_eq
  have hred : ManyOneReducible (fun c : Code ↦ ¬(c.eval 0).Dom) fun p ↦ ¬EqCode p :=
    ⟨f, hf, fun c ↦ not_congr (hpq c)⟩
  exact not_tm2CoRecognizable_halting 0 (tm2Recognizable_of_manyOneReducible hred h)

end Cslib.Decidability
