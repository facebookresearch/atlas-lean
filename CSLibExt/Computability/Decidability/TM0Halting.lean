/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The halting problem for single-tape Turing machines
-/
module

public import CSLibExt.Computability.Decidability.Undecidable
public import MathlibExt.Computability.TuringMachine.Translation.TM2ToTM0

/-!
# The halting problem for single-tape Turing machines

`TM0HaltsOn M l` says that Mathlib's single-tape machine `M` (`Turing.TM0`) halts when started on
the input word `l`. Some such machine, with a finite tape alphabet and finitely many reachable
states, has a halting set that no multi-stack machine (`FinTM2`) decides
(`exists_not_tm2Decidable_tm0HaltsOn`).

The machine is the single-tape emulation (`MetaMathlibExt.TM2ToTM0.tr`, through `TM1`) of a
`FinTM2` whose halting set is the halting problem for codes on input `0`. The emulation halts iff
the original machine does, and its input encoding `TM2to1.trInit` is primitive recursive, so a
decider for the single-tape halting set would decide the halting problem.

This is the source problem for the reduction to string rewriting and the Post correspondence
problem. The finite support (`TM0.Supports`) is what lets a finite rewriting system simulate the
machine.

## Main results

- `TM0HaltsOn` : a single-tape machine halts on an input word.
- `exists_not_tm2Decidable_tm0HaltsOn` : some single-tape machine with a finite alphabet and a
  finite support has an undecidable halting set.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability Turing Encodable MetaMathlibExt.TM2Recursive
open Nat.Partrec (Code)
open scoped MetaMathlibExt.TM2ToTM0

/-- **Halting of a single-tape machine.** A single-tape Turing machine $M$ halts on an input word
$l$ when its run, started in its start state with $l$ on the tape, reaches a halting
configuration. -/
def TM0HaltsOn {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : TM0.Machine Γ Λ) (l : List Γ) :
    Prop :=
  (TM0.eval M l).Dom

/-- **Halting agrees with evaluation for multi-stack machines.** A multi-stack machine halts on a
word $l$ over the alphabet of its input stack if and only if the evaluation of its transition
function, started at its main label and initial internal state with $l$ on the input stack and
all other stacks empty, is defined. -/
theorem tm2HaltsOn_iff_eval_dom (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    TM2HaltsOn tm l ↔ (TM2.eval tm.m tm.k₀ l).Dom := by
  rw [TM2HaltsOn, MetaMathlibExt.TM2ToTM0.initList_eq_init, TM2.eval, Part.map_Dom]
  rfl

/-- **Primitive recursive coding of a finite type.** A finite type $\alpha$ with $n$ elements gets
the primitive recursive coding transported from $\{0, \dots, n - 1\}$ along a fixed (noncanonically
chosen) bijection between $\alpha$ and $\{0, \dots, n - 1\}$. -/
@[instance_reducible]
noncomputable def primcodableOfFintype (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

/-- **The input encoding of the single-tape emulation is primitive recursive.** Let $M$ be a
multi-stack machine together with a bijection $e$ from the alphabet of its input stack to the
Booleans, and suppose the tape alphabet $\Gamma'$ of the single-tape emulation of $M$ is finite and
carries a primitive recursive coding. Then the map sending $n \in \mathbb{N}$ to the initial tape
of the emulation on the input word $e^{-1}(b_1) \cdots e^{-1}(b_m)$, where $b_1 \cdots b_m$ is the
binary code of $n$, is primitive recursive. -/
theorem primrec_trInit_encodeNat (tm : FinTM2) [Primcodable (TM2to1.Γ' tm.K tm.Γ)]
    [Finite (TM2to1.Γ' tm.K tm.Γ)] (e : tm.Γ tm.k₀ ≃ Bool) :
    Primrec fun n ↦ TM2to1.trInit tm.k₀ ((encodeNat n).map e.symm) := by
  let g : Bool → TM2to1.Γ' tm.K tm.Γ := fun b ↦
    (false, Function.update (fun _ ↦ none) tm.k₀ (some (e.symm b)))
  have hL : Primrec fun n ↦ (encodeNat n).reverse.map g :=
    Primrec.list_map (Primrec.list_reverse.comp primrec_encodeNat)
      ((Primrec.dom_finite g).comp Primrec.snd).to₂
  let f : TM2to1.Γ' tm.K tm.Γ → TM2to1.Γ' tm.K tm.Γ := fun x ↦ (true, x.2)
  refine (Primrec.list_cons.comp ((Primrec.dom_finite f).comp (Primrec.list_headI.comp hL))
    (Primrec.list_tail.comp hL)).of_eq fun n ↦ ?_
  have key : (encodeNat n).reverse.map g =
      ((encodeNat n).map e.symm).reverse.map
        fun a ↦ ((false, Function.update (fun _ ↦ none) tm.k₀ (some a)) : TM2to1.Γ' tm.K tm.Γ) := by
    rw [List.map_reverse, List.map_reverse, List.map_map]
    rfl
  simp only [TM2to1.trInit]
  rw [key]
  rfl

/-- **The halting problem for single-tape machines is undecidable.** There are a finite tape
alphabet $\Gamma$ with a blank symbol, decidable equality and a primitive recursive coding, a type
of states $\Lambda$ with a start state, a single-tape Turing machine $M$ with alphabet $\Gamma$ and
states $\Lambda$, and a finite set $S$ of states that contains the start state and is closed under
the transitions of $M$, such that the set of input words on which $M$ halts is not decidable by a
multi-stack machine. -/
theorem exists_not_tm2Decidable_tm0HaltsOn :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ) (_ : Fintype Γ) (_ : DecidableEq Γ)
      (_ : Primcodable Γ) (M : TM0.Machine Γ Λ) (S : Finset Λ),
      TM0.Supports M ↑S ∧ ¬TM2Decidable (TM0HaltsOn M) := by
  let q : ℕ → Prop := fun n ↦ ((Denumerable.ofNat Code n).eval 0).Dom
  have hq : REPred q :=
    Partrec.comp (ComputablePred.halting_problem_re 0) (Computable.ofNat Code)
  obtain ⟨tm, hfin, e, h⟩ := exists_finite_tm2HaltsOn_iff_of_rePred hq
  classical
  have : Fintype tm.K := tm.kFin
  have : Fintype tm.Λ := tm.ΛFin
  have : Fintype tm.σ := tm.σFin
  have : ∀ k, Fintype (tm.Γ k) := fun k ↦ Fintype.ofFinite _
  let _ : Primcodable (TM2to1.Γ' tm.K tm.Γ) := primcodableOfFintype _
  refine ⟨TM2to1.Γ' tm.K tm.Γ, _, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, MetaMathlibExt.TM2ToTM0.tr tm.m,
    TM1to0.trStmts (TM2to1.tr tm.m) (TM2to1.trSupp tm.m Finset.univ),
    MetaMathlibExt.TM2ToTM0.tr_supports tm.m (MetaMathlibExt.TM2ToTM0.supports_univ tm.m),
    fun hdec ↦ ?_⟩
  have hred : ManyOneReducible q (TM0HaltsOn (MetaMathlibExt.TM2ToTM0.tr tm.m)) :=
    ⟨_, (primrec_trInit_encodeNat tm e).to_comp, fun n ↦ by
      rw [h n, tm2HaltsOn_iff_eval_dom, TM0HaltsOn, MetaMathlibExt.TM2ToTM0.tr_eval_dom]⟩
  refine not_tm2Decidable_halting 0 (tm2Decidable_of_manyOneReducible
    ⟨fun c : Code ↦ encode c, Computable.encode, fun c ↦ ?_⟩
    (tm2Decidable_of_manyOneReducible hred hdec))
  simp [q]

end Cslib.Decidability
