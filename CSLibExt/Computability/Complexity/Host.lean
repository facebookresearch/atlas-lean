/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.EncodingConverters
public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.TuringMachine.Cleanup
public import MathlibExt.Computability.TuringMachine.Composition
public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import Mathlib.Tactic.Ring

/-!
# Generic hosts for component machines

A Karp reduction or an NP verifier written as a hand-made `TM2` program does its work in a
*component*: a program on a few stacks of its own, started with its input on some of them. To
get a `TM2ComputableInPolyTime` out of it, a *host* must move the input off the canonical input
stack, run the component, empty every work stack and leave exactly the answer on the output
stack. This file builds that host once, for every component.

* `Comp`: a component machine (finitely many stacks and labels, state `Bool`).
* `reduction`: from a component that turns the bits `x` on its stack `cX` into `f x` on its stack
  `cO` within `p |x|` steps, a `TM2ComputableInPolyTime` for `f` on raw bit lists;
  `isPolyTime_reduction` composes it with `DecodeBits.computable` and `EncodeBits.computable`.
* `verifier`: from a component that starts with `x` on `cX` and `w` on `cW` and stops at label
  `yes` or `no` according to `f x w` within `p (|x| + |w|)` steps, a `TM2ComputableInPolyTime` on
  the `x # w` input `Verifier.pairEncode`; `isPolyTime_verifier` composes it with
  `Converter.computable`.

The host stacks are `inp | out | X1 | W1 | comp k`, the component's stacks embedded by
`TM2Embedding.SEmb` with `e := comp`. Phase 0 moves each input block onto its component stack
with two `moveB` passes through a buffer (`X1` or `W1`), so the order is kept, and resets the
state. The component then runs embedded (`runLe_embed`); its exit labels lead to a `cleanS` loop
that empties every stack but the output. The cleanup's length is bounded by the stack sizes,
which the step count bounds (`TM2Composition.length_iter`).
-/

@[expose] public section

namespace Cslib.Complexity.Host

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
  Cslib.Complexity.DenseSAT

/-- A component machine: finitely many stacks and labels, state `Bool`. `ks` lists the stacks,
so that the host can empty all of them. -/
structure Comp where
  /-- Stack indices. -/
  K : Type
  /-- Decidable equality of stack indices. -/
  [decK : DecidableEq K]
  /-- Finitely many stacks. -/
  [finK : Fintype K]
  /-- Stack alphabets. -/
  Γ : K → Type
  /-- Finite alphabets. -/
  [finΓ : ∀ k, Fintype (Γ k)]
  /-- Labels. -/
  L : Type
  /-- Decidable equality of labels. -/
  [decL : DecidableEq L]
  /-- Finitely many labels. -/
  [finL : Fintype L]
  /-- The program. -/
  prog : L → TM2.Stmt Γ L Bool
  /-- The stacks, listed. -/
  ks : List K
  /-- No stack is listed twice. -/
  ks_nodup : ks.Nodup
  /-- Every stack is listed. -/
  mem_ks : ∀ k, k ∈ ks

attribute [instance] Comp.decK Comp.finK Comp.finΓ Comp.decL Comp.finL

/-! ### Host stacks, alphabets and labels -/

/-- Host stacks: input, output, two buffers for phase 0, and the component's stacks. -/
inductive HK (c : Comp)
  | inp | out | X1 | W1
  | comp (k : c.K)
  deriving DecidableEq

/-- Every host stack, listed. -/
def allKs (c : Comp) : List (HK c) := .inp :: .out :: .X1 :: .W1 :: c.ks.map .comp

theorem allKs_nodup (c : Comp) : (allKs c).Nodup := by
  have h : (c.ks.map HK.comp).Nodup := c.ks_nodup.map fun _ _ h => HK.comp.inj h
  simp [allKs, h]

theorem mem_allKs {c : Comp} (k : HK c) : k ∈ allKs c := by
  cases k <;> simp [allKs, c.mem_ks]

/-- Finitely many host stacks. -/
instance (c : Comp) : Fintype (HK c) := Fintype.ofList (allKs c) mem_allKs

/-- Host alphabets: `α` on the input, the component's alphabets on its stacks, bits elsewhere. -/
@[reducible] def HΓ (c : Comp) (α : Type) : HK c → Type
  | .inp => α
  | .comp k => c.Γ k
  | _ => Bool

/-- Phase-0 labels: move `x` (two passes), drop the separator, move `w` (two passes), reset the
state and start the component. -/
inductive P0 | m1 | m2 | sep | m3 | m4 | go
  deriving DecidableEq

/-- Finitely many phase-0 labels. -/
instance P0.instFintypeEnumFix : Fintype P0 where
  elems := ⟨↑[P0.m1, .m2, .sep, .m3, .m4, .go], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Host labels: phase 0, the component's labels, cleanup and output (with the answer). -/
inductive HLab (c : Comp)
  | ph (p : P0)
  | comp (l : c.L)
  | clean (ans : Bool)
  | fin (ans : Bool)
  deriving DecidableEq

/-- `HLab` as a sum type, for its `Fintype` instance. -/
def HLab.equiv (c : Comp) : HLab c ≃ P0 ⊕ c.L ⊕ Bool ⊕ Bool where
  toFun
    | .ph p => .inl p | .comp l => .inr (.inl l) | .clean a => .inr (.inr (.inl a))
    | .fin a => .inr (.inr (.inr a))
  invFun
    | .inl p => .ph p | .inr (.inl l) => .comp l | .inr (.inr (.inl a)) => .clean a
    | .inr (.inr (.inr a)) => .fin a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p | l | a | a <;> rfl

/-- Finitely many host labels. -/
instance (c : Comp) : Fintype (HLab c) := Fintype.ofEquiv _ (HLab.equiv c).symm

/-- The component's stacks inside a host with input alphabet `α`. -/
def emb (c : Comp) (α : Type) : SEmb c.Γ (HΓ c α) where
  e := .comp
  inj _ _ h := HK.comp.inj h
  ι _ := Equiv.refl _

/-- A host agrees with the component when its `comp k` stacks are the component's stacks. -/
theorem agree_emb {c : Comp} {α : Type} {S : ∀ k, List (c.Γ k)} {T : ∀ k, List (HΓ c α k)} :
    Agree (emb c α) S T ↔ ∀ k, T (.comp k) = S k := by
  refine forall_congr' fun k => ?_
  change T (.comp k) = (S k).map id ↔ _
  rw [List.map_id]

/-! ### Generic pieces of a host run -/

/-- **Two `moveB` passes** through an empty buffer `t` move the bit block `x` of `a` onto `b`,
re-encoded by `g` and in the original order, in `2 |x| + 2` steps. -/
theorem move2_run {K Λ : Type} [DecidableEq K] {Γ : K → Type} {M : Λ → TM2.Stmt Γ Λ Bool}
    {a t b : K} {d : Γ a → Option Bool} {gt : Bool → Γ t} {dt : Γ t → Option Bool}
    {g : Bool → Γ b} {l₁ l₂ l₃ : Λ} (h₁ : M l₁ = moveB a t d gt l₁ l₂)
    (h₂ : M l₂ = moveB t b dt g l₂ l₃) (hat : a ≠ t) (htb : t ≠ b) (hab : a ≠ b)
    (hdt : ∀ y, dt (gt y) = some y) (x : List Bool) (xs A : List (Γ a)) (v : Bool)
    (S : ∀ k, List (Γ k)) (hS : S a = xs ++ A) (hxs : IsBitBlock d xs x)
    (hA : EndsBitBlock d A) (ht : S t = []) :
    ∃ v' S', Run M (2 * x.length + 2) ⟨some l₁, v, S⟩ ⟨some l₃, v', S'⟩ ∧ S' a = A ∧
      S' t = [] ∧ S' b = x.map g ++ S b ∧ ∀ k, k ≠ a → k ≠ t → k ≠ b → S' k = S k := by
  obtain ⟨v₁, S₁, r₁, h1a, h1t, h1k⟩ := moveB_run h₁ hat x xs A v S hS hxs hA
  obtain ⟨v₂, S₂, r₂, h2t, h2b, h2k⟩ := moveB_run h₂ htb x.reverse (x.map gt).reverse [] v₁ S₁
    (by rw [h1t, ht]) (by simp [IsBitBlock, List.map_reverse, hdt])
    (by simp [EndsBitBlock])
  refine ⟨v₂, S₂, (r₁.trans r₂).of_eq (by simp; omega), ?_, h2t, ?_, ?_⟩
  · rw [h2k a hat hab, h1a]
  · rw [h2b, h1k b hab.symm htb.symm]; simp [List.map_reverse]
  · intro k hka hkt hkb; rw [h2k k hkt hkb, h1k k hka hkt]

/-- The stacks the cleanup empties: all but the output stack `o`. -/
def cleanKs (c : Comp) (o : HK c) : List (HK c) := (allKs c).filter (· ≠ o)

theorem cleanKs_nodup (c : Comp) (o : HK c) : (cleanKs c o).Nodup := (allKs_nodup c).filter _

/-- The cleanup empties exactly the stacks other than the output. -/
theorem mem_cleanKs {c : Comp} {o k : HK c} : k ∈ cleanKs c o ↔ k ≠ o := by
  simp [cleanKs, mem_allKs]

/-- **Cleanup** in a host program whose label `clean ans` is `cleanS (cleanKs c o)`: with every
stack of length at most `m`, `fin ans` is reached within `m + 1` steps with only `o` left. -/
theorem cleanup_run {c : Comp} {α : Type} {M : HLab c → TM2.Stmt (HΓ c α) (HLab c) Bool}
    {o : HK c} {ans : Bool} (hM : M (.clean ans) = cleanS (cleanKs c o) (.clean ans) (.fin ans))
    (m : ℕ) (v : Bool) (S : ∀ k, List (HΓ c α k)) (hl : ∀ k, (S k).length ≤ m) :
    RunLe M (m + 1) ⟨some (.clean ans), v, S⟩
      ⟨some (.fin ans), false, update (fun _ => []) o (S o)⟩ := by
  have h := clean_run hM (cleanKs_nodup c o) m v S (fun k _ => hl k)
  have e : (fun k => if k ∈ cleanKs c o then [] else S k) = update (fun _ => []) o (S o) := by
    funext k
    by_cases hk : k = o
    · subst hk; simp [mem_cleanKs]
    · simp [mem_cleanKs, hk]
  rwa [e] at h

/-- Stack sizes grow by at most `pushBound` per step. -/
theorem stk_length_le (M : FinTM2) {n N : ℕ} {S S' : ∀ k, List (M.Γ k)} {v v' : M.σ}
    {l l' : M.Λ} (hS : ∀ k, (S k).length ≤ N) (h : Run M.m n ⟨some l, v, S⟩ ⟨some l', v', S'⟩) :
    ∀ k, (S' k).length ≤ N + TM2Composition.pushBound M * n := fun k =>
  (TM2Composition.length_iter M k n _ _ h).trans (Nat.add_le_add_right (hS k) _)

/-- The initial configuration: the input on `k₀`, every other stack empty. -/
theorem initList_eq (M : FinTM2) (l : List (M.Γ M.k₀)) :
    initList M l = ⟨some M.main, M.initialState, update (fun _ => []) M.k₀ l⟩ := by
  rw [TM2Composition.update_nil_eq_initList]
  rfl

/-- The halting configuration: the output on `k₁`, every other stack empty. -/
theorem haltList_eq (M : FinTM2) (l : List (M.Γ M.k₁)) :
    haltList M l = ⟨none, M.initialState, update (fun _ => []) M.k₁ l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [h]

/-- A single non-empty stack bounds every stack's length. -/
theorem update_length_le {c : Comp} {α : Type} (o : HK c) (l : List (HΓ c α o)) :
    ∀ k, (update (fun _ => []) o l k).length ≤ l.length := by
  intro k
  by_cases h : k = o
  · subst h; simp
  · simp [h]

/-! ### The reduction host -/

section Reduction

variable (c : Comp) (cX cO : c.K) (gX : Bool → c.Γ cX) (start done : c.L)

/-- Component labels in the reduction host: `done` starts the cleanup. -/
def φR (l : c.L) : HLab c := if l = done then .clean false else .comp l

/-- The reduction host: move the input bits onto `cX`, run the component, empty every stack but
`cO`, halt. -/
def rprog : HLab c → TM2.Stmt (HΓ c Bool) (HLab c) Bool
  | .ph .m1 => moveB (Γ := HΓ c Bool) .inp .X1 some id (.ph .m1) (.ph .m2)
  | .ph .m2 => moveB (Γ := HΓ c Bool) .X1 (.comp cX) some gX (.ph .m2) (.ph .go)
  | .ph .go => .load (fun _ => false) (.goto fun _ => φR c done start)
  | .ph .sep | .ph .m3 | .ph .m4 => .halt
  | .comp l => mapS (emb c Bool) (φR c done) (c.prog l)
  | .clean _ => cleanS (cleanKs c (.comp cO)) (.clean false) (.fin false)
  | .fin _ => .halt

/-- The reduction host as a `FinTM2`: input `inp` (raw bits), output the component's `cO`. -/
def rtm : FinTM2 where
  K := HK c
  k₀ := .inp
  k₁ := .comp cO
  Γ := HΓ c Bool
  Λ := HLab c
  main := .ph .m1
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := rprog c cX cO gX start done

/-- The reduction host's step bound: phase 0 and the component, then the cleanup (stacks of
length at most the input plus the pushes so far) and the halt. -/
noncomputable def rtime (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (TM2Composition.pushBound (rtm c cX cO gX start done) + 1) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + p) + Polynomial.X + Polynomial.C 2

theorem rtime_eval (p : Polynomial ℕ) (n : ℕ) :
    (rtime c cX cO gX start done p).eval n =
      (2 * n + 3 + p.eval n) +
        (n + TM2Composition.pushBound (rtm c cX cO gX start done) * (2 * n + 3 + p.eval n)) +
          2 := by
  simp only [rtime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

variable {c cX cO gX start done}

/-- The reduction host runs the component at `comp l`; its exit `done` leads to the cleanup. -/
theorem embeds_rprog (hdone : c.prog done = .halt) :
    Embeds (emb c Bool) (φR c done) c.prog (rprog c cX cO gX start done) := by
  intro l
  by_cases h : l = done
  · subst h; exact .inr hdone
  · left
    rw [show φR c done l = .comp l by simp [φR, h]]
    rfl

/-- **The reduction host's run on one input**: a component run from the raw bits `x` on `cX` to
`out` on `cO` within `p |x|` steps gives a host run that halts with `out.map eO.symm` on `cO` and
every other stack empty. -/
theorem rprog_run_at (eO : c.Γ cO ≃ Bool) (out : List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt) (x : List Bool)
    (hrun : ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = out.map eO.symm) :
    RunLe (rprog c cX cO gX start done) ((rtime c cX cO gX start done p).eval x.length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp x⟩
      ⟨none, false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩ := by
  set S₀ : ∀ k, List (HΓ c Bool k) := update (fun _ => []) .inp x with hS₀
  obtain ⟨v₁, S₁, r₁, -, -, h1b, h1k⟩ := move2_run (M := rprog c cX cO gX start done)
    (a := .inp) (t := .X1) (b := .comp cX) (d := some) (gt := id) (dt := some) (g := gX)
    (l₁ := .ph .m1) (l₂ := .ph .m2) (l₃ := .ph .go) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) x x [] false S₀ (by simp [hS₀]) rfl rfl (by simp [hS₀])
  have r₂ : Run (rprog c cX cO gX start done) 1 ⟨some (.ph .go), v₁, S₁⟩
      ⟨some (φR c done start), false, S₁⟩ := Run.single rfl
  have hag : Agree (emb c Bool) (update (fun _ => []) cX (x.map gX)) S₁ := by
    rw [agree_emb]
    intro k
    by_cases hk : k = cX
    · subst hk; rw [update_self, h1b]; simp [hS₀]
    · rw [update_of_ne hk, h1k _ (by simp) (by simp) (by simpa using hk)]; simp [hS₀]
  obtain ⟨v, S', hr, hO⟩ := hrun
  obtain ⟨T₁, ⟨n₁, hn₁, r₃⟩, hag₁, -⟩ := runLe_embed (φR c done) (embeds_rprog hdone) hr hag
  rw [show φR c done done = .clean false by simp [φR]] at r₃
  have r := (r₁.trans r₂).trans r₃
  have hl := stk_length_le (rtm c cX cO gX start done) (N := x.length)
    (update_length_le (c := c) (α := Bool) .inp x) r
  obtain ⟨n₄, hn₄, r₄⟩ := cleanup_run (M := rprog c cX cO gX start done) (o := .comp cO)
    (ans := false) rfl _ v T₁ hl
  have hT : T₁ (.comp cO) = out.map eO.symm := by rw [agree_emb.1 hag₁ cO, hO]
  rw [hT] at r₄
  have r₅ : Run (rprog c cX cO gX start done) 1
      ⟨some (.fin false), false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩
      ⟨none, false, update (fun _ => []) (.comp cO) (out.map eO.symm)⟩ := Run.single rfl
  refine ⟨_, ?_, (r.trans r₄).trans r₅⟩
  rw [rtime_eval]
  have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (rtm c cX cO gX start done))
    (show 2 * x.length + 2 + 1 + n₁ ≤ 2 * x.length + 3 + p.eval x.length by omega)
  omega

/-- **The reduction host's run** on the raw bits `x`: it halts with `(f x).map eO.symm` on `cO`
and every other stack empty. -/
theorem rprog_run (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm)
    (x : List Bool) :
    RunLe (rprog c cX cO gX start done) ((rtime c cX cO gX start done p).eval x.length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp x⟩
      ⟨none, false, update (fun _ => []) (.comp cO) ((f x).map eO.symm)⟩ :=
  rprog_run_at eO (f x) p hdone x (hrun x)

/-- **Reduction host.** A component that turns the bits `x` on `cX` into `f x` on `cO` (read
through `eO`) within `p |x|` steps gives a polynomial-time `TM2` machine for `f` on raw bit
lists. -/
noncomputable def reduction (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm) :
    TM2ComputableInPolyTime (fun l : List Bool => l) (fun l : List Bool => l) f where
  tm := rtm c cX cO gX start done
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := eO
  time := rtime c cX cO gX start done p
  outputsFun := fun x => by
    have h := rprog_run eO f p hdone hrun x
    unfold RunLe at h
    refine ⟨⟨Classical.choose h, ?_⟩, (Classical.choose_spec h).1⟩
    erw [List.map_id, initList_eq, Option.map_some, haltList_eq]
    exact (Classical.choose_spec h).2

/-- **Reduction host, canonical form**: `f` is polynomial-time (`IsPolyTime`) as soon as some
component computes it within a polynomial number of steps. -/
theorem isPolyTime_reduction (eO : c.Γ cO ≃ Bool) (f : List Bool → List Bool)
    (p : Polynomial ℕ) (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = (f x).map eO.symm) :
    ComplexityTheory.IsPolyTime f := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (reduction eO f p hdone hrun)
  exact tm2ComputableInPolyTime_comp (f := f) (g := id) h EncodeBits.computable

/-- **Decider host**: a component that leaves exactly the bit `L x` on `cO` (read through `eO`)
within `p |x|` steps makes `L` polynomial-time, i.e. puts it in `P`. The reduction host for
`fun x => [L x]`, read with `Bool`'s one-bit encoding. -/
theorem isPolyTime_decider (eO : c.Γ cO ≃ Bool) (L : List Bool → Bool) (p : Polynomial ℕ)
    (hdone : c.prog done = .halt)
    (hrun : ∀ x, ∃ v S', RunLe c.prog (p.eval x.length)
      ⟨some start, false, update (fun _ => []) cX (x.map gX)⟩ ⟨some done, v, S'⟩ ∧
        S' cO = [eO.symm (L x)]) :
    ComplexityTheory.IsPolyTime L := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (reduction eO (fun x => [L x]) p hdone hrun)
  exact ⟨⟨h.toTM2ComputableAux, h.time, h.outputsFun⟩⟩

end Reduction

/-! ### The verifier host -/

section Verifier

variable (c : Comp) (cX cW : c.K) (gX : Bool → c.Γ cX) (gW : Bool → c.Γ cW) (start yes no : c.L)

/-- Component labels in the verifier host: `yes` and `no` start the cleanup with the answer. -/
def φV (l : c.L) : HLab c :=
  if l = yes then .clean true else if l = no then .clean false else .comp l

/-- Read an `x` symbol of the `x # w` input as a bit. -/
def dX : Verifier.G → Option Bool
  | .inl b => some b
  | _ => none

/-- Read a `w` symbol of the `x # w` input as a bit. -/
def dW : Verifier.G → Option Bool
  | .inr (some b) => some b
  | _ => none

/-- The verifier host: move `x` onto `cX` and `w` onto `cW`, run the component, empty every stack
but the output, push the answer. -/
def vprog : HLab c → TM2.Stmt (HΓ c Verifier.G) (HLab c) Bool
  | .ph .m1 => moveB (Γ := HΓ c Verifier.G) .inp .X1 dX id (.ph .m1) (.ph .m2)
  | .ph .m2 => moveB (Γ := HΓ c Verifier.G) .X1 (.comp cX) some gX (.ph .m2) (.ph .sep)
  | .ph .sep => .pop .inp (fun s _ => s) (.goto fun _ => .ph .m3)
  | .ph .m3 => moveB (Γ := HΓ c Verifier.G) .inp .W1 dW id (.ph .m3) (.ph .m4)
  | .ph .m4 => moveB (Γ := HΓ c Verifier.G) .W1 (.comp cW) some gW (.ph .m4) (.ph .go)
  | .ph .go => .load (fun _ => false) (.goto fun _ => φV c yes no start)
  | .comp l => mapS (emb c Verifier.G) (φV c yes no) (c.prog l)
  | .clean ans => cleanS (cleanKs c .out) (.clean ans) (.fin ans)
  | .fin ans => .push .out (fun _ => ans) .halt

/-- The verifier host as a `FinTM2`: input `inp` (the `x # w` alphabet), output `out` (bits). -/
def vtm : FinTM2 where
  K := HK c
  k₀ := .inp
  k₁ := .out
  Γ := HΓ c Verifier.G
  Λ := HLab c
  main := .ph .m1
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := vprog c cX cW gX gW start yes no

/-- The verifier host's step bound: phase 0 and the component, then the cleanup (stacks of
length at most the input plus the pushes so far) and the output step. -/
noncomputable def vtime (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (TM2Composition.pushBound (vtm c cX cW gX gW start yes no) + 1) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 4 + p) + Polynomial.X + Polynomial.C 2

theorem vtime_eval (p : Polynomial ℕ) (n : ℕ) :
    (vtime c cX cW gX gW start yes no p).eval n =
      (2 * n + 4 + p.eval n) +
        (n + TM2Composition.pushBound (vtm c cX cW gX gW start yes no) *
          (2 * n + 4 + p.eval n)) + 2 := by
  simp only [vtime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

variable {c cX cW gX gW start yes no}

/-- The verifier host runs the component at `comp l`; its exits lead to the cleanup. -/
theorem embeds_vprog (hyes : c.prog yes = .halt) (hno : c.prog no = .halt) :
    Embeds (emb c Verifier.G) (φV c yes no) c.prog (vprog c cX cW gX gW start yes no) := by
  intro l
  by_cases h1 : l = yes
  · subst h1; exact .inr hyes
  by_cases h2 : l = no
  · subst h2; exact .inr hno
  left
  rw [show φV c yes no l = .comp l by simp [φV, h1, h2]]
  rfl

/-- **The verifier host's run** on `x # w`: it halts with `[f x w]` on the output stack and every
other stack empty. -/
theorem vprog_run (f : List Bool → List Bool → Bool) (p : Polynomial ℕ) (hXW : cX ≠ cW)
    (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩)
    (x w : List Bool) :
    RunLe (vprog c cX cW gX gW start yes no)
      ((vtime c cX cW gX gW start yes no p).eval (Verifier.pairEncode (x, w)).length)
      ⟨some (.ph .m1), false, update (fun _ => []) .inp (Verifier.pairEncode (x, w))⟩
      ⟨none, false, update (fun _ => []) .out [f x w]⟩ := by
  set M := vprog c cX cW gX gW start yes no with hM
  set N := (Verifier.pairEncode (x, w)).length with hN
  have hNe : N = x.length + 1 + w.length := by
    simp [hN, Verifier.pairEncode]; omega
  set S₀ : ∀ k, List (HΓ c Verifier.G k) := update (fun _ => []) .inp (Verifier.pairEncode (x, w))
    with hS₀
  -- `x` onto `cX`
  obtain ⟨v₁, S₁, r₁, h1a, -, h1b, h1k⟩ := move2_run (M := M)
    (a := .inp) (t := .X1) (b := .comp cX) (d := dX) (gt := id) (dt := some) (g := gX)
    (l₁ := .ph .m1) (l₂ := .ph .m2) (l₃ := .ph .sep) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) x (x.map Sum.inl) (Sum.inr none :: w.map fun b => Sum.inr (some b)) false S₀
    (by simp [hS₀, Verifier.pairEncode]) (by simp [IsBitBlock, dX, Function.comp_def]) rfl
    (by simp [hS₀])
  -- drop the separator
  have r₂ : Run M 1 ⟨some (.ph .sep), v₁, S₁⟩
      ⟨some (.ph .m3), v₁, update S₁ .inp (w.map fun b => Sum.inr (some b))⟩ :=
    Run.single (by simp [hM, vprog, TM2.stepAux, h1a])
  -- `w` onto `cW`
  obtain ⟨v₃, S₃, r₃, -, -, h3b, h3k⟩ := move2_run (M := M)
    (a := .inp) (t := .W1) (b := .comp cW) (d := dW) (gt := id) (dt := some) (g := gW)
    (l₁ := .ph .m3) (l₂ := .ph .m4) (l₃ := .ph .go) rfl rfl (by simp) (by simp) (by simp)
    (fun _ => rfl) w (w.map fun b => Sum.inr (some b)) [] v₁
    (update S₁ .inp (w.map fun b => Sum.inr (some b))) (by simp)
    (by simp [IsBitBlock, dW, Function.comp_def]) rfl
    (by rw [update_of_ne (by simp), h1k _ (by simp) (by simp) (by simp)]; simp [hS₀])
  have r₄ : Run M 1 ⟨some (.ph .go), v₃, S₃⟩ ⟨some (φV c yes no start), false, S₃⟩ :=
    Run.single rfl
  have hag : Agree (emb c Verifier.G)
      (update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)) S₃ := by
    rw [agree_emb]
    intro k
    by_cases hW : k = cW
    · subst hW
      rw [update_self, h3b, update_of_ne (by simp),
        h1k _ (by simp) (by simp) (by simpa using hXW.symm)]
      simp [hS₀]
    rw [update_of_ne hW, h3k _ (by simp) (by simp) (by simpa using hW), update_of_ne (by simp)]
    by_cases hX : k = cX
    · subst hX; rw [update_self, h1b]; simp [hS₀]
    · rw [update_of_ne hX, h1k _ (by simp) (by simp) (by simpa using hX)]; simp [hS₀]
  obtain ⟨v, S', hr⟩ := hrun x w
  obtain ⟨T₁, ⟨n₁, hn₁, r₅⟩, -, hfr⟩ :=
    runLe_embed (φV c yes no) (embeds_vprog hyes hno) hr hag
  rw [show φV c yes no (if f x w then yes else no) = .clean (f x w) by
    cases f x w <;> simp [φV, hyn.symm]] at r₅
  have r := (((r₁.trans r₂).trans r₃).trans r₄).trans r₅
  have hl := stk_length_le (vtm c cX cW gX gW start yes no) (N := N)
    (update_length_le (c := c) (α := Verifier.G) .inp _) r
  obtain ⟨n₆, hn₆, r₆⟩ := cleanup_run (M := M) (o := .out) (ans := f x w) rfl _ v T₁ hl
  have hout : T₁ .out = [] := by
    rw [hfr .out (fun k h => by simp [emb] at h), h3k _ (by simp) (by simp) (by simp),
      update_of_ne (by simp), h1k _ (by simp) (by simp) (by simp)]
    simp [hS₀]
  rw [hout, update_eq_self] at r₆
  have r₇ : Run M 1 ⟨some (.fin (f x w)), false, fun _ => []⟩
      ⟨none, false, update (fun _ => []) .out [f x w]⟩ := Run.single rfl
  refine ⟨_, ?_, (r.trans r₆).trans r₇⟩
  rw [vtime_eval]
  have hp := TM2Composition.eval_mono p (show x.length + w.length ≤ N by omega)
  have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (vtm c cX cW gX gW start yes no))
    (show 2 * x.length + 2 + 1 + (2 * w.length + 2) + 1 + n₁ ≤ 2 * N + 4 + p.eval N by omega)
  omega

/-- **Verifier host.** A component that starts with `x` on `cX` and `w` on `cW` and stops at
`yes` or `no` according to `f x w` within `p (|x| + |w|)` steps gives a polynomial-time `TM2`
machine for `f` on the `x # w` input. -/
noncomputable def verifier (f : List Bool → List Bool → Bool) (p : Polynomial ℕ) (hXW : cX ≠ cW)
    (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩) :
    TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) (fun q => f q.1 q.2) where
  tm := vtm c cX cW gX gW start yes no
  inputAlphabet := Equiv.refl Verifier.G
  outputAlphabet := Equiv.refl Bool
  time := vtime c cX cW gX gW start yes no p
  outputsFun := fun q => by
    obtain ⟨x, w⟩ := q
    have h := vprog_run f p hXW hyn hyes hno hrun x w
    unfold RunLe at h
    refine ⟨⟨Classical.choose h, ?_⟩, (Classical.choose_spec h).1⟩
    erw [List.map_id, List.map_id, initList_eq, Option.map_some, haltList_eq]
    exact (Classical.choose_spec h).2

/-- **Verifier host, canonical form**: `fun q => f q.1 q.2` is polynomial-time (`IsPolyTime`) as
soon as some component decides it within a polynomial number of steps. -/
theorem isPolyTime_verifier (f : List Bool → List Bool → Bool) (p : Polynomial ℕ)
    (hXW : cX ≠ cW) (hyn : yes ≠ no) (hyes : c.prog yes = .halt) (hno : c.prog no = .halt)
    (hrun : ∀ x w, ∃ v S', RunLe c.prog (p.eval (x.length + w.length))
      ⟨some start, false, update (update (fun _ => []) cX (x.map gX)) cW (w.map gW)⟩
      ⟨some (if f x w then yes else no), v, S'⟩) :
    ComplexityTheory.IsPolyTime fun q : List Bool × List Bool => f q.1 q.2 :=
  tm2ComputableInPolyTime_comp (f := id) (g := fun q : List Bool × List Bool => f q.1 q.2)
    Converter.computable (verifier f p hXW hyn hyes hno hrun)

end Verifier

end Cslib.Complexity.Host
