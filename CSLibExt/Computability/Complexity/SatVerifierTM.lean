/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatTokenizer
public import CSLibExt.Computability.Complexity.SatLookup
public import CSLibExt.Computability.Complexity.SatCheck
public import CSLibExt.Computability.Complexity.PairEncodingConverter
public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import MathlibExt.Computability.TuringMachine.Composition
public import MathlibExt.Computability.TuringMachine.Cleanup
public import CSLibExt.Computability.Complexity.CookLevin.BinaryHardness
public import CSLibExt.Computability.Complexity.Karp.ThreeSatFilter
public import Mathlib.Tactic.Ring

/-!
# SAT verifier, assembly: `IsPolyTime satVerifier`

One host `TM2` machine for `Cslib.CookLevin.satVerifier` on the `x # w` input
(`Cslib.Complexity.DenseSAT.Verifier.pairEncode`):

1. phase 0 moves `x` and `w` off the input stack onto two work stacks (`moveB`, twice each);
2. the tokenizer (`Cslib.Complexity.SatVerifier.Tokenizer`, embedded) builds the token and
   table stacks or rejects;
3. the clause-check driver (`Cslib.Complexity.SatVerifier.Check`, embedded, with the lookup
   `Cslib.Complexity.SatVerifier.Lookup` embedded in it) decides `checkSpec`;
4. a cleanup loop empties every work stack and writes the answer.

`verifier` is the resulting `TM2ComputableInPolyTime`; composed with the pair-encoding
converter it gives `isPolyTime_satVerifier`, hence `satDec ∈ NP` and, with `satDec_npHard`,
Cook-Levin for `satDec` (`cook_levin_SAT_np_complete`).

The host takes a flag `cap`: with `cap = true` the clause-length filter `Karp.Filter3` runs
between the tokenizer and the driver and rejects formulas with a clause of more than three
literals, so the same machine verifies 3SAT (`ans_true`, `sat3Dec_mem_NP`); with `cap = false`
the filter always passes (`ans_false`).
-/

@[expose] public section

namespace Cslib.Complexity.SatVerifier.Machine

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
  Cslib.CookLevin Cslib.Logic.PL Computability

/-- The `x # w` alphabet of the input stack. -/
abbrev G := Cslib.Complexity.DenseSAT.Verifier.G

/-- Host stacks: input, output, and the work stacks of all components. -/
inductive HK | inp | out | X | W | T | B | S | A | C | V | P | F | CC | LC | X1 | W1 | U
  deriving DecidableEq

instance HK.instFintypeEnumFix : Fintype HK where
  elems := ⟨↑[HK.inp, .out, .X, .W, .T, .B, .S, .A, .C, .V, .P, .F, .CC, .LC, .X1, .W1, .U],
    by decide⟩
  complete := fun x => by cases x <;> decide

/-- Host alphabets: `G` on the input, `Bool` on the output, `Sym` elsewhere. -/
@[reducible] def HΓ : HK → Type
  | .inp => G
  | .out => Bool
  | _ => Sym

/-- Phase-0 labels: move `x` off the input (twice), drop the separator, move `w` (twice). -/
inductive P0 | m1 | m2 | sep | m3 | m4
  deriving DecidableEq

instance P0.instFintypeEnumFix : Fintype P0 where
  elems := ⟨↑[P0.m1, .m2, .sep, .m3, .m4], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Host labels. -/
inductive HLab
  | ph (p : P0)
  | tok (l : Tokenizer.Lab)
  | flt (l : Karp.Filter3.Lab)
  | chk (l : Check.DLab ⊕ Lookup.Lab)
  | clean (ans : Bool)
  | fin (ans : Bool)
  deriving DecidableEq

/-- `HLab` as a sum type, for its `Fintype` instance. -/
def HLab.equiv :
    HLab ≃ P0 ⊕ Tokenizer.Lab ⊕ Karp.Filter3.Lab ⊕ (Check.DLab ⊕ Lookup.Lab) ⊕ Bool ⊕ Bool where
  toFun
    | .ph p => .inl p | .tok l => .inr (.inl l) | .flt l => .inr (.inr (.inl l))
    | .chk l => .inr (.inr (.inr (.inl l))) | .clean a => .inr (.inr (.inr (.inr (.inl a))))
    | .fin a => .inr (.inr (.inr (.inr (.inr a))))
  invFun
    | .inl p => .ph p | .inr (.inl l) => .tok l | .inr (.inr (.inl l)) => .flt l
    | .inr (.inr (.inr (.inl l))) => .chk l | .inr (.inr (.inr (.inr (.inl a)))) => .clean a
    | .inr (.inr (.inr (.inr (.inr a)))) => .fin a
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p | l | l | l | a | a <;> rfl

instance : Fintype HLab := Fintype.ofEquiv _ HLab.equiv.symm

/-! ### Embeddings of the components -/

/-- Tokenizer stacks in the host. -/
def eT : Tokenizer.K → HK
  | .X => .X | .W => .W | .T => .T | .B => .B | .CC => .CC | .LC => .LC

/-- The tokenizer's stack embedding. -/
def embT : SEmb (fun _ : Tokenizer.K => Sym) HΓ where
  e := eT
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  ι k := match k with
    | .X => Equiv.refl Sym | .W => Equiv.refl Sym | .T => Equiv.refl Sym
    | .B => Equiv.refl Sym | .CC => Equiv.refl Sym | .LC => Equiv.refl Sym

/-- Lookup stacks in the driver. -/
def eL : Lookup.K → Check.K
  | .T => .T | .B => .B | .S => .S | .A => .A | .C => .C | .V => .V

/-- The lookup's stack embedding into the driver. -/
def embL : SEmb (fun _ : Lookup.K => Sym) (fun _ : Check.K => Sym) where
  e := eL
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  ι _ := Equiv.refl Sym

/-- Lookup labels in the driver: its exit returns to `DLab.ret`. -/
def φL (l : Lookup.Lab) : Check.DLab ⊕ Lookup.Lab := if l = .done then .inl .ret else .inr l

/-- The lookup sub-program of the driver. -/
def lkH (l : Lookup.Lab) : Check.Stmt Lookup.Lab := mapS embL φL (Lookup.prog l)

/-- Driver stacks in the host. -/
def eC : Check.K → HK
  | .T => .T | .B => .B | .S => .S | .A => .A | .C => .C | .V => .V | .P => .P | .F => .F

/-- The driver's stack embedding. -/
def embC : SEmb (fun _ : Check.K => Sym) HΓ where
  e := eC
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  ι k := match k with
    | .T => Equiv.refl Sym | .B => Equiv.refl Sym | .S => Equiv.refl Sym | .A => Equiv.refl Sym
    | .C => Equiv.refl Sym | .V => Equiv.refl Sym | .P => Equiv.refl Sym | .F => Equiv.refl Sym

/-- Filter stacks in the host. -/
def eF : Karp.Filter3.K → HK
  | .T => .T | .U => .U

/-- The filter's stack embedding. -/
def embF : SEmb (fun _ : Karp.Filter3.K => Sym) HΓ where
  e := eF
  inj a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  ι k := match k with | .T => Equiv.refl Sym | .U => Equiv.refl Sym

/-- Filter labels in the host: `pass` starts the driver, `fail` cleans up with `false`. -/
def φF : Karp.Filter3.Lab → HLab
  | .pass => .chk (.inl .start)
  | .fail => .clean false
  | l => .flt l

/-- Tokenizer labels in the host: accept starts the filter, reject cleans up with `false`. -/
def φT (l : Tokenizer.Lab) : HLab :=
  if l = .acc then .flt Karp.Filter3.start else if l = .rej then .clean false else .tok l

/-- Driver labels in the host: `yes`/`no` clean up with the answer. -/
def φC : Check.DLab ⊕ Lookup.Lab → HLab
  | .inl .yes => .clean true
  | .inl .no => .clean false
  | l => .chk l

/-! ### The host program -/

/-- Read an `x` symbol of the input as a bit. -/
def dX : G → Option Bool
  | .inl b => some b
  | _ => none

/-- Read a `w` symbol of the input as a bit. -/
def dW : G → Option Bool
  | .inr (some b) => some b
  | _ => none

/-- The work stacks emptied by the cleanup. -/
def workKs : List HK := [.inp, .X, .W, .T, .B, .S, .A, .C, .V, .P, .F, .CC, .LC, .X1, .W1, .U]

/-- The host program. -/
def hprog (cap : Bool) : HLab → TM2.Stmt HΓ HLab Bool
  | .ph .m1 => moveB (Γ := HΓ) HK.inp HK.X1 dX Sym.bit (.ph .m1) (.ph .m2)
  | .ph .m2 => moveB (Γ := HΓ) HK.X1 HK.X Sym.bit? Sym.bit (.ph .m2) (.ph .sep)
  | .ph .sep => .pop .inp (fun s _ => s) (.goto fun _ => .ph .m3)
  | .ph .m3 => moveB (Γ := HΓ) HK.inp HK.W1 dW Sym.bit (.ph .m3) (.ph .m4)
  | .ph .m4 => moveB (Γ := HΓ) HK.W1 HK.W Sym.bit? Sym.bit (.ph .m4) (.tok Tokenizer.start)
  | .tok l => mapS embT φT (Tokenizer.prog l)
  | .flt l => mapS embF φF (Karp.Filter3.prog cap l)
  | .chk l => mapS embC φC (Check.prog lkH Lookup.start l)
  | .clean ans => cleanS workKs (.clean ans) (.fin ans)
  | .fin ans => .push .out (fun _ => ans) (.load (fun _ => false) .halt)

instance (k : HK) : Fintype (HΓ k) := by cases k <;> infer_instance

/-- The host as a `FinTM2`: input `inp` (alphabet `G`), output `out` (alphabet `Bool`). -/
def tm (cap : Bool) : FinTM2 where
  K := HK
  k₀ := .inp
  k₁ := .out
  Γ := HΓ
  Λ := HLab
  main := .ph .m1
  σ := Bool
  initialState := false
  m := hprog cap

variable (cap : Bool)

/-! ### Phase 0: `x` and `w` onto work stacks -/

theorem phase0_run (x w : List Bool) (v : Bool) (S : ∀ k, List (HΓ k))
    (hinp : S .inp = Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w))
    (h0 : ∀ k, k ≠ .inp → S k = []) :
    ∃ v' S', Run (hprog cap) (2 * x.length + 2 * w.length + 5) ⟨some (.ph .m1), v, S⟩
      ⟨some (.tok Tokenizer.start), v', S'⟩ ∧
      S' .X = x.map Sym.bit ∧ S' .W = w.map Sym.bit ∧ ∀ k, k ≠ .X → k ≠ .W → S' k = [] := by
  obtain ⟨v₁, S₁, r₁, h1a, h1b, h1k⟩ := moveB_run (M := hprog cap) (self := .ph .m1)
    (next := .ph .m2)
    (a := HK.inp) (b := HK.X1) (d := dX) (g := Sym.bit) rfl (by decide) x (x.map Sum.inl)
    (Sum.inr none :: w.map fun b => Sum.inr (some b)) v S
    (by simp [hinp, Cslib.Complexity.DenseSAT.Verifier.pairEncode])
    (by simp [IsBitBlock, dX]) (by simp [EndsBitBlock, dX])
  obtain ⟨v₂, S₂, r₂, h2a, h2b, h2k⟩ := moveB_run (M := hprog cap) (self := .ph .m2)
    (next := .ph .sep) (a := HK.X1) (b := HK.X) (d := Sym.bit?) (g := Sym.bit) rfl (by decide)
    x.reverse (x.map Sym.bit).reverse [] v₁ S₁
    (by rw [h1b, h0 .X1 (by decide)]) (by simp [IsBitBlock, Sym.bit?, List.map_reverse])
    (by simp [EndsBitBlock])
  have h2inp : S₂ .inp = Sum.inr none :: w.map fun b => Sum.inr (some b) := by
    rw [h2k .inp (by decide) (by decide), h1a]
  have r₃ : Run (hprog cap) 1 ⟨some (.ph .sep), v₂, S₂⟩
      ⟨some (.ph .m3), v₂, update S₂ .inp (w.map fun b => Sum.inr (some b))⟩ :=
    Run.single (by simp [hprog, TM2.stepAux, h2inp])
  obtain ⟨v₄, S₄, r₄, h4a, h4b, h4k⟩ := moveB_run (M := hprog cap) (self := .ph .m3)
    (next := .ph .m4) (a := HK.inp) (b := HK.W1) (d := dW) (g := Sym.bit) rfl (by decide) w
    (w.map fun b => Sum.inr (some b)) [] v₂ (update S₂ .inp (w.map fun b => Sum.inr (some b)))
    (by simp) (by simp [IsBitBlock, dW]) (by simp [EndsBitBlock])
  have hW1 : S₄ .W1 = (w.map Sym.bit).reverse := by
    rw [h4b, update_of_ne (by decide), h2k .W1 (by decide) (by decide),
      h1k .W1 (by decide) (by decide), h0 .W1 (by decide)]
    simp
  obtain ⟨v₅, S₅, r₅, h5a, h5b, h5k⟩ := moveB_run (M := hprog cap) (self := .ph .m4)
    (next := .tok Tokenizer.start) (a := HK.W1) (b := HK.W) (d := Sym.bit?) (g := Sym.bit) rfl
    (by decide) w.reverse (w.map Sym.bit).reverse [] v₄ S₄ (by rw [hW1]; simp)
    (by simp [IsBitBlock, Sym.bit?, List.map_reverse]) (by simp [EndsBitBlock])
  refine ⟨v₅, S₅, ?_, ?_, ?_, ?_⟩
  · have := (((r₁.trans r₂).trans r₃).trans r₄).trans r₅
    simpa [List.length_reverse, two_mul, add_assoc, add_comm, add_left_comm] using this
  · rw [h5k .X (by decide) (by decide), h4k .X (by decide) (by decide), update_of_ne (by decide),
      h2b, h1k .X (by decide) (by decide), h0 .X (by decide)]
    simp [List.map_reverse]
  · rw [h5b, h4k .W (by decide) (by decide), update_of_ne (by decide),
      h2k .W (by decide) (by decide), h1k .W (by decide) (by decide), h0 .W (by decide)]
    simp [List.map_reverse]
  · intro k hX hW
    by_cases hk1 : k = .W1
    · subst hk1; exact h5a
    by_cases hk2 : k = .inp
    · subst hk2; rw [h5k _ (by decide) (by decide), h4a]
    by_cases hk3 : k = .X1
    · subst hk3
      rw [h5k _ (by decide) (by decide), h4k _ (by decide) (by decide), update_of_ne (by decide),
        h2a]
    rw [h5k k hk1 hW, h4k k hk2 hk1, update_of_ne hk2, h2k k hk3 hX, h1k k hk2 hk3, h0 k hk2]

/-! ### The embeddings are faithful -/

theorem embeds_tok : Embeds embT φT Tokenizer.prog (hprog cap) := by
  intro l
  by_cases h1 : l = .acc
  · subst h1; right; rfl
  by_cases h2 : l = .rej
  · subst h2; right; rfl
  left
  simp [φT, h1, h2, hprog]

theorem embeds_lk : Embeds embL φL Lookup.prog (Check.prog lkH Lookup.start) := by
  intro l
  by_cases h : l = .done
  · subst h; right; rfl
  left
  simp [φL, h, Check.prog, lkH]

theorem embeds_flt : Embeds embF φF (Karp.Filter3.prog cap) (hprog cap) := by
  intro l
  cases l <;> first | exact .inr rfl | exact .inl rfl

theorem embeds_chk : Embeds embC φC (Check.prog lkH Lookup.start) (hprog cap) := by
  intro l
  rcases l with d | l
  · cases d
    all_goals first | (right; rfl) | (left; rfl)
  · left; rfl

/-- The embedded lookup meets the driver's lookup contract. -/
theorem lookupSpec : Check.LookupSpec lkH Lookup.start 8 4 := by
  intro q es R hR v St hT hB hS hA hC hV
  obtain ⟨v', r⟩ := Lookup.run q es R hR v (fun k => St (eL k)) hT hB hS hA hC hV
  obtain ⟨T', r', hAg, hFr⟩ := runLe_embed φL embeds_lk r (S' := St)
    (fun k => by simp [embL])
  have hst : φL Lookup.start = .inr Lookup.start := rfl
  have hdn : φL Lookup.Lab.done = .inl .ret := rfl
  rw [hst, hdn] at r'
  refine ⟨v', ?_⟩
  convert r' using 3
  have hag : ∀ k, T' (eL k) = update (fun k => St (eL k)) Lookup.K.V
      [Sym.bit (liveVal es q)] k := fun k => by simpa [embL] using hAg k
  have hfr : ∀ k, (∀ k', eL k' ≠ k) → T' k = St k := fun k h => hFr k h
  funext k
  cases k
  · simpa [eL] using (hag .T).symm
  · simpa [eL] using (hag .B).symm
  · simpa [eL] using (hag .S).symm
  · simpa [eL] using (hag .A).symm
  · simpa [eL] using (hag .C).symm
  · simpa [eL] using (hag .V).symm
  · rw [hfr .P (by intro k h; cases k <;> simp [eL] at h)]; simp
  · rw [hfr .F (by intro k h; cases k <;> simp [eL] at h)]; simp

/-! ### Cleanup and output -/

theorem workKs_nodup : workKs.Nodup := by decide

theorem mem_workKs (k : HK) (h : k ≠ .out) : k ∈ workKs := by
  cases k <;> simp [workKs] at h ⊢

/-- The cleanup empties every stack: with all stacks of length at most `m` and the output
empty, it reaches `fin` within `m + 1` steps with every stack empty. -/
theorem clean_host (ans : Bool) (m : ℕ) (v : Bool) (S : ∀ k, List (HΓ k))
    (hl : ∀ k, (S k).length ≤ m) (ho : S .out = []) :
    RunLe (hprog cap) (m + 1) ⟨some (.clean ans), v, S⟩ ⟨some (.fin ans), false, fun _ => []⟩ := by
  have r := clean_run (M := hprog cap) (ks := workKs) (self := .clean ans) (next := .fin ans)
    rfl workKs_nodup m v S fun k _ => hl k
  have hS : (fun k => if k ∈ workKs then [] else S k) = fun _ => [] := by
    funext k
    by_cases hk : k = .out
    · subst hk; simp [workKs, ho]
    · simp [mem_workKs k hk]
  rw [hS] at r
  exact r

theorem fin_run (ans v : Bool) :
    Run (hprog cap) 1 ⟨some (.fin ans), v, fun _ => []⟩
      ⟨none, false, update (fun _ => []) HK.out [ans]⟩ :=
  Run.single (by simp [hprog, TM2.stepAux])

/-! ### Sizes of the token and table stacks -/

theorem entsOf_map_length (ns : List ℕ) :
    ∀ w : List Bool,
      (entsOf ns w).map (fun e => e.1.length) = ns.map fun n => (encodeNat n).length := by
  induction ns with
  | nil => intro w; simp [entsOf]
  | cons n ns ih => intro w; cases w <;> simp [entsOf, ih]

theorem tblStk_length (es : List Ent) :
    (tblStk es).length = (es.map fun e => e.1.length + 1).sum := by
  simp [tblStk, entToks, List.length_flatMap]

theorem varsOf_sum_le (φ : CNF) :
    ((varsOf φ).map fun n => (encodeNat n).length + 1).sum ≤ (toks φ).length := by
  induction φ with
  | nil => simp [varsOf, toks]
  | cons C φ ih =>
      have hC : ((C.map Prod.fst).map fun n => (encodeNat n).length + 1).sum + 1 =
          (clauseToks C).length := by
        simp [clauseToks, litToks, List.length_flatMap, List.map_map, Function.comp_def]
      simp only [varsOf, toks, List.flatMap_cons, List.map_append, List.sum_append,
        List.length_append] at ih ⊢
      omega

theorem tblStk_ents_length_le (φ : CNF) (w : List Bool) :
    (tblStk (ents φ w)).length ≤ (toks φ).length := by
  refine le_trans (le_of_eq ?_) (varsOf_sum_le φ)
  rw [tblStk_length, ents]
  have h2 : ((entsOf (varsOf φ) w).map fun e => e.1.length + 1) =
      ((entsOf (varsOf φ) w).map fun e => e.1.length).map (· + 1) := by simp
  rw [h2, entsOf_map_length, List.map_map]
  rfl

/-! ### The whole run -/

/-- The initial host stacks on input `l`. -/
def initS (l : List G) : ∀ k, List (HΓ k) := update (fun _ => []) HK.inp l

/-- Tokenizer-local view of the stacks after phase 0. -/
def tokS (x w : List Bool) : ∀ _ : Tokenizer.K, List Sym
  | .X => x.map Sym.bit
  | .W => w.map Sym.bit
  | _ => []

/-- Driver-local view of the stacks after the tokenizer accepts `φ`. -/
def chkS (φ : CNF) (w : List Bool) : ∀ _ : Check.K, List Sym
  | .T => (toks φ).reverse
  | .B => tblStk (ents φ w)
  | _ => []

/-- Steps before the cleanup, in terms of the input length `N`. -/
def preSteps (N : ℕ) : ℕ := (2 * N + 5) + (2 * N + 2) + (2 * N + 2) + (N * (8 * N + 9) + 1)

theorem lengths_le {n : ℕ} {S S' : ∀ k, List (HΓ k)} {v v' : Bool} {l l' : HLab} (N : ℕ)
    (hS : ∀ k, (S k).length ≤ N) (h : Run (hprog cap) n ⟨some l, v, S⟩ ⟨some l', v', S'⟩) :
    ∀ k, (S' k).length ≤ N + TM2Composition.pushBound (tm cap) * n := fun k =>
  (TM2Composition.length_iter (tm cap) k n ⟨some l, v, S⟩ ⟨some l', v', S'⟩ h).trans
    (Nat.add_le_add_right (hS k) _)

/-- Clean up and halt: from any stacks of length at most `m` with an empty output, reach the
halting configuration with output `[ans]` within `m + 2` steps. -/
theorem finish (ans : Bool) (m : ℕ) (v : Bool) (S : ∀ k, List (HΓ k))
    (hl : ∀ k, (S k).length ≤ m) (ho : S .out = []) :
    ∃ n, n ≤ m + 2 ∧ Run (hprog cap) n ⟨some (.clean ans), v, S⟩
      ⟨none, false, update (fun _ => []) HK.out [ans]⟩ := by
  obtain ⟨n, hn, r⟩ := clean_host cap ans m v S hl ho
  exact ⟨n + 1, by omega, r.trans (fin_run cap ans false)⟩

/-- The host's answer: with `cap`, formulas with a clause of more than three literals are
rejected. -/
def ans (p : List Bool × List Bool) : Bool :=
  ((decodeCNF p.1).map fun φ => (!cap || Karp.is3 φ) && checkSpec φ (ents φ p.2)).getD false

/-- The step bound in terms of the input length `N`: everything before the cleanup, then the
cleanup itself (all stacks are at most `N` plus the pushes so far), then the output step. -/
noncomputable def totalSteps (N : ℕ) : ℕ :=
  preSteps N + (N + TM2Composition.pushBound (tm cap) * preSteps N) + 2

theorem host_run (x w : List Bool) :
    ∃ n, n ≤ totalSteps cap (Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w)).length ∧
      Run (hprog cap) n ⟨some (.ph .m1), false,
        initS (Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w))⟩
        ⟨none, false, update (fun _ => []) HK.out [ans cap (x, w)]⟩ := by
  unfold totalSteps
  set N := (Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w)).length with hN
  have hxN : x.length ≤ N := by
    simp [hN, Cslib.Complexity.DenseSAT.Verifier.pairEncode]
  have hwN : x.length + w.length + 1 = N := by
    simp [hN, Cslib.Complexity.DenseSAT.Verifier.pairEncode]; omega
  set S₀ := initS (Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w)) with hS₀
  have hS₀l : ∀ k, (S₀ k).length ≤ N := by
    intro k; by_cases hk : k = .inp
    · subst hk; simp [hS₀, initS, hN]
    · simp [hS₀, initS, update_of_ne hk]
  -- phase 0
  obtain ⟨v₁, S₁, r₀, h1X, h1W, h1k⟩ := phase0_run cap x w false S₀ (by simp [hS₀, initS])
    (by intro k hk; simp [hS₀, initS, update_of_ne hk])
  have hagT : Agree embT (tokS x w) S₁ := by
    intro k
    cases k
    · show S₁ .X = (x.map Sym.bit).map (fun a => a); rw [h1X, List.map_id']
    · show S₁ .W = (w.map Sym.bit).map (fun a => a); rw [h1W, List.map_id']
    · show S₁ .T = ([] : List Sym).map (fun a => a); rw [h1k .T (by decide) (by decide)]; rfl
    · show S₁ .B = ([] : List Sym).map (fun a => a); rw [h1k .B (by decide) (by decide)]; rfl
    · show S₁ .CC = ([] : List Sym).map (fun a => a); rw [h1k .CC (by decide) (by decide)]; rfl
    · show S₁ .LC = ([] : List Sym).map (fun a => a); rw [h1k .LC (by decide) (by decide)]; rfl
  have hφs : φT Tokenizer.start = .tok Tokenizer.start := by simp [φT, Tokenizer.start]
  have hP0 : 2 * x.length + 2 * w.length + 5 ≤ 2 * N + 5 := by omega
  cases hdec : decodeCNF x with
  | none =>
      obtain ⟨v₂, S₂, r⟩ := Tokenizer.run_none hdec v₁ (tokS x w) rfl rfl rfl rfl
      obtain ⟨T₁, ⟨n₁, hn₁, r₁⟩, -, hfr₁⟩ := runLe_embed φT (embeds_tok cap) r hagT
      rw [hφs, show φT Tokenizer.Lab.rej = .clean false by simp [φT]] at r₁
      have r01 := r₀.trans r₁
      have hl := lengths_le cap N hS₀l r01
      have ho : T₁ .out = [] := by
        rw [hfr₁ .out (by intro k h; cases k <;> simp [embT, eT] at h)]
        exact h1k .out (by decide) (by decide)
      obtain ⟨n₂, hn₂, r₂⟩ := finish cap false _ _ T₁ hl ho
      have hret : ans cap (x, w) = false := by simp [ans, hdec]
      rw [hret]
      refine ⟨_, ?_, r01.trans r₂⟩
      have h1 : 2 * x.length + 2 * w.length + 5 + n₁ ≤ preSteps N := by
        simp only [preSteps]; nlinarith
      have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (tm cap)) h1
      omega
  | some φ =>
      have hx : x = encodeCNF φ := (decodeCNF_eq_some_iff x φ).mp hdec
      have htN : (toks φ).length ≤ N := (toks_length_le φ).trans (hx ▸ hxN)
      have hbN : (tblStk (ents φ w)).length ≤ N := (tblStk_ents_length_le φ w).trans htN
      obtain ⟨v₂, S₂, r, s2X, s2W, s2CC, s2LC, s2T, s2B⟩ :=
        Tokenizer.run_some hdec v₁ (tokS x w) rfl rfl rfl rfl
      obtain ⟨T₁, ⟨n₁, hn₁, r₁⟩, hag₁, hfr₁⟩ := runLe_embed φT (embeds_tok cap) r hagT
      rw [hφs, show φT Tokenizer.Lab.acc = .flt Karp.Filter3.start by simp [φT]] at r₁
      have hfr₁' : ∀ k, (∀ k', eT k' ≠ k) → T₁ k = S₁ k := fun k h => hfr₁ k h
      have hag₁' : ∀ k, T₁ (eT k) = (S₂ k).map (embT.ι k) := hag₁
      have hfrx : ∀ k, (∀ k', eT k' ≠ k) → k ≠ .X → k ≠ .W → T₁ k = [] :=
        fun k h hX hW => (hfr₁' k h).trans (h1k k hX hW)
      have hagF : Agree embF (Karp.Filter3.st (toks φ).reverse []) T₁ := by
        intro k
        cases k
        · show T₁ .T = ((toks φ).reverse).map (fun a => a)
          rw [show T₁ .T = (S₂ .T).map (fun a => a) from hag₁' .T, s2T]; simp [tokS]
        · show T₁ .U = ([] : List Sym).map (fun a => a)
          rw [hfrx .U (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
      obtain ⟨vF, SF, rF, hSF⟩ :=
        Karp.Filter3.run cap φ v₂ (Karp.Filter3.st (toks φ).reverse []) rfl rfl
      obtain ⟨T₁', ⟨nF, hnF, rF'⟩, hagF', hfrF⟩ := runLe_embed φF (embeds_flt cap) rF hagF
      have hnF' : nF ≤ 2 * N + 2 := by omega
      by_cases hc : (!cap || Karp.is3 φ) = true
      swap
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, φF] at rF'
        have r01 := (r₀.trans r₁).trans rF'
        have hl := lengths_le cap N hS₀l r01
        have ho : T₁' .out = [] := by
          rw [hfrF .out (by intro k h; cases k <;> simp [embF, eF] at h),
            hfr₁ .out (by intro k h; cases k <;> simp [embT, eT] at h)]
          exact h1k .out (by decide) (by decide)
        obtain ⟨n₂, hn₂, r₂⟩ := finish cap false _ _ T₁' hl ho
        have hret : ans cap (x, w) = false := by simp [ans, hdec, hc]
        rw [hret]
        refine ⟨_, ?_, r01.trans r₂⟩
        have h1 : 2 * x.length + 2 * w.length + 5 + n₁ + nF ≤ preSteps N := by
          simp only [preSteps]; nlinarith
        have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (tm cap)) h1
        omega
      simp only [hc, ↓reduceIte, φF] at rF'
      have hT1 : T₁' = T₁ := by
        funext k
        by_cases hk : ∃ k', eF k' = k
        · obtain ⟨k', rfl⟩ := hk
          have h3 := hagF' k'
          have h4 := hagF k'
          rw [hSF hc] at h3
          exact h3.trans h4.symm
        · exact hfrF k (fun k' h => hk ⟨k', h⟩)
      obtain rfl : T₁ = T₁' := hT1.symm
      have hagC : Agree embC (chkS φ w) T₁ := by
        intro k
        cases k
        · show T₁ .T = ((toks φ).reverse).map (fun a => a)
          rw [show T₁ .T = (S₂ .T).map (fun a => a) from hag₁' .T, s2T]; simp [tokS]
        · show T₁ .B = (tblStk (ents φ w)).map (fun a => a)
          rw [show T₁ .B = (S₂ .B).map (fun a => a) from hag₁' .B, s2B]; simp [tokS]
        · show T₁ .S = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .S (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
        · show T₁ .A = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .A (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
        · show T₁ .C = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .C (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
        · show T₁ .V = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .V (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
        · show T₁ .P = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .P (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
        · show T₁ .F = ([] : List Sym).map (Equiv.refl Sym)
          rw [hfrx .F (by intro k h; cases k <;> simp [eT] at h) (by decide) (by decide)]; rfl
      obtain ⟨v₃, S₃, rc⟩ := Check.run lookupSpec φ (ents φ w) vF (chkS φ w) rfl rfl rfl rfl rfl
        rfl rfl rfl
      obtain ⟨T₂, ⟨n₂, hn₂, r₂⟩, -, hfr₂⟩ := runLe_embed φC (embeds_chk cap) rc hagC
      have hφc : ∀ c : Bool, φC (.inl (if c then .yes else .no)) = .clean c := by
        intro c; cases c <;> rfl
      rw [hφc, show φC (.inl .start) = .chk (.inl .start) from rfl] at r₂
      have r012 := ((r₀.trans r₁).trans rF').trans r₂
      have hl := lengths_le cap N hS₀l r012
      have ho : T₂ .out = [] := by
        rw [hfr₂ .out (by intro k h; cases k <;> simp [embC, eC] at h),
          hfr₁ .out (by intro k h; cases k <;> simp [embT, eT] at h)]
        exact h1k .out (by decide) (by decide)
      obtain ⟨n₃, hn₃, r₃⟩ := finish cap _ _ _ T₂ hl ho
      have hret : ans cap (x, w) = checkSpec φ (ents φ w) := by
        simp only [ans, hdec, Option.map_some, Option.getD_some, hc, Bool.true_and]
      rw [hret]
      refine ⟨_, ?_, r012.trans r₃⟩
      have hn₂' : n₂ ≤ N * (8 * N + 9) + 1 := by
        refine hn₂.trans ?_
        have := Nat.mul_le_mul htN (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hbN) 9)
        have e : (toks φ).length * (8 * (tblStk (ents φ w)).length + 4 + 5) =
            (toks φ).length * (8 * (tblStk (ents φ w)).length + 9) := by
          rw [show 8 * (tblStk (ents φ w)).length + 4 + 5 =
            8 * (tblStk (ents φ w)).length + 9 by omega]
        omega
      have h1 : 2 * x.length + 2 * w.length + 5 + n₁ + nF + n₂ ≤ preSteps N := by
        simp only [preSteps]; nlinarith
      have h2 := Nat.mul_le_mul_left (TM2Composition.pushBound (tm cap)) h1
      omega

/-! ### The verifier is polynomial-time -/

theorem initList_tm (l : List G) : initList (tm cap) l = ⟨some (.ph .m1), false, initS l⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) :
    haltList (tm cap) l = ⟨none, false, update (fun _ => []) HK.out l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- The host's step bound as a polynomial in the input length. -/
noncomputable def time : Polynomial ℕ :=
  Polynomial.C (TM2Composition.pushBound (tm cap) + 1) *
      (Polynomial.C 8 * Polynomial.X ^ 2 + Polynomial.C 15 * Polynomial.X + Polynomial.C 10) +
    Polynomial.X + Polynomial.C 2

theorem preSteps_eq (N : ℕ) : preSteps N = 8 * N ^ 2 + 15 * N + 10 := by
  simp only [preSteps]; ring_nf

/-- **The `TM2` SAT verifier**: on the `x # w` input it outputs `ans cap (x, w)` within
`time cap` steps. -/
noncomputable def verifier :
    TM2ComputableInPolyTime Cslib.Complexity.DenseSAT.Verifier.pairEncode (fun b : Bool => [b])
      (fun p => ans cap p) where
  tm := tm cap
  inputAlphabet := Equiv.refl G
  outputAlphabet := Equiv.refl Bool
  time := time cap
  outputsFun := fun p => by
    obtain ⟨x, w⟩ := p
    have h := host_run cap x w
    have hn := (Classical.choose_spec h).1
    have r := (Classical.choose_spec h).2
    unfold TM2OutputsInTime
    refine { steps := Classical.choose h, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step (hprog cap)))^[_] (some (initList (tm cap) _)) =
        Option.map (haltList (tm cap)) (some _)
      erw [List.map_id, List.map_id, initList_tm, Option.map_some, haltList_tm]
      exact r
    · refine hn.trans (le_of_eq ?_)
      simp only [totalSteps, time, preSteps_eq, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring

theorem ans_false (p : List Bool × List Bool) : ans false p = (satVerifier p).ret := by
  obtain ⟨x, w⟩ := p
  rw [SatVerifier.satVerifier_ret_eq]
  simp [ans]

/-- The host's answer is polynomial-time, uncapped or capped. -/
theorem isPolyTime_ans : ComplexityTheory.IsPolyTime fun p => ans cap p :=
  tm2ComputableInPolyTime_comp (f := id) (g := fun p => ans cap p)
    Cslib.Complexity.DenseSAT.Converter.computable (verifier cap)

/-- **`satVerifier` is polynomial-time** in formal-math's canonical sense. -/
theorem isPolyTime_satVerifier :
    ComplexityTheory.IsPolyTime fun xw => (satVerifier xw).ret := by
  have h : (fun xw => (satVerifier xw).ret) = fun p => ans false p :=
    funext fun p => (ans_false p).symm
  rw [h]
  exact isPolyTime_ans false

/-- **SAT is in NP** (binary-index `satDec`, canonical classes). -/
theorem satDec_mem_NP : satDec ∈ ComplexityTheory.NP :=
  satDec_mem_NP_of_isPolyTime isPolyTime_satVerifier

/-- **Cook-Levin**: `satDec` is NP-complete for formal-math's canonical `NP`; this is the
statement of the former `theorem_wanted` `MetaMathlibExt.cook_levin_SAT_np_complete`. -/
theorem cook_levin_SAT_np_complete :
    satDec ∈ ComplexityTheory.NP ∧
      ∀ L : ComplexityTheory.DecisionProblem,
        L ∈ ComplexityTheory.NP → PolyManyOneRed L satDec :=
  Cslib.Complexity.CookLevin.Hardness.cook_levin_SAT_np_complete_of_isPolyTime
    isPolyTime_satVerifier

/-! ### 3SAT -/

theorem ans_true (x w : List Bool) :
    ans true (x, w) = (((decodeCNF x).map Karp.is3).getD false && (satVerifier (x, w)).ret) := by
  rw [SatVerifier.satVerifier_ret_eq]
  cases h : decodeCNF x <;> simp [ans, h]

/-- **3SAT is in NP**: the capped host verifies it, with witnesses no longer than the input. -/
theorem sat3Dec_mem_NP : Karp.sat3Dec ∈ ComplexityTheory.NP := by
  refine ⟨Polynomial.X, fun p => ans true p, isPolyTime_ans true, fun x => ?_⟩
  have hv := satVerifier_verifies x
  constructor
  · intro h
    simp only [Karp.sat3Dec, decide_eq_true_eq] at h
    obtain ⟨φ, rfl, h3, hs⟩ := h
    obtain ⟨w, hw, hr⟩ := hv.1 ((Cslib.Complexity.DenseSAT.ToBinary.satDec_encodeCNF φ).2 hs)
    refine ⟨w, hw, ?_⟩
    show ans true (encodeCNF φ, w) = true
    rw [ans_true, decodeCNF_encodeCNF]
    simp [h3, hr]
  · rintro ⟨w, hw, hr⟩
    change ans true (x, w) = true at hr
    rw [ans_true] at hr
    cases hdec : decodeCNF x with
    | none => simp [hdec] at hr
    | some φ =>
        simp only [hdec, Option.map_some, Option.getD_some, Bool.and_eq_true] at hr
        obtain rfl := (decodeCNF_eq_some_iff x φ).1 hdec
        have hs := (Cslib.Complexity.DenseSAT.ToBinary.satDec_encodeCNF φ).1 (hv.2 ⟨w, hw, hr.2⟩)
        simp only [Karp.sat3Dec, decide_eq_true_eq]
        exact ⟨φ, rfl, hr.1, hs⟩

/-- Moved to `SatVerifier.toks_length_le` (`SatVerifierSpec`). -/
@[deprecated SatVerifier.toks_length_le (since := "2026-10-15")]
theorem toks_length_le (φ : CNF) : (toks φ).length ≤ (encodeCNF φ).length :=
  SatVerifier.toks_length_le φ

/-- Moved to `SatVerifier.clauseToks_length_le` (`SatVerifierSpec`). -/
@[deprecated SatVerifier.clauseToks_length_le (since := "2026-10-15")]
theorem clauseToks_length_le (C : CNFClause) :
    (clauseToks C).length ≤ (encodeClause C).length :=
  SatVerifier.clauseToks_length_le C

/-- Moved to the instance `SatVerifier.Sym.instFintype` (`SatVerifierSpec`); kept as a
definition, not an instance, so instance search sees one `Fintype Sym`. -/
@[deprecated SatVerifier.Sym.instFintype (since := "2026-10-15")]
abbrev Sym.instFintype : Fintype Sym := SatVerifier.Sym.instFintype

end Cslib.Complexity.SatVerifier.Machine
