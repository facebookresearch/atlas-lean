/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Hardness.Walk
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import Mathlib.Data.Nat.Choose.Basic

/-! # Parsing and validating the unary CLIQUE header and adjacency length -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.CliquePrepare

open Turing Function MetaMathlibExt.TM2Program
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.Karp Cslib.CookLevin
open Cslib.Complexity.SatVerifier (Sym)

/- The prep pass retains unary `k`, `n` and `choose k 2` and the reversed adjacency bits. -/
inductive K
  | input | matrix | sizeK | n | originalSize | pairSize | threshold | work | aux | t1 | t2
  deriving DecidableEq

instance : Fintype K := Fintype.ofList
  [.input, .matrix, .sizeK, .n, .originalSize, .pairSize, .threshold, .work, .aux, .t1, .t2]
  (by intro k; cases k <;> decide)

/- Only the input and reversed matrix carry raw bits. -/
@[reducible] def Γ : K → Type
  | .input | .matrix => Bool
  | _ => Sym

/- Separate calls of the triangle loop compute the expected length and the threshold. -/
inductive Lab
  | rk | rn | reverse | copyN | restoreN | copyK | restoreK
  | triangle (threshold : Bool) | add (threshold : Bool) | restore (threshold : Bool)
  | cmp | cmp1 (o : Ordering) | cmp2 (o : Ordering) | good | bad
  deriving DecidableEq

instance : Fintype Lab := Fintype.ofList
  [.rk, .rn, .reverse, .copyN, .restoreN, .copyK, .restoreK, .triangle false, .triangle true,
    .add false, .add true, .restore false, .restore true, .cmp, .cmp1 .lt, .cmp1 .eq, .cmp1 .gt,
    .cmp2 .lt, .cmp2 .eq, .cmp2 .gt, .good, .bad]
  (by
    intro l
    cases l with
    | triangle b | add b | restore b => cases b <;> decide
    | cmp1 o | cmp2 o => cases o <;> decide
    | _ => decide)

/- This stack holds a unary counter. -/
def counter (b : Bool) : K := if b then .threshold else .pairSize

/- The unit of either triangle output. -/
def unit (b : Bool) : Γ (counter b) := by cases b <;> exact EmitSS.U

/- One step of a unary reader: preserve the rest after a zero and reject missing terminators. -/
def readU (a : K) (u : Γ a) (self next : Lab) : TM2.Stmt Γ Lab Bool :=
  .peek .input (fun _ o => o.isSome) <| .branch id
    (.pop .input (fun _ o => o.getD false) <| .branch id
      (.push a (fun _ => u) (.goto fun _ => self)) (.goto fun _ => next))
    (.goto fun _ => .bad)

/- Only an exact pair-bit count qualifies for emission. -/
def cmpOut (o : Ordering) : Lab := if o = .eq then .copyK else .bad

/- Parser, bit reversal, triangular counts, and exact comparison. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .rk => readU .sizeK EmitSS.U .rk .rn
  | .rn => readU .n EmitSS.U .rn .reverse
  | .reverse => splitB .input .matrix .originalSize some id (fun _ => EmitSS.U) .reverse .copyN
  | .copyN => xfer .n [⟨.work, EmitSS.U⟩, ⟨.aux, EmitSS.U⟩] .copyN .restoreN
  | .restoreN => xfer .aux [⟨.n, EmitSS.U⟩] .restoreN (.triangle false)
  | .copyK => xfer .sizeK [⟨.work, EmitSS.U⟩, ⟨.aux, EmitSS.U⟩] .copyK .restoreK
  | .restoreK => xfer .aux [⟨.sizeK, EmitSS.U⟩] .restoreK (.triangle true)
  | .triangle b => decr .work (if b then .good else .cmp) (.add b)
  | .add b => xfer .work [⟨counter b, unit b⟩, ⟨.aux, EmitSS.U⟩] (.add b) (.restore b)
  | .restore b => xfer .aux [⟨.work, EmitSS.U⟩] (.restore b) (.triangle b)
  | .cmp => cmpStep .originalSize .pairSize .t1 .t2 EmitSS.U EmitSS.U .cmp
      (.cmp1 .lt) (.cmp1 .eq) (.cmp1 .gt)
  | .cmp1 o => xfer .t1 [⟨.originalSize, EmitSS.U⟩] (.cmp1 o) (.cmp2 o)
  | .cmp2 o => xfer .t2 [⟨.pairSize, EmitSS.U⟩] (.cmp2 o) (cmpOut o)
  | .good | .bad => .halt

private theorem read_some {a : K} {u : Γ a} {self next : Lab}
    (hp : prog self = readU a u self next) (ha : a ≠ .input)
    (n m : ℕ) (r : List Bool) (v : Bool) (S : (k : K) → List (Γ k))
    (hi : S .input = List.replicate n true ++ false :: r) (hc : S a = cnt u m) :
    Run prog (n + 1) ⟨some self, v, S⟩
      ⟨some next, false, update (update S .input r) a (cnt u (n + m))⟩ := by
  induction n generalizing m v S with
  | zero =>
    have hs : update (update S K.input r) a (cnt u (0 + m)) = update S K.input r := by
      have hs' : (update S K.input r) a = cnt u m := by rw [update_of_ne ha, hc]
      rw [Nat.zero_add, ← hs', update_eq_self]
    have hh : S .input = false :: r := hi
    rw [hs]
    apply Run.single
    simp [hp, readU, TM2.stepAux, hh]
  | succ n ih =>
    let r' := List.replicate n true ++ false :: r
    let S' := update (update S K.input r') a (cnt u (m + 1))
    have hh : S .input = true :: r' := hi
    have r₁ : Run prog 1 ⟨some self, v, S⟩ ⟨some self, true, S'⟩ := by
      apply Run.single
      simp [hp, readU, TM2.stepAux, hh, S', ha, hc, cnt_succ]
    have r₂ := ih (m + 1) true S' (by simp [S', ha.symm, r']) (by simp [S'])
    have hf : update (update S' K.input r) a (cnt u (n + (m + 1))) =
        update (update S K.input r) a (cnt u (n + 1 + m)) := by
      have hnm : n + (m + 1) = n + 1 + m := by omega
      rw [hnm]
      funext k
      by_cases hki : k = .input
      · subst k
        simp [ha.symm]
      by_cases hka : k = a
      · subst k
        simp
      simp [S', hki, hka]
    rw [hf] at r₂
    exact (r₁.trans r₂).of_eq (by omega)

private theorem read_none {a : K} {u : Γ a} {self next : Lab}
    (hp : prog self = readU a u self next) (ha : a ≠ .input) (x : List Bool)
    (hx : readUnaryLength x = none) (v : Bool) (S : (k : K) → List (Γ k)) (hi : S .input = x) :
    ∃ w T, Run prog (x.length + 1) ⟨some self, v, S⟩ ⟨some .bad, w, T⟩ := by
  induction x generalizing v S with
  | nil => exact ⟨false, S, Run.single (by simp [hp, readU, TM2.stepAux, hi])⟩
  | cons b x ih =>
    cases b with
    | false => simp [readUnaryLength] at hx
    | true =>
      have hn : readUnaryLength x = none := by simpa [readUnaryLength] using hx
      let S' := update (update S K.input x) a (u :: S a)
      have r₁ : Run prog 1 ⟨some self, v, S⟩ ⟨some self, true, S'⟩ := by
        apply Run.single
        simp [hp, readU, TM2.stepAux, hi, S', ha]
      obtain ⟨w, T, h₂⟩ := ih hn true S' (by simp [S', ha.symm])
      exact ⟨w, T, (r₁.trans h₂).of_eq (by simp; omega)⟩

/- The triangle loop performs the same unary transfer as `EmitSS.tri_run`,
with two continuations and an explicit contract for the cleared source. -/
theorem triangle (b : Bool) (n p : ℕ) (v : Bool) (S : (k : K) → List (Γ k))
    (hw : S .work = cnt EmitSS.U n) (hp : S (counter b) = cnt (unit b) p) (ha : S .aux = []) :
    ∃ w T, Run prog ((n + 1) ^ 2) ⟨some (.triangle b), v, S⟩
      ⟨some (if b then .good else .cmp), w, T⟩ ∧ T .work = [] ∧
      T (counter b) = cnt (unit b) (p + EmitSS.tri n) ∧
      ∀ j, j ≠ .work → j ≠ counter b → T j = S j := by
  have hwc : K.work ≠ counter b := by cases b <;> decide
  have hac : K.aux ≠ counter b := by cases b <;> decide
  induction n generalizing p v S with
  | zero =>
    refine ⟨Flag.tag false, S, decr_run_zero (M := prog) (self := .triangle b) rfl v hw,
      hw, ?_, fun _ _ _ => rfl⟩
    simpa only [EmitSS.tri, Nat.add_zero] using hp
  | succ n ih =>
    let S₁ := update S K.work (cnt EmitSS.U n)
    let S₂ := update S₁ (counter b) (cnt (unit b) (n + p))
    have f₁ : Run prog 1 ⟨some (.triangle b), v, S⟩ ⟨some (.add b), true, S₁⟩ :=
      decr_run_cnt (M := prog) (self := .triangle b) rfl v hw
    have f₂ : Run prog (2 * n + 2) ⟨some (.add b), true, S₁⟩
        ⟨some (.triangle b), false, S₂⟩ :=
      copy_run (M := prog) (l₁ := .add b) (l₂ := .restore b) rfl rfl hwc (by decide) hac.symm
        n p true S₁ (by simp [S₁]) (by simpa [S₁, hwc.symm] using hp) (by simpa [S₁] using ha)
    obtain ⟨w, T, f₃, hTw, hTp, hTf⟩ := ih (n + p) false S₂
      (by simp [S₂, S₁, hwc]) (by simp [S₂]) (by simp [S₂, S₁, hac, ha])
    refine ⟨w, T, ((f₁.trans f₂).trans f₃).of_eq (by ring), hTw, ?_, ?_⟩
    · rw [hTp, EmitSS.tri]; congr 1; omega
    · intro j hj hq
      rw [hTf j hj hq]
      simp [S₂, S₁, hj, hq]

/- The successful header-and-bit-count check. -/
def parse (x : List Bool) : Option (ℕ × ℕ × List Bool) :=
  (decodeKG x).filter fun q => q.2.2.length == (pairs q.2.1).length

/- Input-only initial stacks. -/
def init (x : List Bool) : (k : K) → List (Γ k)
  | .input => x
  | _ => []

/- The parser rejects exactly the malformed raw CLIQUE inputs. On success, all numeric output
counters are bounded by the raw input length or its square, not by a binary input value. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ w T, RunLe prog (20 * (x.length + 1) ^ 2) ⟨some .rk, v, init x⟩
      ⟨some (if (parse x).isSome then .good else .bad), w, T⟩ ∧
      ∀ k n bits, parse x = some (k, n, bits) →
        T .sizeK = cnt EmitSS.U k ∧ T .n = cnt EmitSS.U n ∧
        T .threshold = cnt EmitSS.U (k.choose 2) ∧ T .matrix = bits.reverse := by
  cases h₀ : readUnaryLength x with
  | none =>
    obtain ⟨w, T, h⟩ := read_none (self := .rk) rfl (by decide) x h₀ v (init x) rfl
    have hn : parse x = none := by simp [parse, decodeKG, h₀]
    refine ⟨w, T, ?_, ?_⟩
    · simpa only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
        h.le (show x.length + 1 ≤ 20 * (x.length + 1) ^ 2 by nlinarith)
    · simp [hn]
  | some p =>
    obtain ⟨k, r⟩ := p
    have he := (readUnaryLength_eq_some_iff x k r).mp h₀
    let S₁ := update (update (init x) K.input r) K.sizeK (cnt EmitSS.U k)
    have h₁ : Run prog (k + 1) ⟨some .rk, v, init x⟩ ⟨some .rn, false, S₁⟩ :=
      read_some (self := .rk) rfl (by decide) k 0 r v (init x) he rfl
    cases h₁d : readUnaryLength r with
    | none =>
      obtain ⟨w, T, h⟩ := read_none (self := .rn) rfl (by decide) r h₁d false S₁ (by simp [S₁])
      have hn : parse x = none := by simp [parse, decodeKG, h₀, h₁d]
      have hx : x.length = k + 1 + r.length := by rw [he]; simp; omega
      refine ⟨w, T, ?_, ?_⟩
      · simpa only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
          (h₁.trans h).le (show k + 1 + (r.length + 1) ≤ 20 * (x.length + 1) ^ 2 by nlinarith)
      · simp [hn]
    | some q =>
      obtain ⟨n, bits⟩ := q
      have hr := (readUnaryLength_eq_some_iff r n bits).mp h₁d
      have hd : decodeKG x = some (k, n, bits) := by simp [decodeKG, h₀, h₁d]
      have hlen : x.length = k + n + bits.length + 2 := by rw [he, hr]; simp; omega
      let S₂ := update (update S₁ K.input bits) K.n (cnt EmitSS.U n)
      have h₂ : Run prog (n + 1) ⟨some .rn, false, S₁⟩ ⟨some .reverse, false, S₂⟩ :=
        read_some (self := .rn) rfl (by decide) n 0 bits false S₁
          (by simp [S₁, hr]) (by simp [S₁, init])
      obtain ⟨S₃, h₃, -, hbits, hsize, hf₃⟩ := splitB_run (M := prog) (self := .reverse)
        (a := .input) (b := .matrix) (c := .originalSize) rfl (by decide) (by decide) (by decide)
        id (fun _ => rfl) bits [] false S₂ rfl (by simp [S₂])
      have hcopy := copy_run (M := prog) (l₁ := .copyN) (l₂ := .restoreN) (next := .triangle false)
        rfl rfl (by decide) (by decide) (by decide) n 0 false S₃
        (by rw [hf₃ _ (by decide) (by decide) (by decide)]; simp [S₂])
        (by rw [hf₃ _ (by decide) (by decide) (by decide)]; simp [S₂, S₁, init])
        (by rw [hf₃ _ (by decide) (by decide) (by decide)]; simp [S₂, S₁, init])
      let S₄ := update S₃ K.work (cnt EmitSS.U n)
      obtain ⟨z, S₅, ht₁, hwork, htri, hframe⟩ := triangle false n 0 false S₄ (by simp [S₄])
        (by
          change S₄ .pairSize = []
          simp (disch := decide) [S₄, hf₃, S₂, S₁, init])
        (by simp (disch := decide) [S₄, hf₃, S₂, S₁, init])
      change S₅ .pairSize = cnt EmitSS.U (0 + EmitSS.tri n) at htri
      have hcnt : S₅ .originalSize = cnt EmitSS.U bits.length := by
        rw [hframe _ (by decide) (by decide)]
        simp [S₄, hsize, S₂, S₁, init, cnt]
      have hc₁ : S₅ .t1 = [] := by
        rw [hframe _ (by decide) (by decide)]
        simp (disch := decide) [S₄, hf₃, S₂, S₁, init]
      have hc₂ : S₅ .t2 = [] := by
        rw [hframe _ (by decide) (by decide)]
        simp (disch := decide) [S₄, hf₃, S₂, S₁, init]
      have hc := cmp_run (M := prog) (self := .cmp) (r := Lab.cmp1) (rB := Lab.cmp2)
        (out := cmpOut) rfl (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) bits.length (EmitSS.tri n) z S₅ hcnt
        (by simpa only [Nat.zero_add] using htri)
        hc₁ hc₂
      have hwalk := (((((h₁.trans h₂).trans h₃).trans hcopy).trans ht₁).trans hc).le le_rfl
      have hmin := Nat.min_le_left bits.length (EmitSS.tri n)
      by_cases hvalid : bits.length = (pairs n).length
      · have hyes : cmpOut (compare bits.length (EmitSS.tri n)) = .copyK := by
          rw [hvalid, EmitSS.length_pairs_eq_tri, Nat.compare_eq_eq.mpr rfl]
          rfl
        rw [hyes] at hwalk
        have haux : S₅ .aux = [] := by
          rw [hframe _ (by decide) (by decide)]
          simp (disch := decide) [S₄, hf₃, S₂, S₁, init]
        have hk : S₅ .sizeK = cnt EmitSS.U k := by
          rw [hframe _ (by decide) (by decide)]
          simp (disch := decide) [S₄, hf₃, S₂, S₁]
        have hck := copy_run (M := prog) (l₁ := .copyK) (l₂ := .restoreK)
          (next := .triangle true) rfl rfl (by decide) (by decide) (by decide)
          k 0 false S₅ hk hwork haux
        let S₆ := update S₅ K.work (cnt EmitSS.U k)
        obtain ⟨w, T, hm, -, hth, ff⟩ := triangle true k 0 false S₆ (by simp [S₆])
          (by
            change S₆ .threshold = []
            rw [show S₆ .threshold = S₅ .threshold by simp [S₆], hframe _ (by decide) (by decide)]
            simp (disch := decide) [S₄, hf₃, S₂, S₁, init])
          (by simp [S₆, haux])
        have hp : parse x = some (k, n, bits) := by simp [parse, hd, hvalid]
        refine ⟨w, T, ?_, ?_⟩
        · rw [hp]
          apply ((hwalk.trans (hck.le le_rfl)).trans (hm.le le_rfl)).mono
          split <;> nlinarith
        · intro k' n' bits' hh
          rw [hp] at hh
          obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh) |>.imp_right Prod.mk.inj
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [ff _ (by decide) (by decide)]
            simpa [S₆] using hk
          · rw [ff _ (by decide) (by decide)]
            rw [show S₆ .n = S₅ .n by simp [S₆], hframe _ (by decide) (by decide)]
            simp (disch := decide) [S₄, hf₃, S₂]
          · have ht := EmitSS.length_pairs_eq_tri k
            rw [length_pairs, ← Nat.choose_two_right] at ht
            change T .threshold = cnt EmitSS.U (0 + EmitSS.tri k) at hth
            simpa only [Nat.zero_add, ← ht] using hth
          · rw [ff _ (by decide) (by decide)]
            rw [show S₆ .matrix = S₅ .matrix by simp [S₆], hframe _ (by decide) (by decide)]
            simpa [S₄, S₂, S₁, init] using hbits
      · have hq : bits.length ≠ EmitSS.tri n := by simpa [EmitSS.length_pairs_eq_tri] using hvalid
        have hno : cmpOut (compare bits.length (EmitSS.tri n)) = .bad := by
          simp [cmpOut, hq]
        rw [hno] at hwalk
        have hp : parse x = none := by simp [parse, hd, hvalid]
        refine ⟨false, S₅, ?_, ?_⟩
        · rw [hp]
          apply hwalk.mono
          split <;> nlinarith
        · simp [hp]

end Cslib.Complexity.DensestKSubgraph.Internal.CliquePrepare
