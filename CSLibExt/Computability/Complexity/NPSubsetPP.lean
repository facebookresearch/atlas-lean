/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.BoolClosure

/-!
# NP is contained in PP

Every `NP` language is in `PP`: guess a witness at random, accept if it verifies, otherwise
accept with probability `1/2`; the acceptance probability is `> 1/2` exactly on yes-instances.

Equivalently, the first random bit reserves one half of the random strings for unconditional
acceptance. In the other half, ignore leading zeroes up to and including a `true` marker; the
suffix is an NP witness. This represents all witness lengths up to the NP bound at one exact
coin length. A string with no marker decodes to the empty witness.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPP

open Cslib.Complexity Cslib.Complexity.Classes Cslib.Complexity.DenseSAT
open ComplexityTheory Function TM2Program Turing

private def decodeWitness : List Bool → List Bool
  | [] => []
  | false :: r => decodeWitness r
  | true :: r => r

private theorem length_decodeWitness_le (r : List Bool) :
    (decodeWitness r).length ≤ r.length - 1 := by
  induction r with
  | nil => simp [decodeWitness]
  | cons b r ih =>
    cases b
    · simpa [decodeWitness] using ih.trans (Nat.sub_le r.length 1)
    · simp [decodeWitness]

private theorem decodeWitness_encode (n : ℕ) (w : List Bool) :
    decodeWitness (List.replicate n false ++ true :: w) = w := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append, decodeWitness] using ih

private def prepare (a q : List Bool × List Bool) : List Bool × List Bool :=
  if q.2.headD false then a else (q.1, decodeWitness q.2.tail)

/-! ### Polynomial-time preparation of the verifier input -/

private inductive Lab
  | stash | removeSep | coin | padding | restoreSep | restore | clean | emit | done
  deriving DecidableEq

private instance : Fintype Lab where
  elems := ⟨↑[Lab.stash, .removeSep, .coin, .padding, .restoreSep, .restore, .clean, .emit, .done],
    by decide⟩
  complete := fun l => by cases l <;> decide

@[reducible] private def Γ : Bool → Type
  | false => Verifier.G
  | true => Bool

private abbrev tagW (b : Bool) : Verifier.G := .inr (some b)

private def prog (a : List Bool × List Bool) : Lab → TM2.Stmt Γ Lab Bool
  | .stash => moveB false true Host.dX id .stash .removeSep
  | .removeSep => .pop false (fun _ _ => false) (.goto fun _ => .coin)
  | .coin => .pop false (fun _ o => (o.bind Host.dW).getD false)
      (.goto fun b => if b then .clean else .padding)
  | .padding => .pop false (fun _ o => (o.bind Host.dW) == some false)
      (.goto fun b => if b then .padding else .restoreSep)
  | .restoreSep => .push false (fun _ => .inr none) (.goto fun _ => .restore)
  | .restore => moveB true false some Sum.inl .restore .done
  | .clean => cleanS [false, true] .clean .emit
  | .emit => emitR false (Verifier.pairEncode a) .done
  | .done => .peek true (fun _ _ => false) .halt

private abbrev tm (a : List Bool × List Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ := Γ
  Λ := Lab
  main := .stash
  σ := Bool
  initialState := false
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := prog a

private def stk (i : List Verifier.G) (s : List Bool) : ∀ k, List (Γ k)
  | false => i
  | true => s

@[simp] private theorem update_stk (i j : List Verifier.G) (s : List Bool) :
    update (stk i s) false j = stk j s := by
  funext k
  cases k <;> rfl

private theorem stash_run (a : List Bool × List Bool) (x r : List Bool) :
    ∃ v, Run (prog a) (x.length + 1)
      ⟨some .stash, false, stk (Verifier.pairEncode (x, r)) []⟩
      ⟨some .removeSep, v, stk (.inr none :: r.map tagW) x.reverse⟩ := by
  obtain ⟨v, S, h, hi, hs, _⟩ := moveB_run (M := prog a) (a := false) (b := true)
    (d := Host.dX) (g := id) (self := .stash) (next := .removeSep) rfl (by decide)
    x (x.map Sum.inl) (.inr none :: r.map tagW) false
    (stk (Verifier.pairEncode (x, r)) []) rfl
    (by simp [IsBitBlock, Host.dX, Function.comp_def]) rfl
  have hS : S = stk (.inr none :: r.map tagW) x.reverse := by
    funext k
    cases k
    · exact hi
    · simpa [stk] using hs
  exact ⟨v, hS ▸ h⟩

private theorem padding_run (a : List Bool × List Bool) (r s : List Bool) (v : Bool) :
    RunLe (prog a) (r.length + 1) ⟨some .padding, v, stk (r.map tagW) s⟩
      ⟨some .restoreSep, false, stk ((decodeWitness r).map tagW) s⟩ := by
  induction r generalizing v with
  | nil =>
    apply Run.le (n := 1) _ le_rfl
    exact Run.single (by simp [prog, TM2.stepAux, stk, decodeWitness])
  | cons b r ih =>
    cases b
    · have h : Run (prog a) 1 ⟨some .padding, v, stk ((false :: r).map tagW) s⟩
          ⟨some .padding, true, stk (r.map tagW) s⟩ :=
        Run.single (by simp [prog, TM2.stepAux, stk, Host.dW])
      exact ((h.le le_rfl).trans (ih true)).mono (by simp; omega)
    · apply Run.le (n := 1) _ (by simp)
      exact Run.single (by simp [prog, TM2.stepAux, stk, Host.dW, decodeWitness])

private theorem restore_run (a : List Bool × List Bool) (x w : List Bool) :
    RunLe (prog a) (x.length + 3)
      ⟨some .restoreSep, false, stk (w.map tagW) x.reverse⟩
      ⟨none, false, stk (Verifier.pairEncode (x, w)) []⟩ := by
  have hSep : Run (prog a) 1 ⟨some .restoreSep, false, stk (w.map tagW) x.reverse⟩
      ⟨some .restore, false, stk (.inr none :: w.map tagW) x.reverse⟩ :=
    Run.single (by simp [prog, TM2.stepAux, stk])
  obtain ⟨v, S, h, hs, hi, _⟩ := moveB_run (M := prog a) (a := true) (b := false)
    (d := some) (g := Sum.inl) (self := .restore) (next := .done) rfl (by decide)
    x.reverse x.reverse [] false (stk (.inr none :: w.map tagW) x.reverse)
    (by simp [stk]) (by simp [IsBitBlock]) rfl
  have hS : S = stk (Verifier.pairEncode (x, w)) [] := by
    funext k
    cases k
    · simpa [stk, Verifier.pairEncode, List.map_reverse] using hi
    · exact hs
  have hDone : Run (prog a) 1 ⟨some .done, v, stk (Verifier.pairEncode (x, w)) []⟩
      ⟨none, false, stk (Verifier.pairEncode (x, w)) []⟩ := Run.single rfl
  exact (((hSep.trans (hS ▸ h)).trans hDone).le (by simp; omega))

private theorem accept_run (a : List Bool × List Bool) (r s : List Bool) :
    RunLe (prog a) (r.length + s.length + 3)
      ⟨some .clean, true, stk (r.map tagW) s⟩
      ⟨none, false, stk (Verifier.pairEncode a) []⟩ := by
  have hClean := clean_run (M := prog a) (ks := [false, true]) (self := .clean) (next := .emit)
    rfl (by decide) (r.length + s.length) true (stk (r.map tagW) s) (by
      intro k _
      cases k <;> simp [stk])
  have hs : (fun k => if k ∈ [false, true] then [] else stk (r.map tagW) s k) = stk [] [] := by
    funext k
    cases k <;> rfl
  rw [hs] at hClean
  have hEmit : Run (prog a) 1 ⟨some .emit, false, stk [] []⟩
      ⟨some .done, false, stk (Verifier.pairEncode a) []⟩ := by
    simpa [stk] using
      (emit_run (M := prog a) (self := .emit) (next := .done) (k := false)
        (xs := (Verifier.pairEncode a).reverse) rfl false (stk [] []))
  have hDone : Run (prog a) 1 ⟨some .done, false, stk (Verifier.pairEncode a) []⟩
      ⟨none, false, stk (Verifier.pairEncode a) []⟩ := Run.single rfl
  exact (hClean.trans ((hEmit.trans hDone).le le_rfl)).mono (by omega)

private theorem prepare_run (a : List Bool × List Bool) (x r : List Bool) :
    RunLe (tm a).m (2 * (x.length + r.length) + 7)
      (initList (tm a) (Verifier.pairEncode (x, r)))
      (haltList (tm a) (Verifier.pairEncode (prepare a (x, r)))) := by
  rw [Host.initList_eq, Host.haltList_eq]
  have hs (i : List Verifier.G) :
      update (fun k : Bool => ([] : List (Γ k))) false i = stk i [] := by
    funext k
    cases k <;> rfl
  simp only [tm, hs]
  obtain ⟨v, hStash⟩ := stash_run a x r
  have hSep : Run (prog a) 1 ⟨some .removeSep, v, stk (.inr none :: r.map tagW) x.reverse⟩
      ⟨some .coin, false, stk (r.map tagW) x.reverse⟩ :=
    Run.single (by simp [prog, TM2.stepAux, stk])
  have hCoin : Run (prog a) 1 ⟨some .coin, false, stk (r.map tagW) x.reverse⟩
      ⟨some (if r.headD false then .clean else .padding), r.headD false,
        stk (r.tail.map tagW) x.reverse⟩ := by
    cases r with
    | nil => exact Run.single (by simp [prog, TM2.stepAux, stk])
    | cons b r => cases b <;> exact Run.single (by simp [prog, TM2.stepAux, stk, Host.dW])
  have hStart := (hStash.trans hSep).trans hCoin
  have hTail : r.tail.length ≤ r.length := by simp
  cases h : r.headD false
  · rw [h] at hStart
    simp only [prepare, h, Bool.false_eq_true, ↓reduceIte]
    have hRun := (hStart.le le_rfl).trans ((padding_run a r.tail x.reverse false).trans
      (restore_run a x (decodeWitness r.tail)))
    exact hRun.mono (by omega)
  · rw [h] at hStart
    simp only [prepare, h, ↓reduceIte]
    have hRun := (hStart.le le_rfl).trans (accept_run a r.tail x.reverse)
    exact hRun.mono (by simp; omega)

private noncomputable def prepareComputable (a : List Bool × List Bool) :
    TM2ComputableInPolyTime Verifier.pairEncode Verifier.pairEncode (prepare a) where
  tm := tm a
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  outputsFun := fun ⟨x, r⟩ => by
    let h := prepare_run a x r
    let n := Classical.choose h
    have ⟨hn, hrun⟩ := Classical.choose_spec h
    refine ⟨⟨n, ?_⟩, ?_⟩
    · change Run (tm a).m n (initList (tm a) ((Verifier.pairEncode (x, r)).map id))
        (haltList (tm a) ((Verifier.pairEncode (prepare a (x, r))).map id))
      erw [List.map_id, List.map_id]
      exact hrun
    · change n ≤ (Polynomial.C 2 * Polynomial.X + Polynomial.C 5).eval
        (Verifier.pairEncode (x, r)).length
      simp [Verifier.pairEncode]
      omega

private theorem isPolyTime_prepare (a : List Bool × List Bool) : IsPolyTime (prepare a) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp Converter.computable (prepareComputable a)
  exact tm2ComputableInPolyTime_comp h ToCanonical.computable

/-! ### Counting the two halves of the random strings -/

private theorem majority_of_extra_coin {L : DecisionProblem} (p : Polynomial ℕ)
    (R : List Bool × List Bool → Bool) (hR : IsPolyTime R)
    (htrue : ∀ x r, R (x, true :: r) = true)
    (hfalse : ∀ x, L x = true ↔ ∃ r : List Bool, r.length = p.eval x.length ∧
      R (x, false :: r) = true) : L ∈ PP := by
  refine ⟨p + 1, R, hR, fun x => ?_⟩
  classical
  rw [Polynomial.eval_add, Polynomial.eval_one]
  let m := p.eval x.length
  let A : Set (Fin (m + 1) → Bool) := {r | R (x, List.ofFn r) = true}
  let H : Set (Fin (m + 1) → Bool) := Set.range (fun r : Fin m → Bool => Fin.cons true r)
  change (L x = true → 2 ^ (m + 1) < 2 * A.ncard) ∧
    (L x = false → 2 * A.ncard ≤ 2 ^ (m + 1))
  have hH : H.ncard = 2 ^ m := by
    have hinj : Injective (fun r : Fin m → Bool => (Fin.cons true r : Fin (m + 1) → Bool)) :=
      Fin.cons_right_injective (α := fun _ : Fin (m + 1) => Bool) true
    change (Set.range _).ncard = _
    rw [Set.ncard_range_of_injective hinj]
    simp
  have hHA : H ⊆ A := by
    rintro _ ⟨r, rfl⟩
    change R (x, List.ofFn (Fin.cons true r)) = true
    simpa [List.ofFn_succ] using htrue x (List.ofFn r)
  rw [pow_succ, mul_comm (2 ^ m) 2, ← hH]
  constructor
  · intro hx
    obtain ⟨r, hr, ha⟩ := (hfalse x).mp hx
    let t : Fin m → Bool := fun i => r[i.val]'(by rw [hr]; exact i.isLt)
    have ht : List.ofFn t = r := by
      apply List.ext_get
      · simpa using hr.symm
      · intro i hi hj
        simp [t]
    let s : Fin (m + 1) → Bool := Fin.cons false t
    have hs : s ∈ A := by
      change R (x, List.ofFn (Fin.cons false t)) = true
      simpa [List.ofFn_succ, ht] using ha
    have hsH : s ∉ H := by
      rintro ⟨u, hu⟩
      have he := congrFun hu (0 : Fin (m + 1))
      simp [s] at he
    have hlt : H.ncard < A.ncard :=
      Set.ncard_lt_ncard (lt_of_le_of_ne hHA fun he => hsH (he.symm ▸ hs))
    omega
  · intro hx
    suffices he : A = H by simp [he]
    apply Set.Subset.antisymm _ hHA
    intro r hr
    have hr' : R (x, List.ofFn r) = true := hr
    cases h : r 0 with
    | true =>
      exact ⟨Fin.tail r, by simpa only [← h] using Fin.cons_self_tail r⟩
    | false =>
      exfalso
      have hx' := (hfalse x).mpr ⟨List.ofFn (fun i : Fin m => r i.succ), by simp [m], by
        simpa [List.ofFn_succ, h] using hr'⟩
      simp [hx] at hx'

/-- **NP is contained in PP.** Every decision problem in NP also belongs to PP, the class of
decision problems decided in probabilistic polynomial time with unbounded error.

Source: J. Gill, "Computational complexity of probabilistic
Turing machines" (1977). -/
public theorem np_subset_pp :
    MetaMathlibExt.ComplexityTheory.NP ⊆ PP := by
  intro L hL
  obtain ⟨p, V, hV, hLV⟩ := hL
  by_cases h : ∃ x, L x = true
  · obtain ⟨x₀, hx₀⟩ := h
    obtain ⟨w₀, _, hw₀⟩ := (hLV x₀).mp hx₀
    -- Hard-wire one accepting pair so both branches can use the same verifier.
    let a := (x₀, w₀)
    refine majority_of_extra_coin (p + 1) (V ∘ prepare a) ((isPolyTime_prepare a).comp hV)
      (fun x r => by simpa [prepare, a] using hw₀) (fun x => ?_)
    rw [Polynomial.eval_add, Polynomial.eval_one]
    simp only [Function.comp_apply, prepare, List.headD_cons, Bool.false_eq_true, ↓reduceIte,
      List.tail_cons]
    constructor
    · intro hx
      obtain ⟨w, hw, hv⟩ := (hLV x).mp hx
      refine ⟨List.replicate (p.eval x.length - w.length) false ++ true :: w, ?_, ?_⟩
      · simp; omega
      · simpa only [decodeWitness_encode] using hv
    · rintro ⟨r, hr, hv⟩
      exact (hLV x).mpr ⟨decodeWitness r, by simpa [hr] using length_decodeWitness_le r, hv⟩
  · refine majority_of_extra_coin 0 (fun q => q.2.headD false) (isPolyTime_heads fun b _ => b)
      (fun _ _ => rfl) (fun x => ?_)
    simp [show L x ≠ true from fun hx => h ⟨x, hx⟩]

end MetaMathlibExt.Complexity.KeyTheorems.NPSubsetPP
