/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recursive functions are Turing-computable
-/
module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.PartrecBasis
public import Mathlib.Data.Num.Lemmas

/-!
# Recursive functions are Turing-computable

The forward half of the Turing–Kleene equivalence for Mathlib's bundled finite multi-stack
machines (the TM2 model): every `Computable` function `f : ℕ → ℕ` is computed by a `FinTM2`
under the binary encoding `Computability.encodeNat`.

Mathlib's `Turing.PartrecToTM2.tr` is a TM2 machine that evaluates any
`ToPartrec.Code` (`tr_eval`), but its label type is infinite and its input and output are
lists of naturals in the alphabet `Γ'`.  `fwdTM c` wraps it into a `FinTM2`:

* stacks `K' ⊕ Bool`: the four stacks of `tr`, an input stack of bits and an output stack of
  bits;
* labels `Phase ⊕ {l // l ∈ codeSupp c halt}`: finitely many labels of `tr`, all it can
  reach (`tr_supports`), and five labels for the adapters;
* a pre-phase copies the input bits onto `tr`'s main stack as `trList [n]`, the main phase
  runs `tr` with `halt` redirected to the post-phase (`restrict`), and the post-phase copies
  `trList [f n]` back as bits.

## Main results

- `tm2Computable_of_computable` : a `Computable` function `ℕ → ℕ` is computed by a `FinTM2`
  under `encodeNat`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2Recursive

open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Computability (encodeNat encodeNum encodePosNum)

/-! ### Bits and `Γ'` -/

/-- A bit as a symbol of `Γ'`. -/
def boolToΓ' : Bool → Γ'
  | true => Γ'.bit1
  | false => Γ'.bit0

/-- A symbol of `Γ'` as a bit (`bit1` is `true`). -/
def Γ'ToBool : Γ' → Bool
  | Γ'.bit1 => true
  | _ => false

@[simp] theorem Γ'ToBool_boolToΓ' (b : Bool) : Γ'ToBool (boolToΓ' b) = b := by
  cases b <;> rfl

theorem trPosNum_eq_map (p : PosNum) : trPosNum p = (encodePosNum p).map boolToΓ' := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [trPosNum, encodePosNum, ih, boolToΓ']
  | bit1 p ih => simp [trPosNum, encodePosNum, ih, boolToΓ']

/-- `tr`'s binary encoding of a natural number is `encodeNat` in the symbols of `Γ'`. -/
theorem trNat_eq_map (n : ℕ) : trNat n = (encodeNat n).map boolToΓ' := by
  unfold trNat encodeNat
  cases (n : Num) with
  | zero => rfl
  | pos p => exact trPosNum_eq_map p

theorem boolToΓ'_ne_cons (b : Bool) : boolToΓ' b ≠ Γ'.cons := by cases b <;> decide

/-! ### The wrapped machine -/

/-- `tr`'s four stacks form a finite type (a local instance; Mathlib's `K'` has none). -/
@[instance_reducible]
def fintypeK' : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, fun k ↦ by cases k <;> simp⟩

attribute [local instance] fintypeK'

/-- The adapter labels. -/
inductive Phase
  | pre0 | pre1 | pre2 | post1 | post2
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.pre0, .pre1, .pre2, .post1, .post2}, fun p ↦ by cases p <;> simp⟩

/-- Stack alphabets: `Γ'` on `tr`'s stacks, bits on the input and output stacks. -/
abbrev FΓ : K' ⊕ Bool → Type := Sum.elim (fun _ ↦ Γ') (fun _ ↦ Bool)

variable (c : Code)

/-- The labels of `tr` reachable from `trNormal c halt`. -/
abbrev supp : Finset Λ' := codeSupp c Cont'.halt

/-- Labels of the wrapped machine. -/
abbrev FΛ := Phase ⊕ {l // l ∈ supp c}

/-- Statements of the wrapped machine. -/
abbrev FStmt := TM2.Stmt FΓ (FΛ c) (Option Γ')

/-- A statement of `tr` as a statement of the wrapped machine: stacks move to `inl`, jumps stay
inside `supp c` (by `hq`), and `halt` jumps to the post-phase. -/
noncomputable def restrict :
    (q : TM2.Stmt (fun _ : K' ↦ Γ') Λ' (Option Γ')) → TM2.SupportsStmt (supp c) q → FStmt c
  | .push k f q, hq => .push (Sum.inl k) f (restrict q hq)
  | .peek k f q, hq => .peek (Sum.inl k) f (restrict q hq)
  | .pop k f q, hq => .pop (Sum.inl k) f (restrict q hq)
  | .load a q, hq => .load a (restrict q hq)
  | .branch p q₁ q₂, hq => .branch p (restrict q₁ hq.1) (restrict q₂ hq.2)
  | .goto l, hq => .goto fun v ↦ Sum.inr ⟨l v, hq v⟩
  | .halt, _ => .goto fun _ ↦ Sum.inl Phase.post1

/-- `trNormal c halt` is in the support. -/
theorem start_mem : trNormal c Cont'.halt ∈ supp c := (tr_supports c Cont'.halt).1

/-- The program of the wrapped machine. -/
noncomputable def fwdProg : FΛ c → FStmt c
  | Sum.inl Phase.pre0 =>
    .push (Sum.inl K'.main) (fun _ ↦ Γ'.cons) (.goto fun _ ↦ Sum.inl Phase.pre1)
  | Sum.inl Phase.pre1 =>
    .pop (Sum.inr false) (fun _ ob ↦ ob.map boolToΓ')
      (.branch Option.isSome
        (.push (Sum.inl K'.rev) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.pre1))
        (.goto fun _ ↦ Sum.inl Phase.pre2))
  | Sum.inl Phase.pre2 =>
    .pop (Sum.inl K'.rev) (fun _ o ↦ o)
      (.branch Option.isSome
        (.push (Sum.inl K'.main) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.pre2))
        (.goto fun _ ↦ Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩))
  | Sum.inr l => restrict c (tr l.1) ((tr_supports c Cont'.halt).2 l.1 l.2)
  | Sum.inl Phase.post1 =>
    .pop (Sum.inl K'.main) (fun _ o ↦ o)
      (.branch (fun v ↦ v.elim true fun g ↦ g = Γ'.cons)
        (.goto fun _ ↦ Sum.inl Phase.post2)
        (.push (Sum.inl K'.rev) (fun v ↦ v.getD default) (.goto fun _ ↦ Sum.inl Phase.post1)))
  | Sum.inl Phase.post2 =>
    .pop (Sum.inl K'.rev) (fun _ o ↦ o)
      (.branch Option.isSome
        (.push (Sum.inr true) (fun v ↦ Γ'ToBool (v.getD default))
          (.goto fun _ ↦ Sum.inl Phase.post2))
        .halt)

/-- The wrapped machine. -/
noncomputable def fwdTM : FinTM2 where
  K := K' ⊕ Bool
  k₀ := Sum.inr false
  k₁ := Sum.inr true
  Γ := FΓ
  Λ := FΛ c
  main := Sum.inl Phase.pre0
  σ := Option Γ'
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := fwdProg c

/-! ### Stacks -/

/-- Build the six stacks. -/
def mkStk (a b c' d : List Γ') (i o : List Bool) : ∀ k, List (FΓ k)
  | Sum.inl K'.main => a
  | Sum.inl K'.rev => b
  | Sum.inl K'.aux => c'
  | Sum.inl K'.stack => d
  | Sum.inr false => i
  | Sum.inr true => o

@[simp] theorem mkStk_update_main (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.main) x = mkStk x b c' d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_rev (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.rev) x = mkStk a x c' d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_aux (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.aux) x = mkStk a b x d i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_stack (a b c' d : List Γ') (i o : List Bool) (x : List Γ') :
    Function.update (mkStk a b c' d i o) (Sum.inl K'.stack) x = mkStk a b c' x i o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_in (a b c' d : List Γ') (i o : List Bool) (x : List Bool) :
    Function.update (mkStk a b c' d i o) (Sum.inr false) x = mkStk a b c' d x o := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

@[simp] theorem mkStk_update_out (a b c' d : List Γ') (i o : List Bool) (x : List Bool) :
    Function.update (mkStk a b c' d i o) (Sum.inr true) x = mkStk a b c' d i x := by
  funext k; rcases k with (_ | _ | _ | _) | (_ | _) <;> rfl

/-- Configurations of the wrapped machine. -/
abbrev FCfg := TM2.Cfg FΓ (FΛ c) (Option Γ')

/-- The step of the wrapped machine. -/
noncomputable abbrev fstep : FCfg c → Option (FCfg c) := TM2.step (fwdProg c)

/-- Iterated steps of the wrapped machine. -/
noncomputable abbrev frun (j : ℕ) (x : Option (FCfg c)) : Option (FCfg c) :=
  (flip bind (fstep c))^[j] x

theorem frun_add (j₁ j₂ : ℕ) (x : Option (FCfg c)) :
    frun c (j₁ + j₂) x = frun c j₁ (frun c j₂ x) := Function.iterate_add_apply _ _ _ _

theorem frun_succ (j : ℕ) (d : FCfg c) :
    frun c (j + 1) (some d) = frun c j (fstep c d) := Function.iterate_succ_apply _ _ _

theorem frun_zero (x : Option (FCfg c)) : frun c 0 x = x := rfl

theorem frun_one (d : FCfg c) : frun c 1 (some d) = fstep c d := rfl

/-! ### The pre-phase -/

theorem pre1_loop (a b c' d : List Γ') (bits : List Bool) (v : Option Γ') :
    frun c (bits.length + 1) (some ⟨some (Sum.inl Phase.pre1), v, mkStk a b c' d bits []⟩) =
      some ⟨some (Sum.inl Phase.pre2), none,
        mkStk a ((bits.map boolToΓ').reverse ++ b) c' d [] []⟩ := by
  induction bits generalizing b v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x bits ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.pre1), v, mkStk a b c' d (x :: bits) []⟩ =
        some ⟨some (Sum.inl Phase.pre1), some (boolToΓ' x),
          mkStk a (boolToΓ' x :: b) c' d bits []⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

theorem pre2_loop (a r c' d : List Γ') (v : Option Γ') :
    frun c (r.length + 1) (some ⟨some (Sum.inl Phase.pre2), v, mkStk a r c' d [] []⟩) =
      some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (r.reverse ++ a) [] c' d [] []⟩ := by
  induction r generalizing a v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x r ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.pre2), v, mkStk a (x :: r) c' d [] []⟩ =
        some ⟨some (Sum.inl Phase.pre2), some x, mkStk (x :: a) r c' d [] []⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

/-- The pre-phase: from the input configuration to `tr`'s initial configuration on `[n]`. -/
theorem pre_phase (bits : List Bool) :
    frun c (bits.length + 1 + (bits.length + 1) + 1)
        (some ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩) =
      some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (bits.map boolToΓ' ++ [Γ'.cons]) [] [] [] [] []⟩ := by
  rw [frun_succ]
  have h0 : fstep c ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] bits []⟩ =
      some ⟨some (Sum.inl Phase.pre1), none, mkStk [Γ'.cons] [] [] [] bits []⟩ := by
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  rw [h0, frun_add, pre1_loop]
  have hlen : bits.length = ((bits.map boolToΓ').reverse ++ []).length := by simp
  rw [hlen, pre2_loop]
  simp

/-! ### The post-phase -/

theorem post1_loop (bits : List Bool) (r : List Γ') (o : List Bool) (v : Option Γ') :
    frun c (bits.length + 1) (some ⟨some (Sum.inl Phase.post1), v,
        mkStk (bits.map boolToΓ' ++ [Γ'.cons]) r [] [] [] o⟩) =
      some ⟨some (Sum.inl Phase.post2), some Γ'.cons,
        mkStk [] ((bits.map boolToΓ').reverse ++ r) [] [] [] o⟩ := by
  induction bits generalizing r v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x bits ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.post1), v,
        mkStk ((x :: bits).map boolToΓ' ++ [Γ'.cons]) r [] [] [] o⟩ =
        some ⟨some (Sum.inl Phase.post1), some (boolToΓ' x),
          mkStk (bits.map boolToΓ' ++ [Γ'.cons]) (boolToΓ' x :: r) [] [] [] o⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk, boolToΓ'_ne_cons]
    rw [this, ih]
    simp

theorem post2_loop (r : List Γ') (o : List Bool) (v : Option Γ') :
    frun c (r.length + 1) (some ⟨some (Sum.inl Phase.post2), v, mkStk [] r [] [] [] o⟩) =
      some ⟨none, none, mkStk [] [] [] [] [] ((r.map Γ'ToBool).reverse ++ o)⟩ := by
  induction r generalizing o v with
  | nil =>
    rw [List.length_nil, frun_one]
    simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
  | cons x r ih =>
    rw [List.length_cons, frun_succ]
    have : fstep c ⟨some (Sum.inl Phase.post2), v, mkStk [] (x :: r) [] [] [] o⟩ =
        some ⟨some (Sum.inl Phase.post2), some x, mkStk [] r [] [] [] (Γ'ToBool x :: o)⟩ := by
      simp [fwdProg, TM2.step, TM2.stepAux, mkStk]
    rw [this, ih]
    simp

/-- The post-phase: from `tr`'s halting stacks `trList [m]` to the output bits. -/
theorem post_phase (bits : List Bool) :
    frun c ((bits.length + 1) + (bits.length + 1))
        (some ⟨some (Sum.inl Phase.post1), none,
          mkStk (bits.map boolToΓ' ++ [Γ'.cons]) [] [] [] [] []⟩) =
      some ⟨none, none, mkStk [] [] [] [] [] bits⟩ := by
  rw [frun_add, post1_loop]
  have hlen : bits.length = ((bits.map boolToΓ').reverse ++ []).length := by simp
  rw [hlen, post2_loop]
  simp [List.map_reverse, Function.comp_def]

/-! ### The main phase simulates `tr` -/

/-- `tr`'s stacks inside the wrapped machine, with empty input and output stacks. -/
def liftStk (s : ∀ _ : K', List Γ') : ∀ k, List (FΓ k) :=
  mkStk (s K'.main) (s K'.rev) (s K'.aux) (s K'.stack) [] []

theorem liftStk_inl (s : ∀ _ : K', List Γ') (k : K') : liftStk s (Sum.inl k) = s k := by
  cases k <;> rfl

theorem liftStk_update (s : ∀ _ : K', List Γ') (k : K') (x : List Γ') :
    liftStk (Function.update s k x) = Function.update (liftStk s) (Sum.inl k) x := by
  cases k <;> simp [liftStk]

/-- How a label of `tr` corresponds to a label of the wrapped machine: halting becomes the
post-phase. -/
def LabelRel : Option Λ' → Option (FΛ c) → Prop
  | none, o' => o' = some (Sum.inl Phase.post1)
  | some l, o' => ∃ h : l ∈ supp c, o' = some (Sum.inr ⟨l, h⟩)

theorem stepAux_restrict (q : TM2.Stmt (fun _ : K' ↦ Γ') Λ' (Option Γ'))
    (hq : TM2.SupportsStmt (supp c) q) (v : Option Γ') (s : ∀ _ : K', List Γ') :
    (TM2.stepAux (restrict c q hq) v (liftStk s)).var = (TM2.stepAux q v s).var ∧
      (TM2.stepAux (restrict c q hq) v (liftStk s)).stk = liftStk (TM2.stepAux q v s).stk ∧
      LabelRel c (TM2.stepAux q v s).l (TM2.stepAux (restrict c q hq) v (liftStk s)).l := by
  induction q generalizing v s with
  | push k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.push k f q) hq = .push (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    have := ih hq' v (Function.update s k (f v :: s k))
    rw [liftStk_update] at this
    exact this
  | peek k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.peek k f q) hq = .peek (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    exact ih hq' _ s
  | pop k f q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.pop k f q) hq = .pop (Sum.inl k) f (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    rw [liftStk_inl]
    have := ih hq' (f v (s k).head?) (Function.update s k (s k).tail)
    rw [liftStk_update] at this
    exact this
  | load a q ih =>
    have hq' : TM2.SupportsStmt (supp c) q := hq
    rw [show restrict c (.load a q) hq = .load a (restrict c q hq') from rfl]
    simp only [TM2.stepAux]
    exact ih hq' _ s
  | branch p q₁ q₂ ih₁ ih₂ =>
    rw [show restrict c (.branch p q₁ q₂) hq =
      .branch p (restrict c q₁ hq.1) (restrict c q₂ hq.2) from rfl]
    simp only [TM2.stepAux]
    cases p v
    · exact ih₂ hq.2 v s
    · exact ih₁ hq.1 v s
  | goto l => exact ⟨rfl, rfl, hq v, rfl⟩
  | halt => exact ⟨rfl, rfl, rfl⟩

/-- A configuration of `tr` and the corresponding configuration of the wrapped machine. -/
def TrRel (x : Cfg') (d : FCfg c) : Prop :=
  d.var = x.var ∧ d.stk = liftStk x.stk ∧ LabelRel c x.l d.l

theorem step_rel {x : Cfg'} {d : FCfg c} (hxd : TrRel c x d) {x' : Cfg'}
    (hx' : TM2.step tr x = some x') : ∃ d', fstep c d = some d' ∧ TrRel c x' d' := by
  obtain ⟨l, v, s⟩ := x
  obtain ⟨hv, hs, hl⟩ := hxd
  cases l with
  | none => simp [TM2.step] at hx'
  | some l =>
    obtain ⟨h, hdl⟩ := hl
    obtain ⟨dl, dv, ds⟩ := d
    simp only at hv hs hdl
    subst hv hs hdl
    simp only [TM2.step] at hx'
    obtain rfl := Option.some.inj hx'
    obtain ⟨h₁, h₂, h₃⟩ := stepAux_restrict c (tr l) ((tr_supports c Cont'.halt).2 l h) dv s
    exact ⟨_, rfl, h₁, h₂, h₃⟩

theorem run_rel {x₀ : Cfg'} {d₀ : FCfg c} (h₀ : TrRel c x₀ d₀) :
    ∀ (j : ℕ) {x : Cfg'}, (flip bind (TM2.step tr))^[j] (some x₀) = some x →
      ∃ d, frun c j (some d₀) = some d ∧ TrRel c x d := by
  intro j
  induction j with
  | zero =>
    intro x hx
    obtain rfl := Option.some.inj hx
    exact ⟨d₀, rfl, h₀⟩
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    cases hj : (flip bind (TM2.step tr))^[j] (some x₀) with
    | none => rw [hj] at hx; cases hx
    | some x₁ =>
      rw [hj] at hx
      obtain ⟨d₁, hd₁, hrel⟩ := ih hj
      obtain ⟨d, hd, hrel'⟩ := step_rel c hrel hx
      refine ⟨d, ?_, hrel'⟩
      rw [frun, Function.iterate_succ_apply', ← frun, hd₁]
      exact hd

/-- Reachability gives a number of steps. -/
theorem exists_iterate_eq_of_reaches {α : Type*} {f : α → Option α} {a b : α}
    (h : StateTransition.Reaches f a b) : ∃ N, (flip bind f)^[N] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N + 1, by rw [Function.iterate_succ_apply', hN]; exact hbc⟩

/-- The main phase: `tr` evaluates `c` on `[n]`, and the wrapped machine follows it into the
post-phase. -/
theorem main_phase {f : ℕ → ℕ} (hc : ∀ n, c.eval [n] = pure [f n]) (n : ℕ) :
    ∃ N, frun c N (some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (trList [n]) [] [] [] [] []⟩) =
      some ⟨some (Sum.inl Phase.post1), none, mkStk (trList [f n]) [] [] [] [] []⟩ := by
  have heval := tr_eval c [n]
  rw [hc n] at heval
  have hmem : halt [f n] ∈ StateTransition.eval (TM2.step tr) (init c [n]) := by
    rw [heval]
    exact Part.mem_map _ (Part.mem_some _)
  obtain ⟨N, hN⟩ := exists_iterate_eq_of_reaches (StateTransition.mem_eval.mp hmem).1
  have h₀ : TrRel c (init c [n]) ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
      mkStk (trList [n]) [] [] [] [] []⟩ := ⟨rfl, rfl, start_mem c, rfl⟩
  obtain ⟨⟨dl, dv, ds⟩, hd, hv, hs, hl⟩ := run_rel c h₀ N hN
  refine ⟨N, hd.trans ?_⟩
  simp only [halt] at hv hs hl
  simp only [LabelRel] at hl
  subst hv hs hl
  rfl

/-! ### Assembly -/

theorem trList_singleton (m : ℕ) : trList [m] = (encodeNat m).map boolToΓ' ++ [Γ'.cons] := by
  simp [trList, trNat_eq_map]

/-- The wrapped machine computes `f` when the code `c` evaluates `f`. -/
noncomputable def tm2ComputableOfCode {f : ℕ → ℕ} (hc : ∀ n, c.eval [n] = pure [f n]) :
    TM2Computable encodeNat encodeNat f where
  tm := fwdTM c
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  outputsFun n :=
    ⟨((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)) +
        ((main_phase c hc n).choose +
          ((encodeNat n).length + 1 + ((encodeNat n).length + 1) + 1)), by
      have hinit : initList (fwdTM c) ((encodeNat n).map (Equiv.refl Bool).invFun) =
          (⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] (encodeNat n) []⟩ : FCfg c) := by
        simp only [initList]
        congr 1
        funext k
        rcases k with (_ | _ | _ | _) | (_ | _)
        all_goals first
          | rfl
          | (simp only [fwdTM, mkStk, Equiv.refl, ↓reduceDIte]
             change List.map (id : Bool → Bool) _ = _
             exact List.map_id _)
      have hhalt : haltList (fwdTM c) ((encodeNat (f n)).map (Equiv.refl Bool).invFun) =
          (⟨none, none, mkStk [] [] [] [] [] (encodeNat (f n))⟩ : FCfg c) := by
        simp only [haltList]
        congr 1
        funext k
        rcases k with (_ | _ | _ | _) | (_ | _)
        all_goals first
          | rfl
          | (simp only [fwdTM, mkStk, Equiv.refl, ↓reduceDIte]
             change List.map (id : Bool → Bool) _ = _
             exact List.map_id _)
      have key : frun c (((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)) +
          ((main_phase c hc n).choose +
            ((encodeNat n).length + 1 + ((encodeNat n).length + 1) + 1)))
          (some ⟨some (Sum.inl Phase.pre0), none, mkStk [] [] [] [] (encodeNat n) []⟩) =
          some ⟨none, none, mkStk [] [] [] [] [] (encodeNat (f n))⟩ := by
        rw [frun_add c ((encodeNat (f n)).length + 1 + ((encodeNat (f n)).length + 1)),
          frun_add c (main_phase c hc n).choose, pre_phase, ← trList_singleton,
          (main_phase c hc n).choose_spec, trList_singleton, post_phase]
      rw [hinit, Option.map_some, hhalt]
      exact key⟩

/-- **Recursive functions are Turing-computable.** Every `Computable` function `ℕ → ℕ` is
computed by a bundled finite multi-stack machine (`FinTM2`) under the binary encoding
`encodeNat`. -/
theorem tm2Computable_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    Nonempty (TM2Computable encodeNat encodeNat f) := by
  have hp : Nat.Partrec' fun v : List.Vector ℕ 1 ↦ (f v.head : Part ℕ) :=
    Nat.Partrec'.part_iff₁.mpr hf.partrec
  obtain ⟨c, hc⟩ := Code.exists_code hp
  refine ⟨tm2ComputableOfCode c (f := f) fun n ↦ ?_⟩
  have := hc ⟨[n], rfl⟩
  simp only [Part.coe_some, Part.map_eq_map, Part.map_some] at this
  exact this

end MetaMathlibExt.TM2Recursive
