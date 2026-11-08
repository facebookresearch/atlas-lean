/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turing-computable functions are recursive
-/
module

public import Mathlib.Computability.Partrec
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Turing-computable functions are recursive

The backward half of the Turing–Kleene equivalence for Mathlib's bundled finite multi-stack
machines (the TM2 model): if a `FinTM2` computes `f : ℕ → ℕ` under the binary encoding
`Computability.encodeNat`, then `f` is `Computable`.

The proof simulates the machine on a `Primcodable` state space.  Labels, internal states and
stack indices are finite, so `Primcodable` by choice.  Stack symbols need care: only the input
alphabet is required to be finite, but a machine can only ever hold input symbols or values
`f v` written by a `push` of its finite program, so each symbol that occurs is coded by its
index in a finite list (`symList`).  The coded step (`stepC`) is primitive recursive
(`primrec_stepC`, by induction on the program's statements), it commutes with the coding on
configurations whose symbols are relevant (`stepC_enc`), and the run is the least `n` with a
halted state, found by `Nat.rfind` (`partrec_run`).

## Main results

- `primrec_encodeNat`, `bitsVal_encodeNat` : the binary encoding of `ℕ` is primitive
  recursive, with a primitive recursive left inverse.
- `partrec_run` : iterating a primitive recursive step until a primitive recursive halting
  test succeeds is partial recursive.
- `computable_of_tm2Computable` : a function computed by a `FinTM2` is `Computable`.

## References

- S. C. Kleene, *Introduction to Metamathematics*, North-Holland 1952, §68–§69.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2Recursive

open Computability Turing

/-! ### The binary encoding of `ℕ` -/

theorem encodeNum_bit1 (n : Num) : encodeNum n.bit1 = true :: encodeNum n := by
  cases n <;> rfl

theorem encodeNum_bit0 {n : Num} (hn : n ≠ 0) : encodeNum n.bit0 = false :: encodeNum n := by
  cases n with
  | zero => exact absurd rfl hn
  | pos p => rfl

theorem encodeNat_zero : encodeNat 0 = [] := rfl

/-- The binary encoding is least significant bit first. -/
theorem encodeNat_eq_cons {n : ℕ} (hn : n ≠ 0) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  have key : ∀ b m, encodeNat (Nat.bit b m) =
      if b = false ∧ m = 0 then [] else b :: encodeNat m := by
    intro b m
    unfold encodeNat
    rw [← Num.ofNat'_eq, ← Num.ofNat'_eq, Num.ofNat'_bit]
    cases b with
    | true => simp [encodeNum_bit1]
    | false =>
      by_cases hm : m = 0
      · subst hm
        simp [Num.ofNat'_zero]
        rfl
      · have : ((m : ℕ) : Num) ≠ 0 := fun h ↦ hm (by simpa using congrArg ((↑) : Num → ℕ) h)
        simp only [Bool.cond_false, hm, and_false, ↓reduceIte]
        rw [Num.ofNat'_eq, encodeNum_bit0 this]
  have hbit : Nat.bit (decide (n % 2 = 1)) (n / 2) = n := by
    rw [Nat.bit_val]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega
  conv_lhs => rw [← hbit]
  rw [key]
  have : ¬ (decide (n % 2 = 1) = false ∧ n / 2 = 0) := by
    rintro ⟨h₁, h₂⟩
    simp at h₁
    omega
  simp only [this, ↓reduceIte]

theorem primrec_encodeNat : Primrec encodeNat := by
  have h := Primrec.nat_strong_rec (fun (_ : Unit) n ↦ encodeNat n)
    (g := fun _ l ↦ some (if l.length = 0 then [] else
      (if l.length % 2 = 1 then true else false) :: l.getD (l.length / 2) [])) ?_ ?_
  · exact h.comp (Primrec.const ()) Primrec.id
  · refine Primrec.option_some.comp (Primrec.ite ?_ (Primrec.const _) ?_)
    · exact Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)
    · refine Primrec.list_cons.comp (Primrec.ite ?_ (Primrec.const _) (Primrec.const _)) ?_
      · exact Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.const 2)) (Primrec.const 1)
      · exact (Primrec.list_getD []).comp Primrec.snd
          (Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 2))
  · intro _ n
    simp only [List.length_map, List.length_range, Option.some.injEq]
    by_cases hn : n = 0
    · subst hn
      rfl
    · simp only [hn, ↓reduceIte]
      rw [encodeNat_eq_cons hn, List.getD_eq_getElem _ _ (by simp; omega)]
      simp

/-- Little-endian value of a list of bits. -/
def bitsVal (l : List Bool) : ℕ := l.foldr (fun b n ↦ 2 * n + cond b 1 0) 0

theorem primrec_bitsVal : Primrec bitsVal :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
      (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))).to₂

theorem bitsVal_encodeNat (n : ℕ) : bitsVal (encodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      rfl
    · rw [encodeNat_eq_cons hn]
      simp only [bitsVal, List.foldr_cons] at ih ⊢
      rw [ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hn) one_lt_two)]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-! ### Running a primitive recursive step function -/

section Run

variable {α σ β : Type*} [Primcodable α] [Primcodable σ] [Primcodable β]

/-- Iterating a primitive recursive step until a primitive recursive halting test succeeds, and
reading off the first halted state, is partial recursive. -/
theorem partrec_run {init : α → σ} {step : σ → σ} {halted : σ → Bool} {out : σ → β}
    (hi : Primrec init) (hs : Primrec step) (hh : Primrec halted) (ho : Primrec out) :
    Partrec fun a ↦ (Nat.rfind fun k ↦ Part.some (halted (step^[k] (init a)))).map
      fun k ↦ out (step^[k] (init a)) := by
  have hit : Primrec₂ fun a k ↦ step^[k] (init a) :=
    Primrec.nat_iterate Primrec.snd (hi.comp Primrec.fst) (hs.comp Primrec.snd).to₂
  refine Partrec.map (Partrec.rfind ?_) (ho.comp (hit.comp Primrec.fst Primrec.snd)).to_comp.to₂
  exact (hh.comp₂ hit).to_comp.partrec₂

end Run

/-! ### Primitive recursive helpers -/

section Helpers

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- A function of a natural number that is constant from `N` on is primitive recursive. -/
theorem primrec_of_eventually_const {g : ℕ → β} (N : ℕ) (hg : ∀ c ≥ N, g c = g N) :
    Primrec g := by
  refine ((Primrec.list_getD (g N)).comp (Primrec.const (List.ofFn fun i : Fin N ↦ g i))
    Primrec.id).of_eq fun c ↦ ?_
  by_cases hc : c < N
  · rw [List.getD_eq_getElem _ _ (by simpa using hc)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hc), hg c (by omega)]

/-- Over a finite parameter type, eventual constancy in the natural argument suffices. -/
theorem primrec₂_of_eventually_const [Finite α] {g : α → ℕ → β} (N : ℕ)
    (hg : ∀ a, ∀ c ≥ N, g a c = g a N) : Primrec₂ g := by
  refine (Primrec.option_getD.comp (Primrec.list_getElem?.comp
    ((Primrec.dom_finite fun a ↦ List.ofFn fun i : Fin N ↦ g a i).comp Primrec.fst)
    Primrec.snd) ((Primrec.dom_finite fun a ↦ g a N).comp Primrec.fst)).to₂.of_eq ?_
  intro a c
  by_cases hc : c < N
  · simp [hc]
  · simp [hc, hg a c (by omega)]

/-- Over a finite type of first arguments, primitive recursion in the second argument for each
fixed first argument suffices. -/
theorem primrec₂_of_finite_left [Finite α] {σ : Type*} [Primcodable σ] {g : α → β → σ}
    (hg : ∀ a, Primrec (g a)) : Primrec₂ g := by
  have := Fintype.ofFinite α
  let e := Fintype.equivFin α
  have h : Primrec₂ fun (i : Fin (Fintype.card α)) b ↦ g (e.symm i) b :=
    Primrec.fin_curry₁.mpr fun i ↦ hg _
  exact (h.comp ((Primrec.dom_finite e).comp Primrec.fst) Primrec.snd).of_eq fun p ↦ by simp

end Helpers

/-- Functions from a finite type, coded through `Fin n`. -/
@[instance_reducible]
noncomputable def primcodableArrow (K : Type*) [Fintype K] (β : Type*) [Primcodable β] :
    Primcodable (K → β) :=
  Primcodable.ofEquiv (Fin (Fintype.card K) → β)
    (Equiv.arrowCongr (Fintype.equivFin K) (Equiv.refl β))

section Arrow

variable {K : Type*} [Fintype K] [DecidableEq K] {α β : Type*} [Primcodable α] [Primcodable β]

attribute [local instance] primcodableArrow

omit [DecidableEq K] in
theorem primrec_arrow_eval (k : K) : Primrec fun S : K → β ↦ S k := by
  have : Primrec fun S : K → β ↦ (Equiv.arrowCongr (Fintype.equivFin K) (Equiv.refl β)) S :=
    Primrec.of_equiv
  exact (Primrec.fin_app.comp this (Primrec.const (Fintype.equivFin K k))).of_eq fun S ↦ by simp

theorem primrec_arrow_update (k : K) :
    Primrec₂ fun (S : K → β) (x : β) ↦ Function.update S k x := by
  let e := Equiv.arrowCongr (Fintype.equivFin K) (Equiv.refl β)
  have he : Primrec fun S : K → β ↦ e S := Primrec.of_equiv
  have hupd : Primrec₂ fun (T : Fin (Fintype.card K) → β) (x : β) ↦
      Function.update T (Fintype.equivFin K k) x := by
    have hv : Primrec fun p : (Fin (Fintype.card K) → β) × β ↦
        List.Vector.ofFn fun i ↦ Function.update p.1 (Fintype.equivFin K k) p.2 i := by
      refine Primrec.vector_ofFn fun i ↦ ?_
      by_cases hi : i = Fintype.equivFin K k
      · subst hi
        exact Primrec.snd.of_eq fun p ↦ by simp
      · exact (Primrec.fin_app.comp Primrec.fst (Primrec.const i)).of_eq fun p ↦ by
          simp [Function.update_of_ne hi]
    exact (Primrec.vector_get'.comp hv).of_eq fun p ↦ by funext i; simp
  refine ((Primrec.of_equiv_symm (e := e)).comp (hupd.comp (he.comp Primrec.fst)
    Primrec.snd)).to₂.of_eq fun S x ↦ ?_
  funext k'
  simp only [e, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_apply, id]
  by_cases hk : k' = k
  · subst hk
    simp
  · rw [Function.update_of_ne hk, Function.update_of_ne
      (fun h ↦ hk ((Fintype.equivFin K).injective h))]
    simp

end Arrow

/-! ### Relevant stack symbols -/

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

section Machine

variable (tm : FinTM2)

/-- The symbols a statement can push onto stack `k`. -/
def pushes (k : tm.K) : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Set (tm.Γ k)
  | .push k' f q => (if h : k' = k then Set.range (h ▸ f) else ∅) ∪ pushes k q
  | .peek _ _ q => pushes k q
  | .pop _ _ q => pushes k q
  | .load _ q => pushes k q
  | .branch _ q₁ q₂ => pushes k q₁ ∪ pushes k q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushes_finite (k : tm.K) (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (pushes tm k q).Finite := by
  induction q with
  | push k' f q ih =>
    refine Set.Finite.union ?_ ih
    split
    · next h => subst h; exact Set.finite_range f
    · exact Set.finite_empty
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

/-- The symbols that can ever be on stack `k`: input symbols on the input stack, and symbols
pushed by the program. -/
def relevant (k : tm.K) : Set (tm.Γ k) :=
  (⋃ l, pushes tm k (tm.m l)) ∪ {_x | k = tm.k₀}

theorem relevant_finite (k : tm.K) : (relevant tm k).Finite := by
  refine (Set.finite_iUnion fun l ↦ pushes_finite tm k (tm.m l)).union ?_
  by_cases h : k = tm.k₀
  · subst h
    exact Set.toFinite _
  · simp [h]

/-- The relevant symbols of stack `k`, listed. -/
noncomputable def symList (k : tm.K) : List (tm.Γ k) := (relevant_finite tm k).toFinset.toList

/-- The code of a symbol: its index in `symList`. -/
noncomputable def code (k : tm.K) (x : tm.Γ k) : ℕ :=
  letI := Classical.decEq (tm.Γ k)
  (symList tm k).idxOf x

/-- Decoding a code; `none` past the end of `symList`. -/
noncomputable def decode (k : tm.K) (c : ℕ) : Option (tm.Γ k) := (symList tm k)[c]?

theorem decode_code {k : tm.K} {x : tm.Γ k} (hx : x ∈ relevant tm k) :
    decode tm k (code tm k x) = some x := by
  let _ := Classical.decEq (tm.Γ k)
  have hmem : x ∈ symList tm k := by simpa [symList] using hx
  simp [decode, code, List.getElem?_idxOf hmem]

theorem decode_eq_none {k : tm.K} {c : ℕ} (hc : (symList tm k).length ≤ c) :
    decode tm k c = none := by
  simp [decode, hc]

/-- All symbols on the stacks are relevant. -/
def Relevant (S : ∀ k, List (tm.Γ k)) : Prop := ∀ k, ∀ x ∈ S k, x ∈ relevant tm k

/-! ### The coded machine -/

attribute [local instance] primcodableArrow

/-- Labels, coded through `Fin n`. -/
@[instance_reducible]
noncomputable def primcodableΛ : Primcodable tm.Λ :=
  Primcodable.ofEquiv _ (Fintype.equivFin tm.Λ)

/-- Internal states, coded through `Fin n`. -/
@[instance_reducible]
noncomputable def primcodableσ : Primcodable tm.σ :=
  Primcodable.ofEquiv _ (Fintype.equivFin tm.σ)

attribute [local instance] primcodableΛ primcodableσ

/-- Coded configurations: label, internal state, and stacks of symbol codes. -/
abbrev CodedCfg := Option tm.Λ × tm.σ × (tm.K → List ℕ)

/-- Code the stacks. -/
noncomputable def encStk (S : ∀ k, List (tm.Γ k)) : tm.K → List ℕ :=
  fun k ↦ (S k).map (code tm k)

/-- Code a configuration. -/
noncomputable def enc (c : tm.Cfg) : CodedCfg tm := (c.l, c.var, encStk tm c.stk)

/-- Read the top of a coded stack. -/
noncomputable def readTop (k : tm.K) (S : tm.K → List ℕ) : Option (tm.Γ k) :=
  (S k).head?.bind (decode tm k)

/-- The coded version of `TM2.stepAux`. -/
noncomputable def stepAuxC :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → (tm.K → List ℕ) → CodedCfg tm
  | .push k f q, v, S => stepAuxC q v (Function.update S k (code tm k (f v) :: S k))
  | .peek k f q, v, S => stepAuxC q (f v (readTop tm k S)) S
  | .pop k f q, v, S => stepAuxC q (f v (readTop tm k S)) (Function.update S k (S k).tail)
  | .load a q, v, S => stepAuxC q (a v) S
  | .branch f q₁ q₂, v, S => cond (f v) (stepAuxC q₁ v S) (stepAuxC q₂ v S)
  | .goto f, v, S => (some (f v), v, S)
  | .halt, v, S => (none, v, S)

/-- The coded step. -/
noncomputable def stepC (c : CodedCfg tm) : Option (CodedCfg tm) :=
  c.1.map fun l ↦ stepAuxC tm (tm.m l) c.2.1 c.2.2

/-! ### The coded step is primitive recursive -/

theorem primrec₂_readTop {k : tm.K} {f : tm.σ → Option (tm.Γ k) → tm.σ} :
    Primrec₂ fun (v : tm.σ) (S : tm.K → List ℕ) ↦ f v (readTop tm k S) := by
  have hG : Primrec₂ fun (v : tm.σ) (o : Option ℕ) ↦ f v (o.bind (decode tm k)) := by
    refine Primrec.option_casesOn (o := fun p : tm.σ × Option ℕ ↦ p.2) Primrec.snd
      ((Primrec.dom_finite fun v ↦ f v none).comp Primrec.fst) ?_ |>.of_eq fun p ↦ by
        cases p.2 <;> rfl
    exact (primrec₂_of_eventually_const (g := fun v c ↦ f v (decode tm k c))
      (symList tm k).length fun v c hc ↦ by
        rw [decode_eq_none tm hc, decode_eq_none tm le_rfl]).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact hG.comp Primrec.fst (Primrec.list_head?.comp ((primrec_arrow_eval k).comp Primrec.snd))

theorem primrec₂_stepAuxC (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    Primrec₂ (stepAuxC tm q) := by
  induction q with
  | push k f q ih =>
    exact ih.comp Primrec.fst ((primrec_arrow_update k).comp Primrec.snd
      (Primrec.list_cons.comp ((Primrec.dom_finite fun v ↦ code tm k (f v)).comp Primrec.fst)
        ((primrec_arrow_eval k).comp Primrec.snd)))
  | peek k f q ih => exact ih.comp (primrec₂_readTop tm) Primrec.snd
  | pop k f q ih =>
    exact ih.comp (primrec₂_readTop tm) ((primrec_arrow_update k).comp Primrec.snd
      (Primrec.list_tail.comp ((primrec_arrow_eval k).comp Primrec.snd)))
  | load a q ih => exact ih.comp ((Primrec.dom_finite a).comp Primrec.fst) Primrec.snd
  | branch f q₁ q₂ ih₁ ih₂ =>
    exact Primrec.cond ((Primrec.dom_finite f).comp Primrec.fst) ih₁ ih₂
  | goto f =>
    exact Primrec.pair (Primrec.option_some.comp ((Primrec.dom_finite f).comp Primrec.fst))
      (Primrec.pair Primrec.fst Primrec.snd)
  | halt => exact Primrec.pair (Primrec.const none) (Primrec.pair Primrec.fst Primrec.snd)

theorem primrec_stepC : Primrec (stepC tm) := by
  have h : Primrec₂ fun (l : tm.Λ) (p : tm.σ × (tm.K → List ℕ)) ↦ stepAuxC tm (tm.m l) p.1 p.2 :=
    primrec₂_of_finite_left fun l ↦ primrec₂_stepAuxC tm (tm.m l)
  exact Primrec.option_map Primrec.fst (h.comp Primrec.snd (Primrec.snd.comp Primrec.fst))

/-! ### The coded step simulates the machine -/

theorem encStk_update (S : ∀ k, List (tm.Γ k)) (k : tm.K) (l : List (tm.Γ k)) :
    encStk tm (Function.update S k l) = Function.update (encStk tm S) k (l.map (code tm k)) := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp [encStk]
  · simp [encStk, Function.update_of_ne h]

theorem readTop_encStk {S : ∀ k, List (tm.Γ k)} (hS : Relevant tm S) (k : tm.K) :
    readTop tm k (encStk tm S) = (S k).head? := by
  unfold readTop encStk
  cases hSk : S k with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ relevant tm k := hS k x (by simp [hSk])
    simp [decode_code tm hx]

theorem relevant_update {S : ∀ k, List (tm.Γ k)} (hS : Relevant tm S) {k : tm.K}
    {l : List (tm.Γ k)} (hl : ∀ x ∈ l, x ∈ relevant tm k) :
    Relevant tm (Function.update S k l) := by
  intro k' x hx
  by_cases h : k' = k
  · subst h
    exact hl x (by simpa using hx)
  · exact hS k' x (by simpa [Function.update_of_ne h] using hx)

theorem stepAuxC_enc (q : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hq : ∀ k, pushes tm k q ⊆ relevant tm k) (v : tm.σ) {S : ∀ k, List (tm.Γ k)}
    (hS : Relevant tm S) :
    stepAuxC tm q v (encStk tm S) = enc tm (Turing.TM2.stepAux q v S) ∧
      Relevant tm (Turing.TM2.stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    have hq' : ∀ k', pushes tm k' q ⊆ relevant tm k' :=
      fun k' ↦ (Set.subset_union_right).trans (hq k')
    have hfv : f v ∈ relevant tm k := hq k (Set.mem_union_left _ (by simp))
    have hS' := relevant_update tm hS (k := k) (l := f v :: S k) fun x hx ↦ by
      rcases List.mem_cons.mp hx with rfl | hx
      exacts [hfv, hS k x hx]
    have := ih hq' v hS'
    rw [encStk_update] at this
    simpa [stepAuxC, encStk] using this
  | peek k f q ih =>
    have := ih hq (f v (S k).head?) hS
    simpa [stepAuxC, readTop_encStk tm hS] using this
  | pop k f q ih =>
    have hS' := relevant_update tm hS (k := k) (l := (S k).tail) fun x hx ↦
      hS k x (List.mem_of_mem_tail hx)
    have := ih hq (f v (S k).head?) hS'
    rw [encStk_update] at this
    simpa [stepAuxC, readTop_encStk tm hS, encStk, List.map_tail] using this
  | load a q ih => simpa [stepAuxC] using ih hq (a v) hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f v
    · simpa [stepAuxC, hf] using
        ih₂ (fun k ↦ (Set.subset_union_right).trans (hq k)) v hS
    · simpa [stepAuxC, hf] using
        ih₁ (fun k ↦ (Set.subset_union_left).trans (hq k)) v hS
  | goto f => exact ⟨rfl, hS⟩
  | halt => exact ⟨rfl, hS⟩

theorem stepC_enc {c : tm.Cfg} (hc : Relevant tm c.stk) :
    stepC tm (enc tm c) = (tm.step c).map (enc tm) ∧ ∀ c' ∈ tm.step c, Relevant tm c'.stk := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => exact ⟨rfl, fun c' hc' ↦ absurd hc' (Option.not_mem_none c')⟩
  | some l =>
    have hq : ∀ k, pushes tm k (tm.m l) ⊆ relevant tm k := fun k ↦
      (Set.subset_iUnion (fun l ↦ pushes tm k (tm.m l)) l).trans Set.subset_union_left
    obtain ⟨h₁, h₂⟩ := stepAuxC_enc tm (tm.m l) hq v hc
    refine ⟨?_, ?_⟩
    · simp only [stepC, enc, FinTM2.step, Turing.TM2.step, Option.map_some]
      exact congrArg some h₁
    · intro c' hc'
      obtain rfl := Option.mem_some_iff.mp hc'
      exact h₂

/-- The coded step on optional configurations. -/
noncomputable def optStepC (o : Option (CodedCfg tm)) : Option (CodedCfg tm) := o.bind (stepC tm)

theorem primrec_optStepC : Primrec (optStepC tm) :=
  Primrec.option_bind Primrec.id ((primrec_stepC tm).comp Primrec.snd).to₂

/-- The coded run follows the machine's run, and every configuration on it has relevant
symbols. -/
theorem optStepC_iterate (j : ℕ) {o : Option tm.Cfg} (ho : ∀ c ∈ o, Relevant tm c.stk) :
    (optStepC tm)^[j] (o.map (enc tm)) = ((flip bind tm.step)^[j] o).map (enc tm) ∧
      ∀ c ∈ (flip bind tm.step)^[j] o, Relevant tm c.stk := by
  induction j generalizing o with
  | zero => exact ⟨rfl, ho⟩
  | succ j ih =>
    have hstep : optStepC tm (o.map (enc tm)) = (flip bind tm.step o).map (enc tm) ∧
        ∀ c ∈ flip bind tm.step o, Relevant tm c.stk := by
      cases o with
      | none => exact ⟨rfl, fun c hc ↦ by cases hc⟩
      | some c =>
        obtain ⟨h₁, h₂⟩ := stepC_enc tm (ho c rfl)
        exact ⟨h₁, h₂⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep.1]
    exact ih hstep.2

/-! ### Input, output and halting -/

theorem relevant_initList (s : List (tm.Γ tm.k₀)) : Relevant tm (initList tm s).stk := by
  intro k x hx
  by_cases hk : k = tm.k₀
  · exact Set.mem_union_right _ hk
  · simp [initList, hk] at hx

theorem encStk_initList (s : List (tm.Γ tm.k₀)) :
    encStk tm (initList tm s).stk = Function.update (fun _ ↦ []) tm.k₀ (s.map (code tm tm.k₀)) := by
  funext k
  by_cases hk : k = tm.k₀
  · subst hk
    simp [encStk, initList]
  · simp [encStk, initList, hk]

theorem haltList_stk_k₁ (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

theorem iterate_none (m : ℕ) : (flip bind tm.step)^[m] none = none := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih

/-- Before the halting configuration of a run, every configuration is running. -/
theorem running_before_halt {c₀ : tm.Cfg} {s : ℕ} {c : tm.Cfg}
    (hs : (flip bind tm.step)^[s] (some c₀) = some c) {j : ℕ} (hj : j < s) :
    ∃ c', (flip bind tm.step)^[j] (some c₀) = some c' ∧ c'.l.isSome := by
  have hsplit : ∀ m, (flip bind tm.step)^[j + m] (some c₀) =
      (flip bind tm.step)^[m] ((flip bind tm.step)^[j] (some c₀)) := fun m ↦ by
    rw [Nat.add_comm, Function.iterate_add_apply]
  cases hrun : (flip bind tm.step)^[j] (some c₀) with
  | none =>
    have := hsplit (s - j)
    rw [Nat.add_sub_cancel' hj.le, hs, hrun, iterate_none] at this
    exact absurd this (by simp)
  | some c' =>
    refine ⟨c', rfl, ?_⟩
    cases hl : c'.l with
    | some _ => rfl
    | none =>
      have hstep : flip bind tm.step (some c') = none := by
        obtain ⟨l, v, S⟩ := c'
        subst hl
        rfl
      have := hsplit (s - j)
      rw [Nat.add_sub_cancel' hj.le, hs, hrun, show s - j = (s - j - 1) + 1 by omega,
        Function.iterate_succ_apply, hstep, iterate_none] at this
      exact absurd this (by simp)

end Machine

/-! ### Turing-computable functions are computable -/

attribute [local instance] primcodableArrow primcodableΛ primcodableσ

/-- **Turing-computable functions are recursive.** A function `ℕ → ℕ` computed by a bundled
finite multi-stack machine (`FinTM2`) under the binary encoding `encodeNat` is `Computable`. -/
theorem computable_of_tm2Computable {f : ℕ → ℕ} (h : TM2Computable encodeNat encodeNat f) :
    Computable f := by
  let tm := h.tm
  let initC : ℕ → CodedCfg tm := fun n ↦ (some tm.main, tm.initialState,
    Function.update (fun _ ↦ []) tm.k₀
      ((encodeNat n).map fun b ↦ code tm tm.k₀ (h.inputAlphabet.invFun b)))
  let halted : Option (CodedCfg tm) → Bool := fun o ↦ o.elim true fun c ↦ c.1.isNone
  let decOut : ℕ → Bool := fun c ↦ ((decode tm tm.k₁ c).map h.outputAlphabet).getD false
  let out : Option (CodedCfg tm) → ℕ := fun o ↦
    bitsVal ((o.elim [] fun c ↦ c.2.2 tm.k₁).map decOut)
  have hinitP : Primrec fun n ↦ some (initC n) := by
    refine Primrec.option_some.comp (Primrec.pair (Primrec.const _) (Primrec.pair
      (Primrec.const _) ((primrec_arrow_update tm.k₀).comp (Primrec.const _) ?_)))
    exact Primrec.list_map primrec_encodeNat
      ((Primrec.dom_finite fun b : Bool ↦ code tm tm.k₀ (h.inputAlphabet.invFun b)).comp
        Primrec.snd).to₂
  have hhaltedP : Primrec halted :=
    (Primrec.option_casesOn Primrec.id (Primrec.const true)
      ((Primrec.dom_finite fun l : Option tm.Λ ↦ l.isNone).comp
        (Primrec.fst.comp Primrec.snd)).to₂).of_eq fun o ↦ by cases o <;> rfl
  have hdecOutP : Primrec decOut :=
    primrec_of_eventually_const (symList tm tm.k₁).length fun c hc ↦ by
      simp only [decOut, decode_eq_none tm hc, decode_eq_none tm le_rfl]
  have houtP : Primrec out :=
    primrec_bitsVal.comp (Primrec.list_map ((Primrec.option_casesOn Primrec.id
      (Primrec.const []) ((primrec_arrow_eval tm.k₁).comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun o ↦ by cases o <;> rfl)
      (hdecOutP.comp Primrec.snd).to₂)
  refine (partrec_run hinitP (primrec_optStepC tm) hhaltedP houtP).of_eq_tot fun n ↦ ?_
  -- the machine's run on `n`
  let input := (encodeNat n).map h.inputAlphabet.invFun
  let outL := (encodeNat (f n)).map h.outputAlphabet.invFun
  obtain ⟨s, hs⟩ := h.outputsFun n
  change (flip bind tm.step)^[s] (some (initList tm input)) = some (haltList tm outL) at hs
  have hinit : enc tm (initList tm input) = initC n := by
    simp only [enc, initC, encStk_initList, input, List.map_map]
    rfl
  have hrun : ∀ j, (optStepC tm)^[j] (some (initC n)) =
      ((flip bind tm.step)^[j] (some (initList tm input))).map (enc tm) ∧
      ∀ c ∈ (flip bind tm.step)^[j] (some (initList tm input)), Relevant tm c.stk := by
    intro j
    have := optStepC_iterate tm j (o := some (initList tm input)) fun c hc ↦ by
      obtain rfl := Option.mem_some_iff.mp hc
      exact relevant_initList tm input
    rwa [Option.map_some, hinit] at this
  have hmem : s ∈ Nat.rfind fun k ↦ Part.some (halted ((optStepC tm)^[k] (some (initC n)))) := by
    refine Nat.mem_rfind.mpr ⟨?_, fun {m} hm ↦ ?_⟩
    · rw [(hrun s).1, hs]
      exact Part.mem_some _
    · obtain ⟨c, hc, hl⟩ := running_before_halt tm hs hm
      rw [(hrun m).1, hc]
      simp only [halted, Option.map_some, Option.elim_some, enc]
      simpa using hl
  refine Part.mem_map_iff _ |>.mpr ⟨s, hmem, ?_⟩
  have hrel := (hrun s).2 (haltList tm outL) (by rw [hs]; rfl)
  rw [(hrun s).1, hs]
  simp only [out, Option.map_some, Option.elim_some, enc, encStk, haltList_stk_k₁, List.map_map]
  have hdec : ∀ x ∈ outL, (decOut ∘ code tm tm.k₁) x = h.outputAlphabet x := fun x hx ↦ by
    have hx' : x ∈ relevant tm tm.k₁ := hrel tm.k₁ x (by rw [haltList_stk_k₁]; exact hx)
    simp [decOut, decode_code tm hx']
  rw [List.map_congr_left hdec]
  simp [outL, List.map_map, bitsVal_encodeNat]

end MetaMathlibExt.TM2Recursive
