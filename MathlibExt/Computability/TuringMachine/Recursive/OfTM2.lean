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

/-- **Binary encoding, least significant bit first.** For every natural number $n \neq 0$, the
binary encoding of $n$ is the list whose first bit is true exactly when $n$ is odd, followed by
the binary encoding of $\lfloor n/2 \rfloor$. -/
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

/-- **Value of a little-endian bit list.** The value of a list of bits $b_0, b_1, \dots, b_{m-1}$
is $\sum_{i < m} [b_i]\, 2^i$, where $[b_i]$ is $1$ if $b_i$ is true and $0$ otherwise. So the
first bit is the least significant, and the empty list has value $0$. -/
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

/-- **Running a primitive recursive machine is partial recursive.** Let $\alpha$, $\sigma$ and
$\beta$ be primitive recursively encodable types, and let $\mathrm{init} : \alpha \to \sigma$,
$\mathrm{step} : \sigma \to \sigma$, $\mathrm{halted} : \sigma \to \mathrm{Bool}$ and
$\mathrm{out} : \sigma \to \beta$ be primitive recursive. Then the partial function sending $a$
to $\mathrm{out}(\mathrm{step}^k(\mathrm{init}(a)))$, where $k$ is the least natural number for
which $\mathrm{halted}(\mathrm{step}^k(\mathrm{init}(a)))$ is true, and undefined when there is
no such $k$, is partial recursive. -/
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

/-- **Eventually constant functions on ℕ are primitive recursive.** Let $\beta$ be a primitive
recursively encodable type. If $g : \mathbb{N} \to \beta$ and $N \in \mathbb{N}$ satisfy
$g(c) = g(N)$ for all $c \ge N$, then $g$ is primitive recursive. -/
theorem primrec_of_eventually_const {g : ℕ → β} (N : ℕ) (hg : ∀ c ≥ N, g c = g N) :
    Primrec g := by
  refine ((Primrec.list_getD (g N)).comp (Primrec.const (List.ofFn fun i : Fin N ↦ g i))
    Primrec.id).of_eq fun c ↦ ?_
  by_cases hc : c < N
  · rw [List.getD_eq_getElem _ _ (by simpa using hc)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using hc), hg c (by omega)]

/-- **Eventually constant functions of a finite parameter are primitive recursive.** Let $\alpha$
be a finite primitive recursively encodable type and $\beta$ a primitive recursively encodable
type. If $g : \alpha \to \mathbb{N} \to \beta$ and $N \in \mathbb{N}$ satisfy
$g(a, c) = g(a, N)$ for all $a \in \alpha$ and all $c \ge N$, then $g$ is primitive recursive as
a function of two arguments. -/
theorem primrec₂_of_eventually_const [Finite α] {g : α → ℕ → β} (N : ℕ)
    (hg : ∀ a, ∀ c ≥ N, g a c = g a N) : Primrec₂ g := by
  refine (Primrec.option_getD.comp (Primrec.list_getElem?.comp
    ((Primrec.dom_finite fun a ↦ List.ofFn fun i : Fin N ↦ g a i).comp Primrec.fst)
    Primrec.snd) ((Primrec.dom_finite fun a ↦ g a N).comp Primrec.fst)).to₂.of_eq ?_
  intro a c
  by_cases hc : c < N
  · simp [hc]
  · simp [hc, hg a c (by omega)]

/-- **Joint primitive recursion over a finite first argument.** Let $\alpha$, $\beta$ and
$\sigma$ be primitive recursively encodable types with $\alpha$ finite, and let
$g : \alpha \to \beta \to \sigma$. If $b \mapsto g(a, b)$ is primitive recursive for every
$a \in \alpha$, then $g$ is primitive recursive as a function of two arguments. -/
theorem primrec₂_of_finite_left [Finite α] {σ : Type*} [Primcodable σ] {g : α → β → σ}
    (hg : ∀ a, Primrec (g a)) : Primrec₂ g := by
  have := Fintype.ofFinite α
  let e := Fintype.equivFin α
  have h : Primrec₂ fun (i : Fin (Fintype.card α)) b ↦ g (e.symm i) b :=
    Primrec.fin_curry₁.mpr fun i ↦ hg _
  exact (h.comp ((Primrec.dom_finite e).comp Primrec.fst) Primrec.snd).of_eq fun p ↦ by simp

end Helpers

/-- **Encoding of functions on a finite type.** For a finite type $K$ and a primitive recursively
encodable type $\beta$, the primitive recursive encoding of the functions $K \to \beta$
transported from that of the functions $\mathrm{Fin}\, n \to \beta$, where $n$ is the cardinality
of $K$, along a chosen bijection between $K$ and $\mathrm{Fin}\, n$. -/
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

/-- **Symbols a statement may push.** For a finite multi-stack machine, a stack $k$ and a
statement $q$ over the machine's stack alphabets, labels and internal states, the set of symbols
of stack $k$ consisting of every value, at every internal state, of the symbol function of every
push instruction onto stack $k$ that occurs in $q$, in either branch of each conditional. -/
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

/-- **Relevant symbols of a stack.** For a stack index $k$, the relevant symbols of stack $k$ are
the symbols $f(v)$ of $\Gamma_k$, for every internal state $v$, over all statements that push $f$
onto stack $k$ and occur in the program of some label, together with, when $k$ is the input stack
$k_0$, every symbol of $\Gamma_{k_0}$.

Along a run started from an initial configuration, only relevant symbols occur on the stacks. -/
def relevant (k : tm.K) : Set (tm.Γ k) :=
  (⋃ l, pushes tm k (tm.m l)) ∪ {_x | k = tm.k₀}

theorem relevant_finite (k : tm.K) : (relevant tm k).Finite := by
  refine (Set.finite_iUnion fun l ↦ pushes_finite tm k (tm.m l)).union ?_
  by_cases h : k = tm.k₀
  · subst h
    exact Set.toFinite _
  · simp [h]

/-- **Enumeration of the relevant symbols of a stack.** For a finite multi-stack machine and a
stack index $k$, a list without repetitions whose entries are exactly the relevant symbols of
stack $k$, in an order fixed by choice. -/
noncomputable def symList (k : tm.K) : List (tm.Γ k) := (relevant_finite tm k).toFinset.toList

/-- **Code of a stack symbol.** For a finite multi-stack machine, a stack index $k$ and a symbol
$x$ of stack $k$, the code of $x$ is the position of $x$ (counting from $0$) in the chosen
enumeration of the relevant symbols of stack $k$, or the length of that enumeration if $x$ is not
a relevant symbol. -/
noncomputable def code (k : tm.K) (x : tm.Γ k) : ℕ :=
  letI := Classical.decEq (tm.Γ k)
  (symList tm k).idxOf x

/-- **Decoding a stack symbol.** For a finite multi-stack machine, a stack index $k$ and a natural
number $c$, the decoding of $c$ is the entry at position $c$ (counting from $0$) of the chosen
enumeration of the relevant symbols of stack $k$, and is undefined when $c$ is at least the length
of that enumeration. -/
noncomputable def decode (k : tm.K) (c : ℕ) : Option (tm.Γ k) := (symList tm k)[c]?

theorem decode_code {k : tm.K} {x : tm.Γ k} (hx : x ∈ relevant tm k) :
    decode tm k (code tm k x) = some x := by
  let _ := Classical.decEq (tm.Γ k)
  have hmem : x ∈ symList tm k := by simpa [symList] using hx
  simp [decode, code, List.getElem?_idxOf hmem]

theorem decode_eq_none {k : tm.K} {c : ℕ} (hc : (symList tm k).length ≤ c) :
    decode tm k c = none := by
  simp [decode, hc]

/-- **Stacks with only relevant symbols.** A family of stacks $S$, consisting of a list $S_k$ of
symbols of $\Gamma_k$ for each stack index $k$, has only relevant symbols when for every stack
index $k$, every symbol on $S_k$ is a relevant symbol of stack $k$. -/
def Relevant (S : ∀ k, List (tm.Γ k)) : Prop := ∀ k, ∀ x ∈ S k, x ∈ relevant tm k

/-! ### The coded machine -/

attribute [local instance] primcodableArrow

/-- **Encoding of labels.** For a finite multi-stack machine, the primitive recursive encoding of
its finite type of labels transported from that of $\mathrm{Fin}\, n$, where $n$ is the number of
labels, along a chosen bijection between the two. -/
@[instance_reducible]
noncomputable def primcodableΛ : Primcodable tm.Λ :=
  Primcodable.ofEquiv _ (Fintype.equivFin tm.Λ)

/-- **Encoding of internal states.** For a finite multi-stack machine, the primitive recursive
encoding of its finite type of internal states transported from that of $\mathrm{Fin}\, n$, where
$n$ is the number of internal states, along a chosen bijection between the two. -/
@[instance_reducible]
noncomputable def primcodableσ : Primcodable tm.σ :=
  Primcodable.ofEquiv _ (Fintype.equivFin tm.σ)

attribute [local instance] primcodableΛ primcodableσ

/-- **Coded configurations of a multi-stack machine.** For a finite multi-stack machine with label
set $\Lambda$, internal state set $\sigma$ and stack index set $K$, a coded configuration is a
triple consisting of an optional label in $\Lambda$ (no label marks a halted configuration), an
internal state in $\sigma$, and an assignment of a list of natural numbers to each $k \in K$. -/
abbrev CodedCfg := Option tm.Λ × tm.σ × (tm.K → List ℕ)

/-- **Coded stacks.** For a finite multi-stack machine, the coded stacks of a family $S$ of stacks
assign to each stack index $k$ the list obtained from the stack $S_k$ by replacing each symbol
with its code. -/
noncomputable def encStk (S : ∀ k, List (tm.Γ k)) : tm.K → List ℕ :=
  fun k ↦ (S k).map (code tm k)

/-- **Coding a configuration.** For a finite multi-stack machine, the coded configuration of a
configuration $c$ has the same optional label and internal state as $c$, and the coded stacks of
the stacks of $c$. -/
noncomputable def enc (c : tm.Cfg) : CodedCfg tm := (c.l, c.var, encStk tm c.stk)

/-- **Reading the top of a coded stack.** Let $k$ be a stack index of the machine and let $S$ assign
to each stack index $j$ a list $S_j$ of natural numbers (codes of symbols). The top of stack $k$ as
read from $S$ is no symbol when $S_k$ is empty. Otherwise, if $c$ is the first entry of $S_k$, it is
the decoding of $c$: the symbol of $\Gamma_k$ at position $c$, counting from $0$, in the list of
relevant symbols of stack $k$, or no symbol when $c$ is at least the length of that list. -/
noncomputable def readTop (k : tm.K) (S : tm.K → List ℕ) : Option (tm.Γ k) :=
  (S k).head?.bind (decode tm k)

/-- **The coded execution of a statement.** This mirrors the machine's execution of one statement
on stacks of symbol codes. Given a statement $q$, an internal state $v$ and coded stacks $S$ (a list
$S_k$ of natural numbers for each stack index $k$), it returns a coded configuration (an optional
label, an internal state and coded stacks), by recursion on $q$. A push of $f$ onto stack $k$
followed by $q'$ replaces $S_k$ by the code of the symbol $f(v)$ of stack $k$ followed by $S_k$, and
continues with $q'$. A peek at stack $k$ with update $f$ followed by $q'$ continues with $q'$ from
the internal state $f(v, t)$, where $t$ is the top of coded stack $k$ as read from $S$. A pop is
the same as a peek but also removes the first entry of $S_k$ (if there is one). A load of $a$
followed by $q'$ continues with $q'$ from the internal state $a(v)$. A branch on $f$ executes its
first statement if $f(v)$ is true and its second otherwise. A goto $f$ stops with label $f(v)$,
internal state $v$ and stacks $S$, and a halt stops with no label, internal state $v$ and stacks
$S$. -/
noncomputable def stepAuxC :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → tm.σ → (tm.K → List ℕ) → CodedCfg tm
  | .push k f q, v, S => stepAuxC q v (Function.update S k (code tm k (f v) :: S k))
  | .peek k f q, v, S => stepAuxC q (f v (readTop tm k S)) S
  | .pop k f q, v, S => stepAuxC q (f v (readTop tm k S)) (Function.update S k (S k).tail)
  | .load a q, v, S => stepAuxC q (a v) S
  | .branch f q₁ q₂, v, S => cond (f v) (stepAuxC q₁ v S) (stepAuxC q₂ v S)
  | .goto f, v, S => (some (f v), v, S)
  | .halt, v, S => (none, v, S)

/-- **The coded step.** For a coded configuration $(l, v, S)$, consisting of an optional label $l$,
an internal state $v$ and coded stacks $S$, the coded step is undefined when $l$ is absent (the
configuration has halted). When $l$ is a label, it is the coded configuration obtained by the coded
execution of the program statement of $l$ from the internal state $v$ on the coded stacks $S$. -/
noncomputable def stepC (c : CodedCfg tm) : Option (CodedCfg tm) :=
  c.1.map fun l ↦ stepAuxC tm (tm.m l) c.2.1 c.2.2

/-! ### The coded step is primitive recursive -/

/-- **Updating the state from the top of a coded stack is primitive recursive.** Let $k$ be a
stack index of a finite multi-stack machine, write $\Gamma_k$ for the alphabet of stack $k$, and
let $f$ be any function sending an internal state and an optional symbol of $\Gamma_k$ to an
internal state. Then the map sending an internal state $v$ and coded stacks $S$ (a list $S_j$ of
natural numbers for each stack index $j$) to $f(v, t)$, where $t$ is the top of stack $k$ as read
from $S$, is primitive recursive as a function of two arguments, for the encoding of internal
states and the encoding of functions on the finite type of stack indices. -/
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

/-- **Coded stacks after replacing one stack.** For a finite multi-stack machine, a family $S$ of
stacks, a stack index $k$ and a list $l$ of symbols of stack $k$, the coded stacks of the family
obtained from $S$ by replacing stack $k$ with $l$ are the coded stacks of $S$ with the entry at
$k$ replaced by the list obtained from $l$ by replacing each symbol with its code. -/
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

/-- **The coded step on optional configurations.** For a finite multi-stack machine, the coded
step extended to optional coded configurations: it sends the absent configuration to the absent
configuration, and a coded configuration $c$ to the coded step of $c$, which is itself absent
when $c$ has halted. -/
noncomputable def optStepC (o : Option (CodedCfg tm)) : Option (CodedCfg tm) := o.bind (stepC tm)

theorem primrec_optStepC : Primrec (optStepC tm) :=
  Primrec.option_bind Primrec.id ((primrec_stepC tm).comp Primrec.snd).to₂

/-- **The coded run simulates the machine's run.** Let $o$ be either no configuration or a
configuration of a finite multi-stack machine all of whose stack symbols are relevant. Let
running one step send a running configuration to its successor, and a halted configuration or no
configuration to no configuration. Then for every $j$, applying the coded step on optional
configurations $j$ times to the coding of $o$ gives the coding of the result of running $j$
steps from $o$, and if running $j$ steps from $o$ gives a configuration, all of its stack symbols
are relevant. -/
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

/-- **The initial stacks have only relevant symbols.** For a finite multi-stack machine and every
list $s$ of symbols of the input alphabet $\Gamma_{k_0}$, the stacks of the initial configuration
with input $s$ (the list $s$ on the input stack $k_0$ and every other stack empty) have only
relevant symbols. -/
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

/-- **Configurations before a reached one are running.** Write $\mathrm{step}$ for the machine's
step map, which is undefined on halted configurations (those with no label), and iterate it as a
partial map. Let $c_0$ and $c$ be configurations and $s$ a natural number such that $s$ steps from
$c_0$ reach $c$. Then for every $j < s$, $j$ steps from $c_0$ reach some configuration $c'$, and
$c'$ is running: its label is defined. -/
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

/-- **Turing-computable functions are recursive.** Let $f : \mathbb{N} \to \mathbb{N}$ and suppose
that some finite multi-stack Turing machine (finitely many stacks, labels and internal states,
and a finite input alphabet), together with identifications of its input and output stack
alphabets with the booleans, computes $f$ under the binary encoding of natural numbers (least
significant bit first, with $0$ encoded as the empty list): for every $n$, the machine started
at its main label in its initial internal state, with the encoding of $n$ on its input stack and
all other stacks empty, eventually reaches the halted configuration whose output stack holds the
encoding of $f(n)$, whose other stacks are empty and whose internal state is the initial one.
Then $f$ is computable (recursive). -/
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
