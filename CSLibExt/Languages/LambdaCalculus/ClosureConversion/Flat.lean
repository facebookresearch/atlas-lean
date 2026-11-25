/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flat closure conversion
-/
module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Correctness
public import Mathlib.Data.List.Dedup

/-!
# Flat closure conversion

The free-variable variant of closure conversion (Appel, *Compiling with
Continuations*, Chapter 10, "flat closures"): a lambda captures only the free
variables of its body, each once, instead of the whole environment of
`Correctness.lean`.

For `λ. b`, let `fvs := (freeIndices 1 b).dedup` be the outer variables free in
the lambda. `convertFlat acc t` translates `t` with accessors `acc`:

* `x_i ↦ acc i`;
* `λ. b ↦ (code ⟦b⟧', env)`, where `env` packs `acc i` for `i ∈ fvs` in order,
  and `⟦b⟧'` converts `b` with `x₀ ↦ fst #0` and `x_{j+1} ↦ fst (sndᵏ (snd #0))`
  for `k` the position of `j` in `fvs`;
* `f a ↦ let c = ⟦f⟧ in (fst c) (⟦a⟧, snd c)`, as before.

Correctness (`convertFlat_correct`) only asks the accessors to implement the
variables free in the term (`FlatAccRel`), and relates source closures to
target closures whose environment holds values related to exactly the
captured variables (`FlatValRel`). Closed programs are converted correctly
(`closureConvertFlat_correct`), every code body is closed
(`convertFlat_scoped`, `closureConvertFlat_scoped`), and each closure's
environment has exactly one entry per distinct free variable
(`envFlat_length`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion

universe u

variable {Base : Type u}

open Target Target.Tm Stlc.RawTm

/-- **Free variables one binder deeper.** For every raw term $t$ and natural numbers $d$ and $j$,
$j$ is a free index of $t$ at binder depth $d + 1$ if and only if $j + 1$ is a free index of $t$
at binder depth $d$. -/
theorem mem_freeIndices_succ (t : Stlc.RawTm Base) (d j : Nat) :
    j ∈ freeIndices (d + 1) t ↔ j + 1 ∈ freeIndices d t := by
  induction t generalizing d with
  | var n =>
      simp only [freeIndices]
      by_cases h₁ : d + 1 ≤ n
      · have h₂ : d ≤ n := by omega
        simp only [h₁, h₂, ↓reduceIte, List.mem_singleton]
        omega
      · by_cases h₂ : d ≤ n
        · simp only [h₁, h₂, ↓reduceIte, List.mem_singleton, List.not_mem_nil, false_iff]
          omega
        · simp [h₁, h₂]
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih => simp only [freeIndices_lam]; exact ih (d + 1)

/-- **Variables captured by a lambda.** For a raw term $b$, the captured variables of $b$ form
the list of free indices of $b$ at binder depth $1$ with duplicates removed: the de Bruijn
indices $j$ such that variable $j + 1$ occurs free in $b$, that is, the free variables of the
abstraction $\lambda.\,b$, each listed once. -/
def captured (body : Stlc.RawTm Base) : List Nat := (freeIndices 1 body).dedup

theorem mem_captured {body : Stlc.RawTm Base} {j : Nat} :
    j ∈ captured body ↔ j + 1 ∈ freeIndices 0 body := by
  rw [captured, List.mem_dedup, mem_freeIndices_succ]

/-- **Flat closure environment.** For a map $\mathrm{acc}$ from natural numbers to target terms
and a list $i_1, \dots, i_n$ of natural numbers, the flat environment is the target term
$(\mathrm{acc}(i_1), (\mathrm{acc}(i_2), \dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$, which
packs $\mathrm{acc}(i)$ for each $i$ in the list, in order, as nested pairs ending in
$\mathsf{unit}$; the empty list gives $\mathsf{unit}$. -/
def envFlat (acc : Nat → Tm) : List Nat → Tm
  | [] => .unit
  | i :: is => .pair (acc i) (envFlat acc is)

/-- **Accessors inside flat code.** For a list $L$ of natural numbers, the flat accessors for $L$
assign a target term to each variable: variable $0$ is sent to $\mathsf{fst}\,\#0$, and variable
$j + 1$ is sent to $\mathsf{fst}\,(\mathsf{snd}^k\,(\mathsf{snd}\,\#0))$. Here $\#0$ is target
variable $0$, $\mathsf{snd}^k$ applies the second projection $k$ times, and $k$ is the index of the
first occurrence of $j$ in $L$, or the length of $L$ if $j$ does not occur in $L$.

Inside flat code the parameter $\#0$ is the pair of the argument and the environment, so variable
$0$ is the argument and variable $j + 1$ is the entry of the environment at the position of $j$
in $L$. -/
def flatAcc (fvs : List Nat) : Nat → Tm
  | 0 => .fst (.var 0)
  | j + 1 => .fst (snds (fvs.idxOf j) (.snd (.var 0)))

/-- **Flat closure conversion.** Given accessors $\mathrm{acc}$, a map from natural numbers to
target terms, the flat conversion $C_{\mathrm{acc}}(t)$ of a raw term $t$ is defined by recursion
on $t$. A variable $i$ becomes $\mathrm{acc}(i)$. A lambda $\lambda.\,b$, whose parameter type is
ignored, becomes the pair $(\mathsf{code}\,C_{\mathrm{acc}'}(b), e)$. Here $i_1, \dots, i_n$ are
the captured variables of $b$, the environment $e$ is
$(\mathrm{acc}(i_1), (\mathrm{acc}(i_2), \dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$, and
$\mathrm{acc}'$ sends $0$ to $\mathsf{fst}\,(\mathsf{var}\,0)$ and $j + 1$ to
$\mathsf{fst}\,(\mathsf{snd}^{k+1}\,(\mathsf{var}\,0))$, where $k$ is the position of $j$ in that
list, counting from $0$ (the length $n$ if $j$ does not occur). An application $f\,a$ becomes
$\mathsf{let}\ C_{\mathrm{acc}}(f)\ \mathsf{in}\ (\mathsf{fst}\,(\mathsf{var}\,0))\,
(C_{\mathrm{acc}^{+}}(a), \mathsf{snd}\,(\mathsf{var}\,0))$, where $\mathsf{var}\,0$ is the
variable bound by the $\mathsf{let}$ and $\mathrm{acc}^{+}(i)$ is the shift of $\mathrm{acc}(i)$. -/
def convertFlat : (Nat → Tm) → Stlc.RawTm Base → Tm
  | acc, .var i => acc i
  | acc, .lam _ body =>
      .pair (.code (convertFlat (flatAcc (captured body)) body)) (envFlat acc (captured body))
  | acc, .app f a =>
      .letIn (convertFlat acc f)
        (.app (.fst (.var 0)) (.pair (convertFlat (fun i => (acc i).shift) a) (.snd (.var 0))))

/-- **Flat closure conversion of a program.** The flat closure conversion of a raw term $t$ is
the flat conversion of $t$ with the accessors $i \mapsto \mathsf{var}\,i$, which send each free
variable $i$ of $t$ to the target variable $i$. It is meant for closed terms. -/
def closureConvertFlat (t : Stlc.RawTm Base) : Tm := convertFlat .var t

/-- **Flat value relation.** The flat value relation between source values and target values is
the least relation with the following property. Let $b$ be a raw term, $\rho$ a list of source
values of length $|\rho|$, $c = (c_0, \dots, c_{m-1})$ the list of variables captured by
$\lambda. b$, and $w_0, \dots, w_{m-1}$ target values, as many as there are captured variables. If,
for every $k < m$, $c_k < |\rho|$ and the entry of $\rho$ at index $c_k$ (counting from $0$) is
related to $w_k$, then the source closure of $b$ over $\rho$ is related to the target value
$(\mathsf{code}\,B, \mathrm{enc}(w_0, \dots, w_{m-1}))$, where $B$ is the flat closure conversion
of $b$ with the flat accessors for $c$, and $\mathrm{enc}$ encodes a list of target values as
nested pairs ending in $\mathsf{unit}$. -/
inductive FlatValRel : Source.Value Base → Value → Prop
  | clo {body : Stlc.RawTm Base} {ρ : List (Source.Value Base)} {ws : List Value}
      (hlen : (captured body).length = ws.length)
      (hbound : ∀ k (h₁ : k < (captured body).length), (captured body)[k] < ρ.length)
      (hrel : ∀ k (h₁ : k < (captured body).length) (h₂ : k < ws.length),
        FlatValRel (ρ[(captured body)[k]]'(hbound k h₁)) ws[k]) :
      FlatValRel (.clo body ρ)
        (.pair (.code (convertFlat (flatAcc (captured body)) body)) (encodeEnv ws))

/-- **Accessors implementing the free variables of a term.** Let $\rho$ be a list of source
values of length $|\rho|$, $\rho_t$ a list of target values, $\mathrm{acc}$ a map assigning a target
term to each natural number, and $t$ a raw term. The accessors $\mathrm{acc}$ implement $t$ for
$\rho$ in $\rho_t$ when, for every free variable $i$ of $t$, $i < |\rho|$ and $\mathrm{acc}(i)$
evaluates in the target environment $\rho_t$ to a target value that is related, by the flat value
relation, to the entry of $\rho$ at index $i$ (counting from $0$). -/
def FlatAccRel (ρ : List (Source.Value Base)) (ρt : List Value) (acc : Nat → Tm)
    (t : Stlc.RawTm Base) : Prop :=
  ∀ i ∈ freeIndices 0 t, ∃ h : i < ρ.length, ∃ w, Eval ρt (acc i) w ∧ FlatValRel ρ[i] w

theorem FlatAccRel.mono {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    {t t' : Stlc.RawTm Base} (h : FlatAccRel ρ ρt acc t)
    (hsub : ∀ i, i ∈ freeIndices 0 t' → i ∈ freeIndices 0 t) : FlatAccRel ρ ρt acc t' :=
  fun i hi => h i (hsub i hi)

theorem FlatAccRel.shift {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    {t : Stlc.RawTm Base} (h : FlatAccRel ρ ρt acc t) (x : Value) :
    FlatAccRel ρ (x :: ρt) (fun i => (acc i).shift) t := by
  intro i hi
  obtain ⟨hlt, w, hw, hrel⟩ := h i hi
  exact ⟨hlt, w, hw.shift x, hrel⟩

/-- **Evaluating a flat environment.** Let $\rho$ be a source environment, $\rho_t$ a target
environment, $\mathrm{acc}$ a map from natural numbers to target terms, and $i_1, \dots, i_n$ a
list of natural numbers. Write $\rho_i$ for the entry of $\rho$ at index $i$, counting from $0$.
Suppose every $i$ in the list is less than the length of $\rho$ and $\mathrm{acc}(i)$ evaluates
in $\rho_t$ to a target value related to $\rho_i$ by the flat value relation. Then there are
target values $w_1, \dots, w_n$ such that the flat environment
$(\mathrm{acc}(i_1), (\dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$ evaluates in $\rho_t$ to
$(w_1, (\dots, (w_n, \mathsf{unit})\dots))$, and for each $k$ the index $i_k$ is less than the
length of $\rho$ and $w_k$ is related to $\rho_{i_k}$ by the flat value relation. -/
theorem eval_envFlat {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm} :
    ∀ (is : List Nat), (∀ i ∈ is, ∃ h : i < ρ.length, ∃ w, Eval ρt (acc i) w ∧
      FlatValRel ρ[i] w) →
    ∃ ws : List Value, Eval ρt (envFlat acc is) (encodeEnv ws) ∧ is.length = ws.length ∧
      ∃ hbound : ∀ k (h₁ : k < is.length), is[k] < ρ.length,
      ∀ k (h₁ : k < is.length) (h₂ : k < ws.length), FlatValRel (ρ[is[k]]'(hbound k h₁)) ws[k]
  | [], _ => ⟨[], .unit, rfl, fun k h₁ => absurd h₁ (Nat.not_lt_zero k),
      fun k h₁ => absurd h₁ (Nat.not_lt_zero k)⟩
  | i :: is, h => by
      obtain ⟨hi, w, hw, hrel⟩ := h i List.mem_cons_self
      obtain ⟨ws, hws, hlen, hbound, hrels⟩ :=
        eval_envFlat is fun j hj => h j (List.mem_cons_of_mem i hj)
      refine ⟨w :: ws, .pair hw hws, by simp [hlen], fun k h₁ => ?_, fun k h₁ h₂ => ?_⟩
      · cases k with
        | zero => exact hi
        | succ k => exact hbound k (Nat.lt_of_succ_lt_succ h₁)
      · cases k with
        | zero => exact hrel
        | succ k => exact hrels k (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- **Length of an evaluated flat environment.** Let $\mathrm{acc}$ be a map from natural numbers
to target terms and $i_1, \dots, i_n$ a list of natural numbers. If the flat environment
$(\mathrm{acc}(i_1), (\dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$ evaluates in some target
environment to the encoding $(w_1, (\dots, (w_k, \mathsf{unit})\dots))$ of a list of target values
$w_1, \dots, w_k$, then $k = n$. -/
theorem envFlat_length {ρt : List Value} {acc : Nat → Tm}
    {is : List Nat} {ws : List Value} (h : Eval ρt (envFlat acc is) (encodeEnv ws)) :
    ws.length = is.length := by
  induction is generalizing ws with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => cases h
  | cons i is ih =>
      cases ws with
      | nil => cases h
      | cons w ws =>
          cases h with
          | pair _ hb => simp [ih hb]

/-- **Flat accessors implement the variables of a closure body.** Let $b$ be a raw term, let
$c = (c_0, \dots, c_{m-1})$ be the list of variables captured by $\lambda. b$, let $\rho$ be a list
of source values of length $|\rho|$, write $\rho_n$ for the entry of $\rho$ at index $n$ (counting
from $0$), and let $w_0, \dots, w_{m-1}$ be target values such that $c_k < |\rho|$ and $\rho_{c_k}$
is related to $w_k$ by the flat value relation for every $k < m$. If a source value $v$ is related
to a target value $w$ by the flat value relation, then the flat accessors for $c$ implement the
free variables of $b$ for the source environment $v :: \rho$ (the list $\rho$ with $v$ added at
index $0$) in the one-entry target environment $[(w, \mathrm{enc}(w_0, \dots, w_{m-1}))]$, where
$\mathrm{enc}$ encodes a list of target values as nested pairs ending in $\mathsf{unit}$. That is,
for every free variable $i$ of $b$, $i < |\rho| + 1$ and the flat accessor for $i$ evaluates in
that target environment to a target value related to the entry of $v :: \rho$ at index $i$ by the
flat value relation. -/
theorem flatAccRel_flatAcc {v : Source.Value Base} {ρ : List (Source.Value Base)}
    {body : Stlc.RawTm Base} {w : Value} {ws : List Value} (hvw : FlatValRel v w)
    (hlen : (captured body).length = ws.length)
    (hbound : ∀ k (h₁ : k < (captured body).length), (captured body)[k] < ρ.length)
    (hrel : ∀ k (h₁ : k < (captured body).length) (h₂ : k < ws.length),
      FlatValRel (ρ[(captured body)[k]]'(hbound k h₁)) ws[k]) :
    FlatAccRel (v :: ρ) [.pair w (encodeEnv ws)] (flatAcc (captured body)) body := by
  intro i hi
  cases i with
  | zero => exact ⟨Nat.zero_lt_succ _, w, .fst (.var rfl), hvw⟩
  | succ j =>
      have hj : j ∈ captured body := mem_captured.mpr hi
      have hk : (captured body).idxOf j < (captured body).length :=
        List.idxOf_lt_length_of_mem hj
      have hkws : (captured body).idxOf j < ws.length := hlen ▸ hk
      have hget : (captured body)[(captured body).idxOf j] = j := List.getElem_idxOf hk
      have hlt : j < ρ.length := hget ▸ hbound _ hk
      refine ⟨Nat.succ_lt_succ hlt, ws[(captured body).idxOf j],
        eval_fst_snds (.snd (.var rfl)) hkws, ?_⟩
      have hrelk := hrel _ hk hkws
      have hρ : ρ[(captured body)[(captured body).idxOf j]]'(hbound _ hk) = ρ[j] := by
        simp only [hget]
      rw [hρ] at hrelk
      exact hrelk

/-- **Correctness of flat closure conversion.** Let $\rho$ be a source environment, $\rho_t$ a
target environment, $\mathrm{acc}$ a map from natural numbers to target terms, and $t$ a raw term
that evaluates to a source value $v$ in $\rho$. Suppose that for every free variable $i$ of $t$,
$i$ is less than the length of $\rho$ and $\mathrm{acc}(i)$ evaluates in $\rho_t$ to a target
value related by the flat value relation to the entry $\rho_i$ of $\rho$ at index $i$ (counting
from $0$). Then the flat conversion of $t$ with accessors $\mathrm{acc}$ evaluates in $\rho_t$ to
some target value related to $v$ by the flat value relation. -/
theorem convertFlat_correct {ρ : List (Source.Value Base)} {t : Stlc.RawTm Base}
    {v : Source.Value Base} (h : Source.Eval ρ t v) {ρt : List Value} {acc : Nat → Tm}
    (hacc : FlatAccRel ρ ρt acc t) :
    ∃ w, Eval ρt (convertFlat acc t) w ∧ FlatValRel v w := by
  induction h generalizing ρt acc with
  | @var ρ n v hn =>
      obtain ⟨hlt, w, hw, hrel⟩ := hacc n (by simp)
      have hv : ρ[n] = v := (List.getElem?_eq_some_iff.mp hn).2
      exact ⟨w, hw, hv ▸ hrel⟩
  | @lam ρ A body =>
      have hcap : ∀ i ∈ captured body, i ∈ freeIndices 0 (Stlc.RawTm.lam A body) := by
        intro i hi
        rw [freeIndices_lam, mem_freeIndices_succ]
        exact mem_captured.mp hi
      obtain ⟨ws, hws, hlen, hbound, hrel⟩ :=
        eval_envFlat (acc := acc) (captured body) fun i hi => hacc i (hcap i hi)
      exact ⟨_, .pair .code hws, .clo hlen hbound hrel⟩
  | @app ρ ρ' f a body v w' _ _ _ ihf iha ihb =>
      obtain ⟨wf, hwf, hrelf⟩ := ihf (hacc.mono fun i hi => by simp [hi])
      cases hrelf with
      | @clo _ _ ws hlen hbound hrel =>
          obtain ⟨wa, hwa, hrela⟩ := iha ((hacc.mono fun i hi => by simp [hi]).shift _)
          obtain ⟨wb, hwb, hrelb⟩ := ihb (flatAccRel_flatAcc hrela hlen hbound hrel)
          refine ⟨wb, .letIn hwf (.app (.fst (.var rfl)) (.pair hwa (.snd (.var rfl))) ?_), hrelb⟩
          simpa using hwb

/-- **Correctness of flat closure conversion for closed programs.** Let $t$ be a closed raw
term, that is, one with no free variables. If $t$ evaluates to a source value $v$ in the empty
environment, then the flat closure conversion of $t$ evaluates in the empty target environment
to some target value $w$ related to $v$ by the flat value relation. -/
theorem closureConvertFlat_correct {t : Stlc.RawTm Base} {v : Source.Value Base}
    (ht : t.Closed) (h : Source.Eval [] t v) :
    ∃ w, Eval [] (closureConvertFlat t) w ∧ FlatValRel v w :=
  convertFlat_correct h fun i hi => by rw [ht] at hi; exact absurd hi List.not_mem_nil

theorem scoped_envFlat {m : Nat} {acc : Nat → Tm} :
    ∀ is : List Nat, (∀ i ∈ is, Scoped m (acc i)) → Scoped m (envFlat acc is)
  | [], _ => .unit
  | i :: is, h => .pair (h i List.mem_cons_self)
      (scoped_envFlat is fun j hj => h j (List.mem_cons_of_mem i hj))

theorem scoped_flatAcc (fvs : List Nat) (i : Nat) : Scoped 1 (flatAcc fvs i) := by
  cases i with
  | zero => exact .fst (.var Nat.zero_lt_one)
  | succ j => exact .fst (scoped_snds (.snd (.var Nat.zero_lt_one)))

/-- **Flat closure conversion preserves scoping.** Let $t$ be a raw term, $m$ a natural number
and $\mathrm{acc}$ a map from natural numbers to target terms. If $\mathrm{acc}(i)$ is scoped in
$m$ for every free variable $i$ of $t$, then the flat conversion of $t$ with accessors
$\mathrm{acc}$ is scoped in $m$. In particular every code body it contains is scoped in $1$, so
refers only to its parameter. -/
theorem convertFlat_scoped {m : Nat} (t : Stlc.RawTm Base) {acc : Nat → Tm}
    (hacc : ∀ i ∈ freeIndices 0 t, Scoped m (acc i)) : Scoped m (convertFlat acc t) := by
  induction t generalizing m acc with
  | var i => exact hacc i (by simp)
  | lam A body ih =>
      refine .pair (.code (ih fun i _ => scoped_flatAcc _ i)) (scoped_envFlat _ fun i hi => ?_)
      apply hacc
      rw [freeIndices_lam, mem_freeIndices_succ]
      exact mem_captured.mp hi
  | app f a ihf iha =>
      exact .letIn (ihf fun i hi => hacc i (by simp [hi]))
        (.app (.fst (.var (Nat.zero_lt_succ _)))
          (.pair (iha fun i hi => (hacc i (by simp [hi])).shift)
            (.snd (.var (Nat.zero_lt_succ _)))))

/-- **Flat closure conversion of a closed term is well scoped.** If a raw term $t$ is closed,
then its flat closure conversion is scoped in $0$: it has no free variables, and every code
body in it is scoped in $1$, so refers only to its parameter. -/
theorem closureConvertFlat_scoped {t : Stlc.RawTm Base} (ht : t.Closed) :
    Scoped 0 (closureConvertFlat t) :=
  convertFlat_scoped t fun i hi => by rw [ht] at hi; exact absurd hi List.not_mem_nil

end Cslib.Languages.LambdaCalculus.ClosureConversion
