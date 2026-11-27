/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure conversion and its correctness
-/
module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Source
public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Target
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.ElaborationStructural

/-!
# Closure conversion and its correctness

Closure conversion turns every lambda into an explicit closure: a pair of
closed code and a data structure holding the environment. This file uses the
whole-environment variant: a lambda in a scope of `n` variables captures all
`n` of them, as the nested pairs `(x₀, (x₁, … (xₙ₋₁, ())))`. Code receives the
pair `(argument, environment)` as its single parameter.

`convert acc n t` translates a source term `t` scoped in `n` variables, where
`acc i` is the target expression that fetches source variable `i`:

* `x_i ↦ acc i`;
* `λ. b ↦ (code ⟦b⟧', env)`, where `env` packs `acc 0, …, acc (n-1)` and `⟦b⟧'`
  converts `b` with the accessors `x₀ ↦ fst #0` and `x_{i+1} ↦ fst (sndⁱ (snd #0))`
  of the code's parameter `#0`;
* `f a ↦ let c = ⟦f⟧ in (fst c) (⟦a⟧, snd c)`.

Correctness (`convert_correct`): if the source term evaluates to `v` in the
environment semantics, the converted term evaluates to a target value related
to `v` (`ValRel`: a source closure is related to a pair of the converted code
of its body and an encoding of a pointwise-related environment). Every code
body produced is closed (`convert_scoped`), which is the point of closure
conversion: code can be hoisted to the top level.

The construction follows the textbook presentation of closure conversion
(Appel, *Compiling with Continuations*, Chapter 10) without the CPS stage and
with whole-environment rather than free-variable capture.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion

universe u

variable {Base : Type u}

open Target Target.Tm

/-- **Iterated second projection.** For a natural number $k$ and a target term $e$, the term
$\mathsf{snd}^k\,e$ applies the second projection $k$ times to $e$: $\mathsf{snd}^0\,e = e$ and
$\mathsf{snd}^{k+1}\,e = \mathsf{snd}\,(\mathsf{snd}^k\,e)$. -/
def snds : Nat → Tm → Tm
  | 0, e => e
  | k + 1, e => .snd (snds k e)

/-- **Environment-packing term.** For a map $\mathit{acc}$ from natural numbers to target terms
and a natural number $n$, the environment-packing term of $\mathit{acc}$ and $n$ is the target
term $(\mathit{acc}(0), (\mathit{acc}(1), \dots (\mathit{acc}(n - 1), \mathsf{unit})\dots))$
packing $\mathit{acc}(0), \dots, \mathit{acc}(n - 1)$ as nested pairs ending in $\mathsf{unit}$.
Recursively, it is $\mathsf{unit}$ for $n = 0$, and for $n + 1$ it is the pair of
$\mathit{acc}(0)$ and the environment-packing term of $i \mapsto \mathit{acc}(i + 1)$ and $n$. -/
def envOf (acc : Nat → Tm) : Nat → Tm
  | 0 => .unit
  | n + 1 => .pair (acc 0) (envOf (fun i => acc (i + 1)) n)

/-- **Accessors inside converted code.** Write $\#0$ for the target variable $0$ and
$\mathsf{snd}^i$ for $i$ applications of the second projection. The code accessor for index $0$
is $\mathsf{fst}\,\#0$, and the code accessor for index $i + 1$ is
$\mathsf{fst}\,(\mathsf{snd}^i\,(\mathsf{snd}\,\#0))$. When the code parameter $\#0$ is the pair
of the argument and an environment encoded as nested pairs, accessor $0$ fetches the argument and
accessor $i + 1$ fetches entry $i$ of the environment. -/
def codeAcc : Nat → Tm
  | 0 => .fst (.var 0)
  | i + 1 => .fst (snds i (.snd (.var 0)))

/-- **Closure conversion with accessors.** Let $\mathit{acc}$ be a family of target terms indexed
by the natural numbers (accessor $i$ fetches source variable $i$) and $n$ a natural number (the
number of source variables in scope). The conversion $\mathcal{C}(\mathit{acc}, n, t)$ of a
source term $t$ is defined by recursion on $t$. A variable $i$ converts to $\mathit{acc}(i)$. A
lambda with body $b$ (whatever its parameter type) converts to the pair of
$\mathsf{code}\,\mathcal{C}(c, n + 1, b)$, where $c$ is the family of code accessors, and the
target term packing $\mathit{acc}(0), \dots, \mathit{acc}(n - 1)$ as nested pairs ending in
$\mathsf{unit}$. An application $f\,a$ converts to
$\mathsf{let}\ \mathcal{C}(\mathit{acc}, n, f)\ \mathsf{in}\ (\mathsf{fst}\,\#0)\,
(\mathcal{C}(\mathit{acc}', n, a), \mathsf{snd}\,\#0)$, where $\#0$ is the target variable $0$
and $\mathit{acc}'(i)$ is the shift of $\mathit{acc}(i)$ for every $i$. -/
def convert : (Nat → Tm) → Nat → Stlc.RawTm Base → Tm
  | acc, _, .var i => acc i
  | acc, n, .lam _ body => .pair (.code (convert codeAcc (n + 1) body)) (envOf acc n)
  | acc, n, .app f a =>
      .letIn (convert acc n f)
        (.app (.fst (.var 0)) (.pair (convert (fun i => (acc i).shift) n a) (.snd (.var 0))))

/-- **Closure conversion of a program.** The closure conversion of a source term $t$ is the
conversion of $t$ in a scope of $0$ variables with the accessors that send each index $i$ to the
target variable $i$. It is intended for closed terms. -/
def closureConvert (t : Stlc.RawTm Base) : Tm :=
  convert .var 0 t

/-- **Encoding a list of target values.** The encoding of a list of target values as nested pairs
sends the empty list to the unit value and a list with head $w$ and tail $ws$ to the pair of $w$
and the encoding of $ws$. Thus $[w_0, \dots, w_{k-1}]$ is encoded as
$(w_0, (w_1, \dots (w_{k-1}, \mathsf{unit})))$. -/
def encodeEnv : List Value → Value
  | [] => .unit
  | w :: ws => .pair w (encodeEnv ws)

/-- **Value relation for closure conversion.** The relation between source values and target
values of closure conversion is the least relation such that, for every source lambda body $b$,
every list $\rho$ of source values and every list $ws$ of target values with $|\rho| = |ws|$
and $\rho_i$ related to $ws_i$ for every $i < |\rho|$, the source closure of $b$ over $\rho$ is
related to the target pair $(\mathsf{code}\,c, E)$. Here $c$ is the closure conversion of $b$ in
a scope of $|\rho| + 1$ variables with the code accessors, which read variable $0$ as
$\mathsf{fst}\,\#0$ and variable $i + 1$ as $\mathsf{fst}\,(\mathsf{snd}^i\,(\mathsf{snd}\,\#0))$,
where $\#0$ is the code parameter and $\mathsf{snd}^i$ applies the second projection $i$ times;
and $E$ is the encoding of $ws$ as nested pairs ending in the unit value. -/
inductive ValRel : Source.Value Base → Value → Prop
  | clo {body : Stlc.RawTm Base} {ρ : List (Source.Value Base)} {ws : List Value}
      (hlen : ρ.length = ws.length)
      (hrel : ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i]) :
      ValRel (.clo body ρ) (.pair (.code (convert codeAcc (ρ.length + 1) body)) (encodeEnv ws))

/-- **Accessors implementing a source environment.** Let $\rho$ be a list of source values,
$\rho_t$ a list of target values and $\mathit{acc}$ a family of target terms indexed by the
natural numbers. The accessors $\mathit{acc}$ implement $\rho$ in $\rho_t$ when, for every index
$i$ less than the length of $\rho$, there is a target value $w$ such that $\mathit{acc}(i)$
evaluates to $w$ in the environment $\rho_t$ and the entry of $\rho$ at index $i$ is related to
$w$ by the value relation of closure conversion. -/
def AccRel (ρ : List (Source.Value Base)) (ρt : List Value) (acc : Nat → Tm) : Prop :=
  ∀ i (h : i < ρ.length), ∃ w, Eval ρt (acc i) w ∧ ValRel ρ[i] w

theorem AccRel.shift {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    (h : AccRel ρ ρt acc) (x : Value) : AccRel ρ (x :: ρt) (fun i => (acc i).shift) := by
  intro i hi
  obtain ⟨w, hw, hrel⟩ := h i hi
  exact ⟨w, hw.shift x, hrel⟩

/-- **Packed accessors evaluate to an encoded related environment.** Let $\rho$ be a list of
source values, $\rho_t$ a list of target values and $\mathit{acc}$ a map from natural numbers
to target terms, and suppose the accessors $\mathit{acc}$ implement $\rho$ in $\rho_t$: for
every $i < |\rho|$, the term $\mathit{acc}(i)$ evaluates in $\rho_t$ to a target value related
to $\rho_i$ by the value relation. Then there is a list $ws$ of target values with
$|ws| = |\rho|$ and $\rho_i$ related to $ws_i$ for every $i < |\rho|$, such that the target
term packing $\mathit{acc}(0), \dots, \mathit{acc}(|\rho| - 1)$ as nested pairs ending in
$\mathsf{unit}$ evaluates in $\rho_t$ to the encoding of $ws$ as nested pairs ending in the
unit value. -/
theorem AccRel.envOf {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    (h : AccRel ρ ρt acc) :
    ∃ ws : List Value, Eval ρt (ClosureConversion.envOf acc ρ.length) (encodeEnv ws) ∧
      ρ.length = ws.length ∧
      ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i] := by
  induction ρ generalizing acc with
  | nil => exact ⟨[], .unit, rfl, fun i h₁ => absurd h₁ (Nat.not_lt_zero i)⟩
  | cons v ρ ih =>
      obtain ⟨w, hw, hvw⟩ := h 0 (Nat.zero_lt_succ _)
      have htail : AccRel ρ ρt (fun i => acc (i + 1)) := fun i hi =>
        h (i + 1) (Nat.succ_lt_succ hi)
      obtain ⟨ws, hws, hlen, hrel⟩ := ih htail
      refine ⟨w :: ws, .pair hw hws, by simp [hlen], ?_⟩
      intro i h₁ h₂
      cases i with
      | zero => exact hvw
      | succ i => exact hrel i (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- **Iterated second projections of an encoded environment.** Let $\rho$ be a list of target
values, $e$ a target term and $ws = [w_0, \dots, w_{m-1}]$ a list of target values, and suppose
$e$ evaluates in $\rho$ to the encoding of $ws$, the nested pairs
$(w_0, (w_1, \dots (w_{m-1}, \mathsf{unit})\dots))$. Then for every natural number $k \le m$, the
term obtained by applying the second projection $k$ times to $e$ evaluates in $\rho$ to the
encoding of $[w_k, \dots, w_{m-1}]$, the list $ws$ with its first $k$ entries dropped. -/
theorem eval_snds {ρt : List Value} {e : Tm} {ws : List Value}
    (he : Eval ρt e (encodeEnv ws)) {k : Nat} (hk : k ≤ ws.length) :
    Eval ρt (snds k e) (encodeEnv (ws.drop k)) := by
  induction k with
  | zero => simpa [snds] using he
  | succ k ih =>
      have hk' : k < ws.length := hk
      have h := ih (Nat.le_of_lt hk')
      rw [List.drop_eq_getElem_cons hk'] at h
      exact .snd h

theorem eval_fst_snds {ρt : List Value} {e : Tm} {ws : List Value}
    (he : Eval ρt e (encodeEnv ws)) {i : Nat} (hi : i < ws.length) :
    Eval ρt (.fst (snds i e)) ws[i] := by
  have h := eval_snds he (Nat.le_of_lt hi)
  rw [List.drop_eq_getElem_cons hi] at h
  exact .fst h

/-- **Code accessors implement the extended closure environment.** Let $v$ be a source value
related to a target value $w$ by the value relation of closure conversion, and let $\rho$ and $ws$
be lists of source and target values of the same length such that, for every index $i$ below that
length, the entry of $\rho$ at $i$ is related to the entry of $ws$ at $i$. Then the code accessors
implement the source environment $v :: \rho$ ($\rho$ with $v$ added at index $0$) in the
one-element target environment whose entry is the pair of $w$ and the encoding of $ws$ as nested
pairs ending in $\mathsf{unit}$. -/
theorem accRel_codeAcc {v : Source.Value Base} {ρ : List (Source.Value Base)} {w : Value}
    {ws : List Value} (hvw : ValRel v w) (hlen : ρ.length = ws.length)
    (hrel : ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i]) :
    AccRel (v :: ρ) [.pair w (encodeEnv ws)] codeAcc := by
  intro i hi
  cases i with
  | zero => exact ⟨w, .fst (.var rfl), hvw⟩
  | succ i =>
      have hiρ : i < ρ.length := Nat.lt_of_succ_lt_succ hi
      have hiws : i < ws.length := hlen ▸ hiρ
      exact ⟨ws[i], eval_fst_snds (.snd (.var rfl)) hiws, hrel i hiρ hiws⟩

/-- **Correctness of closure conversion.** Let $\rho$ be a list of source values, $\ell$ its
length, and $t$ a source term that evaluates to a source value $v$ in the environment $\rho$. Let
$\rho_t$ be a list of target values and $\mathit{acc}$ a family of target terms indexed by the
natural numbers that implement $\rho$ in $\rho_t$. Then there is a target value $w$ such that the
conversion of $t$ in a scope of $\ell$ variables with accessors $\mathit{acc}$ evaluates to $w$
in the environment $\rho_t$, and $v$ is related to $w$ by the value relation of closure
conversion. -/
theorem convert_correct {ρ : List (Source.Value Base)} {t : Stlc.RawTm Base}
    {v : Source.Value Base} (h : Source.Eval ρ t v) {ρt : List Value} {acc : Nat → Tm}
    (hacc : AccRel ρ ρt acc) :
    ∃ w, Eval ρt (convert acc ρ.length t) w ∧ ValRel v w := by
  induction h generalizing ρt acc with
  | @var ρ n v hn =>
      have hlt : n < ρ.length := (List.getElem?_eq_some_iff.mp hn).1
      obtain ⟨w, hw, hrel⟩ := hacc n hlt
      have hv : ρ[n] = v := (List.getElem?_eq_some_iff.mp hn).2
      exact ⟨w, hw, hv ▸ hrel⟩
  | @lam ρ A body =>
      obtain ⟨ws, hws, hlen, hrel⟩ := hacc.envOf
      exact ⟨_, .pair .code hws, .clo hlen hrel⟩
  | @app ρ ρ' f a body v w' _ _ _ ihf iha ihb =>
      obtain ⟨wf, hwf, hrelf⟩ := ihf hacc
      cases hrelf with
      | @clo _ _ ws hlen hrel =>
          obtain ⟨wa, hwa, hrela⟩ := iha (hacc.shift _)
          obtain ⟨wb, hwb, hrelb⟩ := ihb (accRel_codeAcc hrela hlen hrel)
          refine ⟨wb, .letIn hwf (.app (.fst (.var rfl)) (.pair hwa (.snd (.var rfl))) ?_), hrelb⟩
          simpa using hwb

/-- **Correctness of closure conversion in the empty environment.** If a source term $t$
evaluates to a source value $v$ in the empty environment, then there is a target value $w$ such
that the closure conversion of $t$ evaluates to $w$ in the empty environment and $v$ is related to
$w$ by the value relation of closure conversion. -/
theorem closureConvert_correct {t : Stlc.RawTm Base} {v : Source.Value Base}
    (h : Source.Eval [] t v) : ∃ w, Eval [] (closureConvert t) w ∧ ValRel v w :=
  convert_correct h (fun i hi => absurd hi (Nat.not_lt_zero i))

theorem scoped_snds {m k : Nat} {e : Tm} (h : Scoped m e) : Scoped m (snds k e) := by
  induction k with
  | zero => exact h
  | succ k ih => exact .snd ih

theorem scoped_envOf {m : Nat} {acc : Nat → Tm} :
    ∀ {n : Nat}, (∀ i, i < n → Scoped m (acc i)) → Scoped m (ClosureConversion.envOf acc n)
  | 0, _ => .unit
  | n + 1, h => .pair (h 0 (Nat.zero_lt_succ n))
      (scoped_envOf fun i hi => h (i + 1) (Nat.succ_lt_succ hi))

theorem scoped_codeAcc (i : Nat) : Scoped 1 (codeAcc i) := by
  cases i with
  | zero => exact .fst (.var Nat.zero_lt_one)
  | succ i => exact .fst (scoped_snds (.snd (.var Nat.zero_lt_one)))

/-- **Converted terms are well scoped.** Let $m$ and $n$ be natural numbers and $t$ a source term
whose list of free indices at binder depth $n$ is empty, that is, $t$ is scoped in $n$ variables.
If $\mathit{acc}$ is a family of target terms indexed by the natural numbers such that
$\mathit{acc}(i)$ is scoped in $m$ for every $i < n$, then the conversion of $t$ in a scope of
$n$ variables with accessors $\mathit{acc}$ is scoped in $m$; in particular, every code body it
contains is scoped in $1$. -/
theorem convert_scoped {m : Nat} (t : Stlc.RawTm Base) :
    ∀ {n : Nat}, Stlc.RawTm.freeIndices n t = [] →
      ∀ {acc : Nat → Tm}, (∀ i, i < n → Scoped m (acc i)) → Scoped m (convert acc n t) := by
  induction t generalizing m with
  | var i =>
      intro n ht acc hacc
      have hi : i < n := by
        by_contra hni
        simp [Stlc.RawTm.freeIndices, Nat.le_of_not_lt hni] at ht
      exact hacc i hi
  | app f a ihf iha =>
      intro n ht acc hacc
      rw [Stlc.RawTm.freeIndices_app, List.append_eq_nil_iff] at ht
      exact .letIn (ihf ht.1 hacc) (.app (.fst (.var (Nat.zero_lt_succ m)))
        (.pair (iha ht.2 fun i hi => (hacc i hi).shift) (.snd (.var (Nat.zero_lt_succ m)))))
  | lam A body ih =>
      intro n ht acc hacc
      rw [Stlc.RawTm.freeIndices_lam] at ht
      exact .pair (.code (ih ht fun i _ => scoped_codeAcc i)) (scoped_envOf hacc)

/-- **Closure conversion of a closed term is well scoped.** If a source term $t$ is closed (it
has no free variables), then its closure conversion is scoped in $0$: it has no free variables,
and every code body in it is scoped in $1$, so refers only to its parameter. -/
theorem closureConvert_scoped {t : Stlc.RawTm Base} (ht : t.Closed) :
    Scoped 0 (closureConvert t) :=
  convert_scoped t ht fun i hi => absurd hi (Nat.not_lt_zero i)

end Cslib.Languages.LambdaCalculus.ClosureConversion
