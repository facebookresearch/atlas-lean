/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics
import CSLibExt.Computability.Complexity.Host
import Mathlib.Data.Fintype.Sigma
import CSLibExt.Computability.Complexity.PolynomialEncoding.Frame
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
import CSLibExt.Computability.Complexity.Preimage
import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
import Mathlib.Data.List.GetD
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts

/-!
# MONOTONE 3-SAT is NP-complete

`monotoneThreeSat_npComplete` proves NP membership and hardness for the bitstring language
`monotoneThreeSatDec`. Membership uses a polynomial-time translation to SAT. It checks clause
length, uniform polarity and binary variable bounds while reading the input. This allows a large
declared variable count without requiring a certificate with one bit per declared variable.

For hardness, replace each literal by a positive variable representing its truth value. A negative
clause prevents the two representatives of a variable from both being true. Repeating literals
pads each nonempty clause to length three. The two translations below are compiled into finite
multistack machines with polynomial step bounds.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

/-- **Monotone 3-SAT instances.** A monotone 3-SAT instance is a pair $(n, \varphi)$ of a
natural number $n$, the number of variables, and a CNF formula $\varphi$. -/
abbrev MonotoneThreeSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF

/-- **Well-formed monotone 3-SAT instances.** A monotone 3-SAT instance $(n, \varphi)$ is well
formed when every clause of the CNF formula $\varphi$ is a list of exactly three literals
(repetitions allowed), each with a variable below $n$, and the literals of each clause are all
positive or all negative. -/
def WellFormed (i : MonotoneThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2, clause.length = 3 ∧ (∀ l ∈ clause, l.1 < i.1) ∧
    ((∀ l ∈ clause, l.2 = true) ∨ (∀ l ∈ clause, l.2 = false)))

/-- **Satisfiable monotone 3-SAT instances.** A monotone 3-SAT instance $(n, \varphi)$ is
feasible when there is a list of $n$ truth values $a_0, \dots, a_{n-1}$ such that the assignment
sending each variable $x < n$ to $a_x$ and every variable $x \ge n$ to false satisfies the CNF
formula $\varphi$. -/
def MonotoneThreeSatFeasible
    (i : MonotoneThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2

open Classical in
/-- **MONOTONE 3-SAT as a decision problem.** The decision problem MONOTONE 3-SAT accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a pair
$(n, \varphi)$ of a natural number $n$ and a CNF formula $\varphi$ such that every clause of
$\varphi$ is a list of exactly three literals (repetitions allowed), every literal of $\varphi$
has a variable below $n$, the literals of each clause are all positive or all negative, and
some assignment of truth values to the variables $0, \dots, n-1$, with every other variable
false, satisfies $\varphi$. Bitstrings that do not decode are rejected. -/
noncomputable def monotoneThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonotoneThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ MonotoneThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

end

/-! ### Finite control with a failure exit, sequential composition and bounded iteration. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

open Turing TM2Program Function

variable {K : Type} [DecidableEq K] {Γ : K → Type}

-- A finite multi-exit TM2 subprogram, parameterized by its host labels.
structure Code (Γ : K → Type) (α : Type) where
  Lab : Type
  [fin : Fintype Lab]
  start : Lab
  prog {L : Type} : (Lab → L) → (α → L) → Lab → TM2.Stmt Γ L Bool

attribute [instance] Code.fin

namespace Code

variable {α β : Type}

abbrev Stores (Γ : K → Type) := ∀ k, List (Γ k)

def Runs (p : Code Γ α) (B : Nat) (S : Stores Γ) (post : α → Stores Γ → Prop) : Prop :=
  ∀ (L : Type) (prog : L → TM2.Stmt Γ L Bool) (pc : p.Lab → L) (ret : α → L),
    (∀ l, prog (pc l) = p.prog pc ret l) → ∀ v : Bool,
    ∃ a T w, RunLe prog B ⟨some (pc p.start), v, S⟩ ⟨some (ret a), w, T⟩ ∧ post a T

theorem Runs.weaken {p : Code Γ α} {B B' : Nat} {S : Stores Γ} {P Q : α → Stores Γ → Prop}
    (h : p.Runs B S P) (hB : B ≤ B') (hPQ : ∀ a T, P a T → Q a T) :
    p.Runs B' S Q := by
  intro L m pc ret hm v
  obtain ⟨a, T, w, run, hp⟩ := h L m pc ret hm v
  exact ⟨a, T, w, run.mono hB, hPQ _ _ hp⟩

def atom (f : {L : Type} → (α → L) → TM2.Stmt Γ L Bool) : Code Γ α where
  Lab := Unit
  start := ()
  prog _ ret _ := f ret

def pure (a : α) : Code Γ α := atom fun ret => .goto fun _ => ret a

theorem pure_run {a : α} (S : Stores Γ) : (pure a).Runs 1 S (fun a' T => a' = a ∧ T = S) := by
  intro L m pc ret hm v
  exact ⟨a, S, v, (Run.single (by rw [hm]; rfl)).le le_rfl, rfl, rfl⟩

abbrev Partial (Γ : K → Type) (α : Type) := Code Γ (Option α)

namespace Partial

def Works (p : Partial Γ α) (B : Nat) (S : Stores Γ) (out : Option (α × Stores Γ)) :=
  p.Runs B S fun a T => (a.map (·, T)) = out

theorem Works.mono {p : Partial Γ α} {B C : Nat} {S : Stores Γ} {o}
    (h : Works p B S o) (hle : B ≤ C) : Works p C S o :=
  h.weaken hle (fun _ _ h => h)

def pure (a : α) : Partial Γ α := Code.pure (some a)

theorem pure_run (a : α) (S : Stores Γ) : Works (pure a) 1 S (some (a, S)) :=
  (Code.pure_run (a := some a) S).weaken le_rfl (fun _ _ h => by rw [h.1, h.2]; rfl)

def fail : Partial Γ α := Code.pure none

theorem fail_run (S : Stores Γ) : Works (fail (α := α)) 1 S none :=
  (Code.pure_run (a := (none : Option α)) S).weaken le_rfl (fun _ _ h => by rw [h.1]; rfl)

def bind [Fintype α] (p : Partial Γ α) (q : α → Partial Γ β) : Partial Γ β where
  Lab := p.Lab ⊕ Σ a, (q a).Lab
  start := .inl p.start
  prog pc ret
    | .inl l => p.prog (fun i => pc (.inl i))
        (fun o => o.elim (ret none) (fun a => pc (.inr ⟨a, (q a).start⟩))) l
    | .inr ⟨a, l⟩ => (q a).prog (fun i => pc (.inr ⟨a, i⟩)) ret l

theorem bind_some [Fintype α] {p : Partial Γ α} {q : α → Partial Γ β}
    {B C : Nat} {S T : Stores Γ} {a : α} {out}
    (h₁ : Works p B S (some (a, T))) (h₂ : Works (q a) C T out) :
    Works (bind p q) (B + C) S out := by
  intro L m pc ret hm v
  obtain ⟨_ | a', T', w, h, he⟩ := h₁ L m (fun i => pc (.inl i))
    (fun o => o.elim (ret none) (fun a => pc (.inr ⟨a, (q a).start⟩))) (fun l => hm (.inl l)) v
  · cases he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  obtain ⟨b, U, w', h', hout⟩ := h₂ L m (fun i => pc (.inr ⟨_, i⟩)) ret
    (fun l => hm (.inr ⟨_, l⟩)) w
  exact ⟨b, U, w', h.trans h', hout⟩

theorem bind_none [Fintype α] {p : Partial Γ α} {q : α → Partial Γ β}
    {B : Nat} {S : Stores Γ} (h₁ : Works p B S none) : Works (bind p q) B S none := by
  intro L m pc ret hm v
  obtain ⟨_ | a', T', w, h, he⟩ := h₁ L m (fun i => pc (.inl i))
    (fun o => o.elim (ret none) (fun a => pc (.inr ⟨a, (q a).start⟩))) (fun l => hm (.inl l)) v
  · exact ⟨none, T', w, h, rfl⟩
  cases he

-- Continue on true, exit normally on false, propagate failure.
def iterate (p : Partial Γ Bool) : Partial Γ Unit where
  Lab := p.Lab
  start := p.start
  prog pc ret := p.prog pc fun
    | none => ret none
    | some true => pc p.start
    | some false => ret (some ())

theorem repeat_more {p : Partial Γ Bool} {B C : Nat} {S T : Stores Γ} {out}
    (h₁ : Works p B S (some (true, T))) (h₂ : Works (iterate p) C T out) :
    Works (iterate p) (B + C) S out := by
  intro L m pc ret hm v
  let go : Option Bool → L
    | none => ret none
    | some true => pc p.start
    | some false => ret (some ())
  obtain ⟨_ | a, U, w, h, he⟩ := h₁ L m pc go hm v
  · cases he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  obtain ⟨b, T, w', h', ht⟩ := h₂ L m pc ret hm w
  exact ⟨b, T, w', h.trans h', ht⟩

theorem repeat_stop {p : Partial Γ Bool} {B : Nat} {S T : Stores Γ}
    (h₁ : Works p B S (some (false, T))) : Works (iterate p) B S (some ((), T)) := by
  intro L m pc ret hm v
  let go : Option Bool → L
    | none => ret none
    | some true => pc p.start
    | some false => ret (some ())
  obtain ⟨_ | a, U, w, h, he⟩ := h₁ L m pc go hm v
  · cases he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  exact ⟨some (), _, w, h, rfl⟩

theorem repeat_fail {p : Partial Γ Bool} {B : Nat} {S : Stores Γ}
    (h₁ : Works p B S none) : Works (iterate p) B S none := by
  intro L m pc ret hm v
  let go : Option Bool → L
    | none => ret none
    | some true => pc p.start
    | some false => ret (some ())
  obtain ⟨_ | a, U, w, h, he⟩ := h₁ L m pc go hm v
  · exact ⟨none, _, w, h, rfl⟩
  cases he

end Partial

end Code
end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Primitive operations on bit stacks, including framed reads and writes. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

open Turing TM2Program Function BitstringEncoding Code Code.Partial
open Cslib.Complexity Cslib.Complexity.PolynomialEncoding

variable {K : Type} [DecidableEq K]

abbrev Store (K : Type) := K → List Bool
abbrev P (K : Type) := Partial (fun _ : K => Bool)

def put2 (S : Store K) (a b : K) (xs ys : List Bool) := update (update S a xs) b ys

private theorem eq_put2 {S T : Store K} {a b : K} {xs ys : List Bool} (hab : a ≠ b)
    (ha : T a = xs) (hb : T b = ys) (h : ∀ k, k ≠ a → k ≠ b → T k = S k) :
    T = put2 S a b xs ys := by
  funext k
  by_cases ka : k = a
  · subst k; simpa [put2, hab] using ha
  by_cases kb : k = b
  · subst k; simpa [put2] using hb
  simp [put2, ka, kb, h k ka kb]

def push (a : K) (b : Bool) : P K Unit := atom fun ret =>
  .push a (fun _ => b) (.goto fun _ => ret (some ()))

theorem push_run (a : K) (b : Bool) (S : Store K) :
    Works (push a b) 1 S (some ((), update S a (b :: S a))) := by
  intro L m pc ret hm v
  exact ⟨_, _, v, (Run.single (by rw [hm]; rfl)).le le_rfl, rfl⟩

def empty (a : K) : P K Bool := atom fun ret =>
  .peek a (fun _ o => o.isNone) (.goto fun b => ret (some b))

theorem empty_run (a : K) (S : Store K) :
    Works (empty a) 1 S (some ((S a).isEmpty, S)) := by
  intro L m pc ret hm v
  refine ⟨some (S a).isEmpty, S, (S a).isEmpty, (Run.single ?_).le le_rfl, rfl⟩
  rw [hm]
  cases h : S a <;> simp [empty, atom, TM2.stepAux, h]

-- Require exactly one bit and return it, consuming the stack.
def singleton (a : K) : P K Bool := atom fun ret =>
  .peek a (fun _ o => o.isSome) <| .branch id
    (.pop a (fun _ o => o.getD false) <| .branch id
      (.peek a (fun _ o => o.isNone) <| .goto fun clean => ret (if clean then some true else none))
      (.peek a (fun _ o => o.isNone)
        <| .goto fun clean => ret (if clean then some false else none)))
    (.goto fun _ => ret none)

theorem singleton_run (a : K) (S : Store K) :
    Works (singleton a) 1 S
      ((BitstringEncoding.bitDecode (α := Bool) (S a)).map (·, update S a [])) := by
  intro L m pc ret hm v
  rcases h : S a with _ | ⟨b, _ | ⟨c, cs⟩⟩
  · refine ⟨none, S, false, (Run.single ?_).le le_rfl, rfl⟩
    rw [hm]
    simp [singleton, atom, TM2.stepAux, h]
  · refine ⟨some b, update S a [], true, (Run.single ?_).le le_rfl, rfl⟩
    rw [hm]
    cases b <;> simp [singleton, atom, TM2.stepAux, h]
  · refine ⟨none, update S a (c :: cs), false, (Run.single ?_).le le_rfl, rfl⟩
    rw [hm]
    cases b <;> simp [singleton, atom, TM2.stepAux, h]

def move (a b : K) : P K Unit where
  Lab := Unit
  start := ()
  prog pc ret _ := moveB a b some id (pc ()) (ret (some ()))

theorem move_run (a b : K) (hab : a ≠ b) (S : Store K) :
    Works (move a b) ((S a).length + 1) S (some ((), put2 S a b [] ((S a).reverse ++ S b))) := by
  intro L m pc ret hm v
  obtain ⟨w, T, h, ha, hb, hk⟩ := moveB_run (a := a) (b := b) (d := some) (g := id)
    (self := pc ()) (next := ret (some ())) (hm ()) hab (S a) (S a) [] v S
      (by simp) (by simp [IsBitBlock]) rfl
  exact ⟨_, _, w, h.le le_rfl, congrArg (fun U : Store K => some ((), U))
    (eq_put2 hab ha (by simpa using hb) hk)⟩

def frameOut (a b : K) : P K Unit where
  Lab := Unit
  start := ()
  prog pc ret _ := emitFrame a b some id (pc ()) (ret (some ()))

theorem frameOut_run (a b : K) (hab : a ≠ b) (S : Store K) :
    Works (frameOut a b) ((S a).length + 1) S
      (some ((), put2 S a b [] ((delimit (S a)).reverse ++ S b))) := by
  intro L m pc ret hm v
  obtain ⟨T, h, ha, hb, hk⟩ := emitFrame_run (a := a) (b := b) (d := some) (g := id)
    (self := pc ()) (next := ret (some ())) (hm ()) hab id (fun _ => rfl) (S a) [] v S rfl (by simp)
  exact ⟨_, _, _, h.le le_rfl, congrArg (fun U : Store K => some ((), U))
    (eq_put2 hab ha (by simpa using hb) hk)⟩

def split (a b t : K) : P K Unit where
  Lab := Bool
  start := false
  prog pc ret
    | false => FramedCNF.Block.read a t some id (pc false) (pc true) (ret none)
    | true => moveB t b some id (pc true) (ret (some ()))

theorem split_run (a b t : K) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (S : Store K)
    (ht : S t = []) :
    Works (split a b t) ((S a).length + 2) S
      ((undelimit (S a)).map (fun (p, r) => ((), put2 S a b r (p ++ S b)))) := by
  intro L m pc ret hm v
  cases hu : undelimit (S a) with
  | none =>
    obtain ⟨w, T, hr⟩ := FramedCNF.Block.run_none (a := a) (b := t) (d := some) (g := id)
      (self := pc false) (good := pc true) (bad := ret none) (hm false) hat id (fun _ => rfl)
      (S a) v S (by simp) hu
    exact ⟨none, T, w, hr.mono (by omega), rfl⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
    obtain ⟨T, hr, ha, ht', hk⟩ := FramedCNF.Block.run_delimit
      (a := a) (b := t) (d := some) (g := id) (self := pc false) (good := pc true)
      (bad := ret none) (hm false) hat id (fun _ => rfl) p r v S (by simpa using he)
    have hT : T t = p.reverse := by simpa [ht] using ht'
    obtain ⟨w, U, hr', htU, hbU, hkU⟩ := moveB_run
      (a := t) (b := b) (d := some) (g := id) (self := pc true) (next := ret (some ()))
      (hm true) hbt.symm p.reverse p.reverse [] false T
        (by simpa using hT) (by simp [IsBitBlock]) rfl
    refine ⟨some (), U, w, (hr.trans hr').le ?_, congrArg (fun U : Store K => some ((), U)) ?_⟩
    · rw [he]; simp [length_delimit]; omega
    · apply eq_put2 hab
      · rw [hkU _ hat hab, ha]
      · simpa [hk _ hab.symm hbt] using hbU
      · intro k hka hkb
        by_cases hkt : k = t
        · subst k; rwa [ht]
        · rw [hkU _ hkt hkb, hk _ hka hkt]

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Stack operations carry bounds on both running time and the lengths of their results. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

open Turing TM2Program Function BitstringEncoding Code Code.Partial

variable {K : Type} [DecidableEq K] {α β : Type}

def workspace (S : Store K) : Store (Option K)
  | none => []
  | some k => S k

def fit (S : Store K) (n : Nat) := ∀ k, (S k).length ≤ n

def pack (out : Option (α × Store K)) := out.map fun (a, T) => (a, workspace T)

@[simp] theorem workspace_update (S : Store K) (k : K) (v : List Bool) :
    update (workspace S) (some k) v = workspace (update S k v) := by
  funext j
  cases j with
  | none => simp [workspace]
  | some i => by_cases hi : i = k <;> simp_all [workspace]

structure Op (K : Type) [DecidableEq K] (α : Type) where
  code : P (Option K) α
  eval : Store K → Option (α × Store K)
  C : Nat
  run : ∀ S n, fit S n → Works code (C * (n + 1)) (workspace S) (pack (eval S))
  size : ∀ S n a T, fit S n → eval S = some (a, T) → fit T (C * (n + 1))

namespace Op

def pure (a : α) : Op K α where
  code := Partial.pure a
  eval S := some (a, S)
  C := 1
  run S n _ := (Partial.pure_run a _).mono (by simp)
  size S n _ _ h he := by cases he; intro k; specialize h k; simp; omega

def fail : Op K α where
  code := Partial.fail
  eval _ := none
  C := 1
  run S n _ := (Partial.fail_run _).mono (by simp)
  size _ _ _ _ _ h := by cases h

noncomputable def bind [Fintype α] (p : Op K α) (q : α → Op K β) : Op K β where
  code := Partial.bind p.code (fun a => (q a).code)
  eval S := (p.eval S).bind fun (a, T) => (q a).eval T
  C := p.C + ((Finset.univ.sup fun a => (q a).C) * (p.C + 1))
  run S n hs := by
    have h := p.run S n hs
    cases he : p.eval S with
    | none =>
      rw [he] at h
      exact (bind_none h).mono (by rw [Nat.add_mul]; omega)
    | some pair =>
      obtain ⟨a, T⟩ := pair
      rw [he] at h
      have hr := (q a).run T _ (p.size S n a T hs he)
      refine (bind_some h hr).mono ?_
      have hc : (q a).C ≤ Finset.univ.sup (fun i => (q i).C) :=
        Finset.le_sup (f := (fun i => (q i).C)) (Finset.mem_univ a)
      calc
        _ ≤ p.C * (n + 1) + (Finset.univ.sup fun i => (q i).C) * ((p.C + 1) * (n + 1)) := by
          gcongr
          rw [Nat.add_mul, Nat.one_mul]
          omega
        _ = _ := by ring
  size S n b U hs he := by
    obtain ⟨⟨a, T⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp he
    have hu := (q a).size T _ b U (p.size S n a T hs ha) hb
    intro k
    have hc : (q a).C ≤ Finset.univ.sup (fun i => (q i).C) :=
      Finset.le_sup (f := (fun i => (q i).C)) (Finset.mem_univ a)
    calc
      _ ≤ _ := hu k
      _ ≤ (Finset.univ.sup fun i => (q i).C) * ((p.C + 1) * (n + 1)) := by
        gcongr
        rw [Nat.add_mul, Nat.one_mul]
        omega
      _ ≤ _ := by rw [← Nat.mul_assoc]; gcongr; omega

theorem eval_bind [Fintype α] (p : Op K α) (q : α → Op K β) (S : Store K) :
    (bind p q).eval S = (p.eval S).bind (fun (a, T) => (q a).eval T) := rfl

def push (a : K) (b : Bool) : Op K Unit where
  code := Machine.push (some a) b
  eval S := some ((), update S a (b :: S a))
  C := 1
  run S n _ := by
    simpa only [workspace_update, workspace, pack, Option.map_some] using
      (push_run (some a) b (workspace S)).mono (show 1 ≤ 1 * (n + 1) by simp)
  size S n _ _ hs he := by
    cases he
    intro j
    by_cases h : j = a
    · subst j; simpa using hs a
    · simpa [h] using Nat.le_succ_of_le (hs j)

def empty (a : K) : Op K Bool where
  code := Machine.empty (some a)
  eval S := some ((S a).isEmpty, S)
  C := 1
  run S n _ := (empty_run (some a) (workspace S)).mono (by simp)
  size S n _ _ hs he := by cases he; intro k; specialize hs k; simp; omega

def singleton (a : K) : Op K Bool where
  code := Machine.singleton (some a)
  eval S := (bitDecode (α := Bool) (S a)).map (·, update S a [])
  C := 1
  run S n _ := by
    have h := (singleton_run (some a) (workspace S)).mono (show 1 ≤ 1 * (n + 1) by simp)
    simpa [pack, workspace_update, workspace, Option.map_map, Function.comp_def] using h
  size S n _ _ hs he := by
    obtain ⟨b, _, he'⟩ := Option.map_eq_some_iff.mp he
    cases he'
    intro j
    by_cases h : j = a
    · subst j; simp
    · simpa [h] using Nat.le_succ_of_le (hs j)

private theorem fit_put2 {a b : K} {p q : List Bool} {S : Store K} {n m : Nat}
    (hs : fit S n) (hn : n ≤ m) (hp : p.length ≤ m) (hq : q.length ≤ m) :
    fit (put2 S a b p q) m := by
  intro k
  have h := (hs k).trans hn
  by_cases hk : k = b <;> by_cases hj : k = a <;> simp_all [put2]

@[simp] private theorem workspace_put2 (S : Store K) (a b : K) (p q : List Bool) :
    put2 (workspace S) (some a) (some b) p q = workspace (put2 S a b p q) := by
  simp [put2]

def move (a b : K) (hab : a ≠ b := by decide) : Op K Unit where
  code := Machine.move (some a) (some b)
  eval S := some ((), put2 S a b [] ((S a).reverse ++ S b))
  C := 2
  run S n hs := by
    have h := move_run (some a) (some b) (by simpa using hab) (workspace S)
    simpa [pack, workspace] using h.mono (show _ ≤ 2 * (n + 1) by
      change (S a).length + 1 ≤ _; have := hs a; omega)
  size S n _ _ hs he := by
    cases he
    apply fit_put2 hs (by omega) (by simp)
    simp; have := hs a; have := hs b; omega

def frameOut (a b : K) (hab : a ≠ b := by decide) : Op K Unit where
  code := Machine.frameOut (some a) (some b)
  eval S := some ((), put2 S a b [] ((delimit (S a)).reverse ++ S b))
  C := 3
  run S n hs := by
    have h := frameOut_run (some a) (some b) (by simpa using hab) (workspace S)
    simpa [pack, workspace] using h.mono (show _ ≤ 3 * (n + 1) by
      change (S a).length + 1 ≤ _; have := hs a; omega)
  size S n _ _ hs he := by
    cases he
    apply fit_put2 hs (by omega) (by simp)
    simp; have := hs a; have := hs b; omega

def split (a b : K) (hab : a ≠ b := by decide) : Op K Unit where
  code := Machine.split (some a) (some b) none
  eval S := (undelimit (S a)).map fun (p, r) => ((), put2 S a b r (p ++ S b))
  C := 2
  run S n hs := by
    have h := split_run (some a) (some b) none (by simpa using hab) (by simp) (by simp)
      (workspace S) rfl
    have h' := h.mono (show _ ≤ 2 * (n + 1) by change (S a).length + 2 ≤ _; have := hs a; omega)
    cases he : undelimit (S a) with
    | none => simpa [workspace, pack, he] using h'
    | some v => obtain ⟨p, r⟩ := v; simpa [workspace, pack, he] using h'
  size S n _ _ hs he := by
    obtain ⟨⟨p, r⟩, hp, he'⟩ := Option.map_eq_some_iff.mp he
    cases he'
    have h := hs a
    rw [(Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hp] at h
    simp only [List.length_append, length_delimit] at h
    apply fit_put2 hs (by omega) (by omega)
    simp; have := hs b; omega

end Op
end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Comparison of low-bit-first binary numerals. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat
open Cslib.Logic.LegacyPL Cslib.CookLevin Cslib.Complexity.Karp
open MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory

namespace Compare

open Turing Function TM2Program TM2Recursive Cslib.Complexity.FramedCNF

-- After normalization, compare low bits first, remembering whether the
-- first input's low-order prefix is less than the second one's.
private def nextLess (lo x y : Bool) : Bool := if x == y then lo else y

def answer (lo : Bool) (u v : List Bool) : Bool :=
  decide (bitsVal u < bitsVal v ∨ bitsVal u = bitsVal v ∧ lo)

private theorem next_answer (lo x y : Bool) (u v : List Bool) :
    answer lo (x :: u) (y :: v) = answer (nextLess lo x y) u v := by
  have eqv (b : Bool) (t : List Bool) :
      bitsVal (b :: t) = 2 * bitsVal t + (if b then 1 else 0) := by
    cases b <;> rfl
  rw [Bool.eq_iff_iff]
  cases lo <;> cases x <;> cases y <;> simp [answer, eqv, nextLess] <;> omega

private def zeroHead (v : List Bool) : List Bool := false :: v

private theorem answer_zero_left (lo : Bool) (u v : List Bool) (h : bitsVal u = 0) :
    answer lo (zeroHead u) v = answer lo u v := by
  simp [answer, zeroHead, show bitsVal (false :: u) = 2 * bitsVal u from by
    simp [bitsVal], h]

private theorem answer_zero_right (lo : Bool) (u v : List Bool) (h : bitsVal v = 0) :
    answer lo u (zeroHead v) = answer lo u v := by
  simp [answer, zeroHead, show bitsVal (false :: v) = 2 * bitsVal v from by
    simp [bitsVal], h]

private def select {Λ : Type} (lo x : Bool) (again : Bool → Λ) :
    TM2.Stmt (fun _ : Bool => Bool) Λ Bool :=
  .goto fun y => again (nextLess lo x y)

def compareStep {Λ : Type} (again exit : Bool → Λ) (lo : Bool) :
    TM2.Stmt (fun _ : Bool => Bool) Λ Bool :=
  .peek false (fun _ b => b.isSome) <| .branch id
    (.pop false (fun _ b => b.getD false) <| .branch id
      (.pop true (fun _ b => b.getD false) (select lo true again))
      (.pop true (fun _ b => b.getD false) (select lo false again)))
    (.peek true (fun _ b => b.isSome) <| .branch id
      (.pop true (fun _ b => b.getD false) (select lo false again))
      (.goto fun _ => exit lo))

def st (u v : List Bool) : Bool → List Bool
  | false => u
  | true => v

private theorem updL (u v u' : List Bool) :
    update (st u v) false u' = st u' v := by funext k; cases k <;> rfl

private theorem updR (u v v' : List Bool) :
    update (st u v) true v' = st u v' := by funext k; cases k <;> rfl

theorem run {Λ : Type} {M : Λ → TM2.Stmt (fun _ : Bool => Bool) Λ Bool}
    {again exit : Bool → Λ} (hM : ∀ lo, M (again lo) = compareStep again exit lo)
    (u v : List Bool) (lo start : Bool) :
    ∃ b, Run M (max u.length v.length + 1) ⟨some (again lo), start, st u v⟩
      ⟨some (exit (answer lo u v)), b, st [] []⟩ := by
  have step {lo' : Bool} {u' v' : List Bool}
      (h : TM2.stepAux (compareStep again exit lo) start (st u v) =
        ⟨some (again lo'), v.head?.getD false, st u' v'⟩) :
      Run M 1 ⟨some (again lo), start, st u v⟩
        ⟨some (again lo'), v.head?.getD false, st u' v'⟩ :=
    Run.single (by rw [hM]; exact h)
  match u, v with
  | [], [] =>
    refine ⟨false, Run.single ?_⟩
    cases lo <;> simp [hM, compareStep, TM2.stepAux, st, answer, bitsVal]
  | [], y :: v =>
    have r := step (lo' := nextLess lo false y) (u' := []) (v' := v) (by
      simp [compareStep, TM2.stepAux, select, updR, st])
    obtain ⟨b, hr⟩ := run hM [] v (nextLess lo false y) y
    have he := (answer_zero_left lo [] (y :: v) rfl).symm.trans (next_answer lo false y [] v)
    rw [he]
    exact ⟨b, (r.trans hr).of_eq (by simp; omega)⟩
  | x :: u, [] =>
    have r := step (lo' := nextLess lo x false) (u' := u) (v' := []) (by
      cases x <;> simp [compareStep, TM2.stepAux, select, updL, updR, st])
    obtain ⟨b, hr⟩ := run hM u [] (nextLess lo x false) false
    have he := (answer_zero_right lo (x :: u) [] rfl).symm.trans (next_answer lo x false u [])
    rw [he]
    exact ⟨b, (r.trans hr).of_eq (by simp; omega)⟩
  | x :: u, y :: v =>
    have r := step (lo' := nextLess lo x y) (u' := u) (v' := v) (by
      cases x <;> simp [compareStep, TM2.stepAux, select, updL, updR, st])
    obtain ⟨b, hr⟩ := run hM u v (nextLess lo x y) y
    rw [next_answer]
    exact ⟨b, (r.trans hr).of_eq (by simp; omega)⟩
termination_by u.length + v.length

-- The decoder accepts every natural-number payload. Normalize it before comparing variable names.
end Compare

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

/-! ### Embedding numeric operations in the working stacks. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine
open Turing Function TM2Program TM2Embedding BitstringEncoding Code Code.Partial
open Cslib.Complexity FramedCNF PolynomialEncoding

variable {K : Type} [DecidableEq K] {α : Type}

namespace Nested
variable {J Λ : Type} [DecidableEq J] [Fintype Λ]
variable (E : SEmb (fun _ : J => Bool) (fun _ : K => Bool))
variable (src : Λ → TM2.Stmt (fun _ : J => Bool) Λ Bool) (start : Λ)
    (exit : Λ → Option α)

def tgt {L : Type} (pc : Λ → L) (ret : α → L) (l : Λ) :=
  (exit l).elim (pc l) ret

def code : Code (fun _ : K => Bool) α where
  Lab := Λ
  start := start
  prog pc ret l := mapS E (tgt exit pc ret) (src l)

theorem run (hs : exit start = none) (hh : ∀ l, (exit l).isSome → src l = .halt)
    {B : Nat} {S T : Store K} {a : α} {s t : Store J} {l : Λ}
    (he : exit l = some a) (ha : Agree E s S) (hT : Agree E t T)
    (hf : Frame E S T)
    (hr : ∀ v, ∃ w, RunLe src B ⟨some start, v, s⟩ ⟨some l, w, t⟩) :
    (code E src start exit).Runs B S (fun b U => b = a ∧ U = T) := by
  intro L m pc ret hm v
  have emb : Embeds E (tgt exit pc ret) src m := by
    intro i
    cases hi : exit i with
    | none =>
      left
      rw [show tgt exit pc ret i = pc i by simp [tgt, hi]]
      exact hm i
    | some b => exact Or.inr (hh _ (by simp [hi]))
  obtain ⟨w, r⟩ := hr v
  obtain ⟨U, r', hU, hF⟩ := runLe_embed _ emb r ha
  refine ⟨a, U, w, by simpa [tgt, hs, he, code] using r', rfl, ?_⟩
  funext k
  by_cases h : ∃ j, E.e j = k
  · obtain ⟨j, rfl⟩ := h; exact (hU j).trans (hT j).symm
  · exact (hF k (by simpa using h)).trans (hf k (by simpa using h)).symm

end Nested

namespace Op

private def normEmb (a b : K) (hab : a ≠ b) :
    SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : Option K => Bool) where
  e
    | .input => some a
    | .buffer => none
    | .output => some b
  inj i j h := by cases i <;> cases j <;> simp_all
  ι _ := Equiv.refl Bool

private def normExit : NormalizeMachine.Lab → Option (Option Unit)
  | .done => some (some ())
  | _ => none

def norm (a b : K) (hab : a ≠ b := by decide) : Op K Unit where
  code := Nested.code (normEmb a b hab) NormalizeMachine.prog (.read none) normExit
  eval S := some ((), put2 S a b [] (normalizeNat (S a) ++ S b))
  C := 3
  run S n hs := by
    let T := put2 S a b [] (normalizeNat (S a) ++ S b)
    have h := Nested.run (normEmb a b hab) NormalizeMachine.prog (.read none) normExit
      rfl (fun l hl => by cases l <;> trivial)
      (S := workspace S) (T := workspace T)
      (s := NormalizeMachine.st (S a) [] (S b))
      (t := NormalizeMachine.st [] [] (normalizeNat (S a) ++ S b))
      (l := .done) rfl
      (fun j => by cases j <;> simp [normEmb, workspace, NormalizeMachine.st])
      (fun j => by cases j <;> simp [normEmb, workspace, NormalizeMachine.st, T, put2, hab])
      (fun k hk => by
        cases k with
        | none => rfl
        | some i =>
          have ha : i ≠ a := fun hi => hk .input (by simp [normEmb, hi])
          have hb : i ≠ b := fun hi => hk .output (by simp [normEmb, hi])
          simp [workspace, T, put2, ha, hb])
      (normalizeNat_run_frame (S a) (S b))
    exact h.weaken (by have := hs a; omega) (fun _ _ ⟨he, ht⟩ => by rw [he, ht]; rfl)
  size S n _ _ hs he := by
    cases he
    intro j
    have ha := length_normalizeNat_le (S a)
    have := hs a; have := hs b; have := hs j
    by_cases hj : j = b <;> by_cases hk : j = a <;> simp_all [put2] <;> omega

private def cmpEmb (a b : K) (hab : a ≠ b) :
    SEmb (fun _ : Bool => Bool) (fun _ : Option K => Bool) where
  e i := some (if i then b else a)
  inj i j h := by cases i <;> cases j <;> simp_all
  ι _ := Equiv.refl Bool

private def cmpProg : Bool ⊕ Bool → TM2.Stmt (fun _ : Bool => Bool) (Bool ⊕ Bool) Bool
  | .inl lo => Compare.compareStep Sum.inl Sum.inr lo
  | .inr _ => .halt

private def cmpExit : Bool ⊕ Bool → Option (Option Bool)
  | .inl _ => none
  | .inr b => some (some b)

def lt (a b : K) (hab : a ≠ b := by decide) : Op K Bool where
  code := Nested.code (cmpEmb a b hab) cmpProg (.inl false) cmpExit
  eval S := some (decide (TM2Recursive.bitsVal (S a) < TM2Recursive.bitsVal (S b)),
    put2 S a b [] [])
  C := 1
  run S n hs := by
    let T := put2 S a b [] []
    have h := Nested.run (cmpEmb a b hab) cmpProg (.inl false) cmpExit
      rfl (fun l hl => by cases l <;> trivial)
      (S := workspace S) (T := workspace T) (s := Compare.st (S a) (S b)) (t := Compare.st [] [])
      (l := .inr (Compare.answer false (S a) (S b))) rfl
      (fun j => by cases j <;> simp [cmpEmb, workspace, Compare.st])
      (fun j => by cases j <;> simp [cmpEmb, workspace, Compare.st, T, put2, hab])
      (fun k hk => by
        cases k with
        | none => rfl
        | some i =>
          have ha : i ≠ a := fun hi => hk false (by simp [cmpEmb, hi])
          have hb : i ≠ b := fun hi => hk true (by simp [cmpEmb, hi])
          simp [workspace, T, put2, ha, hb])
      (fun v => by
        obtain ⟨w, h⟩ := Compare.run (M := cmpProg) (again := Sum.inl) (exit := Sum.inr)
          (fun _ => rfl) (S a) (S b) false v
        exact ⟨w, h.le le_rfl⟩)
    apply h.weaken (by have := hs a; have := hs b; omega)
    rintro _ _ ⟨rfl, rfl⟩; simp [Compare.answer, pack, T]
  size S n _ _ hs he := by
    cases he
    intro j
    have := hs j
    by_cases hj : j = b <;> by_cases hk : j = a <;> simp_all [put2]
    omega

private def copyCode (a b : K) : P (Option K) Unit where
  Lab := Bool
  start := false
  prog pc ret
    | false => moveB (some a) none some id (pc false) (pc true)
    | true => splitB none (some a) (some b) some id id (pc true) (ret (some ()))

def copy (a b : K) (hab : a ≠ b := by decide) : Op K Unit where
  code := copyCode a b
  eval S := some ((), update S b (S a ++ S b))
  C := 2
  run S n hs := by
    intro L m pc ret hm v
    obtain ⟨T, r, ha, ht, hb, hk⟩ := copyB_run
      (a := some a) (b := some b) (t := none) (da := some) (dt := some) (ga := id) (gb := id)
      (gt := id) (first := pc false) (second := pc true) (next := ret (some ()))
      (hm false) (hm true) (by simpa using hab) (by simp) (by simp) (fun _ => rfl) (fun _ => rfl)
      (S a) [] v (workspace S) (by simp [workspace]) rfl rfl
    have he : T = workspace (update S b (S a ++ S b)) := by
      funext k
      cases k with
      | none => exact ht
      | some k =>
        by_cases hka : k = a
        · subst k; simpa [workspace, hab] using ha
        by_cases hkb : k = b
        · subst k; simpa [workspace] using hb
        simpa [workspace, hkb] using hk (some k) (by simpa using hka) (by simpa using hkb) (by simp)
    exact ⟨some (), T, false, r.le (by have := hs a; omega), by rw [he]; rfl⟩
  size S n _ _ hs he := by
    cases he
    intro j
    have := hs a; have := hs b; have := hs j
    by_cases hj : j = b <;> simp_all <;> omega

end Op
end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Check a clause and emit its SAT encoding, normalizing every decoded variable name. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input
open Cslib.CookLevin Cslib.Logic.LegacyPL
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.FramedCNF
open Cslib.Complexity.PolynomialEncoding
open Machine

inductive K | input | bound | raw | clause | lit | name | testName | testBound | body | count | out
  deriving DecidableEq

instance instFintypeK : Fintype K := Fintype.ofList
  [.input, .bound, .raw, .clause, .lit, .name, .testName, .testBound, .body, .count, .out]
  (fun k => by cases k <;> decide)

local infixr:55 " ⇢ " => Op.bind
noncomputable def seq {K : Type} [DecidableEq K] {A : Type} (p : Op K Unit) (q : Op K A) :=
  Op.bind p (fun _ => q)
local infixr:55 " ▷▷ " => seq

private def require {K : Type} [DecidableEq K] (b : Bool) : Op K Unit :=
  if b then Op.pure () else Op.fail

noncomputable def init : Op K Unit :=
  Op.split .input .raw ▷▷ Op.norm .raw .bound

noncomputable def literal : Op K Bool :=
  Op.split .clause .lit ▷▷ Op.split .lit .raw ▷▷ Op.singleton .lit ⇢ fun b =>
  Op.norm .raw .name ▷▷ Op.copy .bound .testBound ▷▷ Op.copy .name .testName ▷▷
  Op.lt .testName .testBound ⇢ fun below =>
  require below ▷▷ Op.frameOut .name .body ▷▷ Op.push .body b ▷▷ Op.pure b

noncomputable def three : Op K Bool :=
  literal ⇢ fun b => literal ⇢ fun c =>
  require (b == c) ▷▷ literal ⇢ fun d =>
  require (b == d) ▷▷ Op.empty .clause ⇢ fun empty =>
  require empty ▷▷ Op.push .count true ▷▷ Op.pure true

noncomputable def one : Op K Bool :=
  Op.empty .input ⇢ fun empty =>
  if empty then Op.pure false else
  Op.split .input .clause ▷▷ Op.push .body true ▷▷ Op.push .body true ▷▷
  Op.push .body true ▷▷ Op.push .body false ▷▷ three

noncomputable def finish : Op K Unit :=
  Op.move .body .out ▷▷ Op.push .out false ▷▷ Op.move .count .out

def st (x n c body count : List Bool) : Store K
  | .input => x
  | .bound => n
  | .clause => c
  | .body => body
  | .count => count
  | _ => []

def pred (n : Nat) (c : CNFClause) :=
  c.length = 3 ∧ (∀ l ∈ c, l.1 < n) ∧
    ((∀ l ∈ c, l.2 = true) ∨ (∀ l ∈ c, l.2 = false))

def ok (n : Nat) (c : CNFClause) : Bool :=
  c.length == 3 && c.all (fun l => decide (l.1 < n)) &&
    (c.all Prod.snd || c.all fun l => !l.2)

theorem ok_iff {n c} : ok n c ↔ pred n c := by simp [ok, pred, and_assoc]

private theorem decodeNatRaw (x : List Bool) : bitDecode x = some (Computability.decodeNat x) := rfl

private theorem pairParts {x : List Bool} {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    bitDecode (α := α × β) x = (undelimit x).bind (fun (p, r) =>
      (bitDecode (α := α) p).bind (fun a => (bitDecode (α := β) r).map (a, ·))) := by
  change (match undelimit x with
    | none => none
    | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
      | some a, some b => some (a, b)
      | _, _ => none) = _
  cases h : undelimit x with
  | none => rfl
  | some v =>
    obtain ⟨p, r⟩ := v
    cases hp : bitDecode (α := α) p <;> cases hr : bitDecode (α := β) r <;> simp [hp, hr]

theorem pairNat {x : List Bool} {α : Type} [BitstringEncoding α] :
    bitDecode (α := Nat × α) x = (undelimit x).bind (fun (p, r) =>
      (bitDecode (α := α) r).map (Computability.decodeNat p, ·)) := by
  simp only [pairParts, decodeNatRaw, Option.bind_some]

theorem decoded_cons (x : List Bool) (α : Type) [BitstringEncoding α] (hx : x ≠ []) :
    bitDecode (α := List α) x = (undelimit x).bind fun (p, r) =>
      (bitDecode (α := α) p).bind fun a => (bitDecode (α := List α) r).map (a :: ·) := by
  cases h : undelimit x with
  | none => exact decode_list_none_of_undelimit_none hx h
  | some v =>
    obtain ⟨p, r⟩ := v
    rw [(undelimit_eq_some_iff _ _ _).mp h, decode_list_delimit]
    rfl

theorem init_eval (x : List Bool) :
    init.eval (st x [] [] [] []) =
      (undelimit x).map (fun (p, r) => ((), st r (normalizeNat p) [] [] [])) := by
  cases h : undelimit x with
  | none => simp [init, seq, Op.eval_bind, Op.split, st, h]
  | some v =>
    obtain ⟨p, r⟩ := v
    simp only [init, seq, Op.split, put2, Op.norm, Op.eval_bind, st, List.append_nil, h,
      Option.map_some, Option.bind_some, Function.update_idem, Function.update_self, ne_eq,
      reduceCtorEq, not_false_eq_true, Function.update_of_ne, Option.some.injEq, Prod.mk.injEq,
      true_and]
    funext k; cases k <;> rfl

-- Read one framed literal from a clause, retaining its raw suffix.
private def getLit (c : List Bool) : Option ((Nat × Bool) × List Bool) := do
  let (p, r) ← undelimit c
  let l ← bitDecode (α := Nat × Bool) p
  return (l, r)

private theorem literal_eval (x n c body count : List Bool) :
    literal.eval (st x n c body count) =
      (getLit c).bind (fun (l, r) =>
        if l.1 < TM2Recursive.bitsVal n then
          some (l.2, st x n r ((encodeLit l).reverse ++ body) count)
        else none) := by
  cases h : undelimit c with
  | none => simp [literal, seq, Op.eval_bind, Op.split, getLit, st, h]
  | some v =>
    obtain ⟨p, r⟩ := v
    cases h' : undelimit p with
    | none =>
      simp [literal, seq, Op.eval_bind, Op.split, getLit, pairNat, h, h', st, Machine.put2]
    | some v =>
      obtain ⟨q, s⟩ := v
      cases h'' : bitDecode (α := Bool) s with
      | none =>
        simp [literal, seq, Op.eval_bind, Op.split, Op.singleton, getLit, pairNat,
          h, h', h'', st, Machine.put2]
      | some b =>
        by_cases hb : Computability.decodeNat q < TM2Recursive.bitsVal n
        all_goals simp only [literal, seq, Op.split, put2, Op.singleton, Op.norm,
          normalizeNat_eq_encode_decode, Op.copy, Op.lt, require, Op.pure, Op.fail, Op.frameOut,
          Op.push, Op.eval_bind, st, List.append_nil, h, Option.map_some, Option.bind_some,
          Function.update_self, Function.update_idem, decide_eq_true_eq, ne_eq, reduceCtorEq,
          not_false_eq_true, Function.update_of_ne, List.append_assoc, h', h'',
          TM2Recursive.bitsVal_encodeNat, hb, ↓reduceIte, getLit, pairNat, Option.pure_def,
          Option.bind_eq_bind, encodeLit, encodeNatPrefix, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append, Option.some.injEq, Prod.mk.injEq,
          true_and, Option.bind_none]
        funext k
        cases k <;> simp [st]

private def takeLits : Nat → List Bool → Option CNFClause
  | 0, x => if x.isEmpty then some [] else none
  | k + 1, x => (getLit x).bind fun (l, r) => (takeLits k r).map (l :: ·)

private theorem decode_nil_iff (x : List Bool) :
    bitDecode (α := CNFClause) x = some [] ↔ x = [] := by
  cases x with
  | nil => simp; rfl
  | cons b x =>
    rw [decoded_cons _ _ (by simp)]
    simp [Option.bind_eq_some_iff, Option.map_eq_some_iff]

private theorem decode_getLit {x : List Bool} (hx : x ≠ []) :
    bitDecode (α := CNFClause) x =
      (getLit x).bind fun (l, r) => (bitDecode r).map (l :: ·) := by
  rw [decoded_cons x _ hx]
  cases h : undelimit x with
  | none => simp [getLit, h]
  | some v =>
    obtain ⟨p, r⟩ := v
    cases hd : bitDecode (α := Nat × Bool) p <;> simp [getLit, h, hd]

private theorem take_iff (k : Nat) (x : List Bool) (c : CNFClause) :
    takeLits k x = some c ↔ bitDecode x = some c ∧ c.length = k := by
  induction k generalizing x c with
  | zero =>
    cases c with
    | nil => simp [takeLits, decode_nil_iff]
    | cons a c => by_cases hx : x = [] <;> simp [takeLits, hx]
  | succ k ih =>
    rcases eq_or_ne x [] with rfl | hx
    · cases c <;> simp [takeLits, getLit, undelimit,
      show bitDecode (α := CNFClause) [] = some [] from rfl]
    rw [decode_getLit hx]
    cases h : getLit x with
    | none => simp [takeLits, h]
    | some v =>
      obtain ⟨l, r⟩ := v
      cases c with
      | nil => simp [takeLits, h, Option.map_eq_some_iff]
      | cons a c => simp [takeLits, h, ih, and_assoc, and_comm, and_left_comm]

private theorem checked_take (n : Nat) (p : List Bool) :
    (takeLits 3 p).filter (ok n) = (bitDecode (α := CNFClause) p).filter (ok n) := by
  suffices h : ∀ c, ((takeLits 3 p).filter (ok n) = some c) ↔
      ((bitDecode (α := CNFClause) p).filter (ok n) = some c) by
    cases he : (takeLits 3 p).filter (ok n) with
    | some c => exact ((h c).mp he).symm
    | none => cases hr : (bitDecode (α := CNFClause) p).filter (ok n) with
              | none => rfl
              | some c => have := (h c).mpr hr; simp [he] at this
  intro c
  simp only [Option.filter_eq_some_iff, take_iff]
  exact ⟨fun ⟨⟨h, _⟩, ho⟩ => ⟨h, ho⟩, fun ⟨h, ho⟩ => ⟨⟨h, (ok_iff.mp ho).1⟩, ho⟩⟩

private theorem one_goodPrefix (x n p r body count : List Bool)
    (hx : x.isEmpty = false) (hframe : undelimit x = some (p, r)) :
    one.eval (st x n [] body count) =
      three.eval (st r n p (false :: true :: true :: true :: body) count) := by
  have h0 : x ≠ [] := List.isEmpty_eq_false_iff.mp hx
  simp only [one, Op.empty, seq, Op.split, put2, Op.push, Op.eval_bind, st, Option.bind_some,
    List.isEmpty_iff, h0, ↓reduceIte, List.append_nil, hframe, Option.map_some,
    Function.update_self, Function.update_idem, ne_eq, reduceCtorEq, not_false_eq_true,
    Function.update_of_ne]
  congr 1
  funext j; cases j <;> rfl

private theorem filter3 (n : Nat) (a b d : Nat × Bool) :
    (some [a, b, d]).filter (ok n) =
      if a.1 < n ∧ b.1 < n ∧ d.1 < n ∧ a.2 = b.2 ∧ a.2 = d.2
      then some [a, b, d] else none := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  obtain ⟨k, u⟩ := d
  cases s <;> cases t <;> cases u <;> simp [ok, Option.filter]

private theorem pushCount (r n body count) :
    Function.update (st r n [] body count) K.count (true :: count)
      = st r n [] body (true :: count) := by
  funext j; cases j <;> rfl

theorem one_eval (x n body count : List Bool) :
    one.eval (st x n [] body count) =
      (if x.isEmpty then some (false, st x n [] body count) else
        (undelimit x).bind fun (p, r) =>
          ((bitDecode (α := CNFClause) p).filter (ok (TM2Recursive.bitsVal n))).map
            (fun c => (true, st r n [] ((encodeClause c).reverse ++ body) (true :: count)))) := by
  by_cases hx : x = []
  · subst x; simp [one, Op.eval_bind, Op.empty, Op.pure, st]
  have hx' : x.isEmpty = false := List.isEmpty_eq_false_iff.mpr hx
  simp only [hx', Bool.false_eq_true, ↓reduceIte]
  cases h : undelimit x with
  | none =>
    simp [one, seq, Op.eval_bind, Op.empty, Op.split, st, hx, h]
  | some v =>
    obtain ⟨p, r⟩ := v
    rw [one_goodPrefix _ _ _ _ _ _ hx' h]
    simp only [Option.bind_some]
    rw [← checked_take]
    simp only [three, Op.eval_bind, seq, literal_eval, takeLits, Option.bind_assoc]
    cases ha : getLit p with
    | none => simp
    | some v =>
      obtain ⟨a, ra⟩ := v
      cases hb : getLit ra with
      | none =>
        by_cases hl : a.1 < TM2Recursive.bitsVal n <;> simp [hl, literal_eval, hb]
      | some v =>
        obtain ⟨b, rb⟩ := v
        cases hc : getLit rb with
        | none =>
          by_cases hl : a.1 < TM2Recursive.bitsVal n <;>
            by_cases hl' : b.1 < TM2Recursive.bitsVal n <;>
            by_cases he : a.2 = b.2 <;>
            simp [hl, hl', he, literal_eval, hb, require, Op.pure, Op.fail, hc]
        | some v =>
          obtain ⟨d, rd⟩ := v
          have key (p q : Bool) : (p == q) = decide (p = q) := by cases p <;> cases q <;> rfl
          by_cases ha' : a.1 < TM2Recursive.bitsVal n <;>
            by_cases hb' : b.1 < TM2Recursive.bitsVal n <;>
            by_cases hc' : d.1 < TM2Recursive.bitsVal n <;>
            by_cases hs : a.2 = b.2 <;> by_cases ht : a.2 = d.2 <;> by_cases hr : rd = [] <;>
            simp [ha', hb', hc', key, hs, ht, hr, literal_eval, hb, hc, require, Op.pure, Op.fail,
              Op.empty, Op.push, filter3, encodeClause, List.append_assoc, List.replicate_succ,
              Option.filter_none]
          all_goals by_cases hlast : b.2 = d.2 <;> simp_all [st, pushCount]

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input

/-! ### Iterate the clause checker, bounding the growth of the reversed SAT output. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input
open Cslib.CookLevin Cslib.Logic.LegacyPL
open Machine Machine.Code Machine.Code.Partial BitstringEncoding
open Cslib.Complexity.FramedCNF Cslib.Complexity.PolynomialEncoding

def parse (x n body count : List Bool) : Option (Unit × Store K) :=
  ((bitDecode (α := CNF) x).filter (List.all · (ok (TM2Recursive.bitsVal n)))).map fun φ =>
    ((), st [] n [] ((φ.flatMap encodeClause).reverse ++ body)
      (List.replicate φ.length true ++ count))

private theorem parse_end (n body count : List Bool)
    : parse [] n body count = some ((), st [] n [] body count) := by
  simp [parse, show bitDecode (α := CNF) [] = some [] from rfl]

private theorem parse_badFrame {x : List Bool} (hx : x ≠ []) (h : undelimit x = none)
    (n body count) :
    parse x n body count = none := by simp [parse, decode_list_none_of_undelimit_none hx h]

private theorem parse_step (p r n body count : List Bool) :
    parse (delimit p ++ r) n body count =
      ((bitDecode (α := CNFClause) p).filter (ok (TM2Recursive.bitsVal n))).bind
        (fun c => parse r n ((encodeClause c).reverse ++ body) (true :: count)) := by
  unfold parse
  rw [decode_list_delimit]
  cases h : bitDecode (α := CNFClause) p with
  | none => simp
  | some c =>
    cases hr : bitDecode (α := CNF) r with
    | none => cases ok (TM2Recursive.bitsVal n) c <;> simp_all [Option.filter]
    | some cs =>
      have hrp : List.replicate (cs.length + 1) true = List.replicate cs.length true ++ [true]
        := List.replicate_succ'
      have hrp' : List.replicate cs.length true ++ true :: count =
          List.replicate (cs.length + 1) true ++ count := by rw [hrp, List.append_assoc]; rfl
      cases h₁ : ok (TM2Recursive.bitsVal n) c <;>
        cases h₂ : cs.all (ok (TM2Recursive.bitsVal n)) <;>
        simp [h₁, h₂, Option.filter, List.append_assoc, hrp']

private theorem fits {x n body count : List Bool} {B : Nat}
    (hx : x.length ≤ B) (hn : n.length ≤ B) (hb : body.length ≤ B) (hc : count.length ≤ B) :
    fit (st x n [] body count) B := by intro k; cases k <;> simp_all [st]

theorem loop_run (x n body count : List Bool) (N B : Nat)
    (hx : x.length ≤ N) (hn : n.length ≤ N) (hN : N ≤ B)
    (hb : body.length + x.length * (one.C * (N + 1) + 1) ≤ B)
    (hc : count.length + x.length ≤ B) :
    Works (iterate one.code) ((x.length + 1) * (one.C * (B + 1))) (workspace (st x n [] body count))
      (pack (parse x n body count)) := by
  have h := one.run (st x n [] body count) B
    (fits (hx.trans hN) (hn.trans hN) (by omega) (by omega))
  rw [one_eval] at h
  cases x with
  | nil =>
    rw [parse_end]
    simpa [pack] using repeat_stop (by simpa [pack] using h)
  | cons z xs =>
    let x := z :: xs
    change body.length + x.length * _ ≤ B at hb
    change count.length + x.length ≤ B at hc
    have hx' : x.isEmpty = false := rfl
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
    change Works _ _ _ (pack ((undelimit x).bind fun (p, r) =>
      ((bitDecode (α := CNFClause) p).filter (ok (TM2Recursive.bitsVal n))).map
        (fun c => (true, st r n [] ((encodeClause c).reverse ++ body) (true :: count))))) at h
    have hpos : 1 ≤ x.length + 1 := by omega
    have hB := Nat.mul_le_mul_right (one.C * (B + 1)) hpos
    rw [Nat.one_mul] at hB
    cases hu : undelimit x with
    | none =>
      simp only [hu, Option.bind_none, pack, Option.map_none] at h
      rw [parse_badFrame (by simp) hu]
      exact (repeat_fail h).mono hB
    | some v =>
      obtain ⟨p, r⟩ := v
      have he := (undelimit_eq_some_iff _ _ _).mp hu
      have hl := congrArg List.length he
      simp only [List.length_append, length_delimit] at hl
      have hr : r.length < x.length := by omega
      change Works _ _ _ (pack (parse x n body count))
      rw [he, parse_step]
      simp only [hu, Option.bind_some] at h
      cases hp : (bitDecode (α := CNFClause) p).filter (ok (TM2Recursive.bitsVal n)) with
      | none =>
        simp only [hp, Option.map_none, pack] at h
        exact (repeat_fail h).mono hB
      | some c =>
        have he' := one_eval x n [] []
        simp only [hx', Bool.false_eq_true, ↓reduceIte, hu, hp, Option.bind_some, Option.map_some,
          List.append_nil] at he'
        have hsize := one.size _ N _ _ (fits hx hn (by simp) (by simp)) he' K.body
        change (encodeClause c).reverse.length ≤ _ at hsize
        rw [List.length_reverse] at hsize
        have hp' := Nat.mul_le_mul_right (one.C * (N + 1) + 1)
          (show r.length + 1 ≤ x.length from hr)
        rw [Nat.add_mul, Nat.one_mul] at hp'
        have hrec := loop_run r n ((encodeClause c).reverse ++ body) (true :: count) N B
          (hr.le.trans hx) hn hN (by simp only [List.length_append, List.length_reverse]; omega)
          (by simp only [List.length_cons]; omega)
        simp only [hp, Option.map_some, pack] at h
        apply (repeat_more h hrec).mono
        have hcst := Nat.mul_le_mul_right (one.C * (B + 1))
          (show r.length + 1 ≤ x.length from hr)
        rw [Nat.add_mul, Nat.one_mul] at hcst
        change _ ≤ (x.length + 1) * (one.C * (B + 1))
        simp only [Nat.add_mul, Nat.one_mul]
        omega
termination_by x.length
decreasing_by subst_vars; exact hr

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input

/-! ### Convert a bounded partial computation into a total bitstring reduction. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine
open Function Turing TM2Program TM2Composition Code Code.Partial
open Cslib.Complexity Polynomial

variable {K : Type} [DecidableEq K] [Fintype K]
variable (p : P K Unit) (i o : K)

private def label : Option Unit → p.Lab ⊕ Bool
  | none => .inr false
  | some () => .inr true

private def machineProg : p.Lab ⊕ Bool → TM2.Stmt (fun _ : K => Bool) (p.Lab ⊕ Bool) Bool
  | .inl l => p.prog Sum.inl (label p) l
  | .inr false => decr o (.inr true) (.inr false)
  | .inr true => .halt

noncomputable def machine [DecidableEq p.Lab] : FinTM2 where
  K := K
  k₀ := i
  k₁ := o
  Γ _ := Bool
  Λ := p.Lab ⊕ Bool
  main := .inl p.start
  σ := Bool
  initialState := false
  m := machineProg p o

private noncomputable def component [DecidableEq p.Lab] : Host.Comp where
  K := K
  Γ _ := Bool
  L := p.Lab ⊕ Bool
  prog := machineProg p o
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks := by simp

omit [Fintype K] in
private theorem clear_run (xs : List Bool) (S : Store K) (h : S o = xs) (v : Bool) :
    ∃ T w, Run (machineProg p o) (xs.length + 1) ⟨some (.inr false), v, S⟩
      ⟨some (.inr true), w, T⟩ ∧ T o = [] := by
  induction xs generalizing S v with
  | nil =>
    refine ⟨S, false, ?_, h⟩
    exact decr_run_zero (M := machineProg p o) (self := Sum.inr false)
      (ifZero := Sum.inr true) (ifPos := Sum.inr false)
      rfl v h
  | cons a xs ih =>
    obtain ⟨T, w, r, ht⟩ := ih (update S o xs) (by simp) true
    refine ⟨T, w, ?_, ht⟩
    have h' := decr_run_pos (M := machineProg p o) (self := Sum.inr false) (ifZero := Sum.inr true)
      (ifPos := Sum.inr false) rfl v h
    exact (h'.trans r).of_eq (by simp; omega)

omit [Fintype K] in
theorem isPolyTime_of_partial [Finite K] (f : List Bool → List Bool) (B : Polynomial Nat)
    (hr : ∀ x, p.Runs (B.eval x.length) (update (fun _ => []) i x)
      (fun a T => (if a.isSome then T o else []) = f x)) : ComplexityTheory.IsPolyTime f := by
  classical
  let _ := Fintype.ofFinite K
  let D := pushBound (machine p i o)
  apply Host.isPolyTime_reduction (c := component p o) (cX := i) (cO := o) (gX := id)
    (start := .inl p.start) (done := .inr true) (Equiv.refl Bool) f
    (B + Polynomial.X + Polynomial.C D * B + 1) rfl
  intro x
  let S : Store K := update (fun _ => []) i x
  obtain ⟨a, T, v, ⟨n, hn, r⟩, he⟩ := hr x _ (machineProg p o) Sum.inl (label p)
    (fun _ => rfl) false
  change ∃ (w : Bool) (U : Store K), RunLe (machineProg p o) _
    ⟨some (.inl p.start), false, update (fun _ => []) i (x.map id)⟩
    ⟨some (.inr true), w, U⟩ ∧ U o = (f x).map id
  simp only [List.map_id, eval_add, eval_X, eval_mul, eval_C, eval_one]
  have hlen := length_iter (machine p i o) o n ⟨some (.inl p.start), false, S⟩
    ⟨some (label p a), v, T⟩ r
  change (T o).length ≤ (S o).length + D * n at hlen
  have hS : (S o).length ≤ x.length := by by_cases h : o = i <;> simp [S, h]
  have ht := Nat.mul_le_mul_left D hn
  cases a with
  | none =>
    obtain ⟨U, w, r', hu⟩ := clear_run p o _ T rfl v
    exact ⟨w, U, (r.trans r').le (by omega), by simp [hu, ← he]⟩
  | some a =>
    exact ⟨v, T, r.le (by omega), by simpa using he⟩

noncomputable def growth [DecidableEq p.Lab] := pushBound (machine p i o)

theorem fit_after [DecidableEq p.Lab] {B N : Nat} {S T : Store K}
    (h : Works p B S (some ((), T))) (hs : fit S N) : fit T (N + growth p i o * B) := by
  obtain ⟨_ | a, U, w, ⟨m, hm, r⟩, he⟩ := h _ (machineProg p o) Sum.inl (label p)
    (fun _ => rfl) false
  · cases he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  intro k
  have hlen := length_iter (machine p i o) k m ⟨some (.inl p.start), false, S⟩
    ⟨some (label p (some ())), w, U⟩ r
  exact hlen.trans (Nat.add_le_add (hs k) (Nat.mul_le_mul_left _ hm))

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Polynomial running time of the translation to SAT. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input

open Machine Code Code.Partial Polynomial Turing TM2Program
open Cslib.CookLevin Cslib.Logic.LegacyPL BitstringEncoding Cslib.Complexity.FramedCNF

private noncomputable def code : P (Option K) Unit :=
  Partial.bind init.code (fun _ => Partial.bind (iterate one.code) (fun _ => finish.code))

def toSAT (x : List Bool) : List Bool :=
  match bitDecode (α := MonotoneThreeSatInstance) x with
  | none => []
  | some (n, φ) => if φ.all (ok n) then encodeCNF φ else []

private theorem start_eq (x : List Bool) :
    Function.update (fun _ : Option K => []) (some K.input) x = workspace (st x [] [] [] []) := by
  funext j; rcases j with _ | j <;> first | rfl | cases j <;> rfl

private theorem initial_fit (x : List Bool) : fit (st x [] [] [] []) x.length := by
  intro k; cases k <;> simp [st]

private theorem finish_eval (n : List Bool) (φ : CNF) :
    ∃ T, finish.eval (st [] n [] (φ.flatMap encodeClause).reverse (List.replicate φ.length true)) =
      some ((), T) ∧ T .out = encodeCNF φ := by
  simp [finish, seq, Op.move, Op.eval_bind, Op.push, st, put2, encodeCNF]

theorem time_toSAT : ComplexityTheory.IsPolyTime toSAT := by
  classical
  let D := growth (iterate one.code) (some K.input) (some K.out)
  let N : Polynomial Nat := 2 * (X + 1)
  let B := (N + 1) * (C one.C * (N + 1) + 2)
  let T := (X + 1) * (C one.C * (B + 1))
  let F := C finish.C * (N + C D * T + 1)
  apply isPolyTime_of_partial code (some K.input) (some K.out) toSAT (C init.C * (X + 1) + T + F)
  intro x
  rw [start_eq]
  let n := N.eval x.length
  let b := B.eval x.length
  let t := T.eval x.length
  have hn : n = 2 * (x.length + 1) := by simp [n, N]
  have hb : b = (n + 1) * (one.C * (n + 1) + 2) := by simp [b, B, n]
  have ht : t = (x.length + 1) * (one.C * (b + 1)) := by simp [t, T, b]
  have hneed : (C init.C * (X + 1) + T + F).eval x.length =
      init.C * (x.length + 1) + t + finish.C * (n + D * t + 1) := by
      simp only [F, n, t, eval_add, eval_mul, eval_C, eval_X, eval_one]
  rw [hneed]
  have h₀ := init.run _ _ (initial_fit x)
  rw [init_eval] at h₀
  unfold code
  have toEq : toSAT x =
      ((undelimit x).bind (fun (p, r) =>
        Option.map encodeCNF
          ((bitDecode (α := CNF) r).filter (·.all (ok (Computability.decodeNat p)))))).getD [] := by
    unfold toSAT
    rw [pairNat]
    cases h : undelimit x with
    | none => rfl
    | some q =>
      obtain ⟨p, r⟩ := q
      cases hr : bitDecode (α := CNF) r with
      | none => simp [hr]
      | some φ =>
        cases hφ : φ.all (ok (Computability.decodeNat p)) <;>
          simp [hr, hφ, Option.filter, -List.all_eq_true]
  rw [toEq]
  cases hu : undelimit x with
  | none =>
    simp only [hu, Option.map_none, pack] at h₀
    have h := bind_none (q := fun _ => Partial.bind (iterate one.code) (fun _ => finish.code)) h₀
    exact h.weaken (by omega) (fun a U he => by cases a <;> simp_all)
  | some q =>
    obtain ⟨p, r⟩ := q
    simp only [hu, Option.map_some, pack] at h₀
    let m := normalizeNat p
    have hem : TM2Recursive.bitsVal m = Computability.decodeNat p := by
      simp [m, normalizeNat_eq_encode_decode, TM2Recursive.bitsVal_encodeNat]
    have hl := congrArg List.length ((undelimit_eq_some_iff _ _ _).mp hu)
    simp only [List.length_append, length_delimit] at hl
    have hrn : r.length ≤ n := by omega
    have hmn : m.length ≤ n := by have := length_normalizeNat_le p; dsimp [m]; omega
    have hnb : n ≤ b := by
      rw [hb]
      exact (Nat.le_succ n).trans (Nat.le_mul_of_pos_right _ (by omega))
    have hfit : fit (workspace (st r m [] [] [])) n := by
      intro j
      rcases j with _ | j
      · simp [workspace]
      · cases j <;> simp_all [st, workspace]
    have h₁ := loop_run r m [] [] n b hrn hmn hnb
      (by simp only [List.length_nil, Nat.zero_add]; rw [hb]; gcongr <;> omega) (by simp; omega)
    have hle : (r.length + 1) * (one.C * (b + 1)) ≤ t := by rw [ht]; gcongr; omega
    replace h₁ := h₁.mono hle
    simp only [parse, hem, List.append_nil] at h₁
    simp only [Option.bind_some]
    cases hd : (bitDecode (α := CNF) r).filter (·.all (ok (Computability.decodeNat p))) with
    | none =>
      simp only [hd, Option.map_none, pack] at h₁
      have h := bind_some (q := fun _ => Partial.bind (iterate one.code) (fun _ => finish.code)) h₀
        (bind_none (q := fun _ => finish.code) h₁)
      exact h.weaken (by omega) (fun a U he => by cases a <;> simp_all)
    | some φ =>
      simp only [hd, Option.map_some, pack] at h₁
      let S := st [] m [] (φ.flatMap encodeClause).reverse (List.replicate φ.length true)
      have hf := fit_after (iterate one.code) (some K.input) (some K.out) h₁ hfit
      have hf' : fit S (n + D * t) := fun k => hf (some k)
      have h₂ := finish.run S _ hf'
      obtain ⟨U, hU, hout⟩ := finish_eval m φ
      change finish.eval S = _ at hU
      rw [hU] at h₂
      have h := bind_some (q := fun _ => Partial.bind (iterate one.code) (fun _ => finish.code)) h₀
        (bind_some (q := fun _ => finish.code) h₁ h₂)
      apply h.weaken (by omega)
      intro a V he
      cases a with
      | none => cases he
      | some a => obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he); exact hout

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Input

/-! ### The assignment semantics of the two reductions. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat
open Cslib.Logic.LegacyPL Cslib.CookLevin Cslib.Complexity.Karp
open MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory

private theorem feasible_iff {i : MonotoneThreeSatInstance} (hw : WellFormed i) :
    MonotoneThreeSatFeasible i ↔ CNFSat i.2 := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨bs, _, hs⟩
    exact ⟨_, hs⟩
  · rintro ⟨a, ha⟩
    refine ⟨List.ofFn (fun j : Fin i.1 => a j), by simp, ?_⟩
    intro c hc
    obtain ⟨l, hl, h⟩ := ha c hc
    have hlt := (hw c hc).2.1 l hl
    refine ⟨l, hl, ?_⟩
    simpa [List.getD_eq_getElem?_getD, hlt, CNFLiteral.Satisfies] using h

private theorem satNil : satDec [] = false := by
  have h : [] ∉ SATLang := fun ⟨φ, he, _⟩ => encodeCNF_ne_nil φ he
  simp [satDec, h]

private theorem toSAT_correct (x : List Bool) :
    monotoneThreeSatDec x = satDec (Input.toSAT x) := by
  classical
  unfold monotoneThreeSatDec Input.toSAT
  cases bitDecode (α := MonotoneThreeSatInstance) x with
  | none => exact satNil.symm
  | some i =>
    obtain ⟨n, φ⟩ := i
    have hw : φ.all (Input.ok n) ↔ WellFormed (n, φ) := by
      rw [List.all_eq_true]
      exact forall_congr' (fun c => forall_congr' (fun _ => Input.ok_iff))
    by_cases h : φ.all (Input.ok n)
    · simp only [h, ↓reduceIte]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Cslib.Complexity.DenseSAT.ToBinary.satDec_encodeCNF]
      exact (and_iff_right (hw.mp h)).trans (feasible_iff (hw.mp h))
    · simp [h, satNil, mt hw.mpr h]

theorem membership : monotoneThreeSatDec ∈ NP :=
  mem_NP_of_polyManyOneRed Cslib.Complexity.SatVerifier.Machine.cook_levin_SAT_np_complete.1
    ⟨Input.toSAT, Input.time_toSAT, toSAT_correct⟩

def letter (l : Nat × Bool) : Nat × Bool :=
  (2 * l.1 + (if l.2 then 0 else 1), true)

def posClause (c : CNFClause) : CNFClause :=
  match c with
  | [a] => [letter a, letter a, letter a]
  | [a, b] => [letter a, letter b, letter b]
  | _ => c.map letter

private theorem mem_posClause (k : Nat × Bool) (c : CNFClause) :
    k ∈ posClause c ↔ ∃ l ∈ c, letter l = k := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩ <;> simp [posClause, eq_comm]

private theorem length_posClause (c : CNFClause) :
    (posClause c).length = 3 ↔ c ≠ [] ∧ c.length ≤ 3 := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩ <;> simp [posClause]
  cases cs <;> simp

def mutex (x : Nat) : CNFClause :=
  [(2 * x, false), (2 * x + 1, false), (2 * x + 1, false)]

-- Emit one exclusion clause per occurrence, so the reduction never needs to deduplicate names.
def monoFormula (φ : CNF) : CNF :=
  φ.map posClause ++ φ.flatten.map (fun l => mutex l.1)

-- Writing the bound as a power of two costs one binary digit per token, plus two.
def ceiling (φ : CNF) : Nat :=
  2 * 2 ^ (Cslib.Complexity.SatVerifier.toks φ).length

private theorem below {φ : CNF} {c : CNFClause} (hc : c ∈ φ) {l : Nat × Bool} (hl : l ∈ c) :
    2 * l.1 + 1 < ceiling φ := by
  open Cslib.Complexity.SatVerifier in
  have hl' : l.1.size < (Cslib.Complexity.SatVerifier.toks φ).length := by
    have sub {α β : Type} (f : α → List β) {a : α} {as : List α} (h : a ∈ as) :
        (f a).length ≤ (as.flatMap f).length := by
      obtain ⟨left, right, rfl⟩ := List.append_of_mem h
      simp
      omega
    have h₁ := sub clauseToks hc
    have h₂ := sub litToks hl
    conv at h₁ => lhs; simp only [clauseToks, List.length_append, List.length_singleton]
    conv at h₂ => lhs; simp only [litToks, List.length_append, List.length_map,
      BinaryNatEncoding.length_encodeNat, List.length_singleton]
    unfold toks
    omega
  have hb := Nat.size_le.mp hl'.le
  unfold ceiling
  omega

def monoInstance (φ : CNF) : MonotoneThreeSatInstance := (ceiling φ, monoFormula φ)

private theorem well_monoInstance (φ : CNF) :
    WellFormed (monoInstance φ) ↔ ∀ c ∈ φ, c ≠ [] ∧ c.length ≤ 3 := by
  constructor
  · intro h c hc
    apply (length_posClause _).mp
    exact (h _ (List.mem_append_left _ (List.mem_map_of_mem hc))).1
  · intro h c hc
    change c ∈ _ ++ _ at hc
    rcases List.mem_append.mp hc with hp | hn
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
      refine ⟨(length_posClause _).mpr (h d hd), ?_, Or.inl ?_⟩
      · intro l hl
        obtain ⟨k, hk, rfl⟩ := (mem_posClause l d).mp hl
        have hb := below hd hk
        change 2 * k.1 + (if k.2 then 0 else 1) < ceiling φ
        split <;> omega
      · intro l hl
        obtain ⟨k, _, rfl⟩ := (mem_posClause l d).mp hl
        rfl
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
      obtain ⟨d, hd, hl⟩ := List.mem_flatten.mp hl
      have hb := below hd hl
      refine ⟨rfl, ?_, Or.inr ?_⟩
      · change ∀ k ∈ mutex l.1, k.1 < ceiling φ
        simp [mutex]
        omega
      · simp [mutex]

private def liftAssignment (a : Nat → Bool) (j : Nat) : Bool :=
  if j % 2 = 0 then a (j / 2) else !a (j / 2)

private theorem sat_monoFormula (φ : CNF) :
    CNFSat (monoFormula φ) ↔ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies, cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hp, hn⟩ := CNF.satisfies_append.mp ha
    refine ⟨fun j => a (2 * j), ?_⟩
    intro c hc
    obtain ⟨l, hl, h⟩ := hp _ (List.mem_map_of_mem hc)
    obtain ⟨⟨j, b⟩, hmem, rfl⟩ := (mem_posClause l c).mp hl
    refine ⟨(j, b), hmem, ?_⟩
    have hmu := hn _ (List.mem_map_of_mem (List.mem_flatten.mpr ⟨c, hc, hmem⟩))
    cases b <;> simp_all [letter, mutex, CNFLiteral.Satisfies]
  · rintro ⟨a, ha⟩
    refine ⟨liftAssignment a, CNF.satisfies_append.mpr ⟨?_, ?_⟩⟩
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨⟨j, b⟩, hl, h⟩ := ha d hd
      refine ⟨_, (mem_posClause _ _).mpr ⟨(j, b), hl, rfl⟩, ?_⟩
      have div : (j * 2 + 1) / 2 = j := by omega
      cases b <;> simpa [div, letter, liftAssignment, Nat.mul_comm 2, CNFLiteral.Satisfies] using h
    · intro c hc
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hc
      have div : (l.1 * 2 + 1) / 2 = l.1 := by omega
      cases h : a l.1 <;> simp [div, mutex, liftAssignment, Nat.mul_comm 2, h]

private theorem formula_correct (φ : CNF) :
    sat3Dec (encodeCNF φ) = monotoneThreeSatDec (bitEncode (monoInstance φ)) := by
  classical
  unfold sat3Dec monotoneThreeSatDec
  rw [bitDecode_bitEncode, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨ψ, he, hlen, hs⟩
    obtain rfl := encodeCNF_injective he
    obtain ⟨a, ha⟩ := cnfSat_iff_exists_satisfies.mp hs
    have hw : WellFormed (monoInstance ψ) := by
      apply (well_monoInstance ψ).mpr
      intro c hc
      exact ⟨fun he => by simpa [he] using ha c hc,
        of_decide_eq_true (List.all_eq_true.mp hlen c hc)⟩
    exact ⟨hw, (feasible_iff hw).mpr ((sat_monoFormula ψ).mpr hs)⟩
  · rintro ⟨hw, hf⟩
    refine ⟨φ, rfl, List.all_eq_true.mpr ?_, (sat_monoFormula φ).mp ((feasible_iff hw).mp hf)⟩
    intro c hc
    exact decide_eq_true ((well_monoInstance φ).mp hw c hc).2

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

/-! ### Compile framed combinations of fixed bits and variable names. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

open Function Turing TM2Program Code Code.Partial BitstringEncoding
variable {K : Type} [DecidableEq K]

def pushList {L : Type} (b : K) (xs : List Bool) (q : TM2.Stmt (fun _ : K => Bool) L Bool) :=
  xs.foldr (fun x i => .push b (fun _ => x) i) q

theorem pushList_step {L : Type} (b : K) (xs : List Bool) (q : TM2.Stmt (fun _ : K => Bool) L Bool)
    (v : Bool) (S : Store K) :
    TM2.stepAux (pushList b xs q) v S = TM2.stepAux q v (update S b (xs.reverse ++ S b)) := by
  induction xs generalizing S with
  | nil => simp [pushList]
  | cons x xs ih =>
    change TM2.stepAux (pushList b xs q) v (update S b (x :: S b)) = _
    rw [ih]; simp [List.reverse_cons, List.append_assoc]

private def appendMapCode (a b : K) (f : Bool → List Bool) : P (Option K) Unit where
  Lab := Bool
  start := false
  prog pc ret
    | false =>
      .peek (some a) (fun _ o => o.isSome) <| .branch id
        (.pop (some a) (fun _ o => o.getD false) <| .push none id <| .branch id
          (pushList (some b) (f true) (.goto fun _ => pc false))
          (pushList (some b) (f false) (.goto fun _ => pc false)))
        (.goto fun _ => pc true)
    | true => moveB none (some a) some id (pc true) (ret (some ()))

private def amapSt (S : Store K) (a b : K) (x y scratch : List Bool) :
    Store (Option K) := update (workspace (put2 S a b x y)) none scratch

private theorem readMap {L : Type} (a b : K) (hab : a ≠ b) (f : Bool → List Bool)
    (m : L → TM2.Stmt (fun _ : Option K => Bool) L Bool) (pc : Bool → L) (ret : Option Unit → L)
    (hm : ∀ l, m (pc l) = (appendMapCode a b f).prog pc ret l) (S : Store K)
    (x y scratch : List Bool) (v : Bool) :
    ∃ w, Run m (x.length + 1) ⟨some (pc false), v, amapSt S a b x y scratch⟩
      ⟨some (pc true), w, amapSt S a b [] ((x.flatMap f).reverse ++ y) (x.reverse ++ scratch)⟩ := by
  induction x generalizing y scratch v with
  | nil =>
    refine ⟨false, Run.single ?_⟩
    simp [hm false, appendMapCode, TM2.stepAux, amapSt, workspace, put2, hab]
  | cons z xs ih =>
    obtain ⟨w, r⟩ := ih ((f z).reverse ++ y) (z :: scratch) z
    have h : Run m 1 ⟨some (pc false), v, amapSt S a b (z :: xs) y scratch⟩
        ⟨some (pc false), z, amapSt S a b xs ((f z).reverse ++ y) (z :: scratch)⟩ := by
      apply Run.single
      cases z <;> simp only [hm false, appendMapCode, TM2.stepAux, amapSt,
        Function.update_of_ne (by simp : some a ≠ none), workspace, put2, update_of_ne hab,
        update_self, List.head?_cons, Option.isSome_some, id_eq, Bool.cond_true, Option.getD_some,
        List.tail_cons, Bool.cond_false, pushList_step]
      all_goals congr 1; funext j; rcases j with _ | j
      all_goals try rfl
      all_goals by_cases hj : j = a <;> by_cases hk : j = b <;> simp_all [workspace]
    refine ⟨w, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using (h.trans r).of_eq
      (show 1 + (xs.length + 1) = (z :: xs).length + 1 by simp; omega)

private theorem appendMap_run (a b : K) (hab : a ≠ b) (f : Bool → List Bool) (S : Store K) :
    Works (appendMapCode a b f) (2 * (S a).length + 2) (workspace S)
      (pack (some ((), update S b (((S a).flatMap f).reverse ++ S b)))) := by
  intro L m pc ret hm v
  obtain ⟨w, r⟩ := readMap a b hab f m pc ret hm S (S a) (S b) [] v
  have h₀ : amapSt S a b (S a) (S b) [] = workspace S := by
    funext j; rcases j with _ | j
    · rfl
    · by_cases hj : j = a <;> by_cases hk : j = b <;> simp_all [amapSt, workspace, put2]
  let y := ((S a).flatMap f).reverse ++ S b
  let U := amapSt S a b [] y (S a).reverse
  rw [h₀, List.append_nil] at r
  obtain ⟨v', T, r', ht, ha, hf⟩ := moveB_run (M := m) (a := none) (b := some a)
    (d := some) (g := id) (self := pc true) (next := ret (some ())) (hm true) (by simp)
    (S a).reverse (S a).reverse [] w U (by simp [U, amapSt]) (by simp [IsBitBlock]) rfl
  have he : T = workspace (update S b y) := by
    funext j; rcases j with _ | j
    · exact ht
    · by_cases hj : j = a
      · subst j; simpa [U, amapSt, put2, workspace, hab] using ha
      · by_cases hk : j = b <;> simpa [U, amapSt, workspace, put2, hj, hk]
        using hf (some j) (by simp) (by simpa using hj)
  exact ⟨some (), T, v', (r.trans r').le (by simp; omega), by rw [he]; rfl⟩

inductive Piece
  | text (w : List Bool)
  | source (f : Bool → List Bool)

def Piece.eval (x : List Bool) : Piece → List Bool
  | .text w => w
  | .source f => x.flatMap f

abbrev Pattern := List Piece

def Pattern.eval (p : Pattern) (x : List Bool) := p.flatMap (Piece.eval x)

def quoted (w : List Bool) := w.flatMap (fun b => [true, b])

def Pattern.frame (p : Pattern) : Pattern :=
  p.map (fun | .text s => Piece.text (quoted s) | .source f => .source (quoted ∘ f))
    ++ [.text [false]]

private theorem eval_quote (p : Pattern) (x : List Bool) :
    (p.map (fun
      | Piece.text s => Piece.text (quoted s)
      | .source f => .source (quoted ∘ f))).flatMap (Piece.eval x) = quoted (p.eval x) := by
  induction p with
  | nil => rfl
  | cons s p ih =>
    cases s <;> simpa [Pattern.eval, Piece.eval, quoted, List.flatMap_assoc,
      Function.comp_def] using ih

@[simp] theorem eval_frame (p : Pattern) (x : List Bool) : p.frame.eval x = delimit (p.eval x) := by
  unfold Pattern.frame Pattern.eval
  rw [List.flatMap_append, eval_quote]
  simpa [Pattern.eval, Piece.eval, quoted] using
    (Cslib.Complexity.Karp.Emit3.delimit_eq (p.eval x)).symm

private def mapC (f : Bool → List Bool) := max (f false).length (f true).length + 2

private theorem size_map (f : Bool → List Bool) (x : List Bool) :
    (x.flatMap f).length ≤ x.length * (max (f false).length (f true).length) := by
  induction x with
  | nil => simp
  | cons b xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    cases b <;> omega

def Op.emitPiece (a b : K) (hab : a ≠ b) (s : Piece) : Op K Unit where
  code := match s with
    | .text w => Code.atom fun ret => pushList (some b) w (.goto fun _ => ret (some ()))
    | .source f => appendMapCode a b f
  eval S := some ((), update S b ((s.eval (S a)).reverse ++ S b))
  C := match s with
    | .text w => w.length + 1
    | .source f => mapC f
  run S n hs := by
    cases s with
    | text w =>
      intro L m pc ret hm v
      refine ⟨some (), _, v, (Run.single ?_).le ?_, rfl⟩
      · rw [hm]
        change TM2.stepAux (pushList (some b) w (.goto fun _ => ret (some ()))) v (workspace S) = _
        rw [pushList_step]
        simp [TM2.stepAux, Piece.eval, workspace]
      · exact Nat.mul_pos (Nat.succ_pos w.length) (Nat.succ_pos n)
    | source f =>
      exact (appendMap_run a b hab f S).mono (by
        have := hs a
        simp only [mapC, Nat.add_mul, Nat.mul_add, Nat.mul_one]
        omega)
  size S n _ _ hs he := by
    cases he
    intro j
    by_cases hj : j = b
    · subst j
      have := hs b
      cases s with
      | text w => simp only [Piece.eval, update_self, List.length_append, List.length_reverse,
        Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]; omega
      | source f =>
        have h := (size_map f (S a)).trans (Nat.mul_le_mul_right _ (hs a))
        simp only [update_self, Piece.eval, List.length_append, List.length_reverse, mapC,
          Nat.mul_add, Nat.add_mul, Nat.mul_one]
        rw [Nat.mul_comm] at h
        omega
    · rw [update_of_ne hj]
      have h := hs j
      cases s <;> simp only [mapC, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] <;> omega

noncomputable def Op.emit (a b : K) (hab : a ≠ b) : Pattern → Op K Unit
  | [] => .pure ()
  | s :: p => Op.bind (Op.emitPiece a b hab s) fun _ => Op.emit a b hab p

theorem Op.emit_eval (a b : K) (hab : a ≠ b) (p : Pattern) (S : Store K) :
    (Op.emit a b hab p).eval S = some ((), update S b ((p.eval (S a)).reverse ++ S b)) := by
  induction p generalizing S with
  | nil => simp [Op.emit, Op.pure, Pattern.eval]
  | cons s p ih =>
    simp [Op.emit, Op.eval_bind, Op.emitPiece, ih, hab, Pattern.eval, List.append_assoc]

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Machine

/-! ### Emit positive clauses and mutual-exclusion clauses into separate accumulators. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output
open BitstringEncoding Machine Machine.Code Machine.Code.Partial
open Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.Karp
open Computability

inductive K | input | header | clause | lit | name | posBody | pos | neg | tmp | out
  deriving DecidableEq

instance instFintypeK : Fintype K := Fintype.ofList
  [.input, .header, .clause, .lit, .name, .posBody, .pos, .neg, .tmp, .out]
  (fun k => by cases k <;> decide)

private def clearCode {J : Type} [DecidableEq J] (k : J) : P (Option J) Unit where
  Lab := Unit
  start := ()
  prog pc ret _ := TM2Program.decr (some k) (ret (some ())) (pc ())

private def clear {J : Type} [DecidableEq J] (k : J) : Op J Unit where
  code := clearCode k
  eval S := some ((), Function.update S k [])
  C := 1
  run S n hs := by
    intro L m pc ret hm v
    have aux (xs : List Bool) (T : Store (Option J)) (he : T (some k) = xs) (v : Bool) :
        ∃ w, TM2Program.Run m (xs.length + 1) ⟨some (pc ()), v, T⟩
          ⟨some (ret (some ())), w, Function.update T (some k) []⟩ := by
      induction xs generalizing T v with
      | nil =>
        refine ⟨false, ?_⟩
        rw [show Function.update T (some k) [] = T by rw [← he, Function.update_eq_self]]
        exact TM2Program.decr_run_zero (hm ()) v he
      | cons x xs ih =>
        obtain ⟨w, h⟩ := ih (Function.update T (some k) xs) (by simp) true
        refine ⟨w, ?_⟩
        simpa using ((TM2Program.decr_run_pos (hm ()) v he).trans h).of_eq
          (show 1 + (xs.length + 1) = (x :: xs).length + 1 by simp; omega)
    obtain ⟨w, h⟩ := aux (S k) (workspace S) rfl v
    exact ⟨some (), _, w, h.le (by have := hs k; omega), by simp [pack]⟩
  size S n _ _ hs he := by
    cases he; intro j
    by_cases hj : j = k
    · subst j; simp
    · simpa [hj] using Nat.le_succ_of_le (hs j)

local infixr:55 " ⇢ " => Op.bind
local infixr:55 " ▷▷ " => Input.seq

def nameP (odd empty : Bool) : Pattern :=
  [.text (if odd || !empty then [odd] else []), .source List.singleton]

def litP (odd empty pol : Bool) : Pattern := ((nameP odd empty).frame ++ [Piece.text [pol]]).frame

def mutexP (empty : Bool) : Pattern :=
  (litP false empty false ++ litP true empty false ++ litP true empty false).frame

def many (p : Pattern) (k : Nat) : Pattern := (List.replicate k p).flatten

private theorem pat_append (p q : Pattern) (x : List Bool) :
    (p ++ q).eval x = p.eval x ++ q.eval x := by simp [Pattern.eval]

private theorem flat_singleton (xs : List Bool) : xs.flatMap List.singleton = xs := by
  induction xs <;> simp_all [List.singleton]

private theorem nameP_eval (j : Nat) (odd : Bool) :
    (nameP odd (encodeNat j).isEmpty).eval (encodeNat j) =
      encodeNat (2 * j + (if odd then 1 else 0)) := by
  cases odd with
  | true => simp [nameP, Pattern.eval, Piece.eval, flat_singleton, Emit3.encodeNat_bit1]
  | false =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rfl
    · have h : encodeNat j ≠ [] := fun h => hj.ne' (Emit3.encodeNat_eq_nil.mp h)
      simp [nameP, Pattern.eval, Piece.eval, flat_singleton, h, Emit3.encodeNat_bit0 _ hj]

private theorem litP_eval (j : Nat) (odd pol : Bool) :
    (litP odd (encodeNat j).isEmpty pol).eval (encodeNat j) =
      delimit (bitEncode (2 * j + (if odd then 1 else 0), pol)) := by
  simp only [litP, eval_frame, pat_append, nameP_eval]
  rfl

theorem enc_cons {α : Type} [BitstringEncoding α] (a : α) (t : List α) :
    bitEncode (a :: t) = delimit (bitEncode a) ++ bitEncode t := rfl

theorem enc_nil {α : Type} [BitstringEncoding α] : bitEncode ([] : List α) = [] := rfl

theorem enc_append {α : Type} [BitstringEncoding α] (u v : List α) :
    bitEncode (u ++ v) = bitEncode u ++ bitEncode v := by
  induction u with
  | nil => simp [enc_nil]
  | cons a u ih => simp [enc_cons, ih, List.append_assoc]

private theorem mutexP_eval (j : Nat) :
    (mutexP (encodeNat j).isEmpty).eval (encodeNat j) = delimit (bitEncode (mutex j)) := by
  simp [mutexP, eval_frame, pat_append, litP_eval, mutex, enc_cons, enc_nil, List.append_assoc]

private theorem many_eval (k : Nat) (l : Nat × Bool) :
    (many (litP (!l.2) (encodeNat l.1).isEmpty true) k).eval (encodeNat l.1) =
      bitEncode (List.replicate k (letter l)) := by
  induction k with
  | zero => simp [many, enc_nil, Pattern.eval]
  | succ k ih =>
    rw [List.replicate_succ, enc_cons]
    change (_ ++ many _ k).eval _ = _
    rw [pat_append, ih, litP_eval]
    cases l with | mk j p => cases p <;> rfl

-- Read one literal, pad the positive clause when this is its last literal, and emit its mutex.
noncomputable def read (copies : Nat) : Op K Bool :=
  Op.split .clause .lit ▷▷ Op.split .lit .name ▷▷ Op.singleton .lit ⇢ fun b =>
  Op.empty .clause ⇢ fun last => Op.empty .name ⇢ fun zero =>
  Op.emit .name .posBody (by decide) (many (litP (!b) zero true) (if last then copies else 1)) ▷▷
  Op.emit .name .neg (by decide) (mutexP zero) ▷▷ clear .name ▷▷ Op.pure last

def st (input header clause posBody pos neg : List Bool) : Store K
  | .input => input
  | .header => header
  | .clause => clause
  | .posBody => posBody
  | .pos => pos
  | .neg => neg
  | _ => []

private theorem read_eval (k : Nat) (l : Nat × Bool) (tail : CNFClause)
    (x h body ps ns : List Bool) :
    (read k).eval (st x h (bitEncode (l :: tail)) body ps ns) =
      some (tail.isEmpty, st x h (bitEncode tail)
        ((bitEncode (List.replicate (if tail.isEmpty then k else 1) (letter l))).reverse ++ body)
        ps ((delimit (bitEncode (mutex l.1))).reverse ++ ns)) := by
  have emp : (bitEncode tail).isEmpty = tail.isEmpty := by
    cases tail with
    | nil => rfl
    | cons a t =>
      rw [enc_cons]
      cases hv : bitEncode a <;> simp [delimit]
  obtain ⟨j, b⟩ := l
  have enc : bitEncode (j, b) = delimit (encodeNat j) ++ [b] := rfl
  have hb : bitDecode (α := Bool) [b] = some b := rfl
  simp only [read, Input.seq, Op.split, put2, Op.singleton, Op.empty, clear, Op.pure, enc_cons, enc,
    Op.eval_bind, st, List.append_nil, undelimit_delimit, Option.map_some, Op.emit_eval,
    Option.bind_some, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
    List.isEmpty_iff, Function.update_idem, Function.update_self, hb, emp, mutexP_eval,
    Option.some.injEq, Prod.mk.injEq, true_and]
  have hv := many_eval (if tail.isEmpty then k else 1) (j, b)
  simp only at hv
  simp only [List.isEmpty_iff] at hv
  have emp' : bitEncode tail = [] ↔ tail = [] := by simpa using congrArg (· = true) emp
  rw [if_congr emp' rfl rfl, hv]
  funext i; cases i <;> simp [st]

noncomputable def close : Op K Bool :=
  Op.move .posBody .tmp ▷▷ Op.frameOut .tmp .pos ▷▷ Op.pure true

noncomputable def finish : Op K Bool :=
  Op.move .neg .out ▷▷ Op.move .pos .out ▷▷ Op.frameOut .header .tmp ▷▷
    Op.move .tmp .out ▷▷ Op.pure false

noncomputable def literals : Op K Bool :=
  Op.empty .clause ⇢ fun empty => if empty then Op.pure false else
  read 3 ⇢ fun last => if last then close else
  read 2 ⇢ fun last => if last then close else
  read 1 ⇢ fun last => if last then close else Op.pure false

noncomputable def step : Op K Bool :=
  Op.empty .input ⇢ fun empty => if empty then finish else
  Op.split .input .clause ▷▷ literals

private theorem close_eval (x h body ps ns : List Bool) :
    close.eval (st x h [] body ps ns) =
      some (true, st x h [] [] ((delimit body.reverse).reverse ++ ps) ns) := by
  simp only [close, Input.seq, Op.move, put2, Op.frameOut, Op.pure, Op.eval_bind, st,
    List.append_nil, Option.bind_some, Function.update_idem, Function.update_self, ne_eq,
    reduceCtorEq, not_false_eq_true, Function.update_of_ne, Option.some.injEq, Prod.mk.injEq,
    true_and]
  funext i; cases i <;> rfl

theorem step_nil (h ps ns : List Bool) :
    ∃ S, step.eval (st [] h [] [] ps ns) = some (false, S) ∧
      S .out = delimit h ++ ps.reverse ++ ns.reverse := by
  simp [step, finish, Input.seq, Op.eval_bind, Op.empty, Op.frameOut, Op.move, Op.pure, st, put2,
    List.append_assoc]

private theorem enter (c : CNFClause) (φ : CNF) (h ps ns : List Bool) :
    step.eval (st (bitEncode (c :: φ)) h [] [] ps ns) =
      literals.eval (st (bitEncode φ) h (bitEncode c) [] ps ns) := by
  have he : bitEncode (c :: φ) ≠ [] := by
    rw [enc_cons]; cases bitEncode c <;> simp [delimit]
  have he' : delimit (bitEncode c) ++ bitEncode φ ≠ [] := he
  simp only [step, Op.empty, Input.seq, Op.split, put2, enc_cons, Op.eval_bind, st,
    Option.bind_some, List.isEmpty_iff, he', ↓reduceIte, List.append_nil, undelimit_delimit,
    Option.map_some]
  congr 1
  funext i; cases i <;> rfl

def short (c : CNFClause) : Bool := !c.isEmpty && decide (c.length ≤ 3)

def edges (c : CNFClause) : CNF := c.map (fun l => mutex l.1)

private theorem nonempty_enc (l : Nat × Bool) (s : CNFClause) : bitEncode (l :: s) ≠ [] := by
  rw [enc_cons]; cases bitEncode l <;> simp [delimit]

private theorem evalEmpty (k : K) (S : Store K)
    : (Op.empty k).eval S = some ((S k).isEmpty, S) := rfl

private theorem evalPure {α : Type} (a : α) (S : Store K) :
    (Op.pure a).eval S = some (a, S) := rfl

private theorem evalIte {α : Type} (b : Bool) (p q : Op K α) (S : Store K) :
    (if b then p else q).eval S = if b then p.eval S else q.eval S := by cases b <;> rfl

private theorem literals_spec (S : Store K) :
    literals.eval S = if (S .clause).isEmpty then some (false, S) else
      ((read 3).eval S).bind fun (a, T) => if a then close.eval T else
        ((read 2).eval T).bind fun (b, U) => if b then close.eval U else
          ((read 1).eval U).bind fun (c, V) => if c then close.eval V else some (false, V) := by
  simp only [literals, Op.eval_bind, evalEmpty, Option.bind_some, evalIte, evalPure]

theorem step_cons (c : CNFClause) (φ : CNF) (h ps ns : List Bool) :
    if short c then
      step.eval (st (bitEncode (c :: φ)) h [] [] ps ns) = some (true,
        st (bitEncode φ) h [] [] ((delimit (bitEncode (posClause c))).reverse ++ ps)
          ((bitEncode (edges c)).reverse ++ ns))
    else ∃ T, step.eval (st (bitEncode (c :: φ)) h [] [] ps ns) = some (false, T) ∧
      T .out = [] := by
  rw [enter]
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, cs⟩⟩⟩⟩ <;>
    simp [short, literals_spec, st, nonempty_enc, read_eval, close_eval,
      enc_nil, List.append_assoc] <;>
    simp [posClause, edges, enc_cons, enc_nil, List.append_assoc]

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output

/-! ### Reconstruct the framed input directly from the SAT tokenizer. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Tokens

open Machine Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier BitstringEncoding Computability

def bits : Sym → List Bool
  | .bit b => quoted (quoted [true, b])
  | .lit b => quoted (quoted [false, b] ++ [false])
  | .cl => [false]
  | _ => []

private theorem q_append (a b : List Bool) : quoted (a ++ b) = quoted a ++ quoted b := by
  simp [quoted]

private theorem bit_tokens (w : List Bool) :
    ((w.map Sym.bit).flatMap bits) = quoted (quoted (quoted w)) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change bits (.bit b) ++ (w.map Sym.bit).flatMap bits = quoted (quoted ([true, b] ++ quoted w))
    rw [ih, q_append, q_append]
    rfl

private theorem lit_tokens (l : Nat × Bool) :
    (litToks l).flatMap bits = quoted (delimit (bitEncode l)) := by
  obtain ⟨j, b⟩ := l
  change ((encodeNat j).map Sym.bit ++ [Sym.lit b]).flatMap bits =
    quoted (delimit (delimit (encodeNat j) ++ [b]))
  have hd (x : List Bool) : delimit x = quoted x ++ [false] := Emit3.delimit_eq x
  simp only [List.flatMap_append, List.flatMap_singleton, bit_tokens, bits, hd, q_append]
  simp [quoted, List.flatMap_assoc, List.append_assoc]

private theorem lits_tokens (c : CNFClause) :
    (c.flatMap litToks).flatMap bits = quoted (bitEncode c) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    change (litToks l ++ c.flatMap litToks).flatMap bits =
      quoted (delimit (bitEncode l) ++ bitEncode c)
    rw [List.flatMap_append, lit_tokens, ih, q_append]

theorem encoded (φ : CNF) : (toks φ).flatMap bits = bitEncode φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change ((c.flatMap litToks ++ [Sym.cl]) ++ toks φ).flatMap bits =
      delimit (bitEncode c) ++ bitEncode φ
    simp only [List.flatMap_append, List.flatMap_singleton, lits_tokens, ih]
    rw [Emit3.delimit_eq]; rfl

theorem length_encoded (φ : CNF) : (bitEncode φ).length ≤ 12 * (toks φ).length := by
  rw [← encoded]
  generalize toks φ = ts
  induction ts with
  | nil => simp
  | cons s ts ih =>
    have h : (bits s).length ≤ 12 := by
      cases s with
      | bit b | lit b | val b => cases b <;> decide
      | _ => decide
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Tokens

/-! ### Bound the time to emit the entire monotone formula. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output
open Machine Machine.Code Machine.Code.Partial BitstringEncoding
open Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.SatVerifier

private def posPart (φ : CNF) := φ.map posClause
private def negPart (φ : CNF) := φ.flatMap edges

def result (φ : CNF) (header ps ns : List Bool) : List Bool :=
  if φ.all short then
    delimit header ++ ps.reverse ++ bitEncode (posPart φ) ++ ns.reverse ++ bitEncode (negPart φ)
  else []

private theorem result_step {c : CNFClause} (hs : short c) (φ : CNF) (h ps ns : List Bool) :
    result (c :: φ) h ps ns = result φ h ((delimit (bitEncode (posClause c))).reverse ++ ps)
      ((bitEncode (edges c)).reverse ++ ns) := by
  simp [result, posPart, negPart, hs, enc_cons, enc_append, List.append_assoc]

private theorem fit_input {φ : CNF} {h ps ns : List Bool} {B : Nat}
    (hx : (bitEncode φ).length ≤ B) (hh : h.length ≤ B)
    (hps : ps.length ≤ B) (hns : ns.length ≤ B) :
    fit (st (bitEncode φ) h [] [] ps ns) B := by intro k; cases k <;> simp_all [st]

private theorem run_aux (φ : CNF) (h ps ns : List Bool) (N B : Nat)
    (hx : (bitEncode φ).length ≤ N) (hh : h.length ≤ N) (hN : N ≤ B)
    (hps : ps.length + φ.length * (step.C * (N + 1)) ≤ B)
    (hns : ns.length + φ.length * (step.C * (N + 1)) ≤ B) :
    ∃ U, Works (iterate step.code) ((φ.length + 1) * (step.C * (B + 1)))
      (workspace (st (bitEncode φ) h [] [] ps ns)) (some ((), U)) ∧
      U (some .out) = result φ h ps ns := by
  induction φ generalizing ps ns with
  | nil =>
    obtain ⟨S, he, hout⟩ := step_nil h ps ns
    have run := step.run (st (bitEncode ([] : CNF)) h [] [] ps ns) B
      (fit_input (hx.trans hN) (hh.trans hN) (by simpa using hps) (by simpa using hns))
    rw [show bitEncode ([] : CNF) = [] from rfl, he] at run
    exact ⟨workspace S, by simpa [enc_nil] using repeat_stop (by simpa [pack] using run),
      by simpa [workspace, result, posPart, negPart, enc_nil] using hout⟩
  | cons c φ ih =>
    have hfit := fit_input (φ := c :: φ) (h := h) (ps := ps) (ns := ns) (hx.trans hN) (hh.trans hN)
      (by omega) (by omega)
    have run := step.run _ _ hfit
    by_cases hs : short c
    · have he := step_cons c φ h ps ns
      simp only [hs, ↓reduceIte] at he
      rw [he] at run
      have he' := step_cons c φ h [] []
      simp only [hs, ↓reduceIte, List.append_nil] at he'
      have hfresh := step.size _ N _ _ (fit_input hx hh (by simp) (by simp)) he'
      have hp := hfresh .pos
      have hn := hfresh .neg
      change (delimit (bitEncode (posClause c))).reverse.length ≤ _ at hp
      change (bitEncode (edges c)).reverse.length ≤ _ at hn
      rw [List.length_reverse] at hp hn
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at hps hns
      have hx' : (bitEncode φ).length ≤ N := by
        rw [enc_cons, List.length_append] at hx; omega
      obtain ⟨U, rt, ho⟩ := ih ((delimit (bitEncode (posClause c))).reverse ++ ps)
        ((bitEncode (edges c)).reverse ++ ns) hx'
        (by simp only [List.length_append, List.length_reverse]; omega)
        (by simp only [List.length_append, List.length_reverse]; omega)
      refine ⟨U, (repeat_more run rt).mono ?_, by rwa [result_step hs]⟩
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · obtain ⟨T, he, ht⟩ := (by simpa [hs] using step_cons c φ h ps ns :
          ∃ T, step.eval (st (bitEncode (c :: φ)) h [] [] ps ns) = some (false, T) ∧ T .out = [])
      rw [he] at run
      refine ⟨workspace T, (repeat_stop run).mono ?_, ?_⟩
      · exact Nat.le_mul_of_pos_left _ (by omega)
      · simpa [workspace, result, hs] using ht

def g (φ : CNF) : List Bool :=
  if φ.all short then bitEncode (monoInstance φ) else []

noncomputable def workBound (t : Nat) : Nat :=
  let n := 12 * (t + 1)
  let b := n + n * (step.C * (n + 1))
  (n + 1) * (step.C * (b + 1))

theorem work_mono : Monotone workBound := by intro a b hab; dsimp [workBound]; gcongr

private theorem negPart_eq (φ : CNF) : negPart φ = φ.flatten.map (fun l => mutex l.1) := by
  induction φ with
  | nil => rfl
  | cons c φ ih => simpa [negPart, edges, List.map_append] using congrArg (edges c ++ ·) ih

theorem run (φ : CNF) :
    ∃ U, Works (iterate step.code) (workBound (toks φ).length)
      (workspace (st (bitEncode φ) (Computability.encodeNat (ceiling φ)) [] [] [] []))
      (some ((), U)) ∧ U (some .out) = g φ := by
  let n := 12 * ((toks φ).length + 1)
  let b := n + n * (step.C * (n + 1))
  have h₁ : (bitEncode φ).length ≤ n := by have := Tokens.length_encoded φ; dsimp [n]; omega
  have hcode (t : Nat) :
      Computability.encodeNat (2 * 2 ^ t) = List.replicate (t + 1) false ++ [true] := by
    rw [← Nat.pow_succ', Cslib.Complexity.Karp.Emit3.encodeNat_two_pow]
  have h₂ : (Computability.encodeNat (ceiling φ)).length ≤ n := by
    simp [ceiling, hcode, n]
  have h₃ : φ.length ≤ n := (Cslib.Complexity.PolynomialEncoding.decoded_list_length_le
    (bitDecode_bitEncode φ)).trans h₁
  have hsize : ([] : List Bool).length + φ.length * (step.C * (n + 1)) ≤ b := by
    simpa [b] using Nat.le_add_left_of_le (Nat.mul_le_mul_right (step.C * (n + 1)) h₃) (k := n)
  obtain ⟨U, r, hu⟩ := run_aux φ _ [] [] n b h₁ h₂ (by dsimp [b]; omega) hsize hsize
  refine ⟨U, r.mono (by change _ ≤ (n + 1) * (step.C * (b + 1)); gcongr), ?_⟩
  rw [hu]
  unfold result g
  split
  · change _ = delimit (Computability.encodeNat (ceiling φ)) ++ bitEncode (monoFormula φ)
    simp [posPart, negPart_eq, monoFormula, enc_append, List.append_assoc]
  · rfl

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output

/-! ### Connect the reduction machine to the SAT tokenizer. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output
open Turing Function TM2Program TM2Embedding BitstringEncoding
open Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier Machine Code Code.Partial

private noncomputable abbrev program := iterate step.code
private abbrev Stk := Option (Option K)

@[reducible] private def alphabet : Stk → Type
  | none => Sym
  | some _ => Bool

private instance finAlphabet (k : Stk) : Fintype (alphabet k) := by cases k <;> infer_instance

private def emb : SEmb (fun _ : Option K => Bool) alphabet where
  e := some
  inj := Option.some_injective _
  ι _ := Equiv.refl Bool

private abbrev Lab := (program.Lab ⊕ Option Unit) ⊕ (Bool ⊕ Unit)

private def start : Lab := .inr (.inl false)
private def readTok : Lab := .inr (.inl true)
private def done : Lab := .inr (.inr ())

private def pc : program.Lab ⊕ Option Unit → Lab
  | .inl l => .inl (.inl l)
  | .inr _ => done

private noncomputable def src : program.Lab ⊕ Option Unit →
    TM2.Stmt (fun _ : Option K => Bool) (program.Lab ⊕ Option Unit) Bool
  | .inl l => program.prog Sum.inl Sum.inr l
  | .inr _ => .halt

private abbrev input : Stk := some (some .input)
private abbrev header : Stk := some (some .header)
private abbrev output : Stk := some (some .out)

-- Prepend a fixed token code to the input stack.
private def prepend (xs : List Bool) (q : TM2.Stmt alphabet Lab Bool) :=
  xs.foldl (fun q b => TM2.Stmt.push input (fun _ => b) q) q

private theorem prepend_step (xs : List Bool) (q : TM2.Stmt alphabet Lab Bool)
    (S : ∀ k, List (alphabet k))
    (v : Bool) : TM2.stepAux (prepend xs q) v S =
      TM2.stepAux q v (update S input (xs ++ S input)) := by
  induction xs generalizing q S with
  | nil => simp [prepend]
  | cons b bs ih =>
    change TM2.stepAux (prepend bs (.push input (fun _ => b) q)) v S = _
    rw [ih]; simp [TM2.stepAux]

private def dispatch (s : Sym) (q : TM2.Stmt alphabet Lab Bool) : TM2.Stmt alphabet Lab Bool :=
  .peek none (fun _ o => decide (o = some s)) <| .branch id
    (.pop none (fun _ _ => false) <|
      prepend (Tokens.bits s) (.push header (fun _ => false) (.goto fun _ => readTok))) q

private def symbols : List Sym :=
  [.cl, .bit true, .bit false, .lit true, .lit false, .val true, .val false, .dead]

private noncomputable def prog : Lab → TM2.Stmt alphabet Lab Bool
  | .inr (.inl false) => .push header (fun _ => true) (.goto fun _ => readTok)
  | .inr (.inl true) => symbols.foldr dispatch
      (.push header (fun _ => false) (.goto fun _ => pc (.inl program.start)))
  | .inl l => mapS emb pc (src l)
  | .inr (.inr ()) => .halt

private def layout (ts : List Sym) (x h : List Bool) : ∀ k, List (alphabet k)
  | none => ts
  | some k => workspace (st x h [] [] [] []) k

private theorem layout_eq (t : List Sym) (x h : List Bool) (S : ∀ k, List (alphabet k))
    (ht : S none = t) (hx : S input = x) (hh : S header = h)
    (h0 : ∀ k, k ≠ none → k ≠ input → k ≠ header → S k = []) : S = layout t x h := by
  funext k
  rcases k with _ | _ | k
  · exact ht
  · apply h0 <;> decide
  · cases k <;> first | exact hx | exact hh | apply h0 <;> decide

private theorem dispatch_step (s : Sym) (ss : List Sym) (q : TM2.Stmt alphabet Lab Bool)
    (ht : s ∈ ss) (t : List Sym) (x h : List Bool) (v : Bool) :
    TM2.stepAux (ss.foldr dispatch q) v (layout (s :: t) x h) =
      ⟨some readTok, false, layout t (Tokens.bits s ++ x) (false :: h)⟩ := by
  induction ss generalizing v with
  | nil => simp at ht
  | cons a ss ih =>
    by_cases ha : s = a
    · subst a
      simp only [List.foldr_cons, dispatch, TM2.stepAux, layout, List.head?_cons, decide_true,
        id_eq, Bool.cond_true, List.tail_cons, prepend_step]
      congr 1
      apply layout_eq <;> simp_all only [Bool.forall_bool, List.mem_cons, true_or, input, ne_eq,
        reduceCtorEq, not_false_eq_true, update_of_ne, layout, workspace, st, header,
        Option.some.injEq, update_self]
      intro k hk hk' hk''
      rcases k with _ | _ | k <;> simp_all
      cases k <;> simp_all
    · simpa [ha, dispatch, TM2.stepAux, layout] using
        ih (List.mem_cons.mp ht |>.resolve_left ha) false

private theorem walk (ts : List Sym) (x h : List Bool) (v : Bool) :
    ∃ w, Run prog (ts.length + 1) ⟨some readTok, v, layout ts x h⟩
      ⟨some (pc (.inl program.start)), w,
        layout [] (ts.reverse.flatMap Tokens.bits ++ x)
          (false :: List.replicate ts.length false ++ h)⟩ := by
  induction ts generalizing x h v with
  | nil =>
    refine ⟨false, Run.single ?_⟩
    simp only [readTok, prog, symbols, List.foldr_cons, List.foldr_nil,
      dispatch, TM2.stepAux, layout,
      List.head?_nil, reduceCtorEq, decide_false, id_eq, Bool.cond_false,
      List.reverse_nil, List.flatMap_nil, List.nil_append, List.length_nil, List.replicate_zero]
    congr 1; funext k
    rcases k with _ | _ | k <;> first | rfl | cases k <;> rfl
  | cons s ts ih =>
    have hmem : s ∈ symbols := by
      cases s with
      | bit b | lit b | val b => cases b <;> decide
      | _ => decide
    have r₁ := Run.single (M := prog) (l := readTok)
      (show TM2.stepAux (prog readTok) v (layout (s :: ts) x h) = _ from
        dispatch_step s _ _ hmem ts x h v)
    obtain ⟨w, r₂⟩ := ih (Tokens.bits s ++ x) (false :: h) false
    have hr : List.replicate (ts.length + 1) false ++ h =
      List.replicate ts.length false ++ false :: h := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    refine ⟨w, ?_⟩
    simpa [List.reverse_cons, List.append_assoc, hr] using (r₁.trans r₂).of_eq
      (show 1 + (ts.length + 1) = (s :: ts).length + 1 by simp; omega)

private theorem boundHead (φ : CNF) :
    (false :: List.replicate (toks φ).length false) ++ [true]
      = Computability.encodeNat (ceiling φ) := by
  rw [ceiling, ← Nat.pow_succ', Emit3.encodeNat_two_pow, List.replicate_succ]

private theorem prog_run (φ : CNF) (v : Bool) (S : ∀ k, List (alphabet k))
    (ht : S none = (toks φ).reverse) (h₀ : ∀ k, k ≠ none → S k = []) :
    ∃ w T, RunLe prog (workBound (toks φ).length + (toks φ).length + 2)
      ⟨some start, v, S⟩ ⟨some done, w, T⟩ ∧ T output = g φ := by
  have he : S = layout (toks φ).reverse [] [] :=
    layout_eq _ _ _ _ ht (h₀ _ (by decide)) (h₀ _ (by decide)) fun k hk _ _ => h₀ k hk
  subst S
  have r₁ : Run prog 1 ⟨some start, v, layout (toks φ).reverse [] []⟩
      ⟨some readTok, v, layout (toks φ).reverse [] [true]⟩ := by
    apply Run.single
    simp only [prog, start, TM2.stepAux]
    congr 1; funext k
    rcases k with _ | _ | k <;> first | rfl | cases k <;> rfl
  obtain ⟨w, r₂⟩ := walk (toks φ).reverse [] [true] v
  rw [List.reverse_reverse, Tokens.encoded, List.append_nil, List.length_reverse, boundHead] at r₂
  obtain ⟨U, hrun, hout⟩ := run φ
  obtain ⟨_ | a, V, v', h₃, he⟩ := hrun _ src Sum.inl Sum.inr (fun _ => rfl) w
  · cases he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  have embProg : Embeds emb pc src prog := by intro l; cases l <;> exact Or.inl rfl
  obtain ⟨T, r₃, ht, _⟩ := runLe_embed pc embProg h₃
    (S' := layout [] (bitEncode φ) (Computability.encodeNat (ceiling φ))) (by
      intro k; change _ = List.map id _; rw [List.map_id_fun]; rfl)
  refine ⟨v', T, (((r₁.trans r₂).le le_rfl).trans r₃).mono (by omega), ?_⟩
  have h := ht (some K.out)
  change T output = List.map id (V (some K.out)) at h
  simpa [hout] using h

private noncomputable def emitter : Emitter := by
  classical
  exact {
    K := Stk
    Γ := alphabet
    L := Lab
    prog := prog
    start := start
    done := done
    start_ne_done := by intro h; cases h
    prog_done := rfl
    cT := none
    cO := output
    cT_ne_cO := by simp [output]
    iT := Equiv.refl _
    eO := Equiv.refl _
    g := g
    noOut := []
    B := fun t => workBound t + t + 2
    B_mono := fun a b hab => by exact Nat.add_le_add_right (Nat.add_le_add (work_mono hab) hab) 2
    run := fun φ v S ht ho h0 => by
      obtain ⟨w, T, hr, hout⟩ := prog_run φ v S (by simpa using ht) (fun k hk => by
        by_cases he : k = output
        · subst k; exact ho
        · exact h0 k hk he)
      exact ⟨w, T, hr, by simpa using hout⟩ }

def reduce (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => g φ
  | none => []

noncomputable section

theorem time_reduce : ComplexityTheory.IsPolyTime reduce := by
  classical
  let n : Polynomial Nat := 12 * (Polynomial.X + 1)
  let b := n + n * (Polynomial.C step.C * (n + 1))
  let W := (n + 1) * (Polynomial.C step.C * (b + 1))
  let : Fintype emitter.K := inferInstanceAs (Fintype Stk)
  let (k : emitter.K) : Fintype (emitter.Γ k) := finAlphabet k
  let : Fintype emitter.L := inferInstanceAs (Fintype Lab)
  exact TokThen.isPolyTime_out emitter Finset.univ.toList (Finset.nodup_toList _) (by simp)
    (W + 3 * Polynomial.X + 5) (fun t => by
      change 2 * t + 3 + (workBound t + t + 2) ≤ _
      simp only [W, b, n, workBound, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      omega)

end

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Output

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat

open Cslib.CookLevin Cslib.Complexity.Karp BitstringEncoding
open Cslib.Logic.LegacyPL

private theorem reduce_correct (x : List Bool) :
    sat3Dec x = monotoneThreeSatDec (Output.reduce x) := by
  classical
  unfold Output.reduce
  cases hd : decodeCNF x with
  | none =>
    have h : ¬ ∃ φ, encodeCNF φ = x ∧ is3 φ = true ∧ CNFSat φ := by
      rintro ⟨φ, rfl, _⟩
      simp at hd
    simp [sat3Dec, h]
    rfl
  | some φ =>
    rw [decodeCNF_eq_some_iff] at hd
    subst x
    rw [formula_correct]
    unfold Output.g
    by_cases hs : φ.all Output.short
    · simp [hs]
    · have hw : ¬ WellFormed (monoInstance φ) := by
        intro hw
        apply hs
        apply List.all_eq_true.mpr
        intro c hc
        obtain ⟨hn, hl⟩ := (well_monoInstance φ).mp hw c hc
        simp [Output.short, hn, hl]
      simp [hs, monotoneThreeSatDec, bitDecode_bitEncode, hw]
      rfl

/-- **MONOTONE 3-SAT is NP-complete.** The decision problem MONOTONE 3-SAT belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to MONOTONE 3-SAT.

Source: T. J. Schaefer, "The complexity of
satisfiability problems", Proceedings of the Tenth Annual ACM Symposium on Theory of
Computing (STOC 1978), ACM, 1978, 216-226 (dichotomy theorem). -/
public theorem monotoneThreeSat_npComplete :
    monotoneThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monotoneThreeSatDec := by
  refine ⟨membership, ?_⟩
  intro L hL
  exact (sat3Dec_npHard L hL).trans ⟨Output.reduce, Output.time_reduce, reduce_correct⟩

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat
