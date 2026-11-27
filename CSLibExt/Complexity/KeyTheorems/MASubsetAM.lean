/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MA is contained in AM

Source:
L. Babai, "Trading group theory for randomness", Proceedings of the Seventeenth
Annual ACM Symposium on Theory of Computing (STOC 1985), 421-429; S. Arora and
B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 8.2
(MA ⊆ AM).
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.CookLevin.Precompute
import CSLibExt.Computability.Complexity.Host
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card.Arithmetic

/-!
# MA is contained in AM

Every Merlin-Arthur language is in `AM`: Merlin's message may as well be sent
after Arthur's coins. The same verifier does not work, since
in `AM` Merlin chooses the witness after seeing the coins, so the soundness
argument needs error amplification first (drive the per-witness soundness error
far below `2 ^ -(witness length)`) and then a union bound over all of Merlin's
possible messages. Both the amplification (a new verifier over concatenated
random strings, needing an `IsPolyTime` witness) and the counting union bound
are beyond a definitional unfolding.
-/

open scoped BigOperators

namespace MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM

open Turing Function TM2Program BitstringEncoding ComplexityTheory

private abbrev Verifier := List Bool × List Bool × List Bool → Bool

private def coinBlock : ℕ → List Bool → List Bool
  | 0, _ => []
  | m + 1, r => r.headD false :: coinBlock m r.tail

private theorem length_coinBlock (m : ℕ) (r : List Bool) :
    (coinBlock m r).length = m := by
  induction m generalizing r <;> simp [coinBlock, *]

private theorem coinBlock_append {m : ℕ} (l r : List Bool) (h : l.length = m) :
    coinBlock m (l ++ r) = l := by
  induction l generalizing m with
  | nil => subst m; rfl
  | cons b l ih =>
    cases m with
    | zero => simp at h
    | succ m => simpa [coinBlock] using congrArg (b :: ·) (ih (by simpa using h))

private def results (R : Verifier) (x w : List Bool) (m : ℕ) :
    ℕ → List Bool → List Bool
  | 0, _ => []
  | k + 1, r =>
    R (x, w, (coinBlock m r).reverse) :: results R x w m k (r.drop m)

private def expanded (p k : Polynomial ℕ) (R : Verifier)
    (v : List Bool × List Bool × List Bool) : Bool :=
  let outcomes := results R v.1 v.2.2 (p.eval v.1.length) (k.eval v.1.length) v.2.1
  decide (outcomes.count false < outcomes.count true)

private def coinEncoding (r : List Bool) : List Bool :=
  r.flatMap fun b => [true, b, false]

private theorem encode_bits (r : List Bool) : bitEncode r = coinEncoding r := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    change [true, b, false] ++ bitEncode r = _
    simp [coinEncoding, ih]

private def trialPrefix (x w : List Bool) : List Bool :=
  delimit (coinEncoding x) ++ delimit (coinEncoding w)

private theorem encoding_trial (x w r : List Bool) :
    bitEncode (x, w, r) = trialPrefix x w ++ coinEncoding r := by
  change delimit (bitEncode x) ++ (delimit (bitEncode w) ++ bitEncode r) = _
  rw [encode_bits, encode_bits, encode_bits, trialPrefix, List.append_assoc]

private def workEncoding (p k : Polynomial ℕ) (v : List Bool × List Bool × List Bool) :
    List (Option Bool) :=
  List.replicate (p.eval v.1.length) (some true) ++ [none] ++
    List.replicate (k.eval v.1.length) (some true) ++ [none] ++
    (trialPrefix v.1 v.2.2).map some ++ [none] ++ v.2.1.reverse.map some ++ [none]

/-! ### Running the verifier on successive coin blocks -/

namespace Repetition

private inductive Work
  | inp | out | width | widthUsed | trials | trialPrefix | prefixUsed | coins | yes | no
  deriving DecidableEq

private instance workFintype : Fintype Work where
  elems := ⟨↑[Work.inp, .out, .width, .widthUsed, .trials, .trialPrefix, .prefixUsed, .coins,
    .yes, .no], by decide⟩
  complete k := by cases k <;> decide

private inductive Control
  | readWidth | readTrials | readPrefix | readCoins
  | nextTrial | sample | restoreWidth | copyPrefix | restorePrefix | count
  | compare | clean (answer : Bool) | done (answer : Bool)
  deriving DecidableEq

private instance controlFintype : Fintype Control where
  elems := ⟨↑[Control.readWidth, .readTrials, .readPrefix, .readCoins, .nextTrial, .sample,
    .restoreWidth, .copyPrefix, .restorePrefix, .count, .compare, .clean false, .clean true,
    .done false, .done true], by decide⟩
  complete l := by cases l <;> first | decide | rename_i b; cases b <;> decide

variable {R : Verifier}
variable (V : TM2ComputableInPolyTime bitEncode bitEncode R)

private abbrev Key := Work ⊕ V.tm.K
private abbrev Label := Control ⊕ V.tm.Λ
private abbrev State := Option Bool × V.tm.σ

private abbrev Alphabet : Key V → Type
  | .inl .inp => Option Bool
  | .inl _ => Bool
  | .inr k => V.tm.Γ k

private abbrev Stacks := (k : Key V) → List (Alphabet V k)

private abbrev jump (l : Control) : TM2.Stmt (Alphabet V) (Label V) (State V) :=
  .load (fun s => (none, s.2)) (.goto fun _ => .inl l)

private def lift : TM2.Stmt V.tm.Γ V.tm.Λ V.tm.σ →
    TM2.Stmt (Alphabet V) (Label V) (State V)
  | .push k f q => .push (.inr k) (fun s => f s.2) (lift q)
  | .pop k f q => .pop (.inr k) (fun s o => (s.1, f s.2 o)) (lift q)
  | .peek k f q => .peek (.inr k) (fun s o => (s.1, f s.2 o)) (lift q)
  | .load f q => .load (fun s => (s.1, f s.2)) (lift q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2) (lift q₁) (lift q₂)
  | .goto f => .goto fun s => .inr (f s.2)
  | .halt => .goto fun _ => .inl .count

private abbrev readField (dst : Key V) (encode : Bool → Alphabet V dst)
    (self next : Control) : TM2.Stmt (Alphabet V) (Label V) (State V) :=
  .pop (.inl .inp) (fun s o => (o.join, s.2)) <|
    .branch (fun s => s.1.isSome)
      (.push dst (fun s => encode (s.1.getD false)) (jump V self))
      (jump V next)

private abbrev move (a b : Key V) (decode : Alphabet V a → Bool) (encode : Bool → Alphabet V b)
    (self next : Control) : TM2.Stmt (Alphabet V) (Label V) (State V) :=
  .pop a (fun s o => (o.map decode, s.2)) <|
    .branch (fun s => s.1.isSome)
      (.push b (fun s => encode (s.1.getD false)) (jump V self))
      (jump V next)

private abbrev putBit (b : Bool) : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm b

private abbrev flag : Flag (State V) where
  tag b := (some b, V.tm.initialState)
  untag s := s.1.getD false
  untag_tag _ := rfl

private abbrev discard : List (Key V) :=
  [.inl .width, .inl .trialPrefix, .inl .coins, .inl .yes, .inl .no]

private def program : Label V → TM2.Stmt (Alphabet V) (Label V) (State V)
  | .inr l => lift V (V.tm.m l)
  | .inl .readWidth => readField V (.inl .width) id .readWidth .readTrials
  | .inl .readTrials => readField V (.inl .trials) id .readTrials .readPrefix
  | .inl .readPrefix => readField V (.inl .trialPrefix) id .readPrefix .readCoins
  | .inl .readCoins => readField V (.inl .coins) id .readCoins .nextTrial
  | .inl .nextTrial => .pop (.inl .trials) (fun s o => (some o.isSome, s.2)) <|
      .branch (fun s => s.1.getD false) (jump V .sample) (jump V .compare)
  | .inl .sample => .pop (.inl .width) (fun s o => (some o.isSome, s.2)) <|
      .branch (fun s => s.1.getD false)
        (.push (.inl .widthUsed) (fun _ => true) <|
          .pop (.inl .coins) (fun s o => (o, s.2)) <|
          .push (.inr V.tm.k₀) (fun _ => putBit V false) <|
          .push (.inr V.tm.k₀) (fun s => putBit V (s.1.getD false)) <|
          .push (.inr V.tm.k₀) (fun _ => putBit V true) (jump V .sample))
        (jump V .restoreWidth)
  | .inl .restoreWidth =>
    move V (.inl .widthUsed) (.inl .width) id id .restoreWidth .copyPrefix
  | .inl .copyPrefix => .pop (.inl .trialPrefix) (fun s o => (o, s.2)) <|
      .branch (fun s => s.1.isSome)
        (.push (.inl .prefixUsed) (fun s => s.1.getD false) <|
          .push (.inr V.tm.k₀) (fun s => putBit V (s.1.getD false)) (jump V .copyPrefix))
        (jump V .restorePrefix)
  | .inl .restorePrefix =>
    .pop (.inl .prefixUsed) (fun s o => (o, s.2)) <|
      .branch (fun s => s.1.isSome)
        (.push (.inl .trialPrefix) (fun s => s.1.getD false) (jump V .restorePrefix))
        (.goto fun _ => .inr V.tm.main)
  | .inl .count => .pop (.inr V.tm.k₁) (fun s o => (o.map V.outputAlphabet, s.2)) <|
      .branch (fun s => s.1.getD false)
        (.push (.inl .yes) (fun _ => true) (jump V .nextTrial))
        (.push (.inl .no) (fun _ => true) (jump V .nextTrial))
  | .inl .compare => .pop (.inl .yes) (fun s o => (some o.isSome, s.2)) <|
      .branch (fun s => s.1.getD false)
        (.pop (.inl .no) (fun s o => (some o.isSome, s.2)) <|
          .branch (fun s => s.1.getD false) (jump V .compare) (jump V (.clean true)))
        (jump V (.clean false))
  | .inl (.clean answer) =>
    letI := flag V
    cleanS (discard V) (.inl (.clean answer)) (.inl (.done answer))
  | .inl (.done answer) =>
    .push (.inl .out) (fun _ => answer) (.load (fun s => (none, s.2)) .halt)

private noncomputable abbrev tm : FinTM2 where
  K := Key V
  kFin := letI := V.tm.kFin; inferInstanceAs (Fintype (Work ⊕ V.tm.K))
  ΛFin := letI := V.tm.ΛFin; inferInstanceAs (Fintype (Control ⊕ V.tm.Λ))
  σFin := letI := V.tm.σFin; inferInstanceAs (Fintype (Option Bool × V.tm.σ))
  Γ := Alphabet V
  k₀ := .inl .inp
  k₁ := .inl .out
  Λ := Label V
  σ := State V
  main := .inl .readWidth
  initialState := (none, V.tm.initialState)
  m := program V
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))

private def cfg (l : Label V) (S : Stacks V) : TM2.Cfg (Alphabet V) (Label V) (State V) :=
  ⟨some l, (none, V.tm.initialState), S⟩

private def hostCfg (l : Control) (S : Stacks V) := cfg V (.inl l) S

private def stackContents (base : (k : Work) → List (Alphabet V (.inl k)))
    (sub : (k : V.tm.K) → List (V.tm.Γ k)) : Stacks V
  | .inl k => base k
  | .inr k => sub k

private theorem update_left (base : (k : Work) → List (Alphabet V (.inl k)))
    (sub : (k : V.tm.K) → List (V.tm.Γ k)) (k : Work)
    (l : List (Alphabet V (.inl k))) :
    update (stackContents V base sub) (.inl k) l = stackContents V (update base k l) sub := by
  funext j
  rcases j with j | j
  · by_cases e : j = k <;> simp [e, stackContents, update_of_ne]
  · simp [stackContents]

private theorem update_right (base : (k : Work) → List (Alphabet V (.inl k)))
    (sub : (k : V.tm.K) → List (V.tm.Γ k)) (k : V.tm.K) (l : List (V.tm.Γ k)) :
    update (stackContents V base sub) (.inr k) l = stackContents V base (update sub k l) := by
  funext j
  rcases j with j | j
  · simp [stackContents]
  · by_cases e : j = k <;> simp [e, stackContents, update_of_ne]

private def labelOf : Option V.tm.Λ → Label V
  | none => .inl .count
  | some l => .inr l

private def embed (base : (k : Work) → List (Alphabet V (.inl k))) (c : V.tm.Cfg) :
    TM2.Cfg (Alphabet V) (Label V) (State V) :=
  ⟨some (labelOf V c.l), (none, c.var), stackContents V base c.stk⟩

private theorem stepAux_lift (q : TM2.Stmt V.tm.Γ V.tm.Λ V.tm.σ)
    (v : V.tm.σ) (s : (k : V.tm.K) → List (V.tm.Γ k))
    (base : (k : Work) → List (Alphabet V (.inl k))) :
    TM2.stepAux (lift V q) (none, v) (stackContents V base s) =
      embed V base (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih => simp [lift, TM2.stepAux, stackContents, update_right, ih]
  | pop k f q ih => simp [lift, TM2.stepAux, stackContents, update_right, ih]
  | peek k f q ih => simp [lift, TM2.stepAux, stackContents, ih]
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ => cases h : f v <;> simp [lift, TM2.stepAux, h, ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

private theorem verifier_run
    (base : (k : Work) → List (Alphabet V (.inl k))) (x w r : List Bool) :
    RunLe (program V) (V.time.eval ((bitEncode (x, w, r)).length))
      (embed V base (initList V.tm ((bitEncode (x, w, r)).map V.inputAlphabet.symm)))
      (embed V base (haltList V.tm ((bitEncode (R (x, w, r))).map V.outputAlphabet.symm))) := by
  obtain ⟨⟨time, run⟩, bound⟩ := V.outputsFun (x, w, r)
  refine ⟨time, bound, ?_⟩
  have sim (a b : V.tm.Cfg) (h : TM2.step V.tm.m a = some b) :
      TM2.step (program V) (embed V base a) = some (embed V base b) := by
    rcases a with ⟨_ | l, v, s⟩
    · cases h
    · change some (TM2.stepAux _ _ _) = some b at h
      cases h
      exact congrArg some (stepAux_lift V (V.tm.m l) v s base)
  unfold Run at *
  exact TM2Composition.iter_sim (embed V base) sim time _ _ run

private theorem readField_run (target : Key V) (hne : (.inl .inp : Key V) ≠ target)
    (enc : Bool → Alphabet V target) (self exit : Control)
    (hp : program V (.inl self) = readField V target enc self exit)
    (l : List Bool) (rest : List (Option Bool)) (S : Stacks V)
    (hS : S (.inl .inp) = l.map some ++ none :: rest) :
    Run (program V) (l.length + 1) (hostCfg V self S)
      (hostCfg V exit (update (update S (.inl .inp) rest) target
        ((l.map enc).reverse ++ S target))) := by
  induction l generalizing S with
  | nil =>
    have htail : S (.inl .inp) = none :: rest := by simpa using hS
    apply Run.single
    have he : update (update S (.inl .inp) rest) target (S target) =
        update S (.inl .inp) rest := by
      rw [← update_of_ne hne.symm (f := S) (v := rest), Function.update_eq_self]
    simp [hostCfg, cfg, hp, readField, TM2.stepAux, htail, jump, he]
  | cons b l ih =>
    let T := update (update S (.inl .inp) (l.map some ++ none :: rest)) target (enc b :: S target)
    have ht : T (.inl .inp) = l.map some ++ none :: rest := by
      simp [T, update_of_ne hne]
    have hs : Run (program V) 1 (hostCfg V self S) (hostCfg V self T) := by
      apply Run.single
      simp [hostCfg, cfg, hp, readField, TM2.stepAux, hS, jump, T, update_of_ne hne.symm]
    have hr := hs.trans (ih T ht)
    have he : update (update T (.inl .inp) rest) target ((l.map enc).reverse ++ T target) =
        update (update S (.inl .inp) rest) target (((b :: l).map enc).reverse ++ S target) := by
      unfold T
      rw [update_comm hne.symm]
      simp [List.append_assoc]
    rw [he] at hr
    exact hr.of_eq (by simp; omega)

-- A trial consumes exactly its allotted bits. An undersized input is padded with zeros.
private theorem sample_run (m u : ℕ) (r : List Bool) (S : Stacks V)
    (hm : S (.inl .width) = List.replicate m true)
    (hu : S (.inl .widthUsed) = List.replicate u true)
    (hr : S (.inl .coins) = r) :
    Run (program V) (m + 1) (hostCfg V .sample S)
      (hostCfg V .restoreWidth
        (update (update (update (update S (.inl .width) []) (.inl .widthUsed)
          (List.replicate (m + u) true)) (.inl .coins) (r.drop m)) (.inr V.tm.k₀)
          ((coinEncoding (coinBlock m r).reverse).map (putBit V) ++ S (.inr V.tm.k₀)))) := by
  induction m generalizing u r S with
  | zero =>
    have he : update S (.inl .width) [] = S := by
      rw [← List.replicate_zero (a := true), ← hm, Function.update_eq_self]
    have he' : update (update S (.inl .widthUsed) (List.replicate u true)) (.inl .coins) r =
        S := by rw [← hu, Function.update_eq_self, ← hr, Function.update_eq_self]
    have hstep : Run (program V) 1 (hostCfg V .sample S) (hostCfg V .restoreWidth S) :=
      Run.single (by simp [hostCfg, cfg, program, TM2.stepAux, hm, jump, he])
    simpa [coinBlock, coinEncoding, he, he'] using hstep
  | succ m ih =>
    let T := update (update (update (update S (.inl .width) (List.replicate m true))
      (.inl .widthUsed) (List.replicate (u + 1) true)) (.inl .coins) r.tail)
        (.inr V.tm.k₀) ([true, r.headD false, false].map (putBit V) ++ S (.inr V.tm.k₀))
    have hs : Run (program V) 1 (hostCfg V .sample S) (hostCfg V .sample T) := by
      apply Run.single
      cases r <;> simp [hostCfg, cfg, program, TM2.stepAux, hm, hu, hr, jump, T,
        List.replicate_succ, update_of_ne]
    have hT := ih (u + 1) r.tail T
      (by simp [T, update_of_ne]) (by simp [T, update_of_ne]) (by simp [T, update_of_ne])
    have hdrop : r.tail.drop m = r.drop (m + 1) := by cases r <;> simp
    have hcount : m + (u + 1) = m + 1 + u := by omega
    have he : coinEncoding (coinBlock (m + 1) r).reverse =
        coinEncoding (coinBlock m r.tail).reverse ++ [true, r.headD false, false] := by
      simp [coinBlock, coinEncoding]
    have eq :
        update (update (update (update T (.inl .width) []) (.inl .widthUsed)
          (List.replicate (m + (u + 1)) true)) (.inl .coins) (r.tail.drop m)) (.inr V.tm.k₀)
          ((coinEncoding (coinBlock m r.tail).reverse).map (putBit V) ++ T (.inr V.tm.k₀)) =
        update (update (update (update S (.inl .width) []) (.inl .widthUsed)
          (List.replicate (m + 1 + u) true)) (.inl .coins) (r.drop (m + 1))) (.inr V.tm.k₀)
          ((coinEncoding (coinBlock (m + 1) r).reverse).map (putBit V) ++ S (.inr V.tm.k₀)) := by
      funext j
      rcases j with j | j
      · cases j <;> simp [T, hdrop, hcount, update_of_ne]
      · by_cases hj : j = V.tm.k₀
        · subst j; simp [T, he, List.append_assoc]
        · simp [T, update_of_ne, hj]
    rw [eq] at hT
    exact (hs.trans hT).of_eq (by omega)

private theorem move_run (a b : Key V) (hne : a ≠ b) (dec : Alphabet V a → Bool)
    (enc : Bool → Alphabet V b) (self exit : Control)
    (hp : program V (.inl self) = move V a b dec enc self exit)
    (l : List (Alphabet V a)) (S : Stacks V) (hS : S a = l) :
    Run (program V) (l.length + 1) (hostCfg V self S)
      (hostCfg V exit (update (update S a []) b ((l.map (enc ∘ dec)).reverse ++ S b))) := by
  induction l generalizing S with
  | nil =>
    have ha : update S a [] = S := by rw [← hS, Function.update_eq_self]
    exact Run.single (by simp [hostCfg, cfg, hp, move, TM2.stepAux, hS, jump, ha])
  | cons x xs ih =>
    let T := update (update S a xs) b (enc (dec x) :: S b)
    have ht : T a = xs := by simp [T, update_of_ne hne]
    have hs : Run (program V) 1 (hostCfg V self S) (hostCfg V self T) :=
      Run.single (by simp [hostCfg, cfg, hp, move, TM2.stepAux, hS, jump, T, update_of_ne hne.symm])
    have hr := hs.trans (ih T ht)
    have he : update (update T a []) b ((xs.map (enc ∘ dec)).reverse ++ T b) =
        update (update S a []) b ((((x :: xs).map (enc ∘ dec)).reverse) ++ S b) := by
      unfold T
      rw [update_comm hne.symm]
      simp [List.append_assoc]
    rw [he] at hr
    exact hr.of_eq (by simp; omega)

private theorem copyPrefix_run (pre : List Bool) (S : Stacks V)
    (hS : S (.inl .trialPrefix) = pre) :
    Run (program V) (pre.length + 1) (hostCfg V .copyPrefix S)
      (hostCfg V .restorePrefix
        (update (update (update S (.inl .trialPrefix) []) (.inl .prefixUsed)
          (pre.reverse ++ S (.inl .prefixUsed))) (.inr V.tm.k₀)
          (pre.reverse.map (putBit V) ++ S (.inr V.tm.k₀)))) := by
  induction pre generalizing S with
  | nil =>
    have h : update S (.inl .trialPrefix) [] = S := by rw [← hS, Function.update_eq_self]
    exact Run.single (by simp [hostCfg, cfg, program, TM2.stepAux, hS, jump, h])
  | cons b pre ih =>
    let T := update (update (update S (.inl .trialPrefix) pre) (.inl .prefixUsed)
      (b :: S (.inl .prefixUsed))) (.inr V.tm.k₀) (putBit V b :: S (.inr V.tm.k₀))
    have hs : Run (program V) 1 (hostCfg V .copyPrefix S) (hostCfg V .copyPrefix T) :=
      Run.single (by simp [hostCfg, cfg, program, TM2.stepAux, hS, jump, T, update_of_ne])
    have hr := hs.trans (ih T (by simp [T, update_of_ne]))
    have he : update (update (update T (.inl .trialPrefix) []) (.inl .prefixUsed)
          (pre.reverse ++ T (.inl .prefixUsed))) (.inr V.tm.k₀)
          (pre.reverse.map (putBit V) ++ T (.inr V.tm.k₀)) =
        update (update (update S (.inl .trialPrefix) []) (.inl .prefixUsed)
          ((b :: pre).reverse ++ S (.inl .prefixUsed))) (.inr V.tm.k₀)
          ((b :: pre).reverse.map (putBit V) ++ S (.inr V.tm.k₀)) := by
      funext j
      rcases j with j | j
      · cases j <;> simp [T, List.append_assoc, update_of_ne]
      · by_cases hj : j = V.tm.k₀
        · subst j; simp [T, List.append_assoc]
        · simp [T, update_of_ne, hj]
    rw [he] at hr
    exact hr.of_eq (by simp; omega)

private theorem restorePrefix_run (pre : List Bool) (S : Stacks V)
    (hS : S (.inl .prefixUsed) = pre) :
    Run (program V) (pre.length + 1) (hostCfg V .restorePrefix S)
      (cfg V (.inr V.tm.main)
        (update (update S (.inl .prefixUsed) []) (.inl .trialPrefix)
          (pre.reverse ++ S (.inl .trialPrefix)))) := by
  induction pre generalizing S with
  | nil =>
    have h : update S (.inl .prefixUsed) [] = S := by rw [← hS, Function.update_eq_self]
    exact Run.single (by simp [cfg, program, TM2.stepAux, hS, h])
  | cons b pre ih =>
    let T := update (update S (.inl .prefixUsed) pre) (.inl .trialPrefix)
      (b :: S (.inl .trialPrefix))
    have hs : Run (program V) 1 (hostCfg V .restorePrefix S) (hostCfg V .restorePrefix T) :=
      Run.single (by simp [hostCfg, cfg, program, TM2.stepAux, hS, jump, T, update_of_ne])
    have hr := hs.trans (ih T (by simp [T, update_of_ne]))
    have he : update (update T (.inl .prefixUsed) []) (.inl .trialPrefix)
          (pre.reverse ++ T (.inl .trialPrefix)) =
        update (update S (.inl .prefixUsed) []) (.inl .trialPrefix)
          ((b :: pre).reverse ++ S (.inl .trialPrefix)) := by
      funext j
      rcases j with j | j
      · cases j <;> simp [T, List.append_assoc, update_of_ne]
      · simp [T, update_of_ne]
    rw [he] at hr
    exact hr.of_eq (by simp; omega)

private def board (m k : ℕ) (pre r : List Bool) (y n : ℕ) :
    (i : Work) → List (Alphabet V (.inl i))
  | .width => List.replicate m true
  | .trials => List.replicate k true
  | .trialPrefix => pre.reverse
  | .coins => r
  | .yes => List.replicate y true
  | .no => List.replicate n true
  | _ => []

private abbrev setInput (bits : List Bool) :=
  update (fun _ => []) V.tm.k₀ (bits.map (putBit V))

private abbrev setOutput (b : Bool) :=
  update (fun _ => []) V.tm.k₁ [V.outputAlphabet.symm b]

private theorem coinEncoding_length (r : List Bool) : (coinEncoding r).length = 3 * r.length := by
  induction r with
  | nil => rfl
  | cons b r ih => simp [coinEncoding] at ih ⊢; omega

private def trialBudget (m l : ℕ) :=
  V.time.eval (l + 3 * m) + 2 * m + 2 * l + 6

private theorem trial_run (x w r : List Bool) (m k y n : ℕ) :
    let pre := trialPrefix x w
    let b := R (x, w, (coinBlock m r).reverse)
    RunLe (program V) (trialBudget V m pre.length)
      (hostCfg V .nextTrial (stackContents V (board V m (k + 1) pre r y n) (fun _ => [])))
      (hostCfg V .nextTrial (stackContents V (board V m k pre (r.drop m)
        (y + if b then 1 else 0) (n + if b then 0 else 1)) (fun _ => []))) := by
  intro pre b
  let r₀ := (coinBlock m r).reverse
  let B := board V m k pre (r.drop m) y n
  let h := board V m k pre r y n
  let S := stackContents V h (fun _ => [])
  have h₀ : Run (program V) 1
      (hostCfg V .nextTrial (stackContents V (board V m (k + 1) pre r y n) (fun _ => [])))
      (hostCfg V .sample S) := by
    apply Run.single
    simp only [program, TM2.stepAux, stackContents, board, List.replicate_succ,
      List.head?_cons, Option.isSome_some, Option.getD_some, Bool.cond_true, List.tail_cons, jump,
      update_left]
    congr 1
    funext j
    rcases j with j | j
    · cases j <;> rfl
    · rfl
  let W := update (board V 0 k pre (r.drop m) y n) .widthUsed (List.replicate m true)
  have h₁ := sample_run V m 0 r S rfl rfl rfl
  have e₁ : update (update (update (update S (.inl .width) []) (.inl .widthUsed)
      (List.replicate (m + 0) true)) (.inl .coins) (r.drop m)) (.inr V.tm.k₀)
      ((coinEncoding r₀).map (putBit V) ++ S (.inr V.tm.k₀)) =
      stackContents V W (setInput V (coinEncoding r₀)) := by
    funext j
    rcases j with j | j
    · cases j <;> simp [W, S, h, board, stackContents, update_of_ne]
    · by_cases e : j = V.tm.k₀ <;> simp [S, stackContents, r₀, update_of_ne, e]
  rw [e₁] at h₁
  have h₂ := move_run V (.inl .widthUsed) (.inl .width) (by simp) id id
    .restoreWidth .copyPrefix rfl (List.replicate m true)
    (stackContents V W (setInput V (coinEncoding r₀))) (by simp [W, stackContents])
  have e₂ : update (update (stackContents V W (setInput V (coinEncoding r₀))) (.inl .widthUsed)
        []) (.inl .width) ((List.replicate m true).map (id ∘ id) |>.reverse) =
      stackContents V B (setInput V (coinEncoding r₀)) := by
    funext j
    rcases j with j | j
    · cases j <;> simp [W, B, board, stackContents, update_of_ne]
    · simp [stackContents, update_of_ne]
  simp only [show (stackContents V W (setInput V (coinEncoding r₀))) (.inl .width) = [] by rfl,
    List.append_nil, e₂, List.length_replicate] at h₂
  let C := update (board V m k [] (r.drop m) y n) .prefixUsed pre
  have h₃ := copyPrefix_run V pre.reverse (stackContents V B (setInput V (coinEncoding r₀))) rfl
  let S₂ := stackContents V B (setInput V (coinEncoding r₀))
  have e₃ : update (update (update S₂ (.inl .trialPrefix) []) (.inl .prefixUsed)
      (pre.reverse.reverse ++ S₂ (.inl .prefixUsed))) (.inr V.tm.k₀)
      (pre.reverse.reverse.map (putBit V) ++ S₂ (.inr V.tm.k₀)) =
      stackContents V C (setInput V (pre ++ coinEncoding r₀)) := by
    funext j
    rcases j with j | j
    · cases j <;> simp [C, B, S₂, board, stackContents, update_of_ne]
    · by_cases e : j = V.tm.k₀ <;> simp [S₂, stackContents, setInput, update_of_ne, e]
  rw [e₃, List.length_reverse] at h₃
  have h₄ := restorePrefix_run V pre
    (stackContents V C (setInput V (pre ++ coinEncoding r₀))) (by simp [C, stackContents])
  let S₃ := stackContents V C (setInput V (pre ++ coinEncoding r₀))
  have e₄ : update (update S₃ (.inl .prefixUsed) []) (.inl .trialPrefix)
      (pre.reverse ++ S₃ (.inl .trialPrefix)) =
      stackContents V B (setInput V (pre ++ coinEncoding r₀)) := by
    funext j
    rcases j with j | j
    · cases j <;> simp [S₃, C, B, board, stackContents, update_of_ne]
    · simp [S₃, stackContents, update_of_ne]
  rw [e₄] at h₄
  have h₅ := verifier_run V B x w r₀
  rw [encoding_trial] at h₅
  simp only [embed, Cslib.Complexity.Host.initList_eq, Cslib.Complexity.Host.haltList_eq,
    labelOf, List.length_append, coinEncoding_length, List.length_reverse, length_coinBlock,
    r₀] at h₅
  have h₆ : Run (program V) 1 (hostCfg V .count (stackContents V B (setOutput V b)))
      (hostCfg V .nextTrial (stackContents V (board V m k pre (r.drop m)
        (y + if b then 1 else 0) (n + if b then 0 else 1)) (fun _ => []))) := by
    apply Run.single
    cases hb : b <;>
      simp only [program, TM2.stepAux, update_right, update_left, stackContents, update_self,
        List.head?_cons, Option.map_some, Equiv.apply_symm_apply, Option.getD_some, List.tail_cons,
        Bool.cond_true, Bool.cond_false, jump, Function.update_idem, Function.update_eq_self,
        B, board, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] <;>
      congr 1 <;>
      funext j <;>
      rcases j with j | j
    all_goals first | rfl | (cases j <;> rfl)
  change RunLe (program V) (V.time.eval (pre.length + 3 * m))
    (cfg V (.inr V.tm.main) (stackContents V B (setInput V (pre ++ coinEncoding r₀))))
    (hostCfg V .count (stackContents V B (setOutput V b))) at h₅
  exact (((((h₀.trans h₁).trans h₂).trans h₃).trans h₄).le le_rfl |>.trans h₅ |>.trans
    (h₆.le le_rfl)).mono (by unfold trialBudget; omega)

private theorem compare_run (m : ℕ) (pre r : List Bool) (y n : ℕ) :
    ∃ y' ≤ y, ∃ n' ≤ n,
      RunLe (program V) (y + 1)
        (hostCfg V .compare (stackContents V (board V m 0 pre r y n) (fun _ => [])))
        (hostCfg V (.clean (decide (n < y)))
          (stackContents V (board V m 0 pre r y' n') (fun _ => []))) := by
  induction y generalizing n with
  | zero =>
    refine ⟨0, le_rfl, n, le_rfl, (Run.single ?_).le le_rfl⟩
    have eh : update (board V m 0 pre r 0 n) .yes [] =
        board V m 0 pre r 0 n := by
      exact Function.update_eq_self _ _
    simp [hostCfg, cfg, program, TM2.stepAux, board, stackContents, jump, update_left, eh]
  | succ y ih =>
    cases n with
    | zero =>
      refine ⟨y, by omega, 0, le_rfl, (Run.single ?_).le (by omega)⟩
      simp only [program, TM2.stepAux, board, stackContents, List.replicate_succ, List.head?_cons,
        Option.isSome_some, Option.getD_some, Bool.cond_true, List.tail_cons, update_left,
        update_of_ne (show Work.no ≠ Work.yes by decide), List.replicate_zero, List.head?_nil,
        Option.isSome_none, Bool.cond_false, List.tail_nil, jump, Nat.zero_lt_succ, decide_true]
      congr 1
      funext j
      rcases j with j | j
      · cases j <;> rfl
      · rfl
    | succ n =>
      obtain ⟨y', hy, n', hn, run⟩ := ih n
      refine ⟨y', by omega, n', by omega, (?_ : Run _ 1 _ _).le le_rfl |>.trans run |>.mono
        (by omega)⟩
      · exact Run.single (by
          simp only [program, TM2.stepAux, board, stackContents, List.replicate_succ,
            List.head?_cons, Option.isSome_some, Option.getD_some, Bool.cond_true, List.tail_cons,
            update_left, update_of_ne (show Work.no ≠ Work.yes by decide), jump]
          congr 1
          funext j
          rcases j with j | j
          · cases j <;> rfl
          · rfl)

private theorem results_length (x w r : List Bool) (m k : ℕ) :
    (results R x w m k r).length = k := by
  induction k generalizing r <;> simp [results, *]

private theorem trials_run (x w r : List Bool) (m k y n : ℕ) :
    let pre := trialPrefix x w
    let outcomes := results R x w m k r
    RunLe (program V) (k * trialBudget V m pre.length + 1)
      (hostCfg V .nextTrial (stackContents V (board V m k pre r y n) (fun _ => [])))
      (hostCfg V .compare (stackContents V (board V m 0 pre (r.drop (m * k))
        (y + outcomes.count true) (n + outcomes.count false)) (fun _ => []))) := by
  intro pre outcomes
  induction k generalizing r y n with
  | zero =>
    simp only [outcomes, results, List.count_nil, Nat.add_zero, Nat.mul_zero, List.drop_zero,
      Nat.zero_mul, Nat.zero_add]
    apply Run.le (n := 1) _ le_rfl
    apply Run.single
    simp [hostCfg, cfg, program, TM2.stepAux, jump, stackContents, board]
  | succ k ih =>
    let b := R (x, w, (coinBlock m r).reverse)
    have h₁ := trial_run V x w r m k y n
    have h₂ := ih (r.drop m) (y + if b then 1 else 0) (n + if b then 0 else 1)
    have ht := h₁.trans h₂
    have he : (r.drop m).drop (m * k) = r.drop (m * (k + 1)) := by
      rw [List.drop_drop, Nat.mul_succ, Nat.add_comm]
    rw [he] at ht
    have hb₀ : (if b then 1 else 0) + (results R x w m k (r.drop m)).count true =
        outcomes.count true := by
      change _ = (b :: results R x w m k (r.drop m)).count true
      cases b <;> simp [Nat.add_comm]
    have hb₁ : (if b then 0 else 1) + (results R x w m k (r.drop m)).count false =
        outcomes.count false := by
      change _ = (b :: results R x w m k (r.drop m)).count false
      cases b <;> simp [Nat.add_comm]
    change RunLe _ (trialBudget V m pre.length + (k * trialBudget V m pre.length + 1)) _ _ at ht
    rw [Nat.add_assoc y, Nat.add_assoc n, hb₀, hb₁] at ht
    exact ht.mono (by rw [Nat.succ_mul]; omega)

private theorem cleanup_run (m : ℕ) (pre r : List Bool) (y n : ℕ) (b : Bool) :
    RunLe (program V) (m + pre.length + r.length + y + n + 2)
      (hostCfg V (.clean b) (stackContents V (board V m 0 pre r y n) (fun _ => [])))
      (haltList (tm V) [b]) := by
  let _ := flag V
  let S := stackContents V (board V m 0 pre r y n) (fun _ => [])
  have hc := clean_run (M := program V) (ks := discard V) (self := .inl (.clean b))
    (next := .inl (.done b)) rfl (by simp [discard]) (m + pre.length + r.length + y + n)
    (none, V.tm.initialState) S (by
      intro j hj
      simp only [discard, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp [S, stackContents, board] <;> omega)
  have hc' : RunLe (program V) (m + pre.length + r.length + y + n + 1)
      (hostCfg V (.clean b) S) ⟨some (.inl (.done b)), Flag.tag false, fun _ => []⟩ := by
    convert hc using 2 <;> try rfl
    funext j
    rcases j with j | j
    · cases j <;> simp [discard, S, board, stackContents]
    · simp [discard, S, stackContents]
  have hd : Run (program V) 1
      ⟨some (.inl (.done b)), Flag.tag false, fun _ => []⟩ (haltList (tm V) [b]) := by
    apply Run.single
    rw [Cslib.Complexity.Host.haltList_eq]
    rfl
  exact hc'.trans (hd.le le_rfl)

private theorem load_run (p k : Polynomial ℕ) (x r w : List Bool) :
    let m := p.eval x.length
    let t := k.eval x.length
    let pre := trialPrefix x w
    Run (program V) (m + t + pre.length + r.length + 4)
      (initList (tm V) (workEncoding p k (x, r, w)))
      (hostCfg V .nextTrial (stackContents V (board V m t pre r 0 0) (fun _ => []))) := by
  intro m t pre
  let s := workEncoding p k (x, r, w)
  let tail := r.reverse.map some ++ [none]
  let E : Stacks V := fun _ => []
  let S₀ := update E (.inl .inp) s
  have hs : s = (List.replicate m true).map some ++ none ::
      ((List.replicate t true).map some ++ none :: (pre.map some ++ none :: tail)) := by
    simp [s, workEncoding, tail, m, t, pre, List.append_assoc]
  have h₀ := readField_run V (.inl .width) (by simp) id .readWidth .readTrials
    rfl (List.replicate m true)
      ((List.replicate t true).map some ++ none :: (pre.map some ++ none :: tail)) S₀
      (by simpa [S₀] using hs)
  let S₁ := update (update E (.inl .width) (List.replicate m true)) (.inl .inp)
    ((List.replicate t true).map some ++ none :: (pre.map some ++ none :: tail))
  have e₁ : update (update S₀ (.inl .inp)
        ((List.replicate t true).map some ++ none :: (pre.map some ++ none :: tail)))
      (.inl .width) (((List.replicate m true).map id).reverse ++ S₀ (.inl .width)) = S₁ := by
    funext j
    rcases j with j | j
    · cases j <;> simp [S₀, S₁, E, update_of_ne]
    · simp [S₀, S₁, E, update_of_ne]
  rw [e₁, List.length_replicate] at h₀
  have h₁ := readField_run V (.inl .trials) (by simp) id .readTrials .readPrefix
    rfl (List.replicate t true) (pre.map some ++ none :: tail) S₁ (by simp [S₁])
  let S₂ := update (update (update E (.inl .width) (List.replicate m true)) (.inl .trials)
    (List.replicate t true)) (.inl .inp) (pre.map some ++ none :: tail)
  have e₂ : update (update S₁ (.inl .inp) (pre.map some ++ none :: tail))
      (.inl .trials) (((List.replicate t true).map id).reverse ++ S₁ (.inl .trials)) = S₂ := by
    funext j
    rcases j with j | j
    · cases j <;> simp [S₁, S₂, E, update_of_ne]
    · simp [S₁, S₂, E, update_of_ne]
  rw [e₂, List.length_replicate] at h₁
  have h₂ := readField_run V (.inl .trialPrefix) (by simp) id .readPrefix .readCoins
    rfl pre tail S₂ (by simp [S₂])
  let S₃ := update (stackContents V (board V m t pre [] 0 0) (fun _ => [])) (.inl .inp) tail
  have e₃ : update (update S₂ (.inl .inp) tail) (.inl .trialPrefix)
      ((pre.map id).reverse ++ S₂ (.inl .trialPrefix)) = S₃ := by
    funext j
    rcases j with j | j
    · cases j <;> simp [S₂, S₃, E, stackContents, board, update_of_ne]
    · simp [S₂, S₃, E, stackContents, update_of_ne]
  rw [e₃] at h₂
  have h₃ := readField_run V (.inl .coins) (by simp) id .readCoins .nextTrial
    rfl r.reverse [] S₃ (by simp [S₃, tail])
  have e₄ : update (update S₃ (.inl .inp) []) (.inl .coins)
      ((r.reverse.map id).reverse ++ S₃ (.inl .coins)) =
      stackContents V (board V m t pre r 0 0) (fun _ => []) := by
    funext j
    rcases j with j | j
    · cases j <;> simp [S₃, stackContents, board, update_of_ne]
    · simp [S₃, stackContents, update_of_ne]
  rw [e₄, List.length_reverse] at h₃
  have hi : initList (tm V) s = hostCfg V .readWidth S₀ := by
    rw [Cslib.Complexity.Host.initList_eq]
    rfl
  rw [hi]
  exact (((h₀.trans h₁).trans h₂).trans h₃).of_eq (by omega)

private noncomputable def computable (p k : Polynomial ℕ) :
    TM2ComputableInPolyTime (workEncoding p k) bitEncode (expanded p k R) where
  tm := tm V
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 20 * (Polynomial.X + 1) +
    Polynomial.X * (V.time.comp (Polynomial.C 3 * Polynomial.X) + Polynomial.C 4 * Polynomial.X + 6)
  outputsFun v := Classical.choice <| by
    rcases v with ⟨x, r, w⟩
    let m := p.eval x.length
    let t := k.eval x.length
    let pre := trialPrefix x w
    let outcomes := results R x w m t r
    let N := (workEncoding p k (x, r, w)).length
    have hN : N = m + t + pre.length + r.length + 4 := by
      simp [N, workEncoding, m, t, pre]; omega
    have h₀ := load_run V p k x r w
    have h₁ := trials_run V x w r m t 0 0
    simp only [Nat.zero_add] at h₁
    obtain ⟨y', hy, n', hn, h₂⟩ :=
      compare_run V m pre (r.drop (m * t)) (outcomes.count true) (outcomes.count false)
    let b := decide (outcomes.count false < outcomes.count true)
    have h₃ := cleanup_run V m pre (r.drop (m * t)) y' n' b
    obtain ⟨time, ht, run⟩ := (((h₀.le le_rfl).trans h₁).trans h₂).trans h₃
    refine ⟨⟨⟨time, ?_⟩, ?_⟩⟩
    · change Run (program V) time
        (initList (tm V) (List.map id (workEncoding p k (x, r, w))))
        (haltList (tm V) (List.map id [b]))
      erw [List.map_id, List.map_id]
      exact run
    · change time ≤ (Polynomial.C 20 * (Polynomial.X + 1) +
        Polynomial.X * (V.time.comp (Polynomial.C 3 * Polynomial.X) +
          Polynomial.C 4 * Polynomial.X + 6)).eval N
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_comp, Polynomial.eval_ofNat]
      have htot := results_length (R := R) x w r m t
      have hy₀ : outcomes.count true ≤ t := (List.count_le_length).trans_eq htot
      have hn₀ : outcomes.count false ≤ t := (List.count_le_length).trans_eq htot
      have hd : (r.drop (m * t)).length ≤ r.length := by simp
      have htime := TM2Composition.eval_mono V.time (show pre.length + 3 * m ≤ 3 * N by omega)
      have hbudget : trialBudget V m pre.length ≤ V.time.eval (3 * N) + 4 * N + 6 := by
        unfold trialBudget
        omega
      have hbound := Nat.mul_le_mul (show t ≤ N by omega) hbudget
      change time ≤ (m + t + pre.length + r.length + 4) +
        (t * trialBudget V m pre.length + 1) + (outcomes.count true + 1) +
        (m + pre.length + (r.drop (m * t)).length + y' + n' + 2) at ht
      omega

end Repetition

/-! ### Preparing the counters and verifier input -/

namespace Prepare

open TM2Embedding
open Cslib.Complexity.CookLevin.CounterView Cslib.Complexity.CookLevin.Precompute

private abbrev Counter := Fin 6
private abbrev base : Counter := 0
private abbrev width : Counter := 1
private abbrev trials : Counter := 2
private abbrev prod : Counter := 3
private abbrev index : Counter := 4
private abbrev scratch : Counter := 5

private inductive Work | input | saved | output
  deriving DecidableEq

private instance workFintype : Fintype Work where
  elems := ⟨↑[Work.input, .saved, .output], by decide⟩
  complete k := by cases k <;> decide

private abbrev Key := SK Counter ⊕ Work

private abbrev Alphabet : Key → Type
  | .inl c => SΓ Counter c
  | .inr .output => Option Bool
  | .inr _ => Bool

private abbrev inp : Key := .inr .input
private abbrev saved : Key := .inr .saved
private abbrev out : Key := .inr .output
private abbrev count (k : Counter) : Key := .inl (.c k)

private abbrev Round (cs : List ℕ) := Option (Fin cs.length × HW)

private def roundAt (cs : List ℕ) (i : ℕ) (s : HW) : Round cs :=
  if h : i < cs.length then some (⟨i, h⟩, s) else none

private def horner (a : Counter) (cs : List ℕ) : Round cs → TM2.Stmt (SΓ Counter) (Round cs) Bool
  | none => .halt
  | some (i, s) => hornS base a prod index scratch cs[i] (roundAt cs i)
      (roundAt cs (i + 1) (.mul .head)) s

private inductive Control (ps ks : List ℕ)
  | start | readInput | readCoins | readWitness | restore
  | evalWidth (r : Round ps) | evalTrials (r : Round ks)
  | emitTrials | sepWidth | emitWidth | clean | done
  deriving DecidableEq

private noncomputable instance controlFintype (ps ks : List ℕ) : Fintype (Control ps ks) :=
  Fintype.ofSurjective
    (fun l : (Round ps ⊕ Round ks) ⊕ Fin 10 =>
      match l with
      | .inl (.inl r) => .evalWidth r
      | .inl (.inr r) => .evalTrials r
      | .inr 0 => .start
      | .inr 1 => .readInput
      | .inr 2 => .readCoins
      | .inr 3 => .readWitness
      | .inr 4 => .restore
      | .inr 5 => .emitTrials
      | .inr 6 => .sepWidth
      | .inr 7 => .emitWidth
      | .inr 8 => .clean
      | .inr _ => .done)
    (by rintro (⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | r | r | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩) <;>
        first | exact ⟨.inl (.inl r), rfl⟩ | exact ⟨.inl (.inr r), rfl⟩ |
          exact ⟨.inr 0, rfl⟩ | exact ⟨.inr 1, rfl⟩ | exact ⟨.inr 2, rfl⟩ |
          exact ⟨.inr 3, rfl⟩ | exact ⟨.inr 4, rfl⟩ | exact ⟨.inr 5, rfl⟩ |
          exact ⟨.inr 6, rfl⟩ | exact ⟨.inr 7, rfl⟩ | exact ⟨.inr 8, rfl⟩ | exact ⟨.inr 9, rfl⟩)

private def emb : SEmb (SΓ Counter) Alphabet where
  e := .inl
  inj := Sum.inl_injective
  ι _ := Equiv.refl _

private abbrev Stmt (ps ks : List ℕ) := TM2.Stmt Alphabet (Control ps ks) Bool

private abbrev discardBit {ps ks : List ℕ} (next : Stmt ps ks) : Stmt ps ks :=
  .pop inp (fun b _ => b) next

private abbrev readBit {ps ks : List ℕ} (next : Stmt ps ks) : Stmt ps ks :=
  .pop inp (fun _ a => a.getD false) next

private abbrev saveBit {ps ks : List ℕ} (next : Stmt ps ks) : Stmt ps ks :=
  .push saved (fun _ => true) <| .push saved (fun _ => true) <|
    .push saved (fun _ => true) <| .push saved id <|
    .push saved (fun _ => true) <| .push saved (fun _ => false) next

private abbrev readDelimitedBit {ps ks : List ℕ} (next : Stmt ps ks) : Stmt ps ks :=
  discardBit (discardBit (readBit (discardBit (discardBit next))))

private abbrev emitCounter {ps ks : List ℕ} (a : Counter) (self next : Control ps ks) :
    Stmt ps ks :=
  .pop (count a) (fun _ t => t.isSome) <|
    .branch id (.push out (fun _ => some true) (.goto fun _ => self)) (.goto fun _ => next)

private def program (ps ks : List ℕ) : Control ps ks → Stmt ps ks
  | .start => .push out (fun _ => none) (.goto fun _ => .readInput)
  | .readInput => readBit <| .branch id
      (readDelimitedBit (saveBit (.push (count base) (fun _ => ()) (.goto fun _ => .readInput))))
      (.push saved (fun _ => false) (.goto fun _ => .readCoins))
  | .readCoins => readBit <| .branch id
      (readDelimitedBit (.push out some (.goto fun _ => .readCoins)))
      (.goto fun _ => .readWitness)
  | .readWitness => readBit <| .branch id
      (readBit (discardBit (saveBit (.goto fun _ => .readWitness))))
      (.push saved (fun _ => false) <| .push out (fun _ => none) (.goto fun _ => .restore))
  | .restore => moveB saved out some some .restore (.evalWidth (roundAt ps 0 (.mul .head)))
  | .evalWidth (some r) => mapS emb Control.evalWidth (horner width ps (some r))
  | .evalWidth none => .goto fun _ => .evalTrials (roundAt ks 0 (.mul .head))
  | .evalTrials (some r) => mapS emb Control.evalTrials (horner trials ks (some r))
  | .evalTrials none => .push out (fun _ => none) (.goto fun _ => .emitTrials)
  | .emitTrials => emitCounter trials .emitTrials .sepWidth
  | .sepWidth => .push out (fun _ => none) (.goto fun _ => .emitWidth)
  | .emitWidth => emitCounter width .emitWidth .clean
  | .clean => .pop (count base) (fun _ a => a.isSome)
      (.goto fun b => if b then .clean else .done)
  | .done => .load (fun _ => false) .halt

private noncomputable abbrev tm (ps ks : List ℕ) : FinTM2 where
  K := Key
  Γ := Alphabet
  k₀ := inp
  k₁ := out
  Λ := Control ps ks
  σ := Bool
  main := .start
  initialState := false
  m := program ps ks
  Γk₀Fin := inferInstanceAs (Fintype Bool)

private def layout (F : Counter → ℕ) (p i : List Bool) (o : List (Option Bool)) :
    (j : Key) → List (Alphabet j)
  | .inl j => st F [] j
  | .inr .saved => p
  | .inr .input => i
  | .inr .output => o

private theorem set_saved (F : Counter → ℕ) (p i : List Bool) (o : List (Option Bool))
    (l : List Bool) : update (layout F p i o) saved l = layout F l i o := by
  funext j
  rcases j with j | j
  · rfl
  · cases j <;> rfl

private theorem set_inp (F : Counter → ℕ) (p i : List Bool) (o : List (Option Bool))
    (l : List Bool) : update (layout F p i o) inp l = layout F p l o := by
  funext j
  rcases j with j | j
  · rfl
  · cases j <;> rfl

private theorem set_out (F : Counter → ℕ) (p i : List Bool) (o l : List (Option Bool)) :
    update (layout F p i o) out l = layout F p i l := by
  funext j
  rcases j with j | j
  · rfl
  · cases j <;> rfl

private theorem set_count (F : Counter → ℕ) (p i : List Bool) (o : List (Option Bool))
    (k : Counter) (n : ℕ) :
    update (layout F p i o) (count k) (cnt () n) = layout (update F k n) p i o := by
  funext j
  rcases j with (_ | j) | j
  · rfl
  · by_cases h : j = k
    · subst j; simp [layout, st, count]
    · simp [h, layout, st, count, update_of_ne]
  · cases j <;> rfl

private theorem delimit_bits_cons (b : Bool) (l : List Bool) :
    delimit (coinEncoding (b :: l)) = [true, true, true, b, true, false] ++
      delimit (coinEncoding l) := rfl

private theorem read_input_run (ps ks : List ℕ) (x p i : List Bool) (o : List (Option Bool))
    (F : Counter → ℕ) (v : Bool) :
    Run (program ps ks) (x.length + 1)
      ⟨some .readInput, v, layout F p (delimit (coinEncoding x) ++ i) o⟩
      ⟨some .readCoins, false,
        layout (update F base (F base + x.length))
          ((delimit (coinEncoding x)).reverse ++ p) i o⟩ := by
  induction x generalizing p F v with
  | nil =>
    exact Run.single (by simp [coinEncoding, delimit, program, TM2.stepAux, inp, saved,
      layout, set_saved, set_inp])
  | cons b x ih =>
    let p' := [false, true, b, true, true, true] ++ p
    let F' := update F base (F base + 1)
    have h : Run (program ps ks) 1
        ⟨some .readInput, v, layout F p (delimit (coinEncoding (b :: x)) ++ i) o⟩
        ⟨some .readInput, b, layout F' p' (delimit (coinEncoding x) ++ i) o⟩ := by
      apply Run.single
      simpa [program, delimit_bits_cons, TM2.stepAux, inp, saved, layout, st,
        p', F', cnt, List.replicate_succ, set_saved, set_inp] using
        congrArg (TM2.Cfg.mk (some (Control.readInput : Control ps ks)) b)
          (set_count F p' (delimit (coinEncoding x) ++ i) o base (F base + 1))
    have hr := h.trans (ih p' F' b)
    have he : F base + 1 + x.length = F base + (b :: x).length := by simp; omega
    simpa [delimit_bits_cons, p', F', List.append_assoc, he, Nat.add_left_comm] using hr

private theorem read_coins_run (ps ks : List ℕ) (r p i : List Bool) (o : List (Option Bool))
    (F : Counter → ℕ) (v : Bool) :
    Run (program ps ks) (r.length + 1)
      ⟨some .readCoins, v, layout F p (delimit (coinEncoding r) ++ i) o⟩
      ⟨some .readWitness, false, layout F p i (r.reverse.map some ++ o)⟩ := by
  induction r generalizing o v with
  | nil => exact Run.single (by simp [coinEncoding, delimit, program, TM2.stepAux,
      inp, layout, set_inp])
  | cons b r ih =>
    have h : Run (program ps ks) 1
        ⟨some .readCoins, v, layout F p (delimit (coinEncoding (b :: r)) ++ i) o⟩
        ⟨some .readCoins, b, layout F p (delimit (coinEncoding r) ++ i) (some b :: o)⟩ := by
      apply Run.single
      simp [program, delimit_bits_cons, TM2.stepAux, inp, out, layout, set_inp, set_out]
    simpa [List.append_assoc, Nat.add_left_comm] using h.trans (ih (some b :: o) b)

private theorem read_witness_run (ps ks : List ℕ) (w p : List Bool) (o : List (Option Bool))
    (F : Counter → ℕ) (v : Bool) :
    Run (program ps ks) (w.length + 1)
      ⟨some .readWitness, v, layout F p (coinEncoding w) o⟩
      ⟨some .restore, false,
        layout F ((delimit (coinEncoding w)).reverse ++ p) [] (none :: o)⟩ := by
  induction w generalizing p v with
  | nil => exact Run.single (by simp [coinEncoding, delimit, program, TM2.stepAux,
      inp, saved, out, layout, set_inp, set_saved, set_out])
  | cons b w ih =>
    let p' := [false, true, b, true, true, true] ++ p
    have h : Run (program ps ks) 1
        ⟨some .readWitness, v, layout F p (coinEncoding (b :: w)) o⟩
        ⟨some .readWitness, b, layout F p' (coinEncoding w) o⟩ := by
      apply Run.single
      simp [program, coinEncoding, TM2.stepAux, inp, saved, layout, p', set_inp, set_saved]
    simpa [p', delimit_bits_cons, List.append_assoc, Nat.add_left_comm] using h.trans (ih p' b)

private theorem restore_run (ps ks : List ℕ) (p : List Bool) (o : List (Option Bool))
    (F : Counter → ℕ) :
    ∃ v, Run (program ps ks) (p.length + 1)
      ⟨some .restore, false, layout F p.reverse [] o⟩
      ⟨some (.evalWidth (roundAt ps 0 (.mul .head))), v, layout F [] [] (p.map some ++ o)⟩ := by
  obtain ⟨v, S, h, hs, ho, hk⟩ := moveB_run (M := program ps ks) (a := saved) (b := out)
    (self := .restore) (next := .evalWidth (roundAt ps 0 (.mul .head)))
    (d := some) (g := some) rfl (by decide) p.reverse p.reverse [] false
      (layout F p.reverse [] o) (by simp [saved, layout]) rfl rfl
  have he : S = layout F [] [] (p.map some ++ o) := by
    funext j
    rcases j with _ | j
    · exact hk _ (by simp [saved]) (by simp [out])
    · cases j
      · exact hk _ (by decide) (by decide)
      · exact hs
      · simpa [out, layout, List.map_reverse] using ho
  rw [he, List.length_reverse] at h
  exact ⟨v, h⟩

private theorem evaluation_run (a : Counter) (p : Polynomial ℕ) (ps ks : List ℕ)
    (lab : Round (coeffs p) → Control ps ks)
    (hEmb : Embeds emb lab (horner a (coeffs p)) (program ps ks))
    (hnd : [base, a, prod, index, scratch].Nodup)
    (F : Counter → ℕ) (ha : F a = 0) (hq : F prod = 0) (hi : F index = 0)
    (ht : F scratch = 0) (v : Bool) (o : List (Option Bool)) :
    ∃ v', Run (program ps ks) (hornT (coeffs p) (F base) 0)
      ⟨some (lab (roundAt (coeffs p) 0 (.mul .head))), v, layout F [] [] o⟩
      ⟨some (lab none), v', layout (update F a (p.eval (F base))) [] [] o⟩ := by
  let cs := coeffs p
  have hp (j : ℕ) (hj : j < cs.length) (s : HW) :
      horner a cs (roundAt cs j s) =
      hornS base a prod index scratch cs[j] (roundAt cs j)
        (if j + 1 < cs.length then roundAt cs (j + 1) (.mul .head) else none) s := by
    rw [show roundAt cs j s = some (⟨j, hj⟩, s) by simp [roundAt, hj]]
    unfold horner
    by_cases h : j + 1 < cs.length <;> simp [roundAt, h]
  obtain ⟨v', hr⟩ := horner_run (M := horner a cs) (mk := roundAt cs) (exit := none)
    cs hp hnd cs.length 0 (by simp) F hq hi ht v []
  have hstart : (if 0 < cs.length then roundAt cs 0 (.mul .head) else none) =
      roundAt cs 0 (.mul .head) := by by_cases h : 0 < cs.length <;> simp [roundAt, h]
  rw [hstart, List.drop_zero, ha, hornVal_coeffs] at hr
  obtain ⟨S, h, hagree, hframe⟩ := run_embed lab hEmb _ _ _ _ _ _ _ (layout F [] [] o) hr
    (fun j => (List.map_id (st F [] j)).symm)
  have he : S = layout (update F a (p.eval (F base))) [] [] o := by
    funext j
    rcases j with j | j
    · exact (hagree j).trans (List.map_id _)
    · cases j <;> exact hframe _ (fun _ => by simp [emb])
  exact ⟨v', he ▸ h⟩

private theorem emit_run (ps ks : List ℕ) (a : Counter) (self exit : Control ps ks)
    (hp : program ps ks self = emitCounter a self exit) (F : Counter → ℕ) (n : ℕ)
    (hn : F a = n) (v : Bool) (o : List (Option Bool)) :
    Run (program ps ks) (n + 1) ⟨some self, v, layout F [] [] o⟩
      ⟨some exit, false, layout (update F a 0) [] [] (List.replicate n (some true) ++ o)⟩ := by
  induction n generalizing F o v with
  | zero =>
    apply Run.single
    have hf : update F a 0 = F := by rw [← hn, Function.update_eq_self]
    simp [hp, emitCounter, TM2.stepAux, count, layout, st, cnt, hn, hf]
  | succ n ih =>
    let F' := update F a n
    have h : Run (program ps ks) 1 ⟨some self, v, layout F [] [] o⟩
        ⟨some self, true, layout F' [] [] (some true :: o)⟩ := by
      apply Run.single
      have he := congrArg (fun S => update S out (some true :: o)) (set_count F [] [] o a n)
      simpa [hp, emitCounter, TM2.stepAux, count, layout, st, cnt, hn, List.replicate_succ,
        out, F', set_out] using congrArg (TM2.Cfg.mk (some self) true) he
    have hr := h.trans (ih F' (by simp [F']) true (some true :: o))
    simpa [F', List.replicate_succ', List.append_assoc, Nat.add_left_comm] using hr

private theorem finish_run (ps ks : List ℕ) (n : ℕ) (v : Bool) (o : List (Option Bool)) :
    Run (program ps ks) (n + 2)
      ⟨some .clean, v, layout (update (fun _ => 0) base n) [] [] o⟩
      (haltList (tm ps ks) o) := by
  induction n generalizing v with
  | zero =>
    have hc : Run (program ps ks) 1
        ⟨some .clean, v, layout (update (fun _ => 0) base 0) [] [] o⟩
        ⟨some .done, false, layout (fun _ => 0) [] [] o⟩ := by
      apply Run.single
      simp [program, TM2.stepAux, count, layout, st, cnt]
    have hd : Run (program ps ks) 1 ⟨some .done, false, layout (fun _ => 0) [] [] o⟩
        (haltList (tm ps ks) o) := by
      apply Run.single
      rw [Cslib.Complexity.Host.haltList_eq]
      apply congrArg (TM2.Cfg.mk none false)
      funext j
      rcases j with (_ | _) | j
      · rfl
      · rfl
      · cases j <;> rfl
    exact hc.trans hd
  | succ n ih =>
    have hs : Run (program ps ks) 1
        ⟨some .clean, v, layout (update (fun _ => 0) base (n + 1)) [] [] o⟩
        ⟨some .clean, true, layout (update (fun _ => 0) base n) [] [] o⟩ := by
      apply Run.single
      have he := (set_count (update (fun _ => 0) base (n + 1)) [] [] o base n).trans
        (congrArg (fun F => layout F [] [] o) (Function.update_idem _ _ _))
      simpa [program, TM2.stepAux, count, layout, st, cnt, List.replicate_succ] using
        congrArg (TM2.Cfg.mk (some (Control.clean : Control ps ks)) true) he
    exact (hs.trans (ih true)).of_eq (by omega)

private theorem combined_run (p k : Polynomial ℕ) (x r w : List Bool) :
    let ps := coeffs p
    let ks := coeffs k
    let n := x.length
    let time := x.length + r.length + w.length + (trialPrefix x w).length + n +
      hornT ps n 0 + hornT ks n 0 + k.eval n + p.eval n + 12
    RunLe (program ps ks) time
      (initList (tm ps ks) (bitEncode (x, r, w)))
      (haltList (tm ps ks) (workEncoding p k (x, r, w))) := by
  intro ps ks n time
  let F : Counter → ℕ := update (fun _ => 0) base n
  let F₁ := update F width (p.eval n)
  let F₂ := update F₁ trials (k.eval n)
  let tape := (trialPrefix x w).map some ++ none :: (r.reverse.map some ++ [none])
  let inp₀ := delimit (coinEncoding x) ++ (delimit (coinEncoding r) ++ coinEncoding w)
  have hinit : initList (tm ps ks) (bitEncode (x, r, w)) =
      ⟨some .start, false, layout (fun _ => 0) [] inp₀ []⟩ := by
    rw [encoding_trial, Cslib.Complexity.Host.initList_eq]
    apply congrArg (TM2.Cfg.mk (some (Control.start : Control ps ks)) false)
    funext j
    rcases j with (_ | _) | j
    · rfl
    · rfl
    · cases j <;> simp [layout, inp₀, trialPrefix, List.append_assoc]
  have h₀ : Run (program ps ks) 1
      ⟨some .start, false, layout (fun _ => 0) [] inp₀ []⟩
      ⟨some .readInput, false, layout (fun _ => 0) [] inp₀ [none]⟩ :=
    Run.single (by simp [program, TM2.stepAux, out, layout, set_out])
  have h₁ := read_input_run ps ks x [] (delimit (coinEncoding r) ++ coinEncoding w)
    [none] (fun _ => 0) false
  simp only [Nat.zero_add, List.append_nil] at h₁
  have h₂ := read_coins_run ps ks r (delimit (coinEncoding x)).reverse (coinEncoding w)
    [none] F false
  have h₃ := read_witness_run ps ks w (delimit (coinEncoding x)).reverse
    (r.reverse.map some ++ [none]) F false
  rw [← List.reverse_append] at h₃
  change Run (program ps ks) _ _ ⟨some .restore, false, layout F (trialPrefix x w).reverse []
    (none :: (r.reverse.map some ++ [none]))⟩ at h₃
  obtain ⟨v, h₄⟩ := restore_run ps ks (trialPrefix x w) (none :: (r.reverse.map some ++ [none])) F
  have hw : Embeds emb Control.evalWidth (horner width ps) (program ps ks) := by
    rintro (_ | a)
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hk : Embeds emb Control.evalTrials (horner trials ks) (program ps ks) := by
    rintro (_ | a)
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨v₁, e₁⟩ := evaluation_run width p ps ks Control.evalWidth hw (by decide)
    F rfl rfl rfl rfl v tape
  have ht : Run (program ps ks) 1
      ⟨some (.evalWidth none), v₁, layout F₁ [] [] tape⟩
      ⟨some (.evalTrials (roundAt ks 0 (.mul .head))), v₁, layout F₁ [] [] tape⟩ :=
    Run.single rfl
  obtain ⟨v₂, e₂⟩ := evaluation_run trials k ps ks Control.evalTrials hk (by decide)
    F₁ rfl rfl rfl rfl v₁ tape
  have hstart : Run (program ps ks) 1 ⟨some (.evalTrials none), v₂, layout F₂ [] [] tape⟩
      ⟨some .emitTrials, v₂, layout F₂ [] [] (none :: tape)⟩ :=
    Run.single (by simp [program, TM2.stepAux, out, layout, set_out])
  have ht₁ := emit_run ps ks trials .emitTrials .sepWidth rfl F₂ (k.eval n) (update_self ..)
    v₂ (none :: tape)
  let afterTrials := List.replicate (k.eval n) (some true) ++ none :: tape
  have hF₂ : update F₂ trials 0 = F₁ := by
    unfold F₂
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
  rw [hF₂] at ht₁
  have hsep : Run (program ps ks) 1 ⟨some .sepWidth, false, layout F₁ [] [] afterTrials⟩
      ⟨some .emitWidth, false, layout F₁ [] [] (none :: afterTrials)⟩ :=
    Run.single (by simp [program, TM2.stepAux, out, layout, set_out])
  have ht₂ := emit_run ps ks width .emitWidth .clean rfl F₁ (p.eval n) (update_self ..)
    false (none :: afterTrials)
  have hF₁ : update F₁ width 0 = F := by
    unfold F₁
    rw [Function.update_idem]
    exact Function.update_eq_self _ _
  rw [hF₁] at ht₂
  have hout : List.replicate (p.eval n) (some true) ++ none :: afterTrials =
      workEncoding p k (x, r, w) := by
    simp [workEncoding, List.append_assoc, afterTrials, tape, n]
  rw [hout] at ht₂
  have hd := finish_run ps ks n false (workEncoding p k (x, r, w))
  rw [hinit]
  have run := (((((((((h₀.trans h₁).trans h₂).trans h₃).trans h₄).trans e₁).trans ht).trans
    e₂).trans hstart).trans ht₁).trans hsep |>.trans ht₂ |>.trans hd
  apply run.le
  dsimp only [time]
  have hbase : F base = n := rfl
  have hbase₁ : F₁ base = n := rfl
  simp only [hbase, hbase₁, ps, ks]
  omega

private noncomputable def computable (p k : Polynomial ℕ) :
    TM2ComputableInPolyTime bitEncode (workEncoding p k) (id :
      List Bool × List Bool × List Bool → List Bool × List Bool × List Bool) := by
  let P := Classical.choose (IsPoly.hornT (coeffs p) (IsPoly.const 0))
  let K := Classical.choose (IsPoly.hornT (coeffs k) (IsPoly.const 0))
  have hp : ∀ n, hornT (coeffs p) n 0 = P.eval n :=
    Classical.choose_spec (IsPoly.hornT (coeffs p) (IsPoly.const 0))
  have hk : ∀ n, hornT (coeffs k) n 0 = K.eval n :=
    Classical.choose_spec (IsPoly.hornT (coeffs k) (IsPoly.const 0))
  let time := Polynomial.C 10 * (Polynomial.X + 1) + P + K + p + k
  refine {
    tm := tm (coeffs p) (coeffs k)
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := time
    outputsFun := fun ⟨x, r, w⟩ => Classical.choice ?_ }
  obtain ⟨t, ht, run⟩ := combined_run p k x r w
  refine ⟨⟨⟨t, ?_⟩, ?_⟩⟩
  · change Run (program (coeffs p) (coeffs k)) t
      (initList (tm (coeffs p) (coeffs k)) ((bitEncode (x, r, w)).map id))
      (haltList (tm (coeffs p) (coeffs k)) ((workEncoding p k (x, r, w)).map id))
    erw [List.map_id, List.map_id]
    exact run
  · let N := (bitEncode (x, r, w)).length
    have hN : N = 6 * x.length + 6 * r.length + 3 * w.length + 2 := by
      rw [show N = (bitEncode (x, r, w)).length by rfl, encoding_trial]
      simp [trialPrefix, Repetition.coinEncoding_length]
      omega
    have hpre : (trialPrefix x w).length = 6 * x.length + 6 * w.length + 2 := by
      simp [trialPrefix, Repetition.coinEncoding_length]
      omega
    have hle : x.length ≤ N := by omega
    have hp' := TM2Composition.eval_mono P hle
    have hk' := TM2Composition.eval_mono K hle
    rw [← hp] at hp'
    rw [← hk] at hk'
    have hp'' := TM2Composition.eval_mono p hle
    have hk'' := TM2Composition.eval_mono k hle
    change t ≤ time.eval N
    simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    change t ≤ x.length + r.length + w.length + (trialPrefix x w).length + x.length +
      hornT (coeffs p) x.length 0 + hornT (coeffs k) x.length 0 +
      k.eval x.length + p.eval x.length + 12 at ht
    omega

end Prepare

/-! ### Counting the accepting random tapes -/

private def votes {α : Type} {n : ℕ} (test : α → Bool) (r : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => test (r i) = true).card

-- The exponential moment with base 2 factors over the independent trials.
private theorem tail {α : Type} [Fintype α] [Nonempty α] (test : α → Bool) (m : ℕ)
    (h : 3 * {a | test a = true}.ncard ≤ Fintype.card α) :
    2 ^ m * {r : Fin (12 * m) → α | 6 * m ≤ votes test r}.ncard ≤
      Fintype.card α ^ (12 * m) := by
  classical
  let N := Fintype.card α
  let A : Set α := {a | test a = true}
  let B : Set (Fin (12 * m) → α) := {r | 6 * m ≤ votes test r}
  let weight : α → ℕ := fun a => 1 + if test a = true then 1 else 0
  have hsum : ∑ a, weight a = N + A.ncard := by
    simp only [weight, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, Finset.sum_boole, N]
    rw [Set.ncard_eq_toFinset_card A]
    exact congrArg (N + ·) (congrArg Finset.card (by ext a; simp [A]))
  have hprod (r : Fin (12 * m) → α) : ∏ i, weight (r i) = 2 ^ votes test r := by
    have he (i : Fin (12 * m)) : weight (r i) = if test (r i) = true then 2 else 1 := by
      simp only [weight]
      split <;> rfl
    simp [he, votes, ← Finset.prod_filter]
  have hmoment : (N + A.ncard) ^ (12 * m) = ∑ r : Fin (12 * m) → α, 2 ^ votes test r := by
    rw [← hsum, Finset.sum_pow']
    simp [hprod]
  have hmarkov : B.ncard * 2 ^ (6 * m) ≤ (N + A.ncard) ^ (12 * m) := by
    rw [hmoment]
    calc
      _ = ∑ _r ∈ B.toFinset, 2 ^ (6 * m) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
      ∑ _r ∈ B.toFinset, 2 ^ (6 * m) ≤ ∑ r ∈ B.toFinset, 2 ^ votes test r := by
        gcongr with r hr
        exact (Set.mem_toFinset.mp hr : r ∈ B)
      _ ≤ ∑ r, 2 ^ votes test r := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hmul : 3 * (N + A.ncard) ≤ 4 * N := by change 3 * A.ncard ≤ N at h; omega
  have h₁ : B.ncard * (2 ^ (6 * m) * 3 ^ (12 * m)) ≤ (4 * N) ^ (12 * m) := by
    calc
      _ = B.ncard * 2 ^ (6 * m) * 3 ^ (12 * m) := by ring
      _ ≤ (N + A.ncard) ^ (12 * m) * 3 ^ (12 * m) := Nat.mul_le_mul_right _ hmarkov
      _ ≤ _ := by rw [← mul_pow, mul_comm (N + A.ncard)]; exact Nat.pow_le_pow_left hmul _
  have h₂ : 2 ^ m * (4 * N) ^ (12 * m) ≤
      (2 ^ (6 * m) * 3 ^ (12 * m)) * N ^ (12 * m) := by
    rw [mul_pow, ← mul_assoc, pow_mul 4, pow_mul 2 6, pow_mul 3, ← mul_pow, ← mul_pow]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide : 2 * 4 ^ 12 ≤ 2 ^ 6 * 3 ^ 12) _)
  have h₃ := (Nat.mul_le_mul_left (2 ^ m) h₁).trans h₂
  exact Nat.le_of_mul_le_mul_right (by simpa only [mul_left_comm, mul_comm, mul_assoc] using h₃ :
    (2 ^ m * B.ncard) * (2 ^ (6 * m) * 3 ^ (12 * m)) ≤
      N ^ (12 * m) * (2 ^ (6 * m) * 3 ^ (12 * m))) (by positivity)

private theorem votes_complement {α : Type} (n : ℕ) (test : α → Bool) (r : Fin n → α) :
    votes test r + votes (fun a => !test a) r = n := by
  simpa only [votes, Bool.not_eq_true', Bool.not_eq_true, Fintype.card_fin, Finset.card_univ] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => test (r i) = true))

private theorem results_blocks (R : Verifier) (x w : List Bool) (m k : ℕ)
    (rs : Fin k → Fin m → Bool) :
    results R x w m k (List.flatten (List.ofFn fun i => List.ofFn (rs i))) =
      List.ofFn fun i => R (x, w, (List.ofFn (rs i)).reverse) := by
  induction k with
  | zero => simp [results]
  | succ k ih =>
    simp only [List.ofFn_succ, List.flatten_cons, results]
    rw [coinBlock_append _ _ (by simp)]
    have hdrop : (List.ofFn (rs 0) ++
        (List.ofFn fun i : Fin k => List.ofFn (rs i.succ)).flatten).drop m =
        (List.ofFn fun i : Fin k => List.ofFn (rs i.succ)).flatten := by
      conv_lhs => arg 1; rw [← List.length_ofFn (f := rs 0)]
      exact List.drop_left
    rw [hdrop]
    exact congrArg (_ :: ·) (ih (fun i => rs i.succ))

private def splitCoins (k m : ℕ) :
    (Fin (k * m) → Bool) ≃ (Fin k → Fin m → Bool) :=
  (finProdFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

private theorem ofFn_split (k m : ℕ) (r : Fin (k * m) → Bool) :
    List.ofFn r = List.flatten (List.ofFn fun i => List.ofFn (splitCoins k m r i)) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp [splitCoins, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

private theorem reverse_trials (R : Verifier) (x w : List Bool) (m : ℕ) :
    {u : Fin m → Bool | R (x, w, (List.ofFn u).reverse) = true}.ncard =
      {u : Fin m → Bool | R (x, w, List.ofFn u) = true}.ncard := by
  let e := (Fin.revPerm (n := m)).arrowCongr (Equiv.refl Bool)
  have he (u : Fin m → Bool) : List.ofFn (e u) = (List.ofFn u).reverse := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
      change u (Fin.rev ⟨i, _⟩) = u ⟨m - 1 - i, _⟩
      congr 1
      apply Fin.ext
      change m - (i + 1) = m - 1 - i
      omega
  let A : Set (Fin m → Bool) := {u | R (x, w, List.ofFn u) = true}
  calc
    _ = (e ⁻¹' A).ncard := by congr 1; ext u; simp [A, he]
    _ = _ := Set.ncard_preimage_of_injective_subset_range e.injective
      (by simp [e.surjective.range_eq])

private def witnesses : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert [] (((witnesses n).image (false :: ·)) ∪ ((witnesses n).image (true :: ·)))

private theorem mem_witnesses (q : ℕ) (w : List Bool) :
    w ∈ witnesses q ↔ w.length ≤ q := by
  induction q generalizing w with
  | zero => simp [witnesses]
  | succ q ih =>
    cases w with
    | nil => simp [witnesses]
    | cons b w => cases b <;> simp [witnesses, ih]

private theorem card_witnesses (q : ℕ) : (witnesses q).card + 1 ≤ 2 ^ (q + 1) := by
  induction q with
  | zero => decide
  | succ q ih =>
    unfold witnesses
    have hi := Finset.card_insert_le (s := ((witnesses q).image (false :: ·) ∪
      (witnesses q).image (true :: ·))) []
    have hu := Finset.card_union_le (s := (witnesses q).image (false :: ·))
      (t := (witnesses q).image (true :: ·))
    have h₀ := Finset.card_image_le (s := witnesses q) (f := (false :: ·))
    have h₁ := Finset.card_image_le (s := witnesses q) (f := (true :: ·))
    rw [pow_succ]
    omega

private theorem split_total (m k : ℕ) :
    Fintype.card (Fin m → Bool) ^ k = 2 ^ (k * m) := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

private theorem flat_tail {m s : ℕ} (test : (Fin m → Bool) → Bool)
    (h : 3 * {u | test u = true}.ncard ≤ 2 ^ m) :
    2 ^ s * {r : Fin ((12 * s) * m) → Bool |
      6 * s ≤ votes test (splitCoins (12 * s) m r)}.ncard ≤ 2 ^ ((12 * s) * m) := by
  let A : Set (Fin (12 * s) → Fin m → Bool) := {r | 6 * s ≤ votes test r}
  let e := splitCoins (12 * s) m
  have hA : 3 * {u | test u = true}.ncard ≤ Fintype.card (Fin m → Bool) := by simpa using h
  have ht := tail test s hA
  rw [split_total] at ht
  change 2 ^ s * (e ⁻¹' A).ncard ≤ 2 ^ ((12 * s) * m)
  rw [Set.ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq])]
  exact ht

private theorem expanded_majority (R : Verifier) (x w : List Bool) (m s : ℕ)
    (r : Fin ((12 * s) * m) → Bool) :
    let test := fun u : Fin m → Bool => R (x, w, (List.ofFn u).reverse)
    let rs := splitCoins (12 * s) m r
    let outcomes := results R x w m (12 * s) (List.ofFn r)
    outcomes.count false < outcomes.count true ↔ votes (fun u => !test u) rs < votes test rs := by
  intro test rs outcomes
  have hr : outcomes = List.ofFn (test ∘ rs) := by
    simp only [outcomes, test, rs, Function.comp_def]
    rw [ofFn_split]
    exact results_blocks R x w m (12 * s) _
  rw [hr]
  simp [votes, Function.comp_def]

private theorem amplified_complete (R : Verifier) (x w : List Bool) (m q : ℕ)
    (h : 2 * 2 ^ m ≤ 3 * {u : Fin m → Bool | R (x, w, List.ofFn u) = true}.ncard) :
    2 * 2 ^ ((12 * (q + 3)) * m) ≤
      3 * {r : Fin ((12 * (q + 3)) * m) → Bool |
        let a := results R x w m (12 * (q + 3)) (List.ofFn r)
        a.count false < a.count true}.ncard := by
  let s := q + 3
  let test := fun u : Fin m → Bool => R (x, w, (List.ofFn u).reverse)
  let A : Set (Fin m → Bool) := {u | test u = true}
  let G : Set (Fin ((12 * s) * m) → Bool) := {r |
    let a := results R x w m (12 * s) (List.ofFn r)
    a.count false < a.count true}
  have hA : 2 * 2 ^ m ≤ 3 * A.ncard := by
    change 2 * 2 ^ m ≤ 3 * {u : Fin m → Bool | R (x, w, (List.ofFn u).reverse) = true}.ncard
    rwa [reverse_trials]
  have hsum : A.ncard + Aᶜ.ncard = 2 ^ m := by simpa using A.ncard_add_ncard_compl
  have hn : 3 * {u | !test u = true}.ncard ≤ 2 ^ m := by
    have he : {u | !test u = true} = Aᶜ := by ext u; simp [A]
    rw [he]
    omega
  have he : Gᶜ = {r : Fin ((12 * s) * m) → Bool |
      6 * s ≤ votes (fun u => !test u) (splitCoins (12 * s) m r)} := by
    ext r
    have hm := expanded_majority R x w m s r
    have hv := votes_complement (12 * s) test (splitCoins (12 * s) m r)
    change (results R x w m (12 * s) (List.ofFn r)).count false <
      (results R x w m (12 * s) (List.ofFn r)).count true ↔
      votes (fun u => !test u) (splitCoins (12 * s) m r) <
        votes test (splitCoins (12 * s) m r) at hm
    change (¬ (results R x w m (12 * s) (List.ofFn r)).count false <
      (results R x w m (12 * s) (List.ofFn r)).count true) ↔
      6 * s ≤ votes (fun u => !test u) (splitCoins (12 * s) m r)
    rw [hm]
    omega
  have ht := flat_tail (m := m) (s := s) (fun u => !test u) hn
  rw [← he] at ht
  have hpow : 3 ≤ 2 ^ s :=
    (by decide : 3 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hg : G.ncard + Gᶜ.ncard = 2 ^ ((12 * s) * m) := by
    simpa using G.ncard_add_ncard_compl
  have hr := (Nat.mul_le_mul_right Gᶜ.ncard hpow).trans ht
  change 2 * 2 ^ ((12 * s) * m) ≤ 3 * G.ncard
  omega

private theorem amplified_sound (R : Verifier) (x w : List Bool) (m q : ℕ)
    (h : 3 * {u : Fin m → Bool | R (x, w, List.ofFn u) = true}.ncard ≤ 2 ^ m) :
    2 ^ (q + 3) * {r : Fin ((12 * (q + 3)) * m) → Bool |
        let a := results R x w m (12 * (q + 3)) (List.ofFn r)
        a.count false < a.count true}.ncard ≤ 2 ^ ((12 * (q + 3)) * m) := by
  let s := q + 3
  let test := fun u : Fin m → Bool => R (x, w, (List.ofFn u).reverse)
  have ht : 3 * {u | test u = true}.ncard ≤ 2 ^ m := by
    change 3 * {u : Fin m → Bool | R (x, w, (List.ofFn u).reverse) = true}.ncard ≤ 2 ^ m
    rwa [reverse_trials]
  refine (Nat.mul_le_mul_left (2 ^ s) (Set.ncard_le_ncard ?_)).trans (flat_tail test ht)
  intro r hr
  have hm := (expanded_majority R x w m s r).mp hr
  have hv := votes_complement (12 * s) test (splitCoins (12 * s) m r)
  change 6 * s ≤ votes test (splitCoins (12 * s) m r)
  change votes (fun u => !test u) (splitCoins (12 * s) m r) <
    votes test (splitCoins (12 * s) m r) at hm
  omega

private theorem union_sound {Ω : Type} [Finite Ω] (q N : ℕ) (A : List Bool → Set Ω)
    (h : ∀ w, w.length ≤ q → 2 ^ (q + 3) * (A w).ncard ≤ N) :
    3 * {r | ∃ w : List Bool, w.length ≤ q ∧ r ∈ A w}.ncard ≤ N := by
  classical
  let W := witnesses q
  let U : Set Ω := {r | ∃ w : List Bool, w.length ≤ q ∧ r ∈ A w}
  have hU : U = ⋃ w ∈ (↑W : Set (List Bool)), A w := by
    ext r
    simp [U, W, mem_witnesses]
  have ht : 2 ^ (q + 3) * U.ncard ≤ 2 ^ (q + 1) * N := calc
    _ ≤ 2 ^ (q + 3) * ∑ w ∈ W, (A w).ncard := by
      rw [hU]
      exact Nat.mul_le_mul_left _ (W.set_ncard_biUnion_le A)
    _ ≤ ∑ _w ∈ W, N := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun w hw => h w ((mem_witnesses q w).mp hw)
    _ = W.card * N := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      have hW : W.card + 1 ≤ 2 ^ (q + 1) := card_witnesses q
      omega)
  have he : 2 ^ (q + 3) = 4 * 2 ^ (q + 1) := by
    rw [show q + 3 = 2 + (q + 1) by omega, pow_add]
    rfl
  rw [he, mul_comm 4, mul_assoc] at ht
  have hf := Nat.le_of_mul_le_mul_left ht (Nat.two_pow_pos (q + 1))
  change 3 * U.ncard ≤ N
  omega


private theorem expanded_polyTime (p k : Polynomial ℕ) {R : Verifier} (hR : IsPolyTime R) :
    IsPolyTime (expanded p k R) := by
  obtain ⟨V⟩ := hR
  exact tm2ComputableInPolyTime_comp (Prepare.computable p k) (Repetition.computable V p k)

public section

open Cslib.Complexity.Classes

/-- **MA is contained in AM.** Every decision problem in the class $\mathsf{MA}$ is in the class
$\mathsf{AM}$.

Source: L. Babai, "Trading group theory for randomness",
Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing
(STOC 1985), 421-429; S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Theorem 8.2 (MA ⊆ AM). -/
public theorem ma_subset_am :
    MA ⊆ AM := by
  rintro L ⟨p, q, R, hR, hL⟩
  let k : Polynomial ℕ := 12 * (q + 3)
  refine ⟨k * p, q, expanded p k R, expanded_polyTime p k hR, fun x => ?_⟩
  let m := p.eval x.length
  let n := q.eval x.length
  have hk : k.eval x.length = 12 * (n + 3) := by simp [k, n]
  rw [Polynomial.eval_mul, hk]
  let A (w : List Bool) : Set (Fin ((12 * (n + 3)) * m) → Bool) := {r |
    let a := results R x w m (12 * (n + 3)) (List.ofFn r)
    a.count false < a.count true}
  let B : Set (Fin ((12 * (n + 3)) * m) → Bool) :=
    {r | ∃ w : List Bool, w.length ≤ n ∧ r ∈ A w}
  have hAB (r : Fin ((12 * (n + 3)) * m) → Bool) (w : List Bool) :
      expanded p k R (x, List.ofFn r, w) = true ↔ r ∈ A w := by
    simp [expanded, hk, A, m]
  have hB : {r : Fin ((12 * (n + 3)) * m) → Bool |
      ∃ w : List Bool, w.length ≤ n ∧ expanded p k R (x, List.ofFn r, w) = true} = B := by
    ext r
    simp only [B, Set.mem_ofPred_eq, hAB]
  change (L x = true → 2 * 2 ^ ((12 * (n + 3)) * m) ≤ 3 *
      {r : Fin ((12 * (n + 3)) * m) → Bool |
        ∃ w : List Bool, w.length ≤ n ∧ expanded p k R (x, List.ofFn r, w) = true}.ncard) ∧
    (L x = false → 3 * {r : Fin ((12 * (n + 3)) * m) → Bool |
        ∃ w : List Bool, w.length ≤ n ∧ expanded p k R (x, List.ofFn r, w) = true}.ncard ≤
      2 ^ ((12 * (n + 3)) * m))
  rw [hB]
  constructor
  · intro hx
    obtain ⟨w, hlen, h⟩ := (hL x).1 hx
    have hsub : A w ⊆ B := fun r hr => ⟨w, hlen, hr⟩
    exact (amplified_complete R x w m n h).trans
      (Nat.mul_le_mul_left 3 (Set.ncard_le_ncard hsub))
  · intro hx
    apply union_sound n _ A
    exact fun w hw => amplified_sound R x w m n ((hL x).2 hx w hw)

end

end MetaMathlibExt.Complexity.KeyTheorems.MASubsetAM
