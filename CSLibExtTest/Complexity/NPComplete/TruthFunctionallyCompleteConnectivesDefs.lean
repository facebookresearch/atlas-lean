/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectivesDefs

namespace MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Logic.LegacyPL Cslib.Circuits

private theorem accepts_encoding (i : TruthFunctionallyCompleteConnectivesInstance) :
    truthFunctionallyCompleteConnectivesDec (bitEncode i) = true ↔
      WellFormed i ∧ TruthFunctionallyCompleteConnectivesFeasible i := by
  simp [truthFunctionallyCompleteConnectivesDec, bitDecode_bitEncode]

/-- The NAND connective. -/
private abbrev nand (a b : Bool) : Bool := !(a && b)

/-- The circuit signature with the single binary gate of `D = [nand]`. -/
private abbrev σn : Signature := ⟨Fin [nand].length, fun _ => 2⟩

/-- Its interpretation, as in the feasibility predicate. -/
private abbrev Jn : Interpretation σn Bool :=
  fun k args => [nand].get k (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)

section Completeness

variable {m : ℕ}

/-- Some wire of `p` computes `h`. -/
private def Avail {g : ℕ} (p : Program σn m g) (h : (Fin m → Bool) → Bool) : Prop :=
  ∃ w, ∀ x, p.trace Jn x w = h x

/-- `h` can be added to any program by appending gates, keeping everything it computes. -/
private def Buildable (h : (Fin m → Bool) → Bool) : Prop :=
  ∀ (g : ℕ) (p : Program σn m g), ∃ (g' : ℕ) (p' : Program σn m g'),
    (∀ k, Avail p k → Avail p' k) ∧ Avail p' h

private theorem buildable_congr {f g : (Fin m → Bool) → Bool} (hf : Buildable f)
    (e : ∀ x, f x = g x) : Buildable g := by
  rw [← funext e]
  exact hf

private theorem buildable_input (i : Fin m) : Buildable fun x => x i :=
  fun g p => ⟨g, p, fun _ h => h, ⟨.input i, fun _ => rfl⟩⟩

private theorem buildable_nand {f g : (Fin m → Bool) → Bool} (hf : Buildable f)
    (hg : Buildable g) : Buildable fun x => nand (f x) (g x) := by
  intro n p
  obtain ⟨n₁, p₁, hp₁, hf₁⟩ := hf n p
  obtain ⟨n₂, p₂, hp₂, wg, hwg⟩ := hg n₁ p₁
  obtain ⟨wf, hwf⟩ := hp₂ _ hf₁
  let line : Line σn m n₂ := ⟨(0 : Fin 1), fun j => if j.val = 0 then wf else wg⟩
  refine ⟨n₂ + 1, p₂.gate line, fun k hk => ?_, ⟨.gate (Fin.last n₂), fun x => ?_⟩⟩
  · obtain ⟨w, hw⟩ := hp₂ k (hp₁ k hk)
    exact ⟨w.castSucc, fun x => (Program.trace_gate_castSucc _ _ _ _ _).trans (hw x)⟩
  · change (p₂.gate line).eval Jn x (Fin.last n₂) = _
    rw [Program.eval_gate_last]
    change nand (p₂.trace Jn x wf) (p₂.trace Jn x wg) = _
    rw [hwf, hwg]

private theorem buildable_not {f : (Fin m → Bool) → Bool} (hf : Buildable f) :
    Buildable fun x => !f x :=
  buildable_congr (buildable_nand hf hf) fun x => by cases f x <;> rfl

private theorem buildable_and {f g : (Fin m → Bool) → Bool} (hf : Buildable f)
    (hg : Buildable g) : Buildable fun x => f x && g x :=
  buildable_congr (buildable_not (buildable_nand hf hg)) fun x => by
    cases f x <;> cases g x <;> rfl

private theorem buildable_or {f g : (Fin m → Bool) → Bool} (hf : Buildable f)
    (hg : Buildable g) : Buildable fun x => f x || g x :=
  buildable_congr (buildable_nand (buildable_not hf) (buildable_not hg)) fun x => by
    cases f x <;> cases g x <;> rfl

/-- With an input `x₀`, `nand(x₀, ¬x₀)` is the constant `true`. -/
private theorem buildable_true (i₀ : Fin m) : Buildable fun (_ : Fin m → Bool) => true :=
  buildable_congr (buildable_nand (buildable_input i₀) (buildable_not (buildable_input i₀)))
    fun x => by cases x i₀ <;> rfl

private theorem buildable_all {ι : Type} (i₀ : Fin m) (l : List ι)
    (F : ι → (Fin m → Bool) → Bool) (hF : ∀ i ∈ l, Buildable (F i)) :
    Buildable fun x => l.all fun i => F i x := by
  induction l with
  | nil => simpa using buildable_true i₀
  | cons i l ih =>
    simpa using buildable_and (hF i List.mem_cons_self)
      (ih fun j hj => hF j (List.mem_cons_of_mem i hj))

private theorem buildable_any {ι : Type} (i₀ : Fin m) (l : List ι)
    (F : ι → (Fin m → Bool) → Bool) (hF : ∀ i ∈ l, Buildable (F i)) :
    Buildable fun x => l.any fun i => F i x := by
  induction l with
  | nil => simpa using buildable_not (buildable_true i₀)
  | cons i l ih =>
    simpa using buildable_or (hF i List.mem_cons_self)
      (ih fun j hj => hF j (List.mem_cons_of_mem i hj))

/-- Every Boolean function of at least one input has a NAND circuit: the disjunction of the
minterms of its true points. -/
private theorem nand_complete (i₀ : Fin m) (f : (Fin m → Bool) → Bool) :
    ∃ c : Circuit σn m 1, c.Computes Jn (single f) := by
  classical
  have hmin (v : Fin m → Bool) :
      Buildable fun x => (List.finRange m).all fun i => decide (x i = v i) :=
    buildable_all i₀ _ _ fun i _ => by
      cases hv : v i
      · simpa using buildable_not (buildable_input i)
      · simpa using buildable_input i
  have hterm (v : Fin m → Bool) :
      Buildable fun x => f v && (List.finRange m).all fun i => decide (x i = v i) := by
    cases f v
    · simpa using buildable_not (buildable_true i₀)
    · simpa using hmin v
  have hf : Buildable f := by
    refine buildable_congr (buildable_any i₀ (Finset.univ : Finset (Fin m → Bool)).toList _
      fun v _ => hterm v) fun x => ?_
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and,
      Bool.and_eq_true, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, forall_const]
    constructor
    · rintro ⟨v, hv, hxv⟩
      rwa [show x = v from funext hxv]
    · exact fun hx => ⟨x, hx, fun _ => rfl⟩
  obtain ⟨g, p, -, w, hw⟩ := hf 0 .empty
  exact ⟨⟨p, fun _ => w⟩, fun x => funext fun _ => hw x⟩

end Completeness

/-- `¬(u₀ ∧ u₁)` in postfix: `u₀ u₁ ∧ ¬`. -/
private abbrev nandTokens : List (ℕ × ℕ) := [(0, 0), (0, 1), (2, 0), (1, 0)]

/-- `u₀ ∧ u₁` in postfix: `u₀ u₁ ∧`. -/
private abbrev andTokens : List (ℕ × ℕ) := [(0, 0), (0, 1), (2, 0)]

/-- A lone continuation bit is a truncated instance encoding. -/
example : truthFunctionallyCompleteConnectivesDec [true] = false := by
  have h : bitDecode (α := TruthFunctionallyCompleteConnectivesInstance) [true] = none := rfl
  simp [truthFunctionallyCompleteConnectivesDec, h]

/-- `{¬(u₀ ∧ u₁)}` is complete: substituting `u₀ ↦ a`, `u₁ ↦ b` gives NAND, which builds every
truth function of at least one argument. -/
example :
    truthFunctionallyCompleteConnectivesDec
      (bitEncode ((2, [nandTokens]) : TruthFunctionallyCompleteConnectivesInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨fun t ht => ?_, [nand], fun θ hθ => ?_, fun m hm f => nand_complete ⟨0, hm⟩ f⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    unfold NonTautology.WellFormed
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hθ
    subst hθ
    refine ⟨nandTokens, List.mem_cons_self, _, rfl, fun x => decide (x = 0), ?_⟩
    funext a b
    cases a <;> cases b <;> rfl

/-- Every substitution instance of `u₀ ∧ u₁` maps `(true, true)` to `true`, so every circuit
over such connectives outputs `true` on the all-true input, and the constant `false` on one
input has no circuit. -/
example :
    truthFunctionallyCompleteConnectivesDec
      (bitEncode ((2, [andTokens]) : TruthFunctionallyCompleteConnectivesInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, D, hD, hcomp⟩ := (accepts_encoding _).1 hacc
  have htt : ∀ θ ∈ D, θ true true = true := by
    intro θ hθ
    obtain ⟨t, ht, E, hE, s, rfl⟩ := hD θ hθ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    have hp : NonTautology.parse andTokens =
        some (.and (.atom ((0 : ℕ) : WithBot ℕ)) (.atom ((1 : ℕ) : WithBot ℕ))) := rfl
    rw [hp, Option.some.injEq] at hE
    subst hE
    simp only [substOp, Proposition.evalBool, NonTautology.valuation, Bool.and_eq_true, ite_self]
    exact ⟨rfl, rfl⟩
  obtain ⟨c, hc⟩ := hcomp 1 Nat.one_pos fun _ => false
  let hom : Homomorphism (σ := ⟨Fin D.length, fun _ => 2⟩) (fun _ _ => ())
      (fun k args => D.get k (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)) :=
    ⟨fun _ => true, fun k _ => (htt _ (List.get_mem D k)).symm⟩
  have h₁ := congrFun (c.map_eval hom fun _ => ()) 0
  have h₂ := congrFun (hc fun _ => true) 0
  exact absurd (h₁.trans h₂) (by simp [hom])

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((2, [andTokens]) : TruthFunctionallyCompleteConnectivesInstance) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  unfold NonTautology.WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.TruthFunctionallyCompleteConnectives
