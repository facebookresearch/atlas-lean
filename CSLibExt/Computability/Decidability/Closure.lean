/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure properties of decidable and recognizable predicates
-/
module

public import CSLibExt.Computability.Decidability.Basic
public import MathlibExt.Computability.RE
public import Mathlib.Computability.Language

/-!
# Closure properties of decidable and recognizable predicates

Decidable predicates (`TM2Decidable`) are closed under conjunction, disjunction and negation.
Recognizable predicates (`TM2Recognizable`) are closed under conjunction and disjunction. The
generic facts about `ComputablePred` and `REPred`, including dovetailing over finite
candidate lists, are in `MathlibExt/Computability/RE.lean`. For Mathlib `Language`s, both
classes are closed under concatenation `*` and Kleene star `∗`: try every split point, or
every partition into nonempty pieces, in parallel for recognizers.

## Main results

- `TM2Decidable.and`, `TM2Decidable.or`, `TM2Recognizable.and`, `TM2Recognizable.or`.
- `TM2Decidable.mul`, `TM2Recognizable.mul`, `TM2Decidable.kstar`, `TM2Recognizable.kstar`.
- `TM2Recognizable.map`: closure of recognizable languages under alphabet maps.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
  Exercises 3.15 and 3.16.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Computability

variable {α : Type*} [Primcodable α]

/-! ### Boolean closure -/

/-- Decidable predicates are closed under conjunction. -/
theorem TM2Decidable.and {p q : α → Prop} (hp : TM2Decidable p) (hq : TM2Decidable q) :
    TM2Decidable fun a ↦ p a ∧ q a :=
  tm2Decidable_iff_computablePred.mpr (MetaMathlibExt.ComputablePred.and
    (tm2Decidable_iff_computablePred.mp hp) (tm2Decidable_iff_computablePred.mp hq))

/-- Decidable predicates are closed under disjunction. -/
theorem TM2Decidable.or {p q : α → Prop} (hp : TM2Decidable p) (hq : TM2Decidable q) :
    TM2Decidable fun a ↦ p a ∨ q a :=
  tm2Decidable_iff_computablePred.mpr (MetaMathlibExt.ComputablePred.or
    (tm2Decidable_iff_computablePred.mp hp) (tm2Decidable_iff_computablePred.mp hq))

/-- Recognizable predicates are closed under conjunction. -/
theorem TM2Recognizable.and {p q : α → Prop} (hp : TM2Recognizable p) (hq : TM2Recognizable q) :
    TM2Recognizable fun a ↦ p a ∧ q a :=
  tm2Recognizable_iff_rePred.mpr (MetaMathlibExt.REPred.and
    (tm2Recognizable_iff_rePred.mp hp) (tm2Recognizable_iff_rePred.mp hq))

/-- Recognizable predicates are closed under disjunction. -/
theorem TM2Recognizable.or {p q : α → Prop} (hp : TM2Recognizable p) (hq : TM2Recognizable q) :
    TM2Recognizable fun a ↦ p a ∨ q a :=
  tm2Recognizable_iff_rePred.mpr (MetaMathlibExt.REPred.or
    (tm2Recognizable_iff_rePred.mp hp) (tm2Recognizable_iff_rePred.mp hq))

/-! ### Concatenation -/

variable {σ : Type*}

/-- The language where a Boolean test is `true`. -/
def boolLang (f : List σ → Bool) : Language σ := {u | f u = true}

@[simp] theorem mem_boolLang {f : List σ → Bool} {u : List σ} : u ∈ boolLang f ↔ f u = true :=
  Iff.rfl

/-- Membership in a concatenation `L₁ * L₂`, as a split `w = u ++ v`. -/
theorem mem_mul_iff_exists_append {L₁ L₂ : Language σ} {w : List σ} :
    w ∈ L₁ * L₂ ↔ ∃ u v, w = u ++ v ∧ u ∈ L₁ ∧ v ∈ L₂ := by
  rw [Language.mem_mul]
  exact ⟨fun ⟨u, hu, v, hv, h⟩ ↦ ⟨u, v, h.symm, hu, hv⟩,
    fun ⟨u, v, h, hu, hv⟩ ↦ ⟨u, hu, v, hv, h.symm⟩⟩

/-- A split test: some split point `i < n` of `w` has its prefix in `f` and suffix in `g`. -/
def splitTest (f g : List σ → Bool) (w : List σ) (n : ℕ) : Bool :=
  Nat.rec false (fun i acc ↦ acc || (f (w.take i) && g (w.drop i))) n

theorem splitTest_iff {f g : List σ → Bool} {w : List σ} {n : ℕ} :
    splitTest f g w n = true ↔ ∃ i < n, f (w.take i) = true ∧ g (w.drop i) = true := by
  induction n with
  | zero => simp [splitTest]
  | succ n ih =>
    simp only [splitTest] at ih ⊢
    rw [Bool.or_eq_true, ih, Bool.and_eq_true]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem mem_mul_iff_splitTest {f g : List σ → Bool} (w : List σ) :
    w ∈ boolLang f * boolLang g ↔
      splitTest f g w (w.length + 1) = true := by
  rw [mem_mul_iff_exists_append, splitTest_iff]
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    refine ⟨u.length, by rw [List.length_append]; omega, ?_, ?_⟩
    · simpa using hu
    · simpa using hv
  · rintro ⟨i, -, hu, hv⟩
    exact ⟨w.take i, w.drop i, (List.take_append_drop i w).symm, hu, hv⟩

variable [Primcodable σ]

/-- A decidable language is the set where a computable test is `true`. -/
theorem TM2Decidable.exists_computable {L : Language σ} (h : TM2Decidable (· ∈ L)) :
    ∃ f : List σ → Bool, Computable f ∧ L = boolLang f := by
  obtain ⟨f, hf, hfeq⟩ :=
    ComputablePred.computable_iff.mp (tm2Decidable_iff_computablePred.mp h)
  exact ⟨f, hf, Set.ext fun u ↦ Iff.of_eq (congrFun hfeq u)⟩

/-- **Decidable languages are closed under concatenation.** -/
theorem TM2Decidable.mul {L₁ L₂ : Language σ} (h₁ : TM2Decidable (· ∈ L₁))
    (h₂ : TM2Decidable (· ∈ L₂)) : TM2Decidable (· ∈ L₁ * L₂) := by
  obtain ⟨f, hf, rfl⟩ := h₁.exists_computable
  obtain ⟨g, hg, rfl⟩ := h₂.exists_computable
  refine tm2Decidable_iff_computablePred.mpr
    (ComputablePred.computable_iff.mpr ⟨fun w ↦ splitTest f g w (w.length + 1), ?_, ?_⟩)
  · have hstep : Computable₂ fun (w : List σ) (p : ℕ × Bool) ↦
        p.2 || (f (w.take p.1) && g (w.drop p.1)) :=
      (Primrec.or.to_comp).comp (Computable.snd.comp Computable.snd)
        ((Primrec.and.to_comp).comp
          (hf.comp ((Primrec.list_take.to_comp).comp (Computable.fst.comp Computable.snd)
            Computable.fst))
          (hg.comp ((Primrec.list_drop.to_comp).comp (Computable.fst.comp Computable.snd)
            Computable.fst)))
    exact Computable.nat_rec (Computable.succ.comp Computable.list_length) (Computable.const false)
      hstep
  · funext w
    exact propext (mem_mul_iff_splitTest w)

/-- The split points of a word. -/
def splits (w : List σ) : List (List σ × List σ) :=
  (List.range (w.length + 1)).map fun i ↦ (w.take i, w.drop i)

theorem primrec_splits : Primrec (splits (σ := σ)) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.list_length))
    ((Primrec.pair (Primrec.list_take.comp Primrec.snd Primrec.fst)
      (Primrec.list_drop.comp Primrec.snd Primrec.fst)).to₂)

omit [Primcodable σ] in
theorem mem_mul_iff_exists_mem_splits {L₁ L₂ : Language σ} (w : List σ) :
    w ∈ L₁ * L₂ ↔ ∃ p ∈ splits w, p.1 ∈ L₁ ∧ p.2 ∈ L₂ := by
  rw [mem_mul_iff_exists_append]
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    refine ⟨(u, v), List.mem_map.mpr ⟨u.length, ?_, ?_⟩, hu, hv⟩
    · rw [List.mem_range, List.length_append]
      omega
    · simp
  · rintro ⟨⟨u, v⟩, hp, hu, hv⟩
    obtain ⟨i, -, he⟩ := List.mem_map.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨w.take i, w.drop i, (List.take_append_drop i w).symm, hu, hv⟩

/-- **Recognizable languages are closed under concatenation.** -/
theorem TM2Recognizable.mul {L₁ L₂ : Language σ} (h₁ : TM2Recognizable (· ∈ L₁))
    (h₂ : TM2Recognizable (· ∈ L₂)) : TM2Recognizable (· ∈ L₁ * L₂) := by
  have h₁' : TM2Recognizable fun q : List σ × (List σ × List σ) ↦ q.2.1 ∈ L₁ :=
    tm2Recognizable_iff_rePred.mpr
      (Partrec.comp (tm2Recognizable_iff_rePred.mp h₁) (Computable.fst.comp Computable.snd))
  have h₂' : TM2Recognizable fun q : List σ × (List σ × List σ) ↦ q.2.2 ∈ L₂ :=
    tm2Recognizable_iff_rePred.mpr
      (Partrec.comp (tm2Recognizable_iff_rePred.mp h₂) (Computable.snd.comp Computable.snd))
  have hR := tm2Recognizable_iff_rePred.mp (h₁'.and h₂')
  refine tm2Recognizable_iff_rePred.mpr
    ((MetaMathlibExt.REPred.exists_mem
      (R := fun (_ : List σ) (p : List σ × List σ) ↦ p.1 ∈ L₁ ∧ p.2 ∈ L₂) hR
      primrec_splits).of_eq fun w ↦ (mem_mul_iff_exists_mem_splits w).symm)

/-! ### Kleene star -/


/-- One letter more: start a new piece, or extend the first piece. -/
def extendPartitions (a : σ) (ws : List (List σ)) : List (List (List σ)) :=
  ([a] :: ws) :: ws.head?.elim [] fun u ↦ [(a :: u) :: ws.tail]

/-- All partitions of a word into nonempty pieces. -/
def partitions (w : List σ) : List (List (List σ)) :=
  w.foldr (fun a acc ↦ acc.flatMap (extendPartitions a)) [[]]

omit [Primcodable σ] in
theorem mem_partitions {w : List σ} {ws : List (List σ)} :
    ws ∈ partitions w ↔ ws.flatten = w ∧ ∀ u ∈ ws, u ≠ [] := by
  induction w generalizing ws with
  | nil =>
    simp only [partitions, List.foldr_nil, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hf, hne⟩
      cases ws with
      | nil => rfl
      | cons u rest =>
        simp only [List.flatten_cons, List.append_eq_nil_iff] at hf
        exact absurd hf.1 (hne u List.mem_cons_self)
  | cons a w ih =>
    simp only [partitions, List.foldr_cons] at ih ⊢
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨vs, hvs, hws⟩
      obtain ⟨hf, hne⟩ := ih.mp hvs
      simp only [extendPartitions, List.mem_cons] at hws
      rcases hws with rfl | hws
      · refine ⟨by simp [hf], ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · simp
        · exact hne u hu
      · cases vs with
        | nil => simp at hws
        | cons v rest =>
          simp only [Option.elim, List.head?_cons, List.tail_cons, List.mem_singleton] at hws
          subst hws
          refine ⟨by simpa using hf, ?_⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simp
          · exact hne u (List.mem_cons_of_mem _ hu)
    · rintro ⟨hf, hne⟩
      cases ws with
      | nil => simp at hf
      | cons u rest =>
        obtain ⟨b, u', rfl⟩ := List.exists_cons_of_ne_nil (hne u List.mem_cons_self)
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
        obtain ⟨rfl, hf⟩ := hf
        cases u' with
        | nil =>
          refine ⟨rest, ih.mpr ⟨by simpa using hf,
            fun v hv ↦ hne v (List.mem_cons_of_mem _ hv)⟩, ?_⟩
          simp [extendPartitions]
        | cons c u'' =>
          refine ⟨(c :: u'') :: rest, ih.mpr ⟨hf, ?_⟩, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · simp
            · exact hne v (List.mem_cons_of_mem _ hv)
          · simp [extendPartitions]

omit [Primcodable σ] in
theorem mem_kstar_iff_exists_mem_partitions {L : Language σ} (w : List σ) :
    w ∈ L∗ ↔ ∃ ws ∈ partitions w, ∀ u ∈ ws, u ∈ L := by
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨ws, rfl, hL⟩
    refine ⟨ws.filter (· ≠ []), mem_partitions.mpr ⟨?_, ?_⟩, ?_⟩
    · clear hL
      induction ws with
      | nil => rfl
      | cons u ws ih =>
        by_cases hu : u = []
        · subst hu
          simpa using ih
        · simpa [hu] using ih
    · intro u hu
      simpa using (List.mem_filter.mp hu).2
    · intro u hu
      exact hL u (List.mem_filter.mp hu).1
  · rintro ⟨ws, hws, hL⟩
    exact ⟨ws, (mem_partitions.mp hws).1.symm, hL⟩

theorem primrec_partitions : Primrec (partitions (σ := σ)) := by
  have hext : Primrec₂ (extendPartitions (σ := σ)) := by
    refine Primrec.list_cons.comp
      (Primrec.list_cons.comp (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
        Primrec.snd) ?_
    refine (Primrec.option_casesOn (Primrec.list_head?.comp Primrec.snd) (Primrec.const [])
      ((Primrec.list_cons.comp (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const [])).to₂)).of_eq
      fun p ↦ ?_
    cases p.2.head? <;> rfl
  exact Primrec.list_foldr Primrec.id (Primrec.const [[]])
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (hext.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂

/-- **Recognizable languages are closed under Kleene star.** -/
theorem TM2Recognizable.kstar {L : Language σ} (h : TM2Recognizable (· ∈ L)) :
    TM2Recognizable (· ∈ L∗) := by
  have hL : REPred fun q : List (List σ) × List σ ↦ q.2 ∈ L :=
    Partrec.comp (tm2Recognizable_iff_rePred.mp h) Computable.snd
  have hall : REPred fun ws : List (List σ) ↦ ∀ u ∈ ws, u ∈ L :=
    (MetaMathlibExt.REPred.forall_mem (R := fun (_ : List (List σ)) (u : List σ) ↦ u ∈ L) hL
      Primrec.id)
  have hall' : REPred fun q : List σ × List (List σ) ↦ ∀ u ∈ q.2, u ∈ L :=
    Partrec.comp hall Computable.snd
  exact tm2Recognizable_iff_rePred.mpr
    ((MetaMathlibExt.REPred.exists_mem
      (R := fun (_ : List σ) (ws : List (List σ)) ↦ ∀ u ∈ ws, u ∈ L) hall'
      primrec_partitions).of_eq fun w ↦ (mem_kstar_iff_exists_mem_partitions w).symm)

/-- **Decidable languages are closed under Kleene star.** -/
theorem TM2Decidable.kstar {L : Language σ} (h : TM2Decidable (· ∈ L)) :
    TM2Decidable (· ∈ L∗) := by
  obtain ⟨f, hf, rfl⟩ := h.exists_computable
  refine tm2Decidable_iff_computablePred.mpr
    (ComputablePred.computable_iff.mpr ⟨fun w ↦ (partitions w).any fun ws ↦ ws.all f, ?_, ?_⟩)
  · have hall : Computable₂ fun (_ : List σ) (ws : List (List σ)) ↦ ws.all f := by
      have hany : Computable fun ws : List (List σ) ↦ ws.any fun u ↦ !f u :=
        MetaMathlibExt.computable_list_any (l := id) (g := fun _ u ↦ !f u) Computable.id
          ((Primrec.not.to_comp).comp (hf.comp Computable.snd)).to₂
      exact ((Primrec.not.to_comp.comp hany).comp Computable.snd).of_eq fun q ↦ by
        simp [List.all_eq_not_any_not]
    exact MetaMathlibExt.computable_list_any primrec_partitions.to_comp hall
  · funext w
    refine propext ((mem_kstar_iff_exists_mem_partitions w).trans ?_)
    simp only [List.any_eq_true, List.all_eq_true]
    exact Iff.rfl

/-! ### Alphabet maps -/

/-- **Recognizable languages are closed under alphabet maps** (`Language.map`): search for a
preimage word, by the unbounded dovetailing of `MetaMathlibExt.REPred.exists`. The map is
primitive recursive, as every map between finite alphabets is. -/
theorem TM2Recognizable.map {τ : Type*} [Primcodable τ] {f : σ → τ} (hf : Primrec f)
    {L : Language σ} (h : TM2Recognizable (· ∈ L)) :
    TM2Recognizable (· ∈ Language.map f L) := by
  classical
  have hL : REPred fun p : List τ × List σ ↦ p.2 ∈ L :=
    Partrec.comp (tm2Recognizable_iff_rePred.mp h) Computable.snd
  have heq : ComputablePred fun p : List τ × List σ ↦ p.2.map f = p.1 :=
    ComputablePred.computable_iff.mpr ⟨fun p ↦ decide (p.2.map f = p.1),
      (Primrec.eq.decide.comp (Primrec.list_map Primrec.snd (hf.comp Primrec.snd).to₂)
        Primrec.fst).to_comp, by funext p; simp⟩
  exact tm2Recognizable_iff_rePred.mpr
    ((MetaMathlibExt.REPred.exists (R := fun (v : List τ) (w : List σ) ↦ w ∈ L ∧ w.map f = v)
      (MetaMathlibExt.REPred.and hL heq.to_re)).of_eq fun _ ↦ Iff.rfl)

end Cslib.Decidability
