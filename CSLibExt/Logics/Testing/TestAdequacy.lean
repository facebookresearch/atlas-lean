/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Cast.Order
/-! # Test adequacy: Goodenough-Gerhart reliability/validity, exhaustive
finite-domain testing, mutation subsumption/score (Zhu, Hall and May 1997). -/

@[expose] public section

namespace Cslib.Testing

/-- A suite passes when every member input satisfies the specification. -/
def Passes {D O : Type*} (P : D → O) (S : D → O → Prop) (t : Finset D) : Prop :=
  ∀ x ∈ t, S x (P x)

/-- A program is correct when every input satisfies the specification. -/
def Correct {D O : Type*} (P : D → O) (S : D → O → Prop) : Prop :=
  ∀ x, S x (P x)

/-- A test adequacy criterion: which suites are adequate for a program and spec. -/
abbrev Criterion (D O : Type*) :=
  (D → O) → (D → O → Prop) → Finset D → Prop

/-- Goodenough–Gerhart reliability: passing transfers across adequate suites. -/
def Reliable {D O : Type*} (C : Criterion D O) (P : D → O) (S : D → O → Prop) :
    Prop :=
  ∀ t₁ t₂, C P S t₁ → C P S t₂ → Passes P S t₁ → Passes P S t₂

/-- Goodenough–Gerhart validity: every incorrect program has an adequate failing
suite. -/
def Valid {D O : Type*} (C : Criterion D O) (P : D → O) (S : D → O → Prop) :
    Prop :=
  ¬ Correct P S → ∃ t, C P S t ∧ ¬ Passes P S t

/-- The empty suite passes vacuously. -/
theorem passes_empty {D O : Type*} (P : D → O) (S : D → O → Prop) :
    Passes P S ∅ :=
  fun x hx => absurd hx (Finset.notMem_empty x)

/-- Passing the larger suite implies passing the smaller one. -/
theorem passes_mono {D O : Type*} (P : D → O) (S : D → O → Prop) {t₁ t₂ : Finset D}
    (hsub : t₁ ⊆ t₂) (hpass : Passes P S t₂) : Passes P S t₁ :=
  fun x hx => hpass x (hsub hx)

/-- Reliable + valid + one adequate passing suite gives correctness. -/
theorem reliable_valid_pass_implies_correct {D O : Type*} (C : Criterion D O)
    (P : D → O) (S : D → O → Prop) (t : Finset D)
    (hrel : Reliable C P S) (hval : Valid C P S)
    (had : C P S t) (hpass : Passes P S t) : Correct P S := by
  by_contra hnc
  obtain ⟨t', had', hnpass⟩ := hval hnc
  exact hnpass (hrel t t' had had' hpass)

/-- Passing the universal suite is correctness (finite domain). -/
theorem exhaustive_finite_domain {D O : Type*} [Fintype D] (P : D → O)
    (S : D → O → Prop) : Passes P S Finset.univ ↔ Correct P S := by
  constructor
  · intro h x
    exact h x (Finset.mem_univ x)
  · intro h x _
    exact h x

/-- The exhaustive criterion: only the universal suite is adequate. -/
def exhaustiveCriterion {D O : Type*} [Fintype D] : Criterion D O :=
  fun _ _ t => t = Finset.univ

theorem reliable_exhaustiveCriterion {D O : Type*} [Fintype D] (P : D → O)
    (S : D → O → Prop) : Reliable (exhaustiveCriterion : Criterion D O) P S := by
  intro t₁ t₂ h₁ h₂ hp
  have e₁ : t₁ = Finset.univ := h₁
  have e₂ : t₂ = Finset.univ := h₂
  subst e₁
  subst e₂
  exact hp

theorem valid_exhaustiveCriterion {D O : Type*} [Fintype D] (P : D → O)
    (S : D → O → Prop) : Valid (exhaustiveCriterion : Criterion D O) P S := by
  intro hnc
  exact ⟨Finset.univ, rfl, fun h => hnc ((exhaustive_finite_domain P S).mp h)⟩

/-- Generic kill-subsumption: every input killing `a` kills `b`. -/
def KillSubsumes {M D : Type*} (k : M → D → Prop) (a b : M) : Prop :=
  ∀ x, k a x → k b x

theorem killSubsumes_refl {M D : Type*} (k : M → D → Prop) (a : M) :
    KillSubsumes k a a :=
  fun _ h => h

theorem killSubsumes_trans {M D : Type*} (k : M → D → Prop) {a b c : M}
    (hab : KillSubsumes k a b) (hbc : KillSubsumes k b c) : KillSubsumes k a c :=
  fun x h => hbc x (hab x h)

/-- Strong killing: the mutant's output differs from the original's. -/
def Kills {D O M : Type*} (P : D → O) (mutant : M → D → O) (x : D) (m : M) :
    Prop :=
  mutant m x ≠ P x

/-- The set of inputs strongly killing a mutant. -/
def killSet {D O M : Type*} (P : D → O) (mutant : M → D → O) (m : M) : Set D :=
  {x | Kills P mutant x m}

/-- A suite kills a mutant when some member input does. -/
def killedBySuite {D O M : Type*} (P : D → O) (mutant : M → D → O) (t : Finset D)
    (m : M) : Prop :=
  ∃ x ∈ t, Kills P mutant x m

theorem killedBySuite_unfold {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (t : Finset D) (m : M) :
    killedBySuite P mutant t m ↔ ∃ x ∈ t, Kills P mutant x m :=
  Iff.rfl

/-- A suite kills a mutant iff some member input belongs to its kill set. -/
theorem killedBySuite_killSet {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (t : Finset D) (m : M) :
    killedBySuite P mutant t m ↔ ∃ x ∈ t, x ∈ killSet P mutant m :=
  Iff.rfl

/-- Mutant subsumption: every test killing `a` kills `b`. This is the strength
relation of p. 392 with arguments in the opposite order to its `⊑` notation:
there `a ⊑ b` says `b` is stronger than `a`. -/
def MutantSubsumes {D O M : Type*} (P : D → O) (mutant : M → D → O) (a b : M) :
    Prop :=
  KillSubsumes (fun m x => Kills P mutant x m) a b

theorem mutantSubsumes_char {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (a b : M) :
    MutantSubsumes P mutant a b ↔ ∀ x, Kills P mutant x a → Kills P mutant x b :=
  Iff.rfl

theorem mutantSubsumes_killSet {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (a b : M) :
    MutantSubsumes P mutant a b ↔ killSet P mutant a ⊆ killSet P mutant b :=
  Iff.rfl

theorem mutantSubsumes_refl {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (a : M) : MutantSubsumes P mutant a a :=
  killSubsumes_refl _ a

theorem mutantSubsumes_trans {D O M : Type*} (P : D → O) (mutant : M → D → O)
    {a b c : M} (hab : MutantSubsumes P mutant a b)
    (hbc : MutantSubsumes P mutant b c) : MutantSubsumes P mutant a c :=
  killSubsumes_trans _ hab hbc

/-- The subsumption preorder on mutants, as a standalone preorder. -/
@[instance_reducible]
def mutantSubsumptionPreorder {D O M : Type*} (P : D → O) (mutant : M → D → O) :
    Preorder M where
  le := MutantSubsumes P mutant
  le_refl := fun _ x h => h
  le_trans := fun _ _ _ hab hbc x hx => hbc x (hab x hx)

theorem mutantSubsumptionPreorder_le {D O M : Type*} (P : D → O)
    (mutant : M → D → O) (a b : M) :
    @LE.le M (mutantSubsumptionPreorder P mutant).toLE a b ↔
      MutantSubsumes P mutant a b :=
  Iff.rfl

/-- A mutant is equivalent when it agrees with the original on every input. -/
def EquivalentMutant {D O M : Type*} (P : D → O) (mutant : M → D → O) (m : M) :
    Prop :=
  ∀ x, mutant m x = P x

theorem equivalentMutant_iff_killSet_empty {D O M : Type*} (P : D → O)
    (mutant : M → D → O) (m : M) :
    EquivalentMutant P mutant m ↔ killSet P mutant m = ∅ := by
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact hx (h x)
  · intro h x
    by_contra hne
    have hx : x ∈ killSet P mutant m := hne
    rw [h] at hx
    exact Set.notMem_empty x hx

/-- An equivalent mutant subsumes every mutant, vacuously: it is killed by no
input, so the required implication holds trivially. This boundary is intended. -/
theorem mutantSubsumes_of_equivalent {D O M : Type*} (P : D → O)
    (mutant : M → D → O) {a b : M} (heq : EquivalentMutant P mutant a) :
    MutantSubsumes P mutant a b :=
  fun x hx => absurd (heq x) hx

/-- Killable within a suite: some member input strongly kills the mutant. -/
def KillableWithin {D O M : Type*} (P : D → O) (mutant : M → D → O) (t : Finset D) (m : M) : Prop :=
  killedBySuite P mutant t m
theorem killableWithin_unfold {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (t : Finset D) (m : M) :
    KillableWithin P mutant t m ↔ killedBySuite P mutant t m := Iff.rfl
/-- Dynamic subsumption within `t`: `a` is killable in `t` and its killers in `t` kill `b`. -/
def DynSubsumesWithin {D O M : Type*} (P : D → O) (mutant : M → D → O)
    (t : Finset D) (a b : M) : Prop :=
  KillableWithin P mutant t a ∧ ∀ x ∈ t, Kills P mutant x a → Kills P mutant x b
theorem dynSubsumesWithin_self_iff {D O M : Type*} (P : D → O)
    (mutant : M → D → O) (t : Finset D) (a : M) :
    DynSubsumesWithin P mutant t a a ↔ KillableWithin P mutant t a :=
    ⟨fun h => h.1, fun h => ⟨h, fun _ _ hk => hk⟩⟩
/-- Dynamic subsumption as a standalone preorder on the killable mutants. -/
@[instance_reducible]
def dynSubsumptionPreorder {D O M : Type*} (P : D → O) (mutant : M → D → O) (t : Finset D) :
    Preorder {m // KillableWithin P mutant t m} where
  le := fun a b => DynSubsumesWithin P mutant t a.val b.val
  le_refl := fun a => ⟨a.property, fun _ _ hk => hk⟩
  le_trans := fun _ _ _ hab hbc => ⟨hab.1, fun x hx hk => hbc.2 x hx (hab.2 x hx hk)⟩
theorem dynSubsumptionPreorder_le {D O M : Type*} (P : D → O) (mutant : M → D → O) (t : Finset D)
    (a b : {m // KillableWithin P mutant t m}) :
    @LE.le _ (dynSubsumptionPreorder P mutant t).toLE a b ↔
      DynSubsumesWithin P mutant t a.val b.val := Iff.rfl
/-- Weak killing: the observed internal states differ at the mutation point. -/
def WeaklyKills {D M St : Type*} (obs : D → St) (obsMutant : M → D → St) (x : D) (m : M) : Prop :=
  obsMutant m x ≠ obs x
/-- Weak subsumption via generic kill-subsumption. The score laws below are
strong-only: a weakly killed mutant may still be output-equivalent. -/
def WeakSubsumes {D M St : Type*} (obs : D → St) (obsMutant : M → D → St) (a b : M) : Prop :=
  KillSubsumes (fun m x => WeaklyKills obs obsMutant x m) a b
theorem weakSubsumes_unfold {D M St : Type*} (obs : D → St) (obsMutant : M → D → St) (a b : M) :
    WeakSubsumes obs obsMutant a b ↔ ∀ x,
      WeaklyKills obs obsMutant x a → WeaklyKills obs obsMutant x b := Iff.rfl
open Classical in
/-- The nonequivalent mutants of a family, as a finset of indices. -/
noncomputable def nonequivMutants {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) : Finset M :=
  Finset.univ.filter (fun m => ¬ EquivalentMutant P mutant m)
open Classical in
/-- The mutants of a family strongly killed by a suite, as a finset of indices. -/
noncomputable def killedMutants {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D) : Finset M :=
  Finset.univ.filter (fun m => killedBySuite P mutant t m)
/-- Mutation score `D / (M - E)`: `none` when all mutants are equivalent, else the
killed-to-nonequivalent ratio. -/
noncomputable def mutationScore {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D) : Option ℚ :=
  if (nonequivMutants P mutant).card = 0 then none
  else some (((killedMutants P mutant t).card : ℚ) / ((nonequivMutants P mutant).card : ℚ))
theorem killedMutants_subset_nonequiv {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D) :
    killedMutants P mutant t ⊆ nonequivMutants P mutant := by
  intro m hm
  simp only [killedMutants, nonequivMutants, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  obtain ⟨x, _, hkill⟩ := hm
  exact fun heq => hkill (heq x)
theorem mutationScore_eq_none_iff {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D) :
    mutationScore P mutant t = none ↔ (nonequivMutants P mutant).card = 0 := by
  simp only [mutationScore]
  by_cases h : (nonequivMutants P mutant).card = 0 <;> simp [h]
theorem mutationScore_nonneg {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D)
    (q : ℚ) (h : mutationScore P mutant t = some q) : 0 ≤ q := by
  by_cases hc : (nonequivMutants P mutant).card = 0
  · simp [mutationScore, hc] at h
  · simp only [mutationScore, ite_eq_right hc, Option.some_inj] at h
    rw [← h]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem mutationScore_le_one {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D)
    (q : ℚ) (h : mutationScore P mutant t = some q) : q ≤ 1 := by
  have hne : (nonequivMutants P mutant).card ≠ 0 := by
    intro hz; have hnone := (mutationScore_eq_none_iff P mutant t).mpr hz
    rw [h] at hnone; simp at hnone
  have hpos : (0 : ℚ) < ((nonequivMutants P mutant).card : ℚ) := Nat.cast_pos.mpr (by omega)
  have h0 : ((nonequivMutants P mutant).card : ℚ) ≠ 0 := ne_of_gt hpos
  have hle : ((killedMutants P mutant t).card : ℚ) ≤ ((nonequivMutants P mutant).card : ℚ) :=
    Nat.cast_le.mpr (Finset.card_le_card (killedMutants_subset_nonequiv P mutant t))
  simp only [mutationScore, ite_eq_right hne, Option.some_inj] at h
  rw [← h, ← div_self h0]
  exact (div_le_div_iff_of_pos_right hpos).mpr hle
/-- Full score is mutation adequacy for the family, not program correctness. -/
theorem mutationScore_eq_one {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t : Finset D) :
    mutationScore P mutant t = some 1 ↔ (nonequivMutants P mutant).card ≠ 0 ∧
      killedMutants P mutant t = nonequivMutants P mutant := by
  constructor
  · intro h
    have hne : (nonequivMutants P mutant).card ≠ 0 := by
      intro hz; have hnone := (mutationScore_eq_none_iff P mutant t).mpr hz
      rw [h] at hnone; simp at hnone
    refine ⟨hne, ?_⟩
    have hpos : (0 : ℚ) < ((nonequivMutants P mutant).card : ℚ) := Nat.cast_pos.mpr (by omega)
    simp only [mutationScore, ite_eq_right hne, Option.some_inj] at h
    have hcast : ((killedMutants P mutant t).card : ℚ) = ((nonequivMutants P mutant).card : ℚ) :=
      (div_eq_one_iff_eq (ne_of_gt hpos)).mp h
    have hle : (nonequivMutants P mutant).card ≤ (killedMutants P mutant t).card :=
      Nat.cast_le.mp (le_of_eq hcast.symm)
    exact Finset.eq_of_subset_of_card_le (killedMutants_subset_nonequiv P mutant t) hle
  · intro ⟨hne, heq⟩
    simp [mutationScore, hne, heq]
theorem killedMutants_mono {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t₁ t₂ : Finset D)
    (hsub : t₁ ⊆ t₂) : killedMutants P mutant t₁ ⊆ killedMutants P mutant t₂ := by
  intro m hm
  simp only [killedMutants, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  obtain ⟨x, hxt, hkill⟩ := hm
  exact ⟨x, hsub hxt, hkill⟩
theorem mutationScore_mono {D O M : Type*} [Fintype M] (P : D → O)
    (mutant : M → D → O) (t₁ t₂ : Finset D)
    (hsub : t₁ ⊆ t₂) (q₁ q₂ : ℚ) (h₁ : mutationScore P mutant t₁ = some q₁)
    (h₂ : mutationScore P mutant t₂ = some q₂) : q₁ ≤ q₂ := by
  have hne : (nonequivMutants P mutant).card ≠ 0 := by
    intro hz; have hnone := (mutationScore_eq_none_iff P mutant t₁).mpr hz
    rw [h₁] at hnone; simp at hnone
  have hpos : (0 : ℚ) < ((nonequivMutants P mutant).card : ℚ) := Nat.cast_pos.mpr (by omega)
  have hcard : ((killedMutants P mutant t₁).card : ℚ) ≤ ((killedMutants P mutant t₂).card : ℚ) :=
    Nat.cast_le.mpr (Finset.card_le_card (killedMutants_mono P mutant t₁ t₂ hsub))
  simp only [mutationScore, ite_eq_right hne, Option.some_inj] at h₁ h₂
  rw [← h₁, ← h₂]
  exact (div_le_div_iff_of_pos_right hpos).mpr hcard
theorem killedMutants_empty {D O M : Type*} [Fintype M] (P : D → O) (mutant : M → D → O) :
    killedMutants P mutant ∅ = ∅ := by
  simp only [killedMutants, Finset.filter_eq_empty_iff]
  intro x _ hkill
  obtain ⟨y, hxy, _⟩ := hkill
  exact Finset.notMem_empty y hxy
theorem mutationScore_empty {D O M : Type*} [Fintype M] (P : D → O) (mutant : M → D → O)
    (hne : (nonequivMutants P mutant).card ≠ 0) : mutationScore P mutant ∅ = some 0 := by
  have hk : killedMutants P mutant ∅ = ∅ := killedMutants_empty P mutant
  simp [mutationScore, hne, hk]

end Cslib.Testing
