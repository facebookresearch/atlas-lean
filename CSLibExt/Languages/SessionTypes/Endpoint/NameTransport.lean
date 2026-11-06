/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Identity

/-!
# Existing π binder transformations for endpoint transport

These algebraic laws concern the canonical π lift/substitution operations;
name and process scoping remain the canonical PiCalculus predicates.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Substitution cancels name lifting.**
Substitution removes an inserted binder without changing its shifted
outer names. The inserted binder's replacement is arbitrary. -/
theorem substName_liftName (b a : Name) (k : Nat) :
    substName b k (liftName k a) = a := by
  cases a with
  | const => rfl
  | var i =>
    by_cases h : k ≤ i
    · have hlt : ¬ i + 1 < k := by omega
      have hne : i + 1 ≠ k := by omega
      simp [liftName, h, substName, hlt, hne]
    · have hlt : i < k := by omega
      simp [liftName, h, substName, hlt]

/-- **Substitution cancels process lifting.**
Removing an inserted binder cancels lifting throughout the unchanged
π syntax, including nested inputs, restrictions, choice and replication. -/
theorem substProc_liftProc (b : Name) (k : Nat) (p : Proc) :
    substProc b k (liftProc k p) = p := by
  induction p generalizing b k <;>
    simp [substProc, liftProc, substName_liftName, *]

/-- **Injectivity of name lifting.** Binder lifting cannot identify two physical names. -/
theorem liftName_injective (k : Nat) : Function.Injective (liftName k) := by
  intro a b h
  have hs := congrArg (substName (.var k) k) h
  simpa only [substName_liftName] using hs

/-- **Name swap is an involution.** Swapping the same two existing binders twice restores a name. -/
theorem swapNameAt_swapNameAt (k : Nat) (a : Name) :
    swapNameAt k (swapNameAt k a) = a := by
  cases a with
  | const => rfl
  | var i =>
    by_cases h₀ : i = k
    · subst i
      simp [swapNameAt]
    · by_cases h₁ : i = k + 1
      · subst i
        simp [swapNameAt]
      · simp [swapNameAt, h₀, h₁]

/-- **Process swap is an involution.**
Existing process swapping is likewise involutive under every binder. -/
theorem swapProc_swapProc (k : Nat) (p : Proc) :
    swapProc k (swapProc k p) = p := by
  induction p generalizing k <;>
    simp [swapProc, swapNameAt_swapNameAt, *]

/-- **A lifted name is never the innermost binder.**
Existing outer names cannot become the fresh innermost binder. -/
theorem liftName_zero_ne_var_zero (a : Name) : liftName 0 a ≠ .var 0 := by
  cases a <;> simp [liftName]

/-- **Commuting a name lift past a lift at cutoff zero.**
Lifting commutes with entering the innermost name binder. -/
theorem liftName_liftName_zero (k : Nat) (a : Name) :
    liftName (k + 1) (liftName 0 a) = liftName 0 (liftName k a) := by
  cases a with
  | const => rfl
  | var i =>
    by_cases h : k ≤ i <;>
      simp [liftName, Nat.add_le_add_iff_right, h]

/-- **Commutation of name lifts at ordered cutoffs.**
Arbitrary-cutoff lift fusion, including the cutoffs reached under input
and restriction binders. -/
theorem liftName_liftName (j k : Nat) (hjk : j ≤ k) (a : Name) :
    liftName (k + 1) (liftName j a) = liftName j (liftName k a) := by
  cases a with
  | const => rfl
  | var i =>
    by_cases hi : j ≤ i
    · by_cases hk : k ≤ i
      · have hk' : k + 1 ≤ i + 1 := by omega
        have hj' : j ≤ i + 1 := by omega
        simp [liftName, hi, hk, hk', hj']
      · have hk' : ¬ k + 1 ≤ i + 1 := by omega
        simp [liftName, hi, hk, hk']
    · have hk : ¬ k ≤ i := by omega
      have hk' : ¬ k + 1 ≤ i := by omega
      simp [liftName, hi, hk, hk']

/-- **Commutation of process lifts at ordered cutoffs.**
Lift fusion throughout existing π syntax, at arbitrary ordered cutoffs. -/
theorem liftProc_liftProc (j k : Nat) (hjk : j ≤ k) (p : Proc) :
    liftProc (k + 1) (liftProc j p) = liftProc j (liftProc k p) := by
  induction p generalizing j k <;>
    simp [liftProc, liftName_liftName j k hjk, *,
      Nat.add_le_add_right hjk 1]

/-- **Lifting preserves and reflects name scoping.**
At an actual ambient cutoff, lifting reflects as well as preserves
canonical name scoping. It is not a second scope definition. -/
theorem closedAt_liftName_iff (n k : Nat) (hk : k ≤ n) (a : Name) :
    (liftName k a).ClosedAt (n + 1) ↔ a.ClosedAt n := by
  cases a with
  | const => rfl
  | var i =>
    by_cases hki : k ≤ i <;> simp only [liftName, hki, ↓reduceIte, Name.ClosedAt]
    all_goals omega

/-- **Injectivity of name swapping.** Swapping existing binders cannot identify physical names. -/
theorem swapNameAt_injective (k : Nat) : Function.Injective (swapNameAt k) := by
  intro a b h
  have he := congrArg (swapNameAt k) h
  simpa only [swapNameAt_swapNameAt] using he

/-- **A lifted key is never a freshly bound key.**
A lifted outer key can never be either freshly bound role at var zero. -/
theorem Key.lift_ne_bound (e : Key) (r : Role) :
    Key.mapName (liftName 0) e ≠ (⟨.var 0, r⟩ : Key) := by
  intro h
  exact liftName_zero_ne_var_zero e.name (congrArg Key.name h)

end Cslib.SessionTypes.Endpoint
