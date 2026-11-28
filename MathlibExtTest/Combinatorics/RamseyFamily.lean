/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RamseyFamily

/-! # Tests for ultrafilters in Ramsey families -/

namespace MetaMathlibExt.betaFamily_isLeftIdeal_iff.Tests

private theorem contains_true_isRamseyFamily : IsRamseyFamily {A : Set Bool | true ∈ A} :=
  ⟨⟨Set.univ, Set.mem_univ true⟩, id, fun _ _ hA hAB => hAB hA, fun _ _ h => h⟩

-- The singleton {false} excludes the principal ultrafilter at false even from the closure.
example : (pure false : Ultrafilter Bool) ∉ closure (betaFamily {A : Set Bool | true ∈ A}) := by
  rw [(isClosed_betaFamily contains_true_isRamseyFamily).closure_eq]
  intro h
  exact Bool.noConfusion (h {false} (by simp))

attribute [local instance] Ultrafilter.semigroup

section

local instance rightZero : Semigroup Bool where
  mul _ y := y
  mul_assoc _ _ _ := rfl

-- For x * y = y, every left translation fixes every set.
example : ∀ p : Ultrafilter Bool, ∀ q ∈ betaFamily {A : Set Bool | true ∈ A},
    p * q ∈ betaFamily {A : Set Bool | true ∈ A} := by
  apply (betaFamily_isLeftIdeal_iff contains_true_isRamseyFamily).2
  exact fun _ _ hE => ⟨true, hE, rfl⟩

end

section

local instance leftZero : Semigroup Bool where
  mul x _ := x
  mul_assoc _ _ _ := rfl

-- For x * y = x, translating {true} by false gives {false}.
example : ¬ ∀ p : Ultrafilter Bool, ∀ q ∈ betaFamily {A : Set Bool | true ∈ A},
    p * q ∈ betaFamily {A : Set Bool | true ∈ A} := by
  intro hleft
  obtain ⟨_, _, h⟩ := (betaFamily_isLeftIdeal_iff contains_true_isRamseyFamily).1 hleft
    false {true} (Set.mem_singleton true)
  exact Bool.noConfusion h

end

end MetaMathlibExt.betaFamily_isLeftIdeal_iff.Tests

namespace MetaMathlibExt.isRamseyFamily_and_betaFamily_eq_of_isClosed.Tests

-- A principal singleton gives exactly the sets containing its point.
example : IsRamseyFamily {A : Set Bool | true ∈ A} ∧
    betaFamily {A : Set Bool | true ∈ A} = {pure true} := by
  simpa using isRamseyFamily_and_betaFamily_eq_of_isClosed
    (isClosed_singleton (x := (pure true : Ultrafilter Bool))) (Set.singleton_nonempty _)

-- The empty closed set gives an empty family, so nonemptiness is essential.
example : ¬ IsRamseyFamily {A : Set Bool | ∃ p ∈ (∅ : Set (Ultrafilter Bool)), A ∈ p} := by
  rintro ⟨⟨A, p, hp, _⟩, _⟩
  exact hp

end MetaMathlibExt.isRamseyFamily_and_betaFamily_eq_of_isClosed.Tests

namespace MetaMathlibExt.mem_iff_exists_mem_betaFamily.Tests

-- Every infinite set of naturals has a witnessing ultrafilter that contains no singleton.
example {A : Set ℕ} (hA : A.Infinite) :
    ∃ p : Ultrafilter ℕ, A ∈ p ∧ ∀ n : ℕ, ({n} : Set ℕ) ∉ p := by
  have hF : IsRamseyFamily {B : Set ℕ | B.Infinite} :=
    ⟨⟨Set.univ, Set.infinite_univ⟩, fun h => h Set.finite_empty,
      fun _ _ h hsub => Set.Infinite.mono hsub h, fun _ _ => Set.infinite_union.mp⟩
  obtain ⟨p, hp, hAp⟩ := (mem_iff_exists_mem_betaFamily hF A).mp hA
  exact ⟨p, hAp, fun n hn => hp {n} hn (Set.finite_singleton n)⟩

end MetaMathlibExt.mem_iff_exists_mem_betaFamily.Tests

namespace MetaMathlibExt.betaFamily_isSubsemigroup_iff.Tests

attribute [local instance] Ultrafilter.semigroup

section

local instance rightZero : Semigroup Bool where
  mul _ y := y
  mul_assoc _ _ _ := rfl

-- In the right-zero semigroup, the singleton test recovers E itself.
example {F : Set (Set Bool)} (hF : IsRamseyFamily F) :
    ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F := by
  apply (betaFamily_isSubsemigroup_iff hF).2
  rintro E ⟨A, hA, hfinite⟩
  obtain ⟨p, _, hp⟩ := (mem_iff_exists_mem_betaFamily hF A).mp hA
  obtain ⟨x, hx⟩ := Ultrafilter.nonempty_of_mem hp
  have h := hfinite {x} (by simpa using hx)
  simp at h
  exact h

end

-- The principal ultrafilter at 2 is not idempotent: the criterion fails with A = {2}, E = {4}.
example : ¬ ∀ p ∈ betaFamily {A : Set ℕ | 2 ∈ A},
    ∀ q ∈ betaFamily {A : Set ℕ | 2 ∈ A}, p * q ∈ betaFamily {A : Set ℕ | 2 ∈ A} := by
  have hF : IsRamseyFamily {A : Set ℕ | 2 ∈ A} := by
    simpa using (isRamseyFamily_and_betaFamily_eq_of_isClosed
      (isClosed_singleton (x := (pure 2 : Ultrafilter ℕ))) (Set.singleton_nonempty _)).1
  intro hmul
  have h4 := (betaFamily_isSubsemigroup_iff hF).1 hmul {4}
    ⟨{2}, Set.mem_singleton 2, fun H hH => Set.mem_iInter₂.mpr fun x hx => by
      have hx2 : x = 2 := hH hx
      subst x
      exact Set.mem_singleton 4⟩
  exact (by decide : (2 : ℕ) ∉ ({4} : Set ℕ)) h4

end MetaMathlibExt.betaFamily_isSubsemigroup_iff.Tests
