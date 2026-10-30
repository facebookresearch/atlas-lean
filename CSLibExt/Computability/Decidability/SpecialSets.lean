/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

@[expose] public section

/-!
# Productive, creative, simple and immune sets

Productive, creative, simple and immune sets (Soare, *Recursively Enumerable
Sets and Degrees*, Ch. I, §5 and Ch. III; Rogers, *Theory of Recursive
Functions and Effective Computability*, §8.4–§8.5) are the classical
hierarchy of "effective" smallness and completeness properties of RE sets.
This file defines them (relative to the standard enumeration of RE sets by
`Nat.Partrec.Code`) and proves the easy implications: productive sets are not
RE, immune sets are not RE, simple sets are not computable, and creative
sets are not computable. The existence of simple and immune sets (finite
injury / priority constructions) and the completeness of creative sets
(every RE set many-one reduces to a creative set) are registered as wanted
theorems in `WantedExt/TheoryOfComputation/SimpleSetExistence.lean`,
`WantedExt/TheoryOfComputation/ImmuneSetExistence.lean` and
`WantedExt/TheoryOfComputation/CreativeComplete.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

/-- The `e`-th recursively enumerable set, enumerated by `Nat.Partrec.Code`.
Source: Rogers, *Theory of Recursive Functions and Effective Computability*,
§1.6 (standard enumeration of the partial recursive functions). -/
def enumRE (e n : ℕ) : Prop :=
  (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) n).Dom

/-- A set is **productive** when a partial recursive function witnesses, for
every index `e` of an RE subset of it, a member outside that subset.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.1. -/
def Productive (P : ℕ → Prop) : Prop :=
  ∃ f : ℕ →. ℕ, Partrec f ∧ ∀ e, (∀ n, enumRE e n → P n) →
    ∃ h : (f e).Dom, P ((f e).get h) ∧ ¬ enumRE e ((f e).get h)

/-- A set is **creative** when it is RE and its complement is productive.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.2. -/
def Creative (P : ℕ → Prop) : Prop :=
  REPred P ∧ Productive (fun n ↦ ¬ P n)

/-- A set is **immune** when it is infinite and contains no infinite RE subset.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.4. -/
def Immune (P : ℕ → Prop) : Prop :=
  Set.Infinite {n | P n} ∧ ∀ A : ℕ → Prop, REPred A → (∀ n, A n → P n) →
    Set.Finite {n | A n}

/-- A set is **simple** when it is RE and its complement is immune.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.3. -/
def Simple (P : ℕ → Prop) : Prop :=
  REPred P ∧ Immune (fun n ↦ ¬ P n)

/-- **A productive set is not recursively enumerable**: if it were `Wₑ`, its
productive function would produce a member outside `Wₑ`.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 5.5. -/
theorem productive_not_re {P : ℕ → Prop} (hP : Productive P) : ¬ REPred P := by
  intro hRE
  obtain ⟨f, hf, hprod⟩ := hP
  have hRE' : Partrec (fun a : ℕ ↦ Part.assert (P a) (fun _ ↦ Part.some ())) := hRE
  have hf' : Partrec (fun a : ℕ ↦
      (Part.assert (P a) (fun _ ↦ Part.some ())).map (fun _ ↦ (0 : ℕ))) :=
    hRE'.map (Computable.const (0 : ℕ)).to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf')
  have henum : ∀ n, enumRE (Encodable.encode c) n ↔ P n := fun n ↦ by
    change (Nat.Partrec.Code.eval
      (Denumerable.ofNat Nat.Partrec.Code (Encodable.encode c)) n).Dom ↔ P n
    rw [Denumerable.ofNat_encode, hc]
    change ((Part.assert (P n) (fun _ ↦ Part.some ())).map (fun _ ↦ (0 : ℕ))).Dom ↔ P n
    rw [Part.map_Dom]
    constructor
    · intro hDom
      obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hDom
      obtain ⟨h, -⟩ := Part.mem_assert_iff.1 hz
      exact h
    · intro h
      exact Part.dom_iff_mem.2
        ⟨(), Part.mem_assert h (Part.mem_some_iff.2 rfl)⟩
  obtain ⟨h, hmem, hnot⟩ :=
    hprod (Encodable.encode c) (fun n hn ↦ (henum n).1 hn)
  exact hnot ((henum _).2 hmem)

/-- **An immune set is not recursively enumerable**: it would be an infinite
RE subset of itself.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 5.6. -/
theorem immune_not_re {P : ℕ → Prop} (hP : Immune P) : ¬ REPred P := by
  intro hRE
  obtain ⟨hinf, hfin⟩ := hP
  exact hinf (hfin P hRE (fun _ h ↦ h))

/-- **A simple set is not computable**: its complement would be an infinite
RE set, contradicting immunity.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 5.6. -/
theorem simple_not_computable {P : ℕ → Prop} (hP : Simple P) : ¬ ComputablePred P := by
  intro hcomp
  obtain ⟨-, hinf, hfin⟩ := hP
  have hfin' : Set.Finite {n | ¬ P n} :=
    hfin _ (ComputablePred.not hcomp).to_re (fun _ h ↦ h)
  exact hinf hfin'

/-- **A simple set is recursively enumerable**, by definition.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.3. -/
theorem simple_re {P : ℕ → Prop} (hP : Simple P) : REPred P :=
  hP.1

/-- **The complement of a simple set is immune**, by definition.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.3. -/
theorem simple_complement_immune {P : ℕ → Prop} (hP : Simple P) :
    Immune (fun n ↦ ¬ P n) :=
  hP.2

/-- **A creative set is recursively enumerable**, by definition.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Definition 5.2. -/
theorem creative_re {P : ℕ → Prop} (hP : Creative P) : REPred P :=
  hP.1

/-- **A creative set is not computable**: its complement is productive, hence
not RE, but the complement of a computable set is RE.
Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I, Theorem 5.7. -/
theorem creative_not_computable {P : ℕ → Prop} (hP : Creative P) :
    ¬ ComputablePred P := by
  intro hcomp
  obtain ⟨-, hprod⟩ := hP
  exact productive_not_re hprod (ComputablePred.not hcomp).to_re

end Cslib.Decidability
