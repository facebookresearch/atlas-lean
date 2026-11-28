/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Dolev-Yao messages and intruder deduction

Ground message terms and the intruder deduction relation from
Cortier and Kremer, "Formal Models and Techniques for Analyzing
Security Protocols", Section 3, Figure 3.1.

Model boundaries: ground terms only over atoms; signature
pair, senc, aenc, pk; no public-key composition rule; knowledge
sets are arbitrary sets; no decision procedure, locality,
equational theories, signatures, hashes, or active intruders.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace Cslib.Crypto.Protocols.DolevYao

/-- Ground Dolev-Yao message terms over atoms of type `A`. -/
inductive Msg (A : Type u) : Type u where
| atom : A → Msg A
| pair : Msg A → Msg A → Msg A
| senc : Msg A → Msg A → Msg A
| aenc : Msg A → Msg A → Msg A
| pk : Msg A → Msg A
deriving DecidableEq

/-- Subterms of a message, including the message itself. -/
def Msg.subterms {A : Type u} [DecidableEq A] : Msg A → Finset (Msg A)
| .atom a => {.atom a}
| .pair m n => {Msg.pair m n} ∪ m.subterms ∪ n.subterms
| .senc m k => {Msg.senc m k} ∪ m.subterms ∪ k.subterms
| .aenc m k => {Msg.aenc m k} ∪ m.subterms ∪ k.subterms
| .pk k => {Msg.pk k} ∪ k.subterms

/-- Every message is a subterm of itself. -/
theorem Msg.mem_subterms_self {A : Type u} [DecidableEq A]
(m : Msg A) : m ∈ m.subterms := by
  cases m <;> simp [Msg.subterms]

/-- Subterm membership is transitive. -/
theorem Msg.subterms_trans {A : Type u} [DecidableEq A]
{m n p : Msg A} :
m ∈ n.subterms → n ∈ p.subterms → m ∈ p.subterms := by
  induction p with
  | atom a =>
    intro h1 h2
    simp [Msg.subterms] at h2 ⊢
    subst h2
    simpa [Msg.subterms] using h1
  | pair x y ihx ihy =>
    intro h1 h2
    simp [Msg.subterms] at h2 ⊢
    rcases h2 with rfl | h | h
    · simpa [Msg.subterms] using h1
    · have hmx := ihx h1 h; simp [hmx]
    · have hmy := ihy h1 h; simp [hmy]
  | senc x y ihx ihy =>
    intro h1 h2
    simp [Msg.subterms] at h2 ⊢
    rcases h2 with rfl | h | h
    · simpa [Msg.subterms] using h1
    · have hmx := ihx h1 h; simp [hmx]
    · have hmy := ihy h1 h; simp [hmy]
  | aenc x y ihx ihy =>
    intro h1 h2
    simp [Msg.subterms] at h2 ⊢
    rcases h2 with rfl | h | h
    · simpa [Msg.subterms] using h1
    · have hmx := ihx h1 h; simp [hmx]
    · have hmy := ihy h1 h; simp [hmy]
  | pk x ih =>
    intro h1 h2
    simp [Msg.subterms] at h2 ⊢
    rcases h2 with rfl | h
    · simpa [Msg.subterms] using h1
    · have hmx := ih h1 h; simp [hmx]

/-- Intruder deduction from `S` by the Figure 3.1 rules. -/
inductive Deducible {A : Type u} (S : Set (Msg A)) : Msg A → Prop where
| mem {m : Msg A} : m ∈ S → Deducible S m
| pair {m n : Msg A} :
Deducible S m → Deducible S n → Deducible S (Msg.pair m n)
| fst {m n : Msg A} : Deducible S (Msg.pair m n) → Deducible S m
| snd {m n : Msg A} : Deducible S (Msg.pair m n) → Deducible S n
| senc {m k : Msg A} :
Deducible S m → Deducible S k → Deducible S (Msg.senc m k)
| sdec {m k : Msg A} :
Deducible S (Msg.senc m k) → Deducible S k → Deducible S m
| aenc {m k : Msg A} :
Deducible S m → Deducible S k → Deducible S (Msg.aenc m k)
| adec {m k : Msg A} :
Deducible S (Msg.aenc m (Msg.pk k)) →
Deducible S k → Deducible S m

/-- Notation for intruder deduction. -/
scoped infix:50 " ⊢ " => Deducible

/-- Deduction is monotone in the knowledge set. -/
theorem Deducible.mono {A : Type u} {S T : Set (Msg A)} {m : Msg A} :
S ⊆ T → Deducible S m → Deducible T m := by
  intro h d
  induction d with
  | mem hm => exact mem (h hm)
  | pair _ _ i1 i2 => exact pair i1 i2
  | fst _ i => exact fst i
  | snd _ i => exact snd i
  | senc _ _ i1 i2 => exact senc i1 i2
  | sdec _ _ i1 i2 => exact sdec i1 i2
  | aenc _ _ i1 i2 => exact aenc i1 i2
  | adec _ _ i1 i2 => exact adec i1 i2

/-- Cut: deducible premises can be inlined into derivations. -/
theorem Deducible.cut {A : Type u} {S T : Set (Msg A)} {m : Msg A} :
(∀ t ∈ T, Deducible S t) → Deducible T m → Deducible S m := by
  intro h d
  induction d with
  | mem hm => exact h _ hm
  | pair _ _ i1 i2 => exact pair i1 i2
  | fst _ i => exact fst i
  | snd _ i => exact snd i
  | senc _ _ i1 i2 => exact senc i1 i2
  | sdec _ _ i1 i2 => exact sdec i1 i2
  | aenc _ _ i1 i2 => exact aenc i1 i2
  | adec _ _ i1 i2 => exact adec i1 i2

/-- Rule-closed supersets contain every deducible message. -/
theorem Deducible.of_subset_closure {A : Type u} {S C : Set (Msg A)}
{m : Msg A} (hSub : S ⊆ C)
(hPair : ∀ m n, m ∈ C → n ∈ C → Msg.pair m n ∈ C)
(hFst : ∀ m n, Msg.pair m n ∈ C → m ∈ C)
(hSnd : ∀ m n, Msg.pair m n ∈ C → n ∈ C)
(hSenc : ∀ m k, m ∈ C → k ∈ C → Msg.senc m k ∈ C)
(hSdec : ∀ m k, Msg.senc m k ∈ C → k ∈ C → m ∈ C)
(hAenc : ∀ m k, m ∈ C → k ∈ C → Msg.aenc m k ∈ C)
(hAdec : ∀ m k, Msg.aenc m (Msg.pk k) ∈ C → k ∈ C → m ∈ C)
(d : Deducible S m) : m ∈ C := by
  induction d with
  | mem hm => exact hSub hm
  | pair _ _ i1 i2 => exact hPair _ _ i1 i2
  | fst _ i => exact hFst _ _ i
  | snd _ i => exact hSnd _ _ i
  | senc _ _ i1 i2 => exact hSenc _ _ i1 i2
  | sdec _ _ i1 i2 => exact hSdec _ _ i1 i2
  | aenc _ _ i1 i2 => exact hAenc _ _ i1 i2
  | adec _ _ i1 i2 => exact hAdec _ _ i1 i2

end Cslib.Crypto.Protocols.DolevYao

end
