/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Crypto.Protocols.DolevYao.Deduction
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

/-!
# Dolev-Yao deduction tests

Checks for ground messages and intruder deduction: worked
decryptions, non-deducibility via closed supersets, monotonicity
and cut, subterm computation, and axiom cleanliness.
-/

set_option autoImplicit false

namespace Cslib.Crypto.Protocols.DolevYao.DeductionTests

/-- Knowledge set from Example 3.3. -/
def S0 : Set (Msg String) :=
  {Msg.pair (Msg.atom "k1") (Msg.atom "k2"),
    Msg.pair (Msg.atom "k3") (Msg.atom "a"),
    Msg.senc (Msg.atom "n") (Msg.pair (Msg.atom "k1") (Msg.atom "k3"))}

/-- Knowledge set from Exercise 1, part 1. -/
def S1 : Set (Msg String) :=
  {Msg.senc (Msg.atom "k2")
    (Msg.pair (Msg.atom "k1") (Msg.senc (Msg.atom "k1") (Msg.atom "k3"))),
    Msg.pair (Msg.atom "k1") (Msg.atom "k1"),
    Msg.senc (Msg.senc (Msg.atom "k1") (Msg.atom "k3")) (Msg.atom "k1")}

private theorem t1_k1 : Deducible S0 (Msg.atom "k1") := by
  have h : Msg.pair (Msg.atom "k1") (Msg.atom "k2") ∈ S0 := by
    simp [S0]
  exact Deducible.fst (Deducible.mem h)

private theorem t1_k3 : Deducible S0 (Msg.atom "k3") := by
  have h : Msg.pair (Msg.atom "k3") (Msg.atom "a") ∈ S0 := by
    simp [S0]
  exact Deducible.fst (Deducible.mem h)

private theorem t1_pair : Deducible S0
    (Msg.pair (Msg.atom "k1") (Msg.atom "k3")) := by
  exact Deducible.pair t1_k1 t1_k3

private theorem t1_n : Deducible S0 (Msg.atom "n") := by
  have h : Msg.senc (Msg.atom "n") (Msg.pair (Msg.atom "k1") (Msg.atom "k3")) ∈ S0 := by
    simp [S0]
  exact Deducible.sdec (Deducible.mem h) t1_pair

example : Deducible S0
    (Msg.pair (Msg.atom "n") (Msg.atom "a")) := by
  have h : Msg.pair (Msg.atom "k3") (Msg.atom "a") ∈ S0 := by
    simp [S0]
  exact Deducible.pair t1_n (Deducible.snd (Deducible.mem h))

private theorem t2_k1 : Deducible S1 (Msg.atom "k1") := by
  have h : Msg.pair (Msg.atom "k1") (Msg.atom "k1") ∈ S1 := by
    simp [S1]
  exact Deducible.fst (Deducible.mem h)

example : Deducible S1 (Msg.atom "k2") := by
  have hs1 : Msg.senc (Msg.senc (Msg.atom "k1") (Msg.atom "k3")) (Msg.atom "k1") ∈ S1 := by
    simp [S1]
  have hs2 : Msg.senc (Msg.atom "k2")
      (Msg.pair (Msg.atom "k1") (Msg.senc (Msg.atom "k1") (Msg.atom "k3"))) ∈ S1 := by
    simp [S1]
  have ds : Deducible S1 (Msg.senc (Msg.atom "k1") (Msg.atom "k3")) :=
    Deducible.sdec (Deducible.mem hs1) t2_k1
  have dp : Deducible S1 (Msg.pair (Msg.atom "k1")
      (Msg.senc (Msg.atom "k1") (Msg.atom "k3"))) :=
    Deducible.pair t2_k1 ds
  exact Deducible.sdec (Deducible.mem hs2) dp

example : Deducible {Msg.aenc (Msg.atom "s") (Msg.pk (Msg.atom "k")), Msg.atom "k"}
    (Msg.atom "s") := by
  have h1 : Msg.aenc (Msg.atom "s") (Msg.pk (Msg.atom "k")) ∈
      ({Msg.aenc (Msg.atom "s") (Msg.pk (Msg.atom "k")), Msg.atom "k"} : Set (Msg String)) := by
    simp
  have h2 : Msg.atom "k" ∈
      ({Msg.aenc (Msg.atom "s") (Msg.pk (Msg.atom "k")), Msg.atom "k"} : Set (Msg String)) := by
    simp
  exact Deducible.adec (Deducible.mem h1) (Deducible.mem h2)

example : Deducible {Msg.pk (Msg.atom "k"), Msg.atom "m"}
    (Msg.aenc (Msg.atom "m") (Msg.pk (Msg.atom "k"))) := by
  have h1 : Msg.atom "m" ∈
      ({Msg.pk (Msg.atom "k"), Msg.atom "m"} : Set (Msg String)) := by
    simp
  have h2 : Msg.pk (Msg.atom "k") ∈
      ({Msg.pk (Msg.atom "k"), Msg.atom "m"} : Set (Msg String)) := by
    simp
  exact Deducible.aenc (Deducible.mem h1) (Deducible.mem h2)

example (a b : String) (h : b ≠ a) :
    ¬ Deducible {Msg.atom a} (Msg.atom b) := by
  intro d
  have hSub : ({Msg.atom a} : Set (Msg String)) ⊆ {m | Msg.atom b ∉ m.subterms} := by
    simp [Set.mem_ofPred_eq, Msg.subterms, Finset.mem_singleton, h]
  have hPair :
      ∀ m n : Msg String,
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        n ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        Msg.pair m n ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m n h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hFst :
      ∀ m n : Msg String,
        Msg.pair m n ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m n h hm
    exact h (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hSnd :
      ∀ m n : Msg String,
        Msg.pair m n ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        n ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m n h hm
    exact h (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hSenc :
      ∀ m k : Msg String,
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        Msg.senc m k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m k h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hSdec :
      ∀ m k : Msg String,
        Msg.senc m k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m k h1 _ hm
    exact h1 (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hAenc :
      ∀ m k : Msg String,
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        Msg.aenc m k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m k h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hAdec :
      ∀ m k : Msg String,
        Msg.aenc m (Msg.pk k) ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        k ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.atom b ∉ m.subterms} : Set (Msg String)) := by
    intro m k h1 _ hm
    exact h1 (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hC :=
    Deducible.of_subset_closure (S := {Msg.atom a})
      (C := {m | Msg.atom b ∉ m.subterms}) (m := Msg.atom b)
      hSub hPair hFst hSnd hSenc hSdec hAenc hAdec d
  simp at hC
  exact hC (Msg.mem_subterms_self _)

example (m : Msg String) : ¬ Deducible ∅ m := by
  intro d
  have hC :=
    Deducible.of_subset_closure (S := (∅ : Set (Msg String)))
      (C := (∅ : Set (Msg String))) (m := m)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) d
  simp at hC

example (k : String) :
    ¬ Deducible {Msg.atom k} (Msg.pk (Msg.atom k)) := by
  intro d
  have hSub : ({Msg.atom k} : Set (Msg String)) ⊆ {m | Msg.pk (Msg.atom k) ∉ m.subterms} := by
    simp [Set.mem_ofPred_eq, Msg.subterms, Finset.mem_singleton]
  have hPair :
      ∀ m n : Msg String,
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        n ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        Msg.pair m n ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m n h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hFst :
      ∀ m n : Msg String,
        Msg.pair m n ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m n h hm
    exact h (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hSnd :
      ∀ m n : Msg String,
        Msg.pair m n ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        n ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m n h hm
    exact h (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hSenc :
      ∀ m k2 : Msg String,
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        Msg.senc m k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m k2 h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hSdec :
      ∀ m k2 : Msg String,
        Msg.senc m k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m k2 h1 _ hm
    exact h1 (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hAenc :
      ∀ m k2 : Msg String,
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        Msg.aenc m k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m k2 h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    simp [Msg.subterms, h1, h2]
  have hAdec :
      ∀ m k2 : Msg String,
        Msg.aenc m (Msg.pk k2) ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        k2 ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) →
        m ∈ ({m | Msg.pk (Msg.atom k) ∉ m.subterms} : Set (Msg String)) := by
    intro m k2 h1 _ hm
    exact h1 (Msg.subterms_trans hm (by simp [Msg.subterms, Msg.mem_subterms_self]))
  have hC :=
    Deducible.of_subset_closure (S := {Msg.atom k})
      (C := {m | Msg.pk (Msg.atom k) ∉ m.subterms}) (m := Msg.pk (Msg.atom k))
      hSub hPair hFst hSnd hSenc hSdec hAenc hAdec d
  simp at hC
  exact hC (Msg.mem_subterms_self _)

example : Deducible (S0 ∪ {Msg.atom "extra"})
    (Msg.atom "k1") := by
  exact Deducible.mono (by simp) t1_k1

example : Deducible S0
    (Msg.pair (Msg.atom "k1") (Msg.atom "k3")) := by
  have hT : ∀ t ∈ S0, Deducible S0 t := fun t ht => Deducible.mem ht
  exact Deducible.cut hT t1_pair

example : Msg.atom "k1" ∈
    (Msg.senc (Msg.pair (Msg.atom "k1") (Msg.atom "k2")) (Msg.atom "k3")).subterms := by
  decide

example : Msg.atom "k3" ∈
    (Msg.senc (Msg.pair (Msg.atom "k1") (Msg.atom "k2")) (Msg.atom "k3")).subterms := by
  decide

example : Msg.atom "n" ∉
    (Msg.senc (Msg.pair (Msg.atom "k1") (Msg.atom "k2")) (Msg.atom "k3")).subterms := by
  decide

#print axioms Msg.mem_subterms_self
#print axioms Msg.subterms_trans
#print axioms Deducible.mono
#print axioms Deducible.cut
#print axioms Deducible.of_subset_closure

end Cslib.Crypto.Protocols.DolevYao.DeductionTests
