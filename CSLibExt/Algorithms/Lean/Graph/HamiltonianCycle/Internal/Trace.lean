/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Internal.Prefix
import Mathlib.Data.List.Chain

/-!
# Private complete traversal proof for binary Hamiltonian certificates

This module transports the actual saved state through canonical `List.forIn`.
Decoded vertices are proof witnesses, never an input oracle for the executor.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

lemma prefix_legal_append (x : Array Bool) (m : Nat) (vs : List (Fin m)) (v : Fin m)
    (hnd : vs.Nodup)
    (hch : vs.IsChain (fun a b => x[a.val * m + b.val]?.getD false = true))
    (hf : v ∉ vs)
    (he : ∀ p, vs.getLast? = some p → x[p.val * m + v.val]?.getD false = true) :
    (vs ++ [v]).Nodup ∧
      (vs ++ [v]).IsChain (fun a b => x[a.val * m + b.val]?.getD false = true) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = v := by simpa using hb
    subst b
    exact fun h => hf (h ▸ ha)
  · rw [List.isChain_append]
    refine ⟨hch, .singleton v, ?_⟩
    intro p hp b hb
    have hb' : b = v := by simpa using hb.symm
    subst b
    exact he p hp

lemma forIn_prefix_sound (x y : Array Bool) (m w : Nat) (hsize : y.size = m * w)
    (indices vs : List (Fin m)) (hnd : vs.Nodup)
    (hch : vs.IsChain (fun a b => x[a.val * m + b.val]?.getD false = true))
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m))
    (hs : (forIn indices (prefixState vs) (sourceStep x y m w)).ret = s)
    (hflag : s.1 = none) :
    ∃ us : List (Fin m), s = prefixState (vs ++ us) ∧
      List.Forall₂ (fun i v => Nat.ofDigits 2
        ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
        indices us ∧ (vs ++ us).Nodup ∧
      (vs ++ us).IsChain (fun a b => x[a.val * m + b.val]?.getD false = true) := by
  induction indices generalizing vs s with
  | nil =>
    simp only [List.forIn_nil, TimeM.ret_pure] at hs
    subst s
    exact ⟨[], by simp, .nil, by simpa using hnd, by simpa using hch⟩
  | cons i indices ih =>
    rw [List.forIn_cons] at hs
    simp only [TimeM.ret_bind] at hs
    cases hstep : (sourceStep x y m w i (prefixState vs)).ret with
    | done t =>
      have hf := sourceStep_flags x y m w i (prefixState vs)
      have hf' : t.1 = some false := by simpa only [hstep] using hf
      have ht : t = s := by simpa only [hstep, TimeM.ret_pure] using hs
      have hn := hf'.symm.trans ((congrArg Prod.fst ht).trans hflag)
      cases hn
    | yield t =>
      simp only [hstep] at hs
      obtain ⟨v, hv, hf, he, rfl⟩ := sourceStep_prefix_yield_info x y m w i vs hsize t hstep
      have hleg := prefix_legal_append x m vs v hnd hch hf he
      obtain ⟨us, hs', halign, hn, hc⟩ := ih (vs ++ [v]) hleg.1 hleg.2 s hs hflag
      refine ⟨v :: us, ?_, .cons hv halign, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using hs'
      · simpa only [List.append_assoc, List.singleton_append] using hn
      · simpa only [List.append_assoc, List.singleton_append] using hc

lemma forIn_flags (x y : Array Bool) (m w : Nat) (indices : List (Fin m))
    (s : Option Bool × Vector Bool m × Option (Fin m) × Option (Fin m)) (hs : s.1 = none) :
    (forIn indices s (sourceStep x y m w)).ret.1 = none ∨
      (forIn indices s (sourceStep x y m w)).ret.1 = some false := by
  induction indices generalizing s with
  | nil => simpa only [List.forIn_nil, TimeM.ret_pure] using Or.inl hs
  | cons i indices ih =>
    rw [List.forIn_cons]
    simp only [TimeM.ret_bind]
    have hf := sourceStep_flags x y m w i s
    cases hstep : (sourceStep x y m w i s).ret with
    | done t =>
      have ht : t.1 = some false := by simpa only [hstep] using hf
      simpa only [hstep, TimeM.ret_pure] using Or.inr ht
    | yield t =>
      have ht : t.1 = none := by simpa only [hstep] using hf
      simpa only [hstep] using ih t ht

lemma forIn_prefix_complete (x y : Array Bool) (m w : Nat) (hsize : y.size = m * w)
    (indices us vs : List (Fin m))
    (halign : List.Forall₂ (fun i v => Nat.ofDigits 2
      ((y.toList.drop (i.val * w)).take w |>.map fun bit => if bit then 1 else 0) = v.val)
      indices us) (hnd : (vs ++ us).Nodup)
    (hch : (vs ++ us).IsChain (fun a b => x[a.val * m + b.val]?.getD false = true)) :
    (forIn indices (prefixState vs) (sourceStep x y m w)).ret = prefixState (vs ++ us) := by
  induction halign generalizing vs with
  | nil => simp only [List.forIn_nil, TimeM.ret_pure, List.append_nil]
  | @cons i v indices us hv halign ih =>
    have hf : v ∉ vs := by
      intro h
      exact (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    have he : ∀ p, vs.getLast? = some p → x[p.val * m + v.val]?.getD false = true := by
      intro p hp
      exact (List.isChain_append.mp hch).2.2 p hp v (by simp)
    have hn : ((vs ++ [v]) ++ us).Nodup := by
      simpa only [List.append_assoc, List.singleton_append] using hnd
    have hc : ((vs ++ [v]) ++ us).IsChain
        (fun a b => x[a.val * m + b.val]?.getD false = true) := by
      simpa only [List.append_assoc, List.singleton_append] using hch
    rw [List.forIn_cons]
    simp only [TimeM.ret_bind, sourceStep_prefix_yield x y m w i v vs hsize hv hf he]
    simpa only [List.append_assoc, List.singleton_append] using ih (vs ++ [v]) hn hc

end Cslib.Algorithms.Lean.Graph
