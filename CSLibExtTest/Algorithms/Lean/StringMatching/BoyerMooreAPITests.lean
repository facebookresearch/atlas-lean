/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.BoyerMoore

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean.StringMatching
open Cslib.Algorithms.Lean.StringMatching.BoyerMoore

example {σ : Nat} (p t : List (Fin σ)) (s : Nat) :
    s ∈ (boyerMooreMatches p t).ret ↔ MatchAt p t s :=
  mem_boyerMooreMatches_iff p t s

example {σ : Nat} (p t : List (Fin σ)) :
    (boyerMooreMatches p t).ret.Pairwise (· < ·) :=
  boyerMooreMatches_pairwise p t

example {σ : Nat} (p t : List (Fin σ)) :
    (boyerMooreMatches p t).ret = (naiveMatches p t).ret :=
  boyerMooreMatches_eq_naiveMatches p t

example {σ : Nat} (p t : List (Fin σ)) :
    (boyerMooreMatches p t).time ≤
      if p.length = 0 then t.length + 1 else if t.length < p.length then 0
      else σ + t.length + 11 * p.length - 6 + (p.length + 4) * (t.length - p.length + 1) :=
  boyerMooreMatches_time_le p t

example {σ : Nat} (t : List (Fin σ)) :
    boyerMooreMatches [] t = ⟨List.range (t.length + 1), t.length + 1⟩ :=
  boyerMooreMatches_nil_pattern t

example {σ : Nat} (p t : List (Fin σ)) (h : t.length < p.length) :
    boyerMooreMatches p t = pure [] :=
  boyerMooreMatches_of_length_lt p t h

example {σ : Nat} (x : Fin σ) (m n : Nat) (hm : 0 < m) (hlen : m ≤ n) :
    (boyerMooreMatches (List.replicate m x) (List.replicate n x)).time =
      m + n + (preprocess (List.replicate m x).toArray.toVector).time +
        (m + 4) * (n - m + 1) :=
  boyerMooreMatches_time_replicate x m n hm hlen

example {σ : Nat} (a b : Fin σ) (m n : Nat) (hab : a ≠ b) (hm : 2 ≤ m) (hlen : m ≤ n) :
    (boyerMooreMatches (List.replicate (m - 1) a ++ [b]) (List.replicate n b)).time =
      m + n + (preprocess (List.replicate (m - 1) a ++ [b]).toArray.toVector).time +
        4 * (n / m) :=
  boyerMooreMatches_time_replicate_append a b m n hab hm hlen
