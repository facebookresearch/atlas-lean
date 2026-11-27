/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Topology.Constructions
import MathlibExt.Combinatorics.Additive.SidonIdealSidonIdealIsFSigma

namespace MathlibExtTest.Combinatorics.Additive.SidonIdealSidonIdealIsFSigma

open MetaMathlibExt

/-- The closed pieces from `sidonIdeal_isFSigma` cover the empty indicator: the
empty set is covered by no Sidon sets. -/
example : (fun _ => false) ∈ ⋃ k, Classical.choose sidonIdeal_isFSigma k := by
  obtain ⟨_, hunion⟩ := Classical.choose_spec sidonIdeal_isFSigma
  rw [← hunion]
  show {n : ℕ | (fun _ => false) n = true} ∈ sidonIdeal
  have hempty : {n : ℕ | (fun _ => false) n = true} = ∅ := by
    ext n
    simp
  rw [hempty]
  exact ⟨0, fun j => j.elim0, fun j => j.elim0, Set.empty_subset _⟩

/-- The closed pieces from `sidonIdeal_isFSigma` cover the indicator of `{5}`:
singletons are Sidon sets. -/
example : (fun n => decide (n = 5)) ∈ ⋃ k, Classical.choose sidonIdeal_isFSigma k := by
  obtain ⟨_, hunion⟩ := Classical.choose_spec sidonIdeal_isFSigma
  rw [← hunion]
  show {n : ℕ | (fun n => decide (n = 5)) n = true} ∈ sidonIdeal
  have hset : {n : ℕ | (fun n => decide (n = 5)) n = true} = {5} := by
    ext n
    simp
  rw [hset]
  apply mem_generatedIdeal
  intro a ha b hb c hc d hd _
  simp only [Set.mem_singleton_iff] at ha hb hc hd
  subst ha
  subst hb
  subst hc
  subst hd
  exact Or.inl ⟨rfl, rfl⟩

/-- Each piece of the decomposition from `sidonIdeal_isFSigma` is closed. -/
example (k : ℕ) : IsClosed (Classical.choose sidonIdeal_isFSigma k) :=
  (Classical.choose_spec sidonIdeal_isFSigma).1 k

/-- Membership in the union from `sidonIdeal_isFSigma` implies membership in the
Sidon ideal: the reverse direction of the defining equality. -/
example (f : ℕ → Bool) (hf : f ∈ ⋃ k, Classical.choose sidonIdeal_isFSigma k) :
    {n | f n = true} ∈ sidonIdeal := by
  obtain ⟨_, hunion⟩ := Classical.choose_spec sidonIdeal_isFSigma
  rw [← hunion] at hf
  exact hf

end MathlibExtTest.Combinatorics.Additive.SidonIdealSidonIdealIsFSigma
