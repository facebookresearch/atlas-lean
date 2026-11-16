/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# CTL EX pre-image

For a Kripke structure on `Fin n`, the EX pre-image of a
state set `S` is the set of states with a successor in
`S`. It is monotone and distributes over unions; the
EU/EG fixpoint iterations build on it and are not included
here.
-/

@[expose] public section

/-- Kripke structures on `Fin n` (CTL core of VER-36):
transition relation and atomic labeling. -/
structure Kripke (n : ℕ) where
  step : Fin n → Finset (Fin n)
  label : Fin n → Finset ℕ

/-- EX model checking: the set of states with a successor in
`S`. -/
def Kripke.pre {n : ℕ} (K : Kripke n) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun s => ∃ t ∈ S, t ∈ K.step s)

/-- A state is in the EX pre-image exactly when it has a
successor in `S`. -/
theorem Kripke.mem_pre {n : ℕ} (K : Kripke n) (S : Finset (Fin n))
    (s : Fin n) :
    s ∈ K.pre S ↔ ∃ t ∈ S, t ∈ K.step s := by
  simp [Kripke.pre]

/-- Monotonicity of the pre-image operator (the fixpoint
iterations for EU/EG build on this). -/
theorem Kripke.pre_mono {n : ℕ} (K : Kripke n)
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    K.pre S ⊆ K.pre T := by
  intro s hs
  rw [Kripke.mem_pre] at hs ⊢
  obtain ⟨t, htS, htstep⟩ := hs
  exact ⟨t, h htS, htstep⟩

/-- The pre-image of the union is the union of pre-images. -/
theorem Kripke.pre_union {n : ℕ} (K : Kripke n)
    (S T : Finset (Fin n)) :
    K.pre (S ∪ T) = K.pre S ∪ K.pre T := by
  ext s
  simp only [Kripke.mem_pre, Finset.mem_union]
  constructor
  · rintro ⟨t, ht | ht, hts⟩
    · exact Or.inl ⟨t, ht, hts⟩
    · exact Or.inr ⟨t, ht, hts⟩
  · rintro (⟨t, ht, hts⟩ | ⟨t, ht, hts⟩)
    · exact ⟨t, Or.inl ht, hts⟩
    · exact ⟨t, Or.inr ht, hts⟩

end
