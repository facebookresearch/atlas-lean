/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Hardy–Littlewood prime-tuple data

Reusable definitions from the Hardy–Littlewood prime-tuple conjecture block
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`).

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL21/Miller/miller8.tex>.
-/

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- Number of distinct residues of the tuple `b` modulo `p`, i.e. the source's
`v_p(b)` (statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
def hardyLittlewoodResidueCount (m : ℕ) (b : Fin m → ℤ) (p : ℕ) : ℕ :=
  (Finset.univ.image (fun i => (b i) % (p : ℤ))).card

/-- Admissibility of the tuple `b`: `v_p(b) ≠ p` for every prime `p`
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
def IsHardyLittlewoodAdmissible (m : ℕ) (b : Fin m → ℤ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → hardyLittlewoodResidueCount m b p ≠ p

/-- The source's `P(x; b)`: number of integers `1 ≤ n ≤ x` for which every
`n + bᵢ` is (a natural) prime
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodPrimeTupleCount (m : ℕ) (b : Fin m → ℤ) (x : ℕ) : ℕ :=
  Set.ncard { n : ℕ | 1 ≤ n ∧ n ≤ x ∧ ∀ i, ∃ q : ℕ, Nat.Prime q ∧ (n : ℤ) + b i = (q : ℤ) }

/-- Euler factor `(p / (p - 1)) ^ (m - 1) * ((p - v_p(b)) / (p - 1))` of the
singular series (statement `jis_43e1aedfa0e84467b1f1765e`,
concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodEulerFactor (m : ℕ) (b : Fin m → ℤ) (p : ℕ) : ℝ :=
  ((p : ℝ) / ((p : ℝ) - 1)) ^ (m - 1) *
    (((p : ℝ) - (hardyLittlewoodResidueCount m b p : ℝ)) / ((p : ℝ) - 1))

/-- Singular series `𝔖(b)`: Euler product over all primes of the Euler factors
(statement `jis_43e1aedfa0e84467b1f1765e`, concept `jis_sem_c814202d5e6a0edd6fed8bb5`). -/
noncomputable def hardyLittlewoodSingularSeries (m : ℕ) (b : Fin m → ℤ) : ℝ :=
  ∏' (p : ℕ), (if Nat.Prime p then hardyLittlewoodEulerFactor m b p else 1)

/-- A finite set `H` of integers is admissible if for every prime `p` its elements miss some
residue class mod `p`; the `Finset` form of `IsHardyLittlewoodAdmissible`
(`isHardyLittlewoodAdmissible_iff_isAdmissibleFinset`).

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 1. -/
def IsAdmissibleFinset (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- For a prime `p`, `v_p(b) ≠ p` exactly when the entries of `b` miss a residue class mod `p`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 1. -/
theorem hardyLittlewoodResidueCount_ne_iff (m : ℕ) (b : Fin m → ℤ) {p : ℕ} (hp : p.Prime) :
    hardyLittlewoodResidueCount m b p ≠ p ↔
      ∃ r : ZMod p, ∀ i, (b i : ZMod p) ≠ r := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  set S := Finset.univ.image fun i => b i % (p : ℤ) with hS
  have hsub : S ⊆ Finset.Ico 0 (p : ℤ) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hp0.ne', Int.emod_lt_of_pos _ hp0⟩
  have hcard : (Finset.Ico 0 (p : ℤ)).card = p := by simp
  have hiff : ∀ i (r : ℤ), 0 ≤ r → r < p → ((b i : ZMod p) = (r : ZMod p) ↔ b i % p = r) := by
    intro i r hr0 hrp
    rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hr0 hrp]
  unfold hardyLittlewoodResidueCount
  rw [← hS]
  constructor
  · intro hne
    have hne' : S ≠ Finset.Ico 0 (p : ℤ) := fun h => hne (h ▸ hcard)
    obtain ⟨r, hr, hrS⟩ : ∃ r ∈ Finset.Ico 0 (p : ℤ), r ∉ S := by
      by_contra hcon
      push Not at hcon
      exact hne' (Finset.Subset.antisymm hsub hcon)
    obtain ⟨hr0, hrp⟩ := Finset.mem_Ico.mp hr
    refine ⟨r, fun i hi => hrS ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (hiff i r hr0 hrp).mp hi⟩
  · rintro ⟨r, hr⟩ heq
    have hSeq : S = Finset.Ico 0 (p : ℤ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, heq])
    have := Fact.mk hp
    have hmem : (r.val : ℤ) ∈ S := by
      rw [hSeq]
      exact Finset.mem_Ico.mpr ⟨by positivity, by exact_mod_cast r.val_lt⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    apply hr i
    rw [← ZMod.natCast_zmod_val r, ← Int.cast_natCast]
    exact (hiff i _ (by positivity) (by exact_mod_cast r.val_lt)).mpr hi

/-- A tuple is Hardy–Littlewood admissible exactly when its set of entries is admissible.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 1. -/
theorem isHardyLittlewoodAdmissible_iff_isAdmissibleFinset (m : ℕ) (b : Fin m → ℤ) :
    IsHardyLittlewoodAdmissible m b ↔ IsAdmissibleFinset (Finset.univ.image b) := by
  refine forall₂_congr fun p hp => ?_
  rw [hardyLittlewoodResidueCount_ne_iff m b hp]
  simp

/-- The empty set is admissible.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 1. -/
theorem isAdmissibleFinset_empty : IsAdmissibleFinset ∅ :=
  fun _ _ => ⟨0, fun h hh => absurd hh (Finset.notMem_empty h)⟩

/-- The one-element set `{0}` is admissible: it misses the class `1` mod `p`.

Source: Carol Wu, *On Smooth Gaps between Primes Using the Maynard-Tao Sieve*,
INTEGERS 25 (2025), Article A44, Definition 1. -/
theorem isAdmissibleFinset_singleton_zero : IsAdmissibleFinset {0} := by
  intro p hp
  have := Fact.mk hp
  refine ⟨1, fun h hh => ?_⟩
  rw [Finset.mem_singleton] at hh
  subst hh
  simp

end MetaMathlibExt

end
