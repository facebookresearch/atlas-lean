/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.CTL.Basic
public import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod

/-! # A diameter completeness threshold for bounded existential reachability -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS

variable {State Label : Type*} (lts : LTS State Label)

/-- A diameter bound `d` means that every path of exactly `d + 1` steps can be replaced by
one of at most `d` steps with the same endpoints. The replacement need not preserve labels. -/
def DiameterBound (d : ℕ) : Prop :=
  ∀ ⦃s t : State⦄ {labels : List Label}, labels.length = d + 1 → lts.MTr s labels t →
    ∃ shorter : List Label, shorter.length ≤ d ∧ lts.MTr s shorter t

/-- The one-above-bound shortening condition gives a short witness for every reachable pair. -/
theorem DiameterBound.shorten {d : ℕ} (hd : lts.DiameterBound d) {s t : State}
    (h : lts.CanReach s t) : ∃ labels : List Label, labels.length ≤ d ∧ lts.MTr s labels t := by
  obtain ⟨labels, h⟩ := h
  induction h with
  | refl => exact ⟨[], Nat.zero_le _, .refl⟩
  | @stepL s a m tail t hstep htail ih =>
      obtain ⟨shorter, hlen, hshort⟩ := ih
      have htrace : lts.MTr s (a :: shorter) t := .stepL hstep hshort
      by_cases hle : (a :: shorter).length ≤ d
      · exact ⟨_, hle, htrace⟩
      · apply hd _ htrace
        simp only [List.length_cons] at hle ⊢
        omega

/-- A diameter bound is equivalent to the all-pairs reachability bound. -/
theorem diameterBound_iff_shorten (d : ℕ) : lts.DiameterBound d ↔
    ∀ s t, lts.CanReach s t → ∃ labels : List Label, labels.length ≤ d ∧ lts.MTr s labels t := by
  constructor
  · intro hd s t h
    exact hd.shorten lts h
  · intro h s t labels _ ht
    exact h s t ⟨labels, ht⟩

/-- A finite state space has a diameter bound, even if there are infinitely many labels.
Take the maximum of the shortest witness lengths over all reachable pairs. -/
theorem exists_diameterBound [Finite State] : ∃ d, lts.DiameterBound d := by
  classical
  let _ := Fintype.ofFinite State
  have hex (p : State × State) (h : lts.CanReach p.1 p.2) :
      ∃ n, ∃ labels : List Label, labels.length = n ∧ lts.MTr p.1 labels p.2 := by
    obtain ⟨labels, h⟩ := h
    exact ⟨labels.length, labels, rfl, h⟩
  let length (p : State × State) := if h : lts.CanReach p.1 p.2 then Nat.find (hex p h) else 0
  refine ⟨Finset.univ.sup length, (lts.diameterBound_iff_shorten _).mpr fun s t h => ?_⟩
  obtain ⟨labels, hlen, htrace⟩ := Nat.find_spec (hex (s, t) h)
  refine ⟨labels, ?_, htrace⟩
  rw [hlen, ← show length (s, t) = Nat.find (hex (s, t) h) by simp [length, h]]
  exact Finset.le_sup (Finset.mem_univ (s, t))

/-- The diameter is the least bound satisfying the path-shortening criterion. -/
noncomputable def diameter [Finite State] : ℕ := by
  classical
  exact Nat.find lts.exists_diameterBound

/-- The diameter satisfies the shortening criterion and is its least natural-number bound. -/
theorem isLeast_diameterBound [Finite State] :
    IsLeast {d | lts.DiameterBound d} lts.diameter := by
  classical
  exact ⟨Nat.find_spec lts.exists_diameterBound, fun _ h => Nat.find_min' _ h⟩

end Cslib.LTS

namespace Cslib.CTL

variable {State Label Atom : Type*} {lts : LTS State Label}
  {valuation : State → Atom → Prop}

/-- Bounded satisfaction of `EF φ` at length `k`: some initial state has a finite run of
exactly `k` steps whose endpoint satisfies `φ`. Length zero is permitted. -/
def existsFinallyAtLength (lts : LTS State Label) (valuation : State → Atom → Prop)
    (initial : Set State) (φ : Formula Atom) (k : ℕ) : Prop :=
  ∃ ss, ss 0 ∈ initial ∧ lts.FiniteRun ss k ∧ Satisfies lts valuation (ss k) φ

/-- Any path-shortening bound is complete for bounded checking of `EF`. The witness has some
length at most the bound; it need not be possible to extend it to the bound itself. -/
theorem existsFinally_iff_exists_le_of_diameterBound {d : ℕ} (hd : lts.DiameterBound d)
    (initial : Set State) (φ : Formula Atom) :
    (∃ s ∈ initial, Satisfies lts valuation s φ.existsFinally) ↔
      ∃ k ≤ d, existsFinallyAtLength lts valuation initial φ k := by
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨t, hreach, ht⟩ := Satisfies.existsFinally_iff_reachable.mp h
    obtain ⟨labels, hlen, htrace⟩ := hd.shorten lts hreach
    obtain ⟨ss, h₀, hk, hrun⟩ := LTS.exists_finiteRun_of_mtr htrace
    exact ⟨labels.length, hlen, ss, h₀ ▸ hs, hrun, hk ▸ ht⟩
  · rintro ⟨k, _, ss, h₀, hrun, hφ⟩
    exact ⟨ss 0, h₀, Satisfies.existsFinally_iff.mpr ⟨ss, k, rfl, hrun, hφ⟩⟩

/-- **Diameter completeness threshold for bounded `EF` checking.** Over a finite state
space, existential reachability from the initial set holds if and only if one of the
bounded instances of length at most the diameter has a witness. In particular, failure
at all lengths up to that bound excludes reachability. This is a semantic result for
`EF`, not a SAT encoding or a threshold for general liveness formulas.

Source: Biere, Cimatti, Clarke, and Zhu, *Symbolic Model Checking without BDDs*,
TACAS 1999, Definition 19 and Theorem 20 (stated there for an atomic target). -/
theorem existsFinally_iff_exists_le_diameter [Finite State] (initial : Set State)
    (φ : Formula Atom) :
    (∃ s ∈ initial, Satisfies lts valuation s φ.existsFinally) ↔
      ∃ k ≤ lts.diameter, existsFinallyAtLength lts valuation initial φ k :=
  existsFinally_iff_exists_le_of_diameterBound lts.isLeast_diameterBound.1 initial φ

end Cslib.CTL
