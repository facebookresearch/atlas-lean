/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.List.OfFn

/-!
# Large sets in semigroups

Notions of largeness for subsets of an arbitrary (not necessarily commutative) semigroup `S`:
piecewise syndetic sets, `J`-sets, central sets and `C`-sets, with their basic characteristic
lemmas. Ultrafilters on `S` are multiplied with Mathlib's `Ultrafilter.semigroup`, for which
`D ∈ p * q` iff `{x | {y | x * y ∈ D} ∈ q} ∈ p`. The `J`-set condition quantifies over nonempty
finite families of sequences, so over an empty semigroup every set is a `J`-set; the lemmas
about `J`-sets therefore assume `[Nonempty S]`.

The definitions follow Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary
Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (after Hindman and Strauss).
-/

namespace MetaMathlibExt

@[expose] public section

attribute [local instance] Ultrafilter.semigroup

section LargeSets

variable {S : Type*} [Semigroup S]

/-- A set `D` in a semigroup `S` is piecewise syndetic when there is a finite `G ⊆ S` such that
for every finite `F ⊆ S` some `x ∈ S` has `F x ⊆ ⋃_{t ∈ G} t⁻¹ D`, where
`t⁻¹ D = {s | t s ∈ D}`.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets, after
Hindman--Strauss). -/
def IsMulPiecewiseSyndetic (D : Set S) : Prop :=
  ∃ G : Finset S, ∀ F : Finset S, ∃ x : S, ∀ f ∈ F, ∃ t ∈ G, t * (f * x) ∈ D

/-- A set `D` in a semigroup `S` is a `J`-set: for every nonempty finite set `F` of sequences
`ℕ → S` there are `m ≥ 1`, `a_1, …, a_{m+1} ∈ S` and indices `t_1 < ⋯ < t_m` with
`(∏_{j=1}^m a_j f(t_j)) a_{m+1} ∈ D` for every `f ∈ F`. Here `m` is written `m + 1` and the
indices start at `0`.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
def IsMulJSet (D : Set S) : Prop :=
  ∀ F : Finset (ℕ → S), F.Nonempty → ∃ (m : ℕ) (a : Fin (m + 2) → S) (t : Fin (m + 1) → ℕ),
    StrictMono t ∧ ∀ f ∈ F,
      (List.ofFn fun j : Fin m => a j.succ.castSucc * f (t j.succ)).foldl (· * ·)
          (a 0 * f (t 0)) * a (Fin.last (m + 1)) ∈ D

/-- A set `D` in a semigroup `S` is central: `D ∈ p` for a minimal idempotent `p ∈ βS`, i.e. an
idempotent lying in the smallest two-sided ideal `K(βS)`. Membership in `K(βS)` is written as
membership in every nonempty two-sided ideal of `βS` (`K(βS)` is itself such an ideal and lies in
all of them).

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2.1 (central sets). -/
def IsCentralSet (D : Set S) : Prop :=
  ∃ p : Ultrafilter S, p * p = p ∧
    (∀ I : Set (Ultrafilter S), I.Nonempty → (∀ q ∈ I, ∀ r, r * q ∈ I ∧ q * r ∈ I) → p ∈ I) ∧
    D ∈ p

/-- A set `D` in a semigroup `S` is a `C`-set: `D ∈ p` for an idempotent `p ∈ J(S)`, the
ultrafilters all of whose members are `J`-sets.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3) (C-sets). -/
def IsCSet (D : Set S) : Prop :=
  ∃ p : Ultrafilter S, p * p = p ∧ (∀ B ∈ p, IsMulJSet B) ∧ D ∈ p

/-- In a nonempty semigroup the whole semigroup is piecewise syndetic.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets). -/
theorem isMulPiecewiseSyndetic_univ [Nonempty S] : IsMulPiecewiseSyndetic (Set.univ : Set S) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  exact ⟨{s}, fun _ => ⟨s, fun _ _ => ⟨s, Finset.mem_singleton_self s, Set.mem_univ _⟩⟩⟩

/-- The empty set is not piecewise syndetic.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2 (piecewise syndetic sets). -/
theorem not_isMulPiecewiseSyndetic_empty : ¬ IsMulPiecewiseSyndetic (∅ : Set S) := by
  rintro ⟨G, hG⟩
  obtain ⟨x, -⟩ := hG ∅
  obtain ⟨y, hy⟩ := hG {x}
  obtain ⟨t, -, ht⟩ := hy x (Finset.mem_singleton_self x)
  exact ht

/-- In a nonempty semigroup the whole semigroup is a `J`-set.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
theorem isMulJSet_univ [Nonempty S] : IsMulJSet (Set.univ : Set S) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  refine fun _ _ => ⟨0, fun _ => s, fun _ => 0, fun i j hij => ?_, fun _ _ => Set.mem_univ _⟩
  have := i.isLt
  have := j.isLt
  simp only [Fin.lt_def] at hij
  omega

/-- In a nonempty semigroup the empty set is not a `J`-set.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3). -/
theorem not_isMulJSet_empty [Nonempty S] : ¬ IsMulJSet (∅ : Set S) := by
  intro h
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨_, _, _, _, hf⟩ := h {fun _ => s} (Finset.singleton_nonempty _)
  exact hf _ (Finset.mem_singleton_self _)

/-- The empty set is not central.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Section 2.1 (central sets). -/
theorem not_isCentralSet_empty : ¬ IsCentralSet (∅ : Set S) := by
  rintro ⟨p, -, -, hp⟩
  exact p.empty_notMem hp

/-- The empty set is not a `C`-set.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Definition 2.4(3) (C-sets). -/
theorem not_isCSet_empty : ¬ IsCSet (∅ : Set S) := by
  rintro ⟨p, -, -, hp⟩
  exact p.empty_notMem hp

end LargeSets

end

end MetaMathlibExt
