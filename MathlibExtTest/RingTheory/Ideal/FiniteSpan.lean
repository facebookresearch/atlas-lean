/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.FiniteSpan

@[expose] public section

universe u

/-- `exactSource` consumer with the original binders. -/
private theorem exactSource {B : Type u} [CommRing B] (P : B → Prop)
    (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → B),
      Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) :=
  Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem P hloc

/-- The constant predicate `True` always has the single witness `1`. -/
example : ∃ (ι : Type) (_ : Finite ι) (f : ι → ℤ),
    Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, True := by
  obtain ⟨ι, hι, f, hf, -⟩ :=
    Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
      (fun _ : ℤ => True) (fun 𝔭 h𝔭 => ⟨1,
        fun h => h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one),
        trivial⟩)
  exact ⟨ι, hι, f, hf, fun _ => trivial⟩

/-- Nontrivial instance over `ℤ`: every prime ideal is proper, so it
misses the unit `1`, and finitely many units span the unit ideal. -/
example : ∃ (ι : Type) (_ : Finite ι) (f : ι → ℤ),
    Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, IsUnit (f i) := by
  apply Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
  intro 𝔭 h𝔭
  exact ⟨1, fun h => h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one),
    isUnit_one⟩
