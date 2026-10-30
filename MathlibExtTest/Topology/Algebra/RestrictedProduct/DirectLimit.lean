/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Algebra.RestrictedProduct.DirectLimit

@[expose] public section

/-!
# Restricted-product direct-limit smoke tests

Concrete finitely supported functions `ℕ → ℤ` (with `U i = {0}`) exercising
the pieces `XS`, the support, and the homeomorphism of Proposition 25.5.
-/

open scoped RestrictedProduct

namespace RestrictedProductDirectLimitTest

/-- The finitely supported function `n ↦ if n = 0 then 5 else 0`,
as an element of the restricted product over `ℕ` with `U i = {0}`. -/
private def testElem : RestrictedProduct (fun _ : ℕ => ℤ)
    (fun _ => ({0} : Set ℤ)) Filter.cofinite :=
  RestrictedProduct.mk (fun n => if n = 0 then 5 else 0) (by
    rw [Filter.eventually_cofinite]
    have hsub : {n : ℕ | ¬ (if n = 0 then 5 else 0) ∈ ({0} : Set ℤ)} ⊆ {0} := by
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn
      by_contra h
      apply hn
      have hn0 : n ≠ 0 := by simpa using h
      simp [hn0]
    exact Set.Finite.subset (Set.finite_singleton 0) hsub)

/-- The values of `testElem`. -/
private theorem testElem_apply (m : ℕ) :
    testElem m = if m = 0 then (5 : ℤ) else 0 := rfl

/-- The zero tuple, in the empty piece. -/
private def zeroTuple : ↥(RestrictedProduct.XS (fun _ : ℕ => ℤ)
    (fun _ => ({0} : Set ℤ)) ∅) :=
  ⟨fun _ => (0 : ℤ), by intro i _; simp⟩

/-- The support of `testElem` is exactly `{0}`. -/
example : RestrictedProduct.supportFinset (fun _ : ℕ => ℤ)
    (fun _ => ({0} : Set ℤ)) testElem = {0} := by
  ext n
  simp only [RestrictedProduct.supportFinset, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, Finset.mem_singleton]
  show (¬ testElem n ∈ ({0} : Set ℤ)) ↔ n = 0
  rw [testElem_apply]
  by_cases hn : n = 0 <;> simp [hn]

/-- `testElem` lies in the piece indexed by its support. -/
example : (testElem : (i : ℕ) → ℤ) ∈
    RestrictedProduct.XS (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ))
      (RestrictedProduct.supportFinset (fun _ : ℕ => ℤ)
        (fun _ => ({0} : Set ℤ)) testElem) :=
  RestrictedProduct.mem_XS_support _ _ testElem

/-- The pieces grow with the indexing set. -/
example : RestrictedProduct.XS (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)) ∅ ⊆
    RestrictedProduct.XS (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)) {0} :=
  RestrictedProduct.XS_mono _ _ (Finset.empty_subset _)

/-- The zero tuple lies in the empty piece. -/
example : (fun _ : ℕ => (0 : ℤ)) ∈
    RestrictedProduct.XS (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)) ∅ := by
  intro i _
  simp

/-- A tuple in a piece is eventually in `U`. -/
example : ∀ᶠ n in Filter.cofinite, (fun _ : ℕ => (0 : ℤ)) n ∈ ({0} : Set ℤ) :=
  RestrictedProduct.XS_mem_restricted (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ))
    (S := ∅) (by intro i _; simp)

/-- The roundtrip `fromDirectLimit ∘ toDirectLimit` is the identity,
on the concrete element `testElem`. -/
example : RestrictedProduct.fromDirectLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ))
      (RestrictedProduct.toDirectLimit (fun _ : ℕ => ℤ)
        (fun _ => ({0} : Set ℤ)) testElem) = testElem :=
  RestrictedProduct.fromDirectLimit_toDirectLimit _ _ testElem

/-- The other roundtrip, at the image of `testElem`. -/
example : RestrictedProduct.toDirectLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ))
      (RestrictedProduct.fromDirectLimit (fun _ : ℕ => ℤ)
        (fun _ => ({0} : Set ℤ))
        (RestrictedProduct.toDirectLimit (fun _ : ℕ => ℤ)
          (fun _ => ({0} : Set ℤ)) testElem)) =
    RestrictedProduct.toDirectLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ)) testElem :=
  RestrictedProduct.toDirectLimit_fromDirectLimit _ _
    (RestrictedProduct.toDirectLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ)) testElem)

/-- The homeomorphism is a homeomorphism: applying it and its inverse
returns the starting element. -/
example : (RestrictedProduct.homeomorph_directLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ))).symm
    ((RestrictedProduct.homeomorph_directLimit (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ))) testElem) = testElem :=
  Homeomorph.symm_apply_apply _ testElem

/-- The canonical maps into the direct limit of the pieces are
compatible with the transition maps, on the concrete zero tuple in the
empty piece. -/
example : TopologicalSpace.DirectLimit.of
      (fun S : Finset ℕ => ↥(RestrictedProduct.XS (fun _ : ℕ => ℤ)
        (fun _ => ({0} : Set ℤ)) S))
      (RestrictedProduct.transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
      (RestrictedProduct.continuous_transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
      {0}
      (RestrictedProduct.transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ))
        ∅ {0} (Finset.empty_subset _) zeroTuple) =
    TopologicalSpace.DirectLimit.of
      (fun S : Finset ℕ => ↥(RestrictedProduct.XS (fun _ : ℕ => ℤ)
        (fun _ => ({0} : Set ℤ)) S))
      (RestrictedProduct.transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
      (RestrictedProduct.continuous_transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
      ∅ zeroTuple :=
  TopologicalSpace.DirectLimit.of_comp
    (fun S : Finset ℕ => ↥(RestrictedProduct.XS (fun _ : ℕ => ℤ)
      (fun _ => ({0} : Set ℤ)) S))
    (RestrictedProduct.transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
    (RestrictedProduct.continuous_transitionMaps (fun _ : ℕ => ℤ) (fun _ => ({0} : Set ℤ)))
    (Finset.empty_subset _) zeroTuple

end RestrictedProductDirectLimitTest
