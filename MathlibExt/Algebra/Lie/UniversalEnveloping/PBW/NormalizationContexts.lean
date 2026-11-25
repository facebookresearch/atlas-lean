/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.Normalization

/-!
# Linear contexts for the ordered-word normalizer

Inserting a Lie vector means expanding its actual basis coordinates. Two
inserted vectors give a bilinear map, even with a fixed word between them.
These maps extend the smaller-word reduction identities through bracket
coefficients in the overlapping and disjoint confluence cases.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

/-- Normalize a word with one inserted vector by its actual basis coordinates. -/
def normalizationInsertion (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] (OrderedWord I →₀ R) :=
  (Finsupp.linearCombination R (fun i => normalize b (p ++ i :: s))).comp b.repr.toLinearMap

theorem normalizationInsertion_apply (b : Module.Basis I R L)
    (p s : List I) (x : L) :
    normalizationInsertion b p s x =
      (b.repr x).sum (fun i r => r • normalize b (p ++ i :: s)) := rfl

@[simp]
theorem normalizationInsertion_basis (b : Module.Basis I R L)
    (p s : List I) (i : I) :
    normalizationInsertion b p s (b i) = normalize b (p ++ i :: s) := by
  change (Finsupp.linearCombination R (fun j => normalize b (p ++ j :: s)))
    (b.repr (b i)) = _
  rw [b.repr_self, Finsupp.linearCombination_single, one_smul]

/-- Normalize two inserted vectors with a fixed finite word between them. -/
def normalizationSeparatedPair (b : Module.Basis I R L) (p m s : List I) :
    L →ₗ[R] L →ₗ[R] (OrderedWord I →₀ R) :=
  (Finsupp.linearCombination R
    (fun i => normalizationInsertion b (p ++ i :: m) s)).comp b.repr.toLinearMap

@[simp]
theorem normalizationSeparatedPair_basis_left (b : Module.Basis I R L)
    (p m s : List I) (i : I) :
    normalizationSeparatedPair b p m s (b i) =
      normalizationInsertion b (p ++ i :: m) s := by
  change (Finsupp.linearCombination R (fun j => normalizationInsertion b (p ++ j :: m) s))
    (b.repr (b i)) = _
  rw [b.repr_self, Finsupp.linearCombination_single, one_smul]

/-- Fixing the right basis vector gives the original one-vector context. -/
theorem normalizationSeparatedPair_basis_right (b : Module.Basis I R L)
    (p m s : List I) (x : L) (j : I) :
    normalizationSeparatedPair b p m s x (b j) =
      normalizationInsertion b p (m ++ j :: s) x := by
  have h : (normalizationSeparatedPair b p m s).flip (b j) =
      normalizationInsertion b p (m ++ j :: s) := by
    apply b.ext
    intro i
    simp only [LinearMap.flip_apply, normalizationSeparatedPair_basis_left,
      normalizationInsertion_basis, List.append_assoc, List.cons_append]
  exact LinearMap.congr_fun h x

/-- The two-variable context for an adjacent pair. -/
def normalizationPair (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] L →ₗ[R] (OrderedWord I →₀ R) :=
  normalizationSeparatedPair b p [] s

theorem normalizationPair_basis_left (b : Module.Basis I R L)
    (p s : List I) (i : I) (x : L) :
    normalizationPair b p s (b i) x = normalizationInsertion b (p ++ [i]) s x := by
  rw [normalizationPair, normalizationSeparatedPair_basis_left]

theorem normalizationPair_basis_right (b : Module.Basis I R L)
    (p s : List I) (x : L) (j : I) :
    normalizationPair b p s x (b j) = normalizationInsertion b p (j :: s) x := by
  rw [normalizationPair, normalizationSeparatedPair_basis_right]
  rfl

/-- The value of one literal oriented basis-pair reduction. -/
def reductionValue (b : Module.Basis I R L) (p : List I) (i j : I) (s : List I) :
    OrderedWord I →₀ R :=
  normalize b (p ++ j :: i :: s) + normalizationInsertion b p s ⁅b i, b j⁆

/-- The normalizer satisfies the reduction selected by its actual search. -/
theorem normalize_eq_reductionValue_of_search (b : Module.Basis I R L)
    {xs p s : List I} {i j : I}
    (h : List.adjacentInversion xs = some (p, i, j, s)) :
    normalize b xs = reductionValue b p i j s := by
  rw [normalize_of_adjacentInversion b h, reductionValue, normalizationInsertion_apply]

end UniversalEnvelopingAlgebra.PBW
