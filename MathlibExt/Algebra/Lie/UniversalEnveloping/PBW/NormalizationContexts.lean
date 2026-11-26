/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.Normalization

/-!
# Linear insertion contexts for PBW normalization

Let `R` be a commutative ring and let `b : I → L` be a Lie-algebra basis indexed by a linearly
ordered alphabet. Inserting a vector `x` between fixed words means summing the normalized
inserted basis words with coefficients from `b.repr(x)`.

Two inserted vectors, with a fixed word between them, give a bilinear normal-form map. The
adjacent-pair version combines exchanged letters with the bracket insertion. These maps record
the vector-valued normalization contexts used by the enveloping relation identities.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

/-- The normal form of a vector inserted between basis words.

For fixed prefix `p` and suffix `s`, expand `x ∈ L` in the basis and form the corresponding
linear combination of normal forms of `p ++ i :: s`. -/
def normalizationInsertion (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] (OrderedWord I →₀ R) :=
  (Finsupp.linearCombination R (fun i => normalize b (p ++ i :: s))).comp b.repr.toLinearMap

/-- The coordinate formula for a normalized vector insertion.

The inserted-vector normal form is the finite sum of `normalize(p ++ i :: s)` weighted by the
basis coordinates of `x`. -/
theorem normalizationInsertion_apply (b : Module.Basis I R L)
    (p s : List I) (x : L) :
    normalizationInsertion b p s x =
      (b.repr x).sum (fun i r => r • normalize b (p ++ i :: s)) := rfl

/-- The normal form of an inserted basis vector.

Inserting `b_i` between `p` and `s` gives `normalize(p ++ i :: s)`. -/
@[simp]
theorem normalizationInsertion_basis (b : Module.Basis I R L)
    (p s : List I) (i : I) :
    normalizationInsertion b p s (b i) = normalize b (p ++ i :: s) := by
  change (Finsupp.linearCombination R (fun j => normalize b (p ++ j :: s)))
    (b.repr (b i)) = _
  rw [b.repr_self, Finsupp.linearCombination_single, one_smul]

/-- The bilinear normal form of two separated vector insertions.

For fixed words `p,m,s`, expand both inserted vectors in the basis and normalize words of the
form `p ++ i :: m ++ j :: s`. -/
def normalizationSeparatedPair (b : Module.Basis I R L) (p m s : List I) :
    L →ₗ[R] L →ₗ[R] (OrderedWord I →₀ R) :=
  (Finsupp.linearCombination R
    (fun i => normalizationInsertion b (p ++ i :: m) s)).comp b.repr.toLinearMap

/-- The left basis coordinate of a separated normalization pair.

Fixing the first inserted vector to `b_i` leaves the one-vector insertion map with prefix `p
++ i :: m` and suffix `s`. -/
@[simp]
theorem normalizationSeparatedPair_basis_left (b : Module.Basis I R L)
    (p m s : List I) (i : I) :
    normalizationSeparatedPair b p m s (b i) =
      normalizationInsertion b (p ++ i :: m) s := by
  change (Finsupp.linearCombination R (fun j => normalizationInsertion b (p ++ j :: m) s))
    (b.repr (b i)) = _
  rw [b.repr_self, Finsupp.linearCombination_single, one_smul]

/-- The right basis coordinate of a separated normalization pair.

Fixing the second vector to `b_j` leaves the one-vector insertion map with prefix `p` and
suffix `m ++ j :: s`. -/
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

/-- The bilinear normal form of adjacent vector insertions.

Use the separated insertion map with empty middle word to normalize an adjacent pair of Lie
vectors between fixed prefix and suffix. -/
def normalizationPair (b : Module.Basis I R L) (p s : List I) :
    L →ₗ[R] L →ₗ[R] (OrderedWord I →₀ R) :=
  normalizationSeparatedPair b p [] s

/-- The left basis coordinate of an adjacent normalization pair.

With first vector `b_i`, the pair map is insertion of the second vector after the prefix `p ++
[i]`. -/
theorem normalizationPair_basis_left (b : Module.Basis I R L)
    (p s : List I) (i : I) (x : L) :
    normalizationPair b p s (b i) x = normalizationInsertion b (p ++ [i]) s x := by
  rw [normalizationPair, normalizationSeparatedPair_basis_left]

/-- The right basis coordinate of an adjacent normalization pair.

With second vector `b_j`, the pair map is insertion of the first vector before the suffix `j
:: s`. -/
theorem normalizationPair_basis_right (b : Module.Basis I R L)
    (p s : List I) (x : L) (j : I) :
    normalizationPair b p s x (b j) = normalizationInsertion b p (j :: s) x := by
  rw [normalizationPair, normalizationSeparatedPair_basis_right]
  rfl

/-- The normal-form value of an adjacent enveloping relation.

For a pair `i,j` between `p` and `s`, add the normal form of the exchanged pair to the
normalized insertion of `[b_i,b_j]`. -/
def reductionValue (b : Module.Basis I R L) (p : List I) (i j : I) (s : List I) :
    OrderedWord I →₀ R :=
  normalize b (p ++ j :: i :: s) + normalizationInsertion b p s ⁅b i, b j⁆

/-- The normalizer at its first adjacent inversion.

If the adjacent-inversion map selects `p,i,j,s`, the normal form equals the exchanged-word
normal form plus the contextual bracket insertion. -/
theorem normalize_eq_reductionValue_of_search (b : Module.Basis I R L)
    {xs p s : List I} {i j : I}
    (h : List.adjacentInversion xs = some (p, i, j, s)) :
    normalize b xs = reductionValue b p i j s := by
  rw [normalize_of_adjacentInversion b h, reductionValue, normalizationInsertion_apply]

end UniversalEnvelopingAlgebra.PBW
