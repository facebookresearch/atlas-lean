/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import MathlibExt.Topology.KrullDimension

/-!
# A closed immersion of integral curves is an isomorphism

Let `j : Z ⟶ X` be a closed immersion of schemes, where `X` is integral and the topological Krull
dimension of `Z` is finite and at least that of `X`. Then `j` is an isomorphism. The proof is the
dimension count of the source: the image of `j` is closed and homeomorphic to `Z`, and if it were a
proper subset of the irreducible space `X`, its dimension plus one would be at most the dimension
of `X` (`IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne`). Hence `j` is surjective,
and a surjective closed immersion into a reduced scheme is an isomorphism
(`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`).

## Main results

* `AlgebraicGeometry.surjective_of_isClosedImmersion_of_topologicalKrullDim_le`: a closed
  immersion into an irreducible scheme whose source has finite dimension at least that of the
  target is surjective.
* `AlgebraicGeometry.isIso_of_isClosedImmersion_of_topologicalKrullDim_le`: the same with an
  integral target is an isomorphism.
* `AlgebraicGeometry.isIso_of_isClosedImmersion_of_topologicalKrullDim_eq_one`: a closed
  immersion between schemes of dimension `1` with integral target is an isomorphism.

## References

* B. Conrad, *Minimal models for elliptic curves*, notes (version of 21 November 2015),
  proof of Theorem 2.8, p. 5.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry

/-- Let `j : Z ⟶ X` be a closed immersion of schemes with `X` irreducible, and suppose that the
topological Krull dimension of `Z` is finite (`≠ ⊤`) and at least that of `X`. Then `j` is
surjective.

This is the dimension step of the proof of Theorem 2.8 in B. Conrad, *Minimal models for elliptic
curves*, p. 5: the image of `j` is closed and homeomorphic to `Z`, so if it missed a point of
`X`, the dimension of `X` would be at least that of `Z` plus one. No
hypothesis on `Z` beyond finiteness of its dimension is needed (nonemptiness of `Z` follows from
the dimension inequality, as `X` is nonempty). -/
theorem surjective_of_isClosedImmersion_of_topologicalKrullDim_le {Z X : Scheme} (j : Z ⟶ X)
    [IsClosedImmersion j] [IrreducibleSpace X]
    (hZ : topologicalKrullDim Z ≠ ⊤) (h : topologicalKrullDim X ≤ topologicalKrullDim Z) :
    Surjective j := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  have hemb := IsClosedImmersion.isClosedEmbedding j
  have hne : Set.range j ≠ Set.univ := fun h' =>
    hx (show x ∈ Set.range j from h' ▸ Set.mem_univ x)
  have key :=
    (IrreducibleSpace.isIrreducible_univ X).topologicalKrullDim_add_one_le_of_isClosed_of_ne
      hemb.isClosed_range (Set.subset_univ _) hne
  rw [(Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq,
    ← hemb.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq] at key
  have hX0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [topologicalKrullDim]
    exact Order.le_krullDim_iff.mpr
      ⟨RelSeries.singleton _ ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩, rfl⟩
  have h1 := key.trans h
  have h0 := hX0.trans h
  generalize topologicalKrullDim Z = d at hZ h0 h1
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl hZ
    | coe d => norm_cast at h1; omega

/-- Let `j : Z ⟶ X` be a closed immersion of schemes with `X` integral, and suppose that the
topological Krull dimension of `Z` is finite (`≠ ⊤`) and at least that of `X`. Then `j` is an
isomorphism.

This generalizes the statement used in the proof of Theorem 2.8 in B. Conrad, *Minimal models for
elliptic curves*, p. 5 (a closed immersion between integral proper curves over a field is an
isomorphism): neither properness, nor a base field, nor integrality of `Z` is needed; only the
integrality of `X` and the dimension comparison are used. -/
theorem isIso_of_isClosedImmersion_of_topologicalKrullDim_le {Z X : Scheme} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsIntegral X]
    (hZ : topologicalKrullDim Z ≠ ⊤) (h : topologicalKrullDim X ≤ topologicalKrullDim Z) :
    IsIso j := by
  have := surjective_of_isClosedImmersion_of_topologicalKrullDim_le j hZ h
  exact isIso_of_isClosedImmersion_of_surjective j

/-- A closed immersion `j : Z ⟶ X` of schemes whose underlying spaces both have topological Krull
dimension `1`, with `X` integral, is an isomorphism.

This is the statement used in the proof of Theorem 2.8 in B. Conrad, *Minimal models for elliptic
curves*, p. 5 ("a closed immersion between integral proper `k(s)`-curves ... must be an
isomorphism"). The hypotheses that the schemes are proper over a field and that `Z` is integral
are dropped, as they are not needed. -/
theorem isIso_of_isClosedImmersion_of_topologicalKrullDim_eq_one {Z X : Scheme} (j : Z ⟶ X)
    [IsClosedImmersion j] [IsIntegral X]
    (hZ : topologicalKrullDim Z = 1) (hX : topologicalKrullDim X = 1) : IsIso j :=
  isIso_of_isClosedImmersion_of_topologicalKrullDim_le j (by rw [hZ]; decide)
    (by rw [hZ, hX])

end AlgebraicGeometry
