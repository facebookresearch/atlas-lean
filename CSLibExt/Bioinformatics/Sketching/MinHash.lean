/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.UniformOn
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# MinHash: the collision probability is the Jaccard similarity

Broder (1997) estimates the resemblance of two documents from their *min-hashes*: for a random
permutation `π` of the universe `U` of shingles, the min-hash of a set `A` is `min π(A)`. If `π`
is uniformly random, two sets collide (`min π(A) = min π(B)`) with probability exactly their
Jaccard similarity `|A ∩ B| / |A ∪ B|`.

Here `U` is a finite linearly ordered type, `π : Equiv.Perm U` is drawn from the uniform
distribution `ProbabilityTheory.uniformOn Set.univ` on `Equiv.Perm U`, and `min π(A)` is
`(A.image π).min`, a value in `WithTop U` (equal to `⊤` exactly when `A` is empty, so an empty
set collides only with an empty set). The measurable structure on `Equiv.Perm U` is any one with
measurable singletons (for instance `⊤`); the uniform law does not depend on it.

## Main results

* `card_minHash_collision`: the counting form: the number of permutations under which `A` and
  `B` collide, times `|A ∪ B|`, is `|A ∩ B|` times the number `|U|!` of all permutations.
* `uniformOn_minHash_collision`: **the MinHash collision probability under a uniformly random
  permutation is `|A ∩ B| / |A ∪ B|`**, for `A ∪ B` nonempty.

The proof: the element `z` of `A ∪ B` with the smallest image under `π` is unique, and the
permutations with a given minimizer `z` are equally many for every `z ∈ A ∪ B` (composing with
the transposition `swap z z'` exchanges the two classes); `A` and `B` collide exactly when the
minimizer lies in `A ∩ B`.

## References

* A. Z. Broder, *On the resemblance and containment of documents*, Proc. Compression and
  Complexity of Sequences (SEQUENCES 1997), IEEE, 21–29.
* A. Z. Broder, M. Charikar, A. M. Frieze and M. Mitzenmacher, *Min-wise independent
  permutations*, J. Comput. System Sci. 60 (2000), 630–659.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Sketching.MinHash

open Finset

variable {U : Type*} [LinearOrder U]

/-- The min-hash of `A` under the permutation `π`: the least element of `π(A)`, or `⊤` if `A` is
empty. -/
def minHash (π : Equiv.Perm U) (A : Finset U) : WithTop U := (A.image π).min

/-- The permutations under which `x` has the smallest image among the elements of `C`. -/
private def minimizers [Fintype U] (C : Finset U) (x : U) : Finset (Equiv.Perm U) :=
  univ.filter fun π => ∀ c ∈ C, π x ≤ π c

private theorem minHash_eq_of_min {π : Equiv.Perm U} {S : Finset U} {z : U} (hz : z ∈ S)
    (hmin : ∀ c ∈ S, π z ≤ π c) : minHash π S = (π z : WithTop U) := by
  refine le_antisymm (Finset.min_le (mem_image_of_mem π hz)) (Finset.le_min fun b hb => ?_)
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hb
  exact WithTop.coe_le_coe.mpr (hmin c hc)

private theorem disjoint_minimizers [Fintype U] (C : Finset U) :
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (minimizers C x) (minimizers C y) := by
  intro x hx y hy hxy
  refine Finset.disjoint_left.mpr fun π h1 h2 => hxy ?_
  simp only [minimizers, mem_filter, mem_univ, true_and] at h1 h2
  exact π.injective (le_antisymm (h1 y hy) (h2 x hx))

private theorem biUnion_minimizers [Fintype U] {C : Finset U} (hC : C.Nonempty) :
    C.biUnion (minimizers C) = univ := by
  refine eq_univ_of_forall fun π => ?_
  obtain ⟨z, hz, hmin⟩ := C.exists_min_image π hC
  exact mem_biUnion.mpr ⟨z, hz, by simpa [minimizers] using hmin⟩

/-- Composing with `swap x y` exchanges the permutations minimized at `x` and at `y`. -/
private theorem card_minimizers_eq [Fintype U] {C : Finset U} {x y : U} (hx : x ∈ C) (hy : y ∈ C) :
    (minimizers C x).card = (minimizers C y).card := by
  classical
  have hmap : ∀ {a b : U}, a ∈ C → b ∈ C → ∀ π ∈ minimizers C a,
      π * Equiv.swap a b ∈ minimizers C b := by
    intro a b ha hb π hπ
    simp only [minimizers, mem_filter, mem_univ, true_and, Equiv.Perm.coe_mul,
      Function.comp_apply, Equiv.swap_apply_right] at hπ ⊢
    intro c hc
    refine hπ _ ?_
    rcases eq_or_ne c a with rfl | hca
    · simpa using hb
    rcases eq_or_ne c b with rfl | hcb
    · simpa using ha
    · rwa [Equiv.swap_apply_of_ne_of_ne hca hcb]
  refine Finset.card_nbij' (· * Equiv.swap x y) (· * Equiv.swap x y) ?_ ?_ ?_ ?_
  · exact fun π hπ => hmap hx hy π hπ
  · intro π hπ
    have := hmap hy hx π hπ
    rwa [Equiv.swap_comm] at this
  · intro π _
    simp [mul_assoc]
  · intro π _
    simp [mul_assoc]

private theorem collision_iff [Fintype U] {A B : Finset U} (hC : (A ∪ B).Nonempty)
    (π : Equiv.Perm U) :
    minHash π A = minHash π B ↔ π ∈ (A ∩ B).biUnion (minimizers (A ∪ B)) := by
  simp only [mem_biUnion, minimizers, mem_filter, mem_univ, true_and, mem_inter]
  constructor
  · intro h
    obtain ⟨z, hz, hmin⟩ := (A ∪ B).exists_min_image π hC
    have hA : ∀ c ∈ A, π z ≤ π c := fun c hc => hmin c (mem_union_left B hc)
    have hB : ∀ c ∈ B, π z ≤ π c := fun c hc => hmin c (mem_union_right A hc)
    refine ⟨z, ?_, hmin⟩
    rcases mem_union.mp hz with hzA | hzB
    · refine ⟨hzA, ?_⟩
      rw [minHash_eq_of_min hzA hA] at h
      obtain ⟨c, hc, hcz⟩ := mem_image.mp (Finset.mem_of_min h.symm)
      rwa [← π.injective hcz]
    · refine ⟨?_, hzB⟩
      rw [minHash_eq_of_min hzB hB] at h
      obtain ⟨c, hc, hcz⟩ := mem_image.mp (Finset.mem_of_min h)
      rwa [← π.injective hcz]
  · rintro ⟨z, ⟨hzA, hzB⟩, hmin⟩
    rw [minHash_eq_of_min hzA fun c hc => hmin c (mem_union_left B hc),
      minHash_eq_of_min hzB fun c hc => hmin c (mem_union_right A hc)]

/-- **MinHash, counting form**: the number of permutations of `U` under which `A` and `B` have
the same min-hash, times `|A ∪ B|`, equals `|A ∩ B|` times the number of all permutations. -/
theorem card_minHash_collision [Fintype U] (A B : Finset U) (hC : (A ∪ B).Nonempty) :
    (univ.filter fun π : Equiv.Perm U => minHash π A = minHash π B).card * (A ∪ B).card =
      (A ∩ B).card * Fintype.card (Equiv.Perm U) := by
  obtain ⟨x₀, hx₀⟩ := hC
  set e := (minimizers (A ∪ B) x₀).card
  have hconst : ∀ x ∈ A ∪ B, (minimizers (A ∪ B) x).card = e :=
    fun x hx => card_minimizers_eq hx hx₀
  have hcoll : (univ.filter fun π : Equiv.Perm U => minHash π A = minHash π B) =
      (A ∩ B).biUnion (minimizers (A ∪ B)) := by
    ext π
    simp only [mem_filter, mem_univ, true_and]
    exact collision_iff ⟨x₀, hx₀⟩ π
  have hsub : A ∩ B ⊆ A ∪ B := inter_subset_union
  have h1 : ((A ∩ B).biUnion (minimizers (A ∪ B))).card = (A ∩ B).card * e := by
    rw [card_biUnion fun x hx y hy hxy =>
      disjoint_minimizers (A ∪ B) x (hsub hx) y (hsub hy) hxy]
    rw [sum_congr rfl fun x hx => hconst x (hsub hx), sum_const, smul_eq_mul]
  have h2 : Fintype.card (Equiv.Perm U) = (A ∪ B).card * e := by
    rw [← card_univ, ← biUnion_minimizers ⟨x₀, hx₀⟩, card_biUnion (disjoint_minimizers _),
      sum_congr rfl hconst, sum_const, smul_eq_mul]
  rw [hcoll, h1, h2]
  ring

/-- **MinHash collision probability** (Broder 1997): for a uniformly random permutation `π` of
the finite universe `U` (`uniformOn Set.univ` on `Equiv.Perm U`, for any measurable structure in
which singletons are measurable, e.g. `⊤`) and sets `A`, `B` with `A ∪ B` nonempty,
`P(min π(A) = min π(B)) = |A ∩ B| / |A ∪ B|`, the Jaccard similarity of `A` and `B`. -/
theorem uniformOn_minHash_collision [Finite U] [MeasurableSpace (Equiv.Perm U)]
    [MeasurableSingletonClass (Equiv.Perm U)] (A B : Finset U) (hC : (A ∪ B).Nonempty) :
    ProbabilityTheory.uniformOn Set.univ {π : Equiv.Perm U | minHash π A = minHash π B} =
      ((A ∩ B).card : ENNReal) / (A ∪ B).card := by
  have := Fintype.ofFinite U
  have hset : {π : Equiv.Perm U | minHash π A = minHash π B} =
      ↑(univ.filter fun π : Equiv.Perm U => minHash π A = minHash π B) := by
    ext π
    simp
  rw [ProbabilityTheory.uniformOn_univ, hset, MeasureTheory.Measure.count_apply_finset]
  have hcard := card_minHash_collision A B hC
  have hb : ((A ∪ B).card : ENNReal) ≠ 0 := by simpa using hC.ne_empty
  have hN : (Fintype.card (Equiv.Perm U) : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  rw [ENNReal.div_eq_div_iff hb (ENNReal.natCast_ne_top _) hN (ENNReal.natCast_ne_top _)]
  rw [mul_comm, mul_comm (Fintype.card _ : ENNReal)]
  exact_mod_cast hcard

end Cslib.Bioinformatics.Sketching.MinHash
