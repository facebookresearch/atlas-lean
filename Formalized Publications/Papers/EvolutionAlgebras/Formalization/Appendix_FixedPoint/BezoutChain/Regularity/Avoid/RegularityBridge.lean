/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Bridge from `Fin k`-indexed regularity data to the regular-sequence API

This file turns explicit successive regularity data for a family `q : Fin k → R`
into Mathlib's `RingTheory.Sequence.IsRegular` list API for `List.ofFn q`, in
the exact form consumed downstream (properness in `top_ne_smul` shape included).
Everything here holds over a general commutative ring `R`.

## Main results

1. `isRegular_ofFn_of_successive`: from successive SMul-regularity
   (`SuccessiveSMulRegular`) plus properness to
   `RingTheory.Sequence.IsRegular R (List.ofFn q)`, by induction on `k`
   peeling off the last element (`List.ofFn_succ_last`) through Mathlib's
   cons-iteration API (`isWeaklyRegular_append_iff`,
   `isWeaklyRegular_singleton_iff`; both are proved in Mathlib from
   `isWeaklyRegular_cons_iff`).
2. `span_range_eq_ofList_ofFn`: `Ideal.span (Set.range q)` equals
   `Ideal.ofList (List.ofFn q)`.
3. `span_ne_top_of_forall_map_zero` / `top_ne_smul_ofList_of_forall_map_zero` /
   `top_ne_smul_ofFn_of_forall_map_zero`: properness from generators vanishing
   under a ring hom into a nontrivial ring (for homogeneous generators this is
   evaluation at the origin), ending in the `top_ne_smul` shape `IsRegular`
   requires.

Main consumers: `MkSystemRegular` (which assembles per-rung regularity into
`SuccessiveSMulRegular`, then applies (1) + (3)) and the unmixedness track
(`Unmixedness`, `LocalUnmixed`, `RegularSequenceDimDrop`, `AssHeightBound`), which
consumes the `SuccessiveSMulRegular` shape and the span identification.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RegularityBridge

variable {R : Type*} [CommRing R]

/-! ## Successive data and span identification

`SuccessiveSMulRegular` is the input shape: per-rung regularity over the span
of previous values, exactly as the avoidance/selection steps produce it.
`span_range_eq_ofList_ofFn` identifies that span with the `ofList` span the
`IsRegular` API speaks about. -/

/-- Successive SMul-regularity data for a `Fin k`-indexed family in `R`: each
`q i` is SMul-regular on `R` modulo the span of the previous values. This is
the shape the downstream steps (avoidance selection, triangular rungs)
assemble; `isRegular_ofFn_of_successive` turns it into Mathlib's `IsRegular`. -/
def SuccessiveSMulRegular {k : ℕ} (q : Fin k → R) : Prop :=
  ∀ i : Fin k,
    IsSMulRegular
      (R ⧸ (Ideal.span (Set.image q { j | j.val < i.val }) • ⊤ : Submodule R R))
      (q i)

/-- The span of the range of `q` equals the `Ideal.ofList` span of `List.ofFn q`,
the form the `IsRegular` API speaks about. -/
theorem span_range_eq_ofList_ofFn {k : ℕ} (q : Fin k → R) :
    Ideal.span (Set.range q) = Ideal.ofList (List.ofFn q) := by
  have hset : ({ r | r ∈ List.ofFn q } : Set R) = Set.range q := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_range, List.mem_ofFn]
  change Ideal.span (Set.range q) = Ideal.span { r | r ∈ List.ofFn q }
  rw [hset]

/-! ## Truncation and reindexing helpers (private)

These identify initial-segment spans across the `Fin k` / `Fin (k + 1)`
boundary so the induction below can restrict successive data to the
`castSucc` prefix and peel off the last element. -/

/-- Truncating a `Fin (n + 1)` value below `n` and re-embedding is the identity. -/
private theorem castSucc_mk_eq {n : ℕ} (j : Fin (n + 1)) (h : j.val < n) :
    (⟨j.val, h⟩ : Fin n).castSucc = j :=
  Fin.ext rfl

/-- Reindexing an initial segment along `Fin.castSucc` does not change its span. -/
private theorem span_image_castSucc_eq {k : ℕ} (q : Fin (k + 1) → R) (j : Fin k) :
    Ideal.span (Set.image q { j' : Fin (k + 1) | j'.val < (j.castSucc).val }) =
      Ideal.span (Set.image (fun i : Fin k => q i.castSucc)
        { j' | j'.val < j.val }) := by
  rw [(rfl : (j.castSucc).val = j.val)]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j', hj', rfl⟩
    exact ⟨⟨j'.val, lt_trans hj' j.isLt⟩, hj', congrArg q (castSucc_mk_eq _ _)⟩
  · rintro ⟨j', hj', rfl⟩
    exact ⟨j'.castSucc, hj', rfl⟩

/-- The span of the values before `Fin.last k` is the `ofList` span of the
`castSucc` prefix list. -/
private theorem span_image_iio_last_eq_ofList {k : ℕ} (q : Fin (k + 1) → R) :
    Ideal.span (Set.image q { j' : Fin (k + 1) | j'.val < (Fin.last k).val }) =
      Ideal.ofList (List.ofFn fun i : Fin k => q i.castSucc) := by
  rw [(rfl : (Fin.last k).val = k), ← span_range_eq_ofList_ofFn]
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨j', hj', rfl⟩
    exact ⟨⟨j'.val, hj'⟩, congrArg q (castSucc_mk_eq _ _)⟩
  · rintro ⟨j', rfl⟩
    exact ⟨j'.castSucc, j'.isLt, rfl⟩

/-! ## Weak regularity by induction on `k`

Peel off the last element (`List.ofFn_succ_last`) through Mathlib's
cons-iteration API; properness is added separately by the next section, since
it needs the evaluation-at-origin argument rather than successive data. -/

/-- Weak regularity of `List.ofFn q` from successive data, by induction on `k`. -/
private theorem weak_aux : ∀ (k : ℕ) (q : Fin k → R), SuccessiveSMulRegular q →
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn q) := by
  intro k
  induction k with
  | zero =>
    intro q _
    rw [List.ofFn_zero]
    exact RingTheory.Sequence.IsWeaklyRegular.nil R R
  | succ k ih =>
    intro q hq
    rw [List.ofFn_succ_last, RingTheory.Sequence.isWeaklyRegular_append_iff]
    refine ⟨?_, ?_⟩
    · apply ih
      intro j
      have hj := hq j.castSucc
      rw [span_image_castSucc_eq q j] at hj
      exact hj
    · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hlast := hq (Fin.last k)
      rw [span_image_iio_last_eq_ofList q] at hlast
      exact hlast

/-- Weak regularity of `List.ofFn q` from successive SMul-regularity data. -/
theorem isWeaklyRegular_ofFn_of_successive {k : ℕ} (q : Fin k → R)
    (h : SuccessiveSMulRegular q) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn q) :=
  weak_aux k q h

/-- Regularity of `List.ofFn q` from successive data plus properness in
`top_ne_smul` form. -/
theorem isRegular_ofFn_of_successive {k : ℕ} (q : Fin k → R)
    (hsucc : SuccessiveSMulRegular q)
    (hproper : (⊤ : Submodule R R) ≠ Ideal.ofList (List.ofFn q) • ⊤) :
    RingTheory.Sequence.IsRegular R (List.ofFn q) :=
  ⟨isWeaklyRegular_ofFn_of_successive q hsucc, hproper⟩

/-! ## Properness from evaluation at the origin

A span contained in the kernel of a ring hom into a nontrivial ring cannot be
`⊤`. For homogeneous generators the hom is evaluation at the origin; the
lemmas below end in the `top_ne_smul` shape `IsRegular` needs. -/

/-- A span whose generators all vanish under a ring hom into a nontrivial ring
is proper. For homogeneous generators this is evaluation at the origin. -/
theorem span_ne_top_of_forall_map_zero {s : Set R} {S : Type*} [CommRing S]
    [Nontrivial S] (φ : R →+* S) (hφ : ∀ r ∈ s, φ r = 0) :
    Ideal.span s ≠ ⊤ := by
  intro hcon
  have h1 : (1 : R) ∈ Ideal.span s := by
    rw [hcon]
    exact Submodule.mem_top
  have hle : Ideal.span s ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    intro r hr
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    exact hφ r hr
  have h0 : φ (1 : R) = 0 := RingHom.mem_ker.mp (hle h1)
  rw [map_one] at h0
  exact one_ne_zero h0

/-- Properness in the `top_ne_smul` form needed by `IsRegular`, from generators
vanishing under an evaluation map. -/
theorem top_ne_smul_ofList_of_forall_map_zero {L : List R} {S : Type*} [CommRing S]
    [Nontrivial S] (φ : R →+* S) (hφ : ∀ r ∈ L, φ r = 0) :
    (⊤ : Submodule R R) ≠ Ideal.ofList L • ⊤ := by
  have hspan : Ideal.span { r | r ∈ L } ≠ ⊤ :=
    span_ne_top_of_forall_map_zero φ (fun r hr => hφ r hr)
  change (⊤ : Submodule R R) ≠ Ideal.span { r | r ∈ L } • ⊤
  rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
  exact Ne.symm hspan

/-- `ofList` properness for `List.ofFn q` when every `q i` vanishes at the origin. -/
theorem top_ne_smul_ofFn_of_forall_map_zero {k : ℕ} (q : Fin k → R) {S : Type*}
    [CommRing S] [Nontrivial S] (φ : R →+* S) (hφ : ∀ i, φ (q i) = 0) :
    (⊤ : Submodule R R) ≠ Ideal.ofList (List.ofFn q) • ⊤ := by
  apply top_ne_smul_ofList_of_forall_map_zero φ
  intro r hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact hφ i

/-! ## References

Mathlib (`Mathlib/RingTheory/Regular/RegularSequence.lean`):
* `Ideal.ofList` (with `ofList_nil`, `ofList_cons`, `ofList_append`),
* `RingTheory.Sequence.IsWeaklyRegular` (`regular_mod_prev`),
* `RingTheory.Sequence.IsRegular` (`top_ne_smul`),
* `RingTheory.Sequence.IsWeaklyRegular.nil`,
* `RingTheory.Sequence.isWeaklyRegular_append_iff`,
* `RingTheory.Sequence.isWeaklyRegular_singleton_iff`,
* consumer-side (used by the track-A3 induction, not here):
  `RingTheory.Sequence.isRegular_cons_iff`.

Mathlib (`Mathlib/RingTheory/Ideal/Span.lean`): `Ideal.span_le`.
Mathlib (`Mathlib/RingTheory/Ideal/Operations.lean`): `Submodule.span_smul_eq`,
`Submodule.set_smul_top_eq_span`.
Lean core (`Init/Data/List/OfFn.lean`): `List.ofFn_zero`, `List.ofFn_succ_last`,
`List.mem_ofFn`, `List.length_ofFn`, `List.getElem_ofFn`.
-/

end RegularityBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
