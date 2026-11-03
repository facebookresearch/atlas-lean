/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.RingTheory.Ideal.Height
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.LocalizationOfCMGap
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop

/-!
# Maximal successive-regular sequences exist in every prime
Proves the `[MaximalRegularSequenceExists]` residual of `LocalizationOfCMGap`
(`LocalizationOfCMGap.MaximalRegularSequenceExists`): in a Noetherian local ring `S`, every
prime `p` contains a successive-regular sequence `x : Fin r → S` that is
maximal, in the sense that every `z ∈ p` is a zerodivisor on
`S ⧸ Ideal.span (Set.range x)`.

Route: bounded lengths via L3
(`length_le_height_of_localized`) + classical max (`Nat.findGreatest`) +
`Fin.snoc`-extension of any non-maximal family. No new mathematics and no
finite-dim hypothesis; the `Fin.snoc` span plumbing duplicates the proofs of
RegularityBridge's private helpers so that proved file stays untouched.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MaximalRegularSequenceExists

universe u

/-! ## Snoc span plumbing (Step C1/C2 helpers)

Snoc analogues of RegularityBridge's private `span_image_castSucc_eq` and
`span_image_iio_last_eq_ofList` (plus the public
`span_range_eq_ofList_ofFn` for the last rung), proved here so the proved
`RegularityBridge.lean` stays untouched. -/

/-- Reindexing an initial segment of `Fin.snoc x z` along `Fin.castSucc`
recovers the initial segment of `x`. -/
theorem span_image_snoc_castSucc {S : Type u} [CommRing S] {r : ℕ}
    (x : Fin r → S) (z : S) (i : Fin r) :
    Ideal.span (Set.image (Fin.snoc (α := fun _ => S) x z)
        { j' : Fin (r + 1) | j'.val < (i.castSucc).val }) =
      Ideal.span (Set.image x { j | j.val < i.val }) := by
  rw [(rfl : (i.castSucc).val = i.val)]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j', hj', rfl⟩
    have hj'e : (⟨j'.val, lt_trans hj' i.isLt⟩ : Fin r).castSucc = j' :=
      Fin.ext rfl
    have h1 : Fin.snoc (α := fun _ => S) x z j'
        = Fin.snoc (α := fun _ => S) x z
          ((⟨j'.val, lt_trans hj' i.isLt⟩ : Fin r).castSucc) :=
      congrArg (Fin.snoc (α := fun _ => S) x z) hj'e.symm
    have h2 : Fin.snoc (α := fun _ => S) x z
          ((⟨j'.val, lt_trans hj' i.isLt⟩ : Fin r).castSucc)
        = x ⟨j'.val, lt_trans hj' i.isLt⟩ :=
      Fin.snoc_castSucc (α := fun _ => S) (n := r) z x _
    exact ⟨⟨j'.val, lt_trans hj' i.isLt⟩, hj', (h1.trans h2).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, Fin.snoc_castSucc (α := fun _ => S) (n := r) z x j⟩

#print axioms span_image_snoc_castSucc

/-- The span of the values of `Fin.snoc x z` before `Fin.last r` is the span
of the range of `x`. -/
theorem span_image_snoc_last {S : Type u} [CommRing S] {r : ℕ}
    (x : Fin r → S) (z : S) :
    Ideal.span (Set.image (Fin.snoc (α := fun _ => S) x z)
        { j' : Fin (r + 1) | j'.val < (Fin.last r).val }) =
      Ideal.span (Set.range x) := by
  rw [(rfl : (Fin.last r).val = r)]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨j', hj', rfl⟩
    have hj'e : (⟨j'.val, hj'⟩ : Fin r).castSucc = j' := Fin.ext rfl
    have h1 : Fin.snoc (α := fun _ => S) x z j'
        = Fin.snoc (α := fun _ => S) x z
          ((⟨j'.val, hj'⟩ : Fin r).castSucc) :=
      congrArg (Fin.snoc (α := fun _ => S) x z) hj'e.symm
    have h2 : Fin.snoc (α := fun _ => S) x z
          ((⟨j'.val, hj'⟩ : Fin r).castSucc)
        = x ⟨j'.val, hj'⟩ :=
      Fin.snoc_castSucc (α := fun _ => S) (n := r) z x _
    exact ⟨⟨j'.val, hj'⟩, (h1.trans h2).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, Fin.snoc_castSucc (α := fun _ => S) (n := r) z x j⟩

#print axioms span_image_snoc_last

/-! ## Quotient regularity transport (Step C3) -/

/-- Regularity of a quotient-ring element `mk z` is regularity of `z` acting
on the quotient module: both say `z • w ∈ J → w ∈ J`. -/
theorem smulRegular_of_mk_regular {S : Type u} [CommRing S]
    (J : Ideal S) (z : S)
    (hreg : IsSMulRegular (S ⧸ J) (Ideal.Quotient.mk J z)) :
    IsSMulRegular (S ⧸ (↑J : Submodule S S)) z := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro w hw
  have hmul : (Ideal.Quotient.mk J z) • (Ideal.Quotient.mk J w) = 0 := by
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have hwJ : z • w ∈ J := hw
    rwa [smul_eq_mul] at hwJ
  have h0 : Ideal.Quotient.mk J w = 0 :=
    IsSMulRegular.right_eq_zero_of_smul hreg hmul
  rwa [Ideal.Quotient.eq_zero_iff_mem] at h0

#print axioms smulRegular_of_mk_regular

/-! ## Snoc-extension (Step C) -/

/-- A non-maximal successive-regular family extends by one element via
`Fin.snoc`: prefix rungs come from the old family (C1), the last rung is the
new regular element transported across the span identification (C2+C3). -/
theorem snoc_extend_of_not_maximal {S : Type u} [CommRing S] {r : ℕ}
    (p : Ideal S) (x : Fin r → S)
    (hsucc : RegularityBridge.SuccessiveSMulRegular x)
    (hmem : ∀ i, x i ∈ p) (z : S) (hz : z ∈ p)
    (hreg : IsSMulRegular (S ⧸ Ideal.span (Set.range x))
      (Ideal.Quotient.mk (Ideal.span (Set.range x)) z)) :
    ∃ y : Fin (r + 1) → S,
      RegularityBridge.SuccessiveSMulRegular y ∧ ∀ i, y i ∈ p := by
  refine ⟨Fin.snoc (α := fun _ => S) x z, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · show IsSMulRegular
          (S ⧸ (Ideal.span (Set.image (Fin.snoc (α := fun _ => S) x z)
            { j' | j'.val < (Fin.last r).val }) • ⊤))
          (Fin.snoc (α := fun _ => S) x z (Fin.last r))
      rw [span_image_snoc_last, RegularSequenceDimDrop.span_smul_top, Fin.snoc_last]
      exact smulRegular_of_mk_regular _ z hreg
    · show IsSMulRegular
          (S ⧸ (Ideal.span (Set.image (Fin.snoc (α := fun _ => S) x z)
            { j' | j'.val < (j.castSucc).val }) • ⊤))
          (Fin.snoc (α := fun _ => S) x z j.castSucc)
      rw [span_image_snoc_castSucc, Fin.snoc_castSucc]
      exact hsucc j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · show Fin.snoc (α := fun _ => S) x z (Fin.last r) ∈ p
      rw [Fin.snoc_last]
      exact hz
    · show Fin.snoc (α := fun _ => S) x z j.castSucc ∈ p
      rw [Fin.snoc_castSucc]
      exact hmem j

#print axioms snoc_extend_of_not_maximal

/-! ## Main theorem (Steps A, B, D) -/

/-- Every prime of a Noetherian local ring contains a maximal
successive-regular sequence: lengths are bounded by `p.height.toNat` (L3),
so the classical maximal length exists, and maximality follows by
snoc-extension contradiction. -/
theorem maxSeqExists : LocalizationOfCMGap.MaximalRegularSequenceExists := by
  classical
  intro S _ _ _ p _
  set P : ℕ → Prop := fun k => ∃ x : Fin k → S,
    RegularityBridge.SuccessiveSMulRegular x ∧ ∀ i, x i ∈ p
  have hP0 : P 0 := ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hne : p.height ≠ ⊤ := Ideal.height_ne_top (inferInstance : p.IsPrime).ne_top
  have hcast : ((p.height.toNat : ℕ) : ℕ∞) = p.height := ENat.natCast_toNat hne
  have hbound : ∀ k, P k → k ≤ p.height.toNat := by
    intro k hk
    obtain ⟨x, hsucc, hmem⟩ := hk
    have hle : (k : ℕ∞) ≤ p.height :=
      LocalizationOfCMGap.length_le_height_of_localized p x hsucc hmem
    rw [← hcast] at hle
    exact ENat.natCast_le_natCast.mp hle
  set r := Nat.findGreatest P p.height.toNat
  have h0B : 0 ≤ p.height.toNat := by omega
  have hPr : P r := Nat.findGreatest_spec h0B hP0
  have hmax : ∀ m, P m → m ≤ r := fun m hm => Nat.le_findGreatest (hbound m hm) hm
  obtain ⟨x, hsucc, hmem⟩ := hPr
  refine ⟨r, x, hsucc, hmem, ?_⟩
  intro z hz hcon
  have hPext : P (r + 1) := snoc_extend_of_not_maximal p x hsucc hmem z hz hcon
  have hle : r + 1 ≤ r := hmax (r + 1) hPext
  omega

#print axioms maxSeqExists

end MaximalRegularSequenceExists
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
