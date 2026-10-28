/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortAxisRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortIntegral
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalog
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOctadStabilizerProjection

/-! The complete rational coordinates of the listed Octad representative, with its exact
120-coordinate sparse short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- The selected octad is the octad of catalogue index zero. -/
theorem generatedAxisGlobalTwelveOctadDiagonal_basis_octad_eq : generatedOctadBasisOctad = 0 := by
  apply (golayOctads.orderIsoOfFin golayOctads_card).injective
  apply Subtype.ext
  have h1 : golayOctadLabel generatedOctadBasisOctad = 3 :=
    congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
      ⟨3, by decide +kernel⟩)
  have h0 : golayOctadLabel 0 = 3 := by
    rw [← generatedAxisGlobalOctadCodeData_actual]
    rfl
  exact h1.trans h0.symm

/-- The executable signed-short packet of the octad-zero axis before triality. -/
def generatedAxisGlobalTwelveOctadDiagonalInitialPacket : GeneratedAxisGlobalRationalPacket :=
  ((fun i j => (generatedAxisGlobalShortIntegral (Sum.inr (Sum.inl (0, 0))) i : ℚ) *
      (generatedAxisGlobalShortIntegral (Sum.inr (Sum.inl (0, 0))) j : ℚ) / 4),
    ((fun s => if (Sum.inr (Sum.inl (0, 0)) : GriessShortIndex) = s then -8 else 0), 0))

/-- The executable packet is the original signed-short packet. -/
theorem generatedAxisGlobalTwelveOctadDiagonalInitialPacket_eq :
    generatedAxisGlobalShortAxisRationalPacket (Sum.inr (Sum.inl (0, 0))) 0 =
      generatedAxisGlobalTwelveOctadDiagonalInitialPacket := by
  simp only [generatedAxisGlobalShortAxisRationalPacket, generatedAxisGlobalTwelveOctadDiagonalInitialPacket,
    generatedAxisGlobalShortIntegral_actual, generatedAxisGlobalIntSign, ite_true, Int.cast_one,
    mul_one]

/-- The complete rational packet of the listed Octad representative. -/
def generatedAxisGlobalTwelveOctadDiagonalVPacket : GeneratedAxisGlobalRationalPacket :=
  generatedAxisGlobalRationalTriality generatedAxisGlobalTwelveOctadDiagonalInitialPacket

/-- The packet gives every actual coordinate of the listed Octad representative. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVPacket_actual :
    griessConwayEncode (generatedOctadLocalAxis 0 0) =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalTwelveOctadDiagonalVPacket := by
  change griessConwayEncode (sExtra (conwayShortAxis
    (Sum.inr (Sum.inl (generatedOctadBasisOctad, 0))) 0)) = _
  rw [generatedAxisGlobalTwelveOctadDiagonal_basis_octad_eq]
  apply generatedAxisGlobalRationalTriality_of_actual
  rw [← generatedAxisGlobalTwelveOctadDiagonalInitialPacket_eq]
  exact generatedAxisGlobalShortAxisRationalPacket_actual _ _

/-- Sparse lookup of the source support labels. -/
def generatedAxisGlobalTwelveOctadDiagonalVTree : GeneratedAxisGlobalSparseLookupTree (Fin 120) :=
  (.branch 556 60
    (.branch 434 30
      (.branch 187 15
        (.branch 171 7
          (.branch 159 3
            (.branch 157 1
              (.branch 156 0
                .empty
                .empty)
              (.branch 158 2
                .empty
                .empty))
            (.branch 161 5
              (.branch 160 4
                .empty
                .empty)
              (.branch 162 6
                .empty
                .empty)))
          (.branch 175 11
            (.branch 173 9
              (.branch 172 8
                .empty
                .empty)
              (.branch 174 10
                .empty
                .empty))
            (.branch 185 13
              (.branch 176 12
                .empty
                .empty)
              (.branch 186 14
                .empty
                .empty))))
        (.branch 211 23
          (.branch 199 19
            (.branch 189 17
              (.branch 188 16
                .empty
                .empty)
              (.branch 198 18
                .empty
                .empty))
            (.branch 201 21
              (.branch 200 20
                .empty
                .empty)
              (.branch 210 22
                .empty
                .empty)))
          (.branch 231 27
            (.branch 221 25
              (.branch 212 24
                .empty
                .empty)
              (.branch 222 26
                .empty
                .empty))
            (.branch 433 29
              (.branch 432 28
                .empty
                .empty)
              .empty))))
      (.branch 465 45
        (.branch 450 38
          (.branch 438 34
            (.branch 436 32
              (.branch 435 31
                .empty
                .empty)
              (.branch 437 33
                .empty
                .empty))
            (.branch 448 36
              (.branch 447 35
                .empty
                .empty)
              (.branch 449 37
                .empty
                .empty)))
          (.branch 462 42
            (.branch 452 40
              (.branch 451 39
                .empty
                .empty)
              (.branch 461 41
                .empty
                .empty))
            (.branch 464 44
              (.branch 463 43
                .empty
                .empty)
              .empty)))
        (.branch 497 53
          (.branch 477 49
            (.branch 475 47
              (.branch 474 46
                .empty
                .empty)
              (.branch 476 48
                .empty
                .empty))
            (.branch 487 51
              (.branch 486 50
                .empty
                .empty)
              (.branch 488 52
                .empty
                .empty)))
          (.branch 553 57
            (.branch 507 55
              (.branch 498 54
                .empty
                .empty)
              (.branch 552 56
                .empty
                .empty))
            (.branch 555 59
              (.branch 554 58
                .empty
                .empty)
              .empty)))))
    (.branch 586 90
      (.branch 571 75
        (.branch 564 68
          (.branch 560 64
            (.branch 558 62
              (.branch 557 61
                .empty
                .empty)
              (.branch 559 63
                .empty
                .empty))
            (.branch 562 66
              (.branch 561 65
                .empty
                .empty)
              (.branch 563 67
                .empty
                .empty)))
          (.branch 568 72
            (.branch 566 70
              (.branch 565 69
                .empty
                .empty)
              (.branch 567 71
                .empty
                .empty))
            (.branch 570 74
              (.branch 569 73
                .empty
                .empty)
              .empty)))
        (.branch 579 83
          (.branch 575 79
            (.branch 573 77
              (.branch 572 76
                .empty
                .empty)
              (.branch 574 78
                .empty
                .empty))
            (.branch 577 81
              (.branch 576 80
                .empty
                .empty)
              (.branch 578 82
                .empty
                .empty)))
          (.branch 583 87
            (.branch 581 85
              (.branch 580 84
                .empty
                .empty)
              (.branch 582 86
                .empty
                .empty))
            (.branch 585 89
              (.branch 584 88
                .empty
                .empty)
              .empty))))
      (.branch 601 105
        (.branch 594 98
          (.branch 590 94
            (.branch 588 92
              (.branch 587 91
                .empty
                .empty)
              (.branch 589 93
                .empty
                .empty))
            (.branch 592 96
              (.branch 591 95
                .empty
                .empty)
              (.branch 593 97
                .empty
                .empty)))
          (.branch 598 102
            (.branch 596 100
              (.branch 595 99
                .empty
                .empty)
              (.branch 597 101
                .empty
                .empty))
            (.branch 600 104
              (.branch 599 103
                .empty
                .empty)
              .empty)))
        (.branch 609 113
          (.branch 605 109
            (.branch 603 107
              (.branch 602 106
                .empty
                .empty)
              (.branch 604 108
                .empty
                .empty))
            (.branch 607 111
              (.branch 606 110
                .empty
                .empty)
              (.branch 608 112
                .empty
                .empty)))
          (.branch 613 117
            (.branch 611 115
              (.branch 610 114
                .empty
                .empty)
              (.branch 612 116
                .empty
                .empty))
            (.branch 615 119
              (.branch 614 118
                .empty
                .empty)
              .empty))))))

/-- The source label stored at a preferred short coordinate, if any. -/
def generatedAxisGlobalTwelveOctadDiagonalVSource (r : GriessShortIndex) : Option (Fin 120) :=
  generatedAxisGlobalSparseLookup generatedAxisGlobalTwelveOctadDiagonalVTree (generatedAxisGlobalShortNumber r)

/-- The candidate source short coefficient. -/
def generatedAxisGlobalTwelveOctadDiagonalVShortQ (r : GriessShortIndex) : ℚ :=
  match generatedAxisGlobalTwelveOctadDiagonalVSource r with
  | some k => generatedAxisGlobalTwelveOctadDiagonalVCoeff k
  | none => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every stored source key is the exact catalogue number of its label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVTree_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun k => generatedAxisGlobalShortNumber (generatedAxisGlobalTwelveOctadDiagonalVLabel k)) generatedAxisGlobalTwelveOctadDiagonalVTree := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- All source labels round trip through the lookup. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVSource_roundtrip : ∀ k : Fin 120,
    generatedAxisGlobalTwelveOctadDiagonalVSource (generatedAxisGlobalTwelveOctadDiagonalVLabel k) = some k := by
  decide +kernel

/-- Every successful lookup returns the label at that coordinate. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVSource_sound (r : GriessShortIndex) (k : Fin 120)
    (h : generatedAxisGlobalTwelveOctadDiagonalVSource r = some k) : generatedAxisGlobalTwelveOctadDiagonalVLabel k = r :=
  generatedAxisGlobalShortNumber_injective
    (generatedAxisGlobalSparseLookup_sound _ _ generatedAxisGlobalTwelveOctadDiagonalVTree_valid _ _ h)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every source label is a pair label or an octad-zero label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVLabel_family : ∀ k : Fin 120,
    (∃ s p, generatedAxisGlobalTwelveOctadDiagonalVLabel k = Sum.inl (s, p)) ∨
      ∃ e, generatedAxisGlobalTwelveOctadDiagonalVLabel k = Sum.inr (Sum.inl (0, e)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
/-- Both pair families have exactly the candidate source coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVPair_certificate : ∀ s : Fin 2, ∀ p : Fin 276,
    generatedAxisGlobalTwelveOctadDiagonalVPacket.2.1 (Sum.inl (s, p)) = generatedAxisGlobalTwelveOctadDiagonalVShortQ (Sum.inl (s, p)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
/-- The octad-zero coordinates have exactly the candidate source coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVOctad_certificate : ∀ e : Fin 64,
    generatedAxisGlobalTwelveOctadDiagonalVPacket.2.1 (Sum.inr (Sum.inl (0, e))) =
      generatedAxisGlobalTwelveOctadDiagonalVShortQ (Sum.inr (Sum.inl (0, e))) := by
  decide +kernel

/-- No label of another family or octad is stored. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVShortQ_zero (r : GriessShortIndex)
    (hr : (∀ s p, r ≠ Sum.inl (s, p)) ∧ ∀ e, r ≠ Sum.inr (Sum.inl (0, e))) :
    generatedAxisGlobalTwelveOctadDiagonalVShortQ r = 0 := by
  unfold generatedAxisGlobalTwelveOctadDiagonalVShortQ
  cases h : generatedAxisGlobalTwelveOctadDiagonalVSource r with
  | none => rfl
  | some k =>
    exfalso
    have hk := generatedAxisGlobalTwelveOctadDiagonalVSource_sound r k h
    rcases generatedAxisGlobalTwelveOctadDiagonalVLabel_family k with ⟨s, p, hs⟩ | ⟨e, he⟩
    · exact hr.1 s p (hk.symm.trans hs)
    · exact hr.2 e (hk.symm.trans he)

/-- The complete source short coordinates are the sparse candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVShort_sparse (r : GriessShortIndex) :
    generatedAxisGlobalTwelveOctadDiagonalVPacket.2.1 r = generatedAxisGlobalTwelveOctadDiagonalVShortQ r := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · exact generatedAxisGlobalTwelveOctadDiagonalVPair_certificate s p
  · by_cases ho : o = 0
    · subst ho
      exact generatedAxisGlobalTwelveOctadDiagonalVOctad_certificate e
    · have hz : (∀ s p, (Sum.inr (Sum.inl (o, e)) : GriessShortIndex) ≠ Sum.inl (s, p)) ∧
          ∀ e', (Sum.inr (Sum.inl (o, e)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (0, e')) := by
        refine ⟨fun s p h => ?_, fun e' h => ?_⟩
        · cases h
        · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
          exact ho h.1
      rw [generatedAxisGlobalTwelveOctadDiagonalVShortQ_zero _ hz]
      simp only [generatedAxisGlobalTwelveOctadDiagonalVPacket, generatedAxisGlobalRationalTriality,
        generatedAxisGlobalTrialityShortQ, generatedAxisGlobalTwelveOctadDiagonalInitialPacket]
      apply Finset.sum_eq_zero
      intro f _
      have hne : (Sum.inr (Sum.inl (0, 0)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (o, f)) := by
        intro h
        simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        exact ho h.1.symm
      simp only [hne, ite_false, mul_zero]
  · have hz : (∀ s p, (Sum.inr (Sum.inr (d, j)) : GriessShortIndex) ≠ Sum.inl (s, p)) ∧
        ∀ e, (Sum.inr (Sum.inr (d, j)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (0, e)) := by
      refine ⟨fun s p h => ?_, fun e h => ?_⟩
      · cases h
      · cases h
    rw [generatedAxisGlobalTwelveOctadDiagonalVShortQ_zero _ hz]
    simp only [generatedAxisGlobalTwelveOctadDiagonalVPacket, generatedAxisGlobalRationalTriality,
      generatedAxisGlobalTrialityShortQ, generatedAxisGlobalTwelveOctadDiagonalInitialPacket, Pi.zero_apply, add_zero,
      mul_zero, zero_div]

/-- The source short coordinates as a finite sum of preferred units. -/
theorem generatedAxisGlobalTwelveOctadDiagonalVShort_sum :
    (griessConwayEncode (generatedOctadLocalAxis 0 0)).2.1 =
      ∑ k : Fin 120, ((generatedAxisGlobalTwelveOctadDiagonalVCoeff k : ℚ) : ℝ) • Pi.single (generatedAxisGlobalTwelveOctadDiagonalVLabel k) (1 : ℝ) := by
  funext r
  rw [generatedAxisGlobalTwelveOctadDiagonalVPacket_actual]
  change ((generatedAxisGlobalTwelveOctadDiagonalVPacket.2.1 r : ℚ) : ℝ) = _
  rw [generatedAxisGlobalTwelveOctadDiagonalVShort_sparse]
  have h := generatedAxisGlobalSparseLookup_sum generatedAxisGlobalTwelveOctadDiagonalVLabel generatedAxisGlobalTwelveOctadDiagonalVSource
    generatedAxisGlobalTwelveOctadDiagonalVSource_roundtrip generatedAxisGlobalTwelveOctadDiagonalVSource_sound generatedAxisGlobalTwelveOctadDiagonalVCoeff r
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  have h' : ((∑ k : Fin 120, generatedAxisGlobalTwelveOctadDiagonalVCoeff k * (if generatedAxisGlobalTwelveOctadDiagonalVLabel k = r then 1 else 0) : ℚ) : ℝ) =
      ∑ k : Fin 120, if r = generatedAxisGlobalTwelveOctadDiagonalVLabel k then ((generatedAxisGlobalTwelveOctadDiagonalVCoeff k : ℚ) : ℝ) else 0 := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : generatedAxisGlobalTwelveOctadDiagonalVLabel k = r
    · simp [hk]
    · simp [hk, Ne.symm hk]
  rw [← h']
  congr 1
  rw [h]
  unfold generatedAxisGlobalTwelveOctadDiagonalVShortQ
  cases generatedAxisGlobalTwelveOctadDiagonalVSource r <;> rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
