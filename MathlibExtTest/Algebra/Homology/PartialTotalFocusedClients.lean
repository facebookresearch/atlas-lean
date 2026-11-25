/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import MathlibExt.Algebra.Homology.PartialTotalZero

/-!
# A finite square client for the partial-total filtration

The four cells in bidegrees `{0,1} × {0,1}` are copies of `ℚ`; every other cell is zero.
Both horizontal and vertical differentials from degree one to degree zero are identities.
The bicomplex square commutes before totalization. The totalization supplies the sign
`(-1)^p` on row `p`, so the last-row quotient at `p = 1` has differential `-id`.

These clients evaluate the zero and successor stages on nonzero generators, check a
successor short complex whose two arrows are nonzero, and verify degreewise stabilization
after the support ends. In particular, the odd-row sign is tested against the wrong `+1`
answer, rather than on a vector killed by the differential.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace PartialTotalFocusedClients

private abbrev Q := ModuleCat.of ℚ ℚ

private abbrev cells : ℕ → ModuleCat ℚ
  | 0 => Q
  | 1 => Q
  | _ + 2 => 0

private def vertical : ∀ n : ℕ, cells (n + 1) ⟶ cells n
  | 0 => 𝟙 Q
  | _ + 1 => 0

private lemma vertical_sq (n : ℕ) : vertical (n + 1) ≫ vertical n = 0 := by
  change (0 : cells (n + 2) ⟶ cells (n + 1)) ≫ vertical n = 0
  exact zero_comp

private abbrev row : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of cells vertical vertical_sq

private abbrev rows : ℕ → ChainComplex (ModuleCat ℚ) ℕ
  | 0 => row
  | 1 => row
  | _ + 2 => 0

private def horizontal : ∀ n : ℕ, rows (n + 1) ⟶ rows n
  | 0 => 𝟙 row
  | _ + 1 => 0

private lemma horizontal_sq (n : ℕ) : horizontal (n + 1) ≫ horizontal n = 0 := by
  change (0 : rows (n + 2) ⟶ rows (n + 1)) ≫ horizontal n = 0
  exact zero_comp

private abbrev square : HomologicalComplex₂ (ModuleCat ℚ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) :=
  ChainComplex.of rows horizontal horizontal_sq

private lemma row_d : row.d 1 0 = 𝟙 Q :=
  ChainComplex.of_d cells vertical 0

private lemma square_vertical : (square.X 1).d 1 0 = 𝟙 Q := row_d

private lemma square_horizontal : square.d 1 0 = 𝟙 row :=
  ChainComplex.of_d rows horizontal 0

-- These two nonzero maps, not just their composites, are part of the fixture.
example : (square.X 1).d 1 0 ≠ 0 := by
  intro h
  rw [square_vertical] at h
  have h1 := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) h
  have hzero : (1 : ℚ) = 0 := h1
  exact one_ne_zero hzero

example : (square.d 1 0).f 1 ≠ 0 := by
  intro h
  rw [square_horizontal] at h
  have h1 := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) h
  have hzero : (1 : ℚ) = 0 := h1
  exact one_ne_zero hzero

example : (square.d 1 0).f 1 ≫ (square.X 0).d 1 0 =
    (square.X 1).d 1 0 ≫ (square.d 1 0).f 0 :=
  (square.d 1 0).comm 1 0

-- Finiteness means zero objects outside the rectangle, not zero differentials on
-- an infinite collection of nonzero carriers.
example (n : ℕ) : square.X (n + 2) = 0 := rfl

example (n : ℕ) : (square.X 0).X (n + 2) = 0 := rfl

example (n : ℕ) : (square.X 1).X (n + 2) = 0 := rfl

private def zeroRecover (n : ℕ) : (square.partialTotal 0).X n ⟶ (square.X 0).X n :=
  (square.partialTotalRowQuotient 0).f n ≫
    (square.totalRowXIso 0 n n (Nat.zero_add n)).hom

private lemma zeroRecover_coordinate (n : ℕ) :
    square.partialTotalComponent 0 ⟨0, by omega⟩ n n (Nat.zero_add n) ≫
      zeroRecover n = 𝟙 _ := by
  unfold zeroRecover
  rw [← Category.assoc, square.partialTotalComponent_comp_partialTotalRowQuotient]
  exact Iso.inv_hom_id _

private def oldGenerator : (square.partialTotal 0).X 1 :=
  (square.partialTotalComponent 0 ⟨0, by omega⟩ 1 1 rfl).hom (1 : ℚ)

private lemma oldGenerator_value : (zeroRecover 1).hom oldGenerator = (1 : ℚ) := by
  have h := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) (zeroRecover_coordinate 1)
  simpa [ModuleCat.hom_comp, oldGenerator] using h

private lemma oldGenerator_ne_zero : oldGenerator ≠ 0 := by
  intro h
  have h1 := oldGenerator_value
  rw [h, map_zero] at h1
  exact zero_ne_one h1

-- The public zero-stage presentation is an actual split short-exact client.
example : square.partialTotalZeroShortComplex.ShortExact :=
  square.partialTotalZeroShortExact

example : ((square.partialTotalZeroShortComplex).map
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)).ShortExact :=
  (square.partialTotalZeroDegreeSplitting 1).shortExact

example : square.partialTotalRowQuotientF 0 1 ≫
    square.partialTotalRowQuotientSectionF 0 1 = 𝟙 _ :=
  square.partialTotalRowQuotientF_zero_comp_sectionF 1

private abbrev step := square.partialTotalSuccShortComplex 0

private lemma inclusion_f_ne_zero : square.partialTotalSuccInclusionF 0 1 ≠ 0 := by
  intro h
  have hid := square.partialTotalMap_f_comp_partialTotalSuccRetractionF 0 1
  rw [h, zero_comp] at hid
  have hvalue := congrArg (fun f : (square.partialTotal 0).X 1 ⟶
    (square.partialTotal 0).X 1 => f.hom oldGenerator) hid
  change (0 : (square.partialTotal 0).X 1) = oldGenerator at hvalue
  exact oldGenerator_ne_zero hvalue.symm

private def lastRecover : (square.partialTotal 1).X 1 ⟶ Q :=
  (square.partialTotalRowQuotient 1).f 1 ≫ (square.totalRowXIso 1 0 1 rfl).hom

private lemma lastRecover_coordinate :
    square.partialTotalComponent 1 ⟨1, by omega⟩ 0 1 rfl ≫ lastRecover = 𝟙 Q := by
  unfold lastRecover
  rw [← Category.assoc, square.partialTotalComponent_comp_partialTotalRowQuotient]
  exact Iso.inv_hom_id _

private lemma quotient_f_ne_zero : (square.partialTotalRowQuotient 1).f 1 ≠ 0 := by
  intro h
  have hvalue := congrArg (fun f : Q ⟶ Q => f.hom (1 : ℚ)) lastRecover_coordinate
  unfold lastRecover at hvalue
  simp only [h] at hvalue
  simp at hvalue

example : step.f ≠ 0 := by
  intro h
  have hf := HomologicalComplex.congr_hom h 1
  change square.partialTotalSuccInclusionF 0 1 = 0 at hf
  exact inclusion_f_ne_zero hf

example : step.g ≠ 0 := by
  intro h
  have hg := HomologicalComplex.congr_hom h 1
  change (square.partialTotalRowQuotient 1).f 1 = 0 at hg
  exact quotient_f_ne_zero hg

-- The quotient kills the old row, not all rows: both short-complex arrows above
-- are nonzero, and the last-row coordinate still survives with value one.
example : step.f ≫ step.g = 0 := step.zero

example : ((square.partialTotalRowQuotient 1).f 1).hom
    (((square.partialTotalMap (Nat.zero_le 1)).f 1).hom oldGenerator) = 0 := by
  have h := HomologicalComplex.congr_hom
    (square.partialTotalMap_comp_partialTotalRowQuotient 0) 1
  have hv := congrArg
    (fun f : (square.partialTotal 0).X 1 ⟶ (square.totalRow 1).X 1 => f.hom oldGenerator) h
  change ((square.partialTotalRowQuotient 1).f 1).hom
    (((square.partialTotalMap (Nat.zero_le 1)).f 1).hom oldGenerator) = 0 at hv
  exact hv

example : step.ShortExact := square.partialTotalSuccShortExact 0

example : ((square.partialTotalSuccShortComplex 0).map
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)).ShortExact :=
  (square.partialTotalSuccDegreeSplitting 0 1).shortExact

-- At the odd last row the quotient transports the nonzero vertical identity to
-- minus the identity in total degrees 2 -> 1.
private lemma signedQuotient_identity :
    square.partialTotalComponent 1 ⟨1, by omega⟩ 1 2 rfl ≫
      (square.partialTotalRowQuotient 1).f 2 ≫ (square.totalRow 1).d 2 1 ≫
        (square.totalRowXIso 1 0 1 rfl).hom = -(𝟙 Q) := by
  rw [square.partialTotalComponent_comp_partialTotalRowQuotient_assoc]
  rw [square.totalRowXIso_inv_comp_d_assoc 1 1 0 2 1 rfl rfl]
  rw [Iso.inv_hom_id, Category.comp_id]
  rw [square_vertical]
  simp only [ComplexShape.ε_down_ℕ, pow_one]
  rw [Units.neg_smul, one_smul]

private abbrev signedQuotientMap : Q ⟶ Q :=
  square.partialTotalComponent 1 ⟨1, by omega⟩ 1 2 rfl ≫
    (square.partialTotalRowQuotient 1).f 2 ≫ (square.totalRow 1).d 2 1 ≫
      (square.totalRowXIso 1 0 1 rfl).hom

private lemma signedQuotient_value : signedQuotientMap.hom (7 : ℚ) = (-7 : ℚ) := by
  simpa [ModuleCat.hom_comp, signedQuotientMap] using
    congrArg (fun f : Q ⟶ Q => f.hom (7 : ℚ)) signedQuotient_identity

-- This negative guard would fail if the first-coordinate sign were omitted.
example : signedQuotientMap.hom (7 : ℚ) ≠ (7 : ℚ) := by
  rw [signedQuotient_value]
  norm_num

-- Row two is genuinely outside the support. The successor quotient is zero,
-- and the degreewise inclusion/retraction are both inverses after stabilization.
private lemma beyond_quotient_zero : square.partialTotalRowQuotient 2 = 0 := by
  apply square.partialTotal_hom_ext 2
  intro i j n hn
  by_cases hi : i.1 = 2
  · have hz : IsZero ((square.X i.1).X j) := by
      rw [hi]
      exact (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) j).map_isZero
        (show IsZero (square.X 2) from isZero_zero _)
    exact hz.eq_of_src _ _
  · simp only [HomologicalComplex.zero_f, comp_zero]
    exact square.partialTotalComponent_comp_partialTotalRowQuotient_eq_zero 2 i j n hn hi

example (n : ℕ) : square.partialTotalSuccInclusionF 1 n ≫
    square.partialTotalSuccRetractionF 1 n = 𝟙 _ :=
  square.partialTotalMap_f_comp_partialTotalSuccRetractionF 1 n

example (n : ℕ) : square.partialTotalSuccRetractionF 1 n ≫
    square.partialTotalSuccInclusionF 1 n = 𝟙 _ := by
  have h := square.partialTotalSuccRetractionF_comp_map_f_add_quotientF_comp_sectionF 1 n
  have hz := HomologicalComplex.congr_hom beyond_quotient_zero n
  change square.partialTotalRowQuotientF 2 n = 0 at hz
  rw [hz, zero_comp, add_zero] at h
  exact h

end PartialTotalFocusedClients
