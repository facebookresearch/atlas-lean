/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadQBound

/-! Small integer certificates expressing the supported roots in an E8 basis.
All data come from the original eight preferred-short vectors, with ordinary
kernel checks; no class or section orbit count is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Inclusion of the eight octad coordinates into their original MOG positions. -/
def generatedOctadIntegerInsert : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 24 → ℤ) where
  toFun v i := if h : 8 ≤ i.val ∧ i.val < 16 then v ⟨i.val - 8, by omega⟩ else 0
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

/-- The six difference roots, sum root, and half-sum root in local coordinates. -/
def generatedOctadIntegerRootMatrix : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![4, 4, 4, 4, 4, 4, 4, 2],
    ![-4, 0, 0, 0, 0, 0, 4, 2],
    ![0, -4, 0, 0, 0, 0, 0, 2],
    ![0, 0, -4, 0, 0, 0, 0, 2],
    ![0, 0, 0, -4, 0, 0, 0, 2],
    ![0, 0, 0, 0, -4, 0, 0, 2],
    ![0, 0, 0, 0, 0, -4, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 2]]

/-- Integer coefficients for the root basis. The exact divisibility for the
pair and even-octad patterns is verified below. -/
def generatedOctadIntegerRootCoordinates (v : Fin 8 → ℤ) (j : Fin 8) : ℤ :=
  let b := ((∑ k, v k) - 8 * v 7) / 8
  if h : j.val < 6 then
    (v 7 - v ⟨j.val + 1, by omega⟩) / 4 + if j = 0 then b else 0
  else if j = 6 then b else v 7 / 2

/-- A local coordinate pair of either sign, including repeated indices. -/
def generatedOctadIntegerPair (s : Fin 2) (i j : Fin 8) (k : Fin 8) : ℤ :=
  4 * (if k = i then 1 else 0) + (if s = 0 then -4 else 4) * (if k = j then 1 else 0)

/-- The actual even-sign octad patterns in local coordinates. -/
def generatedOctadIntegerSigns (e : Fin 64) (k : Fin 8) : ℤ :=
  if (trialityEvenMask e).testBit k.val then -2 else 2

/-- Physical binding of this small matrix to the committed Leech basis certificate. -/
theorem generatedOctadIntegerRoot_physical_certificate : ∀ j : Fin 8,
    leechBasisMatrix *ᵥ generatedOctadBasisIntegerCoordinates.col j =
      generatedOctadIntegerInsert (generatedOctadIntegerRootMatrix.col j) := by
  decide +kernel

/-- Every local pair pattern is an integer combination of the eight actual roots. -/
theorem generatedOctadIntegerPair_span_certificate : ∀ (s : Fin 2) (i j : Fin 8),
    generatedOctadIntegerRootMatrix *ᵥ
      generatedOctadIntegerRootCoordinates (generatedOctadIntegerPair s i j) =
        generatedOctadIntegerPair s i j := by
  decide +kernel

/-- Every even octad sign pattern is an integer combination of these roots. -/
theorem generatedOctadIntegerSigns_span_certificate : ∀ e : Fin 64,
    generatedOctadIntegerRootMatrix *ᵥ
      generatedOctadIntegerRootCoordinates (generatedOctadIntegerSigns e) =
        generatedOctadIntegerSigns e := by
  decide +kernel

/-- Exact insertion of local pair patterns into the physical 24 coordinates. -/
theorem generatedOctadIntegerPair_insert_certificate : ∀ (s : Fin 2) (i j : Fin 8),
    generatedOctadIntegerInsert (generatedOctadIntegerPair s i j) =
      (fun k : Fin 24 =>
        4 * (if k = ⟨8 + i.val, by omega⟩ then 1 else 0) +
          (if s = 0 then -4 else 4) * (if k = ⟨8 + j.val, by omega⟩ then 1 else 0)) := by
  decide +kernel

/-- Exact insertion of the 64 even-sign patterns into the physical octad mask. -/
theorem generatedOctadIntegerSigns_insert_certificate : ∀ e : Fin 64,
    generatedOctadIntegerInsert (generatedOctadIntegerSigns e) =
      (fun k : Fin 24 => if (0xff00 : ℕ).testBit k.val then
        if (trialityEvenMask e * 256).testBit k.val then -2 else 2 else 0) := by
  decide +kernel

/-- The increasing local coordinates of the selected original octad are exactly 8--15. -/
theorem generatedOctadBasisOctad_coordinate (k : Fin 8) :
    golayOctadCoordinate generatedOctadBasisOctad k = ⟨8 + k.val, by omega⟩ := by
  let t := golayMaskSupport (golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val)
  let e := t.orderIsoOfFin (golayOctad_support_card generatedOctadBasisOctad)
  have hm : (0xff00 : ℕ).testBit (8 + k.val) = true := by
    have hc : ∀ j : Fin 8, (0xff00 : ℕ).testBit (8 + j.val) = true := by decide +kernel
    exact hc k
  let v : t := ⟨⟨8 + k.val, by omega⟩, by
    simp only [t, golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      generatedOctadBasisOctad_mask]
    exact hm⟩
  have he : e.symm v = k := by
    apply Fin.ext
    rw [Finset.orderIsoOfFin_symm_apply]
    change (golayMaskSupport
      (golayEncodedMask (golayOctadLabel generatedOctadBasisOctad).val)).sort.idxOf
        (⟨8 + k.val, by omega⟩ : Fin 24) = k.val
    rw [generatedOctadBasisOctad_mask]
    have hs : (golayMaskSupport 0xff00).sort =
        ([8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 24)) := by
      apply (golayMaskSupport 0xff00).sortedLT_sort.eq_of_mem_iff
        (by decide +kernel)
      intro i
      simp only [Finset.mem_sort]
      have hc : ∀ j : Fin 24, j ∈ golayMaskSupport 0xff00 ↔
          j ∈ ([8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 24)) := by decide +kernel
      exact hc i
    rw [hs]
    have hc : ∀ j : Fin 8, ([8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 24)).idxOf
        (⟨8 + j.val, by omega⟩ : Fin 24) = j.val := by decide +kernel
    exact hc k
  have hv : e k = v := by rw [← he, e.apply_symm_apply]
  exact congrArg Subtype.val hv

/-- The original even sign mask agrees with the eight local bits shifted to 8--15. -/
theorem generatedOctadBasisOctad_sign_mask (e : Fin 64) :
    griessOctadSignMask generatedOctadBasisOctad e = trialityEvenMask e * 256 := by
  unfold griessOctadSignMask
  simp_rw [generatedOctadBasisOctad_coordinate]
  have hc : ∀ f : Fin 64,
      ((List.finRange 8).foldr (fun k m =>
        (if (trialityEvenMask f).testBit k.val then 2 ^ (8 + k.val) else 0) ||| m) 0) =
          trialityEvenMask f * 256 := by decide +kernel
  exact hc e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
