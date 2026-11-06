/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton u transport of the entire seventh short-coordinate state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSeventhExpansion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortForward

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The coordinate inclusion of the pure-short summand in the original raw space. -/
def monsterNortonRawShortLiftLinear : (GriessShortIndex → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun X := (0, (X, 0))
  map_add' X Y := by simp only [Prod.mk_add_mk, zero_add]
  map_smul' c X := by simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]

/-- The actual pure-short inclusion as a real linear map. -/
noncomputable def monsterNortonShortLiftLinear : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp monsterNortonRawShortLiftLinear

/-- This inclusion is exactly the original Conway pure-short decoding. -/
theorem monsterNortonShortLiftLinear_apply (X : GriessShortIndex → ℝ) :
    monsterNortonShortLiftLinear X = griessConwayDecode (0, (X, 0)) := by
  rw [monsterNortonShortLiftLinear, LinearMap.comp_apply]
  rfl

private theorem sign_lookup_label (p : Fin 32) :
    monsterNortonLine01OctadSignLookup (monsterNortonLine01OctadSignLabel p) = p := by
  revert p
  decide +kernel

private theorem sign_label_injective : Function.Injective monsterNortonLine01OctadSignLabel :=
  Function.LeftInverse.injective sign_lookup_label

private theorem seventh_coefficient_zero (j : Fin 16) (e : Fin 64)
    (he : ¬ monsterNortonLine01OctadSignSupport e) :
    monsterNortonLine01OctadSeventhCoefficientLookup j e = 0 := by
  revert j e he
  decide +kernel

private theorem supported_sign_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (j : Fin 16) (f : Fin 64 → E) :
    (∑ e : Fin 64, (monsterNortonLine01OctadSeventhCoefficientLookup j e : ℝ) • f e) =
      ∑ p : Fin 32,
        (monsterNortonLine01OctadSeventhCoefficientLookup j
          (monsterNortonLine01OctadSignLabel p) : ℝ) • f (monsterNortonLine01OctadSignLabel p) := by
  let s := Finset.univ.image monsterNortonLine01OctadSignLabel
  have hz : ∀ e ∈ Finset.univ, e ∉ s →
      (monsterNortonLine01OctadSeventhCoefficientLookup j e : ℝ) • f e = 0 := by
    intro e _ he
    have hs : ¬ monsterNortonLine01OctadSignSupport e := by
      intro hs
      apply he
      exact Finset.mem_image.mpr ⟨monsterNortonLine01OctadSignLookup e, Finset.mem_univ _, hs⟩
    rw [seventh_coefficient_zero j e hs, Int.cast_zero, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ s) hz]
  exact Finset.sum_image (fun a _ b _ h => sign_label_injective h)

private theorem source_output (j : Fin 16) (p : Fin 32) :
    monsterNortonLine01ShortInverseOutput (monsterNortonLine01OctadSourceA j p)
      (monsterNortonLine01OctadSourceK j p) =
        Sum.inr (Sum.inl
          (monsterNortonLine01OctadIndex j, monsterNortonLine01OctadSignLabel p)) := by
  have h := monsterNortonLine01OctadSource_right j p
  rw [monsterNortonLine01ShortInverseOutput, ite_eq_left h.1]
  change Sum.inr (Sum.inl
    (monsterNortonLine01OctadIndex (monsterNortonLine01ShortInverseOctadId
      (monsterNortonLine01OctadSourceA j p) (monsterNortonLine01OctadSourceK j p)),
      monsterNortonLine01ShortInverseOctadSigns (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p))) = _
  rw [h.2.1, h.2.2]

/-- Actual Norton u sends each supported seventh octad unit to its original signed source X unit. -/
theorem monsterNortonLine01ShortSeventhU_basis (j : Fin 16) (p : Fin 32) :
    y555NortonActualU.val (monsterNortonShortLiftLinear
      (Pi.single (Sum.inr (Sum.inl
        (monsterNortonLine01OctadIndex j, monsterNortonLine01OctadSignLabel p))) 1)) =
      qSign (monsterNortonLine01ShortInversePhase (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p)) •
        trialityXYZBasis 0 (finProdFinEquiv
          (monsterNortonLine01ShortInputCode (monsterNortonLine01OctadSourceA j p),
            monsterNortonLine01ShortPhysicalColumn (monsterNortonLine01OctadSourceK j p))) := by
  rw [monsterNortonShortLiftLinear_apply]
  have h := monsterNortonLine01ShortForward_actual (monsterNortonLine01OctadSourceA j p)
    (monsterNortonLine01OctadSourceK j p)
  rw [source_output] at h
  exact h

/-- The exact finite odd-short Griess vector reached by applying u to the seventh short state. -/
noncomputable def monsterNortonLine01ShortSeventhUVector : GriessSpace :=
  (1 / 512 : ℝ) • ∑ j : Fin 16, ∑ p : Fin 32,
    (monsterNortonLine01OctadSeventhCoefficientLookup j
      (monsterNortonLine01OctadSignLabel p) : ℝ) •
      (qSign (monsterNortonLine01ShortInversePhase (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p)) •
        trialityXYZBasis 0 (finProdFinEquiv
          (monsterNortonLine01ShortInputCode (monsterNortonLine01OctadSourceA j p),
            monsterNortonLine01ShortPhysicalColumn (monsterNortonLine01OctadSourceK j p))))

/-- This is the full actual u transport of the entire seventh short summand. -/
theorem monsterNortonLine01ShortSeventhU_actual :
    y555NortonActualU.val (monsterNortonShortLiftLinear
      (griessConwayEncode (sExtra monsterNortonLine01TensorAfterVUExtraInverseVInverseUV)).2.1) =
        monsterNortonLine01ShortSeventhUVector := by
  rw [monsterNortonLine01ShortSeventhExpansion_actual, monsterNortonLine01ShortSeventhExpansion,
    map_smul, map_sum]
  simp only [map_sum, map_smul]
  simp_rw [supported_sign_sum, monsterNortonLine01ShortSeventhU_basis]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
