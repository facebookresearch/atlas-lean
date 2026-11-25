/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import MathlibExt.Algebra.Homology.ZeroDifferentialHomology
import MathlibExt.Algebra.Homology.ChainComplex.HomZeroSource

/-!
# Concrete full-product zero-source comparison

Both complexes are constantly `ℚ` in the integer grading with zero differentials.
This is not a finite-support complex: the public Hom product has a coordinate for
every integer source degree. A physical cochain has distinct entries `2`, `3`, `5`
at degrees `-1`, `0`, `1`; all these entries survive in the target homology.

At cohomological degree two the canonical comparison negates those entries:
`triangularSign 2 = -1`, whereas ordinary parity at degree two is `+1`.
The projective-source isomorphism is exercised on the resulting nonzero class.
The differential's separate `m.negOnePow` convention is not tested by this
zero-target-differential fixture. Projectivity instantiates the sufficient
comparison-isomorphism API; this fixture does not test its necessity or a
nontrivial cycle restriction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ChainComplex

namespace HomZeroSourceFocusedClients

private abbrev V : ModuleCat ℚ := ModuleCat.of ℚ ℚ

private abbrev P : ChainComplex (ModuleCat ℚ) ℤ where
  X _ := V
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private abbrev Q : CochainComplex (ModuleCat ℚ) ℤ where
  X _ := V
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

private lemma source_zero : ∀ i j : ℤ, P.d i j = 0 := fun _ _ => rfl
private lemma target_zero : ∀ i j : ℤ, Q.d i j = 0 := fun _ _ => rfl

private lemma source_projective : ∀ p : ℤ, Projective (P.X p) := fun _ => inferInstance

private abbrev scalar (a : ℚ) : V ⟶ V := ModuleCat.ofHom (a • LinearMap.id)

private abbrev weight (p : ℤ) : ℚ :=
  if p = -1 then 2 else if p = 0 then 3 else if p = 1 then 5 else 0

private abbrev physicalFamily (n : ℤ) : ∀ p : ℤ, P.X p ⟶ Q.X (n - p) :=
  fun p => scalar (weight p)

private abbrev cochain (n : ℤ) :=
  (homCochainPhysicalPiEquiv P Q n).symm (physicalFamily n)

private lemma component_value (n p : ℤ) :
    homCochainComponent P Q n (cochain n) p = scalar (weight p) := by
  change (homCochainPhysicalPiEquiv P Q n
    ((homCochainPhysicalPiEquiv P Q n).symm (physicalFamily n))) p = physicalFamily n p
  exact congrFun ((homCochainPhysicalPiEquiv P Q n).apply_symm_apply (physicalFamily n)) p

example : (homCochainComponent P Q 2 (cochain 2) (-1)).hom (1 : ℚ) = 2 := by
  rw [component_value]
  norm_num

example : (homCochainComponent P Q 2 (cochain 2) 0).hom (1 : ℚ) = 3 := by
  rw [component_value]
  norm_num

example : (homCochainComponent P Q 2 (cochain 2) 1).hom (1 : ℚ) = 5 := by
  rw [component_value]
  norm_num

example : (homCochainComponent P Q 2 (cochain 2) 2).hom (1 : ℚ) = 0 := by
  rw [component_value]
  norm_num

-- The reindexed coordinate r = 1 is physical degree -1, not physical degree +1.
example : ((homCochainPiEquiv P Q 2 (cochain 2)) 1).hom (1 : ℚ) = 2 := by
  change ((cochain 2).v 1 3 rfl).hom (1 : ℚ) = 2
  rw [homCochainPhysicalPiEquiv_symm_v]
  change (2 : ℚ) * 1 = 2
  norm_num

example : ((homCochainPiEquiv P Q 2 (cochain 2)) (-1)).hom (1 : ℚ) = 5 := by
  change ((cochain 2).v (-1) 1 rfl).hom (1 : ℚ) = 5
  rw [homCochainPhysicalPiEquiv_symm_v]
  change (5 : ℚ) * 1 = 5
  norm_num

private abbrev H := homCochainComplex P Q

private lemma hom_zero : ∀ i j : ℤ, H.d i j = 0 := by
  intro i j
  by_cases hij : i + 1 = j
  · apply AddCommGrpCat.ext
    intro z
    apply (homCochainPhysicalPiEquiv P Q j).injective
    funext p
    change homCochainComponent P Q j (((H.d i j).hom) z) p =
      homCochainComponent P Q j 0 p
    have hc := homCochainComponent_d P Q source_zero i j hij z p
    exact hc.trans (by rw [target_zero, comp_zero, smul_zero, homCochainComponent_zero])
  · exact H.shape i j hij

private abbrev cycleLift (n : ℤ) : H.X n ⟶ H.cycles n :=
  H.liftCycles (i := n) (𝟙 _) (n + 1)
    ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk n (n + 1) rfl))
    (by rw [Category.id_comp]; exact hom_zero _ _)

private lemma cycleLift_i (n : ℤ) : cycleLift n ≫ H.iCycles n = 𝟙 (H.X n) :=
  H.liftCycles_i _ _ _ _

private abbrev cycle (n : ℤ) : H.cycles n := (cycleLift n).hom (cochain n)

private lemma cycle_value (n : ℤ) : (H.iCycles n).hom (cycle n) = cochain n := by
  have h := ConcreteCategory.congr_hom (cycleLift_i n) (cochain n)
  change (H.iCycles n).hom ((cycleLift n).hom (cochain n)) = cochain n at h
  exact h

private abbrev targetCycleLift (k : ℤ) : Q.X k ⟶ Q.cycles k :=
  Q.liftCycles (i := k) (𝟙 _) (k + 1)
    ((ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk k (k + 1) rfl))
    (by exact Category.id_comp _)

private lemma targetCycleLift_i (k : ℤ) : targetCycleLift k ≫ Q.iCycles k = 𝟙 V :=
  Q.liftCycles_i _ _ _ _

private abbrev targetClass (k : ℤ) : V ⟶ Q.homology k :=
  targetCycleLift k ≫ Q.homologyπ k

private abbrev targetIso (k : ℤ) : Q.homology k ≅ V :=
  HomologicalComplex.zeroDifferentialHomologyIso Q k target_zero

private lemma targetClass_iso (k : ℤ) : targetClass k ≫ (targetIso k).hom = 𝟙 V := by
  exact HomologicalComplex.zeroDifferentialClassMap_homologyIso Q k target_zero

private lemma cycle_component (n p : ℤ) :
    homZeroSourceCycleComponent P Q n source_zero (cycle n) p =
      scalar (weight p) ≫ targetCycleLift (n - p) := by
  apply (cancel_mono (Q.iCycles (n - p))).1
  rw [homZeroSourceCycleComponent_i, cycle_value, component_value,
    Category.assoc, targetCycleLift_i, Category.comp_id]

private abbrev classOf (n : ℤ) : H.homology n := (H.homologyπ n).hom (cycle n)

private abbrev comparison (n : ℤ) := homZeroSourceCohomologyComparison P Q n source_zero

private abbrev decoded (n p : ℤ) : V ⟶ V :=
  (comparison n).hom (classOf n) p ≫ (targetIso (n - p)).hom

private lemma decoded_formula (n p : ℤ) :
    decoded n p = Int.triangularSign n • scalar (weight p) := by
  change (homZeroSourceCohomologyComparison P Q n source_zero
    ((homCochainComplex P Q).homologyπ n (cycle n)) p) ≫
      (targetIso (n - p)).hom = _
  rw [homZeroSourceCohomologyComparison_apply, Linear.units_smul_comp, cycle_component]
  have h : ((scalar (weight p) ≫ targetCycleLift (n - p)) ≫ Q.homologyπ (n - p)) ≫
      (targetIso (n - p)).hom = scalar (weight p) := by
    change (scalar (weight p) ≫ targetClass (n - p)) ≫ (targetIso (n - p)).hom = _
    rw [Category.assoc, targetClass_iso, Category.comp_id]
  exact congrArg (fun f : V ⟶ V => Int.triangularSign n • f) h

private lemma triangular_two : Int.triangularSign 2 = -1 := by decide

example : Int.triangularSign 2 ≠ (2 : ℤ).negOnePow := by decide

private lemma decoded_two (p : ℤ) : decoded 2 p = -(scalar (weight p)) := by
  rw [decoded_formula, triangular_two, Units.neg_smul, one_smul]

private lemma decoded_neg_one_value : (decoded 2 (-1)).hom (1 : ℚ) = -2 := by
  rw [decoded_two]
  norm_num

private lemma decoded_zero_value : (decoded 2 0).hom (1 : ℚ) = -3 := by
  rw [decoded_two]
  norm_num

private lemma decoded_one_value : (decoded 2 1).hom (1 : ℚ) = -5 := by
  rw [decoded_two]
  norm_num

example : [(decoded 2 (-1)).hom (1 : ℚ), (decoded 2 0).hom (1 : ℚ),
    (decoded 2 1).hom (1 : ℚ)] = [-2, -3, -5] := by
  rw [decoded_neg_one_value, decoded_zero_value, decoded_one_value]

example : (decoded 2 0).hom (1 : ℚ) ≠ 3 := by
  rw [decoded_zero_value]
  norm_num

example : (decoded 2 (-1)).hom (1 : ℚ) ≠ (decoded 2 1).hom (1 : ℚ) := by
  rw [decoded_neg_one_value, decoded_one_value]
  norm_num

private abbrev comparisonIso := homZeroSourceCohomologyIso P Q 2 source_zero source_projective

example : comparisonIso.hom = comparison 2 :=
  homZeroSourceCohomologyIso_hom P Q 2 source_zero source_projective

example : IsIso (comparison 2) :=
  isIso_homZeroSourceCohomologyComparison P Q 2 source_zero source_projective

private lemma iso_image_ne_zero : comparisonIso.hom.hom (classOf 2) ≠ 0 := by
  intro h
  have heq : comparisonIso.hom = comparison 2 :=
    homZeroSourceCohomologyIso_hom P Q 2 source_zero source_projective
  have hc : (comparison 2).hom (classOf 2) = 0 :=
    (congrArg (fun f : H.homology 2 ⟶
      AddCommGrpCat.of (∀ p : ℤ, P.X p ⟶ Q.homology (2 - p)) =>
        f.hom (classOf 2)) heq).symm.trans h
  have hp : (comparison 2).hom (classOf 2) 0 = 0 := congrFun hc 0
  have hdecoded : decoded 2 0 = 0 := by
    change (comparison 2).hom (classOf 2) 0 ≫ (targetIso 2).hom = 0
    exact (congrArg (fun f : V ⟶ Q.homology 2 => f ≫ (targetIso 2).hom) hp).trans
      (zero_comp (f := (targetIso 2).hom))
  have hvalue := congrArg (fun f : V ⟶ V => f.hom (1 : ℚ)) hdecoded
  change (decoded 2 0).hom (1 : ℚ) = 0 at hvalue
  rw [decoded_zero_value] at hvalue
  norm_num at hvalue

private lemma class_ne_zero : classOf 2 ≠ 0 := by
  intro h
  apply iso_image_ne_zero
  rw [h, map_zero]

private lemma round_trip : comparisonIso.inv.hom (comparisonIso.hom.hom (classOf 2)) =
    classOf 2 := by
  change (comparisonIso.hom ≫ comparisonIso.inv).hom (classOf 2) = classOf 2
  rw [Iso.hom_inv_id]
  rfl

example : comparisonIso.inv.hom (comparisonIso.hom.hom (classOf 2)) ≠ 0 := by
  rw [round_trip]
  exact class_ne_zero

end HomZeroSourceFocusedClients
