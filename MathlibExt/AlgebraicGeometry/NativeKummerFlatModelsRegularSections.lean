/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Regular sections on the small étale site

Regular functions satisfy étale descent, so the specified native
regular-function sheafification unit is an isomorphism.

Source: Talpo--Vistoli, *Infinite root stacks and quasi-coherent sheaves on
logarithmic schemes*, arXiv:1410.1164v2, Definition6.10 and Remarks6.11--6.12;
Kato, *Logarithmic structures of Fontaine--Illusie*, Section1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

open _root_.CategoryTheory _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels

private theorem regularFunctionsSheaf : Presheaf.IsSheaf Scheme.etaleTopology
    (Scheme.Γ ⋙ liftRings.{0} ⋙ forget CommRingCat.{1}) := by
  have : Scheme.etaleTopology.Subcanonical := by
    apply GrothendieckTopology.Subcanonical.of_le (K := Scheme.fppfTopology)
    apply Precoverage.toGrothendieck_mono
    exact Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_of_nat_equiv
    (P₁ := yoneda.obj (Spec (.of (MvPolynomial PUnit (ULift ℤ)))))
    (fun {X} ↦ (AffineSpace.toSpecMvPolyIntEquiv PUnit).trans
      ((Equiv.funUnique PUnit Γ(X, ⊤)).trans Equiv.ulift.symm))
    (by intro Y Z f g; rfl)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

set_option backward.isDefEq.respectTransparency.types false in
private theorem rawRingSheaf (X : Scheme.{0}) :
    Presheaf.IsSheaf X.smallEtaleTopology (rawRing X) := by
  have : (Scheme.Etale.forget X).IsContinuous X.smallEtaleTopology
      (Scheme.etaleTopology.over X) := by
    have hle : Scheme.precoverage @Etale ≤ MorphismProperty.precoverage @Etale :=
      fun _ _ hR _ _ hf ↦ hR.2 hf
    have h := MorphismProperty.isContinuous_comap_forget
      (S := X) (Scheme.precoverage @Etale) hle
    rw [MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
      (Scheme.precoverage @Etale) hle] at h
    exact h
  apply (Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology
    (rawRing X) (forget CommRingCat.{1})).2
  exact (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
    X.smallEtaleTopology (Scheme.etaleTopology.over X) _
    ((Over.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.etaleTopology.over X) Scheme.etaleTopology _ regularFunctionsSheaf)

end MathlibExt.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

namespace WantedExt.AlgebraicGeometry.NativeKummerFlatModels

open _root_.CategoryTheory _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
open MathlibExt.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

/-- Ordinary regular-function descent for the specified native etale unit. -/
public theorem regularSections : RegularSectionComparisons
    := by
  constructor
  intro X U
  have := isIso_toSheafify X.smallEtaleTopology (rawRingSheaf X)
  change IsIso ((toSheafify X.smallEtaleTopology (rawRing X)).app (op U))
  infer_instance

end WantedExt.AlgebraicGeometry.NativeKummerFlatModels
