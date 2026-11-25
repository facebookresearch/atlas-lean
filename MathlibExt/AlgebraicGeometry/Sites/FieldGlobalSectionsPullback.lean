/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.FieldInverseImageStalks
public import MathlibExt.AlgebraicGeometry.Sites.FieldGlobalSectionsInvariants
public import MathlibExt.AlgebraicGeometry.Sites.FieldContinuousCohomologyDerivedInvariants
public import MathlibExt.CategoryTheory.NatIso.ComparisonCoherence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Literal original terminal-section pullback and invariant normalization
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

variable (k Ω K Ψ : Type u) [Field k] [Field Ω] [Field K] [Field Ψ]
variable [Algebra k Ω] [Algebra K Ψ] [IsSepClosure k Ω] [IsSepClosure K Ψ]
attribute [local instance] IsSepClosure.sep_closed

/-- The actual original terminal object remains terminal under actual base change. -/
def fieldBaseChangeTerminalIso (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj (fieldIdentityEtale k) ≅
      fieldIdentityEtale K := by
  letI := smallEtaleBaseChange_preservesFiniteLimits (fieldOriginalPullback k Ω K Ψ e)
  exact ((identityEtaleIsTerminal (Spec (.of k))).isTerminalObj
    (smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)) (fieldIdentityEtale k)).uniqueUpToIso
      (identityEtaleIsTerminal (Spec (.of K)))

/-- Original global sections pull back through the actual adjunction unit,
then restrict along the actual terminal-object comparison. -/
def fieldPullbackGlobalSections (e : GaloisUnits.FieldMap k Ω K Ψ) :
    Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⟶
      smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
        Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w} := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let L := smallEtaleInverseImage.{u, w} f
  let EY := (sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op (fieldIdentityEtale k))
  let EB := (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op ((smallEtaleBaseChange f).obj (fieldIdentityEtale k)))
  let EX := (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).obj
    (op (fieldIdentityEtale K))
  let η : EY ⟶ L ⋙ EB :=
    Functor.whiskerRight (smallEtaleInverseImageAdjunction.{u, w} f).unit EY
  let r : EB ⟶ EX :=
    (sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max u w}).map
      (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op
  exact (fieldGammaSectionsIso.{u, w} k).hom ≫ η ≫
    Functor.whiskerLeft L r ≫ Functor.whiskerLeft L (fieldGammaSectionsIso.{u, w} K).inv

omit [IsSepClosure k Ω] [IsSepClosure K Ψ] in
set_option backward.isDefEq.respectTransparency false in
-- V2/V3 implicit simplification could not see the same terminal-evaluation aliases.
theorem fieldPullbackGlobalSections_terminal_section
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q ≫
        (fieldGammaSectionsIso.{u, w} K).hom.app
          ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q) =
      (fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
        ((smallEtaleInverseImageAdjunction.{u, w}
          (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
        (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
          (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op) := by
  change ((fieldGammaSectionsIso.{u, w} k).hom.app Q ≫
      ((smallEtaleInverseImageAdjunction.{u, w}
        (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)) ≫
      (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
        (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op) ≫
      (fieldGammaSectionsIso.{u, w} K).inv.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)) ≫ _ = _
  exact CategoryTheory.comp_three_iso_inv_hom
    ((fieldGammaSectionsIso.{u, w} k).hom.app Q)
    (((smallEtaleInverseImageAdjunction.{u, w}
      (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op (fieldIdentityEtale k)))
    (((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj.map
      (fieldBaseChangeTerminalIso k Ω K Ψ e).inv.op)
    ((fieldGammaSectionsIso.{u, w} K).app
      ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q))


/-- The inverse terminal comparison carries the SAME original terminal point
to the actual original base-change point. -/
theorem fieldBaseChangeTerminalPoint (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (fieldGeometricPoint K Ψ).fiber.map (fieldBaseChangeTerminalIso k Ω K Ψ e).inv
        (fieldTerminalFiberPoint K Ψ) =
      fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω) := by
  let F := (fieldGeometricPoint K Ψ).fiber
  let i := fieldBaseChangeTerminalIso k Ω K Ψ e
  let t := fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k) (fieldTerminalFiberPoint k Ω)
  have ht : F.map i.hom t = fieldTerminalFiberPoint K Ψ := Subsingleton.elim _ _
  exact F.map_iso_inv_point i t (fieldTerminalFiberPoint K Ψ) ht

theorem fieldBaseChangeTerminalCommonPoint (e : GaloisUnits.FieldMap k Ω K Ψ) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).fiber.map
        (fieldBaseChangeTerminalIso k Ω K Ψ e).inv (ULift.up (fieldTerminalFiberPoint K Ψ)) =
      ULift.up (fieldChangeOriginalPoint k Ω K Ψ e (fieldIdentityEtale k)
        (fieldTerminalFiberPoint k Ω)) :=
  congrArg ULift.up (fieldBaseChangeTerminalPoint k Ω K Ψ e)

set_option backward.isDefEq.respectTransparency false in
-- V6 recorded a Trans-synthesis failure at the same sheaf/presheaf stalk aliases.
/-- The actual unit-defined section map has the same original invariant-value normalization. -/
theorem fieldPullbackGlobalSections_invariant_val (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    ((fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
          ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)).val =
      (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        (((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c).val) := by
  let f := fieldOriginalPullback k Ω K Ψ e
  let F := (smallEtaleInverseImage.{u, w} f).obj Q
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)
  let U := fieldIdentityEtale k
  let V := fieldIdentityEtale K
  let z := fieldTerminalFiberPoint k Ω
  let y := fieldTerminalFiberPoint K Ψ
  let t := fieldChangeOriginalPoint k Ω K Ψ e U z
  let i := fieldBaseChangeTerminalIso k Ω K Ψ e
  let a := (fieldGammaSectionsIso.{u, w} k).hom.app Q c
  let d := ((smallEtaleInverseImageAdjunction.{u, w} f).unit.app Q).hom.app (op U) a
  have hs := fieldGlobalSectionsInvariantsIso_germ.{u, w} k Ω Q c
  have ht := fieldGlobalSectionsInvariantsIso_germ.{u, w} K Ψ F
    ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)
  have hsec := ConcreteCategory.congr_hom
    (fieldPullbackGlobalSections_terminal_section.{u, w} k Ω K Ψ e Q) c
  have hw := Φ.toPresheafFiber_w_apply i.inv (ULift.up y) F.obj d
  have hp := fieldBaseChangeTerminalCommonPoint.{u, w} k Ω K Ψ e
  have hg := fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e Q U z a
  have h1 : Φ.toPresheafFiber V (ULift.up y) F.obj
      ((fieldGammaSectionsIso.{u, w} K).hom.app F
        ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c)) =
      Φ.toPresheafFiber V (ULift.up y) F.obj (F.obj.map i.inv.op d) :=
    congrArg (fun v => Φ.toPresheafFiber V (ULift.up y) F.obj v) hsec
  have h2 : Φ.toPresheafFiber V (ULift.up y) F.obj (F.obj.map i.inv.op d) =
      Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U)
        (Φ.fiber.map i.inv (ULift.up y)) F.obj d := hw
  have h3 : Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U)
      (Φ.fiber.map i.inv (ULift.up y)) F.obj d =
      Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U) (ULift.up t) F.obj d :=
    congrArg (fun p => Φ.toPresheafFiber ((smallEtaleBaseChange f).obj U) p F.obj d) hp
  have h4 := congrArg
    (fun v => (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q v) hs.symm
  exact ht.trans (h1.trans (h2.trans (h3.trans (hg.symm.trans h4))))

/-- The SAME Γ0 map is exactly original invariant restriction followed by the actual ξ. -/
theorem fieldPullbackGlobalSections_invariants (e : GaloisUnits.FieldMap k Ω K Ψ)
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (c : (Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}).obj Q) :
    (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom.app
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q)
          ((fieldPullbackGlobalSections.{u, w} k Ω K Ψ e).app Q c) =
      DiscreteAbelianAction.invariantsFunctor.map
        ((fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app Q)
        ((fieldInvariantRestriction.{u, u, w} k Ω K Ψ
          (GaloisUnits.FieldMap.restrictContinuous e)).app
            ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
              ((fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom.app Q c)) := by
  apply Subtype.ext
  exact fieldPullbackGlobalSections_invariant_val.{u, w} k Ω K Ψ e Q c


/-- The whole degree-zero natural transformation is normalized by the
existing invariant restriction and the SAME module comparison. -/
theorem fieldPullbackGlobalSections_invariants_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ) :
    fieldPullbackGlobalSections.{u, w} k Ω K Ψ e ≫
        Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e))
          (fieldGlobalSectionsInvariantsIso.{u, w} K Ψ).hom =
      (fieldGlobalSectionsInvariantsIso.{u, w} k Ω).hom ≫
        Functor.whiskerLeft (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
          (fieldInvariantRestriction.{u, u, w} k Ω K Ψ
            (GaloisUnits.FieldMap.restrictContinuous e)) ≫
        Functor.whiskerRight (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom
          (fieldInvariantFunctor.{u, w} K Ψ) := by
  apply NatTrans.ext
  funext Q
  ext c
  exact fieldPullbackGlobalSections_invariants.{u, w} k Ω K Ψ e Q c

/-- Every original coefficient section enters the comparison through ONE lift. -/
theorem fieldChange_original_coefficient_germ
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    let Q := (liftCoefficients.{u, w} (Spec (.of k))).obj F
    (fieldChangeUnderlyingStalkIso.{u, w} k Ω K Ψ e).hom.app Q
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          U (ULift.up z) Q.obj (ULift.up c)) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap K Ψ)).toPresheafFiber
        ((smallEtaleBaseChange (fieldOriginalPullback k Ω K Ψ e)).obj U)
        (ULift.up (fieldChangeOriginalPoint k Ω K Ψ e U z))
        ((smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e)).obj Q).obj
        (((smallEtaleInverseImageAdjunction.{u, w}
          (fieldOriginalPullback k Ω K Ψ e)).unit.app Q).hom.app (op U) (ULift.up c)) :=
  fieldChangeUnderlyingStalkIso_original_germ_apply.{u, w} k Ω K Ψ e
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F) U z (ULift.up c)

/-- Every original sheaf morphism is transported with its SAME one-lift components. -/
theorem fieldChange_original_coefficient_naturality
    (e : GaloisUnits.FieldMap k Ω K Ψ)
    {F F' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w}} (τ : F ⟶ F') :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        GaloisUnits.restrictModules (GaloisUnits.FieldMap.restrictContinuous e)).map
          ((liftCoefficients.{u, w} (Spec (.of k))).map τ) ≫
        (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F') =
      (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.app
          ((liftCoefficients.{u, w} (Spec (.of k))).obj F) ≫
        (smallEtaleInverseImage.{u, w} (fieldOriginalPullback k Ω K Ψ e) ⋙
          fieldGeometricStalkGaloisFunctor.{u, w} K Ψ).map
            ((liftCoefficients.{u, w} (Spec (.of k))).map τ) :=
  (fieldChangeStalkModuleIso.{u, w} k Ω K Ψ e).hom.naturality
    ((liftCoefficients.{u, w} (Spec (.of k))).map τ)

end AlgebraicGeometry.Scheme.DerivedSections

end
