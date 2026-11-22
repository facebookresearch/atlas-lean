/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.Stable.ShiftedTargets
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKPuppeHom

/-!
# Original suspension Hom comparisons at every integer target degree

The Hom comparison uses the original I-cone/scalar-sphere isomorphism,
the actual scalar Quillen adjunction, the original Q counit and the
integer target-loop comparison. Its two functions keep those same maps
in their original order. Both source and target naturalities are proved
for the complete functions, including their inverses.

These are the shift functions for the actual symmetric Puppe sequence.
The underlying carrier and the weak class are the original native level
carrier and Omega-target tests. MMSS, *Model categories of diagram
spectra*, December 30, 1999 manuscript, Theorem 8.12(vi), pages 27–28,
is the source of this shifted Hom sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom

private abbrev C := Actual.SymmetricCarrier.{u, v}

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev H := toHomotopyCategory C.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B)
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev ISusp := OriginalISuspension.suspension (B := B)
  (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
private abbrev scalarSusp := EnrichedFunctorCat.tensorLeft
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) PointedCGWH.sphereOne.{u, v}
private abbrev scalarLoop := cotensor (I := PointedCGWH.SymmetricOperatorIndex.{u, v})
  PointedCGWH.sphereOne.{u, v}
private abbrev adj := ScalarLeibniz.adjunction
  (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) PointedCGWH.sphereOne.{u, v}

private theorem originalSphereQuillen : adj.{u, v}.IsQuillenAdjunction := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  exact ScalarCompatibility.scalar_isQuillen (B := B) PointedCGWH.sphereOne

private theorem originalQCofibrant (X : C.{u, v}) : IsCofibrant (Q.obj X) :=
  Replacement.isCofibrant_cofibrantReplacement (B := B) X

private theorem shiftedTargetFibrant (q : ℤ) (E : C.{u, v}) :
    IsFibrant ((ShiftedTargets.target q).obj E) :=
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant _

attribute [local instance] originalSphereQuillen originalQCofibrant shiftedTargetFibrant

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

private instance nativeZero : HasZeroObject C.{u, v} := Diagrams.nativeHasZeroObject

/-- The full original Hom test in degree q, before requiring its target to be Omega. -/
abbrev test (q : ℤ) (X E : C.{u, v}) :=
  H.{u, v}.obj X ⟶ H.{u, v}.obj ((ShiftedTargets.target q).obj E)

/-- The genuine scalar adjunct acts on the same original Q source at every target degree. -/
def scalarHomEquiv (q : ℤ) (X E : C.{u, v}) :
    (H.{u, v}.obj (scalarSusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) ≃
    (H.{u, v}.obj (Q.obj X) ⟶
      H.{u, v}.obj (scalarLoop.obj ((ShiftedTargets.target q).obj E))) :=
  QuillenOrdinaryHoHom.homEquiv adj (Q.obj X) ((ShiftedTargets.target q).obj E)

/-- The full integer shift uses the original suspension comparison, Q counit and delta. -/
def suspensionHomEquiv (q : ℤ) (X E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    (H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) ≃ test (B := B) (q + 1) X E :=
  (Iso.homCongr (NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X)
      (Iso.refl _)).trans
    ((scalarHomEquiv (B := B) q X E).trans
      (Iso.homCongr (NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X)
        (ShiftedTargets.nextLoopIso (B := B) q E hE).symm))

/-- The forward integer-shift function keeps all four actual endpoint maps. -/
theorem suspensionHomEquiv_apply (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    suspensionHomEquiv (B := B) q X E hE g =
      (NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X).inv ≫
        scalarHomEquiv (B := B) q X E
          ((NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).inv ≫ g) ≫
          (ShiftedTargets.nextLoopIso (B := B) q E hE).inv := by
  simp only [suspensionHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id, Iso.symm_hom]

/-- The inverse integer-shift function keeps the same four maps and actual inverse adjunct. -/
theorem suspensionHomEquiv_symm_apply (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : test (B := B) (q + 1) X E) :
    (suspensionHomEquiv (B := B) q X E hE).symm g =
      (NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).hom ≫
        (scalarHomEquiv (B := B) q X E).symm
          ((NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X).hom ≫ g ≫
            (ShiftedTargets.nextLoopIso (B := B) q E hE).hom) := by
  simp only [suspensionHomEquiv, Equiv.symm_trans_apply, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.refl_inv, Category.comp_id, Iso.symm_hom, Iso.symm_inv]

/-- Degree minus one is the already constructed actual first-delooping Hom equivalence. -/
theorem suspensionHomEquiv_neg_one (X E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) :
    suspensionHomEquiv (B := B) (-1) X E hE =
      NativeOmegaRecovery.NativeSymmetricDelooping.negativeHomEquiv (B := B) X E hE := by
  simp only [suspensionHomEquiv, ShiftedTargets.nextLoopIso_neg_one_iso]
  rfl

/-- The full scalar adjunct retains every original same-Q source transformation. -/
theorem scalarHomEquiv_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X) (E : C.{u, v})
    (g : H.{u, v}.obj (scalarSusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    scalarHomEquiv (B := B) q X' E (H.{u, v}.map (scalarSusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map (Q.map f) ≫ scalarHomEquiv (B := B) q X E g :=
  QuillenOrdinaryHoHom.homEquiv_naturality_left adj
    ((ShiftedTargets.target q).obj E) (Q.map f) g

/-- The same original scalar adjunct retains every complete shifted target map. -/
theorem scalarHomEquiv_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}} (t : E ⟶ E')
    (g : H.{u, v}.obj (scalarSusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    scalarHomEquiv (B := B) q X E' (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      scalarHomEquiv (B := B) q X E g ≫
        H.{u, v}.map (scalarLoop.map ((ShiftedTargets.target q).map t)) :=
  QuillenOrdinaryHoHom.homEquiv_naturality_right adj (Q.obj X) g
    ((ShiftedTargets.target q).map t)

/-- Every original source arrow acts on the complete forward integer-shift Hom function. -/
theorem suspensionHomEquiv_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    suspensionHomEquiv (B := B) q X' E hE (H.{u, v}.map (ISusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map f ≫ suspensionHomEquiv (B := B) q X E hE g := by
  rw [suspensionHomEquiv_apply, suspensionHomEquiv_apply]
  have hS := NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso_inv_naturality
    (B := B) f
  have hQ := NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso_inv_naturality
    (B := B) f
  have hInput :
      (NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X').inv ≫
        (H.{u, v}.map (ISusp.map (Q.map f)) ≫ g) =
      H.{u, v}.map (scalarSusp.map (Q.map f)) ≫
        ((NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).inv ≫ g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ g) hS.symm).trans (Category.assoc _ _ _))
  rw [hInput, scalarHomEquiv_source]
  simpa only [Category.assoc] using congrArg
    (fun m => m ≫ scalarHomEquiv (B := B) q X E
      ((NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).inv ≫ g) ≫
        (ShiftedTargets.nextLoopIso (B := B) q E hE).inv) hQ.symm

/-- Every original Omega target map acts on the complete forward integer-shift function. -/
theorem suspensionHomEquiv_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    suspensionHomEquiv (B := B) q X E' hE'
        (g ≫ H.{u, v}.map ((ShiftedTargets.target q).map t)) =
      suspensionHomEquiv (B := B) q X E hE g ≫
        H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t) := by
  rw [suspensionHomEquiv_apply, suspensionHomEquiv_apply]
  rw [← Category.assoc
    (NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).inv g,
    scalarHomEquiv_target]
  have hNext := ShiftedTargets.nextLoopIso_inv_naturality (B := B) q hE hE' t
  simpa only [Category.assoc] using congrArg
    (fun m => (NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X).inv ≫
      scalarHomEquiv (B := B) q X E
        ((NativeOmegaRecovery.NativeSymmetricDelooping.suspensionHoIso (B := B) X).inv ≫ g) ≫ m)
    hNext

/-- The full inverse shift retains the same complete source naturality square. -/
theorem suspensionHomEquiv_symm_source (q : ℤ) {X X' : C.{u, v}} (f : X' ⟶ X)
    (E : C.{u, v}) (hE : Actual.SymmetricIsOmega E) (g : test (B := B) (q + 1) X E) :
    (suspensionHomEquiv (B := B) q X' E hE).symm (H.{u, v}.map f ≫ g) =
      H.{u, v}.map (ISusp.map (Q.map f)) ≫
        (suspensionHomEquiv (B := B) q X E hE).symm g := by
  apply (suspensionHomEquiv (B := B) q X' E hE).injective
  rw [Equiv.apply_symm_apply, suspensionHomEquiv_source, Equiv.apply_symm_apply]

/-- The full inverse shift retains every complete Omega target transformation. -/
theorem suspensionHomEquiv_symm_target (q : ℤ) (X : C.{u, v}) {E E' : C.{u, v}}
    (hE : Actual.SymmetricIsOmega E) (hE' : Actual.SymmetricIsOmega E') (t : E ⟶ E')
    (g : test (B := B) (q + 1) X E) :
    (suspensionHomEquiv (B := B) q X E' hE').symm
        (g ≫ H.{u, v}.map ((ShiftedTargets.target (q + 1)).map t)) =
      (suspensionHomEquiv (B := B) q X E hE).symm g ≫
        H.{u, v}.map ((ShiftedTargets.target q).map t) := by
  apply (suspensionHomEquiv (B := B) q X E' hE').injective
  rw [Equiv.apply_symm_apply,
    suspensionHomEquiv_target (B := B) q X hE hE' t, Equiv.apply_symm_apply]

/-- Every positive suspension Hom test recovers its whole original class after the inverse shift. -/
theorem suspensionHomEquiv_left_inverse (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E)
    (g : H.{u, v}.obj (ISusp.obj (Q.obj X)) ⟶
      H.{u, v}.obj ((ShiftedTargets.target q).obj E)) :
    (suspensionHomEquiv (B := B) q X E hE).symm
      (suspensionHomEquiv (B := B) q X E hE g) = g :=
  (suspensionHomEquiv (B := B) q X E hE).symm_apply_apply g

/-- Every original integer Hom class recovers the same class after the forward shift. -/
theorem suspensionHomEquiv_right_inverse (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) (g : test (B := B) (q + 1) X E) :
    suspensionHomEquiv (B := B) q X E hE
      ((suspensionHomEquiv (B := B) q X E hE).symm g) = g :=
  (suspensionHomEquiv (B := B) q X E hE).apply_symm_apply g

/-- Every complete original Ho source morphism preserves the actual chosen null class. -/
theorem nullHom_precomp {X Y Z : C.{u, v}}
    (g : H.{u, v}.obj X ⟶ H.{u, v}.obj Y) :
    g ≫ OrdinaryHoCofiberKernel.nullHom Y Z = OrdinaryHoCofiberKernel.nullHom X Z := by
  let e := NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization H.{u, v} (Q.obj X) Y (e.hom ≫ g)
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← hf, OrdinaryHoCofiberKernel.precomp_nullHom]
  change _ = (NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso (B := B) X).hom ≫ _
  rw [NativeOmegaRecovery.NativeSymmetricDelooping.epsilonHoIso_hom]
  exact (OrdinaryHoCofiberKernel.precomp_nullHom (C := C.{u, v}) (Z := Z)
    ((Replacement.cofibrantReplacementCounit (B := B)
      (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).app X)).symm

private theorem actualAdjunct_null (q : ℤ) (X E : C.{u, v}) :
    adj.homEquiv (Q.obj X) ((ShiftedTargets.target q).obj E)
        (OrdinaryHoCofiberKernel.nullMap (scalarSusp.obj (Q.obj X))
          ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullMap (Q.obj X)
        (scalarLoop.obj ((ShiftedTargets.target q).obj E)) := by
  let Z : C.{u, v} := Diagrams.zeroDiagram
  have hZ : IsZero Z := Diagrams.zeroDiagram_isZero
  have hNull : OrdinaryHoCofiberKernel.nullMap (scalarSusp.obj (Q.obj X))
      ((ShiftedTargets.target q).obj E) =
    Diagrams.toZero (scalarSusp.obj (Q.obj X)) ≫
      Diagrams.zeroTo ((ShiftedTargets.target q).obj E) := by
    rw [← OrdinaryHoChosenPuppe.actualNullMap_eq_chosen Z hZ]
    unfold OrdinaryHoChosenPuppe.nullMap
    have hFirst : OrdinaryHoChosenPuppe.toZero Z hZ (scalarSusp.obj (Q.obj X)) =
        Diagrams.toZero (scalarSusp.obj (Q.obj X)) := hZ.isTerminal.hom_ext _ _
    have hSecond : OrdinaryHoChosenPuppe.fromZero Z hZ ((ShiftedTargets.target q).obj E) =
        Diagrams.zeroTo ((ShiftedTargets.target q).obj E) := hZ.isInitial.hom_ext _ _
    rw [hFirst, hSecond]
  rw [hNull, adj.homEquiv_naturality_right]
  let RZ := scalarLoop.obj Z
  have hRZ : IsZero RZ := NativeK.cotensorZero_isZero PointedCGWH.sphereOne
  have hFirst : adj.homEquiv (Q.obj X) Z (Diagrams.toZero (scalarSusp.obj (Q.obj X))) =
      hRZ.isTerminal.from (Q.obj X) := hRZ.isTerminal.hom_ext _ _
  have hSecond : scalarLoop.map (Diagrams.zeroTo ((ShiftedTargets.target q).obj E)) =
      hRZ.isInitial.to (scalarLoop.obj ((ShiftedTargets.target q).obj E)) :=
    hRZ.isInitial.hom_ext _ _
  rw [hFirst, hSecond]
  exact OrdinaryHoChosenPuppe.actualNullMap_eq_chosen RZ hRZ (Q.obj X)
    (scalarLoop.obj ((ShiftedTargets.target q).obj E))

/-- The full actual scalar Hom function preserves the original null class in every integer. -/
theorem scalarHomEquiv_null (q : ℤ) (X E : C.{u, v}) :
    scalarHomEquiv (B := B) q X E
        (OrdinaryHoCofiberKernel.nullHom (scalarSusp.obj (Q.obj X))
          ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (Q.obj X)
        (scalarLoop.obj ((ShiftedTargets.target q).obj E)) := by
  unfold scalarHomEquiv OrdinaryHoCofiberKernel.nullHom
  rw [QuillenOrdinaryHoHom.homEquiv_map]
  exact H.{u, v}.congr_map (actualAdjunct_null (B := B) q X E)

/-- The whole suspension shift preserves the same original null class in every integer. -/
theorem suspensionHomEquiv_null (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    suspensionHomEquiv (B := B) q X E hE
        (OrdinaryHoCofiberKernel.nullHom (ISusp.obj (Q.obj X))
          ((ShiftedTargets.target q).obj E)) =
      OrdinaryHoCofiberKernel.nullHom X ((ShiftedTargets.target (q + 1)).obj E) := by
  rw [suspensionHomEquiv_apply, nullHom_precomp, scalarHomEquiv_null]
  rw [← Category.assoc, nullHom_precomp, OrdinaryHoCofiberKernel.nullHom_postcomp]

/-- The inverse whole shift recovers the actual original null class at the suspended source. -/
theorem suspensionHomEquiv_symm_null (q : ℤ) (X E : C.{u, v})
    (hE : Actual.SymmetricIsOmega E) :
    (suspensionHomEquiv (B := B) q X E hE).symm
        (OrdinaryHoCofiberKernel.nullHom X ((ShiftedTargets.target (q + 1)).obj E)) =
      OrdinaryHoCofiberKernel.nullHom (ISusp.obj (Q.obj X))
        ((ShiftedTargets.target q).obj E) := by
  apply (suspensionHomEquiv (B := B) q X E hE).injective
  rw [Equiv.apply_symm_apply, suspensionHomEquiv_null]

end PointedCGWH.Spectra.Symmetric.Stable.ShiftedHom
