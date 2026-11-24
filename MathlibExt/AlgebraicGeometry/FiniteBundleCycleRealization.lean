/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralMotivicBundleFrameMaps
public import MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels

/-!
# Actual finite bundle-cycle realization through a complement frame

For a finite relative cycle Z on E, the support over L is the original
scheme pullback Z times_X L. Its two module sections are the actual Z
vector and L vector. Their native direct-sum section is evaluated through
the whole frame E plus L isomorphic to free O^n. The resulting finite
cycle on L times A^n has its original support-image multiplicities.

All coefficient classes are native sums of the original quotient-cycle
classes. The map from Thom(L) is native cofiber descent of that same
coefficient section, before any Thom-isomorphism theorem is invoked.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.1 and Lemma 5.2.
The cycle/image providers and complement-null proof remain explicit sourced
construction outputs. Nilpotents are retained by the original scheme maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteBundleCycleRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry TopologicalSpace
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes MotivicBundleModels GeneralModuleTotalSpaces
open GeneralMotivicBundleFrameMaps PointedMotivicModels PointedMotivicQuotients
open MotivicAffineQuotientModels EffectiveMotivicComplexModels

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {P : SmoothProductSystem k} (A : StandardSchemes P)
  {X : SmoothScheme k} {M N : X.scheme.left.Modules} {d e n : ℕ}
  (G : BundleGeometry X M d) (L : BundleGeometry X N e)
  (S : BundleGeometry X (M ⊞ N) n)
  (φ : (M ⊞ N) ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin n))

/-- The original source-base projection of the finite relative support. -/
def relativeBase (z : G.RelativeGenerator) : z.val.presentation.scheme ⟶ X.scheme.left :=
  z.val.presentation.inclusion ≫ pullback.fst X.scheme.hom G.smoothTotal.scheme.hom

/-- The original vector coordinate of the same support. -/
def relativeVector (z : G.RelativeGenerator) :
    z.val.presentation.scheme ⟶ G.smoothTotal.scheme.left :=
  z.val.presentation.inclusion ≫ pullback.snd X.scheme.hom G.smoothTotal.scheme.hom

/-- The actual source cycle support over the complement bundle total space. -/
def cycleScheme (z : G.RelativeGenerator) : Scheme.{0} :=
  pullback (relativeBase G z) L.projection.left

/-- The common original base map of this actual scheme pullback. -/
def cycleBase (z : G.RelativeGenerator) : cycleScheme G L z ⟶ X.scheme.left :=
  pullback.fst (relativeBase G z) L.projection.left ≫ relativeBase G z

/-- Its E vector is the original support vector, through the original total-space dictionary. -/
def eVector (z : G.RelativeGenerator) : cycleScheme G L z ⟶ G.total.total :=
  pullback.fst (relativeBase G z) L.projection.left ≫ relativeVector G z ≫ G.totalIso.hom

/-- The E coordinate lies over the literal common base map. -/
theorem eVector_over (z : G.RelativeGenerator) :
    eVector G L z ≫ G.total.projection = cycleBase G L z := by
  have h := z.property
  change z.val.presentation.inclusion ≫
    pullback.snd X.scheme.hom G.smoothTotal.scheme.hom ≫ G.projection.left =
      z.val.presentation.inclusion ≫ pullback.fst X.scheme.hom G.smoothTotal.scheme.hom at h
  have hG : G.projection.left = G.totalIso.hom ≫ G.total.projection := rfl
  rw [hG] at h
  simpa only [eVector, cycleBase, relativeVector, relativeBase,
    Category.assoc]
    using congrArg (fun a ↦ pullback.fst (relativeBase G z) L.projection.left ≫ a) h

/-- Its L vector is the original second projection, retaining the same module section. -/
def lVector (z : G.RelativeGenerator) : cycleScheme G L z ⟶ L.total.total :=
  pullback.snd (relativeBase G z) L.projection.left ≫ L.totalIso.hom

/-- The L coordinate lies over the same actual scheme-pullback base. -/
theorem lVector_over (z : G.RelativeGenerator) :
    lVector G L z ≫ L.total.projection = cycleBase G L z := by
  change pullback.snd (relativeBase G z) L.projection.left ≫ L.projection.left = _
  exact (pullback.condition (f := relativeBase G z) (g := L.projection.left)).symm

/-- The actual E section on this original support scheme. -/
def eSection (z : G.RelativeGenerator) :
    Γ((Scheme.Modules.pullback (cycleBase G L z)).obj M, ⊤) :=
  pulledSection M G.total.projection G.total.universalSection
    (cycleBase G L z) (eVector G L z) (eVector_over G L z)

/-- The actual L section on that same support scheme. -/
def lSection (z : G.RelativeGenerator) :
    Γ((Scheme.Modules.pullback (cycleBase G L z)).obj N, ⊤) :=
  pulledSection N L.total.projection L.total.universalSection
    (cycleBase G L z) (lVector G L z) (lVector_over G L z)

/-- Native biproduct injections assemble the original two sections. -/
def sumSection (z : G.RelativeGenerator) :
    Γ((Scheme.Modules.pullback (cycleBase G L z)).obj (M ⊞ N), ⊤) :=
  ((((Scheme.Modules.pullback (cycleBase G L z)).map biprod.inl).val.app (op ⊤)).hom
    (eSection G L z)) +
  ((((Scheme.Modules.pullback (cycleBase G L z)).map biprod.inr).val.app (op ⊤)).hom
    (lSection G L z))

/-- The resulting vector in A^n is computed from the actual total-space lift and frame. -/
def affineVector (z : G.RelativeGenerator) : cycleScheme G L z ⟶ (A.affine n).scheme.left :=
  S.total.lift (cycleBase G L z) (sumSection G L z) ≫ S.totalIso.inv ≫
    (frameMap A S φ (nativeFrameOver A S φ)).left

/-- The actual image map retains the original L coordinate and the computed affine vector. -/
def cycleProjection (z : G.RelativeGenerator) :
    cycleScheme G L z ⟶ productScheme L.smoothTotal (A.affine n) :=
  pullback.lift (pullback.snd (relativeBase G z) L.projection.left)
    (affineVector A G L S φ z) (by
      rw [L.base_eq]
      simp only [affineVector, Category.assoc]
      rw [Over.w (frameMap A S φ (nativeFrameOver A S φ)), S.base_eq]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (S.total.lift (cycleBase G L z) (sumSection G L z)),
        S.total.lift_over (cycleBase G L z) (sumSection G L z)]
      have h := pullback.condition (f := relativeBase G z) (g := L.projection.left)
      have hL : L.projection.left = L.totalIso.hom ≫ L.total.projection := rfl
      have h' : pullback.snd (relativeBase G z) L.projection.left ≫
          (L.totalIso.hom ≫ L.total.projection) =
          pullback.fst (relativeBase G z) L.projection.left ≫ relativeBase G z :=
        (congrArg (fun f ↦ pullback.snd (relativeBase G z) L.projection.left ≫ f) hL).symm.trans
          h.symm
      simpa only [cycleBase, Category.assoc]
        using congrArg (fun f ↦ f ≫ X.scheme.hom) h')

/-- The geometry fixes every image support and original generic local-ring multiplicity. -/
structure CycleGeometry (z : G.RelativeGenerator) where
  noetherian : IsNoetherian (cycleScheme G L z)
  finite : IsFinite (cycleProjection A G L S φ z)
  finiteLength : ∀ w : irreducibleComponents (cycleScheme G L z),
    Module.length ((cycleScheme G L z).presheaf.stalk w.2.1.genericPoint)
      ((cycleScheme G L z).presheaf.stalk w.2.1.genericPoint) ≠ ⊤
  image : ∀ _w : irreducibleComponents (cycleScheme G L z),
    Generator L.smoothTotal (A.affine n)
  image_eq : ∀ w : irreducibleComponents (cycleScheme G L z),
    ((image w).support : Set (productScheme L.smoothTotal (A.affine n))) =
      closure {cycleProjection A G L S φ z w.2.1.genericPoint}

/-- The transformed cycle is the actual generic-image pushforward, including residue degrees. -/
def CycleGeometry.cycle {z : G.RelativeGenerator} (C : CycleGeometry A G L S φ z) :
    Cycles L.smoothTotal (A.affine n) := by
  letI := C.noetherian
  letI : Finite (irreducibleComponents (cycleScheme G L z)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI := Fintype.ofFinite (irreducibleComponents (cycleScheme G L z))
  exact ∑ w : irreducibleComponents (cycleScheme G L z),
    (((Module.length ((cycleScheme G L z).presheaf.stalk w.2.1.genericPoint)
      ((cycleScheme G L z).presheaf.stalk w.2.1.genericPoint)).toNat : ℤ) *
      ((cycleProjection A G L S φ z).residueDegree w.2.1.genericPoint : ℤ)) •
      generatorCycle (C.image w)

/-- Actual finite relative cycles with arbitrary coefficient-module values. -/
abbrev RelativeCoefficientCycles (V : ModuleCat.{1} ℤ) := G.RelativeGenerator →₀ V

variable {D₀ : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D₀ G₀] [CorrespondenceAdditivity D₀ G₀]
  {R : RepresentableSystem D₀ G₀}
  (T : NisTensorSystem k) (Q : PointedSimplicialModuleFunctor k)
  (H : ModuleSectionSystem Q)
  (C : ∀ z : G.RelativeGenerator, CycleGeometry A G L S φ z)

/-- Every coefficient is the native sum of the original affine quotient-cycle classes. -/
def coefficientClass (V : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G V) :
    (affineCoefficient (D := D₀) (G := G₀) (P := P) (A := A) (R := R) T n V).obj.obj
      (op L.smoothTotal) :=
  z.sum fun g v ↦ affineCoefficientClass (D := D₀) (G := G₀) (P := P)
    (A := A) (R := R) T n V L.smoothTotal (C g).cycle v

/-- The actual represented coefficient section, before taking the Thom quotient. -/
def coefficientMap (V : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G V) :
    representedPointed L.smoothTotal ⟶
      affineK (D := D₀) (G := G₀) (P := P) (A := A) (R := R) T Q n V :=
  H.sectionMap _ L.smoothTotal
    (coefficientClass (A := A) (G := G) (L := L) (S := S) (φ := φ) (T := T) (C := C) V z)

/-- Only the literal complement-null equation is a source proof output. -/
structure ComplementNull (V : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G V) : Prop where
  null : representedMap L.complementInclusion ≫
    coefficientMap (D₀ := D₀) (G₀ := G₀) (R := R) A G L S φ T Q H C V z =
    zeroMap (representedPointed L.complement)
      (affineK (D := D₀) (G := G₀) (P := P) (A := A) (R := R) T Q n V)

/-- Construction 5.1 is the native cofiber descent of the original finite-cycle section. -/
def realizationMap (V : ModuleCat.{1} ℤ) (z : RelativeCoefficientCycles G V)
    (h : ComplementNull (D₀ := D₀) (G₀ := G₀) (R := R) A G L S φ T Q H C V z) :
    L.thom ⟶ affineK (D := D₀) (G := G₀) (P := P) (A := A) (R := R) T Q n V :=
  cofiberDesc (representedMap L.complementInclusion)
    (coefficientMap (D₀ := D₀) (G₀ := G₀) (R := R) A G L S φ T Q H C V z) h.null

end MathlibExt.AlgebraicGeometry.FiniteBundleCycleRealization
