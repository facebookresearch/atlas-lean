/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicUnitRootClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The actual universal permutation quotient and its Thom diagram

Each finite stage has the original associated permutation module, the
diagonal invariant line fixed in its torsor frame, and the native cokernel
bundle. Transition modules retain the original frame and cokernel squares.
Their total/complement/Thom maps are the native maps of those same modules.
The global zero map is formed from the original zero sections and colimits.

Source: Voevodsky, arXiv:math/0107109v1, Theorems 6.14 and 6.16.
The integral class d is a zero pullback of this quotient-bundle Thom
class; the mod-ell reduction and based integral-boundary lift c are later
operations, not independent geometric class inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPrimeClassGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicGeometricClassifyingSpaces MotivicBundleModels
open GeneralMotivicBundleFrameMaps PointedMotivicModels PointedMotivicQuotients

variable {k : Type} [Field k] {ell : ℕ}
  [C : ConstantGroupGeometry (k := k) (H := Equiv.Perm (Fin ell))]

/-- The actual tautological permutation representation of S_ell. -/
def standardPermutation : Equiv.Perm (Fin ell) →* Equiv.Perm (Fin ell) := MonoidHom.id _

/-- The invariant line uses the actual source sheaf unit and all original coordinates. -/
structure DiagonalLine {U : FreeQuotient (k := k) (H := Equiv.Perm (Fin ell))}
    (E : AssociatedPermutationModule U (standardPermutation (ell := ell))) where
  inclusion : SheafOfModules.unit U.base.scheme.left.ringCatSheaf ⟶ E.module
  [mono : Mono inclusion]
  normalization : (Scheme.Modules.pullback U.projection.left).map inclusion ≫ E.frame.hom =
    (AlgebraicBundleGeometry.pullbackUnit U.total.scheme.left U.base.scheme.left
      U.projection.left).hom ≫
        ∑ j : Fin ell, SheafOfModules.ιFree (R := U.total.scheme.left.ringCatSheaf) j

attribute [instance] DiagonalLine.mono

/-- The original quotient is the actual cokernel of O -> xi_ell. -/
structure PrimeBundleStage (U : FreeQuotient (k := k) (H := Equiv.Perm (Fin ell))) where
  permutation : AssociatedPermutationModule U (standardPermutation (ell := ell))
  line : DiagonalLine permutation
  quotient : BundleGeometry U.base (cokernel line.inclusion) (ell - 1)

/-- Pull an original permutation-module map through the actual base/total arrow. -/
def transportedSection {U V : FreeQuotient (k := k) (H := Equiv.Perm (Fin ell))}
    (a : FreeQuotientArrow U V) (E : AssociatedPermutationModule U (standardPermutation (ell := ell)))
    (F : AssociatedPermutationModule V (standardPermutation (ell := ell)))
    (f : E.module ⟶ (Scheme.Modules.pullback a.base.left).obj F.module)
    (T : Over (Spec (.of k))) (u : T ⟶ U.total.scheme)
    (s : Γ((Scheme.Modules.pullback (u ≫ U.projection).left).obj E.module, ⊤)) :
    Γ((Scheme.Modules.pullback (u ≫ a.total ≫ V.projection).left).obj F.module, ⊤) := by
  let h : (u ≫ a.total ≫ V.projection).left = (u ≫ U.projection ≫ a.base).left := by
    have ha : a.total.left ≫ V.projection.left = U.projection.left ≫ a.base.left :=
      congrArg Over.Hom.left a.projection
    change (u.left ≫ a.total.left) ≫ V.projection.left =
      (u.left ≫ U.projection.left) ≫ a.base.left
    simp only [Category.assoc]
    rw [ha]
  let transport := (Scheme.Modules.pullbackCongr h.symm).hom.app F.module
  let sectionMap := (Scheme.Modules.pullback (u ≫ U.projection).left).map f ≫
    (Scheme.Modules.pullbackComp (u ≫ U.projection).left a.base.left).hom.app F.module ≫
      transport
  exact ((sectionMap.val.app (op ⊤)).hom s)

/-- Every transition frame is normalized on all actual pulled sections and coordinates. -/
def IsFrameArrow {U V : FreeQuotient (k := k) (H := Equiv.Perm (Fin ell))}
    (a : FreeQuotientArrow U V) (E : AssociatedPermutationModule U (standardPermutation (ell := ell)))
    (F : AssociatedPermutationModule V (standardPermutation (ell := ell)))
    (f : E.module ⟶ (Scheme.Modules.pullback a.base.left).obj F.module) : Prop :=
  ∀ (T : Over (Spec (.of k))) (u : T ⟶ U.total.scheme) (j : Fin ell)
    (s : Γ((Scheme.Modules.pullback (u ≫ U.projection).left).obj E.module, ⊤)),
    F.toPermutationFrame.coordinate T (u ≫ a.total) j (transportedSection a E F f T u s) =
      E.toPermutationFrame.coordinate T u j s

/-- The entire prime quotient-bundle diagram retains the original permutation/line/cokernel arrows. -/
structure PrimeThomDiagram (A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))) where
  stage : ∀ m : ℕ, PrimeBundleStage (A.step m).quotient
  permutationMap : ∀ m : ℕ, (stage m).permutation.module ⟶
    (Scheme.Modules.pullback (A.transition m).base.left).obj (stage (m + 1)).permutation.module
  permutationNormalization : ∀ m : ℕ,
    IsFrameArrow (A.transition m) (stage m).permutation (stage (m + 1)).permutation (permutationMap m)
  lineSquare : ∀ m : ℕ, (stage m).line.inclusion ≫ permutationMap m =
    (AlgebraicBundleGeometry.pullbackUnit (A.step m).quotient.base.scheme.left
      (A.step (m + 1)).quotient.base.scheme.left (A.transition m).base.left).inv ≫
        (Scheme.Modules.pullback (A.transition m).base.left).map (stage (m + 1)).line.inclusion
  quotientMap : ∀ m : ℕ, cokernel (stage m).line.inclusion ⟶
    (Scheme.Modules.pullback (A.transition m).base.left).obj (cokernel (stage (m + 1)).line.inclusion)
  quotientSquare : ∀ m : ℕ, cokernel.π (stage m).line.inclusion ≫ quotientMap m =
    permutationMap m ≫
      (Scheme.Modules.pullback (A.transition m).base.left).map (cokernel.π (stage (m + 1)).line.inclusion)
  complement : ∀ m : ℕ, ComplementMap (stage m).quotient (stage (m + 1)).quotient
    (A.transition m).base (quotientMap m)
  zeroNaturality : ∀ m : ℕ,
    representedMap (A.transition m).base ≫ (stage (m + 1)).quotient.zeroThom =
      (stage m).quotient.zeroThom ≫
        thomMap (stage m).quotient (stage (m + 1)).quotient (A.transition m).base
          (quotientMap m) (complement m)

/-- The Thom sequence is computed from those actual module and complement maps. -/
def primeThomSequence {A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
    (E : PrimeThomDiagram A) : ℕ ⥤ PointedSpaces (k := k) :=
  Functor.ofSequence (X := fun m => (E.stage m).quotient.thom) (fun m =>
    thomMap (E.stage m).quotient (E.stage (m + 1)).quotient (A.transition m).base
      (E.quotientMap m) (E.complement m))

/-- The global Thom object is the native colimit of the original quotient bundles. -/
def primeGlobalThom {A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
    (E : PrimeThomDiagram A) : PointedSpaces (k := k) := colimit (primeThomSequence E)

/-- The actual finite quotient Thom class enters through its native cocone. -/
def primeThomStageMap {A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
    (E : PrimeThomDiagram A) (m : ℕ) :
    (E.stage m).quotient.thom ⟶ primeGlobalThom E :=
  colimit.ι (primeThomSequence E) m

/-- Every original zero section is retained in the whole natural source diagram. -/
def primeZeroTransformation {A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
    (E : PrimeThomDiagram A) : pointedSequence A ⟶ primeThomSequence E :=
  NatTrans.ofSequence (fun m => (E.stage m).quotient.zeroThom) (by
    intro m
    simpa only [pointedSequence, primeThomSequence, Functor.ofSequence_map_homOfLE_succ]
      using E.zeroNaturality m)

/-- The global zero pullback is a map of the actual native colimit diagrams. -/
def primeGlobalZero {A : GeometricApproximation (k := k) (H := Equiv.Perm (Fin ell))}
    (E : PrimeThomDiagram A) : geometricClassifyingSpace A ⟶ primeGlobalThom E :=
  colim.map (primeZeroTransformation E)

end MathlibExt.AlgebraicGeometry.MotivicPrimeClassGeometry
