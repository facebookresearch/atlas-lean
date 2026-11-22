/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.RightShift
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK

/-!
# The original all-pair orthogonal Omega condition under right shifts

Every source/added-degree pair of the original orthogonal stabilization
family retains its whole native transpose. Under the genuine coend right
shift, that transpose is the original transpose at the shifted source,
followed by the actual three-block isometry on its target. This proves Omega
preservation for the complete original family, including arbitrary added
degree, arbitrary shift degree and the zero-degree cases.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory HomotopicalAlgebra
open CategoryTheory.Spectra CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega

/-- The actual continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on the orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The genuine continuous enriched structure on the orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original continuous block-exchange symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}

open RightShift

/-- The complete source I-space functor is restriction through the original delta. -/
abbrev bare (F : Carrier.{u, v}) : OrthogonalIndex ⥤ PointedCGWH.{u, v} :=
  ((OrthogonalSourceRightModule.restrictionFunctor.{u, v}).obj
    F).toEnrichedFunctor.toOrdinaryFunctor

/-- The source's unchanged actual native stabilization transpose at every degree pair. -/
abbrev omegaMap (F : Carrier.{u, v}) (n a : OrthogonalIndex) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
      (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).obj
        (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a))) :=
  CurrentFree.adjoint (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a))
    (PointedCGWH.orthogonalSphere.{u, v} a) (OrthogonalOperatorIndex.nu.{u, v} n a) F

/-- The actual full native stabilization action is the coefficient-first coend action. -/
theorem current_action_eq (F : Carrier.{u, v}) (n k a : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} (a + n) k) :
    CurrentFree.action (OrthogonalOperatorIndex.ofIndex.{u, v} n)
      (OrthogonalOperatorIndex.ofIndex.{u, v} k) (S.{u, v}.obj a)
      (Enriched.SphereOperator.coefficientHom d.{u, v} S.{u, v} n k a f) F =
      RightShift.action F n k a f := by
  let M := S.{u, v}.obj a
  let X := F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  let H := OrthogonalOperatorIndex.hom.{u, v} n k
  let p : M ⟶ H := Enriched.SphereOperator.coefficientHom d.{u, v} S.{u, v} n k a f
  let q := F.toEnrichedFunctor.map
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k)
  change (p ▷ X) ≫ (β_ X H).inv ≫ MonoidalClosed.uncurry q =
    (β_ M X).hom ≫ MonoidalClosed.uncurry (p ≫ q)
  rw [MonoidalClosed.uncurry_natural_left]
  have hb := braiding_inv_naturality_left p X
  have hs := SymmetricCategory.braiding_swap_eq_inv_braiding X M
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ MonoidalClosed.uncurry q)
      (hb.trans (congrArg (fun t => t ≫ (X ◁ p)) hs.symm))

/-- The entire original native nu inclusion retains its coefficient-first native block label. -/
theorem nu_eq_coefficientHom (n a : OrthogonalIndex) :
    OrthogonalOperatorIndex.nu.{u, v} n a =
      Enriched.SphereOperator.coefficientHom d.{u, v} S.{u, v} n (n + a) a (β_ a n).hom :=
  (OrthogonalSourceRightModule.rightSphereHom_eq_original_nu.{u, v} n a).symm

/-- The complete original Omega arrow is the actual coend coefficient-action transpose. -/
theorem omegaMap_eq_adjoint (F : Carrier.{u, v}) (n a : OrthogonalIndex) :
    omegaMap F n a = RightShift.adjoint F n (n + a) a (β_ a n).hom := by
  unfold omegaMap CurrentFree.adjoint RightShift.adjoint
  apply congrArg MonoidalClosed.curry
  have h := congrArg (fun p => CurrentFree.action (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a))
    (PointedCGWH.orthogonalSphere.{u, v} a) p F) (nu_eq_coefficientHom n a)
  exact h.trans (current_action_eq F n (n + a) a (β_ a n).hom)

/-- Uncurrying the original native Omega arrow retains the whole original right-sphere action. -/
theorem omegaMap_uncurry (F : Carrier.{u, v}) (n a : OrthogonalIndex) :
    MonoidalClosed.uncurry (omegaMap F n a) = RightShift.action F n (n + a) a (β_ a n).hom := by
  exact (congrArg MonoidalClosed.uncurry (omegaMap_eq_adjoint F n a)).trans
    (MonoidalClosed.uncurry_curry (RightShift.action F n (n + a) a (β_ a n).hom))

/-- Every source, shift and added degree keeps its original full transpose and block isometry. -/
theorem shift_adjoint (F : Carrier.{u, v}) (r n a : OrthogonalIndex) :
    omegaMap ((RightShift.shift r).obj F) n a =
      omegaMap F (n + r) a ≫ (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).map
        ((bare F).map (RightShift.blockSwap r n a).hom) := by
  let p := (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).map
    ((bare F).map (RightShift.blockSwap r n a).hom)
  have hs := omegaMap_eq_adjoint ((RightShift.shift r).obj F) n a
  have hg := RightShift.shift_adjoint F r n a
  have ho := congrArg (fun q => q ≫ p) (omegaMap_eq_adjoint F (n + r) a)
  exact hs.trans (hg.trans ho.symm)

/-- Genuine coend right shifts preserve the original entire all-pair Omega condition. -/
theorem shift_isOmega (r : OrthogonalIndex) (F : Carrier.{u, v}) (hF : Actual.OrthogonalIsOmega F) :
    Actual.OrthogonalIsOmega ((RightShift.shift r).obj F) := by
  intro label
  rcases label with ⟨n, a⟩
  let p := (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).map
    ((bare F).map (RightShift.blockSwap r n a).hom)
  let e := (ihom (PointedCGWH.orthogonalSphere.{u, v} a)).mapIso
    ((bare F).mapIso (RightShift.blockSwap r n a))
  have : IsIso p := by change IsIso e.hom; infer_instance
  have hp : weakEquivalences PointedCGWH.{u, v} p :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso p
  have ho : weakEquivalences PointedCGWH.{u, v} (omegaMap F (n + r) a) := hF (n + r, a)
  change weakEquivalences PointedCGWH.{u, v} (omegaMap ((RightShift.shift r).obj F) n a)
  rw [shift_adjoint]
  exact (weakEquivalences PointedCGWH.{u, v}).comp_mem (omegaMap F (n + r) a) p ho hp

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega
