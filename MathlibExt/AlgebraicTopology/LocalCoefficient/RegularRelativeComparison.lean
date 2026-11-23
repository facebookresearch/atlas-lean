/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.RegularModuleBasis
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Relative regular coefficients and the literal pulled-back native cover

The established regular coefficient chain comparisons commute with the
original base-map chain morphism. For monic base maps, taking their actual
cokernels identifies relative regular chains with the relative chains of the literal pulled cover.
The quotient maps, their inverses and homology projections use those same maps.

These project-derived comparisons support the project's covering-model
proof of the cell construction requested in Weibel, The K-book, Exercise
IV.1.4 (printed p. 273). They reuse the existing regular-path chain square
and categorical cokernel APIs.

This comparison does not identify a family of relative cells with a free
module, or establish acyclicity of a homotopy fiber.
-/

noncomputable section

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

/-- The actual cokernel of the regular coefficient chain map of `f`. -/
noncomputable def originalRegularRelativeChainComplex {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)))

/-- The quotient to relative regular chains for the same original base map. -/
noncomputable def originalRegularRelativeChainProjection {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    localCoefficientChainComplex
        (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)) ⟶
      originalRegularRelativeChainComplex f y :=
  cokernel.π (localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y)))

/-- The literal native covering pullback is a pair when the original map is monic. -/
@[expose]
noncomputable def originalRegularPulledCoverPair {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) : SSetPair.{u} := by
  letI : Mono (TopCat.toSSet.map f) := inferInstance
  exact SSetPair.of (pullback.snd (TopCat.toSSet.map f)
    (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
      (TopCat.toSSetObj₀Equiv.symm y)))

/-- The pair inclusion is the second projection of the actual covering pullback. -/
theorem originalRegularPulledCoverPair_hom {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    (originalRegularPulledCoverPair f y).hom =
      pullback.snd (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm y)) := by
  rfl

private noncomputable def regularRelativeArrowIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    Arrow.mk (localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))) ≅
        Arrow.mk (SSet.chainComplexMap (originalRegularPulledCoverPair f y).hom
          (ModuleCat.of ℤ (ULift.{u} ℤ))) := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let p := originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let n := SSet.chainComplexMap p.hom R
  let eS := originalTopRegularPullbackCoverChainIso f y
  let eT := originalTopRegularCoverChainIso Y y
  exact Arrow.isoMk' m n eS eT (originalTopRegularCoverChainMap_square f y).symm

/-- Relative regular chains identify with the actual relative native cover chains. -/
noncomputable def originalRegularRelativeChainIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    originalRegularRelativeChainComplex f y ≅
      (originalRegularPulledCoverPair f y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let p := originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  exact CokernelCofork.mapIsoOfIsColimit
    (cokernelIsCokernel m) (p.isColimitCokernelCoforkChainComplex R)
      (regularRelativeArrowIso f y)

/-- The relative comparison commutes with the whole original quotient chain map. -/
theorem originalRegularRelativeChainIso_projection {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    originalRegularRelativeChainProjection f y ≫ (originalRegularRelativeChainIso f y).hom =
      (originalTopRegularCoverChainIso Y y).hom ≫
        (originalRegularPulledCoverPair f y).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ)) := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let p := originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  exact CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel m)
    (p.cokernelCoforkChainComplex R) (regularRelativeArrowIso f y).hom

/-- The inverse relative comparison commutes with the same original quotient. -/
theorem originalRegularRelativeChainIso_inverse_projection {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    (originalRegularPulledCoverPair f y).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ)) ≫
        (originalRegularRelativeChainIso f y).inv =
      (originalTopRegularCoverChainIso Y y).inv ≫ originalRegularRelativeChainProjection f y := by
  let A := localCoefficientChainComplex
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let P := (originalRegularPulledCoverPair f y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
  let V := (SSet.KanComplex.nativeCover (TopCat.toSSet.obj Y)
    (TopCat.toSSetObj₀Equiv.symm y)).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
  let e : originalRegularRelativeChainComplex f y ≅ P := originalRegularRelativeChainIso f y
  let eT : A ≅ V := originalTopRegularCoverChainIso Y y
  let q : A ⟶ originalRegularRelativeChainComplex f y := originalRegularRelativeChainProjection f y
  let qP : V ⟶ P := (originalRegularPulledCoverPair f y).chainComplexπ
    (ModuleCat.of ℤ (ULift.{u} ℤ))
  have hProjection : q ≫ e.hom = eT.hom ≫ qP := originalRegularRelativeChainIso_projection f y
  have hPre : eT.inv ≫ (q ≫ e.hom) = qP :=
    (congrArg (fun t => eT.inv ≫ t) hProjection).trans (eT.inv_hom_id_assoc qP)
  have hCancel : q ≫ (e.hom ≫ e.inv) = q :=
    (congrArg (fun t => q ≫ t) e.hom_inv_id).trans (Category.comp_id q)
  calc
    qP ≫ e.inv = (eT.inv ≫ (q ≫ e.hom)) ≫ e.inv :=
      congrArg (fun t => t ≫ e.inv) hPre.symm
    _ = eT.inv ≫ ((q ≫ e.hom) ≫ e.inv) := Category.assoc _ _ _
    _ = eT.inv ≫ (q ≫ (e.hom ≫ e.inv)) :=
      congrArg (fun t => eT.inv ≫ t) (Category.assoc q e.hom e.inv)
    _ = eT.inv ≫ q := congrArg (fun t => eT.inv ≫ t) hCancel

/-- The actual regular coefficient base-map chain morphism is monic for a monic `f`. -/
theorem originalRegularPullbackChainMap_mono {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    Mono (localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))) := by
  let p := originalRegularPulledCoverPair f y
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let n := SSet.chainComplexMap p.hom R
  let eS := originalTopRegularPullbackCoverChainIso f y
  let eT := originalTopRegularCoverChainIso Y y
  have hMonoN : Mono n := inferInstance
  have hMonoS : Mono eS.hom := inferInstance
  have hMonoComposite : Mono (eS.hom ≫ n) := mono_comp' hMonoS hMonoN
  have hSquare : m ≫ eT.hom = eS.hom ≫ n := originalTopRegularCoverChainMap_square f y
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hMonoComposite hSquare

/-- The actual regular coefficient quotient sequence is short exact. -/
theorem originalRegularRelative_shortExact {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) :
    (ShortComplex.cokernelSequence (localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk y)))).ShortExact := by
  let m := localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))
  let : Mono m := originalRegularPullbackChainMap_mono f y
  let : Mono (Arrow.mk m).hom := by
    change Mono m
    infer_instance
  exact ShortComplex.cokernelSequence_shortExact (Arrow.mk m)

/-- Relative regular homology is the actual relative homology of the pulled cover. -/
noncomputable def originalRegularRelativeHomologyIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) (n : ℕ) :
    (originalRegularRelativeChainComplex f y).homology n ≅
      (originalRegularPulledCoverPair f y).homology (ModuleCat.of ℤ (ULift.{u} ℤ)) n :=
  HomologicalComplex.homologyMapIso (originalRegularRelativeChainIso f y) n

/-- The whole quotient-to-relative homology map is calibrated by the same cover comparison. -/
theorem originalRegularRelativeHomologyIso_projection {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) (n : ℕ) :
    HomologicalComplex.homologyMap (originalRegularRelativeChainProjection f y) n ≫
        (originalRegularRelativeHomologyIso f y n).hom =
      HomologicalComplex.homologyMap (originalTopRegularCoverChainIso Y y).hom n ≫
        (originalRegularPulledCoverPair f y).homologyπ (ModuleCat.of ℤ (ULift.{u} ℤ)) n := by
  let H : ChainComplex (ModuleCat.{u} ℤ) ℕ ⥤ ModuleCat.{u} ℤ :=
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n
  let q := originalRegularRelativeChainProjection f y
  let e := originalRegularRelativeChainIso f y
  let eT := originalTopRegularCoverChainIso Y y
  let qP := (originalRegularPulledCoverPair f y).chainComplexπ (ModuleCat.of ℤ (ULift.{u} ℤ))
  exact (H.map_comp q e.hom).symm.trans
    ((congrArg H.map (originalRegularRelativeChainIso_projection f y)).trans
      (H.map_comp eT.hom qP))

/-- The original relative object is the cokernel of its actual regular chain map. -/
theorem originalRegularRelativeChainComplex_eq_cokernel {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    originalRegularRelativeChainComplex f y =
      cokernel (localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))) := by
  rfl

/-- The whole original quotient map is the same cokernel projection under the object equality. -/
theorem originalRegularRelativeChainProjection_eq_cokernelπ {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) :
    originalRegularRelativeChainProjection f y ≫
        (eqToIso (originalRegularRelativeChainComplex_eq_cokernel f y)).hom =
      cokernel.π (localCoefficientPullbackChainMap f
        (CategoryTheory.regularPathModuleCoefficientFunctor
            (_root_.FundamentalGroupoid.mk y))) := by
  rfl

/-- The actual original regular relative quotient map is an epimorphism. -/
theorem originalRegularRelativeChainProjection_epi {X Y : TopCat.{u}}
    (f : X ⟶ Y) (y : Y) : Epi (originalRegularRelativeChainProjection f y) := by
  change Epi (cokernel.π (localCoefficientPullbackChainMap f
    (CategoryTheory.regularPathModuleCoefficientFunctor (_root_.FundamentalGroupoid.mk y))))
  infer_instance

/-- The homology comparison maps the same original relative chain isomorphism. -/
theorem originalRegularRelativeHomologyIso_hom {X Y : TopCat.{u}}
    (f : X ⟶ Y) [Mono f] (y : Y) (n : ℕ) :
    (originalRegularRelativeHomologyIso f y n).hom =
      HomologicalComplex.homologyMap (originalRegularRelativeChainIso f y).hom n := by
  rfl

end TopCat

end
