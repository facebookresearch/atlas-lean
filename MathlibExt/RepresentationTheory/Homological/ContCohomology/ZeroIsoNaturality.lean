/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
The existing homogeneous identity-evaluation comparison is natural in the original coefficient
arrows.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe v w

namespace ContinuousCohomology

open CategoryTheory CategoryTheory.Limits



/-- The existing identity-evaluation comparison is natural in every original
coefficient map, on the same homogeneous cocycles and homology quotient. -/
theorem homogeneousZeroIso_coefficient_naturality {G : ProfiniteGrp.{v}}
    {X Y : TopRep.{max v w, 0, v} ℤ G} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap
        ((homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map f) 0 ≫
      (zeroIso Y).hom = (zeroIso X).hom ≫ (TopRep.invariantsFunctor ℤ G).map f := by
  apply (cancel_epi (π X 0)).1
  apply ConcreteCategory.ext
  apply DFunLike.ext
  intro c
  apply Subtype.ext
  let m := (homogeneousCochainsFunctor.{0, v, w} (k := ℤ) (G := G)).map f
  let cY := HomologicalComplex.cyclesMap m 0 c
  have hπ := congrArg (fun q => q c) (HomologicalComplex.homologyπ_naturality m 0)
  have hI := congrArg (fun q => (q c).val 1) (HomologicalComplex.cyclesMap_i m 0)
  have hval : (m.f 0 ((TopRep.homogeneousCochains X).iCycles 0 c)).val 1 =
      f.hom (((TopRep.homogeneousCochains X).iCycles 0 c).val 1) := by
    rfl
  exact (congrArg (fun q => ((zeroIso Y).hom q).val) hπ).trans
    ((homogeneousZeroIso_cycles_value.{0, v, w} Y cY).trans
      (hI.trans (hval.trans
        (congrArg f.hom (homogeneousZeroIso_cycles_value.{0, v, w} X c)).symm)))

end ContinuousCohomology
