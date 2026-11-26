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
# Naturality of identity evaluation in continuous degree-zero cohomology

Let G be a profinite group and X,Y topological ℤ-representations, with
coefficient carriers in max(v,w), where G has universe v.
The canonical isomorphism H⁰_cts(G,X) ≅ X^G is given by evaluating a
closed homogeneous degree-zero cochain at the identity.
It is natural under continuous equivariant ℤ-linear coefficient maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe v w

namespace ContinuousCohomology

open CategoryTheory CategoryTheory.Limits



/-- For a profinite group G and a continuous equivariant ℤ-linear
map f : X → Y between topological representations, the identity-evaluation
isomorphisms satisfy
zeroIso_Y ∘ H⁰_cts(G,f)=Inv_G(f) ∘ zeroIso_X.
The coefficient topology need not be discrete. -/
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
