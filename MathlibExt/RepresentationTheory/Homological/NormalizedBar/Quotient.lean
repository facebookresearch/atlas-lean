/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.Normalization

/-!
# The degeneracy subcomplex and literal normalized bar quotient

Native kernels and cokernels in the abelian category of complexes give the
actual degeneracy subcomplex and quotient. The tuple projection is a split
epimorphism, so its coimage is canonically the literal normalized complex.
The degree kernel is certified by the actual nonidentity tuple projection,
whose kernel is the group-ring span of identity-containing symbols.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

universe u v

namespace Rep.NormalizedBar

variable (k : Type u) [CommRing k] (G : Type v) [Group G]

/-- The literal nonidentity tuple degree is projective, using the native
representation/module equivalence and the actual free group-ring basis.
Coefficient and group universes remain independent. -/
theorem degree_projective (n : ℕ) : Projective (degree k G n) := by
  apply Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective
  exact @ModuleCat.projective_of_free _ _
    (ModuleCat.of k[G] (Representation.free k G (Tuple G n)).asModule)
    _ (Representation.freeAsModuleBasis k G (Tuple G n))

instance complex_X_projective (n : ℕ) : Projective ((complex k G).X n) := by
  change Projective (degree k G n)
  exact degree_projective k G n

instance projection_epi : Epi (projection k G) :=
  epi_of_epi_fac (inclusion_comp_projection k G)

/-- The actual degeneracy subcomplex of the standard complex. -/
abbrev degeneracyComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  kernel (projection k G)

/-- Its actual chain inclusion. -/
abbrev degeneracyInclusion : degeneracyComplex k G ⟶ standardComplex k G :=
  kernel.ι (projection k G)

@[reassoc]
theorem degeneracyInclusion_comp_projection :
    degeneracyInclusion k G ≫ projection k G = 0 :=
  kernel.condition (projection k G)

/-- The actual cokernel quotient by the degeneracy subcomplex. -/
abbrev quotientComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  cokernel (degeneracyInclusion k G)

/-- The actual quotient map into that cokernel. -/
abbrev quotientMap : standardComplex k G ⟶ quotientComplex k G :=
  cokernel.π (degeneracyInclusion k G)

/-- The native coimage isomorphism identifies the actual degeneracy quotient
with the literal nonidentity tuple complex. No isomorphism is a caller input. -/
def quotientIso : quotientComplex k G ≅ complex k G :=
  asIso (Abelian.factorThruCoimage (projection k G))

@[reassoc (attr := simp)]
theorem quotientMap_comp_quotientIso_hom :
    quotientMap k G ≫ (quotientIso k G).hom = projection k G :=
  Abelian.coimage.fac (projection k G)

/-- The component kernel is exactly the degenerate-symbol span in the
inhomogeneous tuple presentation, through the actual standard-basis iso. -/
theorem projection_f_kernel_iff (n : ℕ) (f : (fullDegree k G n).V) :
    ((projection k G).f n).hom ((basisIso k G n).inv.hom f) = 0 ↔
      f ∈ degenerateDegree k G n := by
  rw [projection_f]
  change (rawProjection k G n).hom
      ((basisIso k G n).hom.hom ((basisIso k G n).inv.hom f)) = 0 ↔ _
  rw [Rep.hom_inv_apply]
  exact rawProjection_eq_zero_iff k G n f

/-- The differential on a literal normalized symbol is the projection of
the actual standard differential on its raw homogeneous representative. -/
theorem differential_on_raw_lift (n : ℕ) (x : (degree k G (n + 1)).V) :
    ((complex k G).d (n + 1) n).hom x =
      (standardProjection k G n).hom
        (((standardComplex k G).d (n + 1) n).hom
          ((standardRawInclusion k G (n + 1)).hom x)) := by
  have h := congrArg (fun f => f.hom ((standardRawInclusion k G (n + 1)).hom x))
    ((projection k G).comm (n + 1) n)
  change ((complex k G).d (n + 1) n).hom
      (((projection k G).f (n + 1)).hom
        ((standardRawInclusion k G (n + 1)).hom x)) =
    ((projection k G).f n).hom
      (((standardComplex k G).d (n + 1) n).hom
        ((standardRawInclusion k G (n + 1)).hom x)) at h
  rw [projection_f, projection_f] at h
  have hx : (standardProjection k G (n + 1)).hom
      ((standardRawInclusion k G (n + 1)).hom x) = x :=
    congrArg (fun f => f.hom x) (standardRawInclusion_comp_standardProjection k G (n + 1))
  have hd := congrArg
    (fun y : (degree k G (n + 1)).V => ((complex k G).d (n + 1) n).hom y) hx
  exact hd.symm.trans h

end Rep.NormalizedBar

end
