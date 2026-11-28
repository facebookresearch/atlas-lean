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
# Degeneracy subcomplex and normalized group-bar quotient

Let k be a commutative ring in universe u and G a group in universe v.
The normalized degree is a free k[G]-module on nonidentity tuples,
hence a projective representation. The split chain projection
π:C→Q from standard homogeneous chains has degeneracy kernel D.

Its cokernel quotient C/D is canonically Q.
Degree kernel membership is the group-ring span of identity-containing
tuple symbols. For a normalized element x in degree n+1, its differential
can be computed by raw homogeneous inclusion, the standard alternating
boundary, then the degree n nonidentity projection.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

universe u v

namespace Rep.NormalizedBar

variable (k : Type u) [CommRing k] (G : Type v) [Group G]

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
Each normalized degree Q_n is a projective representation,
being free over k[G] on the nonidentity tuple index set. -/
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

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
The degeneracy complex is D=ker(π:C→Q) in the abelian
category of nonnegative representation complexes. -/
abbrev degeneracyComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  kernel (projection k G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
The degeneracy inclusion D→C is the kernel inclusion
of the normalization projection. -/
abbrev degeneracyInclusion : degeneracyComplex k G ⟶ standardComplex k G :=
  kernel.ι (projection k G)

@[reassoc]
theorem degeneracyInclusion_comp_projection :
    degeneracyInclusion k G ≫ projection k G = 0 :=
  kernel.condition (projection k G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
The quotient complex is Coker(D→C), the chain cokernel by
the degeneracy subcomplex. -/
abbrev quotientComplex : ChainComplex (Rep.{max u v} k G) ℕ :=
  cokernel (degeneracyInclusion k G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
The quotient chain map C→Coker(D→C) is the cokernel
projection of the degeneracy inclusion. -/
abbrev quotientMap : standardComplex k G ⟶ quotientComplex k G :=
  cokernel.π (degeneracyInclusion k G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
The canonical isomorphism Coker(D→C)≅Q identifies the
quotient projection with π:C→Q. -/
def quotientIso : quotientComplex k G ≅ complex k G :=
  asIso (Abelian.factorThruCoimage (projection k G))

@[reassoc (attr := simp)]
theorem quotientMap_comp_quotientIso_hom :
    quotientMap k G ≫ (quotientIso k G).hom = projection k G :=
  Abelian.coimage.fac (projection k G)

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
For a full tuple vector f, converting it to standard homogeneous
coordinates and projecting by π is zero exactly when f lies in
the k[G]-span of identity-containing tuples. -/
theorem projection_f_kernel_iff (n : ℕ) (f : (fullDegree k G n).V) :
    ((projection k G).f n).hom ((basisIso k G n).inv.hom f) = 0 ↔
      f ∈ degenerateDegree k G n := by
  rw [projection_f]
  change (rawProjection k G n).hom
      ((basisIso k G n).hom.hom ((basisIso k G n).inv.hom f)) = 0 ↔ _
  rw [Rep.hom_inv_apply]
  exact rawProjection_eq_zero_iff k G n f

/-- Let k be a commutative ring in universe u and G a group in
universe v. Let C be the standard homogeneous group complex, Q the
normalized nonidentity-tuple complex, π:C→Q its split projection,
and I:Q→C its normalization-corrected section.
For x∈Q_(n+1), the differential has the raw-lift formula
d_Q(x)=π_n(d_C(r_(n+1)(x))),
where r is the raw homogeneous tuple inclusion.
This is a degreewise computation with the standard alternating boundary. -/
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
