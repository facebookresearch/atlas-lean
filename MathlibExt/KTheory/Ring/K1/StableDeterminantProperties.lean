/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K1.StableDeterminant
public import MathlibExt.KTheory.Ring.StableElementary.Basic

/-! # Stable determinant properties

Naturality for ring homomorphisms via finite representatives and
`Matrix.GeneralLinearGroup.det_mapRingHom`, surjectivity from rank-one
`det_surjective` and `StableGL.det_of`, and the elementary subgroup lying in
the kernel via closure generators and `det_elementary`.
-/

@[expose] public section

open AlgebraicKTheory
open Matrix.GeneralLinearGroup

universe u

noncomputable section

namespace AlgebraicKTheory

namespace StableGL

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S]

/-- Same-universe pointwise naturality of the stable determinant. -/
@[simp]
theorem det_mapRingHom (f : R →+* S) (x : StableGL R) :
    det (R := S) ((StableGL.functor.map (SemiRingCat.ofHom f)).hom x) =
      (det (R := R) x).map f.toMonoidHom := by
  obtain ⟨n, g, rfl⟩ := StableGL.exists_finite_rep (R := R) x
  calc det (R := S) ((StableGL.functor.map (SemiRingCat.ofHom f)).hom (StableGL.of g))
      = det (R := S) (StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g)) := by
        rw [StableGL.map_of]
    _ = Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mapRingHom f g) := by
        rw [StableGL.det_of]
    _ = (Matrix.GeneralLinearGroup.det g).map f := by
        rw [Matrix.GeneralLinearGroup.det_mapRingHom]
    _ = (Matrix.GeneralLinearGroup.det g).map f.toMonoidHom := rfl
    _ = (det (R := R) (StableGL.of g)).map f.toMonoidHom := by
        rw [StableGL.det_of]

/-- Bundled `MonoidHom` equality for determinant naturality. -/
theorem det_comp_mapRingHom (f : R →+* S) :
    (det (R := S)).comp (StableGL.functor.map (SemiRingCat.ofHom f)).hom =
      (Units.map f.toMonoidHom).comp (det (R := R)) := by
  apply MonoidHom.ext
  intro x
  exact det_mapRingHom f x

variable (R : Type u) [CommRing R]

/-- Stable determinant is surjective, via rank-one finite surjectivity. -/
theorem det_surjective : Function.Surjective (det (R := R)) := by
  intro u
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 1) (R := R) u
  exact ⟨StableGL.of g, by
    calc det (R := R) (StableGL.of g)
        = Matrix.GeneralLinearGroup.det g := StableGL.det_of g
      _ = u := hg⟩

end StableGL

/-- Stable elementary subgroup lies in the kernel of the stable determinant. -/
theorem stableElementarySubgroup_le_ker_det (R : Type u) [CommRing R] :
    stableElementarySubgroup R ≤ MonoidHom.ker (StableGL.det (R := R)) := by
  rw [stableElementarySubgroup, Subgroup.closure_le]
  intro y hy
  obtain ⟨n, i, j, hij, a, rfl⟩ := hy
  have hdet :
      StableGL.det (R := R)
        (StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a)) = 1 := by
    rw [StableGL.det_of, Matrix.GeneralLinearGroup.det_elementary]
  exact MonoidHom.mem_ker.mpr hdet

end AlgebraicKTheory

end
