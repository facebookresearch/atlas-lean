/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ClosureQuasiCompactImage

/-!
# Tests for the closure of the image of a quasi-compact morphism
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MathlibExtTest.AlgebraicGeometry.ClosureQuasiCompactImage

universe u

/-- Every point of the closure of the image of a quasi-compact morphism is a specialization of a
point of the image. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (y : Y)
    (hy : y ∈ closure (Set.range f)) : ∃ x, f x ⤳ y :=
  f.exists_specializes_of_mem_closure_range hy

/-- So the closure of the image is the set of specializations of points of the image. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    closure (Set.range f) = {y | ∃ x, f x ⤳ y} := by
  ext y
  refine ⟨f.exists_specializes_of_mem_closure_range, ?_⟩
  rintro ⟨x, hx⟩
  exact hx.mem_closed isClosed_closure (subset_closure ⟨x, rfl⟩)

/-- The affine case: for a ring map `R →+* A`, a prime of `R` containing the kernel contains the
contraction of a prime of `A`. -/
example {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (p : PrimeSpectrum R)
    (hp : RingHom.ker φ ≤ p.asIdeal) : ∃ q : PrimeSpectrum A, PrimeSpectrum.comap φ q ≤ p :=
  PrimeSpectrum.exists_comap_le_of_ker_le φ p hp

end MathlibExtTest.AlgebraicGeometry.ClosureQuasiCompactImage
