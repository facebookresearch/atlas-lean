/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereMonoidal

/-!
# Exact isomorphism characteristics of the original sphere coefficient
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory

/-- The selected strong unit Iso is the original one-point sphere unit. -/
theorem originalOrthogonalSphereMonoidal_epsilonIso :
    letI := originalOrthogonalSphereMonoidal.{u, v}
    Functor.Monoidal.εIso originalOrthogonalSphereOrdinary.{u, v} =
      PointedCGWH.orthogonalSphereUnitIso.{u, v} := by
  let _ := originalOrthogonalSphereMonoidal.{u, v}
  apply Iso.ext
  rfl

/-- The selected strong tensor Iso is the actual inverse ordered sphere splitting. -/
theorem originalOrthogonalSphereMonoidal_muIso (m n : OrthogonalIndex) :
    letI := originalOrthogonalSphereMonoidal.{u, v}
    Functor.Monoidal.μIso originalOrthogonalSphereOrdinary.{u, v} m n =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).symm := by
  let _ := originalOrthogonalSphereMonoidal.{u, v}
  apply Iso.ext
  rfl

end CategoryTheory.Spectra
