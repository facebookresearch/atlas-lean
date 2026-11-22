/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.EnrichedOrdinaryMonoidal
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereFunctor
public import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor

/-!
# The actual original orthogonal sphere monoidal coefficient

The ordinary coefficient and monoidal structure are projected from the entire
original enriched sphere functor. Its epsilon and mu are exactly the original
one-point unit and inverse ordered sphere splitting.
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

/-- The original full Orth sphere functor viewed on its actual ordinary native arrows. -/
def originalOrthogonalSphereOrdinary : OrthogonalIndex ⥤ PointedCGWH.{u, v} :=
  orthogonalSphereFunctor.{u, v}.toOrdinaryFunctor

/-- The original native sphere object is retained in every degree. -/
@[simp]
theorem originalOrthogonalSphereOrdinary_obj (n : OrthogonalIndex) :
    originalOrthogonalSphereOrdinary.{u, v}.obj n = PointedCGWH.orthogonalSphere.{u, v} n := rfl

/-- The native ordinary arrow acts by the original full sphere action. -/
theorem originalOrthogonalSphereOrdinary_map {m n : OrthogonalIndex} (f : m ⟶ n) :
    originalOrthogonalSphereOrdinary.{u, v}.map f = orthogonalSphereMap.{u, v} f := rfl

/-- Actual full enriched monoidal data determines the original ordinary lax structure. -/
@[instance_reducible]
def originalOrthogonalSphereLax : originalOrthogonalSphereOrdinary.{u, v}.LaxMonoidal :=
  EnrichedFunctor.inducedOrdinaryLaxMonoidal OrthogonalIndex.enrichedMonoidalData.{u, v}
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf PointedCGWH.{u, v})
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

/-- The selected lax unit is the actual one-point sphere unit. -/
theorem originalOrthogonalSphereLax_epsilon :
    letI := originalOrthogonalSphereLax.{u, v}
    Functor.LaxMonoidal.ε originalOrthogonalSphereOrdinary.{u, v} =
      PointedCGWH.orthogonalSphereUnitIso.{u, v}.hom := rfl

/-- Every selected lax tensorator is the actual inverse ordered sphere splitting. -/
theorem originalOrthogonalSphereLax_mu (m n : OrthogonalIndex) :
    letI := originalOrthogonalSphereLax.{u, v}
    Functor.LaxMonoidal.μ originalOrthogonalSphereOrdinary.{u, v} m n =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} m n).inv := rfl

/-- The original unit and ordered tensorators supply the actual strong monoidal structure. -/
@[instance_reducible]
def originalOrthogonalSphereMonoidal : originalOrthogonalSphereOrdinary.{u, v}.Monoidal := by
  letI := originalOrthogonalSphereLax.{u, v}
  letI : IsIso (Functor.LaxMonoidal.ε originalOrthogonalSphereOrdinary.{u, v}) :=
    orthogonalSphereStrongData.{u, v}.unitIso
  letI : ∀ m n, IsIso (Functor.LaxMonoidal.μ originalOrthogonalSphereOrdinary.{u, v} m n) :=
    orthogonalSphereStrongData.{u, v}.tensorIso
  exact Functor.Monoidal.ofLaxMonoidal originalOrthogonalSphereOrdinary.{u, v}

/-- The actual original index braiding remains compatible with original sphere multiplication. -/
@[instance_reducible]
def originalOrthogonalSphereBraided :
    letI := originalOrthogonalSphereMonoidal.{u, v}
    originalOrthogonalSphereOrdinary.{u, v}.Braided := by
  letI := originalOrthogonalSphereMonoidal.{u, v}
  constructor
  intro m n
  exact orthogonalSphereBraidedData.{u, v}.braided m n

end CategoryTheory.Spectra
