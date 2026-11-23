/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.Topology.Sphere.StandardCover

/-!
# Standard spheres as pointed spaces

The north pole gives the standard Euclidean sphere model a canonical
basepoint, uniformly in its dimension and ambient universe.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace TopCat

/-- The north-pole basepoint of the standard sphere. -/
def sphereBasepoint (m : ℕ) :
    TopCat.of PUnit ⟶ TopCat.sphere.{u} m :=
  TopCat.ofHom
    (ContinuousMap.const _
      (ULift.up.{u, 0} (AlgebraicTopology.northPt m)))

/-- The standard sphere pointed at its north pole. -/
def pointedSphere (m : ℕ) : PointedTopCat.{u} :=
  Under.mk (sphereBasepoint.{u} m)

end TopCat
