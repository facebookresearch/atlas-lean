/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The checked matrix prefixes are the actual original-source C322 representatives. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCRepresentativeCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepresentativeValues

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The selected finite matrix prefix denotes exactly its actual original C322 representative. -/
theorem y322Orthogonal3TCRepresentativeCache_source (i : Fin 3159) :
    y322Orthogonal3TCCacheSource (y322Orthogonal3TCRepresentativeCache i) =
      y322TCIndexRepresentative i := by
  unfold y322Orthogonal3TCCacheSource y322TCIndexRepresentative
  apply congrArg (y322LocalProgramValue y322TransportProgram)
  apply Fin.ext
  change 38540 + (y322Orthogonal3TCCacheNode (y322Orthogonal3TCRepresentativeCache i)).val =
    38540 + (y322TCIndexRepresentativeNode i).val
  rw [y322Orthogonal3TCRepresentativeCache_node]

/-- Each actual original-source representative has exactly the checked finite image matrix. -/
theorem y322Orthogonal3TCRepresentative_matrix (i : Fin 3159) :
    (y322Orthogonal3Hom (y322TCIndexRepresentative i)).val =
      y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache i) := by
  rw [← y322Orthogonal3TCRepresentativeCache_source]
  exact (y322Orthogonal3TCCacheSource_matrices _).1

/-- Each actual original-source representative inverse has its exact checked image matrix. -/
theorem y322Orthogonal3TCRepresentative_inverse (i : Fin 3159) :
    ((y322Orthogonal3Hom (y322TCIndexRepresentative i))⁻¹).val =
      y322Orthogonal3TCCacheInverse (y322Orthogonal3TCRepresentativeCache i) := by
  rw [← y322Orthogonal3TCRepresentativeCache_source]
  exact (y322Orthogonal3TCCacheSource_matrices _).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
