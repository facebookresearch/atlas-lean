/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedClassicalComplexComparisonClassicalIdentitySourceTransportEquivalence
import MathlibExt.AlgebraicGeometry.ClassicalComplexCoefficientMaps
import MathlibExt.AlgebraicGeometry.DerivedNativeComplexTruncation

/-!
# Corollaries of classical identity source transport equivalence

Transport gives a bijection on derived isomorphisms and every native
complexes object is isomorphic to a transported classical object.

References: Toën--Vaquié math/0503269v5 §3.1 pp36--37 and p8;
Stacks 03G8, 06YY, 0D6D, 0DLD/0DLE. The native ordinary-stack source
is ComplexesStack.lean at AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b; its general algebraic-space
algebraicity theorem is not re-requested here.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
open MathlibExt.AlgebraicGeometry.NativeIdentityComplexesStack

namespace MathlibExtTest.AlgebraicGeometry
namespace DerivedClassicalComplexComparisonClassicalIdentitySourceTransportEquivalence

universe u

private theorem transport_isomorphisms_bijective (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A))
    (H : IdentityComplexesTransportSource L A J) (E E' : ComplexesFibre L J) :
    Function.Bijective ((identityComplexesTransport H).map :
      (E ⟶ E') → ((identityComplexesTransport H).obj E ⟶
        (identityComplexesTransport H).obj E')) := by
  have := classical_identity_source_transport_equivalence k O L A J H
  exact ⟨(identityComplexesTransport H).map_injective,
    (identityComplexesTransport H).map_surjective⟩

private theorem native_object_has_classical_presentation (k : Type u) [CommRing k]
    (O : ∀ X : Scheme.{u}, EtaleStructureSource X) (L : EtalePullbackSystem O)
    (A : CommAlgCat.{u} k) (J : AffineEtaleModuleSource O (ordinaryRing A))
    (H : IdentityComplexesTransportSource L A J) (E : NativeComplexesFibre L A J) :
    ∃ E' : ComplexesFibre L J, Nonempty ((identityComplexesTransport H).obj E' ≅ E) := by
  have := classical_identity_source_transport_equivalence k O L A J H
  exact ⟨(identityComplexesTransport H).objPreimage E,
    ⟨(identityComplexesTransport H).objObjPreimageIso E⟩⟩

end DerivedClassicalComplexComparisonClassicalIdentitySourceTransportEquivalence
end MathlibExtTest.AlgebraicGeometry
