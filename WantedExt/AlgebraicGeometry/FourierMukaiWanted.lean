/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FourierMukai

/-!
# Unresolved existence and composition of Fourier–Mukai derived functors

Completed ordinary constructions and conditional Kan-extension implementations
are in `MathlibExt.AlgebraicGeometry.FourierMukai`. This file asks for the
missing existence instances and the flat, quasi-coherent composition theorem.
No completed construction is marked wanted.

The derived operators have fixed cochain tensor, pullback and pushforward
sources, with genuine Kan universal properties. The classes in the proved
core carry only these actual derived-existence assumptions.

The composition request is the flat special case of Stacks 0FYS. All three
structure maps are quasi-compact, quasi-separated and flat. The kernels and
source objects have quasi-coherent cohomology. The isomorphism is natural in
source objects and is stated in the ambient derived category.

The public AxiomMath/Stacks proof also uses derived tensor associativity,
monoidality and composition of derived pullback, composition of derived
pushforward, quasi-coherent preservation, derived base change (08IB) and the
projection formula (08EU). Those comparison proofs are not supplied by
Kan-extension existence alone and remain necessary for this request.
The completed seven-step assembly is
`fourierMukaiCompIsoOfComparisons` in the proved core; its input comparisons
still have to be constructed and proved invertible in the stated scope.

## References

* The Stacks Project, Tags 06YJ, 06YU, 0FYQ, 0FYS, 08IB and 08EU.
* AxiomMath/Stacks at commit c496df0d9beea9deaeabcea8492605f9a0a2313b,
  `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Basic.lean`,
  `Composition.lean` and `CompositionIso.lean`. The adapted completed
  constructions and their Apache-2.0 notice are in the proved core.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry.FourierMukai

namespace WantedExt.AlgebraicGeometry.FourierMukaiWanted

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Existence of the actual left derived module-sheaf pullbacks. Source:
Stacks 06YJ; their cochain sources are fixed in the proved core. -/
public instance_wanted derivedPullbacks_exists : HasDerivedPullbacks.{u}

/-- Existence of the actual unbounded right derived module-sheaf direct
images. Source: Stacks 0FYQ's direct-image factor. -/
public instance_wanted derivedPushforwards_exists : HasDerivedPushforwards.{u}

/-- Existence of the left derived total cochain tensor along `Q × Q`,
deriving both variables. Source: Stacks 06YU. -/
public instance_wanted derivedTensors_exists : HasDerivedTensors.{u}

/-- **Composition of Fourier–Mukai functors, flat case.** Let $f : X \to S$, $g : Y \to S$
and $h : Z \to S$ be quasi-compact, quasi-separated, flat morphisms of schemes, and let
$K \in D(X \times_S Y)$ and $K' \in D(Y \times_S Z)$ have quasi-coherent cohomology sheaves.
Then there is an isomorphism $\Phi_{K'}(\Phi_K(M)) \cong \Phi_{K \star K'}(M)$, natural in the
complexes $M \in D(X)$ with quasi-coherent cohomology sheaves, where $\Phi$ is the Fourier–Mukai
functor `fourierMukai` and
$K \star K' = R\mathrm{pr}_{13,*}(L\mathrm{pr}_{12}^* K \otimes^L L\mathrm{pr}_{23}^* K')$ is the
convolution `convolution` on $X \times_S Z$. Here $D$ is the unbounded derived category of sheaves
of modules, and derived pullback, pushforward and tensor product are the total derived functors,
assumed to exist (`HasDerivedPullbacks`, `HasDerivedPushforwards`, `HasDerivedTensors`).

Source: Stacks 0FYS (flat case), 08IB and 08EU. -/
public theorem_wanted fourierMukai_comp_of_flat {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] [Flat f] [Flat g] [Flat h]
    (K : D (pullback f g)) (K' : D (pullback g h))
    (hK : quasicoherent (pullback f g) K)
    (hK' : quasicoherent (pullback g h) K') :
    Nonempty
      ((quasicoherent X).ι ⋙ fourierMukai f g K ⋙ fourierMukai g h K' ≅
        (quasicoherent X).ι ⋙ fourierMukai f h (convolution f g h K K'))

end WantedExt.AlgebraicGeometry.FourierMukaiWanted
