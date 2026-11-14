/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoherentGTheory

/-!
# Localization and Zariski descent for the actual coherent S-construction

The spaces and all maps in these requests are geometric realizations of
actual short-exact coherent flags. Support means that the actual sheaf
restriction is zero; it is not a supported-vector-bundle subcategory.
The fibre and pullback are subspaces of continuous paths with the displayed
endpoints, and the comparison maps are normalized by their projections.

Generic Grothendieck groups, symmetric spectra and Karoubi constructions
already occur in the public sources. These requests concern the higher
coherent-theory localization and descent for the concrete S-construction
carrier here. No higher-dimensional GRR or completed spectrum system is
claimed by this packet.

Sources: Quillen, *Higher algebraic K-theory I* (1973), §5, localization;
Waldhausen, *Algebraic K-theory of spaces* (1985), §1.3. Existing generic
point-set spectra:
https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/SymmetricSpectrum.lean
Existing Grothendieck groups:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/CategoryTheory/Abelian/GrothendieckGroup.lean
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoherentHigherGTheoryWanted

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentGTheory

/-- The actual supported coherent space is the homotopy fibre of restriction,
with its projection equal up to homotopy to the actual inclusion. -/
public theorem_wanted localization (X : Scheme.{0}) [IsNoetherian X]
    (U : X.Opens) [RestrictionCoherent X U] :
    ∃ e : ContinuousMap.HomotopyEquiv (supportedSpace X U)
        (homotopyFiber (restriction X U) (gBase U)),
      Nonempty ((fiberProjection (restriction X U) (gBase U)).comp e.toFun |>.Homotopy
        (supportedInclusion X U).hom)

/-- An actual two-open covering square realizes as a homotopy pullback,
normalized by both actual restriction maps. -/
public theorem_wanted zariski_descent (X U V W : Scheme.{0})
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian V] [IsNoetherian W]
    (i : U ⟶ X) (j : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V)
    [IsOpenImmersion i] [IsOpenImmersion j]
    [IsOpenImmersion p] [IsOpenImmersion q]
    (square : IsPullback p q i j)
    (cover : Set.range i.base ∪ Set.range j.base = Set.univ)
    [OpenRestrictionCoherent i] [OpenRestrictionCoherent j]
    [OpenRestrictionCoherent p] [OpenRestrictionCoherent q] :
    ∃ e : ContinuousMap.HomotopyEquiv (gSpace X)
        (homotopyPullback (openRestriction p) (openRestriction q)),
      Nonempty ((pullbackFirst (openRestriction p) (openRestriction q)).comp e.toFun |>.Homotopy
        (openRestriction i).hom) ∧
      Nonempty ((pullbackSecond (openRestriction p) (openRestriction q)).comp e.toFun |>.Homotopy
        (openRestriction j).hom)

end WantedExt.AlgebraicGeometry.CoherentHigherGTheoryWanted
