/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/RingTheory/Flat/MiracleFlatness.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), for the statement of local miracle flatness:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: recorded as `theorem_wanted`, with the Cohen–Macaulay condition
`Module.IsMaximalCohenMacaulay S S` expanded to the equality of Mathlib's `IsLocalRing.depth` and
`ringKrullDim`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

/-!
# Local miracle flatness

A local homomorphism from a regular local ring `R` to a Cohen–Macaulay
Noetherian local ring `S` is flat if the dimension of `S` is the sum of
the dimensions of `R` and the closed fiber `S/𝔪_R S`.

Cohen–Macaulayness is expressed by the depth of `S` as a module over
itself, at its own maximal ideal, equaling its Krull dimension.
Mathlib's regular local ring class includes locality and Noetherianity.

The credited Axiom source contains an ordinary proof, using its concrete
regular-sequence definition of depth. The main theorem remains deferred
here pending the following proof dependencies:

* `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient`, from
  `StacksFrontier/RingTheory/Flat/LocalCriterionVariant/Criterion.lean`
  (Stacks 00ML), with its Tor-vanishing and nilpotent-descent support.
* `Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim`,
  from `StacksFrontier/RingTheory/CohenMacaulay/RegularSequence/DimensionCriterion.lean`
  (Stacks 02JN), with its regular-sequence and depth dimension arguments.
* Identification of the source's regular-sequence depth with the
  Ext-based `IsLocalRing.depth` used in the statement below. Mathlib's
  `Ideal.depth_eq_sSup_length_isRegular` already expresses this depth as the supremum of the
  lengths of regular sequences in the ideal; what remains is to match the source's definition with
  that supremum.

The complete principal-ideal tensor injectivity lemma from the source
argument is ported in `MathlibExt/RingTheory/MiracleFlatness.lean`.

For universal compactified Jacobians with a nondegenerate stability parameter, flatness is
supplied by Kass–Pagani, Corollary 4.4. This module records the general local criterion. Applying
it to a further family requires identifying its stalk algebra maps and proving the displayed
dimension equality for those local rings.

## References

* The Stacks Project, Algebra, Lemma 00R4 (miracle flatness).
  https://stacks.math.columbia.edu/tag/00R4
* The public `AxiomMath/Stacks` interface and its precise revision are
  credited in the adaptation notice above.
* J. L. Kass and N. Pagani, *The stability space of compactified universal
  Jacobians*, Corollary 4.4. https://arxiv.org/abs/1707.02284v4
-/

namespace WantedExt.RingTheory.MiracleFlatnessWanted

/-- Miracle flatness for a local algebra over a regular local ring: if `R → S` is a local
homomorphism from a regular local ring `R` to a Noetherian local ring `S` that is Cohen–Macaulay
(`depth S = dim S`, with `S` as an `S`-module) and `dim S = dim R + dim (S ⧸ 𝔪_R S)`, then `S` is
flat over `R`. The closed fiber `S ⧸ 𝔪_R S` is formed using the same algebra map that defines
`Module.Flat R S`.
Source: The Stacks Project, Tag 00R4. -/
public theorem_wanted miracleFlatness
    (R S : Type*) [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hCM : (IsLocalRing.depth (ModuleCat.of S S) : WithBot ℕ∞) =
      ringKrullDim S)
    (hDim : ringKrullDim S = ringKrullDim R +
      ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map
        (algebraMap R S))) :
    Module.Flat R S

end WantedExt.RingTheory.MiracleFlatnessWanted
