/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The local miracle flatness interface is adapted from
`StacksFrontier/RingTheory/Flat/MiracleFlatness.lean` in `AxiomMath/Stacks`
at commit c496df0d9beea9deaeabcea8492605f9a0a2313b:
https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/RingTheory/Flat/MiracleFlatness.lean

That repository is distributed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The source file does not
identify individual authors or contain a copyright notice.

Modification notice: recorded the local criterion as `theorem_wanted` and
expanded `Module.IsMaximalCohenMacaulay S S` to the depth equality expressed
using Mathlib's `IsLocalRing.depth` and `ringKrullDim`.
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

For the calibration application, flatness of the universal compactified
Jacobian is already available externally from KP, Corollary 4.4. This
module records the general local criterion. Applying it to a further
family requires identifying its stalk algebra maps and proving the
displayed dimension equality for those local rings.

## References

* The Stacks Project, Algebra, Lemma 00R4 (miracle flatness).
  https://stacks.math.columbia.edu/tag/00R4
* The public `AxiomMath/Stacks` interface and its precise revision are
  credited in the adaptation notice above.
* J. L. Kass and N. Pagani, *The stability space of compactified universal
  Jacobians*, Corollary 4.4. https://arxiv.org/abs/1707.02284v4
-/

namespace WantedExt.RingTheory.MiracleFlatnessWanted

/-- Miracle flatness for a local algebra over a regular local ring.
The depth condition uses `S` as an `S`-module, and the closed fiber is
formed using the same algebra map that defines `Module.Flat R S`.
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
