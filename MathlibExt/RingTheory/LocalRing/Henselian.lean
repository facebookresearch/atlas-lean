/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Henselian

@[expose] public section

/-!
# Henselianity from maximal-adic completeness

A local ring that is complete for its maximal-ideal adic topology satisfies
Hensel's lemma, hence is a Henselian local ring.

Source map: prerequisite for ATLAS NumberTheoryI item N211, Theorem 10.13
(Section 10.2), at atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, whose
[English target is N211 / Theorem 10.13, lines 1466-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483).
That target assumes a complete DVR
and builds the equivalence for unramified extensions.

The implementation source is
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean):
[`dvr_extension_henselian` (lines 988-999)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L988-L999)
turns maximal-ideal-adic completeness
of an extension DVR into `HenselianLocalRing` by invoking Mathlib's
`IsAdicComplete.henselianRing` and mapping the derivative-unit condition through
the residue quotient. `residueFieldFunctor_full_faithfulness` uses that instance
at [line 1019](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1019)
before its Hensel-lifting argument.
[`residueFieldFunctor_isEquivalence` (lines 1320-1338)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338)
is the eventual N211 package.

`HenselianLocalRing.of_isAdicComplete_maximalIdeal` corresponds to
`dvr_extension_henselian` and supplies the Henselian instance used by the later
fullness/equivalence stages.

The reusable theorem intentionally generalizes the source helper: it requires only
`CommRing R`, `IsLocalRing R`, and maximal-ideal-adic completeness. It removes
the source helper's `IsDomain` and `IsDiscreteValuationRing` assumptions, retaining
their needed `IsLocalRing` consequence, and extracts the result from its
extension-specific context because neither `IsAdicComplete.henselianRing` nor
the quotient-unit conversion uses them.

The conclusion is exactly `HenselianLocalRing R`; the proof maps the derivative's
unit property into the residue quotient before applying the Mathlib Hensel theorem.

This is only a prerequisite stage, not the full N211 theorem: it does not construct
residue-field morphisms, prove full faithfulness or essential surjectivity, lift
equivalences, or establish a category equivalence.
-/

/-- **Complete local rings are Henselian.** Let $R$ be a local ring with maximal ideal
$\mathfrak m$. If $R$ is Hausdorff and complete for the $\mathfrak m$-adic topology, then $R$
is a Henselian local ring. -/
theorem HenselianLocalRing.of_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R := by
  have hH := IsAdicComplete.henselianRing R (IsLocalRing.maximalIdeal R)
  exact {
    is_henselian := fun f hf a0 hroot hderiv => by
      have hderiv' : IsUnit
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
            (Polynomial.eval a0 (Polynomial.derivative f))) :=
        hderiv.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
      exact hH.is_henselian f hf a0 hroot hderiv'
  }
