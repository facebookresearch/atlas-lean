/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ResidueField.DVRBijective
public import MathlibExt.RingTheory.LocalRing.Henselian

/-!
# Complete-DVR wrappers for the residue-field Hom bijection

Source map: ATLAS NumberTheoryI item N211, Theorem 10.13 (Section 10.2).
All links below pin atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`. English target:
[`v1/Atlas/NumberTheoryI/targets.yaml`, N211 / Theorem 10.13, lines
1466-1483](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483):
assumes a complete DVR and asserts the residue-field
functor's Hom-set bijection and isomorphism-class consequences for finite
unramified extensions.
Implementation:
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean):
[`dvr_extension_henselian` (lines 988-999)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L988-L999)
obtains a Henselian local ring
from maximal-ideal-adic completeness, installed for the target at line 1019
before Hensel lifting;
[`residueFieldFunctor_full_faithfulness` (lines 1013-1165)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1013-L1165)
proves the Hom-set bijection; the equivalence lift is constructed at
[lines 1220-1303](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1220-L1303);
[`residueFieldFunctor_isEquivalence` (lines 1320-1338)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338)
packages the eventual theorem.

This module imports the N211 bijectivity/equivalence layer (`DVRBijective`)
and the separately extracted completeness-to-Henselian bridge (`Henselian`).

`DVRResidue.residueFieldMapAlgHom_bijective_of_isAdicComplete` replaces the
explicit target `HenselianLocalRing C` assumption of
`residueFieldMapAlgHom_bijective` by maximal-ideal-adic completeness of the
target DVR. It yields existence and uniqueness of lifts of residue-field
algebra homomorphisms through bijectivity.

`DVRResidue.exists_algEquiv_lift_residueField_of_isAdicComplete` replaces
explicit Henselian assumptions on both `B` and `C` by their
maximal-ideal-adic completeness and returns an `A`-algebra equivalence whose
forward and inverse residue maps equal the supplied residue-field equivalence
and its inverse.

These are the ring-level complete-DVR wrappers for the Hom-bijection and
isomorphism-lifting clauses. `Algebra.Etale A B` / `Algebra.Etale A C` are
the reusable unramified interfaces used here.

This remains a prerequisite stage, not the full N211 target: it does not
derive étaleness from ATLAS's source-facing residue-separability/degree
hypotheses, construct every finite separable residue extension, prove finite
Hom sets, or establish a categorical equivalence.
-/

@[expose] public section

variable {A B C : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra A C]
variable [Module.Finite A B] [Module.Finite A C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]

namespace DVRResidue

/-- **Algebra maps from an étale DVR extension into a complete one match residue-field maps.**
Let $A$, $B$, $C$ be discrete valuation rings, with $B$ and $C$ finite $A$-algebras whose structure
maps are local homomorphisms, $B$ étale over $A$, and $C$ complete and separated for its
maximal-ideal-adic topology. Write $\kappa(R)$ for the residue field of a local ring $R$. Then
sending an $A$-algebra homomorphism $B \to C$ to the $\kappa(A)$-algebra homomorphism
$\kappa(B) \to \kappa(C)$ it induces is a bijection. -/
theorem residueFieldMapAlgHom_bijective_of_isAdicComplete
    [Algebra.Etale A B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C] :
    Function.Bijective
      (residueFieldMapAlgHom (A := A) (B := B) (C := C)) := by
  let : HenselianLocalRing C :=
    HenselianLocalRing.of_isAdicComplete_maximalIdeal C
  exact residueFieldMapAlgHom_bijective

/-- **Lifting residue-field isomorphisms between complete étale DVR extensions.** Let $A$, $B$, $C$
be discrete valuation rings, with $B$ and $C$ finite $A$-algebras whose structure maps are local
homomorphisms, both étale over $A$, and both complete and separated for their maximal-ideal-adic
topologies. Write $\kappa(R)$ for the residue field of a local ring $R$. Then every
$\kappa(A)$-algebra isomorphism $e \colon \kappa(B) \to \kappa(C)$ lifts to an $A$-algebra
isomorphism $e' \colon B \to C$: the map that $e'$ induces on residue fields is $e$, and the map
that $e'^{-1}$ induces is $e^{-1}$. -/
theorem exists_algEquiv_lift_residueField_of_isAdicComplete
    [Algebra.Etale A B] [Algebra.Etale A C]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    ∃ e' : B ≃ₐ[A] C,
      residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
      residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom := by
  let : HenselianLocalRing B :=
    HenselianLocalRing.of_isAdicComplete_maximalIdeal B
  let : HenselianLocalRing C :=
    HenselianLocalRing.of_isAdicComplete_maximalIdeal C
  exact exists_algEquiv_lift_residueField e

end DVRResidue
