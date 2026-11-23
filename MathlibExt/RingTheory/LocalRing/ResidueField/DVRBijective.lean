/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.ResidueField.DVRFull

/-!
# Bijections on residue-field morphisms for local DVR extensions

This module integrates the separate faithfulness and fullness stages.

Source map: ATLAS NumberTheoryI item N211, Theorem 10.13 (Section 10.2).
All links below pin atlas-lean revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`. English target:
[`v1/Atlas/NumberTheoryI/targets.yaml` (lines 1466-1483)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1466-L1483):
morphism
formula (lines 1470-1475), isomorphism-class consequence (lines 1476-1477), and
Hom-set bijection (lines 1478-1480).
Implementation:
[`v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean):
[`residueFieldFunctorAlg` (lines 1001-1011)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1001-L1011)
defines the induced residue-field map;
[`residueFieldFunctor_full_faithfulness` (lines 1013-1165)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1013-L1165)
proves the Hom-set bijection;
[equivalence lift (lines 1220-1303)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1220-L1303)
with forward and inverse lifts
(lines 1225-1229), residue identities (lines 1234-1238), inverse laws
(lines 1240-1288), and resulting algebra equivalence (lines 1290-1303);
[`residueFieldFunctor_isEquivalence` (lines 1320-1338)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean#L1320-L1338)
packages full faithfulness,
essential surjectivity, and equivalence lifting.

`DVRResidue.residueFieldMapAlgHom_bijective` formalizes the Hom-set bijection by
combining `residueFieldMapAlgHom_injective` and `residueFieldMapAlgHom_surjective`.
Only target `C` needs `HenselianLocalRing` here: fullness lifts roots into `C`,
while injectivity uses the source's `Algebra.Etale A B`, hence formally-unramified,
structure.

`DVRResidue.exists_algEquiv_lift_residueField` formalizes the isomorphism-lifting
clause. Both `B` and `C` are étale and Henselian because fullness is used for both
`e` and `e.symm`; faithfulness then proves the lifted maps are inverse. The two
returned equalities for `e'.toAlgHom` and `e'.symm.toAlgHom` are the forward and
inverse versions of the source formula saying reduction after a lifted map equals
the residue-field map.

ATLAS derives Henselianity from maximal-ideal-adic completeness of its valuation
rings; this reusable layer assumes those Henselian structures explicitly. It does
not establish the complete-DVR bridge, essential surjectivity on objects,
finiteness of Hom sets, or a categorical equivalence.
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

/-- **Algebra maps from an étale DVR extension into a Henselian one match residue-field maps.**
Let $A$, $B$, $C$ be discrete valuation rings, with $B$ and $C$ finite $A$-algebras whose structure
maps are local homomorphisms, $B$ étale over $A$, and $C$ a Henselian local ring. Write
$\kappa(R)$ for the residue field of a local ring $R$. Then sending an $A$-algebra homomorphism
$B \to C$ to the $\kappa(A)$-algebra homomorphism $\kappa(B) \to \kappa(C)$ it induces is a
bijection. -/
theorem residueFieldMapAlgHom_bijective
    [Algebra.Etale A B] [HenselianLocalRing C] :
    Function.Bijective
      (residueFieldMapAlgHom (A := A) (B := B) (C := C)) :=
  ⟨residueFieldMapAlgHom_injective, residueFieldMapAlgHom_surjective⟩

/-- **Lifting residue-field isomorphisms between Henselian étale DVR extensions.** Let $A$, $B$,
$C$ be discrete valuation rings, with $B$ and $C$ finite $A$-algebras whose structure maps are local
homomorphisms, both étale over $A$ and both Henselian local rings. Write $\kappa(R)$ for the
residue field of a local ring $R$. Then every $\kappa(A)$-algebra isomorphism
$e \colon \kappa(B) \to \kappa(C)$ lifts to an $A$-algebra isomorphism $e' \colon B \to C$: the
map that $e'$ induces on residue fields is $e$, and the map that $e'^{-1}$ induces is $e^{-1}$. -/
theorem exists_algEquiv_lift_residueField
    [Algebra.Etale A B] [Algebra.Etale A C]
    [HenselianLocalRing B] [HenselianLocalRing C]
    (e : IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField C) :
    ∃ e' : B ≃ₐ[A] C,
      residueFieldMapAlgHom e'.toAlgHom = e.toAlgHom ∧
      residueFieldMapAlgHom e'.symm.toAlgHom = e.symm.toAlgHom := by
  obtain ⟨f, hf⟩ :=
    residueFieldMapAlgHom_surjective (A := A) (B := B) (C := C) e.toAlgHom
  obtain ⟨g, hg⟩ :=
    residueFieldMapAlgHom_surjective (A := A) (B := C) (C := B) e.symm.toAlgHom
  have hfg : f.comp g = AlgHom.id A C := by
    apply residueFieldMapAlgHom_injective (A := A) (B := C) (C := C)
    rw [residueFieldMapAlgHom_comp, hf, hg, residueFieldMapAlgHom_id]
    ext x
    simp
  have hgf : g.comp f = AlgHom.id A B := by
    apply residueFieldMapAlgHom_injective (A := A) (B := B) (C := B)
    rw [residueFieldMapAlgHom_comp, hf, hg, residueFieldMapAlgHom_id]
    ext x
    simp
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, ?_, ?_⟩
  · exact hf
  · change residueFieldMapAlgHom g = e.symm.toAlgHom
    exact hg

end DVRResidue
