/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.ArtinMap
import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusRestriction

/-!
# Restriction of the Artin map (ATLAS N402, Stages C3 and final)

This file ports frozen ATLAS source declarations
`prop_7_22_artinMap_at_prime` at source lines `755--771` and
`proposition_21_1_artin_commutes` at source lines `773--801` in
[`RayClassFields.lean` at commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L755-L771)
and
[`RayClassFields.lean` at commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L773-L801):
in a tower `M / L / K`, restriction of the `M`-Artin map agrees with the
`L`-Artin map.

## Source-to-API mapping

Source declaration `prop_7_22_artinMap_at_prime` at source lines `755--771`
maps to public API
`Modulus.restrictNormalHom_artinMap_primeCoprimeUnit`.

Frozen source declaration `proposition_21_1_artin_commutes`, lines `773--801`,
maps to `Modulus.restrictNormalHom_comp_artinMap`.

Both abelian hypotheses are required by the two public Artin maps: the `M`
Artin map needs `[IsAbelianGalois K M]` and the `L` Artin map needs
`[IsAbelianGalois K L]`. The explicit `hL` and `hM` are the repaired
unramified-domain certificates consumed by the two public Artin maps.
`hL` corresponds to source `hdiv`, while `hM` is the deliberate additional
repaired assumption required by the honest upper Artin map; exact hypothesis
parity with the source is not claimed, and no unrelated ray class field
results are claimed here.

The bundled hom equality `Modulus.restrictNormalHom_comp_artinMap` is
an equivalent bundled, more reusable form of ATLAS's universally quantified
pointwise theorem: they are extensionally equivalent, and the pointwise
statement for any coprime ideal follows by `DFunLike.congr_fun`.
-/

@[expose] public noncomputable section

namespace NumberField
namespace Modulus

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsAbelianGalois K L] [IsAbelianGalois K M]

/-- **Restriction of the Artin map at a prime.** Let $K \subseteq L \subseteq M$ be a tower of
number fields with $L/K$ and $M/K$ abelian Galois, and let $\mathfrak m$ be a modulus of $K$ with
finite part $\mathfrak m_0$ such that every prime of $\mathcal O_K$ not dividing $\mathfrak m_0$
is unramified in $L$ and in $M$. For every prime $\mathfrak p$ of $\mathcal O_K$ not dividing
$\mathfrak m_0$, restricting to $L$ the image of $\mathfrak p$ under the Artin map of $M/K$ gives
the image of $\mathfrak p$ under the Artin map of $L/K$. -/
theorem restrictNormalHom_artinMap_primeCoprimeUnit
    (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvm : ¬ m.finiteSupported v) :
    AlgEquiv.restrictNormalHom L
        (m.artinMap (L := M) hM (m.primeCoprimeUnit v hvm)) =
      m.artinMap (L := L) hL (m.primeCoprimeUnit v hvm) := by
  rw [m.artinMap_primeCoprimeUnit (L := M) hM v hvm,
    m.artinMap_primeCoprimeUnit (L := L) hL v hvm]
  exact m.restrictNormalHom_frobeniusAtCoprimePrime
    (L := L) (M := M) hL hM ⟨v, hvm⟩

/-- **The Artin map commutes with restriction.** Let $K \subseteq L \subseteq M$ be a tower of
number fields with $L/K$ and $M/K$ abelian Galois, and let $\mathfrak m$ be a modulus of $K$
with finite part $\mathfrak m_0$ such that every prime of $\mathcal O_K$ not dividing
$\mathfrak m_0$ is unramified in $L$ and in $M$. Then the Artin map of $M/K$ followed by
restriction $\mathrm{Gal}(M/K) \to \mathrm{Gal}(L/K)$ equals the Artin map of $L/K$, as
homomorphisms from the group of fractional ideals of $K$ coprime to $\mathfrak m_0$ to
$\mathrm{Gal}(L/K)$. -/
theorem restrictNormalHom_comp_artinMap
    (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M) :
    (AlgEquiv.restrictNormalHom L).comp (m.artinMap (L := M) hM) =
      m.artinMap (L := L) hL := by
  apply (MonoidHom.cancel_right m.freeGroupToCoprime_surjective).mp
  apply FreeGroup.ext_hom
  intro p
  simpa only [MonoidHom.comp_apply, m.freeGroupToCoprime_of] using
    m.restrictNormalHom_artinMap_primeCoprimeUnit
      (L := L) (M := M) hL hM p.val p.property

end Modulus

end NumberField
