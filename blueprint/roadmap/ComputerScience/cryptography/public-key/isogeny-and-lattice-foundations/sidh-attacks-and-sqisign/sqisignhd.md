# SQIsignHD: SQIsign with higher-dimensional response representation

Representing the response isogeny $\sigma:E_A\to E_2$ of arbitrary (non-smooth) degree by its action on $2^{e}$-torsion, verified via a dimension-$4$ (FastSQIsignHD) or dimension-$8$ (RigorousSQIsignHD) isogeny chain obtained from Kani's lemma, yields a variant of SQIsign (SQIsignHD) in which the response can be computed without the expensive conversion to $2$-power norm ideals and in which the response distribution is uniform over isogenies of a given degree class. The resulting signature scheme is universally unforgeable under chosen-message attacks in the random oracle model, assuming that the supersingular endomorphism problem remains hard for adversaries with access to an oracle sampling random isogenies of non-smooth degree from a given curve (unconditionally given this assumption for RigorousSQIsignHD, and under additional heuristics for FastSQIsignHD).

## Proof sketch

The signer samples a random equivalent ideal of suitable (not necessarily smooth) norm, which by the Deuring correspondence gives an isogeny of that degree with a uniform-looking distribution, and outputs its torsion images. The verifier applies the higher-dimensional representation lemma to check the isogeny. Simulation is easier because uniform responses can be generated from the statement alone given a sampling algorithm, which yields the cleaner reduction.

## Depends on

- [SQIsign: compact signatures from the SQIsign identification protocol](sqisign-signature.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)
- [The SQIsign identification protocol](sqisign-identification.md)

## Proof depends on

- [Higher-dimensional representations of isogenies of arbitrary degree](hd-isogeny-representation.md)

## Sources

- Pierrick Dartois, Antonin Leroux, Damien Robert, Benjamin Wesolowski, "SQIsignHD: New Dimensions in Cryptography", EUROCRYPT (2024), IACR ePrint 2023/436.
