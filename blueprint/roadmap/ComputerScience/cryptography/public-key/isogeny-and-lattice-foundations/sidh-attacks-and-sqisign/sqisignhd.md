# SQIsignHD: SQIsign with higher-dimensional response representation

Representing the response isogeny $\sigma:E_A\to E_2$ of arbitrary (non-smooth) degree by its action on $2^{e}$-torsion, verified via a higher-dimensional (dimension $4$, or $2$ in later optimizations) isogeny chain obtained from Kani's lemma, yields a variant of SQIsign (SQIsignHD) in which the response can be computed without the expensive conversion to $2$-power norm ideals and in which the response distribution is uniform over isogenies of a given degree class. This gives significantly faster signing, smaller signatures, and a security reduction (in the random oracle model) to the one-endomorphism (or endomorphism ring) problem, with heavier verification due to higher-dimensional isogeny computations.

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
