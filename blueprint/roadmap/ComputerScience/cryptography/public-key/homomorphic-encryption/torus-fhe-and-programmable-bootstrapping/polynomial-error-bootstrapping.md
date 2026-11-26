# Bootstrapping with polynomial error and FHE from LWE with polynomial approximation factors

Assuming LWE with a polynomial modulus-to-noise ratio (implied, via Regev's quantum reduction, by the worst-case hardness of lattice problems with polynomial approximation factors), there is a bootstrappable homomorphic encryption scheme whose bootstrapping procedure, implemented by GSW-style accumulators performing the decryption arithmetic in a cyclic group (permutation matrices or monomials), incurs only polynomial (in fact quasi-linear in the security parameter) error growth. Consequently, assuming in addition circular security, fully homomorphic encryption exists based on LWE with polynomial approximation factors.

## Proof sketch

Represent the decryption's inner product modulo $q$ as a composition of group elements in $\mathbb{Z}_q$ embedded as permutation matrices encrypted with GSW; products of GSW ciphertexts in a fixed left-to-right order accumulate error additively. Rounding the final value uses a small lookup, keeping the overall error polynomial.

## Depends on

- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [FHEW: bootstrapping LWE ciphertexts with a ring-GSW accumulator](fhew-bootstrapping.md)
- [Regev's quantum worst-case to average-case reduction for LWE](../../isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/regev-worst-case-reduction.md)

## Sources

- Jacob Alperin-Sheriff, Chris Peikert, "Faster Bootstrapping with Polynomial Error", CRYPTO (2014).
- Craig Gentry, Amit Sahai, Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", CRYPTO (2013).
