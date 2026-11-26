# FHEW: bootstrapping LWE ciphertexts with a ring-GSW accumulator

There is an LWE-based fully homomorphic encryption scheme (FHEW) evaluating a homomorphic NAND followed by bootstrapping in which the accumulator is a ring-GSW ciphertext over $\mathbb{Z}_Q[X]/(X^{N}+1)$ updated by homomorphic multiplications by encrypted monomials $X^{a_is_i}$ (or by additions in the exponent), followed by extraction and key and modulus switching. Its security relies on Ring-LWE/LWE and circular security of the bootstrapping keys, and its error growth during bootstrapping is additive (quasi-linear) in the number of accumulator updates.

## Proof sketch

Use GSW-style ciphertexts whose multiplication grows noise asymmetrically: multiplying a fresh-noise GSW encryption of a monomial into the accumulator adds noise proportional to the fresh noise, not the accumulator's. Encoding the decryption equation in the exponent of $X$ (a cyclic group of order $2N$) makes the accumulator compute the phase homomorphically; a final extraction reads the most significant bit.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Noise of the TRGSW–TRLWE external product](external-product-noise.md)
- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)

## Sources

- Léo Ducas, Daniele Micciancio, "FHEW: Bootstrapping Homomorphic Encryption in Less than a Second", EUROCRYPT (2015), IACR ePrint 2014/816.
- Jacob Alperin-Sheriff, Chris Peikert, "Faster Bootstrapping with Polynomial Error", CRYPTO (2014).
