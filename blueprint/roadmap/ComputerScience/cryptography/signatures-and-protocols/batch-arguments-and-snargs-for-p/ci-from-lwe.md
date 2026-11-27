# Correlation intractability and NIZK for NP from LWE

Assuming the hardness of LWE (with polynomial modulus-to-noise ratio), there is a hash family that is correlation intractable for all efficiently searchable relations of bounded circuit size. Consequently the Fiat–Shamir transform applied to (a parallel-repeated, commit-and-open variant of) a public-coin zero-knowledge proof for an NP-complete language with a lossy/extractable commitment is sound, and non-interactive zero-knowledge arguments (in fact proofs, with appropriate commitments) for all of NP exist in the common reference string model from LWE.

## Proof sketch

The hash key is an FHE encryption of a circuit computing the searchable relation's bad-challenge function; hashing evaluates it homomorphically and outputs the ciphertext's decryption-relevant bits, so that a correlation would require predicting the encrypted function's output, contradicting LWE-based security through a lossiness argument. For commit-and-open protocols with extractable commitments, the bad challenge is efficiently computable from the commitment, so CI applies.

## Depends on

- [Correlation-intractable hash families](correlation-intractability.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Sources

- Chris Peikert, Sina Shiehian, "Noninteractive Zero Knowledge for NP from (Plain) Learning With Errors", CRYPTO (2019).
- Ran Canetti, Yilei Chen, Justin Holmgren, Alex Lombardi, Guy N. Rothblum, Ron D. Rothblum, Daniel Wichs, "Fiat-Shamir: From Practice to Theory", STOC (2019).
