# GSW is bootstrappable and yields leveled FHE from LWE

At the logarithmic-depth parameter family ($t = 1 + \lceil\log_2(\lambda+2)\rceil$, $w = 16384 t^2$, $L = 512 t$), GSW evaluates its own decryption circuit and its NAND-augmented decryption circuit within the depth budget, so it is bootstrappable for the identity and NAND gates; its secret keys, fresh ciphertexts and evaluation outputs have fixed widths, and evaluation of every permitted circuit is perfectly correct. Consequently, under decision LWE for this family, Gentry's bootstrapping construction instantiated with GSW is a leveled fully homomorphic encryption scheme that is correct, compact and IND-CPA secure, with an explicit concrete bound in terms of the LWE advantage and the statistical hiding error; under an additional circular-security assumption it is fully homomorphic.

## Proof sketch

The decryption circuit has depth $O(\log n + \log w) = O(t)$, which fits the budget $L = 512t$ with room for the NAND gate; then apply the leveled bootstrapping theorem with GSW's IND-CPA security.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)
- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [GSW evaluates Boolean circuits of bounded depth](gsw-circuit-evaluation.md)
- [GSW decryption has logarithmic-depth circuits](gsw-decryption-circuit.md)
- [IND-CPA security of GSW from decision LWE](gsw-ind-cpa-from-lwe.md)
- [Bootstrapping gives leveled fully homomorphic encryption](../bootstrapping-constructions/leveled-fhe-from-bootstrapping.md)
- [Fully homomorphic encryption from a circular-secure bootstrappable scheme](../bootstrapping-constructions/fhe-from-circular-security.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
