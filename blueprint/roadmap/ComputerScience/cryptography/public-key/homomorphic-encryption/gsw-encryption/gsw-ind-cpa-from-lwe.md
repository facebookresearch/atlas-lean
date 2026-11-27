# IND-CPA security of GSW from decision LWE

Consider GSW with modulus $q = 2^w$, LWE dimension $n$, error distribution $\chi$, $N = (n+1)w$ and $m > 2n\log_2 q = 2nw$ (Gentry, Sahai and Waters, Section 3.2, Lemma 1, following Regev). If decision LWE holds for $(n, q, \chi)$, then the public matrix $A$ together with $R \cdot A$ for uniform $R \in \{0,1\}^{N \times m}$ is computationally indistinguishable from uniform, and GSW is IND-CPA secure: the advantage of every probabilistic polynomial-time adversary is bounded by the advantage of an LWE distinguisher built from it plus the leftover-hash-lemma distance of $R \cdot A$ from uniform, which is negligible.

## Proof sketch

Replace the LWE public matrix by a uniform one (one LWE hop); then $R \cdot A$ is statistically close to uniform by the leftover hash lemma, so the ciphertext is statistically independent of the message.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [GSW ciphertexts are statistically hiding under a uniform public matrix](gsw-statistical-hiding.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
