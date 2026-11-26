# IND-CPA security of GSW from decision LWE

Consider GSW with a parameter family indexed by $\lambda$ (for example $k = \lambda + 1$, $n = k$, $w = 16 + 8\lceil \log_2 k \rceil$, $N = (n+1)w$, $m = N + 2\lambda$, centered-binomial LWE errors) satisfying the entropy margin $m \ge w(n+1) + 2\lambda$ and the fresh-decryption margin. If decision LWE holds for this family and error law, GSW is IND-CPA secure: every probabilistic polynomial-time adversary has advantage at most twice the advantage of an LWE distinguisher built from it plus $2N\sqrt{2^{w(n+1)}/2^m}$, which is negligible.

## Proof sketch

Replace the LWE public matrix by a uniform one (one LWE hop for each challenge bit) and apply statistical hiding.

## Depends on

- [The Gentry–Sahai–Waters (GSW) encryption scheme](gsw-scheme.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [GSW ciphertexts are statistically hiding under a uniform public matrix](gsw-statistical-hiding.md)

## Sources

- Craig Gentry, Amit Sahai and Brent Waters, "Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based", Advances in Cryptology – CRYPTO 2013, 2013.
