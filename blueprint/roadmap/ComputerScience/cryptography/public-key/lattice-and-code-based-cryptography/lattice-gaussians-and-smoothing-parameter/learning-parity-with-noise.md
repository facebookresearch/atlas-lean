# Learning parity with noise

For dimension $n$ and noise rate $\tau \in (0, 1/2)$, the *learning parity with noise* (LPN) distribution for a secret $s \in \mathbb{F}_2^n$ outputs samples $(a, \langle a, s\rangle + e)$ with $a$ uniform in $\mathbb{F}_2^n$ and $e$ Bernoulli($\tau$). *Search LPN* asks to recover $s$ from polynomially many samples; *decision LPN* asks to distinguish them from uniform pairs. LPN is LWE over $\mathbb{Z}_2$ with Bernoulli noise; the *error-secret* variant draws $s$ from the noise distribution as well.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- A. Blum, M. Furst, M. Kearns and R. J. Lipton, "Cryptographic Primitives Based on Hard Learning Problems", Advances in Cryptology (CRYPTO 1993), LNCS 773, 1994.
- C. Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science 10(4), 2016.
