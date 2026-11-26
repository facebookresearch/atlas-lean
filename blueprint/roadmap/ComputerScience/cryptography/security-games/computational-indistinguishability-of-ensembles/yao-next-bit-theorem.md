# Yao's next-bit theorem: a generator is pseudorandom iff it is unpredictable

Let $G$ be a deterministic polynomial-time generator with output length $\ell(n) > n$, $\ell$ polynomially bounded. Then $G$ is a secure pseudorandom generator against probabilistic polynomial-time tests if and only if it is next-bit unpredictable. Concretely, every test $D$ yields a predictor $P$ (which on index $i$ runs the predictor $P_i$ of the positional sum bound) with

$$\mathrm{PRGadv}(D, G) \le \ell(n) \cdot \max_{i < \ell(n)} |\mathrm{NBadv}_P(n, i)|,$$

and every predictor yields a test with equal advantage.

## Proof sketch

Unpredictability follows from security by part (a) of the predictor–distinguisher correspondence. Conversely, the predictor that samples $i$ uniformly from $\{0,\dots,\ell-1\}$ and runs $P_i$ from part (b) has advantage at least $\mathrm{PRGadv}(D,G)/\ell(n)$, which is non-negligible whenever $D$'s advantage is.

## Depends on

- [Next-bit unpredictability of a generator](next-bit-unpredictability.md)
- [Asymptotic PRG security relative to a class of distinguishers](../../symmetric-key/pseudorandom-generators/prgsecure.md)

## Proof depends on

- [Next-bit predictors and distinguishers: exact transfer and the positional sum bound](predictor-distinguisher-correspondence.md)

## Sources

- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
