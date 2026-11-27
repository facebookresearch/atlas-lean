# Next-bit unpredictability of a generator

Let $G$ be a deterministic generator mapping $n$-bit seeds to $\ell(n)$-bit outputs. A *next-bit predictor* is a probabilistic algorithm $P$ that receives $1^n$, an index $i < \ell(n)$ and the prefix $y_1 \cdots y_i$ of $y = G(s)$ for a uniform seed $s$, and outputs a guess for $y_{i+1}$. Its prediction advantage at $(n, i)$ is

$$\mathrm{NBadv}_P(n, i) = \Pr_{s}\bigl[P(1^n, i, G(s)_{1..i}) = G(s)_{i+1}\bigr] - \tfrac{1}{2}.$$

$G$ is *unpredictable* if for every probabilistic polynomial-time predictor $P$ the quantity $\max_{i < \ell(n)} |\mathrm{NBadv}_P(n, i)|$ is negligible.

## Depends on

- [Probabilistic polynomial-time Turing machines](../asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
- M. Blum and S. Micali, "How to Generate Cryptographically Strong Sequences of Pseudo-Random Bits", SIAM Journal on Computing 13(4), 1984.
