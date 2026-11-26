# Correctness of refresh and NAND refresh

Suppose $\mathcal{E}$ correctly evaluates its decryption circuit and its NAND-augmented decryption circuit on fresh encryptions. Then for every key pair $(pk_1, sk_1)$, every well-sized ciphertext $c$ (fresh or the output of an earlier evaluation) and every honest encryption $\overline{sk_1}$ of $sk_1$ under $pk_2$, $\mathrm{Dec}(sk_2, \mathrm{Refresh}(pk_2, \overline{sk_1}, c)) = \mathrm{Dec}(sk_1, c)$, and NAND refresh decrypts to $\neg(\mathrm{Dec}(sk_1, c) \wedge \mathrm{Dec}(sk_1, c'))$. The output has the same width as a base ciphertext. If encryption, evaluation and the decryption-circuit generator run in (strict) probabilistic polynomial time, so do refresh and NAND refresh.

## Proof sketch

The inputs to the homomorphic evaluation are fresh encryptions of the bits of $sk_1$ and of $c$, and the evaluated circuit outputs $\mathrm{Dec}(sk_1, c)$ on those plaintexts; correctness of evaluation on fresh inputs transfers this to the plaintext of the result, with no hypothesis on how $c$ itself was produced.

## Depends on

- [Gentry's refresh (recryption) algorithm](refresh-algorithm.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
