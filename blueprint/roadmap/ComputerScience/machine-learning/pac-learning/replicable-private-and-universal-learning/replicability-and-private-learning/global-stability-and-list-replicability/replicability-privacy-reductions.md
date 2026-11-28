# Sample-efficient reductions between replicability and approximate differential privacy

Let $T$ be a statistical task (solved from i.i.d. samples, success measured with failure probability).

- **Replicability to privacy.** If a $0.01$-replicable algorithm solves $T$ with $n_R$ samples and failure probability $\beta$, then for all $0 < \varepsilon, \delta \le 1$ an $(\varepsilon,\delta)$-differentially private algorithm solves $T$ with failure probability $O(\beta \log(1/\beta))$ using $n_R \cdot O\big(\log(1/\delta)\log(1/\beta)/\varepsilon + \log^2(1/\beta)\big)$ samples.
- **Privacy to replicability.** If $\rho \in (0,1)$ is sufficiently small and $A$ on $m$ samples is $(\varepsilon,\delta)$-differentially private with finite output space, $\varepsilon = \rho/\sqrt{8 m \log(1/\rho)}$ and $\delta \le \varepsilon\rho^6/m^2$, then running $A$ through correlated sampling against its own output distribution is $O(\rho)$-replicable and leaves the output distribution on every fixed dataset unchanged. Combined with privacy amplification by subsampling, this gives, for constant replicability: there are absolute constants $c, K > 0$ such that if a $(0.1, c/n^3)$-differentially private algorithm with finite output space solves $T$ with $n$ samples and failure probability $\beta$, then a $c$-replicable algorithm solves $T$ with $K n^2$ samples and failure probability $\beta$. Composing with the first reduction, for all $\varepsilon, \delta > 0$ an $(\varepsilon, \delta)$-differentially private algorithm solves $T$ with failure probability $O(\beta\log(1/\beta))$ using $O\big(\log(1/\delta)\log(1/\beta)/\varepsilon + \log^2(1/\beta)\big) \cdot n^2$ samples.
- **Computational separation.** Assuming public-key encryption with a randomizable ciphertext structure, there is a statistical task solvable efficiently under differential privacy but not efficiently replicably, and any such separation implies the existence of one-way functions.

These reductions yield sample-efficient replicable algorithms for PAC learning, distribution estimation and testing, amplification of $\delta$ in approximate privacy, and conversions from item-level to user-level privacy.

## Proof sketch

Replicability to privacy: draw $k_1 = O(\log(1/\beta))$ random seeds and, for each seed, run the replicable algorithm with that same seed on many independent disjoint blocks of the sample (about $(\log(1/\delta)/\varepsilon + \log(1/\beta))$ blocks per seed). Reusing a seed across blocks is what creates a heavy output: for a good seed, replicability makes one canonical output appear in most of that seed's runs, whereas runs with fresh seeds need not agree. Private selection of an approximate mode (stable histograms) then outputs a heavy element with privacy, since neighbouring samples change only one block's output. Privacy to replicability: a private algorithm with small $\varepsilon$ is perfectly generalizing, so its output distribution on a random sample is close in total variation to a sample-independent simulator distribution; correlated sampling of two such nearby distributions agrees with high probability. For the constant-replicability form, running the private algorithm on a random subsample of $n$ out of $m = Kn^2$ samples is $(1/\sqrt{Km}, cK/m^2)$-differentially private and has the same output distribution on i.i.d. data, so the correlated-sampling step applies with a small constant $\rho$. The cryptographic separation uses a ciphertext-identification problem where private algorithms can output a fresh re-randomized ciphertext, but replicability would require a canonical decryption.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)
- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Public-key encryption scheme](../../../../../cryptography/security-games/generic-security-games/pkescheme.md)
- [One-way function families](../../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Transfer theorem for adaptive data analysis](../../../../../cryptography/differential-privacy/differentially-private-transfer.md)

## Sources

- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921, Theorem 3.1 and Algorithm 1, Corollary 3.18, Theorems 6.1 and 6.2 and their proofs, Sections 1.1.1, 1.1.2, 4 and 6.
