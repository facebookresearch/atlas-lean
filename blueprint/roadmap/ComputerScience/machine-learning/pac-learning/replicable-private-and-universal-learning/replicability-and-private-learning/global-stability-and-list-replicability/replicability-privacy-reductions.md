# Sample-efficient reductions between replicability and approximate differential privacy

Let $T$ be a statistical task (solved from i.i.d. samples, success measured with failure probability).

- **Replicability to privacy.** If a $0.01$-replicable algorithm solves $T$ with $n_R$ samples and failure probability $\beta$, then for all $0 < \varepsilon, \delta \le 1$ an $(\varepsilon,\delta)$-differentially private algorithm solves $T$ with failure probability $O(\beta \log(1/\beta))$ using $n_R \cdot O\big(\log(1/\delta)\log(1/\beta)/\varepsilon + \log^2(1/\beta)\big)$ samples.
- **Privacy to replicability.** If $A$ on $m$ samples is $(\varepsilon,\delta)$-differentially private with finite output space, $\varepsilon = \rho/\sqrt{8 m \log(1/\rho)}$ and $\delta$ polynomially small in $\rho/m$, then running $A$ through correlated sampling against its own output distribution is $O(\rho)$-replicable and leaves the output distribution on every fixed dataset unchanged; combined with privacy amplification by subsampling, an $(\varepsilon_0, \delta)$-differentially private algorithm with constant $\varepsilon_0$ on $m$ samples and suitably small $\delta$ yields an $O(\rho)$-replicable algorithm on $\tilde O(m^2/\rho^2)$ samples.
- **Computational separation.** Assuming public-key encryption with a randomizable ciphertext structure, there is a statistical task solvable efficiently under differential privacy but not efficiently replicably, and any such separation implies the existence of one-way functions.

These reductions yield sample-efficient replicable algorithms for PAC learning, distribution estimation and testing, amplification of $\delta$ in approximate privacy, and conversions from item-level to user-level privacy.

## Proof sketch

Replicability to privacy: run the replicable algorithm on many disjoint subsamples with independent shared seeds; for a good seed, one canonical output appears in most runs, and private selection of the mode (stable histograms) outputs it with privacy. Privacy to replicability: a private algorithm with small $\varepsilon$ is perfectly generalizing, so its output distribution on a random sample is close in total variation to a sample-independent simulator distribution; correlated sampling of two such nearby distributions agrees with high probability. The cryptographic separation uses a ciphertext-identification problem where private algorithms can output a fresh re-randomized ciphertext, but replicability would require a canonical decryption.

## Depends on

- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Public-key encryption scheme](../../../../../cryptography/security-games/generic-security-games/pkescheme.md)
- [One-way function families](../../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Transfer theorem for adaptive data analysis](../../../../../cryptography/differential-privacy/differentially-private-transfer.md)

## Sources

- M. Bun, M. Gaboardi, M. Hopkins, R. Impagliazzo, R. Lei, T. Pitassi, S. Sivakumar, J. Sorrell, "Stability is Stable: Connections between Replicability, Privacy, and Adaptive Generalization", STOC (2023), arXiv:2303.12921, Theorem 3.1, Corollary 3.18, Sections 1.1.1, 1.1.2, 4 and 6.
