# Local differential privacy is equivalent to statistical query learning

In the local model each of the $n$ individuals applies an $\varepsilon$-differentially private randomizer to their own example and an untrusted analyst sees only the randomized reports. A concept class is PAC learnable by a locally private algorithm with polynomially many individuals if and only if it is learnable in the statistical query model with polynomially many queries of inverse-polynomial tolerance: a statistical query of tolerance $\tau$ is simulated by $O(\log(1/\beta)/(\varepsilon^2\tau^2))$ local reports, and conversely a local algorithm making $t$ randomizer calls can be simulated, up to statistical distance $\beta$, by a statistical query algorithm making $O(t e^{\varepsilon})$ queries of tolerance $\Theta(\beta/(e^{2\varepsilon} t))$. In particular parity functions are not learnable with polynomially many reports under local privacy, although they are privately learnable in the central model. Non-interactive local algorithms correspond to non-adaptive statistical query algorithms and are strictly weaker than interactive ones: the masked-parity class separates them for learning under the uniform distribution.

## Proof sketch

To answer a query $\psi$ locally, each individual reports randomized response on the bit $\psi(x_i)$, and debiasing the average gives accuracy $\tau$ with the stated number of reports. Conversely, an $\varepsilon$-local randomizer's output distribution can be sampled by rejection sampling, where each acceptance probability is an expectation over the data distribution that can be estimated with statistical queries. The parity lower bound follows from the statistical query lower bound for parities.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [Differential privacy](../../../../../cryptography/differential-privacy/differentially-private.md)
- [Statistical query model with tolerance and the SQ dimension](../../../statistical-query-dimension/statistical-query-dimension.md)

## Proof depends on

- [Parities are not learnable from statistical queries](../../../statistical-query-dimension/parities-not-sq-learnable.md)

## Sources

- S. P. Kasiviswanathan, H. K. Lee, K. Nissim, S. Raskhodnikova, A. Smith, "What Can We Learn Privately?", FOCS (2008); SIAM Journal on Computing 40 (2011), arXiv:0803.0924, Section 5 (Definitions 5.1–5.5, Lemmas 5.6 and 5.8, Theorems 5.7 and 5.14), Theorem 4.4.
