# Answering many statistical queries under zCDP with the Gaussian mechanism

Let $q_1, \dots, q_k$ be (adaptively chosen) statistical queries $q_j(S) = \frac1n\sum_i \psi_j(z_i)$ with $\psi_j \in [0,1]$. Answering each with independent Gaussian noise of standard deviation

$$
\sigma = \frac{1}{n}\sqrt{\frac{k}{2\rho}}
$$

is $\rho$-zCDP, and with probability at least $1 - \beta$ all answers differ from the empirical values $q_j(S)$ by at most $\sigma\sqrt{2\log(2k/\beta)} = \frac{1}{n}\sqrt{\frac{k\log(2k/\beta)}{\rho}}$. Converting to $(\varepsilon,\delta)$-DP, the maximum error is $O\big(\sqrt{k\log(1/\delta)\log(k/\beta)}/(\varepsilon n)\big)$, so $n = \tilde O(\sqrt{k}/(\alpha\varepsilon))$ samples suffice for empirical error $\alpha$; accuracy with respect to a population distribution under adaptive choice needs, in addition, a transfer theorem.

## Proof sketch

Each query has $\ell_2$-sensitivity $1/n$, so each answer is $\frac{1}{2n^2\sigma^2} = \frac{\rho}{k}$-zCDP, and adaptive composition over $k$ queries gives $\rho$-zCDP. A Gaussian tail bound and a union bound over the $k$ answers give the error bound, and the zCDP-to-approximate-DP conversion with $\rho \approx \varepsilon^2/\log(1/\delta)$ gives the last statement.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)
- [Adaptive composition and post-processing of zCDP](zcdp-composition-and-post-processing.md)
- [Conversion from zCDP to approximate differential privacy](zcdp-to-approximate-dp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Proposition 1.6, Lemma 1.7 and Proposition 1.3.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513.
