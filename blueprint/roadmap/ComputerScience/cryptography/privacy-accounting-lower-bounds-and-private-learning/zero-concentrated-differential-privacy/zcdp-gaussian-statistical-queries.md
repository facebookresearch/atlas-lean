# Answering many statistical queries under zCDP with the Gaussian mechanism

Fix $\rho > 0$ and positive integers $n$ and $k$ (the scale below is undefined for $\rho = 0$, which the zCDP definition allows). Let $q_1, \dots, q_k$ be (adaptively chosen) statistical queries $q_j(S) = \frac1n\sum_i \psi_j(z_i)$ with $\psi_j \in [0,1]$. Answering each with independent Gaussian noise of standard deviation

$$
\sigma = \frac{1}{n}\sqrt{\frac{k}{2\rho}}
$$

is $\rho$-zCDP, and with probability at least $1 - \beta$ all answers differ from the empirical values $q_j(S)$ by at most $\sigma\sqrt{2\log(2k/\beta)} = \frac{1}{n}\sqrt{\frac{k\log(2k/\beta)}{\rho}}$. Here $\beta \in (0,1)$. For $(\varepsilon,\delta)$-DP with $\varepsilon > 0$ and $\delta \in (0,1)$, write $L = \log(1/\delta)$ and take $\rho = (\sqrt{L + \varepsilon} - \sqrt{L})^2$; the maximum error is then $\frac{(\sqrt{L+\varepsilon} + \sqrt{L})\sqrt{k\log(2k/\beta)}}{\varepsilon n}$. When $\varepsilon = O(\log(1/\delta))$ this is $O\big(\sqrt{k\log(1/\delta)\log(2k/\beta)}/(\varepsilon n)\big)$, so $n = \tilde O(\sqrt{k}/(\alpha\varepsilon))$ samples suffice for empirical error $\alpha$; accuracy with respect to a population distribution under adaptive choice needs, in addition, a transfer theorem.

## Proof sketch

Each query has $\ell_2$-sensitivity $1/n$, so each answer is $\frac{1}{2n^2\sigma^2} = \frac{\rho}{k}$-zCDP, and adaptive composition over $k$ queries gives $\rho$-zCDP. A Gaussian tail bound and a union bound over the $k$ answers give the error bound. The zCDP-to-approximate-DP conversion $\varepsilon = \rho + 2\sqrt{\rho L}$, solved for $\rho$ (Bun–Steinke, Lemma 3.5 with $\xi = 0$), gives $\sqrt{\rho} = \sqrt{L+\varepsilon} - \sqrt{L} = \varepsilon/(\sqrt{L+\varepsilon} + \sqrt{L})$; substituting into the error bound gives the last statement, and for $\varepsilon \le cL$ the factor $\sqrt{L+\varepsilon} + \sqrt{L}$ is at most $(1 + \sqrt{1+c})\sqrt{L}$, so $\rho = \Theta(\varepsilon^2/L)$.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)
- [Adaptive composition and post-processing of zCDP](zcdp-composition-and-post-processing.md)
- [Conversion from zCDP to approximate differential privacy](zcdp-to-approximate-dp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Proposition 1.6, Lemma 1.7, Proposition 1.3 and Lemma 3.5.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513.
