# Kingman limit under a strong seed bank with diverging mean age

In the [renewal seed-bank Wright–Fisher model](kingman-limit-of-the-renewal-seed-bank-ancestral-process.md) with $N$ individuals per generation, take the $N$-dependent seed-bank age distribution

$$\mu_N = (1-\varepsilon)\,\delta_1 + \varepsilon\,\delta_{N^\beta}, \qquad \varepsilon \in (0,1),\ \beta > 0,$$

so each individual inherits its type from the previous generation with probability $1-\varepsilon$ and from $N^\beta$ generations back with probability $\varepsilon$. The mean age $\mathbb E_{\mu_N} = 1 + \varepsilon(N^\beta - 1)$ diverges, which places the model outside the finite-mean theory. Sample $m$ individuals with initial generations drawn independently from a law $\gamma$ on $\mathbb N_0$ of finite support, let $(A^N_k)_{k\ge0}$ be the partition-valued ancestral process (blocks merge when lines pick the same individual in the same generation) and $T^N_{\mathrm{MRCA}}(m)$ the time at which a single block remains.

**Theorem.** If $0 < \beta < 1/4$, then for every $m$ and every finitely supported $\gamma$,

$$\big(A^N_{\lfloor \varepsilon^2 N^{1+2\beta} t \rfloor}\big)_{t\ge0} \Longrightarrow \text{Kingman's } m\text{-coalescent}$$

weakly in Skorokhod space as $N\to\infty$, and

$$\lim_{N\to\infty} \frac{\mathbb E\big[T^N_{\mathrm{MRCA}}(m)\big]}{\varepsilon^2 N^{1+2\beta}} = 2\Big(1 - \frac1m\Big).$$

**Proposition.** For every $\beta > 0$ and $N$ large, $\mathbb E[T^N_{\mathrm{MRCA}}(m)] \ge \varepsilon N^{1+\beta} \vee N$; and if $0 < \beta < 1/3$, then $\mathbb P(T^N_{\mathrm{MRCA}}(m) < \varepsilon^2 N^{1+2\beta-\delta}) \to 0$ for every $\delta > 0$.

So a strong seed bank stretches the coalescent time scale from $N$ to order $N^{1+2\beta}$ while keeping Kingman's genealogy shape.

## Depends on

- [Kingman limit of the renewal seed-bank ancestral process](kingman-limit-of-the-renewal-seed-bank-ancestral-process.md)

## Expansion

Each ancestral line is a renewal process whose renewal indicator is encoded by an urn chain $(X_k)$ on $\{0,\dots,N^\beta-1\}$; its unique stationary law is $\nu_N(k) = \mu_N(\{k+1,\dots\})/\mathbb E_{\mu_N}$, so a line occupies a given generation with stationary probability $1/\mathbb E_{\mu_N} \approx 1/(\varepsilon N^\beta)$. Two lines meet with probability about $(\varepsilon N^\beta)^{-2} N^{-1}$ per generation, which is the source of the scale $\varepsilon^2 N^{1+2\beta}$. For $\beta < 1/4$ the urn chain mixes in total variation within $N^{\lambda}$ steps for any $\lambda > 3\beta$, and is already mixed at an independent geometric time of mean $N$; this separation of time scales makes successive coalescence times asymptotically exponential and memoryless, yielding Kingman's coalescent. The expected-TMRCA formula is the Kingman value $\sum_{k=2}^m \binom k2^{-1} = 2(1-1/m)$.

## Sources

- Jochen Blath, Bjarki Eldon, Adrián González Casanova, Noemi Kurt, "Genealogy of a Wright Fisher model with strong seed bank component", in *XI Symposium on Probability and Stochastic Processes*, Progress in Probability, Birkhäuser (2015), 81–100, <https://doi.org/10.1007/978-3-319-13984-5_4>; preprint arXiv:1403.2925, <https://doi.org/10.48550/arXiv.1403.2925>. Numbering of the arXiv version: Section 2 (equation for $\mu_N$, Definition of the ancestral process, Theorem 2.2, Corollary 2.3, Proposition 2.4), Section 3 (Lemmas 3.1–3.3).
