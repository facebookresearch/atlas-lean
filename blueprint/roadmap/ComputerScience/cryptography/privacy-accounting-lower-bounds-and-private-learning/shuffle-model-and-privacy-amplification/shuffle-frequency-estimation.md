# Nearly optimal frequency estimation in the shuffle model

For every $k$ and $\varepsilon_0 > 0$ there are $\varepsilon_0$-locally private protocols for frequency estimation over $[k]$ whose estimate $\hat p$ of the empirical frequency vector $p(X)$ of $X \in [k]^n$ satisfies

$$
\mathbb{E}\,\|p(X) - \hat p\|_2^2 = O\!\left(\frac{1}{n} + \frac{k e^{\varepsilon_0}}{n (e^{\varepsilon_0} - 1)^2}\right).
$$

Shuffling the reports and applying the clone amplification bound yields, for $\varepsilon, \delta \in (0,1)$, a simple $(\varepsilon,\delta)$-differentially private shuffle protocol for frequency estimation with

$$
\mathbb{E}\,\|p(X) - \hat p\|_2^2 = O\!\left(\frac{k\log(1/\delta)}{(\varepsilon n)^2} + \frac{1}{n}\right),
$$

error close to the central model and nearly optimal among single-message shuffle protocols. The local parameter depends on the regime. When $\varepsilon^2 n$ is large compared with $\log(1/\delta)$ (for instance $\varepsilon^2 n \ge 200\log(1/\delta)$), take $\varepsilon_0 = \log\big(\varepsilon^2 n/(100\log(1/\delta))\big)$; this logarithm is negative when $\varepsilon^2 n < 100\log(1/\delta)$, and then $\varepsilon_0$ of order $\varepsilon\sqrt{n/\log(1/\delta)}$ is used instead (for $\varepsilon$ between $\sqrt{\log(1/\delta)/n}$ and $\sqrt{200\log(1/\delta)/n}$, the choice made for $\varepsilon = \sqrt{\log(1/\delta)/n}$ gives the stated error up to a constant factor).

## Proof sketch

Use the optimal local protocol of Acharya–Sun–Zhang and Chen–Kairouz–Özgür (a single message of $\log k + 2$ bits per user, with the stated error, asymptotically optimal among local protocols for $\varepsilon_0 \le \log k$), so that the coordinate variances sum to $O\bigl(1/n + k e^{\varepsilon_0}/(n(e^{\varepsilon_0}-1)^2)\bigr)$. Plain $k$-ary randomized response does not attain this for every $k$ and $\varepsilon_0$: on data with no copies of value $j$ it reports $j$ with probability $1/(e^{\varepsilon_0} + k - 1)$, and debiasing gives coordinate variance $(e^{\varepsilon_0} + k - 2)/(n(e^{\varepsilon_0} - 1)^2)$, larger by a factor of order $k e^{-\varepsilon_0}$ when $k$ grows. The clone bound shows the shuffled output is $(\varepsilon,\delta)$-DP with $\varepsilon$ of order $\sqrt{e^{\varepsilon_0}\log(1/\delta)/n}$ for $\varepsilon_0 \ge 1$ and of order $\varepsilon_0\sqrt{\log(1/\delta)/n}$ for $\varepsilon_0 \le 1$, so choosing $\varepsilon_0$ to make this equal to the target $\varepsilon$ and substituting gives the error bound; with $e^{\varepsilon_0} \ge 2$ the local error term is at most $4k/(n e^{\varepsilon_0})$.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Hiding among the clones: nearly optimal amplification by shuffling](amplification-by-shuffling-clones-bound.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803, Theorems 5.1 and 5.2 and Section 5.
