# Nearly optimal frequency estimation in the shuffle model

For every $k$ and $\varepsilon_0 > 0$ there are $\varepsilon_0$-locally private protocols for frequency estimation over $[k]$ whose estimate $\hat p$ of the empirical frequency vector $p(X)$ of $X \in [k]^n$ satisfies

$$
\mathbb{E}\,\|p(X) - \hat p\|_2^2 = O\!\left(\frac{1}{n} + \frac{k e^{\varepsilon_0}}{n (e^{\varepsilon_0} - 1)^2}\right).
$$

Shuffling the reports and applying the clone amplification bound with $\varepsilon_0 \approx \log\big(\varepsilon^2 n/\log(1/\delta)\big)$ yields a simple $(\varepsilon,\delta)$-differentially private shuffle protocol for frequency estimation with error close to the central model, and nearly optimal among single-message shuffle protocols.

## Proof sketch

Use the optimal local protocol of Acharya–Sun–Zhang and Chen–Kairouz–Özgür (a single message of $\log k + 2$ bits per user, with the stated error, asymptotically optimal among local protocols for $\varepsilon_0 \le \log k$), so that the coordinate variances sum to $O\bigl(1/n + k e^{\varepsilon_0}/(n(e^{\varepsilon_0}-1)^2)\bigr)$. Plain $k$-ary randomized response does not attain this for every $k$ and $\varepsilon_0$: on data with no copies of value $j$ it reports $j$ with probability $1/(e^{\varepsilon_0} + k - 1)$, and debiasing gives coordinate variance $(e^{\varepsilon_0} + k - 2)/(n(e^{\varepsilon_0} - 1)^2)$, larger by a factor of order $k e^{-\varepsilon_0}$ when $k$ grows. The clone bound shows the shuffled output is $(\varepsilon,\delta)$-DP with $\varepsilon \approx \sqrt{e^{\varepsilon_0}\log(1/\delta)/n}$, so choosing $\varepsilon_0$ to make this equal to the target $\varepsilon$ and substituting gives the error bound.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Hiding among the clones: nearly optimal amplification by shuffling](amplification-by-shuffling-clones-bound.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803, Theorem 5.1 and Section 5.
