# Nearly optimal frequency estimation in the shuffle model

For every $k$ and $\varepsilon_0 > 0$ there are $\varepsilon_0$-locally private protocols for frequency estimation over $[k]$ whose estimate $\hat p$ of the empirical frequency vector $p(X)$ of $X \in [k]^n$ satisfies

$$
\mathbb{E}\,\|p(X) - \hat p\|_2^2 = O\!\left(\frac{1}{n} + \frac{k e^{\varepsilon_0}}{n (e^{\varepsilon_0} - 1)^2}\right).
$$

Shuffling the reports and applying the clone amplification bound with $\varepsilon_0 \approx \log\big(\varepsilon^2 n/\log(1/\delta)\big)$ yields a simple $(\varepsilon,\delta)$-differentially private shuffle protocol for frequency estimation with error close to the central model, and nearly optimal among single-message shuffle protocols.

## Proof sketch

Use a local randomizer with large $\varepsilon_0$ (such as $k$-ary randomized response or a hashing-based variant) whose variance per coordinate is $O(e^{\varepsilon_0}/(n(e^{\varepsilon_0}-1)^2))$ after debiasing. The clone bound shows the shuffled output is $(\varepsilon,\delta)$-DP with $\varepsilon \approx \sqrt{e^{\varepsilon_0}\log(1/\delta)/n}$, so choosing $\varepsilon_0$ to make this equal to the target $\varepsilon$ and substituting gives the error bound.

## Depends on

- [Hiding among the clones: nearly optimal amplification by shuffling](amplification-by-shuffling-clones-bound.md)
- [Local randomizers and the shuffle model](shuffle-model.md)

## Proof depends on

- [Hiding among the clones: nearly optimal amplification by shuffling](amplification-by-shuffling-clones-bound.md)
- [Local randomizers and the shuffle model](shuffle-model.md)

## Sources

- V. Feldman, A. McMillan, K. Talwar, "Hiding Among the Clones: A Simple and Nearly Optimal Analysis of Privacy Amplification by Shuffling", FOCS (2021), arXiv:2012.12803.
