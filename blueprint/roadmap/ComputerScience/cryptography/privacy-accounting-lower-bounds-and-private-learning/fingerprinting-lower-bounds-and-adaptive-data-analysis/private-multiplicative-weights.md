# Private multiplicative weights answers exponentially many counting queries

There is an $(\varepsilon,\delta)$-differentially private mechanism that answers any sequence of $k$ adaptively chosen counting queries over a data universe $\mathcal{X}$ (for example $\mathcal{X} = \{0,1\}^d$) to within error $\alpha$ with high probability, provided the dataset has

$$
n = O\!\left(\frac{\sqrt{\log|\mathcal{X}|}\,\log k\,\sqrt{\log(1/\delta)}}{\alpha^2\,\varepsilon}\right)
$$

records (up to lower-order logarithmic factors). The mechanism maintains a multiplicative-weights synthetic distribution over $\mathcal{X}$, answers each query from the synthetic distribution unless a sparse-vector test signals a large error, and in that case performs a multiplicative-weights update using a noisy true answer.

## Proof sketch

Each update decreases the relative entropy between the true data distribution and the synthetic distribution by $\Omega(\alpha^2)$, so at most $O(\log|\mathcal{X}|/\alpha^2)$ updates occur. Privacy is paid only for the updates: between two updates the threshold tests form one run of the sparse vector technique (AboveThreshold), whose privacy cost does not grow with the number of below-threshold answers, so the $k$ tests are not composed one by one (that would scale with $k$). For queries with sensitivity $1$ on the integer counts (the fractions multiplied by $n$) and discrete Laplace noise of the scales in the linked lemma, each run is $\varepsilon_0$-differentially private; advanced composition over the $O(\log\lvert\mathcal{X}\rvert/\alpha^2)$ runs and the noisy answers used in updates then gives the total privacy cost and the $\sqrt{\log|\mathcal{X}|\log(1/\delta)}/\alpha$ factor; the $\log k$ factor pays for the error tests over $k$ queries.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Privacy of AboveThreshold with discrete Laplace noise](../../discrete-privacy-mechanisms/above-threshold-privacy.md)
- [Advanced composition](../../differential-privacy/differentially-private-pi-advanced.md)
- [The Laplace mechanism is differentially private](../../laplace-and-exponential-mechanisms/laplace-mechanism-differentially-private.md)

## Sources

- M. Hardt, G. N. Rothblum, "A Multiplicative Weights Mechanism for Privacy-Preserving Data Analysis", FOCS (2010).
- M. Bun, J. Ullman, S. Vadhan, "Fingerprinting Codes and the Price of Approximate Differential Privacy", STOC (2014); SIAM Journal on Computing 47 (2018), arXiv:1311.3158.
