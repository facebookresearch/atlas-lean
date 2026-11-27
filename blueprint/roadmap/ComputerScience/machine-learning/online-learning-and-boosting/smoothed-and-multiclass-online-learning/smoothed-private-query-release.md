# Smoothed analysis of differentially private query release

When the database entries are drawn from $\sigma$-smooth distributions (relative to a base measure $\mu$), there are $(\varepsilon,\delta)$-differentially private algorithms answering the counting queries of a class $Q$ of VC dimension $d$ with error depending only on $d$, $\log(1/\sigma)$, the size $n$ of the database and the privacy parameters, not on the size of the domain. For a $\sigma$-smooth database, the $\varepsilon$-differentially private Smooth Multiplicative Weights Exponential Mechanism answers all queries with error at most $\frac1n + 2\sqrt{\log(1/\sigma)/T} + 10Td\log(2n/\sigma)/(\varepsilon n)$ with high probability (after $T$ iterations), and an $(\varepsilon,\delta)$-private projected variant releases a synthetic distribution with error $O\big(\sqrt{d/(\varepsilon n)}\cdot\mathrm{polylog}(1/\sigma, n/\sigma, 1/\delta)\big)$ on every query, in contrast with the worst-case setting, where private learning and query release require finite Littlestone dimension (so that, for example, thresholds and halfspaces over infinite domains are not privately learnable).

## Proof sketch

Replace $Q$ by a $\gamma$-cover $Q'$ under the uniform measure, of size $(41/\gamma)^d$; since the data distribution has density at most $1/\sigma$, each query and its proxy differ on the data by at most $2\gamma/\sigma$. Run the multiplicative weights exponential mechanism of Hardt, Ligett and McSherry on $Q'$: its error depends on $\ln|Q'|$ and on the KL divergence from the starting distribution to the data distribution, which smoothness bounds by $\ln(1/\sigma)$ in place of the logarithm of the domain size. For data release, each multiplicative-weights iterate is projected in KL divergence onto the convex set of $\sigma$-smooth distributions, which only increases the progress, so the released distribution is itself smooth and answers all of $Q$, not just $Q'$.

## Depends on

- [Smoothed adversaries in online learning](smoothed-adversary.md)
- [Differential privacy](../../../cryptography/differential-privacy/differentially-private.md)
- [Private learning requires log-star of the Littlestone dimension samples](../../pac-learning/replicable-private-and-universal-learning/replicability-and-private-learning/private-learning-and-littlestone-classes/private-learning-requires-log-star-littlestone.md)

## Proof depends on

- [Private multiplicative weights answers exponentially many counting queries](../../../cryptography/privacy-accounting-lower-bounds-and-private-learning/fingerprinting-lower-bounds-and-adaptive-data-analysis/private-multiplicative-weights.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129, Section 4, Theorems 4.2 and 4.3.
