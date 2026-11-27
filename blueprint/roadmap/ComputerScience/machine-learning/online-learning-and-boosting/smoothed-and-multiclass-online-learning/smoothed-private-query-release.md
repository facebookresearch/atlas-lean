# Smoothed analysis of differentially private query release

Call a distribution $D$ $\sigma$-smooth if its density with respect to the uniform base measure $u$ on the domain is at most $1/\sigma$, that is $dD/du \le 1/\sigma$, or $D(x) \le u(x)/\sigma$ for point masses on a finite domain, and call a database $B$ of size $n$ **$\sigma$-smooth for $Q$** if some $\sigma$-smooth distribution $D$ gives every query the same answer as the empirical distribution of $B$: $q(D) = q(D_B)$ for all $q \in Q$. Drawing each entry from a smooth distribution does not suffice: on a domain of more than $n/\sigma$ points the empirical distribution of $n$ entries has atoms of mass at least $1/n > 1/(\sigma|X|)$, so it is not $\sigma$-smooth, and its query answers need not match those of any smooth law; the condition is on the dataset's query answers. For such databases there are $(\varepsilon,\delta)$-differentially private algorithms answering the counting queries of a class $Q$ of VC dimension $d$ with error depending only on $d$, $\log(1/\sigma)$, the size $n$ of the database and the privacy parameters, not on the size of the domain. For a database that is $\sigma$-smooth for $Q$, the $\varepsilon$-differentially private Smooth Multiplicative Weights Exponential Mechanism, run for $T$ iterations on a $\gamma$-cover with $\gamma = \sigma/(2n)$, answers all queries with error at most $\frac1n + 2\sqrt{\log(1/\sigma)/T} + 10Td\log(2n/\sigma)/(\varepsilon n)$ with probability at least $1 - 2T(\gamma/41)^{d}$, and an $(\varepsilon,\delta)$-private projected variant (Projected Smooth Multiplicative Weights Exponential Mechanism, which keeps every iterate $\sigma$-smooth) releases a synthetic distribution that, with probability at least $1 - 1/\mathrm{poly}(n/\sigma)^{d}$ over the mechanism's randomness, has error $O\big(\sqrt{d/(\varepsilon n)}\cdot\mathrm{polylog}(1/\sigma, n/\sigma, 1/\delta)\big)$ on every query (Theorem 4.3), the privacy guarantee holding unconditionally, in contrast with the worst-case setting, where private learning and query release require finite Littlestone dimension (so that, for example, thresholds and halfspaces over infinite domains are not privately learnable).

## Proof sketch

Replace $Q$ by a $\gamma$-cover $Q'$ under the uniform measure, of size $(41/\gamma)^d$; since the data's query answers are those of a distribution with density at most $1/\sigma$, each query and its proxy differ on the data by at most $2\gamma/\sigma$. Run the multiplicative weights exponential mechanism of Hardt, Ligett and McSherry on $Q'$: its error depends on $\ln|Q'|$ and on the KL divergence from the starting distribution to the data distribution, which smoothness bounds by $\ln(1/\sigma)$ in place of the logarithm of the domain size. For data release, each multiplicative-weights iterate is projected in KL divergence onto the convex set of $\sigma$-smooth distributions, which only increases the progress, so the released distribution is itself smooth and answers all of $Q$, not just $Q'$.

## Depends on

- [Smoothed adversaries in online learning](smoothed-adversary.md)
- [Differential privacy](../../../cryptography/differential-privacy/differentially-private.md)
- [Private learning requires log-star of the Littlestone dimension samples](../../pac-learning/replicable-private-and-universal-learning/replicability-and-private-learning/private-learning-and-littlestone-classes/private-learning-requires-log-star-littlestone.md)

## Proof depends on

- [Private multiplicative weights answers exponentially many counting queries](../../../cryptography/privacy-accounting-lower-bounds-and-private-learning/fingerprinting-lower-bounds-and-adaptive-data-analysis/private-multiplicative-weights.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129, Section 4, Theorems 4.2 and 4.3.
